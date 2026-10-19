"""Small LSP adapter for the trusted, loopback-only textbook preview.

The language server owns elaboration, diagnostics and tactic states. This module
only frames JSON-RPC messages and maps positions into generated example contexts.
No exercise files are written or imported from the learner's private solutions.
"""
from __future__ import annotations

import json
import os
from pathlib import Path
import queue
import re
import shutil
import subprocess
import threading
import time
import uuid


class RpcError(RuntimeError):
    pass


class LeanRpc:
    def __init__(self, root: Path):
        self.root = root
        lake = shutil.which('lake') or str(Path.home() / '.elan/bin/lake.exe')
        self.process = subprocess.Popen(
            [lake, 'env', 'lean', '--server'], cwd=root,
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
            creationflags=subprocess.CREATE_NO_WINDOW if os.name == 'nt' else 0,
        )
        self.write_lock = threading.Lock()
        self.lock = threading.Lock()
        self.pending = {}
        self.documents = {}
        self.next_id = 0
        threading.Thread(target=self._read, daemon=True).start()
        self.request('initialize', {
            'processId': None, 'rootUri': root.as_uri(),
            'capabilities': {'textDocument': {'publishDiagnostics': {'versionSupport': True}}},
            'initializationOptions': {'hasWidgets': False},
        })
        self.send({'method': 'initialized', 'params': {}})

    def send(self, message):
        payload = json.dumps({'jsonrpc': '2.0', **message}, ensure_ascii=False).encode('utf-8')
        with self.write_lock:
            try:
                self.process.stdin.write(f'Content-Length: {len(payload)}\r\n\r\n'.encode() + payload)
                self.process.stdin.flush()
            except (OSError, ValueError) as error:
                raise RpcError('Lean has stopped. Restart the preview server.') from error

    def request(self, method, params, timeout=40):
        channel = queue.Queue(maxsize=1)
        with self.lock:
            self.next_id += 1
            identifier = self.next_id
            self.pending[identifier] = channel
        try:
            self.send({'id': identifier, 'method': method, 'params': params})
            try:
                message = channel.get(timeout=timeout)
            except queue.Empty as error:
                self.send({'method': '$/cancelRequest', 'params': {'id': identifier}})
                raise RpcError('Lean timed out. Shorten the example and try again.') from error
            if 'error' in message:
                raise RpcError(message['error'].get('message', 'Lean request failed.'))
            return message.get('result')
        finally:
            with self.lock:
                self.pending.pop(identifier, None)

    def _read(self):
        try:
            while True:
                headers = {}
                while True:
                    line = self.process.stdout.readline()
                    if not line:
                        return
                    if line in (b'\r\n', b'\n'):
                        break
                    key, _, value = line.decode('ascii').partition(':')
                    headers[key.lower()] = value.strip()
                payload = self.process.stdout.read(int(headers['content-length']))
                message = json.loads(payload)
                if 'id' in message and 'method' not in message:
                    with self.lock:
                        target = self.pending.get(message['id'])
                    if target:
                        target.put_nowait(message)
                elif 'method' in message and 'id' in message:
                    # Lean may request client capabilities we do not implement.
                    self.send({'id': message['id'], 'result': None})
                elif message.get('method') == 'textDocument/publishDiagnostics':
                    params = message['params']
                    doc = self.documents.get(params['uri'])
                    if doc is not None and params.get('version', doc['version']) == doc['version']:
                        doc['diagnostics'] = params.get('diagnostics', [])
                elif message.get('method') == '$/lean/fileProgress':
                    params = message['params']
                    doc = self.documents.get(params['textDocument']['uri'])
                    if doc is not None:
                        doc['busy'] = bool(params.get('processing', []))
        except (OSError, ValueError, KeyError, queue.Full):
            pass
        finally:
            with self.lock:
                channels = list(self.pending.values())
            for channel in channels:
                try:
                    channel.put_nowait({'error': {'message': 'Lean has stopped. Restart the preview server.'}})
                except queue.Full:
                    pass

    def close(self):
        if self.process.poll() is not None:
            return
        if os.name == 'nt':
            subprocess.run(['taskkill', '/PID', str(self.process.pid), '/T', '/F'],
                           stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                           creationflags=subprocess.CREATE_NO_WINDOW)
        else:
            self.process.terminate()
        self.process.wait(timeout=5)


def close_scopes(source):
    """Close document scopes, which normally continue into later code blocks."""
    scopes = []
    for line in source.splitlines():
        match = re.match(r'^(?:namespace|section)(?:\s+(\S+))?\s*$', line)
        if match:
            scopes.append(match.group(1) or '')
        elif re.match(r'^end(?:\s+\S+)?\s*$', line) and scopes:
            scopes.pop()
    return '\n' + ''.join('end' + (' ' + name if name else '') + '\n' for name in reversed(scopes))


class Playground:
    def __init__(self, root, snippets):
        self.root = root
        (root / 'tmp/web-playground').mkdir(parents=True, exist_ok=True)
        self.snippets = snippets
        self.rpc = None
        self.lock = threading.Lock()
        self.sessions = {}

    def _server(self):
        with self.lock:
            if self.rpc is None:
                self.rpc = LeanRpc(self.root)
            return self.rpc

    def _document(self, data):
        key, code = data.get('snippet'), data.get('code')
        if key not in self.snippets or not isinstance(code, str):
            raise ValueError('Select an example from the current textbook.')
        if len(code.encode('utf-8')) > 50000:
            raise ValueError('The example is too long (maximum 50 KB).')
        rpc = self._server()
        now = time.monotonic()
        with self.lock:
            for token, session in list(self.sessions.items()):
                if now - session['used'] > 600 and not session['lock'].locked():
                    rpc.send({'method': 'textDocument/didClose', 'params': {'textDocument': {'uri': session['uri']}}})
                    rpc.documents.pop(session['uri'], None)
                    del self.sessions[token]
            token = data.get('session')
            session = self.sessions.get(token)
            if session is None:
                if len(self.sessions) >= 8:
                    raise ValueError('Too many open examples. Wait a few minutes and try again.')
                token = uuid.uuid4().hex
                uri = (self.root / 'tmp' / 'web-playground' / f'{token}.lean').as_uri()
                session = {'uri': uri, 'snippet': key, 'lock': threading.Lock(),
                           'version': 0, 'used': now, 'diagnostics': [], 'busy': True}
                self.sessions[token] = session
                rpc.documents[uri] = session
        return rpc, token, session, key, code

    def _update(self, rpc, session, key, code):
        """Synchronize the editable document under its session lock."""
        session['used'] = time.monotonic()
        if session.get('code') == code and session['snippet'] == key:
            return
        prefix = self.snippets[key]['before'].rstrip() + '\n\n'
        # Preserve blank proof lines so cursor positions stay inside the proof.
        source = prefix + code + ('' if code.endswith('\n') else '\n')
        full = source + close_scopes(source)
        session.update(snippet=key, version=session['version'] + 1, diagnostics=[], busy=True,
                       offset=prefix.count('\n'), code=code, completions=None)
        document = {'uri': session['uri'], 'version': session['version']}
        if session['version'] == 1:
            rpc.send({'method': 'textDocument/didOpen', 'params': {'textDocument': {
                **document, 'languageId': 'lean4', 'text': full}}})
        else:
            rpc.send({'method': 'textDocument/didChange', 'params': {
                'textDocument': document, 'contentChanges': [{'text': full}]}})

    def check(self, data):
        rpc, token, session, key, code = self._document(data)
        with session['lock']:
            self._update(rpc, session, key, code)
            # Lean's synchronization request covers all diagnostics, including code
            # after the selected cursor, without guessing from progress notifications.
            rpc.request('textDocument/waitForDiagnostics', {
                'uri': session['uri'], 'version': session['version']})
            diagnostics = []
            context_errors = []
            for original in session['diagnostics']:
                item = dict(original)
                start = original['range']['start']['line'] - session['offset']
                if start < 0:
                    if original.get('severity') == 1:
                        context_errors.append(original['message'])
                    continue
                item['line'] = start + 1
                item['column'] = original['range']['start']['character'] + 1
                # Keep Lean's diagnostic intact, but distinguish incomplete work
                # from invalid code. The UI displays the former with the goals.
                if 1 in original.get('leanTags', []):
                    item['kind'] = 'unfinished'
                elif original.get('severity') == 2 and re.fullmatch(
                        r"declaration uses [‘'`]sorry[’'`]", original['message'].strip()):
                    item['kind'] = 'unfinished'
                else:
                    item['kind'] = 'diagnostic'
                diagnostics.append(item)
            position = data.get('position') or {'line': max(0, len(code.splitlines()) - 1), 'character': 0}
            goal = self._goal(rpc, session, position)
            return {'session': token, 'version': session['version'], 'goal': goal,
                    'diagnostics': diagnostics, 'contextErrors': context_errors}

    def complete(self, data):
        rpc, token, session, key, code = self._document(data)
        with session['lock']:
            self._update(rpc, session, key, code)
            rows = code.split('\n')
            position = data.get('position', {})
            line = max(0, min(int(position.get('line', 0)), len(rows) - 1))
            row = rows[line].encode('utf-16-le')
            column = max(0, min(int(position.get('character', 0)), len(row) // 2))
            before = row[:column * 2].decode('utf-16-le', errors='replace')
            after = row[column * 2:].decode('utf-16-le', errors='replace')
            # Lean normally returns a label replacing the last identifier segment.
            # Synthetic completions may instead provide an explicit LSP text edit.
            left = re.search(r"[^\W\d][\w'₀-₉]*$", before, re.UNICODE)
            right = re.match(r"[\w'₀-₉]*", after, re.UNICODE)
            prefix = left.group() if left else ''
            start = column - len(prefix.encode('utf-16-le')) // 2
            end = column + len(right.group().encode('utf-16-le')) // 2
            result = rpc.request('textDocument/completion', {
                'textDocument': {'uri': session['uri']},
                'position': {'line': line + session['offset'], 'character': column}}) or {}
            items = result.get('items', [])
            items.sort(key=lambda item: (not item['label'].lower().startswith(prefix.lower()),
                                         item.get('sortText', item['label'])))
            items = items[:100]
            identifier = uuid.uuid4().hex
            session['completions'] = {'id': identifier, 'items': items}
            choices = []
            for index, item in enumerate(items):
                edit = item.get('textEdit')
                if edit:
                    edit_range = edit.get('replace') or edit.get('range') or edit.get('insert')
                    edit_range = {edge: {**pos, 'line': pos['line'] - session['offset']}
                                  for edge, pos in edit_range.items()}
                    new_text = edit['newText']
                else:
                    edit_range = {'start': {'line': line, 'character': start},
                                  'end': {'line': line, 'character': end}}
                    new_text = item.get('insertText', item['label'])
                choices.append({'index': index, 'label': item['label'], 'detail': item.get('detail', ''),
                                'range': edit_range, 'text': new_text})
            return {'session': token, 'version': session['version'], 'completion': identifier,
                    'items': choices, 'isIncomplete': result.get('isIncomplete', False)}

    def resolve(self, data):
        session = self.sessions.get(data.get('session'))
        if session is None:
            raise ValueError('Request completions for this example first.')
        with session['lock']:
            cached = session.get('completions')
            if data.get('version') != session['version'] or not cached or data.get('completion') != cached['id']:
                raise ValueError('The code changed. Request completions again.')
            index = data.get('index')
            if not isinstance(index, int) or not 0 <= index < len(cached['items']):
                raise ValueError('Select a completion from the current list.')
            item = cached['items'][index]
            if not item.get('detail'):
                item = self._server().request('completionItem/resolve', item)
                cached['items'][index] = item
            session['used'] = time.monotonic()
            return {'detail': item.get('detail', ''),
                    'documentation': (item.get('documentation') or {}).get('value', '')}

    @staticmethod
    def _goal(rpc, session, position):
        line = max(0, min(int(position.get('line', 0)), len(session['code'].splitlines())))
        character = max(0, min(int(position.get('character', 0)), 5000))
        def query(row, col):
            return rpc.request('$/lean/plainGoal', {'textDocument': {'uri': session['uri']},
                'position': {'line': row + session['offset'], 'character': col}})
        result = query(line, character)
        rows = session['code'].split('\n')
        if result is None and line < len(rows) and not rows[line][:character].strip():
            # On a blank proof line, ask Lean for the state immediately after
            # the preceding command, rather than inferring a goal ourselves.
            previous = line - 1
            while previous >= 0 and not rows[previous].strip():
                previous -= 1
            if previous >= 0:
                column = len(rows[previous].rstrip().encode('utf-16-le')) // 2
                result = query(previous, column)
        return result.get('goals', []) if result is not None else None

    def goal(self, data):
        session = self.sessions.get(data.get('session'))
        if session is None:
            raise ValueError('Run this example before requesting its goal.')
        with session['lock']:
            if data.get('version') != session['version']:
                raise ValueError('The code changed. Run the example again.')
            session['used'] = time.monotonic()
            return {'goal': self._goal(self._server(), session, data.get('position', {})),
                    'version': session['version']}

    def close(self):
        if self.rpc:
            self.rpc.close()
