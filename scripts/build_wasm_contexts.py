"""Compile exact exercise prefixes with the matching native wasm32 Lean toolchain."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess


def scope_commands(source):
    """Replay lexical context, including multiline variables and local notation."""
    lines = source.splitlines()
    commands = []
    for index, line in enumerate(lines):
        if (re.match(r'^(?:namespace|section|end|open|variable|set_option|noncomputable section|local (?:notation|infixr?|prefix|postfix|attribute))\b', line)
                and not line.rstrip().endswith(' in')):
            commands.append(line)
            for continuation in lines[index + 1:]:
                if continuation and not continuation[0].isspace():
                    break
                commands.append(continuation)
    return '\n'.join(commands)

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--site', type=Path, required=True)
parser.add_argument('--lean', type=Path, required=True)
parser.add_argument('--ample-lib', type=Path, required=True)
parser.add_argument('--output', type=Path, required=True)
args = parser.parse_args()
output = args.output.resolve()
output.mkdir(parents=True, exist_ok=True)
manifest = json.loads((args.site / 'playground.json').read_text(encoding='utf-8'))
contexts = {}
for item in manifest.values():
    if not item.get('exercise'):
        continue
    source = item.get('sourceBefore', item['before'])
    digest = hashlib.sha256(source.encode()).hexdigest()
    if digest in contexts:
        continue
    name = 'AmpleBrowserContext.C' + digest[:24]
    relative = Path(*name.split('.'))
    source_path = output / relative.with_suffix('.lean')
    source_path.parent.mkdir(parents=True, exist_ok=True)
    scopes = []
    for line in source.splitlines():
        opened = re.fullmatch(r'(namespace|section)(?:\s+(\S+))?\s*', line)
        if opened:
            scopes.append(opened[2] or '')
        elif re.fullmatch(r'end(?:\s+\S+)?\s*', line) and scopes:
            scopes.pop()
    closed = source + '\n' + ''.join('end' + (' ' + scope if scope else '') + '\n' for scope in reversed(scopes))
    source_path.write_text(closed, encoding='utf-8')
    olean = relative.with_suffix('.olean')
    env = {**os.environ, 'LEAN_PATH': str(args.ample_lib.resolve()) + os.pathsep + str(output)}
    result = subprocess.run([str(args.lean.resolve()), '-o', str(olean), str(relative.with_suffix('.lean'))],
                            cwd=output, env=env, text=True, capture_output=True, timeout=180)
    if result.returncode or 'declaration uses `sorry`' in result.stdout:
        raise RuntimeError(f'{name}: {result.stdout}\n{result.stderr}')
    files = []
    for file in sorted(source_path.parent.glob(source_path.stem + '.*')):
        if file.suffix == '.lean':
            continue
        raw = file.read_bytes()
        files.append({'name': file.relative_to(output).as_posix(), 'bytes': len(raw),
                      'sha256': hashlib.sha256(raw).hexdigest()})
    contexts[digest] = {'module': name, 'scope': scope_commands(source), 'files': files}
    print(f'Checked {name} ({len(files)} files)', flush=True)
(output / 'contexts.json').write_text(json.dumps(contexts, indent=2) + '\n', encoding='utf-8')
print(f'Built {len(contexts)} exact exercise contexts.', flush=True)
