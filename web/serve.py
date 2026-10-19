"""Serve the generated book and a trusted local Lean playground using Python's standard library."""
import argparse
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer
import json
from pathlib import Path
from urllib.parse import urlsplit

from lean_rpc import Playground, RpcError


ROOT = Path(__file__).resolve().parents[1]
PUBLIC = ROOT / '_out/html-multi'


class PreviewHandler(SimpleHTTPRequestHandler):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, directory=str(PUBLIC), **kwargs)

    def _origin(self):
        origin = self.headers.get('Origin')
        if origin and urlsplit(origin).hostname not in ('127.0.0.1', 'localhost', '::1'):
            return False
        return origin or ''

    def _json(self, status, data):
        body = json.dumps(data, ensure_ascii=False).encode('utf-8')
        self.send_response(status)
        origin = self._origin()
        if origin:
            self.send_header('Access-Control-Allow-Origin', origin)
            self.send_header('Vary', 'Origin')
        self.send_header('Content-Type', 'application/json; charset=utf-8')
        self.send_header('Cache-Control', 'no-store')
        self.send_header('Content-Length', str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def do_OPTIONS(self):
        if self._origin() is False:
            return self._json(403, {'error': 'The Lean preview accepts loopback origins only.'})
        self.send_response(204)
        self.send_header('Access-Control-Allow-Origin', self._origin())
        self.send_header('Access-Control-Allow-Methods', 'GET, POST, OPTIONS')
        self.send_header('Access-Control-Allow-Headers', 'Content-Type')
        self.send_header('Access-Control-Allow-Private-Network', 'true')
        self.end_headers()

    def do_GET(self):
        if urlsplit(self.path).path == '/api/lean/status':
            if self._origin() is False:
                return self._json(403, {'error': 'Loopback origins only.'})
            return self._json(200, {'available': True, 'snippets': len(self.server.playground.snippets)})
        super().do_GET()

    def do_POST(self):
        if self._origin() is False:
            return self._json(403, {'error': 'The Lean preview accepts loopback origins only.'})
        if self.headers.get_content_type() != 'application/json':
            return self._json(415, {'error': 'Use application/json.'})
        try:
            size = int(self.headers.get('Content-Length', '0'))
            if not 0 < size <= 80000:
                return self._json(413, {'error': 'Invalid request size.'})
            data = json.loads(self.rfile.read(size))
            if not isinstance(data, dict):
                raise ValueError('Expected a JSON object.')
            route = urlsplit(self.path).path
            if route == '/api/lean/check':
                result = self.server.playground.check(data)
            elif route == '/api/lean/goal':
                result = self.server.playground.goal(data)
            elif route == '/api/lean/complete':
                result = self.server.playground.complete(data)
            elif route == '/api/lean/resolve':
                result = self.server.playground.resolve(data)
            else:
                return self._json(404, {'error': 'Unknown Lean endpoint.'})
            self._json(200, result)
        except (ValueError, TypeError, KeyError) as error:
            self._json(400, {'error': str(error)})
        except RpcError as error:
            self._json(503, {'error': str(error)})
        except (BrokenPipeError, ConnectionResetError, ConnectionAbortedError):
            pass


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--port', type=int, default=8000)
    args = parser.parse_args()
    manifest = PUBLIC / 'playground.json'
    if not manifest.is_file():
        raise SystemExit('Generate the textbook first: lake exe textbook')
    playground = Playground(ROOT, json.loads(manifest.read_text(encoding='utf-8')))
    server = ThreadingHTTPServer(('127.0.0.1', args.port), PreviewHandler)
    server.daemon_threads = True
    server.playground = playground
    print(f'Textbook and Lean playground: http://127.0.0.1:{args.port}/', flush=True)
    print('Trusted local preview only. Do not expose this process to a public network.', flush=True)
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass
    finally:
        server.server_close()
        playground.close()


if __name__ == '__main__':
    main()
