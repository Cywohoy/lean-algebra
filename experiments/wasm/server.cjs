// Static experiment server. There is no compiler process or proof submission endpoint.
const fs = require('node:fs');
const fsp = require('node:fs/promises');
const http = require('node:http');
const path = require('node:path');
const upstream = path.resolve(__dirname, '../../tmp/wasm/upstream');
const artifacts = path.join(upstream, 'tests/.artifacts');
const ample = path.resolve(__dirname, '../../../Ample');

function listFiles(root, relative = '') {
  return fs.readdirSync(path.join(root, relative), {withFileTypes: true}).flatMap(entry => {
    const name = relative ? `${relative}/${entry.name}` : entry.name;
    return entry.isDirectory() ? listFiles(root, name) : [name];
  });
}

async function createServer({isolate = true} = {}) {
  const lib = path.join(artifacts, 'lib/lean');
  const nativeModule = path.join(ample, '.lake/build/lib/lean/Ample/Tactic/Classical.olean');
  const manifest = listFiles(lib);
  if (fs.existsSync(nativeModule)) manifest.push('Ample/Tactic/Classical.olean');
  const mime = {'.html': 'text/html; charset=utf-8', '.js': 'text/javascript', '.wasm': 'application/wasm'};
  const server = http.createServer(async (req, res) => {
    try {
      if (isolate) {
        res.setHeader('Cross-Origin-Opener-Policy', 'same-origin');
        res.setHeader('Cross-Origin-Embedder-Policy', 'require-corp');
      }
      const route = decodeURIComponent(new URL(req.url, 'http://localhost').pathname);
      if (route === '/favicon.ico') { res.writeHead(204).end(); return; }
      if (route === '/library.json') {
        res.writeHead(200, {'Content-Type': 'application/json'}).end(JSON.stringify(manifest)); return;
      }
      let root = __dirname;
      let relative = route.slice(1) || 'index.html';
      if (route === '/worker.js') { root = path.join(upstream, 'public'); relative = 'lean-worker-persistent.worker.js'; }
      else if (route === '/coi-serviceworker.js') { root = path.resolve(upstream, '../coi-serviceworker'); relative = 'coi-serviceworker.js'; }
      else if (route.startsWith('/runtime/')) { root = path.join(artifacts, 'runtime'); relative = route.slice(9); }
      else if (route === '/library/Ample/Tactic/Classical.olean') {
        root = path.dirname(nativeModule); relative = path.basename(nativeModule);
      } else if (route.startsWith('/library/')) { root = lib; relative = route.slice(9); }
      const filename = path.resolve(root, relative);
      if (!filename.startsWith(path.resolve(root) + path.sep)) { res.writeHead(403).end(); return; }
      const stat = await fsp.stat(filename);
      res.writeHead(200, {'Content-Type': mime[path.extname(filename)] || 'application/octet-stream', 'Content-Length': stat.size});
      fs.createReadStream(filename).pipe(res);
    } catch { if (!res.headersSent) res.writeHead(404); res.end(); }
  });
  await new Promise(resolve => server.listen(0, '127.0.0.1', resolve));
  return server;
}

module.exports = {createServer, upstream, artifacts, ample};
if (require.main === module) createServer().then(server => console.log(`Experiment: http://127.0.0.1:${server.address().port}/`));
