/* Exercise the static reader below the repository prefix used by GitHub Pages. */
const assert = require('node:assert/strict');
const fs = require('node:fs/promises');
const http = require('node:http');
const path = require('node:path');
let playwright;
try { playwright = require('playwright'); }
catch { playwright = require(path.join(process.env.USERPROFILE, '.cache/codex-runtimes/codex-primary-runtime/dependencies/node/node_modules/playwright')); }
const root = path.resolve(__dirname, '../_out/pages');
const prefix = '/lean-algebra/';
const mime = {'.html': 'text/html; charset=utf-8', '.js': 'text/javascript',
  '.css': 'text/css', '.json': 'application/json', '.woff2': 'font/woff2', '.svg': 'image/svg+xml'};

async function main() {
  const server = http.createServer(async (req, res) => {
    try {
      const url = new URL(req.url, 'http://localhost');
      if (url.pathname === '/favicon.ico') { res.writeHead(204).end(); return; }
      if (!url.pathname.startsWith(prefix)) { res.writeHead(404).end(); return; }
      let filename = path.resolve(root, decodeURIComponent(url.pathname.slice(prefix.length)) || '.');
      if (filename !== root && !filename.startsWith(root + path.sep)) { res.writeHead(403).end(); return; }
      if ((await fs.stat(filename)).isDirectory()) filename = path.join(filename, 'index.html');
      res.writeHead(200, {'Content-Type': mime[path.extname(filename)] || 'application/octet-stream'});
      res.end(await fs.readFile(filename));
    } catch { res.writeHead(404).end(); }
  });
  await new Promise(resolve => server.listen(0, '127.0.0.1', resolve));
  const base = process.env.BOOK_URL || `http://127.0.0.1:${server.address().port}${prefix}`;
  const browser = await playwright.chromium.launch({headless: true,
    executablePath: process.env.CHROME_PATH || (process.platform === 'win32' ? 'C:/Program Files/Google/Chrome/Application/chrome.exe' : undefined)});
  try {
    const context = await browser.newContext({permissions: ['clipboard-read', 'clipboard-write']});
    const page = await context.newPage();
    const failures = [];
    const apiRequests = [];
    page.on('pageerror', error => failures.push(error.message));
    page.on('response', response => { if (response.status() >= 400) failures.push(response.url()); });
    page.on('request', request => { if (request.url().includes('/api/lean/')) apiRequests.push(request.url()); });
    await page.goto(base + 'foundations/sets/equality/');
    await page.evaluate(() => document.fonts.ready);
    const proof = page.locator('.book-example').filter({hasText: '@[ext] theorem set_ext'});
    await proof.locator('.tactic > label').filter({hasText: /^funext x$/}).click();
    assert.ok((await proof.locator('.book-step-state').innerText()).includes('S x = T x'));
    assert.ok(await proof.getByRole('button', {name: '단계', exact: true}).isVisible());
    await proof.getByRole('button', {name: '복사', exact: true}).click();
    await page.waitForFunction(() => document.body.textContent.includes('복사됨'));
    assert.ok((await page.evaluate(() => navigator.clipboard.readText())).includes('theorem set_ext'));
    await page.goto(base + 'preliminaries/equivalence-relations/');
    await page.waitForURL(base + 'foundations/relations/equivalence-relations/');
    await page.goto(base + 'foundations/cardinality/same-cardinality/#cardinality-quotient-type');
    await page.waitForURL(base + 'foundations/cardinality/cardinals/');
    assert.deepEqual(apiRequests, []);
    assert.deepEqual(failures, []);
    console.log('PASS: static proof steps, clipboard, assets, legacy redirects, and no Lean server requests.');
  } finally {
    await browser.close();
    server.closeAllConnections();
    await new Promise(resolve => server.close(resolve));
  }
}
main().catch(error => { console.error(error); process.exit(1); });
