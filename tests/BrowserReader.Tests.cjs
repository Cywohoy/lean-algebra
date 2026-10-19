// Exercise the published reader using static files only, with no Lean HTTP API.
const assert = require('node:assert/strict');
const fs = require('node:fs');
const http = require('node:http');
const path = require('node:path');
let playwright;
try { playwright = require('playwright'); }
catch { playwright = require(path.join(process.env.USERPROFILE, '.cache/codex-runtimes/codex-primary-runtime/dependencies/node/node_modules/playwright')); }
const site = path.resolve('_out/pages');
const localManifest = JSON.parse(fs.readFileSync(path.join(site, 'playground.json'), 'utf8'));
let manifest = localManifest;
const uploads = [];
function walk(directory) {
  return fs.readdirSync(directory, {withFileTypes: true}).flatMap(entry => {
    const file = path.join(directory, entry.name);
    return entry.isDirectory() ? walk(file) : file.endsWith('.html') ? [file] : [];
  });
}
const pages = walk(site);
function example(match) {
  const pair = Object.entries(manifest).find(([, value]) => match(value.code));
  assert(pair, 'The selected textbook example disappeared');
  const [key, data] = pair;
  const localKey = Object.entries(localManifest).find(([, value]) => value.code === data.code)?.[0] || key;
  const file = pages.find(file => fs.readFileSync(file, 'utf8').includes(`data-snippet="${localKey}"`));
  assert(file, key);
  return {key, data, url: path.relative(site, file).replaceAll('\\', '/').replace(/index\.html$/, '')};
}
async function main() {
  const server = http.createServer((request, response) => {
    const pathname = decodeURIComponent(new URL(request.url, 'http://localhost').pathname);
    if (request.method !== 'GET') uploads.push(pathname);
    if (pathname === '/favicon.ico') { response.writeHead(204).end(); return; }
    if (!pathname.startsWith('/lean-algebra/')) { response.writeHead(404).end(); return; }
    let file = path.resolve(site, pathname.slice('/lean-algebra/'.length));
    if (!file.startsWith(site + path.sep)) { response.writeHead(403).end(); return; }
    if (fs.existsSync(file) && fs.statSync(file).isDirectory()) file = path.join(file, 'index.html');
    if (!fs.existsSync(file)) { response.writeHead(404).end(); return; }
    const mime = {'.html': 'text/html', '.js': 'text/javascript', '.css': 'text/css', '.json': 'application/json', '.wasm': 'application/wasm'};
    response.writeHead(200, {'Content-Type': mime[path.extname(file)] || 'application/octet-stream', 'Content-Length': fs.statSync(file).size});
    fs.createReadStream(file).pipe(response);
  });
  await new Promise(resolve => server.listen(0, '127.0.0.1', resolve));
  const base = process.env.BOOK_URL || `http://127.0.0.1:${server.address().port}/lean-algebra/`;
  if (process.env.BOOK_URL) manifest = await (await fetch(new URL('playground.json', base))).json();
  const browser = await playwright.chromium.launch({channel: 'chrome', headless: true});
  try {
    const page = await browser.newPage({viewport: {width: 1360, height: 1000}});
    if (process.env.TRACE_WASM) await page.addInitScript(() => {
      const NativeWorker = Worker;
      window.Worker = class extends NativeWorker {
        constructor(...args) {
          super(...args);
          this.addEventListener('message', ({data}) => {
            console.log('WORKER', JSON.stringify({type: data.type, success: data.success, data: data.data, error: data.error, elapsed: data.elapsed}));
          });
        }
      };
    });
    const errors = [];
    page.on('pageerror', error => { errors.push(error.message); console.error(error.message); });
    page.on('console', message => { if (message.type() === 'error' || process.env.TRACE_WASM) console.error('BROWSER:', message.text()); });
    page.on('requestfailed', request => console.error('REQUEST:', request.url(), request.failure()?.errorText));
    page.on('request', request => { if (request.method() !== 'GET' || request.postData()) uploads.push(request.url()); });
    async function open(selected) {
      await page.goto(new URL(selected.url, base).href);
      const wrapper = page.locator(`[data-snippet="${selected.key}"]`);
      await wrapper.hover();
      await wrapper.getByRole('button', {name: /^(편집|풀기)$/}).click();
      await wrapper.locator('textarea').waitFor();
      return wrapper;
    }
    async function status(wrapper, expected) {
      try {
        const key = await wrapper.getAttribute('data-snippet');
        await page.waitForFunction(({key, expected}) => {
          const text = document.querySelector(`[data-snippet="${key}"] .book-run-status`)?.textContent;
          return text?.includes(expected) || text === '실행 실패' || /^오류 \d+개$/.test(text || '');
        }, {key, expected}, {timeout: 120000});
        assert((await wrapper.locator('.book-run-status').innerText()).includes(expected));
      }
      catch (error) { console.error(await wrapper.locator('.book-live-editor').innerText()); throw error; }
    }
    const selected = example(code => code.startsWith('example {A : Type _} {S T : Set A}') && code.includes('funext x'));
    let wrapper = await open(selected);
    await status(wrapper, '증명 중');
    assert(await page.evaluate(() => crossOriginIsolated));
    const proof = 'example {A : Type _} {S T : Set A}\n    (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T := by\n  funext x\n  apply propext\n  exact h x';
    await wrapper.locator('textarea').fill(proof);
    await status(wrapper, '오류 없음');
    await wrapper.locator('textarea').evaluate(input => {
      const position = input.value.indexOf('funext x') + 'funext x'.length;
      input.setSelectionRange(position, position); input.dispatchEvent(new MouseEvent('click', {bubbles: true}));
    });
    await page.waitForFunction(() => document.querySelector('.book-live-goal')?.textContent.includes('S x = T x'));
    await wrapper.locator('textarea').fill(proof.replace('exact h x', 'exact h'));
    await status(wrapper, '오류 1개');
    assert((await wrapper.locator('.book-diagnostics').innerText()).includes('Type mismatch'));
    await wrapper.getByRole('button', {name: '초기화', exact: true}).click();
    assert.equal((await wrapper.locator('textarea').inputValue()).trimEnd(), selected.data.code.trimEnd());
    console.log('PASS: public editing, real errors, cursor goals, and reset');

    const exercise = example(code => code.startsWith('theorem exercise_add_three_preserves_lt'));
    wrapper = await open(exercise);
    await status(wrapper, '증명 중');
    assert(await wrapper.locator('dialog').isVisible());
    assert((await wrapper.locator('.book-exercise-statement').innerText()).includes('문제 1'));
    assert((await wrapper.locator('.book-exercise-declaration').innerText()).includes('a + 3 < b + 3'));
    assert.equal((await wrapper.locator('textarea').inputValue()).trim(), 'sorry');
    await wrapper.locator('textarea').fill('  ');
    await page.waitForFunction(() => document.querySelector('.book-live-goal')?.textContent.includes('⊢ a + 3 < b + 3'), null, {timeout: 120000});
    await wrapper.locator('textarea').fill('  apply Nat.add_lt_add_right (k := 3)\n  exact h');
    await status(wrapper, '풀이 완료');
    // Full-source mode preserves the proof, and changed statements are not marked solved.
    await wrapper.getByRole('button', {name: '전체 코드', exact: true}).click();
    assert((await wrapper.locator('textarea').inputValue()).startsWith('theorem exercise_'));
    const canonical = await wrapper.locator('textarea').inputValue();
    await wrapper.locator('textarea').fill('theorem exercise_add_three_preserves_lt : True := by\n  trivial');
    await status(wrapper, '코드 검사 통과');
    await wrapper.locator('textarea').fill(canonical);
    await wrapper.getByRole('button', {name: '증명만 편집', exact: true}).click();
    await status(wrapper, '풀이 완료');
    assert(await wrapper.locator('.book-reader-panel').evaluate(panel => panel.getBoundingClientRect().width > 1000));
    const downloadEvent = page.waitForEvent('download');
    await wrapper.getByRole('button', {name: '풀이 내려받기', exact: true}).click();
    const download = await downloadEvent;
    assert(download.suggestedFilename().endsWith('.lean'));
    await download.saveAs('tmp/browser-exercise-download.lean');
    const downloaded = fs.readFileSync('tmp/browser-exercise-download.lean', 'utf8');
    assert(downloaded.includes('import Ample.') && downloaded.includes('exact h'));
    await page.keyboard.press('Escape');
    assert.equal(await wrapper.locator('dialog').isVisible(), false);
    await wrapper.getByRole('button', {name: '풀기', exact: true}).click();
    assert((await wrapper.locator('textarea').inputValue()).includes('exact h'));
    await status(wrapper, '풀이 완료');
    await page.screenshot({path: 'tmp/exercise-workspace-desktop.png'});
    await page.setViewportSize({width: 390, height: 844});
    const layout = await wrapper.locator('dialog').evaluate(dialog => ({
      width: dialog.getBoundingClientRect().width, overflow: dialog.scrollWidth > dialog.clientWidth,
      code: dialog.querySelector('textarea').getBoundingClientRect().bottom,
      goals: dialog.querySelector('.book-live-output').getBoundingClientRect().top,
    }));
    assert(layout.width <= 390 && !layout.overflow && layout.goals >= layout.code, JSON.stringify(layout));
    await page.screenshot({path: 'tmp/exercise-workspace-mobile.png'});
    await page.setViewportSize({width: 1360, height: 1000});
    await page.keyboard.press('Escape');
    await page.reload();
    wrapper = page.locator(`[data-snippet="${exercise.key}"]`);
    await wrapper.getByRole('button', {name: '풀기', exact: true}).click();
    assert((await wrapper.locator('textarea').inputValue()).includes('exact h'));
    await status(wrapper, '풀이 완료');
    await page.keyboard.press('Escape');
    console.log('PASS: proof-only exercise workspace, draft, download, mode switch, and responsive layout');

    const chain = example(code => code.startsWith('theorem exercise_shift_lt '));
    wrapper = await open(chain);
    await status(wrapper, '증명 중');
    await wrapper.locator('textarea').fill('  apply Nat.add_lt_add_right (k := c)\n  exact hab');
    await status(wrapper, '증명 중');
    await wrapper.getByRole('button', {name: '(2)', exact: true}).click();
    await wrapper.locator('textarea').fill('  apply exercise_shift_lt\n  apply exercise_shift_lt\n  exact hab');
    await status(wrapper, '풀이 완료');
    await wrapper.getByRole('button', {name: '(1)', exact: true}).click();
    assert((await wrapper.locator('textarea').inputValue()).includes('(k := c)'));
    await status(wrapper, '풀이 완료');
    await wrapper.locator('textarea').fill('  exact True.intro');
    await status(wrapper, '오류 1개');
    await wrapper.locator('.book-diagnostics .book-error').first().click();
    assert.equal(await wrapper.locator('textarea').evaluate(input => input.selectionStart), 2);
    await page.keyboard.press('Escape');
    console.log('PASS: dependent subproblems, combined checking, and diagnostic cursor mapping');

    const cantor = example(code => code.startsWith('theorem cantor_not_surjective '));
    wrapper = await open(cantor);
    await status(wrapper, '오류 없음');
    console.log('PASS: the infinite-cardinality chapter and diagonal argument');

    const concrete = example(code => code.startsWith('theorem cardinal_fin '));
    wrapper = await open(concrete);
    await status(wrapper, '오류 없음');
    await wrapper.locator('textarea').evaluate(input => {
      input.setSelectionRange(input.value.indexOf('rfl'), input.value.indexOf('rfl'));
      input.dispatchEvent(new MouseEvent('click', {bubbles: true}));
    });
    await page.waitForFunction(() => document.querySelector('.book-live-goal')?.textContent.includes('n : Nat'));
    const state = await wrapper.locator('.book-live-goal').innerText();
    assert(!/\b[A-C] : Type|\bm : Nat/.test(state), state);
    await page.screenshot({path: 'tmp/public-browser-editor.png'});
    assert.deepEqual(uploads, [], 'Proof text must stay in the browser');
    assert.deepEqual(errors, []);
    console.log('PASS: actual cardinality context, required variables only, no compiler server');
  } finally {
    await browser.close(); server.closeAllConnections();
    await new Promise(resolve => server.close(resolve));
  }
}
main().catch(error => {console.error(error); process.exitCode = 1;});
