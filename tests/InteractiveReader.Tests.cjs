/* Exercise the real reader controls and Lean requests, including a corrected proof. */
const assert = require('node:assert/strict');
const path = require('node:path');
let playwright;
try { playwright = require('playwright'); }
catch { playwright = require(path.join(process.env.USERPROFILE, '.cache/codex-runtimes/codex-primary-runtime/dependencies/node/node_modules/playwright')); }
const {chromium} = playwright;
const base = process.env.BOOK_URL || 'http://127.0.0.1:8001';

async function main() {
  const browser = await chromium.launch({headless: true,
    executablePath: process.env.CHROME_PATH || (process.platform === 'win32' ? 'C:/Program Files/Google/Chrome/Application/chrome.exe' : undefined)});
  try {
    const page = await browser.newPage({viewport: {width: 1360, height: 1000}});
    const errors = [];
    page.on('pageerror', error => errors.push(error.message));
    await page.goto(base + '/foundations/sets/equality/#sets-proposition-extensionality');
    await page.evaluate(() => document.fonts.ready);
    await page.locator('#sets-proposition-extensionality').evaluate(el => el.scrollIntoView({block:'start'}));
    await page.evaluate(() => window.scrollBy(0, -70));
    await page.screenshot({path: 'tmp/interactive-reader-default.png'});

    const complete = page.locator('.book-example').filter({hasText: '@[ext] theorem set_ext'});
    assert.equal(await complete.count(), 1);
    // Clicking the tactic itself opens its state without a toolbar prerequisite.
    await complete.locator('.tactic > label').filter({hasText: /^funext x$/}).click();
    assert.ok((await complete.locator('.book-step-state').innerText()).includes('S x = T x'));
    await complete.getByRole('button', {name: '← 이전', exact: true}).click();
    assert.ok((await complete.locator('.book-step-state').innerText()).includes('S = T'));
    await complete.getByRole('button', {name: '다음 →', exact: true}).click();
    await complete.getByRole('button', {name: '다음 →', exact: true}).click();
    assert.ok((await complete.locator('.book-step-state').innerText()).includes('S x ↔ T x'));
    await complete.getByRole('button', {name: '다음 →', exact: true}).click();
    assert.equal((await complete.locator('.book-step-state').innerText()).trim(), '남은 목표 없음');
    await complete.getByRole('button', {name: '← 이전', exact: true}).click();
    assert.ok((await complete.locator('.book-step-state').innerText()).includes('S x ↔ T x'));
    await complete.screenshot({path: 'tmp/interactive-reader-steps.png'});

    const manifest = await (await page.request.get(base + '/playground.json')).json();
    const attemptKey = Object.entries(manifest).find(([, entry]) =>
      entry.code.startsWith('example {A : Type _} {S T : Set A}') && entry.code.includes('funext x'))[0];
    const attempt = page.locator(`[data-snippet="${attemptKey}"]`);
    await attempt.hover();
    await attempt.getByRole('button', {name: '편집', exact: true}).click();
    const input = attempt.locator('textarea');
    const original = await input.inputValue();
    assert.ok(original.startsWith('example {A : Type _} {S T : Set A}'), original);
    const proof = original.trimEnd() + '\n  apply propext\n  exact h x';
    await input.fill(proof);
    // Editing alone must trigger elaboration; no explicit run is needed.
    await page.waitForFunction(() => [...document.querySelectorAll('.book-run-status')].some(el => el.textContent === '오류 없음'), null, {timeout: 60000});
    await input.evaluate(el => {
      const rows = el.value.split('\n');
      const index = rows.findIndex(line => line.trim() === 'funext x');
      const position = rows.slice(0, index).reduce((n, row) => n + row.length + 1, 0) + rows[index].length;
      el.focus(); el.setSelectionRange(position, position); el.dispatchEvent(new MouseEvent('click', {bubbles: true}));
    });
    await page.waitForFunction(() => document.querySelector('.book-live-goal')?.textContent.includes('S x = T x'), null, {timeout: 15000});
    await attempt.screenshot({path: 'tmp/interactive-reader-editor.png'});
    await input.fill(proof.replace('exact h x', 'exact h'));
    await page.waitForFunction(() => [...document.querySelectorAll('.book-run-status')].some(el => /오류 \d+개/.test(el.textContent)), null, {timeout: 60000});
    assert.ok((await attempt.locator('.book-diagnostics').innerText()).includes('Type mismatch'));

    await page.reload();
    const restored = page.locator(`[data-snippet="${attemptKey}"]`);
    await restored.hover();
    await restored.getByRole('button', {name: '편집', exact: true}).click();
    assert.ok((await restored.locator('textarea').inputValue()).endsWith('exact h'));
    await restored.getByRole('button', {name: '초기화', exact: true}).click();
    assert.equal((await restored.locator('textarea').inputValue()).trimEnd(), original.trimEnd());

    await page.goto(base + '/foundations/using-proofs/exercises/');
    const solutions = page.locator('details.book-disclosure').filter({has: page.locator('summary', {hasText: '풀이'})});
    assert.equal(await solutions.count(), 4);
    assert.equal(await solutions.first().getAttribute('open'), null);
    await solutions.first().locator('summary').click();
    assert.equal(await solutions.first().getAttribute('open'), '');
    await solutions.first().locator('summary').click();
    assert.equal(await solutions.first().getAttribute('open'), null);
    const exerciseKey = Object.entries(manifest).find(([, entry]) =>
      entry.code.startsWith('theorem exercise_add_three_preserves_lt'))[0];
    const exercise = page.locator(`[data-snippet="${exerciseKey}"]`);
    await exercise.hover();
    await exercise.getByRole('button', {name: '편집', exact: true}).click();
    const exerciseInput = exercise.locator('textarea');
    await exerciseInput.fill((await exerciseInput.inputValue()).replace('  sorry', '  '));
    await page.waitForFunction(() => [...document.querySelectorAll('.book-live-goal')].some(el =>
      el.textContent.includes('⊢ a + 3 < b + 3')), null, {timeout: 60000});
    await page.waitForFunction(() => document.querySelector('.book-run-status')?.textContent === '증명 중', null, {timeout: 15000});
    assert.equal(await exercise.locator('.book-diagnostics .book-error').count(), 0);
    assert.ok(!(await exercise.locator('.book-diagnostics').innerText()).includes('unsolved goals'));
    // Real language-server completion supplies the theorem and its signature.
    const unfinished = await exerciseInput.inputValue();
    await exerciseInput.fill(unfinished + '-- \\[[]]');
    await exerciseInput.press('Tab');
    assert.ok((await exerciseInput.inputValue()).endsWith('-- ⟦⟧'));
    assert.equal(await exerciseInput.evaluate(el => el.selectionStart), (await exerciseInput.inputValue()).length - 1);
    await exerciseInput.fill(unfinished + 'apply Nat.add_lt_add_r');
    await exerciseInput.press('Control+Space');
    const candidate = exercise.getByRole('option', {name: 'add_lt_add_right', exact: true});
    await candidate.waitFor({timeout: 60000});
    await page.waitForFunction(() => document.querySelector('.book-completion-detail')?.textContent.includes('n + k < m + k'), null, {timeout: 15000});
    await exercise.screenshot({path: 'tmp/interactive-reader-completion.png'});
    await exerciseInput.press('ArrowDown');
    assert.equal(await candidate.getAttribute('aria-selected'), 'false');
    await exerciseInput.press('ArrowUp');
    assert.equal(await candidate.getAttribute('aria-selected'), 'true');
    await exerciseInput.press('Tab');
    assert.ok((await exerciseInput.inputValue()).endsWith('apply Nat.add_lt_add_right'));
    assert.equal(await exercise.locator('.book-completion').isVisible(), false);
    // Typing without a shortcut also opens completion; Escape dismisses it.
    await exerciseInput.fill(unfinished + 'apply Nat.add_lt_add_r');
    await candidate.waitFor({timeout: 60000});
    await exerciseInput.press('Escape');
    assert.equal(await exercise.locator('.book-completion').isVisible(), false);
    await exerciseInput.fill(unfinished);
    await exerciseInput.fill((await exerciseInput.inputValue()) + 'apply Nat.add_lt_add_right\n  ');
    await page.waitForFunction(() => [...document.querySelectorAll('.book-live-goal')].some(el =>
      el.textContent.includes('⊢ a < b')), null, {timeout: 60000});
    await page.goto(base + '/foundations/cardinality/exercises/');
    assert.ok(await page.locator('details.book-disclosure').count());

    const mobile = await browser.newPage({viewport: {width: 390, height: 844}, isMobile: true, hasTouch: true});
    await mobile.goto(base + '/foundations/sets/equality/#sets-proposition-extensionality');
    const small = mobile.locator(`[data-snippet="${attemptKey}"]`);
    await small.getByRole('button', {name: '편집', exact: true}).click();
    await small.locator('textarea').waitFor();
    const bounds = await small.boundingBox();
    assert.ok(bounds.width <= 390, JSON.stringify(bounds));
    await small.screenshot({path: 'tmp/interactive-reader-mobile.png'});
    assert.deepEqual(errors, []);
    console.log('PASS: click-to-open steps, unfinished goals vs real errors, Lean completion/types, auto checking, drafts, reset, disclosures, and mobile controls');
  } finally { await browser.close(); }
}
main().catch(error => {console.error(error); process.exit(1);});
