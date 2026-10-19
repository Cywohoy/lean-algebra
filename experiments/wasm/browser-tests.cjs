const assert = require('node:assert/strict');
const fs = require('node:fs/promises');
const path = require('node:path');
const {createServer, ample} = require('./server.cjs');
let playwright;
try { playwright = require('playwright'); }
catch { playwright = require(path.join(process.env.USERPROFILE, '.cache/codex-runtimes/codex-primary-runtime/dependencies/node/node_modules/playwright')); }

async function main() {
  const useServiceWorker = process.argv.includes('--service-worker');
  const server = await createServer({isolate: !useServiceWorker});
  const browser = await playwright.chromium.launch({channel: 'chrome', headless: true});
  const report = {testedAt: new Date().toISOString(), browser: browser.version(), useServiceWorker, cases: []};
  try {
    const page = await browser.newPage();
    const proofRequests = [];
    page.on('request', request => {
      if (request.method() !== 'GET' || request.postData()) proofRequests.push(request.url());
    });
    page.on('pageerror', error => console.error('PAGE:', error.message));
    await page.goto(`http://127.0.0.1:${server.address().port}/`);
    report.beforeServiceWorker = await page.evaluate(() => crossOriginIsolated);
    if (useServiceWorker) {
      assert.equal(report.beforeServiceWorker, false);
      await page.goto(`http://127.0.0.1:${server.address().port}/?coi`);
      await page.waitForFunction(() => crossOriginIsolated && !!window.wasmExperiment);
    }
    report.isolated = await page.evaluate(() => crossOriginIsolated);
    assert.equal(report.isolated, true);
    console.log('Booting the actual browser Worker…');
    report.boot = await page.evaluate(() => wasmExperiment.boot());
    console.log(`Ready: ${Math.round(report.boot.bootMs)} ms`);

    const sets = await fs.readFile(path.join(ample, 'Ample/Math/Sets.lean'), 'utf8');
    // Named boundaries below keep the source sample independent of later custom tactics.
    const transStart = sets.indexOf('theorem subset_trans ');
    const transLastLine = sets.indexOf('exact hTUx hxT', transStart);
    const transEnd = transLastLine + 'exact hTUx hxT'.length;
    const publicSetSample = 'namespace Ample\n' + sets.slice(sets.indexOf('def Set ('), sets.indexOf('example : 3'))
      + sets.slice(sets.indexOf('def Subset '), sets.indexOf('theorem subset_refl'))
      + sets.slice(transStart, transEnd) + '\nend Ample';
    assert(transStart >= 0 && transLastLine > transStart, 'Ample sample boundaries changed');
    const cases = [
      ['implication', 'theorem sample (P Q : Prop) (h : P → Q) (hp : P) : Q := by\n  apply h\n  exact hp', 'ok'],
      ['arithmetic', 'example (n : Nat) : 2 * n ≠ 5 := by\n  omega', 'ok'],
      ['public-set-proof', publicSetSample, 'ok'],
      ['false-equality', 'example : 2 + 2 = 5 := by\n  rfl', 'error'],
      ['unfinished-goal', 'theorem sample (P Q : Prop) : P → Q := by\n  intro hp', 'error'],
      ['explicit-goal-trace', 'theorem sample (P : Prop) : P → P := by\n  intro hp\n  trace_state\n  exact hp', 'ok'],
      ['custom-macro', 'macro "finish_trivial" : tactic => `(tactic| exact True.intro)\nexample : True := by finish_trivial', 'probe'],
      ['lean-import', 'import Lean\n#check Lean.Elab.Tactic.evalTactic', 'probe'],
      ['native-ample-import', 'import Ample.Tactic.Classical\nopen Ample\nexample (P : Prop) (h : ¬¬P) : P := by\n  by_contra hn\n  exact h hn', 'probe'],
    ];
    for (const [name, code, expect] of cases) {
      console.log(`Running: ${name}`);
      const result = await page.evaluate(code => wasmExperiment.compile(code), code);
      const diagnostics = result.output.flatMap(line => { try { return [JSON.parse(line)]; } catch { return []; } });
      const errors = diagnostics.filter(item => item.severity === 'error');
      const accepted = result.success && errors.length === 0;
      report.cases.push({name, code, ...result, accepted, diagnostics});
      console.log(JSON.stringify({name, accepted, ms: Math.round(result.wallMs), output: result.output}));
      if (expect === 'ok') assert(accepted, `${name} rejected`);
      if (expect === 'error') assert(!accepted, `${name} was incorrectly accepted`);
      if (name === 'unfinished-goal') assert(result.output.join('\n').includes('⊢ Q'));
      if (name === 'explicit-goal-trace') assert(result.output.join('\n').includes('⊢ P'));
      if (name === 'native-ample-import') assert(result.output.join('\n').includes('incompatible header'));
    }
    assert.deepEqual(proofRequests, [], 'Proof text must not be submitted to the static server');
    report.proofSubmissionRequests = proofRequests;
  } finally {
    const out = path.resolve(__dirname, `../../tmp/wasm/browser-results${useServiceWorker ? '-sw' : ''}.json`);
    await fs.writeFile(out, JSON.stringify(report, null, 2) + '\n');
    await browser.close();
    server.closeAllConnections();
    await new Promise(resolve => server.close(resolve));
    console.log(`Report: ${out}`);
  }
}
main().catch(error => { console.error(error); process.exitCode = 1; });
