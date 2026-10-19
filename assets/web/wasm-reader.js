import {createLeanRuntime} from './lean-wasm.js';

// Keep the reader's request/response contract; execution stays in one Worker.
export function createBrowserBackend(siteRoot) {
  const runtime = createLeanRuntime(new URL(document.querySelector('meta[name="lean-wasm-base"]').content, siteRoot), message => {
    const count = /Loading library packs: (\d+\/\d+)/.exec(message)?.[1];
    window.dispatchEvent(new CustomEvent('book-lean-progress', {
      detail: count ? `Lean 파일을 불러오는 중 (${count})…` : 'Lean을 준비하는 중…',
    }));
  });
  let boot;
  let queue = Promise.resolve();
  let currentSource;
  let currentResult;
  let serial = 0;
  const sessions = new Map();
  const snippets = new Map();

  async function isolate(key) {
    if (crossOriginIsolated) return;
    if (!isSecureContext || !navigator.serviceWorker) {
      throw new Error('이 브라우저에서는 Lean을 실행할 수 없습니다. 최신 데스크톱 Chrome 또는 Firefox를 사용해 주세요.');
    }
    sessionStorage.setItem('lean-algebra.reopen', key);
    let reloading = false;
    window.coi = {async doReload() {
      if (reloading) return;
      reloading = true;
      const registration = await navigator.serviceWorker.ready;
      const worker = registration.active;
      if (worker.state !== 'activated') await new Promise(resolve => worker.addEventListener('statechange', () => {
        if (worker.state === 'activated') resolve();
      }));
      location.reload();
    }};
    await new Promise((_, reject) => {
      const script = document.createElement('script');
      script.src = new URL('coi-serviceworker.js', siteRoot);
      script.onload = () => window.coi.doReload().catch(reject);
      script.onerror = () => reject(new Error('Lean 실행 환경을 불러오지 못했습니다. 페이지를 새로고침해 주세요.'));
      document.head.append(script);
      setTimeout(() => reject(new Error('Lean 실행 환경을 준비하지 못했습니다. 페이지를 새로고침해 주세요.')), 30000);
    });
  }
  function closeScopes(source) {
    const scopes = [];
    for (const line of source.split('\n')) {
      const open = /^(?:namespace|section)(?:\s+(\S+))?\s*$/.exec(line);
      if (open) scopes.push(open[1] || '');
      else if (/^end(?:\s+\S+)?\s*$/.test(line)) scopes.pop();
    }
    return '\n' + scopes.reverse().map(name => `end${name ? ' ' + name : ''}\n`).join('');
  }
  async function compile(document) {
    if (currentSource === document.source) return currentResult;
    const result = await runtime.compile(document.source);
    if (!result.success) throw new Error('Lean 실행이 중단되었습니다. 페이지를 새로고침해 주세요.');
    currentSource = document.source;
    currentResult = result;
    document.result = result;
    return result;
  }
  async function goals(document, position) {
    await compile(document);
    const state = await runtime.goalsAt(document.offset + position.line, position.character);
    return state.found ? state.goals : null;
  }
  async function execute(path, payload) {
    if (path === '/api/lean/check') {
      await isolate(payload.snippet);
      boot ||= runtime.boot();
      await boot;
      if (!snippets.has(payload.snippet)) {
        const response = await fetch(new URL(`playground/${payload.snippet}.json`, siteRoot));
        if (!response.ok) throw new Error('예제의 실행 환경을 불러오지 못했습니다.');
        snippets.set(payload.snippet, await response.json());
      }
      const prefix = snippets.get(payload.snippet).before.trimEnd() + '\n\n';
      const token = sessions.has(payload.session) ? payload.session : `wasm-${++serial}`;
      const previous = sessions.get(token);
      const source = prefix + payload.code + (payload.code.endsWith('\n') ? '' : '\n');
      const document = {source: source + closeScopes(source), code: payload.code,
        offset: prefix.split('\n').length - 1, version: (previous?.version || 0) + 1};
      // The public reader has one active editor. Bound retained source strings.
      sessions.clear();
      sessions.set(token, document);
      const result = await compile(document);
      const diagnostics = [];
      const contextErrors = [];
      for (const line of result.output) {
        let item;
        try { item = JSON.parse(line); } catch { continue; }
        const row = (item.pos?.line || 1) - document.offset;
        if (row < 1) {
          if (item.severity === 'error') contextErrors.push(item.data);
          continue;
        }
        const unfinished = item.kind === 'Tactic.unsolvedGoals' || item.kind === 'hasSorry'
          || /declaration uses [`']sorry[`']/.test(item.data || '');
        diagnostics.push({line: row, column: (item.pos?.column || 0) + 1,
          severity: item.severity === 'error' ? 1 : item.severity === 'warning' ? 2 : 3,
          kind: unfinished ? 'unfinished' : 'diagnostic', message: item.data, isSilent: item.isSilent});
      }
      return {session: token, version: document.version, diagnostics, contextErrors,
        goal: await goals(document, payload.position || {line: 0, character: 0})};
    }
    const document = sessions.get(payload.session);
    if (!document || document.version !== payload.version) throw new Error('The code changed. Run this example again.');
    if (path === '/api/lean/goal') return {goal: await goals(document, payload.position)};
    throw new Error('This browser editor does not yet provide Lean completion.');
  }
  return {call(path, payload) {
    const task = queue.catch(() => {}).then(() => execute(path, payload));
    queue = task;
    return task;
  }};
}
