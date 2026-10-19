/* Interactive reading and a local Lean playground. No third-party scripts. */
(() => {
  'use strict';
  const siteRoot = new URL('.', document.baseURI);
  const staticReading = document.querySelector('meta[name="book-mode"]')?.content === 'static';
  const browserLean = document.querySelector('meta[name="book-mode"]')?.content === 'wasm';
  let browserBackend;
  const snippets = new Map();
  let backend;
  let activeEditor;
  let panelCounter = 0;
  const element = (tag, className, text) => {
    const node = document.createElement(tag);
    if (className) node.className = className;
    if (text !== undefined) node.textContent = text;
    return node;
  };
  const button = (text, action, className = '') => {
    const node = element('button', `book-button ${className}`, text);
    node.type = 'button';
    node.addEventListener('click', action);
    return node;
  };
  const plain = node => {
    const clone = node.cloneNode(true);
    clone.querySelectorAll('.tactic-state, .tactic-toggle, .hover-container, .hover-info').forEach(el => el.remove());
    return clone.textContent;
  };
  async function snippet(key) {
    if (!snippets.has(key)) {
      snippets.set(key, fetch(new URL(`playground/${key}.json`, siteRoot)).then(response => {
        if (!response.ok) throw new Error('코드를 불러오지 못했습니다. 페이지를 새로고침해 주세요.');
        return response.json();
      }).catch(error => { snippets.delete(key); throw error; }));
    }
    return snippets.get(key);
  }
  function stored(key) { try { return localStorage.getItem(key); } catch { return null; } }
  function store(key, value) { try { localStorage.setItem(key, value); } catch { /* Private browsing may disable storage. */ } }
  function tabSession(value) {
    try {
      if (value) sessionStorage.setItem('lean-algebra.session', value);
      return sessionStorage.getItem('lean-algebra.session');
    } catch { return null; }
  }
  async function endpoint() {
    if (backend) return backend;
    const candidates = [location.origin];
    if (['127.0.0.1', 'localhost'].includes(location.hostname)) {
      candidates.push(`http://${location.hostname}:8001`);
    }
    for (const candidate of new Set(candidates)) {
      try {
        const response = await fetch(`${candidate}/api/lean/status`, {signal: AbortSignal.timeout(2500)});
        if (response.ok && (await response.json()).available) return (backend = candidate);
      } catch { /* Try the local companion server, when present. */ }
    }
    throw new Error('Lean 서버에 연결할 수 없습니다. interactive-preview.bat를 실행해 주세요.');
  }
  async function call(path, payload) {
    if (browserLean) {
      browserBackend ||= import(new URL('assets/web/wasm-reader.js', siteRoot))
        .then(module => module.createBrowserBackend(siteRoot));
      return (await browserBackend).call(path, payload);
    }
    const base = await endpoint();
    const response = await fetch(base + path, {
      method: 'POST', headers: {'Content-Type': 'application/json'}, body: JSON.stringify(payload),
    });
    const data = await response.json();
    if (!response.ok) throw new Error(data.error || 'Lean request failed.');
    return data;
  }

  // Keep both branch-local states and the outer state after a nested `have`.
  function proofSteps(code) {
    const steps = [];
    const walk = tactic => {
      const label = tactic.querySelector(':scope > label');
      const state = tactic.querySelector(':scope > .tactic-state');
      if (!label || !state) return;
      const children = [...label.querySelectorAll('.tactic')].filter(child => child.parentElement.closest('.tactic') === tactic);
      children.forEach(walk);
      const first = plain(label).trim().split('\n')[0].trim();
      if (!children.length || /^(have|suffices)\b/.test(first)) steps.push({label, state, title: first});
    };
    [...code.querySelectorAll('.tactic')].filter(node => !node.parentElement.closest('.tactic')).forEach(walk);
    return steps;
  }

  function decorate(wrapper) {
    const source = wrapper.querySelector('.hl.lean.block');
    if (!source || wrapper.dataset.readerReady) return;
    if (!/\b(def|theorem|lemma|example|structure|inductive|instance)\b/.test(plain(source))) return;
    wrapper.dataset.readerReady = 'true';
    const key = wrapper.dataset.snippet;
    const steps = proofSteps(source);
    const toolbar = element('div', 'book-toolbar');
    toolbar.setAttribute('aria-label', '예제 도구');
    const kind = element('span', 'book-example-kind', /\bsorry\b/.test(plain(source)) ? '연습문제' : 'Lean');
    toolbar.append(kind);
    const body = element('div', 'book-example-body');
    source.before(body);
    body.append(source);
    wrapper.prepend(toolbar);
    const panel = element('section', 'book-reader-panel');
    panel.id = `book-panel-${++panelCounter}`;
    panel.hidden = true;
    body.append(panel);
    let mode = null;
    let stepIndex = 0;
    let editor;
    let selectStep;
    const status = element('span', 'book-toolbar-status');
    status.setAttribute('role', 'status');
    let stepButton;
    const editButton = button('편집', () => setMode(mode === 'edit' ? null : 'edit'));
    if (browserLean) editButton.title = '브라우저에서 Lean을 실행합니다. 첫 실행 시 약 300 MB를 내려받습니다.';
    const copyButton = button('복사', async () => {
      try {
        const text = mode === 'edit' && editor ? editor.input.value : (await snippet(key)).code;
        await navigator.clipboard.writeText(text);
        status.textContent = '복사됨';
      } catch { status.textContent = '복사 실패'; }
    }, 'book-copy');
    if (steps.length) {
      stepButton = button('단계', () => setMode(mode === 'steps' ? null : 'steps'));
      toolbar.append(stepButton);
    }
    if (!staticReading) toolbar.append(editButton);
    toolbar.append(copyButton, status);
    for (const control of [stepButton, editButton].filter(Boolean)) {
      control.setAttribute('aria-controls', panel.id);
      control.setAttribute('aria-expanded', 'false');
    }

    function showSteps() {
      const heading = element('div', 'book-panel-heading');
      heading.append(element('strong', '', '가정과 목표'));
      const state = element('div', 'book-step-state hl lean');
      state.setAttribute('aria-live', 'polite');
      const controls = element('div', 'book-step-controls');
      const previous = button('← 이전', () => show(stepIndex - 1));
      const next = button('다음 →', () => show(stepIndex + 1));
      const count = element('span', 'book-step-count');
      const title = element('code', 'book-step-title');
      controls.append(previous, count, next);
      const header = element('div', 'book-step-header');
      header.append(heading, controls);
      panel.append(header, title, state);
      function show(index) {
        stepIndex = Math.max(0, Math.min(index, steps.length - 1));
        source.querySelectorAll('.book-current-step').forEach(node => node.classList.remove('book-current-step'));
        const step = steps[stepIndex];
        step.label.classList.add('book-current-step');
        const selected = step.label.getBoundingClientRect();
        const viewport = source.getBoundingClientRect();
        if (selected.top < viewport.top) source.scrollTop -= viewport.top - selected.top;
        else if (selected.bottom > viewport.bottom) source.scrollTop += selected.bottom - viewport.bottom;
        const clone = step.state.cloneNode(true);
        clone.removeAttribute('id');
        clone.querySelectorAll('[id]').forEach(node => node.removeAttribute('id'));
        clone.style.display = 'block';
        if (!clone.querySelector('.goal')) clone.textContent = '남은 목표 없음';
        state.replaceChildren(clone);
        title.textContent = step.title;
        count.textContent = `${stepIndex + 1} / ${steps.length}`;
        previous.disabled = stepIndex === 0;
        next.disabled = stepIndex === steps.length - 1;
      }
      selectStep = show;
      show(stepIndex);
    }

    async function setMode(next) {
      if (next === 'edit') {
        if (activeEditor && activeEditor.wrapper !== wrapper) activeEditor.close();
        activeEditor = {wrapper, close: () => setMode(null)};
      } else if (activeEditor?.wrapper === wrapper) activeEditor = null;
      mode = next;
      wrapper.classList.toggle('book-reading', mode === 'steps');
      wrapper.classList.toggle('book-editing', mode === 'edit');
      panel.hidden = !mode;
      if (stepButton) stepButton.setAttribute('aria-expanded', String(mode === 'steps'));
      editButton.setAttribute('aria-expanded', String(mode === 'edit'));
      source.querySelectorAll('.tactic-toggle').forEach(toggle => { toggle.checked = false; });
      source.querySelectorAll('.book-current-step').forEach(node => node.classList.remove('book-current-step'));
      panel.replaceChildren();
      if (mode === 'steps') showSteps();
      if (mode === 'edit') {
        panel.append(element('p', 'book-help', '불러오는 중…'));
        try {
          const data = await snippet(key);
          if (mode !== 'edit') return;
          panel.replaceChildren();
          editor ||= createEditor(key, data);
          panel.append(editor.root);
          editor.input.focus();
          editor.activate();
        } catch (error) { panel.replaceChildren(element('p', 'book-error', error.message)); }
      }
    }
    source.addEventListener('click', event => {
      if (!steps.length || event.target.closest('a[href]') || event.ctrlKey || event.metaKey) return;
      if (window.getSelection()?.toString()) return;
      const label = event.target.closest('.tactic > label');
      const index = steps.findIndex(step => step.label === label);
      event.preventDefault();
      event.stopPropagation();
      if (mode !== 'steps') setMode('steps');
      selectStep(index >= 0 ? index : stepIndex);
    }, true);
    if (steps.length) {
      source.tabIndex = 0;
      source.setAttribute('aria-label', 'Lean 증명. 누르면 단계별 가정과 목표를 볼 수 있습니다.');
      source.addEventListener('keydown', event => {
        if (event.target !== source || !['Enter', ' '].includes(event.key)) return;
        event.preventDefault();
        setMode(mode === 'steps' ? null : 'steps');
      });
    }
  }

  function createEditor(key, original) {
    const root = element('div', 'book-live-editor');
    const controls = element('div', 'book-editor-controls');
    const input = element('textarea', 'book-code-input');
    input.setAttribute('aria-label', '수정할 Lean 코드');
    input.spellcheck = false;
    input.autocapitalize = 'off';
    input.autocomplete = 'off';
    input.wrap = 'off';
    const storageKey = `lean-algebra.code.${key}`;
    input.value = stored(storageKey) ?? original.code.trimEnd();
    const message = element('span', 'book-run-status', '대기 중');
    message.setAttribute('role', 'status');
    const run = button('실행', check, 'book-primary');
    const reset = button('초기화', () => {
      input.value = original.code.trimEnd();
      changed();
      input.focus();
    });
    controls.append(run, reset, message);
    const columns = element('div', 'book-editor-columns');
    const codePane = element('div', 'book-edit-code');
    const gutter = element('pre', 'book-line-numbers');
    gutter.setAttribute('aria-hidden', 'true');
    codePane.append(gutter, input);
    const completion = element('div', 'book-completion');
    completion.hidden = true;
    const choices = element('div', 'book-completion-list');
    choices.id = `book-completion-${++panelCounter}`;
    choices.setAttribute('role', 'listbox');
    choices.setAttribute('aria-label', 'Lean 자동완성');
    const signature = element('pre', 'book-completion-detail');
    completion.append(choices, signature);
    codePane.append(completion);
    input.setAttribute('aria-autocomplete', 'list');
    input.setAttribute('aria-controls', choices.id);
    input.setAttribute('aria-expanded', 'false');
    const output = element('section', 'book-live-output');
    output.setAttribute('aria-label', 'Lean 실행 결과');
    const outputHeading = element('strong', 'book-panel-heading', '가정과 목표');
    const goal = element('pre', 'book-live-goal', '실행 후 코드 위치를 선택하면 가정과 목표가 표시됩니다.');
    const diagnostics = element('div', 'book-diagnostics');
    output.append(outputHeading, goal, diagnostics);
    columns.append(codePane, output);
    root.append(controls, columns, element('p', 'book-help',
      browserLean ? '브라우저 실행 · 첫 실행 시 약 300 MB 다운로드 · Ctrl+Enter 실행 · \\forall + Tab → ∀'
        : '자동 실행 · Ctrl+Space 자동완성 · Ctrl+Enter 즉시 실행 · \\forall + Tab → ∀'));
    if (browserLean) window.addEventListener('book-lean-progress', event => {
      if (busy && root.isConnected) message.textContent = event.detail;
    });
    let session;
    let version;
    let checkedCode;
    let busy = false;
    let timer;
    let compileTimer;
    let activated = false;
    let requestNumber = 0;
    let documentQueue = Promise.resolve();
    let completionTimer;
    let detailTimer;
    let completionNumber = 0;
    let completionResult;
    let completionCode;
    let completionCursor;
    let selectedChoice = 0;
    let composing = false;
    // Serialize edits to the same LSP document. Skip queued requests for text
    // that has already changed instead of sending an older document to Lean.
    function documentCall(path, code, payload) {
      const task = documentQueue.catch(() => {}).then(async () => {
        if (input.value !== code || !root.isConnected) return null;
        const result = await call(path, {snippet: key, code, session: session || tabSession(), ...payload});
        session = result.session;
        tabSession(session);
        version = result.version;
        return result;
      });
      documentQueue = task;
      return task;
    }
    function position() {
      const before = input.value.slice(0, input.selectionStart);
      const lines = before.split('\n');
      return {line: lines.length - 1, character: lines.at(-1).length};
    }
    function lines() {
      gutter.textContent = Array.from({length: input.value.split('\n').length}, (_, i) => i + 1).join('\n');
      const narrow = window.matchMedia('(max-width: 640px)').matches;
      input.wrap = narrow ? 'soft' : 'off';
      input.style.height = narrow ? 'auto' : `${Math.min(680, Math.max(200, input.value.split('\n').length * 28 + 24))}px`;
      if (narrow) input.style.height = `${Math.min(680, Math.max(200, input.scrollHeight))}px`;
    }
    function scheduleCheck(delay = 650) {
      clearTimeout(compileTimer);
      compileTimer = setTimeout(check, delay);
    }
    function changed() {
      hideCompletions();
      store(storageKey, input.value);
      message.textContent = '수정됨';
      message.className = 'book-run-status';
      ++requestNumber;
      lines();
      scheduleCheck();
      const prefix = input.value.slice(0, input.selectionStart);
      if (composing || !input.matches(':focus') || input.selectionStart !== input.selectionEnd || /\\[^\s]*$/.test(prefix)) return;
      if (!browserLean && /[\p{L}_][\p{L}\p{N}_']{1,}$|[\p{L}\p{N}_']\.$/u.test(prefix)) {
        completionTimer = setTimeout(() => complete(false), 220);
      }
    }
    function showGoal(value) {
      goal.textContent = value === null ? '이 위치에는 표시할 목표가 없습니다.'
        : value.length ? value.join('\n\n') : '남은 목표 없음';
    }
    async function check() {
      clearTimeout(compileTimer);
      if (busy || !root.isConnected) return;
      busy = true;
      run.disabled = true;
      message.textContent = '실행 중…';
      message.className = 'book-run-status';
      const code = input.value;
      ++requestNumber;
      try {
        const result = await documentCall('/api/lean/check', code, {position: position()});
        if (!result) return;
        checkedCode = code;
        if (code !== input.value) return;
        showGoal(result.goal);
        diagnostics.replaceChildren();
        for (const item of result.diagnostics) {
          if (item.kind === 'unfinished' || item.isSilent) continue;
          const diagnostic = button(`${item.line}:${item.column}  ${item.message}`, () => {
            const start = input.value.split('\n').slice(0, item.line - 1).reduce((n, line) => n + line.length + 1, 0);
            input.focus();
            input.setSelectionRange(start + item.column - 1, start + item.column - 1);
            updateGoal();
          }, item.severity === 1 ? 'book-error' : 'book-warning');
          diagnostics.append(diagnostic);
        }
        if (result.contextErrors.length) {
          throw new Error('이 예제에 필요한 정의를 불러오지 못했습니다.\n' + result.contextErrors.join('\n'));
        }
        const errors = result.diagnostics.filter(item => item.severity === 1 && item.kind !== 'unfinished');
        const holes = result.diagnostics.some(item => item.kind === 'unfinished');
        message.textContent = errors.length ? `오류 ${errors.length}개` : holes ? '증명 중' : '오류 없음';
        message.classList.toggle('book-error', !!errors.length);
        message.classList.toggle('book-success', !errors.length && !holes);
      } catch (error) {
        if (code === input.value) {
          message.textContent = '실행 실패';
          diagnostics.replaceChildren(element('p', 'book-error', error.message));
        }
      } finally {
        busy = false;
        run.disabled = false;
        if (input.value !== code) scheduleCheck(250);
        else if (checkedCode === code) updateGoal();
      }
    }
    async function updateGoal() {
      clearTimeout(timer);
      if (busy || !root.isConnected || !session || checkedCode !== input.value) return;
      const current = ++requestNumber;
      timer = setTimeout(async () => {
        try {
          const result = await call('/api/lean/goal', {session, version, position: position()});
          if (current === requestNumber && checkedCode === input.value) showGoal(result.goal);
        } catch (error) {
          if (root.isConnected && /Run this example|code changed/.test(error.message)) {
            checkedCode = undefined;
            scheduleCheck(50);
          }
        }
      }, 180);
    }
    function hideCompletions() {
      clearTimeout(completionTimer);
      clearTimeout(detailTimer);
      ++completionNumber;
      completion.hidden = true;
      completionResult = undefined;
      input.setAttribute('aria-expanded', 'false');
      input.removeAttribute('aria-activedescendant');
    }
    function placeCompletions() {
      if (completion.hidden) return;
      // A hidden mirror measures the caret in both wrapped and unwrapped text.
      const mirror = element('div');
      const style = getComputedStyle(input);
      for (const property of ['font', 'lineHeight', 'letterSpacing', 'tabSize', 'padding', 'boxSizing',
        'wordBreak', 'overflowWrap', 'borderWidth', 'borderStyle']) mirror.style[property] = style[property];
      Object.assign(mirror.style, {position: 'fixed', visibility: 'hidden', left: '0', top: '0',
        width: `${input.clientWidth}px`, whiteSpace: input.wrap === 'soft' ? 'pre-wrap' : 'pre'});
      mirror.append(document.createTextNode(input.value.slice(0, input.selectionStart)));
      const caret = element('span', '', '\u200b');
      mirror.append(caret);
      document.body.append(mirror);
      const rect = input.getBoundingClientRect();
      const pane = codePane.getBoundingClientRect();
      const x = rect.left - pane.left + caret.offsetLeft - input.scrollLeft;
      const y = rect.top - pane.top + caret.offsetTop - input.scrollTop + parseFloat(style.lineHeight);
      mirror.remove();
      const width = Math.min(560, codePane.clientWidth);
      completion.style.width = `${width}px`;
      completion.style.left = `${Math.max(0, Math.min(x, codePane.clientWidth - width))}px`;
      completion.style.top = `${Math.max(0, Math.min(y, codePane.clientHeight))}px`;
    }
    function choose(index) {
      if (!completionResult?.items.length) return;
      selectedChoice = (index + completionResult.items.length) % completionResult.items.length;
      [...choices.children].forEach((node, i) => node.setAttribute('aria-selected', String(i === selectedChoice)));
      const node = choices.children[selectedChoice];
      input.setAttribute('aria-activedescendant', node.id);
      if (node.offsetTop < choices.scrollTop) choices.scrollTop = node.offsetTop;
      else if (node.offsetTop + node.offsetHeight > choices.scrollTop + choices.clientHeight) {
        choices.scrollTop = node.offsetTop + node.offsetHeight - choices.clientHeight;
      }
      const item = completionResult.items[selectedChoice];
      signature.textContent = item.detail || '타입을 불러오는 중…';
      clearTimeout(detailTimer);
      const result = completionResult;
      detailTimer = setTimeout(async () => {
        try {
          const detail = await call('/api/lean/resolve', {session, version: result.version,
            completion: result.completion, index: item.index});
          if (completionResult !== result || result.items[selectedChoice] !== item) return;
          item.detail = detail.detail;
          signature.textContent = detail.detail || detail.documentation || item.label;
        } catch { /* A changed document invalidates older completion details. */ }
      }, 100);
    }
    async function complete(explicit) {
      if (browserLean) return;
      clearTimeout(completionTimer);
      const code = input.value;
      const cursor = input.selectionStart;
      const request = ++completionNumber;
      try {
        const result = await documentCall('/api/lean/complete', code, {position: position()});
        if (!result || request !== completionNumber || cursor !== input.selectionStart || code !== input.value || !input.matches(':focus')) return;
        completionResult = result;
        completionCode = code;
        completionCursor = cursor;
        choices.replaceChildren();
        completion.hidden = false;
        input.setAttribute('aria-expanded', 'true');
        for (const [index, item] of result.items.entries()) {
          const node = element('div', 'book-completion-option', item.label);
          node.id = `${choices.id}-${index}`;
          node.setAttribute('role', 'option');
          node.addEventListener('pointerdown', event => {
            event.preventDefault();
            selectedChoice = index;
            acceptCompletion();
          });
          choices.append(node);
        }
        if (result.items.length) choose(0);
        else if (explicit) signature.textContent = '일치하는 항목 없음';
        else hideCompletions();
        placeCompletions();
      } catch (error) {
        if (!explicit || request !== completionNumber) return;
        completion.hidden = false;
        choices.replaceChildren();
        signature.textContent = error.message;
        placeCompletions();
      }
    }
    function acceptCompletion() {
      const item = completionResult?.items[selectedChoice];
      if (!item || completionCode !== input.value || completionCursor !== input.selectionStart) return hideCompletions();
      const offset = pos => input.value.split('\n').slice(0, pos.line).reduce((n, row) => n + row.length + 1, 0) + pos.character;
      const start = offset(item.range.start);
      const end = offset(item.range.end);
      input.focus();
      input.setRangeText(item.text, start, end, 'end');
      changed();
      // A chosen name should not immediately reopen the same completion menu.
      clearTimeout(completionTimer);
    }
    input.addEventListener('input', changed);
    input.addEventListener('compositionstart', () => { composing = true; hideCompletions(); });
    input.addEventListener('compositionend', () => { composing = false; changed(); });
    input.addEventListener('click', () => { hideCompletions(); updateGoal(); });
    input.addEventListener('blur', hideCompletions);
    input.addEventListener('select', updateGoal);
    input.addEventListener('keyup', event => { if (event.key.startsWith('Arrow')) updateGoal(); });
    input.addEventListener('scroll', () => { gutter.scrollTop = input.scrollTop; placeCompletions(); });
    const symbols = {'forall': '∀', 'exists': '∃', 'in': '∈', 'notin': '∉', 'subseteq': '⊆',
      'and': '∧', 'or': '∨', 'not': '¬', 'to': '→', 'iff': '↔', 'equiv': '≡', 'times': '×',
      'le': '≤', 'ge': '≥', 'ne': '≠', 'emptyset': '∅', 'inter': '∩', 'union': '∪',
      'cap': '∩', 'cup': '∪', 'circ': '∘', 'langle': '⟨', 'rangle': '⟩', '<': '⟨', '>': '⟩', '.': '·',
      '[[': '⟦', ']]': '⟧', '[[]]': '⟦$CURSOR⟧'};
    input.addEventListener('keydown', event => {
      if (event.isComposing) return;
      if ((event.ctrlKey || event.metaKey) && event.code === 'Space') {
        event.preventDefault(); complete(true); return;
      }
      if (!completion.hidden) {
        if (event.key === 'Escape') { event.preventDefault(); hideCompletions(); return; }
        if (completionResult?.items.length) {
          if (['ArrowDown', 'ArrowUp'].includes(event.key)) {
            event.preventDefault(); choose(selectedChoice + (event.key === 'ArrowDown' ? 1 : -1)); return;
          }
          if (['Enter', 'Tab'].includes(event.key) && !event.ctrlKey && !event.metaKey && !event.shiftKey) {
            event.preventDefault(); acceptCompletion(); return;
          }
        }
      }
      if (['ArrowLeft', 'ArrowRight', 'Home', 'End'].includes(event.key)) hideCompletions();
      if ((event.ctrlKey || event.metaKey) && event.key === 'Enter') { event.preventDefault(); check(); }
      if (event.key === 'Tab') {
        event.preventDefault();
        const start = input.selectionStart;
        const match = input.value.slice(0, start).match(/\\([a-zA-Z<>.\[\]]+)$/);
        if (match && symbols[match[1]]) {
          const replacement = symbols[match[1]];
          const marker = replacement.indexOf('$CURSOR');
          const begin = start - match[0].length;
          input.setRangeText(replacement.replace('$CURSOR', ''), begin, start, 'end');
          if (marker >= 0) input.setSelectionRange(begin + marker, begin + marker);
        }
        else if (!event.shiftKey) input.setRangeText('  ', start, input.selectionEnd, 'end');
        changed();
      }
      if (event.key === 'Enter' && !event.ctrlKey && !event.metaKey) {
        event.preventDefault();
        const before = input.value.slice(0, input.selectionStart).split('\n').at(-1);
        const indent = before.match(/^ */)[0] + (/\bby\s*$/.test(before) ? '  ' : '');
        input.setRangeText('\n' + indent, input.selectionStart, input.selectionEnd, 'end');
        changed();
      }
    });
    lines();
    function activate() {
      lines();
      if (!activated) {
        const hole = input.value.search(/\bsorry\b/);
        const position = hole < 0 ? input.value.length : hole;
        input.setSelectionRange(position, position);
        activated = true;
      }
      if (checkedCode !== input.value) scheduleCheck(50);
      else updateGoal();
    }
    window.addEventListener('resize', () => { if (root.isConnected) { lines(); placeCompletions(); } });
    return {root, input, activate};
  }

  function foldLegacyHints() {
    for (const paragraph of document.querySelectorAll('main p')) {
      if (paragraph.closest('.book-disclosure')) continue;
      if (!/^힌트\s/.test(paragraph.textContent.trim())) continue;
      const details = element('details', 'book-disclosure');
      details.append(element('summary', '', '힌트'));
      paragraph.before(details);
      details.append(paragraph);
    }
  }
  function start() {
    document.querySelectorAll('.book-example').forEach(decorate);
    foldLegacyHints();
    if (browserLean) {
      const reopen = sessionStorage.getItem('lean-algebra.reopen');
      sessionStorage.removeItem('lean-algebra.reopen');
      if (reopen) {
        const wrapper = [...document.querySelectorAll('.book-example')].find(node => node.dataset.snippet === reopen);
        [...(wrapper?.querySelectorAll('.book-button') || [])].find(node => node.textContent === '편집')?.click();
      }
    }
  }
  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', start);
  else start();
})();
