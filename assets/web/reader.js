/* Interactive reading and browser-local Lean execution. */
(() => {
  'use strict';
  const siteRoot = new URL('.', document.baseURI);
  const staticReading = document.querySelector('meta[name="book-mode"]')?.content === 'static';
  const browserLean = document.querySelector('meta[name="book-mode"]')?.content === 'wasm';
  let browserBackend;
  const snippets = new Map();
  let activeEditor;
  const openEditors = new Map();
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
  async function call(path, payload) {
    if (!browserLean) throw new Error('WASM 실행 환경이 준비되지 않았습니다. 미리보기를 다시 시작해 주세요.');
    browserBackend ||= import(new URL('assets/web/wasm-reader.js', siteRoot))
      .then(module => module.createBrowserBackend(siteRoot));
    return (await browserBackend).call(path, payload);
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
    const exercise = wrapper.dataset.exerciseUnit === 'proofs';
    wrapper.classList.toggle('book-exercise', exercise);
    const steps = proofSteps(source);
    const toolbar = element('div', 'book-toolbar');
    toolbar.setAttribute('aria-label', '예제 도구');
    const body = element('div', 'book-example-body');
    source.before(body);
    body.append(source);
    wrapper.prepend(toolbar);
    const panel = element('section', 'book-reader-panel');
    panel.id = `book-panel-${++panelCounter}`;
    panel.hidden = true;
    body.append(panel);
    let workspace;
    const problemParagraphs = [];
    if (exercise) {
      workspace = element('dialog', 'book-exercise-workspace');
      const heading = element('div', 'book-exercise-heading');
      const title = element('strong', '', '연습문제 풀이');
      title.id = `book-exercise-${panelCounter}`;
      workspace.setAttribute('aria-labelledby', title.id);
      heading.append(title, button('본문으로', () => setMode(null)));
      const statement = element('div', 'book-exercise-statement');
      for (let node = wrapper.previousElementSibling; node?.tagName === 'P'; node = node.previousElementSibling) {
        problemParagraphs.unshift(node);
        if (/^문제\s*\d/.test(node.textContent.trim())) break;
      }
      for (const paragraph of problemParagraphs) {
        const clone = paragraph.cloneNode(true);
        clone.querySelectorAll('[id]').forEach(node => node.removeAttribute('id'));
        statement.append(clone);
      }
      workspace.append(heading, statement, panel);
      wrapper.append(workspace);
      workspace.addEventListener('cancel', event => { event.preventDefault(); setMode(null); });
    }
    let mode = null;
    let stepIndex = 0;
    let editor;
    let selectStep;
    const status = element('span', 'book-toolbar-status');
    status.setAttribute('role', 'status');
    let stepButton;
    const editButton = exercise ? button('풀기', () => setMode(mode === 'edit' ? null : 'edit')) : null;
    if (editButton && browserLean) editButton.title = '브라우저에서 Lean을 실행합니다. 첫 실행 시 약 300 MB를 내려받습니다.';
    const copyButton = button('', async () => {
      try {
        const text = mode === 'edit' && editor ? editor.code() : (await snippet(key)).code;
        await navigator.clipboard.writeText(text);
        status.textContent = '복사됨';
      } catch { status.textContent = '복사 실패'; }
    }, 'book-copy');
    copyButton.setAttribute('aria-label', '복사');
    copyButton.title = '코드 복사';
    const copyIcon = document.createElementNS('http://www.w3.org/2000/svg', 'svg');
    copyIcon.setAttribute('viewBox', '0 0 24 24');
    copyIcon.setAttribute('width', '16'); copyIcon.setAttribute('height', '16');
    copyIcon.setAttribute('fill', 'none'); copyIcon.setAttribute('stroke', 'currentColor');
    copyIcon.setAttribute('stroke-width', '1.5'); copyIcon.setAttribute('aria-hidden', 'true');
    const outline = document.createElementNS('http://www.w3.org/2000/svg', 'path');
    outline.setAttribute('d', 'M8 8h12v13H8z M16 8V3H3v13h5');
    copyIcon.append(outline); copyButton.append(copyIcon);
    if (steps.length && !exercise) {
      stepButton = button('단계', () => setMode(mode === 'steps' ? null : 'steps'));
      toolbar.prepend(stepButton);
    }
    if (exercise) {
      const card = element('section', 'book-exercise-card');
      const heading = element('div', 'book-exercise-card-heading');
      const number = problemParagraphs[0]?.querySelector('strong');
      heading.append(element('strong', '', number?.textContent || '연습문제'));
      number?.remove();
      editButton.classList.add('book-solve-button');
      if (!staticReading) heading.append(editButton);
      const disclosure = wrapper.nextElementSibling;
      wrapper.before(card);
      card.append(heading, ...problemParagraphs, wrapper);
      if (disclosure?.matches('details.book-disclosure')) card.append(disclosure);
    }
    toolbar.append(copyButton, status);
    if (exercise) openEditors.set(key, () => setMode('edit'));
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
      if (workspace) {
        if (mode === 'edit' && !workspace.open) workspace.showModal();
        else if (mode !== 'edit' && workspace.open) { workspace.close(); editButton.focus(); }
        document.documentElement.classList.toggle('book-solving', mode === 'edit');
      }
      panel.hidden = !mode;
      if (stepButton) stepButton.setAttribute('aria-expanded', String(mode === 'steps'));
      editButton?.setAttribute('aria-expanded', String(mode === 'edit'));
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
          if (!editor) {
            const model = exercise ? await import(new URL('assets/web/exercise-model.js', siteRoot)) : null;
            if (mode !== 'edit') return;
            editor = createEditor(key, data, model?.exerciseModel);
          }
          panel.append(editor.root);
          editor.input.focus();
          editor.activate();
        } catch (error) { panel.replaceChildren(element('p', 'book-error', error.message)); }
      }
    }
    source.addEventListener('click', event => {
      if ((!steps.length && !exercise) || event.target.closest('a[href]') || event.ctrlKey || event.metaKey) return;
      if (window.getSelection()?.toString()) return;
      if (exercise) {
        event.preventDefault(); event.stopPropagation(); setMode('edit'); return;
      }
      const label = event.target.closest('.tactic > label');
      const index = steps.findIndex(step => step.label === label);
      event.preventDefault();
      event.stopPropagation();
      if (mode !== 'steps') setMode('steps');
      selectStep(index >= 0 ? index : stepIndex);
    }, true);
    if (steps.length || exercise) {
      source.tabIndex = 0;
      source.setAttribute('aria-label', exercise ? 'Lean 연습문제. 누르면 풀이 화면이 열립니다.'
        : 'Lean 증명. 누르면 단계별 가정과 목표를 볼 수 있습니다.');
      source.addEventListener('keydown', event => {
        if (event.target !== source || !['Enter', ' '].includes(event.key)) return;
        event.preventDefault();
        setMode(exercise ? 'edit' : mode === 'steps' ? null : 'steps');
      });
    }
  }

  function createEditor(key, original, makeExercise) {
    const root = element('div', 'book-live-editor');
    const controls = element('div', 'book-editor-controls');
    const input = element('textarea', 'book-code-input');
    input.setAttribute('aria-label', '수정할 Lean 코드');
    input.spellcheck = false;
    input.autocapitalize = 'off';
    input.autocomplete = 'off';
    input.wrap = 'off';
    const storageKey = `lean-algebra.code.${key}`;
    const draft = stored(storageKey) ?? original.code.trimEnd();
    const exercise = makeExercise?.(original.code, draft);
    let fullCode = exercise?.full || false;
    let selectedProof = 0;
    const declaration = element('pre', 'book-exercise-declaration');
    const proofControls = element('div', 'book-proof-controls');
    function currentCode() {
      if (!exercise || fullCode) return input.value;
      exercise.bodies[selectedProof] = exercise.sourceBody(input.value);
      return exercise.source(exercise.bodies);
    }
    function editableStart() { return exercise && !fullCode ? exercise.start(exercise.bodies, selectedProof) : 0; }
    function loadProof() {
      input.value = exercise.editorBody(exercise.bodies[selectedProof]);
      declaration.textContent = exercise.parts[selectedProof].header.trimEnd();
      declaration.hidden = fullCode;
      proofControls.hidden = fullCode || exercise.parts.length === 1;
      input.setAttribute('aria-label', fullCode ? '연습문제 전체 코드' : `풀이 ${selectedProof + 1}`);
      [...proofControls.children].forEach((node, i) => node.setAttribute('aria-pressed', String(i === selectedProof)));
    }
    if (exercise) {
      for (const [index] of exercise.parts.entries()) proofControls.append(button(`(${index + 1})`, () => {
        currentCode(); selectedProof = index; loadProof(); input.focus(); changed();
      }));
      if (fullCode) input.value = draft;
      else loadProof();
    } else input.value = draft;
    const message = element('span', 'book-run-status', '대기 중');
    message.setAttribute('role', 'status');
    const run = button(exercise ? '검사' : '실행', check, 'book-primary');
    const reset = button('초기화', () => {
      if (exercise) {
        exercise.bodies = exercise.parts.map(part => part.body);
        if (fullCode) input.value = original.code.trimEnd();
        else loadProof();
      } else input.value = original.code.trimEnd();
      changed();
      input.focus();
    });
    controls.append(run, reset, message);
    if (exercise) {
      const toggle = button(fullCode ? '증명만 편집' : '전체 코드', () => {
        const source = currentCode();
        if (fullCode) {
          const bodies = exercise.parse(source);
          if (!bodies) {
            message.textContent = '정리의 선언이나 보조 정의를 수정한 코드는 전체 코드에서 편집할 수 있습니다.';
            return;
          }
          exercise.bodies = bodies;
        }
        fullCode = !fullCode;
        if (fullCode) input.value = source;
        else loadProof();
        declaration.hidden = fullCode;
        proofControls.hidden = fullCode || exercise.parts.length === 1;
        toggle.textContent = fullCode ? '증명만 편집' : '전체 코드';
        input.setAttribute('aria-label', fullCode ? '연습문제 전체 코드' : `풀이 ${selectedProof + 1}`);
        input.focus(); changed();
      });
      const download = button('풀이 내려받기', () => {
        let source = original.before.trimEnd() + '\n\n' + currentCode() + '\n';
        const scopes = [];
        for (const line of source.split('\n')) {
          const open = /^(namespace|section)(?:\s+(\S+))?\s*$/.exec(line);
          if (open) scopes.push(open[2] || '');
          else if (/^end(?:\s+\S+)?\s*$/.test(line)) scopes.pop();
        }
        source += scopes.reverse().map(name => `end${name ? ' ' + name : ''}\n`).join('');
        const url = URL.createObjectURL(new Blob([source], {type: 'text/plain;charset=utf-8'}));
        const link = element('a'); link.href = url; link.download = exercise.parts[0].name + '.lean';
        link.click(); setTimeout(() => URL.revokeObjectURL(url), 1000);
      });
      controls.insertBefore(toggle, message);
      controls.insertBefore(download, message);
      root.append(proofControls, declaration);
      declaration.hidden = fullCode;
      proofControls.hidden = fullCode || exercise.parts.length === 1;
    }
    const columns = element('div', 'book-editor-columns');
    const codePane = element('div', 'book-edit-code');
    const gutter = element('pre', 'book-line-numbers');
    gutter.setAttribute('aria-hidden', 'true');
    codePane.append(gutter, input);
    const output = element('section', 'book-live-output');
    output.setAttribute('aria-label', 'Lean 실행 결과');
    const outputHeading = element('strong', 'book-panel-heading', '가정과 목표');
    const goal = element('pre', 'book-live-goal', '실행 후 코드 위치를 선택하면 가정과 목표가 표시됩니다.');
    const diagnostics = element('div', 'book-diagnostics');
    output.append(outputHeading, goal, diagnostics);
    columns.append(codePane, output);
    root.append(controls, columns, element('p', 'book-help',
      '자동 검사 · Ctrl+Enter 즉시 검사 · \\forall + Tab → ∀'));
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
    // Serialize edits to the same LSP document. Skip queued requests for text
    // that has already changed instead of sending an older document to Lean.
    function documentCall(path, code, payload) {
      const task = documentQueue.catch(() => {}).then(async () => {
        if (currentCode() !== code || !root.isConnected) return null;
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
      const visible = input.value.slice(0, input.selectionStart);
      const offset = exercise && !fullCode ? exercise.sourceBody(visible).length : input.selectionStart;
      const before = currentCode().slice(0, editableStart() + offset);
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
      store(storageKey, currentCode());
      message.textContent = '수정됨';
      message.className = 'book-run-status';
      ++requestNumber;
      lines();
      scheduleCheck();

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
      const code = currentCode();
      ++requestNumber;
      try {
        const result = await documentCall('/api/lean/check', code, {position: position()});
        if (!result) return;
        checkedCode = code;
        if (code !== currentCode()) return;
        showGoal(result.goal);
        diagnostics.replaceChildren();
        for (const item of result.diagnostics) {
          if (item.kind === 'unfinished' || item.isSilent) continue;
          const start = code.split('\n').slice(0, item.line - 1).reduce((n, line) => n + line.length + 1, 0) + item.column - 1;
          const proofIndex = exercise && !fullCode
            ? exercise.parts.findLastIndex((_, i) => exercise.start(exercise.bodies, i) <= start) : -1;
          const row = proofIndex < 0 ? item.line
            : code.slice(exercise.start(exercise.bodies, proofIndex), start).split('\n').length;
          const label = proofIndex >= 0 && exercise.parts.length > 1 ? `풀이 (${proofIndex + 1}) ` : '';
          const column = proofIndex < 0 ? item.column : Math.max(1, item.column - 2);
          const diagnostic = button(`${label}${row}:${column}  ${item.message}`, () => {
            if (exercise && !fullCode) {
              const index = exercise.parts.findLastIndex((_, i) => exercise.start(exercise.bodies, i) <= start);
              if (index >= 0) { selectedProof = index; loadProof(); lines(); }
            }
            input.focus();
            const offset = Math.max(0, start - editableStart());
            const cursor = exercise && !fullCode
              ? exercise.editorBody(exercise.bodies[selectedProof].slice(0, offset)).length : offset;
            input.setSelectionRange(cursor, cursor);
            updateGoal();
          }, item.severity === 1 ? 'book-error' : 'book-warning');
          diagnostics.append(diagnostic);
        }
        if (result.contextErrors.length) {
          throw new Error('이 예제에 필요한 정의를 불러오지 못했습니다.\n' + result.contextErrors.join('\n'));
        }
        const errors = result.diagnostics.filter(item => item.severity === 1 && item.kind !== 'unfinished');
        const holes = result.diagnostics.some(item => item.kind === 'unfinished');
        message.textContent = errors.length ? `오류 ${errors.length}개` : holes ? '증명 중'
          : exercise ? (exercise.parse(code) ? '풀이 완료' : '코드 검사 통과') : '오류 없음';
        message.classList.toggle('book-error', !!errors.length);
        message.classList.toggle('book-success', !errors.length && !holes);
      } catch (error) {
        if (code === currentCode()) {
          message.textContent = '실행 실패';
          diagnostics.replaceChildren(element('p', 'book-error', error.message));
        }
      } finally {
        busy = false;
        run.disabled = false;
        if (currentCode() !== code) scheduleCheck(250);
        else if (checkedCode === code) updateGoal();
      }
    }
    async function updateGoal() {
      clearTimeout(timer);
      if (busy || !root.isConnected || !session || checkedCode !== currentCode()) return;
      const current = ++requestNumber;
      timer = setTimeout(async () => {
        try {
          const result = await call('/api/lean/goal', {session, version, position: position()});
          if (current === requestNumber && checkedCode === currentCode()) showGoal(result.goal);
        } catch (error) {
          if (root.isConnected && /Run this example|code changed/.test(error.message)) {
            checkedCode = undefined;
            scheduleCheck(50);
          }
        }
      }, 180);
    }
    input.addEventListener('input', changed);
    input.addEventListener('compositionend', changed);
    input.addEventListener('click', updateGoal);
    input.addEventListener('select', updateGoal);
    input.addEventListener('keyup', event => { if (event.key.startsWith('Arrow')) updateGoal(); });
    input.addEventListener('scroll', () => { gutter.scrollTop = input.scrollTop; });
    const symbols = {'forall': '∀', 'exists': '∃', 'in': '∈', 'notin': '∉', 'subseteq': '⊆',
      'and': '∧', 'or': '∨', 'not': '¬', 'to': '→', 'iff': '↔', 'equiv': '≡', 'times': '×',
      'le': '≤', 'ge': '≥', 'ne': '≠', 'emptyset': '∅', 'inter': '∩', 'union': '∪',
      'cap': '∩', 'cup': '∪', 'circ': '∘', 'langle': '⟨', 'rangle': '⟩', '<': '⟨', '>': '⟩', '.': '·',
      '[[': '⟦', ']]': '⟧', '[[]]': '⟦$CURSOR⟧'};
    input.addEventListener('keydown', event => {
      if (event.isComposing) return;
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
      if (checkedCode !== currentCode()) scheduleCheck(50);
      else updateGoal();
    }
    window.addEventListener('resize', () => { if (root.isConnected) { lines(); } });
    return {root, input, activate, code: currentCode};
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
      if (reopen) openEditors.get(reopen)?.();
    }
  }
  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', start);
  else start();
})();
