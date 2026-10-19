// The upstream Worker owns the compiler; this page never sends proof text to a server.
let worker;
let pending;
let output = [];
let libraryManifest = [];
let libraryPacks = [];
let ready = false;
const runtimeProfile = [];
const loadedFiles = new Set();
const statusNode = document.querySelector('#status');
const outputNode = document.querySelector('#output');
const sourceNode = document.querySelector('#source');
const goalNode = document.querySelector('#goal-state');
fetch('runtime.json').then(response => response.json()).then(runtime => {
  document.querySelector('#runtime-note').textContent = `Lean ${runtime.version} — isolated browser experiment.`;
}).catch(() => {});

function request(message, expected, timeout = 180000, transfer = []) {
  if (pending) throw new Error('A compiler operation is already running');
  output = [];
  return new Promise((resolve, reject) => {
    const timer = setTimeout(() => {
      pending = null;
      worker.terminate();
      reject(new Error(`Timed out waiting for ${expected}; reload to restart`));
    }, timeout);
    pending = { expected, resolve, reject, timer };
    worker.postMessage(message, transfer);
  });
}

async function boot() {
  if (worker) throw new Error('Reload the page before starting another runtime');
  if (!crossOriginIsolated) throw new Error('Cross-origin isolation is required by this runtime');
  const started = performance.now();
  const timings = [];
  const mark = stage => timings.push({stage, elapsedMs: performance.now() - started});
  statusNode.textContent = 'Loading runtime and library…';
  worker = new Worker('worker.js?assetBase=runtime');
  worker.onmessage = ({data}) => {
    if (data.type === 'profile') runtimeProfile.push(data);
    if (data.type === 'stdout' || data.type === 'stderr') output.push(data.data);
    if (data.type === 'import_progress') statusNode.textContent = `Loading modules: ${data.loaded}/${data.total}`;
    if (pending && (data.type === pending.expected || data.type === 'error')) {
      const current = pending;
      pending = null;
      clearTimeout(current.timer);
      if (data.type === 'error') current.reject(new Error(data.data));
      else current.resolve({...data, output: [...output]});
    }
  };
  worker.onerror = event => {
    if (pending) {
      clearTimeout(pending.timer);
      pending.reject(new Error(event.message));
      pending = null;
    }
  };
  const manifest = await (await fetch('library.json')).json();
  mark('manifest');
  libraryManifest = Array.isArray(manifest) ? manifest : manifest.files;
  libraryPacks = manifest.packs || [];
  const files = await fetchLibrary(libraryManifest.filter(name => name === 'Init.olean' || name.startsWith('Init/')));
  mark('initial-library-fetched');
  await request({type: 'load_library', files}, 'library_received', 180000, files.map(file => file.data));
  await request({type: 'start_worker'}, 'worker_ready');
  mark('runtime-ready');
  // Measure the first import separately from later editing cycles.
  const warmup = await compile('#check Nat');
  mark('initial-import');
  if (!warmup.success) throw new Error(JSON.stringify(warmup));
  statusNode.textContent = 'Ready';
  ready = true;
  document.querySelector('#check').disabled = false;
  return {bootMs: performance.now() - started, libraryFiles: files.length, warmup, timings, runtimeProfile};
}

async function fetchLibrary(manifest) {
  if (libraryPacks.length) return fetchPackedLibrary(manifest);
  const files = [];
  let next = 0;
  await Promise.all(Array.from({length: 16}, async () => {
    while (next < manifest.length) {
      const name = manifest[next++];
      const response = await fetch(`library/${name}`);
      if (!response.ok) throw new Error(`Cannot load ${name}: ${response.status}`);
      files.push({name, data: await response.arrayBuffer()});
      loadedFiles.add(name);
    }
  }));
  return files;
}

async function fetchPackedLibrary(manifest) {
  const wanted = new Set(manifest);
  const packs = libraryPacks.filter(pack => pack.entries.some(entry => wanted.has(entry.path)));
  const files = [];
  let next = 0;
  let finished = 0;
  await Promise.all(Array.from({length: 2}, async () => {
    while (next < packs.length) {
      const pack = packs[next++];
      const response = await fetch(`packs/${pack.file}`);
      if (!response.ok) throw new Error(`Cannot load ${pack.file}: ${response.status}`);
      const compressed = await response.arrayBuffer();
      const digest = [...new Uint8Array(await crypto.subtle.digest('SHA-256', compressed))]
        .map(byte => byte.toString(16).padStart(2, '0')).join('');
      if (compressed.byteLength !== pack.bytes || digest !== pack.sha256) throw new Error(`Corrupt library pack: ${pack.file}`);
      const raw = await new Response(new Blob([compressed]).stream().pipeThrough(new DecompressionStream('gzip'))).arrayBuffer();
      if (raw.byteLength !== pack.rawBytes) throw new Error(`Invalid decoded size: ${pack.file}`);
      for (const entry of pack.entries) if (wanted.has(entry.path)) {
        if (entry.offset < 0 || entry.offset + entry.bytes > raw.byteLength) throw new Error(`Invalid pack entry: ${entry.path}`);
        files.push({name: entry.path, data: raw.slice(entry.offset, entry.offset + entry.bytes)});
        loadedFiles.add(entry.path);
      }
      statusNode.textContent = `Loading library packs: ${++finished}/${packs.length}`;
    }
  }));
  if (files.length !== manifest.length) throw new Error('The library pack index is incomplete');
  return files;
}

async function compile(code) {
  const started = performance.now();
  if (/^(?:(?:public|meta)\s+)*import\s/m.test(code)) {
    const additional = libraryManifest.filter(name => !loadedFiles.has(name));
    if (additional.length) {
      statusNode.textContent = 'Loading additional libraries…';
      const files = await fetchLibrary(additional);
      const staged = await request({type: 'add_files', files}, 'files_added', 180000, files.map(file => file.data));
      if (staged.count !== files.length) throw new Error('Not all requested library files could be staged');
    }
  }
  const libraryMs = performance.now() - started;
  const result = await request({type: 'compile', code, path: '/workspace/Experiment.lean'}, 'compile_result');
  return {...result, wallMs: performance.now() - started, libraryMs};
}

async function goalsAt(line, character) {
  const result = await request({type: 'goals', line, character}, 'goals_result');
  if (!result.success) throw new Error(result.error);
  for (const line of result.output) {
    try {
      const data = JSON.parse(line);
      if (typeof data.found === 'boolean' && Array.isArray(data.goals)) return data;
    } catch {}
  }
  throw new Error('Lean returned no goal response');
}

window.wasmExperiment = {boot, compile, goalsAt};
let checkedSource = null;
let usesSorry = false;
let checking = false;
let editTimer;

async function showCursorGoals() {
  if (pending || checking || checkedSource !== sourceNode.value) return;
  const cursor = sourceNode.selectionStart;
  const code = checkedSource;
  const before = sourceNode.value.slice(0, sourceNode.selectionStart);
  const rows = before.split('\n');
  try {
    const result = await goalsAt(rows.length - 1, rows.at(-1).length);
    if (code !== sourceNode.value || cursor !== sourceNode.selectionStart) {
      setTimeout(showCursorGoals, 0);
      return;
    }
    goalNode.textContent = result.found
      ? result.goals.length ? result.goals.join('\n\n') : usesSorry ? 'The proof contains a placeholder.' : 'No remaining goals.'
      : 'No proof state at this position.';
  } catch (error) { goalNode.textContent = String(error); }
}

async function checkEditor() {
  if (checking || !ready) return;
  if (pending) {
    editTimer = setTimeout(checkEditor, 100);
    return;
  }
  checking = true;
  const code = sourceNode.value;
  document.querySelector('#check').disabled = true;
  statusNode.textContent = 'Checking…';
  try {
    const result = await compile(code);
    if (code !== sourceNode.value) return;
    checkedSource = result.success ? code : null;
    const messages = result.output.flatMap(line => { try { return [JSON.parse(line)]; } catch { return []; } });
    const errors = messages.filter(message => message.severity === 'error');
    usesSorry = messages.some(message => message.kind === 'hasSorry'
      || /declaration uses [`']sorry[`']/.test(message.data || message.message || ''));
    const unfinished = errors.length && errors.every(message => message.kind === 'Tactic.unsolvedGoals');
    outputNode.textContent = messages.map(message => message.data || message.message).filter(Boolean).join('\n\n')
      || result.output.join('\n') || 'No diagnostics.';
    statusNode.textContent = !result.success ? 'Runtime error'
      : unfinished ? 'Unfinished proof' : errors.length ? `${errors.length} error(s)` : usesSorry ? 'Unfinished proof' : 'Checked';
  } catch (error) { statusNode.textContent = 'Failed'; outputNode.textContent = String(error); }
  finally {
    checking = false;
    document.querySelector('#check').disabled = false;
    if (code !== sourceNode.value) editTimer = setTimeout(checkEditor, 100);
    else await showCursorGoals();
  }
}

document.querySelector('#start').onclick = async () => {
  document.querySelector('#start').disabled = true;
  try { await boot(); await checkEditor(); }
  catch (error) { statusNode.textContent = 'Failed'; outputNode.textContent = String(error); }
};
document.querySelector('#check').onclick = checkEditor;
sourceNode.addEventListener('input', () => {
  if (!ready) return;
  clearTimeout(editTimer);
  goalNode.textContent = '';
  statusNode.textContent = 'Waiting for edits…';
  editTimer = setTimeout(checkEditor, 500);
});
sourceNode.addEventListener('click', showCursorGoals);
sourceNode.addEventListener('keyup', showCursorGoals);
