// The upstream Worker owns the compiler; this page never sends proof text to a server.
let worker;
let pending;
let output = [];
const statusNode = document.querySelector('#status');
const outputNode = document.querySelector('#output');

function request(message, expected, timeout = 180000) {
  if (pending) throw new Error('A compiler operation is already running');
  output = [];
  return new Promise((resolve, reject) => {
    const timer = setTimeout(() => {
      pending = null;
      worker.terminate();
      reject(new Error(`Timed out waiting for ${expected}; reload to restart`));
    }, timeout);
    pending = { expected, resolve, reject, timer };
    worker.postMessage(message);
  });
}

async function boot() {
  if (worker) throw new Error('Reload the page before starting another runtime');
  if (!crossOriginIsolated) throw new Error('Cross-origin isolation is required by this runtime');
  const started = performance.now();
  statusNode.textContent = 'Loading runtime and library…';
  worker = new Worker('worker.js?assetBase=runtime');
  worker.onmessage = ({data}) => {
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
  const files = [];
  let next = 0;
  await Promise.all(Array.from({length: 16}, async () => {
    while (next < manifest.length) {
      const name = manifest[next++];
      const response = await fetch(`library/${name}`);
      if (!response.ok) throw new Error(`Cannot load ${name}: ${response.status}`);
      files.push({name, data: await response.arrayBuffer()});
    }
  }));
  await request({type: 'load_library', files}, 'library_received');
  await request({type: 'start_worker'}, 'worker_ready');
  // Measure the first import separately from later editing cycles.
  const warmup = await compile('#check Nat');
  if (!warmup.success) throw new Error(JSON.stringify(warmup));
  statusNode.textContent = 'Ready';
  document.querySelector('#check').disabled = false;
  return {bootMs: performance.now() - started, libraryFiles: files.length, warmup};
}

async function compile(code) {
  const started = performance.now();
  const result = await request({type: 'compile', code, path: '/workspace/Experiment.lean'}, 'compile_result');
  return {...result, wallMs: performance.now() - started};
}

window.wasmExperiment = {boot, compile};
document.querySelector('#start').onclick = async () => {
  document.querySelector('#start').disabled = true;
  try { const result = await boot(); outputNode.textContent = `Ready in ${(result.bootMs / 1000).toFixed(1)} seconds.`; }
  catch (error) { statusNode.textContent = 'Failed'; outputNode.textContent = String(error); }
};
document.querySelector('#check').onclick = async () => {
  document.querySelector('#check').disabled = true;
  statusNode.textContent = 'Checking…';
  try {
    const result = await compile(document.querySelector('#source').value);
    outputNode.textContent = result.output.join('\n') || 'No diagnostics.';
    statusNode.textContent = `${Math.round(result.wallMs)} ms`;
  } catch (error) { statusNode.textContent = 'Failed'; outputNode.textContent = String(error); }
  finally { document.querySelector('#check').disabled = false; }
};
