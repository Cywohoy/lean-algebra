"""Stage a checksum-pinned browser runtime and translate book-only imports."""
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import tarfile
import urllib.request

ROOT = Path(__file__).resolve().parents[1]


def prepare(site, bundle=None, download=False):
    spec = json.loads((ROOT / 'web/wasm-runtime.json').read_text(encoding='utf-8'))
    if download:
        cache = ROOT / 'tmp/wasm/downloads'
        cache.mkdir(parents=True, exist_ok=True)
        bundle = cache / (spec['sha256'] + '.tar.gz')
        if not bundle.exists():
            partial = bundle.with_suffix('.partial')
            with urllib.request.urlopen(spec['url'], timeout=120) as response, partial.open('wb') as output:
                while data := response.read(1024 * 1024):
                    output.write(data)
            partial.replace(bundle)
    with Path(bundle).open('rb') as stream:
        digest = hashlib.file_digest(stream, 'sha256').hexdigest()
    if digest != spec['sha256']:
        raise ValueError('Browser runtime checksum mismatch; no unverified runtime is staged')
    relative = 'wasm/' + digest[:16] + '/'
    target = site / relative
    target.mkdir(parents=True, exist_ok=True)
    with tarfile.open(bundle) as archive:
        archive.extractall(target, filter='data')
    for required in ['runtime/lean.js', 'runtime/lean.wasm', 'library.json', 'worker.js', 'upstream-worker.js']:
        if not (target / required).is_file():
            raise ValueError('Incomplete browser runtime: ' + required)
    import shutil
    shutil.copyfile(target / 'coi-serviceworker.js', site / 'coi-serviceworker.js')
    (site / 'assets/web').mkdir(parents=True, exist_ok=True)
    shutil.copyfile(ROOT / 'assets/web/reader.js', site / '-verso-data/reader.js')
    shutil.copyfile(ROOT / 'assets/web/reader.css', site / '-verso-data/reader.css')
    for name in ['lean-wasm.js', 'wasm-reader.js', 'exercise-model.js']:
        shutil.copyfile(ROOT / 'assets/web' / name, site / 'assets/web' / name)
    loader = importlib.util.spec_from_file_location('book_math_export', ROOT / 'scripts/sync_ample.py')
    exporter = importlib.util.module_from_spec(loader)
    loader.loader.exec_module(exporter)
    intro = exporter.export_module((ROOT / 'AlgebraBook/Introduction.lean').read_text(encoding='utf-8'))
    intro_imports = re.findall(r'^import (\S+)\s*$', intro, re.M)
    intro_body = re.sub(r'^import \S+\s*$', '', intro, flags=re.M)

    def translate(before):
        imports = []
        extra = ''
        for name in re.findall(r'^import (\S+)\s*$', before, re.M):
            if name == 'AlgebraBook.Introduction':
                imports.extend(intro_imports)
                extra = intro_body + '\n'
            else:
                imports.append(exporter.library_import(name))
        body = re.sub(r'^import \S+\s*$', '', before, flags=re.M)
        body = re.sub(r'^export_course_compat\s*$', '', body, flags=re.M)
        return ''.join('import ' + name + '\n' for name in dict.fromkeys(imports)) + '\n' + extra + body

    manifest_path = site / 'playground.json'
    manifest = json.loads(manifest_path.read_text(encoding='utf-8'))
    for key, snippet in manifest.items():
        snippet['before'] = translate(snippet['before'])
        (site / 'playground' / (key + '.json')).write_text(json.dumps(snippet, ensure_ascii=False), encoding='utf-8')
    manifest_path.write_text(json.dumps(manifest, ensure_ascii=False), encoding='utf-8')
    return relative
