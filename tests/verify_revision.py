"""Compile the textbook's extracted code, exercise templates, and tactic regressions."""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor, as_completed
import hashlib
import shutil
import subprocess

root = Path(__file__).resolve().parents[1]
before = {p: hashlib.sha256(p.read_bytes()).hexdigest()
          for p in (root/'Exercises').rglob('*') if p.is_file()}
lake = shutil.which('lake') or str(Path.home() / '.elan/bin/lake.exe')
# Include compatibility and public tactic entry points used by regression files.
subprocess.run([lake, 'build', 'AlgebraBook', 'Ample.Tactic'], cwd=root, check=True)
paths = sorted((root/'_out/example-code').rglob('*.lean'))
paths += sorted((root/'ExerciseTemplates').glob('*.lean'))
paths += sorted((root/'tests').glob('*.lean'))
logdir = root/'output/revision-tests'
logdir.mkdir(parents=True, exist_ok=True)

def check(path):
    relative = path.relative_to(root)
    result = subprocess.run([lake, 'env', 'lean', str(relative)], cwd=root,
                            capture_output=True, text=True, encoding='utf-8')
    name = str(relative).replace('\\','__').replace('/','__')+'.log'
    (logdir/name).write_text(result.stdout+result.stderr, encoding='utf-8')
    return str(relative), result.returncode, result.stdout + result.stderr

failures=[]
with ThreadPoolExecutor(max_workers=4) as pool:
    for future in as_completed([pool.submit(check,p) for p in paths]):
        name, code, output=future.result()
        if code:
            failures.append(name)
            print('FAIL:', name, flush=True)
            print(output, flush=True)

after = {p: hashlib.sha256(p.read_bytes()).hexdigest()
         for p in (root/'Exercises').rglob('*') if p.is_file()}
assert before == after, 'Personal solutions changed during verification.'

print(f'Checked {len(paths)} Lean files; {len(failures)} failed. Private solutions preserved.',flush=True)
if failures:
    raise SystemExit(1)
