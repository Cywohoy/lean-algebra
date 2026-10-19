"""Verify optional tracing without changing whether tactics solve their goals."""
from pathlib import Path
import shutil
import subprocess

root = Path(__file__).resolve().parents[1]
lake = shutil.which('lake') or str(Path.home() / '.elan/bin/lake.exe')
result = subprocess.run([lake, 'env', 'lean', 'tests/AutomationTrace.lean'],
                        cwd=root, capture_output=True, text=True, encoding='utf-8')
assert result.returncode == 0, result.stdout + result.stderr
output = result.stdout
assert '[Ample.arith] Proved: m / n ≤ m' in output, output
assert 'Rule: Nat.div_le_self' in output, output
assert 'Rule: Ample.isInfinite_transport' in output, output
assert 'condition: cardinal A = cardinal B' in output, output
assert 'Hypothesis: hA : IsInfinite A' in output, output
assert 'Proved: n ≤ n + 1' not in output, output
assert 'Proved: n < n' not in output, output
assert '_private.' not in output, output
print('PASS: tracing is optional and reports completed proof rules and conditions only')
