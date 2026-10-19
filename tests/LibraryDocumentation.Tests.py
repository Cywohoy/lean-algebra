"""Keep the public library English while allowing the textbook to be Korean."""
from pathlib import Path
import re
import runpy

root = Path(__file__).resolve().parents[1]
package = root / '.lake/packages/ample'
assert (package / 'Ample').is_dir(), 'Run lake update ample first.'
paths = sorted((package / 'Ample').rglob('*.lean'))
paths += [package / 'README.md', package / 'THIRD_PARTY_NOTICES.md']
for path in paths:
    source = path.read_text(encoding='utf-8')
    assert not re.search(r'[\uac00-\ud7a3]', source), path.relative_to(package)

strip_notes = runpy.run_path(str(root / 'scripts/sync_ample.py'))['without_textbook_annotations']
sample = '''-- 교재의 풀이 설명
  · -- 두 경우를 나눈다.
    exact h
def ordinary := "
-- 문자열 안의 한글
"
def raw := r##"
-- 원시 문자열 안의 한글 "
"##
def quote : Char := '"'
-- 따옴표 뒤의 풀이 설명
/- Outer block
/- Nested block -/
-- 블록 주석 안의 설명
-/
-- Copyright: 원문의 표시를 보존한다.
'''
expected = sample.replace('-- 교재의 풀이 설명', '').replace('  · -- 두 경우를 나눈다.', '  ·').replace('-- 따옴표 뒤의 풀이 설명', '')
assert strip_notes(sample) == expected

print(f'PASS: {len(paths)} English library files; textbook annotations, literals, and notices stay separated')
