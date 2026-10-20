"""Check the reading routes and exported proof boundaries in the generated book."""
from pathlib import Path
from html.parser import HTMLParser
import re
import sys
import json
from urllib.parse import urlsplit, unquote

root=Path(__file__).resolve().parents[1]
buildroot=Path(sys.argv[1]) if len(sys.argv)>1 else root/'_out'
htmlroot=buildroot/'html-multi'

class Headings(HTMLParser):
    def __init__(self):
        super().__init__()
        self.level=None
        self.text=[]
        self.headings=[]
    def handle_starttag(self,tag,attrs):
        if tag in ('h1','h2','h3'):
            self.level=tag
            self.text=[]
    def handle_data(self,data):
        if self.level: self.text.append(data)
    def handle_endtag(self,tag):
        if tag==self.level:
            self.headings.append(' '.join(''.join(self.text).split()))
            self.level=None

sections={
 'foundations/introduction':('1.1.','Lean'),
 'foundations/using-proofs':('1.2.','증명의 구성과 사용'),
 'foundations/sets':('1.3.','집합의 구성'),
 'foundations/functions':('1.4.','함수'),
 'foundations/preliminaries':('1.5.','자연수와 정수'),
 'foundations/relations':('1.6.','동치관계와 몫집합'),
 'foundations/cardinality':('1.7.','집합의 크기와 유한성'),
 'foundations/infinite-cardinality':('1.8.','무한집합의 크기'),
}
for folder,(number,title) in sections.items():
    parser=Headings()
    parser.feed((htmlroot/folder/'index.html').read_text(encoding='utf-8'))
    assert any(number in h and title in h for h in parser.headings),(folder,parser.headings)

for old,target in {
 'foundations/preliminaries/equivalence-relations':'/foundations/relations/equivalence-relations/',
 'foundations/cardinality/power-sets':'/foundations/infinite-cardinality/power-sets/',
}.items():
    assert target in (htmlroot/old/'index.html').read_text(encoding='utf-8')
    assert (htmlroot/target.strip('/')/'index.html').is_file(),target

for page in ['tactics/failures', 'tactics/failures/unpack',
             'tactics/failures/function-equality',
             'tactics/failures/contexts',
             'tactics/failures/result-types',
             'tactics/automation/tracing',
             'tactics/automation/conventions']:
    assert (htmlroot/page/'index.html').is_file(),page

# Explicit migration links must land on an existing page and section, without
# relying on an old build's redirect pages being left in the destination.
main=(root/'Main.lean').read_text(encoding='utf-8-sig')
redirects=dict(re.findall(r'\("([^"\n]+)", "(/[^"\n]+)"\)',main))
sections=json.loads((htmlroot/'xref.json').read_text(encoding='utf-8'))[
    'Verso.Genre.Manual.section']['contents']
for legacy in ['preliminaries/products', 'preliminaries/equivalence-relations']:
    assert legacy in redirects, legacy
for old, target in redirects.items():
    url=urlsplit(target)
    destination=htmlroot/url.path.strip('/')/'index.html'
    assert destination.is_file(), (old,target)
    content=destination.read_text(encoding='utf-8')
    if url.fragment:
        tag=unquote(url.fragment)
        # Legacy subsection pages now redirect into a continuous unit page.
        if '<main>' not in content:
            entry=sections[tag][0]
            content=(htmlroot/entry['address'].strip('/')/'index.html').read_text(encoding='utf-8')
        assert re.search(r'\bid=[\"\']'+re.escape(tag)+r'[\"\']',content), (old,target)

for path in (root/'AlgebraBook').rglob('*.lean'):
    source=path.read_text(encoding='utf-8-sig')
    for config,code in re.findall(r'```savedLean([^\n]*)\n(.*?)\n```',source,re.S):
        if '-keep' not in config:
            assert not re.search(r'\bsorry\b|^axiom\s',code,re.M),path

exports=list((buildroot/'example-code').rglob('*.lean'))
assert len(exports)==9, len(exports)
assert not (htmlroot/'operations-and-groups').exists()
assert not (root/'AlgebraBook/Groups').exists()
homepage = (htmlroot/'index.html').read_text(encoding='utf-8')
assert 'Lean으로 배우는 기초 수학' in homepage
assert 'group_calc' not in (root/'AlgebraBook/Tactics.lean').read_text(encoding='utf-8')
print('PASS: standalone foundations book, 8 sections, links, proofs, and 9 code exports')
