"""Check the static book under a repository URL prefix, as used by GitHub Pages."""
from html.parser import HTMLParser
from pathlib import Path
from urllib.parse import unquote, urljoin, urlsplit

root = Path(__file__).resolve().parents[1]
site = root / '_out/pages'
prefix = '/lean-algebra/'
origin = 'https://example.test'


class Links(HTMLParser):
    def __init__(self):
        super().__init__()
        self.base = None
        self.urls = []
        self.static = False

    def handle_starttag(self, tag, pairs):
        attrs = dict(pairs)
        if tag == 'base':
            self.base = attrs.get('href')
            return
        if tag == 'meta' and attrs.get('name') == 'book-mode':
            self.static = attrs.get('content') == 'static'
        for key in ('href', 'src'):
            if attrs.get(key): self.urls.append(attrs[key])
        if tag == 'meta' and attrs.get('http-equiv', '').lower() == 'refresh':
            self.urls.append(attrs['content'].split('url=', 1)[1])


pages = list(site.rglob('*.html'))
assert pages, 'Stage the site first: python scripts/prepare_pages.py'
checked = 0
for page in pages:
    parser = Links()
    parser.feed(page.read_text(encoding='utf-8'))
    assert parser.static, page
    url = origin + prefix + page.relative_to(site).as_posix()
    base = urljoin(url, parser.base) if parser.base else url
    for link in parser.urls:
        target = urlsplit(urljoin(base, link))
        if target.scheme not in ('http', 'https') or target.netloc != 'example.test':
            continue
        assert target.path.startswith(prefix), (page, link, target.path)
        local = site / unquote(target.path[len(prefix):])
        if local.is_dir(): local /= 'index.html'
        assert local.is_file(), (page, link, local)
        checked += 1

assert (site / '.nojekyll').is_file()
assert not (site / 'operations-and-groups').exists()
print(f'PASS: {len(pages)} static pages and {checked} local links work below {prefix}')
