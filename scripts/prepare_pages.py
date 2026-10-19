"""Stage the generated book for static hosting, without the local Lean editor."""
from pathlib import Path
import shutil

ROOT = Path(__file__).resolve().parents[1]


def main():
    output = (ROOT / '_out').resolve()
    source = (output / 'html-multi').resolve()
    destination = (output / 'pages').resolve()
    # Only replace this script's generated staging folder, never the source or workspace.
    assert destination.parent == output and destination.name == 'pages'
    assert source.parent == output and source != destination
    if not (source / 'index.html').is_file():
        raise SystemExit('Generate the book first: lake exe textbook')
    if destination.exists():
        shutil.rmtree(destination)
    shutil.copytree(source, destination)
    marker = '<meta name="book-mode" content="static">'
    for page in destination.rglob('*.html'):
        html = page.read_text(encoding='utf-8')
        assert '</head>' in html, page
        page.write_text(html.replace('</head>', marker + '</head>', 1), encoding='utf-8')
    (destination / '.nojekyll').write_text('', encoding='utf-8')
    print('Static book staged in _out/pages.')


if __name__ == '__main__':
    main()
