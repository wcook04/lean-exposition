#!/usr/bin/env python3
"""Check authored Markdown file destinations; frozen upstream text is untouched."""
from pathlib import Path
import re
import sys
from urllib.parse import unquote, urlsplit

ROOT = Path(__file__).resolve().parents[1]
FILES = [ROOT / x for x in ('README.md', 'AGENTS.md', 'CLAUDE.md', 'CONTRIBUTING.md', 'SECURITY.md', 'examples/README.md')]
for directory in ('docs', 'skills', 'lean', 'papers'):
    FILES.extend((ROOT / directory).rglob('*.md'))
FILES.extend((ROOT / 'examples').glob('*/README.md'))
def markdown_links(text):
    """Return destinations and undefined explicit reference labels.

    Shortcut brackets may be mathematical citations, so only full and collapsed
    reference links are required to resolve. This is a bounded authoring check,
    not a Markdown renderer or remote-link availability check.
    """
    # Code and mathematical expressions can contain link-like bracket syntax.
    text = re.sub(r'(?ms)^(`{3,}|~{3,}).*?^\1[^\n]*$', '', text)
    text = re.sub(r'(?s)\$\$.*?\$\$|\\\[.*?\\\]|\\\(.*?\\\)', '', text)
    text = re.sub(r'`[^`\n]+`|(?<!\\)\$(?:\\.|[^$\n])*\$', '', text)
    normalize = lambda label: ' '.join(label.split()).casefold()
    definitions = dict((normalize(label), destination) for label, destination in
                       re.findall(r'(?m)^ {0,3}\[([^\]]+)\]:\s*(\S+)', text))
    missing = []
    for label, reference in re.findall(r'(?<!\\)\[([^\]\n]+)\][ \t]*\[([^\]\n]*)\]', text):
        key = normalize(reference or label)
        if key not in definitions:
            missing.append(key)
    links = re.findall(r'(?<!!)\[[^\]]+\]\(([^)]+)\)', text)
    return links + list(definitions.values()), sorted(set(missing))


def check(files=FILES, root=ROOT):
    errors = []
    for path in files:
        if not path.is_file():
            errors.append(f'missing document: {path.relative_to(root)}')
            continue
        links, missing = markdown_links(path.read_text())
        errors.extend(f'{path.relative_to(root)}: undefined reference link [{label}]' for label in missing)
        for link in links:
            url = urlsplit(link.strip('<>'))
            if url.scheme or not url.path:
                continue
            destination = (path.parent / unquote(url.path)).resolve()
            if not destination.is_relative_to(root) or not destination.exists():
                errors.append(f'{path.relative_to(root)}: missing or external local destination {link}')
    return errors


if __name__ == '__main__':
    errors = check()
    if errors:
        print('\n'.join(errors), file=sys.stderr)
        raise SystemExit(1)
    print(f'Local Markdown destinations and explicit references OK ({len(FILES)} authored documents)')
