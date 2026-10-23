#!/usr/bin/env python3
"""Check authored Markdown file destinations; frozen upstream text is untouched."""
from pathlib import Path
import re
import sys
from urllib.parse import unquote, urlsplit

ROOT = Path(__file__).resolve().parents[1]
FILES = [ROOT / x for x in ('README.md', 'AGENTS.md', 'CONTRIBUTING.md', 'SECURITY.md')]
for directory in ('docs', 'skills', 'lean', 'papers'):
    FILES.extend((ROOT / directory).rglob('*.md'))
FILES.extend((ROOT / 'examples').glob('*/README.md'))
errors = []
for path in FILES:
    if not path.is_file():
        errors.append(f'missing document: {path.relative_to(ROOT)}')
        continue
    text = path.read_text()
    # Code and mathematical expressions can contain link-like bracket syntax.
    text = re.sub(r'(?ms)^(`{3,}|~{3,}).*?^\1[^\n]*$', '', text)
    text = re.sub(r'(?s)\$\$.*?\$\$|\\\[.*?\\\]|\\\(.*?\\\)', '', text)
    text = re.sub(r'`[^`\n]+`|(?<!\\)\$(?:\\.|[^$\n])*\$', '', text)
    links = re.findall(r'(?<!!)\[[^\]]+\]\(([^)]+)\)', text)
    links += re.findall(r'(?m)^\[[^\]]+\]:\s*(\S+)', text)
    for link in links:
        url = urlsplit(link.strip('<>'))
        if url.scheme or not url.path:
            continue
        destination = (path.parent / unquote(url.path)).resolve()
        if not destination.is_relative_to(ROOT) or not destination.exists():
            errors.append(f'{path.relative_to(ROOT)}: missing or external local destination {link}')
if errors:
    print('\n'.join(errors), file=sys.stderr)
    raise SystemExit(1)
print(f'Local Markdown destinations OK ({len(FILES)} authored documents)')
