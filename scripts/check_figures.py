#!/usr/bin/env python3
"""Fail when a figure a paper's documents reference is not in the build, or not on the live site.

Usage:
    check_figures.py <paper> DIST             every local Markdown figure in instances/<paper>/papers/*/paper.md
                                              must exist as DIST/paper-figures/<slot>/<name>
    check_figures.py <paper> DIST --live URL  also fetch URL/paper-figures/<slot>/<name> and require 200

Run from the repository root while an adapted edition is staged (scripts/build_library_paper.sh does this).
"""
from __future__ import annotations

import re
import sys
import urllib.request
from pathlib import Path

FIGURE = re.compile(r"!\[[^\]]*\]\((?:\./)?((?:figures/)?[\w.-]+\.(?:svg|png|jpe?g|webp))\)", re.I)


def references(paper: str) -> list[tuple[str, str]]:
    refs = []
    for md in sorted(Path(f"instances/{paper}/papers").glob("*/paper.md")):
        for link in FIGURE.findall(md.read_text(encoding="utf-8")):
            refs.append((md.parent.name, Path(link).name))
    return sorted(set(refs))


def status(url: str) -> int:
    try:
        with urllib.request.urlopen(urllib.request.Request(url, method="GET"), timeout=30) as r:
            return r.status
    except urllib.error.HTTPError as e:
        return e.code
    except Exception:
        return 0


def main(argv: list[str]) -> int:
    if len(argv) not in (2, 4) or (len(argv) == 4 and argv[2] != "--live"):
        print(__doc__)
        return 2
    paper, dist = argv[0], Path(argv[1])
    live = argv[3].rstrip("/") if len(argv) == 4 else None
    bad = []
    refs = references(paper)
    for slot, name in refs:
        if not (dist / "paper-figures" / slot / name).is_file():
            bad.append(f"missing from the build: paper-figures/{slot}/{name}")
        if live:
            code = status(f"{live}/paper-figures/{slot}/{name}")
            if code != 200:
                bad.append(f"live {code}: {live}/paper-figures/{slot}/{name}")
    for line in bad:
        print(line)
    where = " and live" if live else ""
    print(f"figures: {len(refs)} referenced, {len(bad)} problem(s){where}")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
