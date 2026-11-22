#!/usr/bin/env python3
"""Fail when wording from private files appears in files about to be published.

    check_private_wording.py --private P [P ...] --public-source S [S ...] --scan D [D ...] [--words 8]

A hash guard (private_guard.py) catches a private file copied whole; this catches its wording
carried into anything else. Every run of --words consecutive words (lower-cased, with TeX commands,
markup and punctuation removed) of the --private files is a private phrase, unless it also occurs in
a --public-source file: the texts that are meant to be published and that private notes may quote
(an edition's TeX, its public change map, the authors' own source). Every text file under --scan,
and the text of every PDF there (poppler's pdftotext), is searched for the remaining phrases. A
match prints the published file and the number of phrases it shares (never the phrases) and exits 1.
With --baseline (the site as it is published now), wording already published is reported apart, so
the check answers what a new build adds.
Folders and ZIP files given as --private are read whole.
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import zipfile
from pathlib import Path

TEXT = {".md", ".json", ".txt", ".tex", ".html", ".js", ".css", ".xml", ".patch", ".log", ".csv", ".svg", ".toml", ".yml", ".yaml", ".py", ".lean"}


def words(text: str) -> list[str]:
    text = re.sub(r"\\[A-Za-z]+\*?", " ", text)
    return re.findall(r"[a-z0-9]+", text.lower())


def shingles(text: str, n: int) -> set[tuple[str, ...]]:
    """Runs of n words that read as prose: at least n - 3 of them words of three or more letters (so
    runs of identifiers, ids and numbers, which any two texts about one paper share, do not count)."""
    w = words(text)
    runs = (tuple(w[i:i + n]) for i in range(len(w) - n + 1))
    return {r for r in runs if sum(1 for t in r if len(t) >= 3 and t.isalpha()) >= n - 3}


def texts(path: Path):
    """(name, text) for a file, every text file of a folder, every member of a ZIP, and a PDF's text."""
    files = sorted(p for p in path.rglob("*") if p.is_file()) if path.is_dir() else [path]
    for f in files:
        suffix = f.suffix.lower()
        if suffix == ".zip":
            with zipfile.ZipFile(f) as z:
                for name in z.namelist():
                    if Path(name).suffix.lower() in TEXT:
                        yield f"{f}!{name}", z.read(name).decode("utf-8", "replace")
        elif suffix == ".pdf":
            run = subprocess.run(["pdftotext", "-q", str(f), "-"], capture_output=True, text=True)
            yield str(f), run.stdout
        elif suffix in TEXT or not suffix:
            try:
                raw = f.read_text(encoding="utf-8")
            except UnicodeDecodeError:
                continue
            if suffix == ".json":
                # The strings a JSON file holds, as text: its escapes would otherwise glue words together.
                try:
                    raw = "\n".join(strings(json.loads(raw)))
                except ValueError:
                    pass
            yield str(f), raw


def strings(value):
    if isinstance(value, str):
        yield value
    elif isinstance(value, dict):
        for k, v in value.items():
            yield k
            yield from strings(v)
    elif isinstance(value, list):
        for v in value:
            yield from strings(v)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--private", type=Path, nargs="+", required=True)
    ap.add_argument("--public-source", type=Path, nargs="+", required=True)
    ap.add_argument("--scan", type=Path, nargs="+", required=True)
    ap.add_argument("--baseline", type=Path, nargs="*", default=[],
                    help="files already published (the live site): their wording is not new, and is reported apart")
    ap.add_argument("--words", type=int, default=8)
    a = ap.parse_args()
    private: set = set()
    for p in a.private:
        for _, text in texts(p):
            private |= shingles(text, a.words)
    allowed: set = set()
    for p in a.public_source:
        for _, text in texts(p):
            allowed |= shingles(text, a.words)
    secret = private - allowed
    published: set = set()
    for p in a.baseline:
        for _, text in texts(p):
            published |= shingles(text, a.words)
    already = secret & published
    secret -= published
    found = []
    for p in a.scan:
        for name, text in texts(p):
            hits = shingles(text, a.words) & secret
            if hits:
                found.append((name, len(hits)))
    for name, n in found:
        print(f"{name}: {n} phrase(s) of {a.words} words from a private file")
    if a.baseline:
        print(f"{len(already)} phrase(s) shared with private files were already published before this build (baseline)")
    print(f"private wording check: {len(private)} private phrases, {len(secret)} not in any public source; "
          f"{'FOUND in ' + str(len(found)) + ' file(s)' if found else 'none in the published files'}")
    return 1 if found else 0


if __name__ == "__main__":
    sys.exit(main())
