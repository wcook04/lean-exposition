#!/usr/bin/env python3
"""Fail when a file about to be published matches a private source.

Usage:
    private_guard.py PATH...     scan the files under each PATH (a file or a folder)
    private_guard.py --tracked   scan the files git tracks in this repository
    private_guard.py --self-test plant a match in a scratch folder and check that the scan fails

Rules come from scripts/private_sources.txt: `re:` patterns are searched, case-insensitively, in
every file that decodes as UTF-8; `sha256:` hashes are compared with every file and every member
of a ZIP. A match prints the path and the rule's kind (never the matched text) and exits 1.
"""
from __future__ import annotations

import hashlib
import re
import subprocess
import sys
import tempfile
import zipfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
RULES = HERE / "private_sources.txt"
# The rule file and this guard name the patterns themselves; nothing else is exempt.
EXEMPT = {RULES.resolve(), Path(__file__).resolve(), (HERE.parent / "tests/test_private_guard.py").resolve()}


def load(path: Path = RULES) -> tuple[list[re.Pattern], set[str]]:
    patterns, hashes = [], set()
    for line in path.read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if line.startswith("re:"):
            patterns.append(re.compile(line[3:], re.I))
        elif line.startswith("sha256:"):
            hashes.add(line[7:].strip().lower())
    if not patterns and not hashes:
        raise SystemExit(f"{path}: no rules")
    return patterns, hashes


def files_under(paths: list[Path]):
    for path in paths:
        if path.is_file():
            yield path
        elif path.is_dir():
            yield from (p for p in sorted(path.rglob("*")) if p.is_file() and ".git" not in p.relative_to(path).parts)


def scan(paths: list[Path], patterns: list[re.Pattern], hashes: set[str]) -> list[str]:
    found = []
    for path in files_under(paths):
        if path.resolve() in EXEMPT:
            continue
        data = path.read_bytes()
        if hashlib.sha256(data).hexdigest() in hashes:
            found.append(f"{path}: hash of a private file")
            continue
        if path.suffix.lower() == ".zip":
            try:
                with zipfile.ZipFile(path) as archive:
                    for member in archive.namelist():
                        body = archive.read(member)
                        if hashlib.sha256(body).hexdigest() in hashes or any(p.search(member) for p in patterns):
                            found.append(f"{path}: a member matches a private source")
                            break
            except zipfile.BadZipFile:
                pass
        try:
            text = data.decode("utf-8")
        except UnicodeDecodeError:
            continue
        if any(p.search(text) for p in patterns):
            found.append(f"{path}: text matches a private-source pattern")
    return found


def tracked() -> list[Path]:
    root = Path(subprocess.run(["git", "rev-parse", "--show-toplevel"], capture_output=True, text=True, check=True).stdout.strip())
    names = subprocess.run(["git", "ls-files", "-z"], cwd=root, capture_output=True, check=True).stdout.split(b"\0")
    return [root / n.decode() for n in names if n]


def self_test() -> int:
    patterns, hashes = load()
    with tempfile.TemporaryDirectory() as scratch:
        root = Path(scratch)
        (root / "clean.txt").write_text("A page about the Euler equations.\n")
        if scan([root], patterns, hashes):
            print("self-test: a clean folder was flagged", file=sys.stderr)
            return 1
        (root / "planted.md").write_text("Notes on the Lennon–Pittel draft.\n")
        if not scan([root], patterns, hashes):
            print("self-test: a planted match was not caught", file=sys.stderr)
            return 1
        (root / "planted.md").unlink()
        secret = b"private bytes for the self-test\n"
        (root / "blob.bin").write_bytes(secret)
        if not scan([root], patterns, hashes | {hashlib.sha256(secret).hexdigest()}):
            print("self-test: a planted hash was not caught", file=sys.stderr)
            return 1
    print("self-test: the guard fails on planted matches and passes a clean folder")
    return 0


def main(argv: list[str]) -> int:
    if argv == ["--self-test"]:
        return self_test()
    paths = tracked() if argv == ["--tracked"] else [Path(a) for a in argv]
    if not paths:
        print(__doc__, file=sys.stderr)
        return 2
    patterns, hashes = load()
    found = scan(paths, patterns, hashes)
    for line in found:
        print(line, file=sys.stderr)
    if found:
        print(f"private-source guard: {len(found)} file(s) match; nothing may be published", file=sys.stderr)
        return 1
    print(f"private-source guard: clean ({len(patterns)} pattern(s), {len(hashes)} hash(es))")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
