#!/usr/bin/env python3
"""Check the relocated reading packet's PDF files and named companion links.

Requires PyMuPDF. This checks structure, not appearance or mathematics.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import pymupdf


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", type=Path, help="directory containing long/, short/, expository/")
    args = parser.parse_args()
    root = args.directory.resolve()
    reports = []
    errors = []
    for relative in ("long/reasoning-record.pdf", "short/paper.pdf", "expository/main.pdf"):
        path = root / relative
        if not path.is_file():
            errors.append(f"Missing {relative}")
            continue
        with pymupdf.open(path) as doc:
            links = []
            for xref in range(1, doc.xref_length()):
                if doc.xref_get_key(xref, "A/S") != ("name", "/GoToR"):
                    continue
                kind, filename = doc.xref_get_key(xref, "A/F")
                dest_kind, dest = doc.xref_get_key(xref, "A/D")
                if kind != "string":
                    errors.append(f"{relative}: unsupported file action at xref {xref}")
                    continue
                target = (path.parent / filename).resolve()
                if root not in target.parents or not target.is_file():
                    errors.append(f"{relative}: missing or external companion {filename}")
                    continue
                with pymupdf.open(target) as other:
                    if dest_kind == "string":
                        if dest not in other.resolve_names():
                            errors.append(f"{relative}: missing destination {filename}#{dest}")
                    elif dest_kind == "array":
                        page = re.match(r"\[(\d+)", dest)
                        if not page or int(page.group(1)) >= len(other):
                            errors.append(f"{relative}: invalid destination {filename}:{dest}")
                    else:
                        errors.append(f"{relative}: unsupported destination {dest_kind}:{dest}")
                links.append({"file": filename, "destination": dest})
            reports.append({"file": relative, "pages": len(doc),
                            "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
                            "companion_links": links})
    print(json.dumps({"ok": not errors, "papers": reports, "errors": errors}, indent=2))
    raise SystemExit(bool(errors))


if __name__ == "__main__":
    main()
