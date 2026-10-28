#!/usr/bin/env python3
"""Render the first page of each published PDF as its picture on the papers shelf.

The front page's shelf shows each paper's real first page, so the picture is the
object that its PDF link opens. A page is drawn as ink on a transparent ground at
two widths, 176 and 352 pixels, for ordinary and high-density screens; the
stylesheet lays it on paper in both colour schemes. This follows the Plectis
site's landing paper sheets (ai_workflow tools/meta/dissemination/
build_landing_paper_sheets.py), with Poppler's transparent page in place of an
image library.

manifest.json records each source PDF's SHA-256. The build shows a picture only
while it matches its PDF, and the site's tests fail with this command's name when
a re-rendered PDF has made a picture stale. Requires pdftocairo (Poppler) and
cwebp (libwebp). From the repository root:

    python site/scripts/render-paper-pages.py
    python site/scripts/render-paper-pages.py --check
"""
from __future__ import annotations

import argparse
import hashlib
import json
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

SITE = Path(__file__).resolve().parents[1]
REPO = SITE.parent
OUT = SITE / "public" / "paper-pages"
MANIFEST = OUT / "manifest.json"
# The PDFs the site publishes, as PAPER_PDFS in site/vite.config.ts names them;
# the site's tests check that every published PDF has a current picture here.
PAPERS = {
    "long": ("papers/qaoa-sk/long/reasoning-record.pdf", "long-record"),
    "short": ("papers/qaoa-sk/short/paper.pdf", "short-paper"),
    "expository": ("papers/qaoa-sk/expository/main.pdf", "exposition"),
    "architecture": ("papers/architecture/paper.pdf", "architecture"),
}
WIDTHS = (176, 352)


def tool(name: str) -> str:
    path = shutil.which(name)
    if path is None:
        raise SystemExit(f"{name} is required to render the paper pages")
    return path


def render(pdf: Path, name: str, tmp: Path) -> dict[str, object]:
    files: dict[str, str] = {}
    height = 0
    for width in WIDTHS:
        png = tmp / f"{name}-{width}"
        subprocess.run(
            [tool("pdftocairo"), "-png", "-transp", "-singlefile", "-f", "1", "-l", "1",
             "-scale-to-x", str(width), "-scale-to-y", "-1", str(pdf), str(png)],
            check=True,
        )
        target = OUT / f"{name}-{width}.webp"
        subprocess.run(
            [tool("cwebp"), "-quiet", "-q", "84", "-alpha_q", "90", "-m", "6",
             f"{png}.png", "-o", str(target)],
            check=True,
        )
        files[str(width)] = target.name
        # PNG width and height are big-endian integers at bytes 16-24.
        header = Path(f"{png}.png").read_bytes()[16:24]
        height = int.from_bytes(header[4:8], "big")
    return {"files": files, "width": WIDTHS[-1], "height": height}


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--check", action="store_true", help="report pictures whose PDF changed; write nothing")
    args = parser.parse_args(argv)
    manifest = json.loads(MANIFEST.read_text(encoding="utf-8")) if MANIFEST.exists() else {}
    stale: list[str] = []
    rows: dict[str, dict[str, object]] = {}
    with tempfile.TemporaryDirectory() as tmp:
        for stage, (relative, name) in PAPERS.items():
            pdf = REPO / relative
            digest = "sha256:" + hashlib.sha256(pdf.read_bytes()).hexdigest()
            if args.check:
                row = manifest.get(stage, {})
                files = row.get("files", {}).values()
                if row.get("pdf_sha256") != digest or not files or not all((OUT / f).exists() for f in files):
                    stale.append(stage)
                continue
            OUT.mkdir(parents=True, exist_ok=True)
            rows[stage] = {"pdf": relative, "pdf_sha256": digest, **render(pdf, name, Path(tmp))}
            print(f"{stage}: {relative} -> {', '.join(rows[stage]['files'].values())}")
    if args.check:
        if stale:
            print("stale paper pages (run python site/scripts/render-paper-pages.py): " + ", ".join(stale))
            return 1
        print("paper pages match their PDFs")
        return 0
    MANIFEST.write_text(json.dumps(rows, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    sys.exit(main())
