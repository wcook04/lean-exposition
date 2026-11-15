#!/usr/bin/env python3
"""Render the three PCP papers with the repository's Pandoc/Tectonic route.

Write intermediate TeX and unreviewed PDFs outside the checkout. Inspect the
result before copying final PDFs into the manuscript directories.
"""
import argparse
from pathlib import Path
import subprocess


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--stage", choices=("all", "long", "short", "expository"), default="all")
    args = parser.parse_args()
    family = Path(__file__).resolve().parent
    repo = family.parents[1]
    out = args.out.resolve()
    if out == repo or repo in out.parents:
        parser.error("use an intermediate output directory outside the checkout")
    names = {"long": "reasoning-record", "short": "paper", "expository": "main"}
    for stage, name in names.items():
        if args.stage not in ("all", stage):
            continue
        dest = out / stage
        dest.mkdir(parents=True, exist_ok=True)
        tex = dest / f"{name}.tex"
        subprocess.run([
            "pandoc", str(family / stage / f"{name}.md"),
            "--from", "markdown+raw_tex+tex_math_dollars+gfm_auto_identifiers", "--to", "latex", "--standalone",
            "--lua-filter", str(family / "pdf-links.lua"),
            "--lua-filter", str(repo / "scripts/paper_anchors.lua"),
            "--include-in-header", str(family / "latex-preamble.tex"),
            "-V", "fontsize=11pt", "-V", "geometry:margin=1in",
            "-M", "keep-display-leads=true",
            "-M", "lang=en-GB", "-M", "title=", "--output", str(tex),
        ], check=True, cwd=repo)
        subprocess.run(["tectonic", str(tex), "--outdir", str(dest)], check=True, cwd=repo)


if __name__ == "__main__":
    main()
