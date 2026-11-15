#!/usr/bin/env python3
"""Render the three PCP papers with the repository's Pandoc/Tectonic route.

Write intermediate TeX and unreviewed PDFs outside the checkout. Inspect the
result before copying final PDFs into the manuscript directories.
"""
import argparse
import json
from pathlib import Path
import shutil
import subprocess


MARKDOWN_FORMAT = "markdown+raw_tex+tex_math_dollars+gfm_auto_identifiers"


def copy_image_assets(source: Path, dest: Path) -> None:
    """Put local Markdown images beside generated TeX for Tectonic."""
    ast = json.loads(subprocess.check_output(
        ["pandoc", str(source), "--from", MARKDOWN_FORMAT, "--to", "json"], text=True))
    names = set()

    def visit(node):
        if isinstance(node, dict):
            if node.get("t") == "Image":
                names.add(node["c"][2][0])
            for value in node.values():
                visit(value)
        elif isinstance(node, list):
            for value in node:
                visit(value)

    visit(ast)
    for name in sorted(names):
        parts = name.split("/")
        if (not name or any(part in ("", ".", "..") for part in parts)
                or any(char in name for char in '\\?#:<>%"')
                or Path(name).is_absolute()):
            raise ValueError(f"image path must stay within the manuscript folder: {name}")
        image = (source.parent / name).resolve()
        if not image.is_relative_to(source.parent.resolve()):
            raise ValueError(f"image path escapes the manuscript folder: {name}")
        if image.suffix.lower() not in {".png", ".jpg", ".jpeg", ".pdf"}:
            raise ValueError(f"Tectonic needs a PNG, JPEG or PDF image in the manuscript: {name}")
        if not image.is_file():
            raise FileNotFoundError(f"manuscript image is missing: {name}")
        target = dest / name
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(image, target)


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
        source = family / stage / f"{name}.md"
        subprocess.run([
            "pandoc", str(source),
            "--from", MARKDOWN_FORMAT, "--to", "latex", "--standalone",
            "--lua-filter", str(family / "pdf-links.lua"),
            "--lua-filter", str(repo / "scripts/paper_anchors.lua"),
            "--include-in-header", str(family / "latex-preamble.tex"),
            "-V", "fontsize=11pt", "-V", "geometry:margin=1in",
            "-M", "keep-display-leads=true",
            "-M", "lang=en-GB", "-M", "title=", "--output", str(tex),
        ], check=True, cwd=repo)
        copy_image_assets(source, dest)
        subprocess.run(["tectonic", str(tex), "--outdir", str(dest)], check=True, cwd=repo)


if __name__ == "__main__":
    main()
