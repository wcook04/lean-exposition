#!/usr/bin/env python3
"""Rebuild the two PCP navigation figures beside their manuscripts.

Adapted from diagram-design's architecture example (MIT, pinned in README)
and Matplotlib's table_demo.py (Matplotlib licence). See the adjacent licences.
Requires matplotlib and cairosvg; no network or external font download.
"""
from pathlib import Path
from xml.etree import ElementTree as ET
import copy
import re

import cairosvg
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

FAMILY = Path(__file__).resolve().parents[1]
NS = "http://www.w3.org/2000/svg"
ET.register_namespace("", NS)
INK = "#263742"
MUTED = "#465b68"
BLUE = "#285c76"
PAPER = "#ffffff"

# Adapt the upstream example's actual two-layer card, tag, title and subtitle
# component. Replace its web-stack labels, preserve the component hierarchy,
# enlarge its type for print, and discard the decorative background and numerals.
CARD = ET.fromstring('''<g xmlns="http://www.w3.org/2000/svg">
  <rect x="0" y="0" width="288" height="96" rx="6" fill="#ffffff"/>
  <rect x="0" y="0" width="288" height="96" rx="6" fill="#f7f9fa" stroke="#a3b0b6" stroke-width="1.2"/>
  <text x="16" y="23" fill="#465b68" font-size="12" font-family="Georgia, serif">TAG</text>
  <text x="16" y="48" fill="#263742" font-size="17" font-weight="bold" font-family="Georgia, serif">TITLE</text>
  <text x="16" y="72" fill="#465b68" font-size="14" font-family="Georgia, serif">SUBTITLE</text>
</g>''')


def element(parent, tag, **attrs):
    return ET.SubElement(parent, f"{{{NS}}}{tag}", {k.replace('_', '-'): str(v) for k, v in attrs.items()})


def text(parent, x, y, words, size=14, **attrs):
    node = element(parent, "text", x=x, y=y, fill=INK, font_size=size,
                   font_family="Georgia, serif", **attrs)
    node.text = words
    return node


def proof_map():
    root = ET.Element(f"{{{NS}}}svg", viewBox="0 0 740 644", role="img",
                      attrib={"aria-labelledby": "map-title map-desc"})
    element(root, "title", id="map-title").text = "From algebraic tests to the PCP theorem"
    element(root, "desc", id="map-desc").text = (
        "Low-degree tests and binary encodings supply soundness of the binary low-degree test. "
        "Its four nearby polynomials and the local-correction and zero-on-grid bounds feed the three-colouring verifier. "
        "The verifier combines with machine and reduction contracts to give the PCP theorem. "
        "This is a selected mathematical-use map, not an extracted Lean graph.")
    defs = element(root, "defs")
    marker = element(defs, "marker", id="arrow", markerWidth=8, markerHeight=6,
                     refX=7, refY=3, orient="auto")
    element(marker, "polygon", points="0 0, 8 3, 0 6", fill=BLUE)
    element(root, "rect", width=740, height=644, fill=PAPER)
    text(root, 20, 26, "FROM THE TESTS TO THE THEOREM", 15, letter_spacing="1")
    # Orthogonal rounded paths and arrow markers adapted from the source example.
    paths = ["M 164,160 V 204", "M 576,160 V 176 Q 576,184 568,184 H 252 Q 244,184 244,192 V 204",
             "M 308,252 H 432", "M 164,300 V 332 Q 164,340 172,340 H 284 V 372",
             "M 576,300 V 332 Q 576,340 568,340 H 460 V 372",
             "M 460,468 V 512", "M 308,560 H 432"]
    for d in paths:
        element(root, "path", d=d, fill="none", stroke=BLUE, stroke_width=1.6,
                marker_end="url(#arrow)")
    # Each edge names the particular guarantee used at its destination.
    edge_labels = [
        (150, 180, "point-versus-line", "end"), (150, 196, "bound", "end"),
        (412, 178, "binary error bounds", "middle"),
        (370, 230, "distance", "middle"), (370, 246, "bounds", "middle"),
        (178, 323, "four fixed nearby polynomials", "start"),
        (562, 323, "grid-constraint bounds", "end"),
        (446, 497, "completeness + soundness", "end"),
        (370, 538, "time, randomness", "middle"), (370, 554, "and NP reduction", "middle"),
    ]
    for x, y, label, anchor in edge_labels:
        text(root, x, y, label, 13.5, text_anchor=anchor)
    cards = [
        (20, 64, "ALGEBRAIC CHAPTER", "Low-degree tests", "Standard; point-versus-line"),
        (432, 64, "BINARY CHAPTER", "Binary encodings", "Set-multilinear encoding; Hadamard test"),
        (20, 204, "SOUNDNESS BOUND (B15)", "Binary low-degree test", "One nearby polynomial; two distances"),
        (432, 204, "BOUNDS (B16), (B25)", "Local correction", "and the zero-on-grid test"),
        (228, 372, "ASSEMBLED VERIFIER", "Three-colouring", "Four nearby polynomials; seven checks"),
        (20, 512, "IMPLEMENTATION CONTRACTS", "Machines and reductions", "Fair bits; costs; reduction from NP"),
        (432, 512, "ENDPOINT", "The PCP theorem", "Log random bits; constant queries"),
    ]
    for x, y, tag, title, subtitle in cards:
        card = copy.deepcopy(CARD)
        card.set("transform", f"translate({x},{y})")
        for n, label in zip(list(card)[2:], (tag, title, subtitle)):
            n.text = label
        if tag == "ASSEMBLED VERIFIER":
            list(card)[1].set("fill", "#eef4f7")
            list(card)[1].set("stroke", BLUE)
        root.append(card)
    text(root, 20, 634, "Each arrow names a guarantee used at its destination. Further dependencies are omitted.", 13)
    path = FAMILY / "long/proof-map.svg"
    ET.ElementTree(root).write(path, encoding="utf-8", xml_declaration=True)
    cairosvg.svg2png(url=str(path), write_to=str(path.with_suffix(".png")), scale=3)


def table_checks():
    # Adapt table_demo.py's cellText / rowLabels / colLabels table construction.
    # Here the cells record use, not a numeric series; remove its stacked bars.
    columns = ["1\nColour\nLDT\n ", "2\nVertex\nLDT\n ", "3\nDifference\nLDT\n ",
               "4\nEdge\nLDT\n ", "5\nVertex\nzero on\ngrid", "6\nEdge\nzero on\ngrid", "7\nDifference\ncheck\n "]
    rows = [r"Colour $\chi$ · points", r"Colour $\chi$ · lines",
            r"Vertex $M_V$ · points", r"Vertex $M_V$ · lines",
            r"Difference $\chi'$ · points", r"Difference $\chi'$ · lines",
            r"Edge $M_E$ · points", r"Edge $M_E$ · lines"]
    uses = [{0, 4, 6}, {0}, {1, 4}, {1, 4}, {2, 5, 6}, {2}, {3, 5}, {3, 5}]
    cell_text = [[label] + ["•" if c in u else "" for c in range(7)]
                 for label, u in zip(rows, uses)]
    plt.rcParams.update({"font.family": "DejaVu Serif", "svg.fonttype": "none"})
    fig, ax = plt.subplots(figsize=(9.2, 5.8))
    fig.patch.set_facecolor("white")
    ax.axis("off")
    colors = ["#f3f6f7" if r // 2 % 2 == 0 else "white" for r in range(8)]
    table = ax.table(cellText=cell_text, colLabels=["Stored table"] + columns,
                     colWidths=[0.34] + [0.65 / 7] * 7,
                     cellLoc="center", loc="center", bbox=[0, 0.16, 0.99, 0.68])
    table.auto_set_font_size(False)
    table.set_fontsize(12)
    for (r, c), cell in table.get_celld().items():
        cell.set_edgecolor("#c7d0d5")
        cell.set_linewidth(0.5)
        cell.set_text_props(color=INK)
        if r == 0:
            cell.set_height(cell.get_height() * 2.2)
            cell.set_text_props(fontsize=10.8)
            cell.set_facecolor("#e9eff2")
        elif c >= 0:
            cell.set_facecolor(colors[r-1])
            cell.set_text_props(fontsize=18)
        if c == 5:
            cell.set_facecolor("#eee5d5")
            cell.set_edgecolor("#93723c")
            cell.set_linewidth(0.9)
        if c == 0:
            cell.set_text_props(fontsize=12, ha="left")
            cell.PAD = 0.04
    ax.text(0.0, 0.97, "EIGHT TABLES, SEVEN CHECKS", transform=ax.transAxes,
            fontsize=14, color=INK, va="top")
    ax.text(0.0, 0.895, "Each dot marks a table the check may query. LDT = binary low-degree test.",
            transform=ax.transAxes, fontsize=10, color=MUTED)
    ax.text(0.0, 0.09, "Worked trace: check 5 follows the colour bit and two local corrections of the vertex certificate.",
            transform=ax.transAxes, fontsize=10, color=INK)
    ax.text(0.0, 0.035, "All seven checks must pass. Public adjacency is computed from the input graph.",
            transform=ax.transAxes, fontsize=10, color=MUTED)
    fig.subplots_adjust(left=0.02, right=0.99, bottom=0.02, top=0.98)
    dest = FAMILY / "expository/table-checks"
    fig.savefig(dest.with_suffix(".png"), dpi=300)
    fig.savefig(dest.with_suffix(".svg"), metadata={"Title": "Eight tables and seven checks",
                "Description": "Incidence matrix showing which stored tables each verifier check may query. The worked trace follows the vertex zero-on-grid test, column five."})
    svg = dest.with_suffix(".svg")
    markup = svg.read_text()
    markup = markup.replace('<svg ', '<svg role="img" aria-labelledby="checks-title checks-desc" ', 1)
    description = ('<title id="checks-title">Eight tables and seven checks</title>'
                   '<desc id="checks-desc">Dots show which physical tables each check may query. '
                   'Column five is the vertex zero-on-grid test, the branch illustrated by the worked trace.</desc>')
    markup = re.sub(r'(<svg[^>]*>)', lambda m: m.group(1) + description, markup, count=1)
    svg.write_text(markup)
    plt.close(fig)


if __name__ == "__main__":
    proof_map()
    table_checks()
