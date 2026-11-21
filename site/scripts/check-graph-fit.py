#!/usr/bin/env python3
"""Check in a real browser that the reader's graph frames its subject whole.

After a phrase is clicked on the Graph tab, and after the paper is scrolled to a new
passage, every card the graph frames (the pane's `data-framed` ids: the selected card with
its neighbours, a declaration's Lean neighbourhood, or the passage's cards) must lie inside
the visible part of the graph: under its head, above the Lean in a split, inside the pane.
The Graph tab must always be split, and the part under the graph must never be empty.

    python site/scripts/check-graph-fit.py http://localhost:5173/ [--width 1440 --height 900]

Run it against a served build of either instance (`npm run dev` or `npm run preview`). It
needs Playwright for Python with Chromium installed. It exits 1 and names each card outside.
"""
from __future__ import annotations

import argparse
import sys

from playwright.sync_api import sync_playwright

VISIBLE = r"""
() => {
  const pane = document.querySelector('.map-pane');
  if (!pane) return {error: 'no pane'};
  if (!pane.hasAttribute('data-framed')) return {error: 'the graph has not framed anything yet'};
  const ids = (pane.getAttribute('data-framed') || '').split(' ').filter(Boolean);
  const body = pane.querySelector('.map-pane__body').getBoundingClientRect();
  const lean = pane.matches('.map-pane--split') ? pane.querySelector('.lean-page').getBoundingClientRect() : null;
  const bottom = lean ? Math.min(body.bottom, lean.top - 11) : body.bottom;
  const outside = [];
  for (const id of ids) {
    const cards = [...pane.querySelectorAll('.card[data-record]')].filter((c) => c.dataset.record === id);
    if (!cards.length) continue;  // an assumption, drawn as a tag on another card
    const ok = cards.some((c) => {
      const r = c.getBoundingClientRect();
      return r.top >= body.top - 1 && r.bottom <= bottom + 1 && r.left >= body.left - 1 && r.right <= body.right + 1;
    });
    if (!ok) outside.push(id);
  }
  const page = pane.querySelector('.lean-page');
  const below = page ? page.innerText.replace(/\s+/g, ' ').trim() : '';
  return {ids, outside, split: pane.matches('.map-pane--split'), below: below.length};
}
"""


def check(page, label: str, failures: list[str]) -> None:
    page.wait_for_timeout(2600)
    found = page.evaluate(VISIBLE)
    if found.get("error"):
        failures.append(f"{label}: {found['error']}")
    elif not found["ids"] and found.get("split") and found["below"] >= 30:
        print(f"{label}: nothing on the map to frame here; the Lean part holds {found['below']} characters")
    elif not found.get("split"):
        failures.append(f"{label}: the Graph tab is not split")
    elif found["below"] < 30:
        failures.append(f"{label}: the part under the graph is empty")
    elif found["outside"]:
        failures.append(f"{label}: outside the visible graph: {', '.join(found['outside'])}")
    else:
        print(f"{label}: {len(found['ids'])} framed cards, all inside")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("base", help="the served site's root, e.g. http://localhost:5173/")
    parser.add_argument("--width", type=int, default=1440)
    parser.add_argument("--height", type=int, default=900)
    parser.add_argument("--papers", nargs="+", default=["short", "expository", "long"])
    args = parser.parse_args()
    base = args.base.rstrip("/")
    failures: list[str] = []
    with sync_playwright() as p:
        browser = p.chromium.launch()
        for paper in args.papers:
            page = browser.new_page(viewport={"width": args.width, "height": args.height})
            page.goto(f"{base}/read/{paper}/?v=graph", wait_until="networkidle")
            page.wait_for_timeout(1500)
            # Following the paper: two passages apart.
            for step in (1, 2):
                page.mouse.wheel(0, 1600)
                check(page, f"{paper}: reading, scroll {step}", failures)
            # A phrase clicked on the Graph tab, then another further on.
            for nth in (5, 25):
                phrase = page.locator(".paper .tie[data-tone]").nth(nth)
                phrase.scroll_into_view_if_needed()
                box = phrase.bounding_box()
                page.mouse.click(box["x"] + 4, box["y"] + box["height"] / 2)
                check(page, f"{paper}: phrase {nth} opened", failures)
            page.close()
        browser.close()
    for line in failures:
        print("FAIL", line)
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
