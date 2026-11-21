#!/usr/bin/env python3
"""Check in a real browser that every graph card shows its whole short title inside its box.

Renders the full map, the reader's graph pane for each paper (at the top and two places
further on), and the Lean neighbourhood of phrases that are no step of the map, then checks
every card drawn:

- no title is shortened (`data-short`, the map's mark for a cut title), and none is a word
  followed by an ellipsis;
- no title's text runs outside its card (checked after KaTeX has set it);
- no title is a sentence: at most twelve words.

    python site/scripts/check-card-titles.py http://localhost:5173/ [--width 1440 --height 900]

Exits 1 and names each card that fails.
"""
from __future__ import annotations

import argparse
import re
import sys

from playwright.sync_api import sync_playwright

CARDS = """
() => {
  const out = [];
  const seen = (el) => { const r = el.getBoundingClientRect(); return r.width > 0 && r.height > 0 && r.bottom > 0 && r.top < innerHeight; };
  for (const card of document.querySelectorAll('.card[data-record], .nb-card')) {
    if (!seen(card)) continue;
    // A map card holds a full and a compact title and shows one: check the one shown.
    const title = [...card.querySelectorAll('.card__ctitle, .card__title, .nb-card__title')].find((el) => {
      const r = el.getBoundingClientRect();
      return r.width > 0 && r.height > 0 && getComputedStyle(el).visibility !== 'hidden';
    });
    if (!title) continue;
    const box = card.getBoundingClientRect();
    const words = title.getBoundingClientRect();
    const shown = (title.dataset.short || title.textContent || '').trim();
    out.push({
      id: card.dataset.record || '',
      text: shown,
      short: !!title.dataset.short,
      // Line boxes round by a pixel or two at a zoomed scale; text past that is text outside.
      over: title.scrollWidth > title.clientWidth + 3 || title.scrollHeight > title.clientHeight + 3
        || words.right > box.right + 1 || words.bottom > box.bottom + 1 || words.left < box.left - 1,
    });
  }
  return out;
}
"""


def inspect(page, label: str, failures: list[str]) -> int:
    # After the camera's last glide (the fit and its fallbacks end within two seconds).
    page.wait_for_timeout(2600)
    cards = page.evaluate(CARDS)
    for card in cards:
        text = card["text"]
        why = []
        if card["short"]:
            why.append("title shortened")
        if re.fullmatch(r"\S+\s*…", text):
            why.append("one word and an ellipsis")
        if card["over"]:
            why.append("text outside the card")
        if len(text.split()) > 12:
            why.append(f"{len(text.split())}-word title")
        if why:
            failures.append(f"{label}: {card['id'] or text[:40]}: {', '.join(why)} ({text[:60]!r})")
    return len(cards)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("base")
    parser.add_argument("--width", type=int, default=1440)
    parser.add_argument("--height", type=int, default=900)
    args = parser.parse_args()
    base = args.base.rstrip("/")
    failures: list[str] = []
    with sync_playwright() as p:
        browser = p.chromium.launch()
        page = browser.new_page(viewport={"width": args.width, "height": args.height})
        page.goto(f"{base}/map", wait_until="networkidle")
        print(f"map: {inspect(page, 'map', failures)} cards")
        for paper in ("short", "expository", "long"):
            page.goto(f"{base}/read/{paper}/?v=graph", wait_until="networkidle")
            total = inspect(page, f"{paper} pane", failures)
            for _ in range(2):
                page.mouse.wheel(0, 2400)
                total += inspect(page, f"{paper} pane", failures)
            # A few phrases on the Graph tab: their step, or their Lean neighbours.
            for nth in (3, 12, 30):
                phrase = page.locator(".paper .tie[data-tone]").nth(nth)
                if not phrase.count():
                    continue
                phrase.evaluate("e => e.scrollIntoView({block: 'center'})")
                page.wait_for_timeout(300)
                box = phrase.bounding_box()
                page.mouse.click(box["x"] + 4, box["y"] + box["height"] / 2)
                total += inspect(page, f"{paper} phrase {nth}", failures)
            print(f"{paper}: {total} cards")
        browser.close()
    for line in failures:
        print("FAIL", line)
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
