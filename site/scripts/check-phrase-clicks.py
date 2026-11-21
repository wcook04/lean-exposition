#!/usr/bin/env python3
"""Click every phrase of a paper in a real browser and report any that opens no card.

For each phrase tie of `/ties/<paper>` (the static edition's file), the paper is scrolled so
the phrase's first mark is in view, and the mouse clicks the point at the middle of its first
line, as a reader would. The phrase works when the address then names it (`n=`, the step or
`phrase:<id>`). A phrase that fails is classed by why: no mark on the page at all, or the
place it sits (abstract, caption, table, list, theorem block, footnote, link, display), so a
dead class can be found and fixed.

    python site/scripts/check-phrase-clicks.py http://localhost:5173/ [--papers short ...]

Run it against a served build (`npm run dev` with the static edition). Needs Playwright for
Python with Chromium. Exits 1 if any phrase opens no card.
"""
from __future__ import annotations

import argparse
import json
import sys
from collections import Counter
from urllib.parse import parse_qs, urlsplit

from playwright.sync_api import sync_playwright

PLACE = """
(el) => {
  const kinds = [['figcaption', 'caption'], ['table', 'table'], ['li', 'list'], ['.note, aside', 'footnote'],
    ['.math-display', 'display'], ['a', 'link'], ['blockquote', 'quotation'], ['h1, h2, h3, h4, h5, h6', 'heading']];
  for (const [sel, name] of kinds) if (el.closest(sel)) return name;
  const part = el.closest('[data-part]');
  if (part && Number(part.dataset.part) < 3) return 'front matter or abstract';
  if (el.closest('em, i') && /Theorem|Lemma|Proposition|Corollary/.test(el.closest('p')?.textContent ?? '')) return 'theorem block';
  return 'paragraph';
}
"""


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("base")
    parser.add_argument("--papers", nargs="+", default=["short", "expository", "long"])
    parser.add_argument("--width", type=int, default=1440)
    parser.add_argument("--height", type=int, default=900)
    args = parser.parse_args()
    base = args.base.rstrip("/")
    dead_total = 0
    with sync_playwright() as p:
        browser = p.chromium.launch()
        for paper in args.papers:
            page = browser.new_page(viewport={"width": args.width, "height": args.height})
            index = page.request.get(f"{base}/edition/index.json").json()
            ties = page.request.get(f"{base}/edition/{index['responses'][f'/ties/{paper}']}").json()
            ties = ties.get("data", ties)
            first = {}
            for segment, (_, _, members) in enumerate(ties["segments"]):
                first.setdefault(members[0], segment)
            page.goto(f"{base}/read/{paper}/?v=lean", wait_until="networkidle")
            # Parts away from the screen render in idle time: wait until every mark is there.
            page.evaluate("""async () => {
              let last = -1;
              for (let i = 0; i < 120; i++) {
                const n = document.querySelectorAll('.paper [data-t]').length;
                if (n === last && !document.querySelector('.part--waiting, .part[data-waiting]')) return n;
                last = n;
                window.scrollTo(0, (i % 2 ? 0 : document.body.scrollHeight) * Math.random());
                await new Promise((r) => setTimeout(r, 500));
              }
              return last;
            }""")
            dead: list[tuple[str, str]] = []
            for t, tie in enumerate(ties["ties"]):
                segment = first.get(t)
                expected = tie["record"] or f"phrase:{tie['phrase']}"
                if segment is None:
                    dead.append((tie.get("phrase", str(t)), "no segment"))
                    continue
                # A part renders when it nears the screen: bring the phrase's place there first.
                locate = """async (segment) => {
                      const marks = [...document.querySelectorAll(`.paper [data-t="${segment}"]`)];
                      const el = marks[0];
                      if (!el) return null;
                      el.scrollIntoView({block: 'center'});
                      await new Promise((r) => setTimeout(r, 120));
                      // A reader clicks the words, not a link inside them: the first point on the
                      // phrase that is not a link, else its first word.
                      const rects = marks.flatMap((m) => [...m.getClientRects()]);
                      for (const r of rects) {
                        for (let x = r.left + 4; x < r.right - 2; x += 12) {
                          const y = r.top + r.height / 2;
                          const hit = document.elementFromPoint(x, y);
                          if (hit && marks.some((m) => m.contains(hit)) && !hit.closest('a')) return {x, y, inside: true};
                        }
                      }
                      const r = rects[0] ?? el.getBoundingClientRect();
                      const x = r.left + Math.min(8, r.width / 2), y = r.top + r.height / 2;
                      return {x, y, inside: el.contains(document.elementFromPoint(x, y))};
                    }"""
                found = page.evaluate(locate, segment)
                if not found:
                    # A part far off may not have rendered yet: the reader's own address brings it.
                    page.goto(f"{base}/read/{paper}/?v=lean&l={tie['at']}", wait_until="networkidle")
                    page.wait_for_timeout(1200)
                    found = page.evaluate(locate, segment)
                if not found:
                    dead.append((tie.get("phrase", str(t)), "no mark on the page"))
                    continue
                node = ""
                for attempt in range(2):
                    page.mouse.click(found["x"], found["y"])
                    page.wait_for_timeout(700)
                    node = parse_qs(urlsplit(page.url).query).get("n", [""])[0]
                    if node == expected:
                        break
                    found = page.evaluate(locate, segment) or found
                if node != expected:
                    el = page.locator(f'.paper [data-t="{segment}"]').first
                    where = el.evaluate(PLACE)
                    dead.append((tie.get("phrase", str(t)), where if found.get("inside") else f"{where}, covered by another element"))
            print(f"{paper}: {len(ties['ties'])} phrases, {len(dead)} open no card")
            for why, n in Counter(why for _, why in dead).most_common():
                print(f"  {n} {why}: {', '.join(p for p, w in dead if w == why)[:300]}")
            dead_total += len(dead)
            page.close()
        browser.close()
    print(json.dumps({"dead": dead_total}))
    return 1 if dead_total else 0


if __name__ == "__main__":
    sys.exit(main())
