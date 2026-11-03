"""Real input on the references: open, Escape, scroll, click, ten rounds on each paper.

Usage: check-reference-cards.py <site-url> [--rounds N]

Serve a build first, or point it at a dev server. Needs Playwright for Python and Chromium. Each
round points at the first reference in view that opens in place, at the place a tester's eye picks
(ten pixels into its box, half way down), and that card must open under its sentence with its cue
and no new tab, then close on Escape on the same pixel. A wrapped link is the case that matters:
the middle of its box is the leading between its two lines.
"""

import argparse
import sys

from playwright.sync_api import sync_playwright

PAPERS = ("short", "long", "expository")
SPOT = """() => {
  for (const a of document.querySelectorAll('.part__text a[data-ref]')) {
    const href = a.getAttribute('href') ?? '';
    if (a.classList.contains('companion') || (href.startsWith('#') && !/^#(thm|lem|prop|cor|eq|fig|question)-/.test(href))) continue;
    const r = a.getBoundingClientRect();
    if (r.top > 170 && r.bottom < 640) return {x: r.left + 10, y: r.top + r.height / 2, words: a.textContent.slice(0, 44), lines: a.getClientRects().length};
  }
  return null;
}"""
SEEN = """() => {
  const card = document.querySelector('.ref-inset');
  return {insets: document.querySelectorAll('.ref-inset').length, y: scrollY, cue: card ? getComputedStyle(card).animationName : ''};
}"""


def wheel(page, steps):
    page.mouse.move(380, 400)
    for _ in range(steps):
        page.mouse.wheel(0, 120)
        page.wait_for_timeout(30)
    page.wait_for_timeout(300)


def run(page, base, stage, rounds):
    page.goto(f"{base}/read/{stage}", wait_until="load")
    page.wait_for_selector(".part__text", timeout=60000)
    page.wait_for_timeout(2500)
    opened = wrapped = 0
    misses = []
    for number in range(rounds):
        spot = page.evaluate(SPOT)
        for _ in range(60):
            if spot:
                break
            wheel(page, 5)
            spot = page.evaluate(SPOT)
        if not spot:
            misses.append((number, "no reference in view"))
            continue
        tabs = len(page.context.pages)
        top = page.evaluate("scrollY")
        page.mouse.move(spot["x"], spot["y"])
        page.wait_for_timeout(400)
        page.mouse.click(spot["x"], spot["y"])
        page.wait_for_timeout(450)
        seen = page.evaluate(SEEN)
        wrapped += spot["lines"] > 1
        if seen["insets"] != 1 or len(page.context.pages) != tabs or seen["cue"] != "ref-inset-cue":
            misses.append((number, spot["words"], seen))
        else:
            opened += 1
        page.keyboard.press("Escape")
        page.wait_for_timeout(450)
        seen = page.evaluate(SEEN)
        if seen["insets"] or abs(seen["y"] - top) >= 1:
            misses.append((number, "Escape", spot["words"], seen["insets"], seen["y"] - top))
        wheel(page, 5)
    return opened, wrapped, misses


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("base")
    parser.add_argument("--rounds", type=int, default=10)
    args = parser.parse_args()
    failed = False
    with sync_playwright() as p:
        browser = p.chromium.launch()
        page = browser.new_page(viewport={"width": 1440, "height": 790})
        errors = []
        page.on("pageerror", lambda error: errors.append(str(error)[:160]))
        for stage in PAPERS:
            opened, wrapped, misses = run(page, args.base.rstrip("/"), stage, args.rounds)
            print(f"{stage}: {opened} of {args.rounds} opened, {wrapped} on wrapped links")
            for miss in misses:
                print("  missed", miss)
            failed = failed or bool(misses)
        reduced = browser.new_page(viewport={"width": 1440, "height": 790}, reduced_motion="reduce")
        reduced.goto(f"{args.base.rstrip('/')}/read/short", wait_until="load")
        reduced.wait_for_selector(".part__text", timeout=60000)
        reduced.wait_for_timeout(2500)
        wheel(reduced, 18)
        spot = reduced.evaluate(SPOT)
        reduced.mouse.click(spot["x"], spot["y"])
        reduced.wait_for_timeout(300)
        seen = reduced.evaluate(SEEN)
        print("reduced motion:", seen["insets"], "card, animation", seen["cue"])
        failed = failed or seen["insets"] != 1 or seen["cue"] != "none"
        if errors:
            print("page errors", errors[:3])
            failed = True
        browser.close()
    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()
