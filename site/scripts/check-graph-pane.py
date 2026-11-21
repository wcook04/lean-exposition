#!/usr/bin/env python3
"""Check the reader's graph pane in a real browser against docs/graph-pane.md.

For each paper, at 1440x900 and 2560x1440, the pane is checked while following the paper
(two places), after a phrase is clicked and after a neighbour card is clicked, with the shared
assertions of `graph_pane_checks.py` (`check_graph_pane`, `check_scrolls`). Then it checks what
the shared module cannot know about this reader: a click on a phrase or a card keeps the view,
Escape returns to following the paper, and the dock under the graph is never empty.

    python site/scripts/check-graph-pane.py http://127.0.0.1:8651/lean-exposition-site/ [--papers short long] [--shots DIR --name sk]

Serve a static build first (any server that falls back to index.html for unknown paths). It
needs Playwright for Python with Chromium installed. It exits 1 and names each failure.
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path
from urllib.parse import parse_qs, urlsplit

from playwright.sync_api import Page, sync_playwright

sys.path.insert(0, str(Path(__file__).resolve().parent))
from graph_pane_checks import check_graph_pane, check_scrolls  # noqa: E402

DOCK = ".map-pane__dock"
SIZES = [(1440, 900), (2560, 1440)]


def settle(page: Page, ms: int = 1400) -> None:
    page.wait_for_timeout(ms)


def view(page: Page) -> str:
    return page.evaluate("() => document.querySelector('.map-pane')?.dataset.view ?? ''")


def click_phrase(page: Page, nth: int) -> bool:
    """Click the words of the nth coloured phrase, as a reader would (not a link inside it)."""
    phrase = page.locator(".paper .tie[data-tone]").nth(nth)
    if not phrase.count():
        return False
    phrase.evaluate("e => e.scrollIntoView({block: 'center'})")
    page.wait_for_timeout(300)
    box = phrase.evaluate("e => { const r = e.getClientRects()[0]; return r ? {x: r.left, y: r.top, width: r.width, height: r.height} : null; }")
    if not box:
        return False
    page.mouse.click(box["x"] + 4, box["y"] + box["height"] / 2)
    return True


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("base", help="the served site's root, e.g. http://127.0.0.1:8651/lean-exposition-site/")
    parser.add_argument("--papers", nargs="+", default=["short", "expository", "long"])
    parser.add_argument("--phrase", type=int, default=6, help="which coloured phrase to click")
    parser.add_argument("--shots", help="save a screenshot of each state into this folder")
    parser.add_argument("--name", default="site", help="file name prefix for --shots")
    args = parser.parse_args()
    base = args.base.rstrip("/")
    failures: list[str] = []
    with sync_playwright() as p:
        browser = p.chromium.launch()
        for width, height in SIZES:
            for paper in args.papers:
                page = browser.new_page(viewport={"width": width, "height": height})
                errors: list[str] = []
                page.on("pageerror", lambda error: errors.append(str(error)[:200]))
                label = f"{paper} {width}"

                def shot(state: str) -> None:
                    if args.shots:
                        page.screenshot(path=str(Path(args.shots) / f"{args.name}-{paper}-{state}-{width}.png"))

                page.goto(f"{base}/read/{paper}/?v=graph", wait_until="networkidle")
                settle(page, 2500)
                # Following the paper, two places apart.
                for step in (1, 2):
                    page.mouse.move(width * 0.25, height * 0.5)
                    page.mouse.wheel(0, 1800 * step)
                    settle(page)
                    failures += check_graph_pane(page, f"{label}: following, place {step}", dock=DOCK)
                    failures += check_scrolls(page, f"{label}: following, place {step}")
                shot("following")
                # A phrase clicked: the view stays Graph.
                if click_phrase(page, args.phrase):
                    settle(page)
                    if view(page) != "graph":
                        failures.append(f"{label}: a phrase click changed the view to {view(page)}")
                    if "n" not in parse_qs(urlsplit(page.url).query):
                        failures.append(f"{label}: the phrase click opened nothing")
                    failures += check_graph_pane(page, f"{label}: phrase clicked", dock=DOCK)
                    failures += check_scrolls(page, f"{label}: phrase clicked")
                    shot("phrase")
                # A neighbour card clicked: it becomes the subject, and the view stays Graph.
                card = page.locator('.fg__card[data-band="uses"], .fg__card[data-band="users"]').first
                if card.count():
                    want = card.get_attribute("data-card")
                    card.scroll_into_view_if_needed()
                    card.click()
                    settle(page)
                    subjects = page.evaluate("() => [...document.querySelectorAll('.fg__card[data-band=subject]')].map((c) => c.dataset.card)")
                    if want not in subjects:
                        failures.append(f"{label}: the clicked card {want} is not the subject ({', '.join(subjects)})")
                    if view(page) != "graph":
                        failures.append(f"{label}: a card click changed the view to {view(page)}")
                    failures += check_graph_pane(page, f"{label}: card clicked", dock=DOCK)
                    failures += check_scrolls(page, f"{label}: card clicked")
                    shot("card")
                # Escape follows the paper again and keeps the view.
                page.keyboard.press("Escape")
                settle(page)
                query = parse_qs(urlsplit(page.url).query)
                if "n" in query or "d" in query:
                    failures.append(f"{label}: Escape left {page.url} pinned")
                if view(page) != "graph":
                    failures.append(f"{label}: Escape changed the view to {view(page)}")
                failures += check_graph_pane(page, f"{label}: after Escape", dock=DOCK)
                if errors:
                    failures.append(f"{label}: page errors: {'; '.join(errors[:3])}")
                page.close()
        browser.close()
    for line in failures:
        print("FAIL", line)
    print("graph pane:", "fails" if failures else "passes")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
