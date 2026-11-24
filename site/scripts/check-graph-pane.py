#!/usr/bin/env python3
"""Check the reader's graph pane in a real browser against docs/graph-pane.md.

For each paper, at 1440x900 and 2560x1440, the pane is checked while following the paper
(two places), after a phrase is clicked and after a neighbour card is clicked, with the shared
assertions of `graph_pane_checks.py` (`check_graph_pane`, then `check_groups`, which opens the largest group). Then it checks what
the shared module cannot know about this reader: a click on a phrase or a card keeps the view,
Escape returns to following the paper, and the dock under the graph is never empty.

    python site/scripts/check-graph-pane.py http://127.0.0.1:8651/lean-exposition-site/ [--papers short long] [--shots DIR --name sk]

For a focused check of a linked passage's painted graph, pass its reader address with
``--painted-fit``. The Riemann result is a one-sided fixture in the real PDF reader:

    python site/scripts/check-graph-pane.py http://127.0.0.1:47335/riemann-hypothesis-reader/ \
      --painted-fit '?n=rh.result&l=b11474-11623&v=lean&view=pdf&page=4' --one-sided-cap

Serve a static build first (any server that falls back to index.html for unknown paths). It
needs Playwright for Python with Chromium installed. It exits 1 and names each failure.
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path
from urllib.parse import parse_qs, urljoin, urlsplit

from playwright.sync_api import Locator, Page, sync_playwright

sys.path.insert(0, str(Path(__file__).resolve().parent))
from graph_pane_checks import GRAPH_SETTLED, check_graph_pane, check_groups, painted_fit  # noqa: E402

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


def measure_painted(
    graph: Locator, label: str, bad: list[str], *, should_fit: bool = True,
) -> dict:
    graph.wait_for(timeout=15000)
    graph.locator(".fg__lines .fg__wire").first.wait_for(state="attached", timeout=15000)
    settled = graph.evaluate(GRAPH_SETTLED)
    result, shape = painted_fit(graph)
    if not settled:
        bad.append(f"{label}: the painted graph did not settle: {shape}")
    if shape.get("detached"):
        bad.append(f"{label}: wires detached from their card borders: {shape['detached']}")
    if result != should_fit:
        bad.append(f"{label}: fitted={result}, expected {should_fit}, {shape}")
    elif should_fit and shape["scale"] > 1.151:
        bad.append(f"{label}: fitted past the 1.15 scale limit: {shape}")
    else:
        print(f"ok  {label}: {shape}", flush=True)
    if graph.locator(".fg__mini").count():
        bad.append(f"{label}: the reader graph has a miniature overview")
    return shape


def check_painted_fit(page: Page, url: str, one_sided_cap: bool) -> list[str]:
    """Check a real local graph in desktop and landscape viewports and after a manual fit."""
    bad = []
    errors = []
    page.on("pageerror", lambda error: errors.append(str(error)))
    page.goto(url, wait_until="domcontentloaded")
    graph = page.locator(".map-pane__local .fg:visible").last
    initial = measure_painted(graph, "painted fit on cold load at 1440×900", bad)
    if one_sided_cap and (sorted(initial.get("sides", []))[:1] != [0] or sum(initial.get("sides", [])) < 2):
        bad.append(f"painted fit needs at least two neighbours on one side only: {initial}")
    if len(initial.get("subjects", [])) != 1:
        bad.append(f"painted fit needs exactly one subject to check wire attachments: {initial}")
    if not all(initial.get("counts", {}).get(mark) for mark in ("card", "label", "wire", "arrow")):
        bad.append(f"painted fit needs cards, labels, wires and arrowheads: {initial}")
    if one_sided_cap and abs(initial.get("scale", 0) - 1.15) > 0.002:
        bad.append(f"the wide fixture must reach the 1.15 scale limit: {initial}")
    page.set_viewport_size({"width": 1180, "height": 760})
    desktop = measure_painted(graph, "painted fit after resizing the desktop pane to 1180×760", bad)
    if initial.get("view") == desktop.get("view") or initial.get("subjects") != desktop.get("subjects"):
        bad.append(f"desktop resize must change the viewport while keeping the subject: {initial} → {desktop}")
    page.set_viewport_size({"width": 844, "height": 390})
    resized = measure_painted(graph, "painted fit after resizing to 844×390", bad)
    if initial.get("view") == resized.get("view") or initial.get("subjects") != resized.get("subjects"):
        bad.append(f"resize must change the viewport while keeping the subject: {initial} → {resized}")
    canvas = graph.locator(".fg__scroll")
    graph.get_by_role("button", name="Zoom in", exact=True).click()
    for _ in range(3):
        canvas.press("ArrowRight")
    disturbed = measure_painted(graph, "zoom and manual pan move the drawing out of fit", bad, should_fit=False)
    if not disturbed.get("outside"):
        bad.append(f"zoomed graph never overflowed its viewport: {disturbed}")
    graph.get_by_role("button", name="Fit", exact=True).click()
    restored = measure_painted(graph, "manual Fit reframes the painted graph", bad)
    if resized.get("subjects") != restored.get("subjects") or resized.get("sides") != restored.get("sides"):
        bad.append(f"Fit changed the graph's subject or neighbours: {resized} → {restored}")
    page.set_viewport_size({"width": 1440, "height": 900})
    graph.get_by_role("button", name="Minimise graph", exact=True).click()
    page.locator(".map-pane .mode-toggle").get_by_role("button", name="Graph", exact=True).click()
    separate = page.locator('.map-pane[data-view="graph"] .fg:visible').last
    separate.locator(".fg__lines .fg__wire").first.wait_for(state="attached", timeout=15000)
    for _ in range(4):
        separate.get_by_role("button", name="Zoom in", exact=True).click()
    _, zoomed = painted_fit(separate) if separate.evaluate(GRAPH_SETTLED) else (False, {})
    if not zoomed.get("outside"):
        bad.append(f"separate Graph tab never settled into an overflowing view after zooming: {zoomed}")
    if zoomed.get("detached"):
        bad.append(f"separate Graph tab has detached wires after zooming: {zoomed['detached']}")
    if page.locator(".fg__mini").count():
        bad.append("the zoomed separate Graph tab has a miniature overview")
    pane = page.locator('.map-pane[data-view="graph"]:visible').last
    pane.get_by_role("button", name="Whole proof map", exact=True).click()
    pane.locator('.tree[data-mode="overview"] .card').first.wait_for(state="attached", timeout=15000)
    pane.get_by_role("button", name="Neighbours of this step", exact=True).click()
    separate.wait_for(timeout=15000)
    _, reopened = painted_fit(separate)
    if initial.get("subjects") != reopened.get("subjects"):
        bad.append(f"returning from the whole proof map changed the local subject: {initial} → {reopened}")
    else:
        print("ok  the separate Graph tab opens the whole proof map and returns to the same subject", flush=True)
    if errors:
        bad.append(f"painted fit: page errors: {'; '.join(errors[:3])}")
    return bad


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("base", help="the served site's root, e.g. http://127.0.0.1:8651/lean-exposition-site/")
    parser.add_argument("--papers", nargs="+", default=["short", "expository", "long"])
    parser.add_argument("--phrase", type=int, default=6, help="which coloured phrase to click")
    parser.add_argument("--shots", help="save a screenshot of each state into this folder")
    parser.add_argument("--name", default="site", help="file name prefix for --shots")
    parser.add_argument("--painted-fit", metavar="ADDRESS", help="only check painted fit at this linked passage address, relative to base or absolute")
    parser.add_argument("--one-sided-cap", action="store_true", help="also require a one-sided fixture that reaches the 1.15 cap at 1440×900")
    args = parser.parse_args()
    if args.one_sided_cap and not args.painted_fit:
        parser.error("--one-sided-cap requires --painted-fit")
    base = args.base.rstrip("/")
    failures: list[str] = []
    with sync_playwright() as p:
        browser = p.chromium.launch()
        if args.painted_fit:
            url = urljoin(base + "/", args.painted_fit)
            cold = browser.new_page(viewport={"width": 1180, "height": 760})
            try:
                cold.goto(url, wait_until="domcontentloaded")
                graph = cold.locator(".map-pane__local .fg:visible").last
                measure_painted(graph, "painted fit on independent cold load at 1180×760", failures)
            finally:
                cold.close()
            page = browser.new_page(viewport={"width": 1440, "height": 900})
            try:
                failures += check_painted_fit(page, url, args.one_sided_cap)
            finally:
                page.close()
        for width, height in (() if args.painted_fit else SIZES):
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
                    failures += check_groups(page, f"{label}: following, place {step}")
                shot("following")
                # A phrase clicked: the view stays Graph.
                if click_phrase(page, args.phrase):
                    settle(page)
                    if view(page) != "graph":
                        failures.append(f"{label}: a phrase click changed the view to {view(page)}")
                    if "n" not in parse_qs(urlsplit(page.url).query):
                        failures.append(f"{label}: the phrase click opened nothing")
                    failures += check_graph_pane(page, f"{label}: phrase clicked", dock=DOCK)
                    failures += check_groups(page, f"{label}: phrase clicked")
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
                    failures += check_groups(page, f"{label}: card clicked")
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
