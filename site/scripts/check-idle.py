#!/usr/bin/env python3
"""Check that a reader is completely still while nobody touches it, and that `?l=` opens on its phrase.

For each address, at each window width, with the graph tab open and then the Lean tab, the page
is left alone after it settles and the check counts, over a few idle seconds: DOM mutations, URL
changes (pushState, replaceState and the address itself), layout shifts and scroll events. Each
must be zero (mutations may be allowed a small bound with --max-mutations). A loop between a
layout and its own measurement (a scroll bar that comes and goes, a fit that answers itself)
shows here as a steady stream of mutations at some widths.

Chromium runs with classic scroll bars that take room, as on a desktop, not the overlay bars
of headless mode: without them such a loop cannot happen in the test.

    python site/scripts/check-idle.py http://127.0.0.1:47311/library/euler/ \
        --paths "?l=b629-736" lean/TorusEuler.theorem11 --widths 1440 2000 2560 \
        --at b629-736 --slot short

With --at, the address `?l=<at>` is also opened cold: the address must keep <at>, and the phrases
lit as current must lie inside that slice (checked against the paper's ties, edition/ties/<slot>.json).
It needs Playwright for Python with Chromium installed. It exits 1 and names each failure.
"""
from __future__ import annotations

import argparse
import json
import sys
import urllib.request

from playwright.sync_api import Page, sync_playwright

INIT = r"""
(() => {
  const w = window;
  w.__still = { muts: 0, urls: 0, shifts: 0, scrolls: 0, tops: {} };
  for (const k of ['pushState', 'replaceState']) {
    const o = history[k].bind(history);
    history[k] = function (...a) { w.__still.urls++; return o(...a); };
  }
  addEventListener('scroll', () => { w.__still.scrolls++; }, true);
  try {
    new PerformanceObserver((l) => { for (const e of l.getEntries()) if (!e.hadRecentInput) w.__still.shifts++; })
      .observe({ type: 'layout-shift', buffered: false });
  } catch (e) {}
  const name = (n) => {
    const t = n && n.nodeType === 1 ? n : n && n.parentElement;
    if (!t) return '?';
    const c = typeof t.className === 'string' ? t.className : (t.className && t.className.baseVal) || '';
    return t.tagName.toLowerCase() + (c ? '.' + c.trim().split(/\s+/).slice(0, 2).join('.') : '');
  };
  const start = () => new MutationObserver((ms) => {
    for (const m of ms) {
      w.__still.muts++;
      const k = `${m.type} ${name(m.target)} ${m.attributeName || ''}`;
      w.__still.tops[k] = (w.__still.tops[k] || 0) + 1;
    }
  }).observe(document, { subtree: true, childList: true, attributes: true, characterData: true });
  if (document.documentElement) start(); else addEventListener('DOMContentLoaded', start);
})();
"""

RESET = "() => { window.__still = { muts: 0, urls: 0, shifts: 0, scrolls: 0, tops: {} }; }"


def pane_tab(page: Page, which: str) -> bool:
    """Choose the right pane's Graph or Lean tab, as a reader would. False if the pane has no such tab."""
    tab = page.locator(".map-pane button", has_text=which).first
    if not tab.count() or not tab.is_visible():
        return False
    tab.click()
    return True


def idle(page: Page, ms: int) -> dict:
    page.evaluate(RESET)
    href = page.evaluate("location.href")
    page.wait_for_timeout(ms)
    got = page.evaluate("window.__still")
    if page.evaluate("location.href") != href:
        got["urls"] += 1
    return got


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("base", help="the reader's root, ending in /")
    ap.add_argument("--paths", nargs="+", default=[""], help="addresses under the root to check")
    ap.add_argument("--widths", nargs="+", type=int, default=[1440, 2000, 2560])
    ap.add_argument("--sweep", nargs=3, type=int, metavar=("FROM", "TO", "STEP"), help="every width from FROM to TO in STEP")
    ap.add_argument("--height", type=int, default=1200)
    ap.add_argument("--first", type=int, default=12000, help="ms to let the page render itself fully the first time")
    ap.add_argument("--settle", type=int, default=2500, help="ms after a resize or a tab change")
    ap.add_argument("--idle", type=int, default=3000, help="ms of idle time counted")
    ap.add_argument("--max-mutations", type=int, default=0)
    ap.add_argument("--cpu-slowdown", type=float, default=1, help="slow the page's CPU by this factor, as on a shared runner")
    ap.add_argument("--quiet-within", type=int, default=2000,
                    help="ms after first paint by which a freshly opened page must be completely still (0 skips)")
    ap.add_argument("--at", help="a slice whose ?l= address must open on its own phrase")
    ap.add_argument("--slot", default="short", help="the paper slot of the root address, for --at")
    ap.add_argument("--headed", action="store_true")
    args = ap.parse_args()
    widths = list(range(args.sweep[0], args.sweep[1] + 1, args.sweep[2])) if args.sweep else args.widths
    bad: list[str] = []
    with sync_playwright() as p:
        browser = p.chromium.launch(headless=not args.headed, ignore_default_args=["--hide-scrollbars"])
        for path in args.paths:
            # Quiet soon after first paint: a page that settles only after a long wait churns while it is read.
            if args.quiet_within:
                page = browser.new_page(viewport={"width": widths[0], "height": args.height})
                page.add_init_script(INIT)
                if args.cpu_slowdown > 1:
                    page.context.new_cdp_session(page).send("Emulation.setCPUThrottlingRate", {"rate": args.cpu_slowdown})
                page.goto(args.base + path, wait_until="domcontentloaded")
                page.wait_for_function("() => performance.getEntriesByName('first-contentful-paint').length > 0", timeout=60000)
                fcp = page.evaluate("performance.getEntriesByName('first-contentful-paint')[0].startTime")
                now = page.evaluate("performance.now()")
                page.wait_for_timeout(max(0, fcp + args.quiet_within - now))
                got = idle(page, args.idle)
                label = f"{path or '/'} at {widths[0]}px, {args.quiet_within} ms after first paint"
                # The page itself must be still; an address the reader settles once (its reading place) is
                # checked by the idle windows below, after the page has been left alone longer.
                if got["muts"] > args.max_mutations or got["shifts"] or got["scrolls"]:
                    top = sorted(got["tops"].items(), key=lambda kv: -kv[1])[:3]
                    bad.append(f"{label}: {got['muts']} mutations ({'; '.join(f'{k} x{v}' for k, v in top)}), "
                               f"{got['shifts']} layout shifts, {got['scrolls']} scroll events")
                else:
                    print(f"ok  {label}: still for {args.idle} ms", flush=True)
                page.close()
            page = browser.new_page(viewport={"width": widths[0], "height": args.height})
            page.add_init_script(INIT)
            page.goto(args.base + path, wait_until="domcontentloaded")
            page.wait_for_timeout(args.first)
            for width in widths:
                page.set_viewport_size({"width": width, "height": args.height})
                page.wait_for_timeout(args.settle)
                for tab in ["Graph", "Lean"]:
                    # The right pane shows from 1280px; below that the reader has no tabs to choose.
                    has = pane_tab(page, tab)
                    if not has and tab == "Lean":
                        break
                    if has:
                        page.wait_for_timeout(args.settle)
                    got = idle(page, args.idle)
                    label = f"{path or '/'} at {width}px, {tab if has else 'no pane'}"
                    problems = []
                    if got["muts"] > args.max_mutations:
                        top = sorted(got["tops"].items(), key=lambda kv: -kv[1])[:3]
                        problems.append(f"{got['muts']} mutations ({'; '.join(f'{k} x{v}' for k, v in top)})")
                    if got["urls"]:
                        problems.append(f"{got['urls']} address changes")
                    if got["shifts"]:
                        problems.append(f"{got['shifts']} layout shifts")
                    if got["scrolls"]:
                        problems.append(f"{got['scrolls']} scroll events")
                    if problems:
                        bad.append(f"{label}: " + ", ".join(problems))
                    else:
                        print(f"ok  {label}: still for {args.idle} ms", flush=True)
            page.close()
        if args.at:
            page = browser.new_page(viewport={"width": widths[0], "height": args.height})
            page.goto(f"{args.base}?l={args.at}", wait_until="domcontentloaded")
            page.wait_for_timeout(args.first)
            search = page.evaluate("location.search")
            if f"l={args.at}" not in search:
                bad.append(f"?l={args.at} became {search}")
            with urllib.request.urlopen(f"{args.base}edition/ties/{args.slot}.json") as r:
                segments = json.load(r)["segments"]
            start, end = (int(x) for x in args.at[1:].split("-"))
            lit = page.evaluate("[...document.querySelectorAll('.paper [data-on]')].map((e) => Number(e.dataset.t)).filter((t) => !Number.isNaN(t))")
            if not lit:
                bad.append(f"?l={args.at}: no phrase is lit")
            outside = [t for t in lit if not (segments[t][0] < end and segments[t][1] > start)]
            if outside:
                bad.append(f"?l={args.at}: lit phrases outside the slice: segments {outside[:5]}")
            if lit and not outside and f"l={args.at}" in search:
                print(f"ok  ?l={args.at} opens on its phrase ({len(lit)} spans) and keeps its address")
            page.close()
        browser.close()
    for line in bad:
        print(f"FAIL {line}")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
