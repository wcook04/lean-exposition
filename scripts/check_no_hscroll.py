#!/usr/bin/env python3
"""Fail if anything in a served library paper scrolls sideways.

    python scripts/check_no_hscroll.py http://127.0.0.1:47311/library/euler/ [--widths 390 800 1024 1100 1440 2000 2560] [--dark] [--shots DIR]

For each window width and each of the paper's documents (read/<slot>/), from a cold browser: scroll
the whole paper from top to bottom so every lazily rendered part and formula is laid out and fitted,
then list every element whose computed overflow-x is auto or scroll and whose scrollWidth exceeds
its clientWidth by more than 1px, every visible "Scroll formula" control, and any sideways overflow
of the page itself. With --shots, also screenshot the numbered displays named by --equation (by
default (1.2) and (5.43)) and the widest display formula. Needs Playwright for Python with Chromium.
Exits 1 if anything scrolls sideways.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
import urllib.request
from pathlib import Path

from playwright.sync_api import sync_playwright

# Every element that would show a horizontal scroll bar, and every "Scroll formula" control shown.
SIDEWAYS = """() => {
  const out = [];
  for (const el of document.querySelectorAll('body *')) {
    if (!el.getClientRects().length) continue;
    const x = getComputedStyle(el).overflowX;
    if ((x === 'auto' || x === 'scroll') && el.scrollWidth > el.clientWidth + 1) {
      const name = el.tagName.toLowerCase() + (typeof el.className === 'string' && el.className ? '.' + el.className.trim().split(/\\s+/).join('.') : '');
      out.push(`${name} scrollWidth ${el.scrollWidth} > clientWidth ${el.clientWidth}: ${(el.textContent || '').replace(/\\s+/g, ' ').trim().slice(0, 60)}`);
    }
  }
  for (const cue of document.querySelectorAll('.math-cue__scroll')) if (cue.getClientRects().length) out.push('a "Scroll formula" control is shown');
  // A display that does not scroll must still fit: the rendered formula (.katex-html and each
  // piece of it) and its number lie inside the column's content box, never cut off by the clip.
  for (const box of document.querySelectorAll('.prose .math-display')) {
    if (!box.getClientRects().length) continue;
    const html = box.querySelector(':scope > .katex-display > .katex > .katex-html');
    if (!html) continue;
    const parts = [html, ...html.querySelectorAll(':scope > .katex-base, :scope > .katex-tag, :scope > .tag'), ...box.querySelectorAll(':scope > .math-number')].filter(p => p.getClientRects().length);
    const left = box.getBoundingClientRect().left + box.clientLeft;
    const extent = Math.max(0, ...parts.map(p => p.getBoundingClientRect().right - left));
    if (extent > box.clientWidth + 1) {
      const t = box.closest('[data-t]') || box;
      out.push(`math-display${t.dataset.t ? ' data-t=' + t.dataset.t : ''}${box.dataset.unfitted !== undefined ? ' (not yet fitted, transparent)' : ''} form=${box.dataset.form || '0'} fit=${box.dataset.fit || '-'} reaches ${extent.toFixed(0)} in a ${box.clientWidth}px column: ${(box.querySelector('.math-number, .katex-tag') || {}).textContent || ''} ${box.textContent.replace(/\\s+/g, ' ').slice(0, 50)}`);
    }
  }
  const page = document.documentElement.scrollWidth - document.documentElement.clientWidth;
  if (page > 1) out.push(`the page is ${page}px wider than the window`);
  return out;
}"""

# Scroll every vertically scrolling column that holds the paper (and the window) to its end, a
# screen at a time, so lazily rendered parts and formulas near the screen are fitted.
SCROLL_STEP = """() => {
  const paper = document.querySelector('.paper');
  const boxes = [document.scrollingElement];
  for (let el = paper && paper.parentElement; el; el = el.parentElement) {
    const y = getComputedStyle(el).overflowY;
    if ((y === 'auto' || y === 'scroll') && el.scrollHeight > el.clientHeight + 1) boxes.push(el);
  }
  let moved = false;
  for (const box of boxes) {
    const before = box.scrollTop;
    box.scrollTop = before + Math.max(200, box.clientHeight * 0.9);
    if (box.scrollTop > before + 1) moved = true;
  }
  return moved;
}"""

WIDEST = """(labels) => {
  const boxes = [...document.querySelectorAll('.prose .math-display')];
  const pick = new Map();
  for (const label of labels) {
    const box = boxes.find(b => { const t = b.querySelector(':scope > .math-number, .katex-tag, .tag'); return t && t.textContent.replace(/[\\s\\u200b]/g, '') === `(${label})`; });
    if (box) pick.set(label, box);
  }
  // The widest display as written: the longest TeX once a broken form's own line and column
  // marks are taken away, so the same formula is picked before and after it breaks.
  const plain = (tex) => tex.replace(/\\\\(begin|end)\\{[^}]*\\}|\\\\tag\\{[^}]*\\}|\\\\\\\\(\\{\\})?|&|\\\\q?quad(\\{\\})?|\\s+/g, '');
  let widest = null, most = 0;
  for (const b of boxes) {
    const tex = b.querySelector('.katex-mathml annotation');
    const w = tex ? plain(tex.textContent).length : 0;
    if (w > most) { most = w; widest = b; }
  }
  if (widest) pick.set('widest', widest);
  document.querySelectorAll('[data-shot]').forEach(e => e.removeAttribute('data-shot'));
  for (const [label, box] of pick) box.setAttribute('data-shot', label);
  return [...pick.keys()];
}"""


def documents(base: str) -> list[str]:
    """The paper's document slots, read from the served edition's index."""
    with urllib.request.urlopen(base + "edition/index.json") as response:
        index = json.load(response)
    slots = []
    for slot in sorted(index.get("documents", {})):
        # A slot the paper does not have (an absent long record) has no page of its own.
        try:
            with urllib.request.urlopen(base + f"read/{slot}/") as response:
                if response.status == 200:
                    slots.append(slot)
        except OSError:
            pass
    return slots or ["short"]


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("base")
    ap.add_argument("--widths", type=int, nargs="+", default=[390, 800, 1024, 1100, 1440, 2000, 2560])
    ap.add_argument("--slots", nargs="+", help="document slots to read (default: every slot the edition serves)")
    ap.add_argument("--shots", type=Path)
    ap.add_argument("--dark", action="store_true", help="read in the dark colour scheme")
    ap.add_argument("--equation", action="append", default=[], help="an equation number to screenshot, e.g. 1.2")
    args = ap.parse_args()
    base = args.base.rstrip("/") + "/"
    slots = args.slots or documents(base)
    labels = args.equation or ["1.2", "5.43"]
    failures: list[str] = []
    with sync_playwright() as pw:
        browser = pw.chromium.launch()
        for width in args.widths:
            height = 844 if width < 500 else 900 if width < 2000 else 1440
            for slot in slots:
                context = browser.new_context(viewport={"width": width, "height": height}, is_mobile=width < 500, has_touch=width < 500, color_scheme="dark" if args.dark else "light")
                page = context.new_page()
                page.goto(base + f"read/{slot}/")
                try:
                    page.wait_for_selector(".paper .part__text", state="attached", timeout=60000)
                except Exception as error:
                    failures.append(f"{width} read/{slot}: the paper did not open ({error})")
                    print(f"FAIL {width} read/{slot}: the paper did not open", flush=True)
                    context.close()
                    continue
                page.wait_for_load_state("networkidle")
                page.wait_for_timeout(1000)
                for _ in range(2000):
                    if not page.evaluate(SCROLL_STEP):
                        break
                    page.wait_for_timeout(60)
                page.wait_for_timeout(1500)
                # A display whose part was typeset after the scroll passed it is still waiting to be
                # fitted (transparent until then): bring each into view, as a reader would, so every
                # display is checked as the reader sees it.
                for _ in range(400):
                    left = page.evaluate("""() => { const b = document.querySelector('.prose .math-display[data-unfitted]'); if (!b) return 0; b.scrollIntoView({ block: 'center' }); return document.querySelectorAll('.prose .math-display[data-unfitted]').length; }""")
                    if not left:
                        break
                    page.wait_for_timeout(250)
                found = page.evaluate(SIDEWAYS)
                tag = f"{width} read/{slot}"
                print(f"{'ok  ' if not found else 'FAIL'} {tag}: {len(found)} sideways scroller(s)", flush=True)
                for line in found[:8]:
                    print(f"     {line}")
                failures += [f"{tag}: {line}" for line in found]
                # Expand, where a display offers it: a dialog across the window whose formula
                # fits without scrolling, and Escape closes it.
                expand = page.locator(".math-cue:not([hidden]) .math-cue__expand").first
                if expand.count():
                    expand.scroll_into_view_if_needed()
                    expand.click()
                    page.wait_for_selector("dialog.modal--formula[open]", timeout=5000)
                    inside = page.evaluate("""() => { const d = document.querySelector('dialog.modal--formula[open]'); const m = d.querySelector('.math-display');
                      const sideways = [...d.querySelectorAll('*')].filter(e => ['auto', 'scroll'].includes(getComputedStyle(e).overflowX) && e.scrollWidth > e.clientWidth + 1).length;
                      const parts = [...m.querySelectorAll('.katex-html > .katex-base, .katex-tag, .tag')].map(p => p.getBoundingClientRect().right);
                      return { sideways, out: Math.max(0, ...parts) - m.getBoundingClientRect().right, wide: d.getBoundingClientRect().width / innerWidth }; }""")
                    if args.shots:
                        args.shots.mkdir(parents=True, exist_ok=True)
                        page.screenshot(path=str(args.shots / f"{slot}-expand-{width}.png"))
                    page.keyboard.press("Escape")
                    page.wait_for_timeout(300)
                    closed = page.locator("dialog.modal--formula[open]").count() == 0
                    bad = inside["sideways"] or inside["out"] > 1 or inside["wide"] < 0.9 or not closed
                    print(f"{'FAIL' if bad else 'ok  '} {tag}: Expand {inside}, closed by Escape {closed}", flush=True)
                    if bad:
                        failures.append(f"{tag}: Expand {inside}, closed by Escape {closed}")
                if args.shots:
                    args.shots.mkdir(parents=True, exist_ok=True)
                    for label in page.evaluate(WIDEST, labels):
                        box = page.locator(f'[data-shot="{label}"]')
                        box.scroll_into_view_if_needed()
                        page.wait_for_timeout(300)
                        name = re.sub(r"[^\w.-]", "_", f"{slot}-{label}-{width}{'-dark' if args.dark else ''}.png")
                        # The display with its column around it: the shot shows its fit against the column's edge.
                        column = page.evaluate("""(label) => { const b = document.querySelector(`[data-shot="${label}"]`); const r = b.getBoundingClientRect(); const p = (b.closest('.paper') || b).getBoundingClientRect(); return {x: Math.max(0, p.left - 8), y: Math.max(0, r.top - 60), width: Math.min(innerWidth - Math.max(0, p.left - 8), p.width + 16), height: Math.min(r.height + 120, innerHeight - Math.max(0, r.top - 60))}; }""", label)
                        page.screenshot(path=str(args.shots / name), clip=column)
                context.close()
        browser.close()
    if failures:
        print(f"{len(failures)} sideways scroller(s)", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
