#!/usr/bin/env python3
"""Check a served library paper's shell in a real browser: the columns, Hide pane, the contents
column, the Read menu and Compare.

It checks, each from a fresh browser with empty storage:

 1. no overlap: at 1100, 1440, 2000 and 2560 wide, at the top of the paper and further down, no
    line of the paper (and nothing in its strip) has a box that crosses the pane's left edge, and
    the page does not scroll sideways;
 2. Hide pane, at 1440 and 2000, in light and dark: with words selected, "Hide pane" removes the
    pane, the paper stands whole inside the window with nothing over it and the page does not
    scroll sideways; "Show pane" brings the pane back on the same subject (the band's state and
    its quotation unchanged) and nothing overlaps;
 3. the contents column (from 1680 wide): search first, then the sections, then the topic key;
    no credit or other prose in it; it scrolls on its own; a section with subsections folds and
    unfolds; the section being read is marked as the paper scrolls;
 4. the paper's front matter: the authors on one line, the credit once under them, and no
    "Contents" block in the paper;
 5. the Read menu lists only the documents it should (--menu, the expected titles in order),
    with no "draft";
 6. Compare offers only the levels the paper has (--levels, the expected column names).

With --shots DIR it also saves screenshots of the first load, the contents column scrolled, the
Read menu open, Hide pane on and off, and Compare, at 2000 and 1440 in light and dark.

    python site/scripts/check-reader-shell.py http://127.0.0.1:47311/library/euler/ \\
        --menu "Finite-Time Singularity Formation for the Three-Dimensional Euler Equations" \\
        --levels Lean "Authors’ paper" --shots shots/

It prints `ok ...` for each check that holds and `FAIL ...` for each that does not, and exits 1
if any failed. Controls are clicked with the mouse at the centre of their box, never with
Playwright's own click(), which scrolls the page first.
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

from playwright.sync_api import Browser, Page, sync_playwright

FAILURES: list[str] = []
SHOTS: Path | None = None
NAME = "paper"


def check(ok: bool, what: str, detail: str = "") -> bool:
    if ok:
        print(f"ok   {what}")
    else:
        FAILURES.append(what)
        print(f"FAIL {what}" + (f": {detail}" if detail else ""))
    return ok


def shot(page: Page, what: str) -> None:
    if SHOTS is None:
        return
    SHOTS.mkdir(parents=True, exist_ok=True)
    page.screenshot(path=str(SHOTS / f"{NAME}-{what}.png"))


def open_page(browser: Browser, url: str, width: int, height: int, scheme: str = "light") -> Page:
    context = browser.new_context(viewport={"width": width, "height": height}, color_scheme=scheme, device_scale_factor=1)
    page = context.new_page()
    page.goto(url)
    page.wait_for_selector(".part__text [data-t]", state="attached", timeout=30000)
    page.wait_for_timeout(1800)
    return page


def centre_click(page: Page, selector: str, text: str | None = None) -> bool:
    loc = page.locator(selector, has_text=text) if text else page.locator(selector)
    for i in range(loc.count()):
        box = loc.nth(i).bounding_box()
        if box and box["width"] > 0 and box["height"] > 0 and loc.nth(i).is_visible():
            page.mouse.click(box["x"] + box["width"] / 2, box["y"] + box["height"] / 2)
            return True
    return False


# Every text fragment of the paper's column in the window (and the strip's controls), as boxes,
# against the pane's left edge. A fragment whose box reaches past the edge runs under the pane.
CROSSING = r"""
() => {
  const pane = document.querySelector('.reader__map');
  const paper = document.querySelector('.reader__paper');
  if (!paper) return { error: 'no paper' };
  const edge = pane ? pane.getBoundingClientRect().left : innerWidth;
  const out = [];
  let lines = 0;
  const walker = document.createTreeWalker(paper, NodeFilter.SHOW_TEXT);
  const range = document.createRange();
  for (let node = walker.nextNode(); node; node = walker.nextNode()) {
    if (!node.textContent.trim()) continue;
    const host = node.parentElement;
    if (!host || host.closest('[hidden], .skip-link, .katex-mathml, .visually-hidden')) continue;
    // A formula or the Lean may scroll inside its own box; its box is what must stay clear.
    const box = host.closest('.katex-display, .math-scroll, pre, .table-scroll');
    range.selectNodeContents(node);
    for (const r of box ? [box.getBoundingClientRect()] : range.getClientRects()) {
      if (r.width === 0 || r.bottom < 0 || r.top > innerHeight) continue;
      lines++;
      if (r.right > edge + 0.5) out.push({ text: node.textContent.trim().slice(0, 50), right: Math.round(r.right), edge: Math.round(edge) });
    }
  }
  return { edge: Math.round(edge), lines, crossing: out.slice(0, 5), count: out.length,
           sideways: document.documentElement.scrollWidth - document.documentElement.clientWidth };
}
"""


def no_overlap(browser: Browser, url: str) -> None:
    for width in (1100, 1440, 2000, 2560):
        page = open_page(browser, url, width, 1000)
        for where, y in (("top", 0), ("1500px down", 1500), ("6000px down", 6000)):
            page.evaluate("(y) => window.scrollTo(0, y)", y)
            page.wait_for_timeout(600)
            got = page.evaluate(CROSSING)
            check(got.get("lines", 0) > 0 and got.get("count", 1) == 0, f"1 {width}: no paper line crosses the pane's edge ({where})",
                  f"{got.get('count')} of {got.get('lines')} cross the edge at {got.get('edge')}: {got.get('crossing')}")
            check(got.get("sideways", 1) <= 0, f"1 {width}: the page does not scroll sideways ({where})", f"{got.get('sideways')}px")
        page.context.close()


def subject(page: Page) -> dict:
    return page.evaluate(
        """() => ({ state: document.querySelector('.subject-band')?.dataset.state ?? null,
                   words: document.querySelector('.subject-band')?.textContent?.trim() ?? null,
                   quote: document.querySelector('.map-pane blockquote, .map-pane .inspector__quote, .map-pane [class*=quote]')?.textContent?.trim()?.slice(0, 80) ?? null })"""
    )


TIE_POINT = r"""
() => {
  for (const e of document.querySelectorAll('.part__text [data-t]')) {
    const r = e.getClientRects()[0];
    if (!r || r.width < 24 || r.top < 160 || r.bottom > innerHeight - 120) continue;
    const y = r.top + r.height / 2;
    for (const f of [0.5, 0.35, 0.65]) {
      const x = r.left + r.width * f;
      const hit = document.elementFromPoint(x, y);
      if (hit && (hit === e || e.contains(hit)) && !hit.closest('.katex')) return { x, y };
    }
  }
  return null;
}
"""


def paper_box(page: Page) -> dict:
    return page.evaluate(
        """() => { const p = document.querySelector('.reader__paper .paper') ?? document.querySelector('.reader__paper');
                   const r = p.getBoundingClientRect();
                   const strip = document.querySelector('.reader-strip').getBoundingClientRect();
                   return { left: r.left, right: r.right, width: r.width, strip: strip.right, vw: innerWidth,
                            pane: !!document.querySelector('.reader__map'),
                            sideways: document.documentElement.scrollWidth - document.documentElement.clientWidth }; }"""
    )


def hide_pane(browser: Browser, url: str) -> None:
    for width in (1440, 2000):
        for scheme in ("light", "dark"):
            at = f"{width} {scheme}"
            page = open_page(browser, url, width, 1000, scheme)
            page.evaluate("window.scrollTo(0, 1400)")
            page.wait_for_timeout(700)
            point = page.evaluate(TIE_POINT)
            if not check(point is not None, f"2 {at}: a linked phrase is in view to select"):
                page.context.close()
                continue
            page.mouse.click(point["x"], point["y"])
            page.wait_for_timeout(1000)
            before = subject(page)
            check(before["state"] == "words", f"2 {at}: words are selected", str(before))
            y0 = page.evaluate("scrollY")
            if width == 2000:
                shot(page, f"{scheme}-pane-shown")
            check(centre_click(page, ".reader-strip__map"), f"2 {at}: Hide pane is in the strip")
            page.wait_for_timeout(1000)
            hidden = paper_box(page)
            check(not hidden["pane"], f"2 {at}: Hide pane removes the pane", str(hidden))
            check(hidden["left"] >= 0 and hidden["right"] <= hidden["vw"] and hidden["strip"] <= hidden["vw"], f"2 {at}: the paper stands whole in the window", str(hidden))
            check(hidden["sideways"] <= 0, f"2 {at}: nothing scrolls sideways with the pane hidden", str(hidden))
            covered = page.evaluate(
                """() => { const p = document.querySelector('.reader__paper .paper'); const r = p.getBoundingClientRect();
                           const ys = [200, innerHeight / 2, innerHeight - 80]; const xs = [r.left + 20, (r.left + r.right) / 2, r.right - 20];
                           const bad = []; for (const y of ys) for (const x of xs) { const e = document.elementFromPoint(x, y);
                             if (e && !e.closest('.reader__paper') && !e.closest('.topbar')) bad.push(e.className || e.tagName); }
                           return bad; }"""
            )
            check(not covered, f"2 {at}: nothing stands over the paper with the pane hidden", str(covered))
            label = page.evaluate("document.querySelector('.reader-strip__map')?.textContent?.trim()")
            check(label == "Show pane", f"2 {at}: the control then reads Show pane", str(label))
            if width == 2000:
                shot(page, f"{scheme}-pane-hidden")
            else:
                shot(page, f"{width}-{scheme}-pane-hidden")
            check(centre_click(page, ".reader-strip__map"), f"2 {at}: Show pane is in the strip")
            page.wait_for_timeout(1500)
            after = subject(page)
            shown = paper_box(page)
            check(shown["pane"], f"2 {at}: Show pane brings the pane back", str(shown))
            check(after["state"] == before["state"] and after["quote"] == before["quote"], f"2 {at}: the pane comes back on the same subject", f"{before} -> {after}")
            got = page.evaluate(CROSSING)
            check(got.get("count", 1) == 0 and got.get("sideways", 1) <= 0, f"2 {at}: after Show pane no line crosses the pane", str(got))
            page.context.close()


def contents_column(browser: Browser, url: str) -> None:
    page = open_page(browser, url, 2000, 1000)
    col = page.evaluate(
        """() => { const nav = document.querySelector('.reader__outline .outline'); if (!nav) return null;
                   const kids = [...nav.children].map(e => e.className || e.tagName);
                   const order = ['paper-search', 'outline__list', 'phrase-key'].map(c => kids.findIndex(k => String(k).includes(c)));
                   const prose = [...nav.querySelectorAll('p')].filter(p => !p.closest('details') && !p.closest('.phrase-key__head') && !p.className.includes('phrase-key__head') && !p.className.includes('phrase-key__family-name') && !p.className.includes('paper-search__none')).map(p => p.textContent.trim().slice(0, 60));
                   const s = getComputedStyle(nav);
                   return { kids, order, prose, overflow: s.overflowY, scrolls: nav.scrollHeight > nav.clientHeight,
                            sticky: getComputedStyle(nav.parentElement).position, credit: /Anthropic|repository|reviewed/.test(nav.textContent) }; }"""
    )
    if not check(col is not None, "3 2000: the contents column stands at the left"):
        page.context.close()
        return
    o = col["order"]
    check(all(i >= 0 for i in o) and o == sorted(o), "3 search, then the sections, then the topic key", str(col["kids"]))
    check(not col["credit"] and not col["prose"], "3 no credit and no prose in the column", str(col["prose"]))
    check(col["overflow"] == "auto" and col["sticky"] == "sticky", "3 the column is sticky and scrolls on its own", str(col))
    shot(page, "light-first-load")
    folds = page.locator(".outline__fold")
    if check(folds.count() > 0, "3 sections with subsections have a fold control"):
        closed = page.evaluate("[...document.querySelectorAll('.outline__fold')].findIndex(b => b.getAttribute('aria-expanded') === 'false')")
        if closed >= 0:
            n0 = page.evaluate("document.querySelectorAll('.outline__item').length")
            box = folds.nth(closed).bounding_box()
            page.evaluate("(i) => document.querySelectorAll('.outline__fold')[i].scrollIntoView({block: 'center'})", closed)
            box = folds.nth(closed).bounding_box()
            page.mouse.click(box["x"] + box["width"] / 2, box["y"] + box["height"] / 2)
            page.wait_for_timeout(300)
            n1 = page.evaluate("document.querySelectorAll('.outline__item').length")
            check(n1 > n0, "3 unfolding a section lists its subsections", f"{n0} -> {n1}")
            page.mouse.click(box["x"] + box["width"] / 2, box["y"] + box["height"] / 2)
            page.wait_for_timeout(300)
            check(page.evaluate("document.querySelectorAll('.outline__item').length") == n0, "3 folding it again hides them")
    # The section being read is marked as the paper scrolls.
    first = page.evaluate("document.querySelector('.outline [aria-current=location]')?.textContent ?? null")
    page.evaluate("window.scrollTo(0, document.documentElement.scrollHeight * 0.4)")
    page.wait_for_timeout(1200)
    later = page.evaluate("document.querySelector('.outline [aria-current=location]')?.textContent ?? null")
    check(later is not None and later != first, "3 the current section is marked as the paper scrolls", f"{first} -> {later}")
    page.evaluate("document.querySelector('.reader__outline .outline').scrollTop = 99999")
    page.wait_for_timeout(300)
    shot(page, "light-contents-scrolled")
    page.context.close()


def front_matter(browser: Browser, url: str) -> None:
    page = open_page(browser, url, 1440, 1000)
    got = page.evaluate(
        """() => { const ul = document.querySelector('.paper ul.authors'); const lis = ul ? [...ul.children] : [];
                   const tops = new Set(lis.map(li => Math.round(li.getBoundingClientRect().top)));
                   const credit = [...document.querySelectorAll('.front-credit')];
                   const headings = [...document.querySelectorAll('.paper h1, .paper h2')].map(h => h.textContent.trim());
                   return { authors: lis.length, oneLine: tops.size === 1, text: ul?.innerText ?? null,
                            bullets: !!ul && getComputedStyle(ul).listStyleType !== 'none' && lis.some(li => getComputedStyle(li).display === 'list-item'),
                            credits: credit.length, creditText: credit[0]?.textContent ?? '',
                            accountLine: !!document.querySelector('.account-line'),
                            contents: headings.some(h => /^(table of )?contents$/i.test(h)) }; }"""
    )
    if got["authors"]:
        check(got["oneLine"] and not got["bullets"], "4 the authors stand on one line", str(got))
    check(got["credits"] == 1 and not got["accountLine"], "4 the credit is said once, under the authors", str(got))
    check("AI" in got["creditText"] and "About" in got["creditText"], "4 the credit line names the AI-made links and points to About", got["creditText"][:200])
    check(not got["contents"], "4 the paper has no Contents block", str(got))
    page.context.close()


def read_menu(browser: Browser, url: str, menu: list[str]) -> None:
    for width, scheme in ((2000, "light"), (2000, "dark"), (1440, "light"), (1440, "dark")):
        page = open_page(browser, url, width, 1000, scheme)
        centre_click(page, ".readmenu__button")
        page.wait_for_timeout(400)
        items = page.evaluate("[...document.querySelectorAll('.readmenu__menu [role=menuitem]')].map(a => a.querySelector('.readmenu__name')?.textContent?.trim() ?? a.textContent.trim())")
        names = [i for i in items if i and not i.lower().startswith("all ")]
        text = page.evaluate("document.querySelector('.readmenu__menu')?.textContent ?? ''")
        check(names == menu, f"5 {width} {scheme}: the Read menu lists only {menu}", str(items))
        check("draft" not in text.lower(), f"5 {width} {scheme}: no draft label in the Read menu", text[:200])
        shot(page, f"{scheme}-read-menu" if width == 2000 else f"{width}-{scheme}-read-menu")
        page.keyboard.press("Escape")
        page.mouse.click(4, 400)
        page.wait_for_timeout(300)
        shot(page, f"{scheme}-first-load" if width == 2000 else f"{width}-{scheme}-first-load")
        page.context.close()


def compare(browser: Browser, url: str, levels: list[str]) -> None:
    base = url.rstrip("/")
    for width, scheme in ((2000, "light"), (2000, "dark"), (1440, "light"), (1440, "dark")):
        context = browser.new_context(viewport={"width": width, "height": 1000}, color_scheme=scheme)
        page = context.new_page()
        page.goto(f"{base}/compare/")
        page.wait_for_timeout(5000)
        offered = page.evaluate("[...document.querySelectorAll('.table-line button[aria-pressed], .table-head span, .bench-levels button, [aria-label*=level] button')].map(e => e.textContent.trim())")
        named = sorted(set(o for o in offered if o and not o.startswith('Filter')))
        check(named == sorted(levels), f"6 {width} {scheme}: Compare offers only {levels}", str(offered))
        text = page.evaluate("document.querySelector('main')?.innerText ?? document.body.innerText")
        for absent in ("Long record", "Short paper", "Exposition"):
            if absent not in levels:
                check(absent not in text, f"6 {width} {scheme}: Compare does not mention {absent}", "")
        shot(page, f"{scheme}-compare" if width == 2000 else f"{width}-{scheme}-compare")
        context.close()


def main() -> int:
    global SHOTS, NAME
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("url")
    ap.add_argument("--menu", nargs="+", help="the Read menu's expected titles, in order")
    ap.add_argument("--levels", nargs="+", help="Compare's expected level names")
    ap.add_argument("--shots", type=Path)
    ap.add_argument("--name", default=None, help="prefix for screenshot files (default: the paper's id from the address)")
    ap.add_argument("--only", nargs="+", choices=["overlap", "hide", "contents", "front", "menu", "compare"])
    args = ap.parse_args()
    SHOTS = args.shots
    NAME = args.name or args.url.rstrip("/").rsplit("/", 1)[-1]
    url = args.url if args.url.endswith("/") else args.url + "/"
    run = set(args.only or ["overlap", "hide", "contents", "front", "menu", "compare"])
    with sync_playwright() as p:
        browser = p.chromium.launch()
        if "overlap" in run:
            no_overlap(browser, url)
        if "hide" in run:
            hide_pane(browser, url)
        if "contents" in run:
            contents_column(browser, url)
        if "front" in run:
            front_matter(browser, url)
        if "menu" in run and args.menu:
            read_menu(browser, url, args.menu)
        if "compare" in run and args.levels:
            compare(browser, url, args.levels)
        browser.close()
    print(f"\n{len(FAILURES)} failed" if FAILURES else "\nall checks hold")
    return 1 if FAILURES else 0


if __name__ == "__main__":
    sys.exit(main())
