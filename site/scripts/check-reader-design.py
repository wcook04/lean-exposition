#!/usr/bin/env python3
"""Check a served library paper's reader against docs/reader-design.md, in a real browser.

It checks, each from a fresh browser with empty storage:

 1. first visit: the pane has no separate view tabs, the address has no `v=`, and the hint
    (`.reader-hint`) is visible and whole, at 1440x900 and at 390x844;
 2. a click on linked words selects them (`.subject-band[data-state="words"]`, `data-pin`, a 2px
    underline) and does not scroll the paper;
 3. linked Lean and its local graph fit together by default. Minimise graph restores the tabs,
    and Graph, Lean and Combine views retain the scroll, subject and history;
 4. Auto, and Escape, release the selection in place: no scroll, no history entry;
 5. "Return to selected words" brings the selection back into view and keeps it;
 6. a click on plain, unlinked words changes neither the state nor the address;
 7. a paragraph's margin control selects the paragraph, lists its linked passages, and choosing
    one selects those words; Enter on the control does the same as a click;
 8. at 1100x900 the paper and the pane stand side by side, nothing fixed over the paper;
 9. on a 390x844 touch phone: a tap opens the whole-screen sheet, "Back to paper" restores the
    place and leaves the held bar, scrolling never reopens the sheet, the bar's View reopens it
    and its Auto ends the selection;
10. in the Graph view Fit changes only the drawing: the band's words stay, an opened member
    list stays open, and the band does not move;
11. under `prefers-reduced-motion: reduce` the selected marks have no transition and the sheet
    and member list no running animation;
12. the band's Auto | Manual switch: a first visit is Auto, a deep link is Manual, a click on words
    turns it to Manual, scrolling in Manual leaves the pane, Auto follows again without moving the
    paper and the pane then changes as the paper scrolls, Manual while following keeps what the
    pane shows, Escape is Auto, and the mode survives Graph and back to Lean.

Controls in the sticky pane are clicked with the mouse at the centre of their box, never with
Playwright's own `click()`, which scrolls the page first and would falsify every scroll check.

    /Users/willcook/src/ai_workflow/.venv/bin/python site/scripts/check-reader-design.py \
        http://127.0.0.1:47342/library/euler/

It needs Playwright for Python with Chromium installed. It prints `ok ...` for each check that
holds and `FAIL ...` for each that does not, and exits 1 if any failed.
"""
from __future__ import annotations

import argparse
import json
import sys
import urllib.request

from playwright.sync_api import Browser, Page, sync_playwright

from graph_pane_checks import paired_geometry

FAILURES: list[str] = []


def check(ok: bool, what: str, detail: str = "") -> bool:
    if ok:
        print(f"ok   {what}")
    else:
        FAILURES.append(what)
        print(f"FAIL {what}" + (f": {detail}" if detail else ""))
    return ok


# ------------------------------------------------------------------------------------ helpers


def open_page(browser: Browser, base: str, width: int, height: int, touch: bool = False, reduced: bool = False) -> Page:
    context = browser.new_context(
        viewport={"width": width, "height": height},
        has_touch=touch,
        is_mobile=touch,
        device_scale_factor=1,
    )
    page = context.new_page()
    if reduced:
        page.emulate_media(reduced_motion="reduce")
    page.goto(base)
    page.wait_for_selector(".part__text [data-t]", timeout=30000)
    page.wait_for_timeout(1500)
    return page


def state(page: Page) -> str | None:
    return page.evaluate("document.querySelector('.subject-band')?.dataset.state ?? null")


def band_words(page: Page) -> str | None:
    return page.evaluate("document.querySelector('.subject-band__words')?.textContent ?? null")


def scroll_y(page: Page) -> float:
    return page.evaluate("scrollY")


def history_length(page: Page) -> int:
    return page.evaluate("history.length")


def centre_click(page: Page, selector: str, text: str | None = None) -> bool:
    """Click the first visible match at the centre of its box with the mouse. False if none."""
    loc = page.locator(selector, has_text=text) if text else page.locator(selector)
    for i in range(loc.count()):
        box = loc.nth(i).bounding_box()
        if box and box["width"] > 0 and box["height"] > 0 and loc.nth(i).is_visible():
            page.mouse.click(box["x"] + box["width"] / 2, box["y"] + box["height"] / 2)
            return True
    return False


def pane_tab(page: Page, which: str) -> bool:
    return centre_click(page, ".map-pane .mode-toggle button", which)


def minimise_graph(page: Page) -> bool:
    return centre_click(page, ".map-pane__local-head button", "Minimise graph")


# A point on the first line fragment of a linked phrase in the paper, inside the viewport and not
# under anything else: the element at that point must be the phrase or inside it.
TIE_POINT = r"""
(minTop) => {
  const vh = innerHeight;
  for (const e of document.querySelectorAll('.part__text [data-t]')) {
    const r = e.getClientRects()[0];
    if (!r || r.width < 24 || r.top < minTop || r.bottom > vh - 120) continue;
    // The centre of the fragment's own rectangle, on its words and not on a formula, so a touch
    // tap is not moved by the browser's touch adjustment towards some other target.
    const y = r.top + r.height / 2;
    for (const f of [0.5, 0.35, 0.65, 0.2, 0.8]) {
      const x = r.left + r.width * f;
      const hit = document.elementFromPoint(x, y);
      if (hit && (hit === e || e.contains(hit)) && !hit.closest('.katex')) return { x, y, t: e.dataset.t };
    }
  }
  return null;
}
"""


def click_tie(page: Page, min_top: int = 150, tap: bool = False) -> dict | None:
    point = page.evaluate(TIE_POINT, min_top)
    for _ in range(8):
        if point is not None:
            break
        scroll_by(page, 300)
        point = page.evaluate(TIE_POINT, min_top)
    if point is None:
        return None
    point["scroll_before"] = scroll_y(page)
    if tap:
        page.touchscreen.tap(point["x"], point["y"])
    else:
        page.mouse.click(point["x"], point["y"])
    page.wait_for_timeout(800)
    return point


def scroll_by(page: Page, dy: int) -> None:
    page.evaluate("(dy) => window.scrollBy(0, dy)", dy)
    page.wait_for_timeout(700)


def pins(page: Page) -> int:
    return page.evaluate("document.querySelectorAll('.part__text [data-t][data-pin]').length")


# ------------------------------------------------------------------------------------ checks


def first_visit(browser: Browser, base: str) -> None:
    for width, height in ((1440, 900), (390, 844)):
        page = open_page(browser, base, width, height, touch=width < 768)
        at = f"{width}x{height}"
        if width >= 768:
            tabs = page.locator(".map-pane .mode-toggle button").count()
            check(tabs == 0, f"1 first visit {at}: there are no separate view tabs", f"{tabs} tabs")
        check("v=" not in page.url, f"1 first visit {at}: the address has no v=", page.url)
        hint = page.evaluate(
            """() => { const e = document.querySelector('.reader-hint'); if (!e) return null;
                 const r = e.getBoundingClientRect(); const s = getComputedStyle(e);
                 return { visible: r.width > 0 && r.height > 0 && s.visibility !== 'hidden' && s.display !== 'none',
                          sw: e.scrollWidth, cw: e.clientWidth, text: e.textContent }; }"""
        )
        check(hint is not None and hint["visible"], f"1 first visit {at}: the hint is visible", str(hint))
        if hint:
            check(hint["sw"] <= hint["cw"], f"1 first visit {at}: the hint's whole text fits", f"scrollWidth {hint['sw']} > clientWidth {hint['cw']}")
        if width < 768:
            # docs/reader-design.md, "A phone": nothing scrolls sideways but a formula or the Lean in its own box.
            wide = page.evaluate("[document.documentElement.scrollWidth, document.documentElement.clientWidth]")
            check(wide[0] <= wide[1], f"1 first visit {at}: the page does not scroll sideways", f"document scrollWidth {wide[0]} > clientWidth {wide[1]}")
        page.context.close()


def select_and_views(browser: Browser, base: str) -> None:
    page = open_page(browser, base, 1440, 900)
    scroll_by(page, 1200)
    y0 = scroll_y(page)
    point = click_tie(page)
    if not check(point is not None, "2 a linked phrase is in view to click"):
        page.context.close()
        return
    check(state(page) == "words", "2 a click on linked words selects them", f"state {state(page)}")
    check(pins(page) > 0, "2 the selected marks carry data-pin", f"{pins(page)} pinned")
    sizes = page.evaluate("[...document.querySelectorAll('.part__text [data-t][data-pin]')].map(e => getComputedStyle(e).backgroundSize)")
    heights = [s.split()[-1] if s else "" for s in sizes]
    check(bool(heights) and all(h == "2px" for h in heights), "2 the selected line is 2px", f"background-size {sizes[:3]}")
    check(abs(scroll_y(page) - y0) <= 1, "2 the click does not scroll the paper", f"scrollY {y0} -> {scroll_y(page)}")

    # 3: Open the two old tabs from the combined view, then return to the combined view.
    y1, h1 = scroll_y(page), history_length(page)
    title = page.evaluate("document.querySelector('.lean-page__title')?.textContent ?? null")
    fit, geometry = paired_geometry(page)
    check(fit, "3 Lean and its dependency graph fit together", str(geometry))
    check(minimise_graph(page), "3 Minimise graph is available in the default view")
    page.wait_for_timeout(500)
    check(page.locator(".map-pane .mode-toggle button").count() == 2
          and not page.locator(".map-pane__local").count(), "3 minimising restores the two separate views")
    ok = pane_tab(page, "Graph")
    page.wait_for_timeout(1500)
    ok = pane_tab(page, "Lean") and ok
    page.wait_for_timeout(1200)
    check(ok, "3 the Graph and Lean tabs are there to press")
    check(abs(scroll_y(page) - y1) <= 1, "3 Graph and back to Lean do not scroll the paper", f"scrollY {y1} -> {scroll_y(page)}")
    after = page.evaluate("document.querySelector('.lean-page__title')?.textContent ?? null")
    check(title is not None and after == title, "3 Graph and back to Lean keep the subject", f"{title!r} -> {after!r}")
    check(state(page) == "words", "3 Graph and back to Lean keep the selection", f"state {state(page)}")
    check(history_length(page) == h1, "3 Graph and back to Lean add no history entry", f"history {h1} -> {history_length(page)}")
    check(centre_click(page, ".map-pane__bar button", "Combine views"), "3 Combine views is available in the separate views")
    page.wait_for_timeout(1200)
    fit, geometry = paired_geometry(page)
    check(fit and "v=" not in page.url, "3 combining restores the automatic pair", str(geometry))
    check(scroll_y(page) == y1 and history_length(page) == h1 and state(page) == "words"
          and page.locator(".lean-page__title").first.text_content() == title,
          "3 combining keeps the selection, subject, scroll and history")

    # 5: Return to selected words.
    scroll_by(page, 1500)
    centre_click(page, ".subject-band__act")
    page.wait_for_timeout(2000)
    inside = page.evaluate(
        """() => [...document.querySelectorAll('.part__text [data-t][data-pin]')].some(e => [...e.getClientRects()].some(r => r.bottom > 0 && r.top < innerHeight && r.width > 0))"""
    )
    check(inside, "5 Return to selected words brings a selected mark into view")
    check(state(page) == "words", "5 Return to selected words keeps the selection", f"state {state(page)}")

    # 4: Auto, then Escape.
    for how in ("Auto", "Escape"):
        if state(page) != "words":
            click_tie(page)
        if not check(state(page) == "words", f"4 words are selected before {how}", f"state {state(page)}"):
            continue
        scroll_by(page, 1500)
        y2, h2 = scroll_y(page), history_length(page)
        if how == "Escape":
            page.keyboard.press("Escape")
        else:
            centre_click(page, AUTO)
        page.wait_for_timeout(1000)
        check(abs(scroll_y(page) - y2) <= 1, f"4 {how} does not move the paper", f"scrollY {y2} -> {scroll_y(page)}")
        check(state(page) == "following", f"4 {how} follows the paper again", f"state {state(page)}")
        check(page.evaluate("document.querySelectorAll('[data-pin]').length") == 0, f"4 {how} leaves no mark pinned")
        check(history_length(page) == h2, f"4 {how} adds no history entry", f"history {h2} -> {history_length(page)}")
    page.context.close()


PLAIN_POINT = r"""
() => {
  for (const p of document.querySelectorAll('.part__text p')) {
    const walker = document.createTreeWalker(p, NodeFilter.SHOW_TEXT);
    for (let n = walker.nextNode(); n; n = walker.nextNode()) {
      const parent = n.parentElement;
      if (!parent || parent.closest('[data-t], a, .katex, button')) continue;
      const text = n.textContent;
      for (let i = 0; i + 3 < text.length; i++) {
        if (!/\w\w\w/.test(text.slice(i, i + 3))) continue;
        const range = document.createRange();
        range.setStart(n, i + 1);
        range.setEnd(n, i + 2);
        const r = range.getClientRects()[0];
        if (!r || r.top < 150 || r.bottom > innerHeight - 120 || r.width <= 0) continue;
        const x = r.left + r.width / 2, y = r.top + r.height / 2;
        const hit = document.elementFromPoint(x, y);
        if (hit && hit === parent && !hit.closest('[data-t], a')) return { x, y };
      }
    }
  }
  return null;
}
"""


AUTO = ".map-pane .subject-band .mode-switch__side:first-child"
MANUAL = ".map-pane .subject-band .mode-switch__side:last-child"


def mode(page: Page) -> str | None:
    """Which side of the band's Auto | Manual switch is pressed."""
    return page.evaluate(
        "(() => { const on = document.querySelector('.map-pane .subject-band .mode-switch__side[aria-pressed=\"true\"]'); return on ? on.textContent.trim() : null; })()"
    )


def settle_band(page: Page) -> None:
    """Wait for the subject band's switch, which comes with the pane, however slow the machine."""
    try:
        page.wait_for_selector(".map-pane .subject-band .mode-switch", timeout=60000)
        page.wait_for_timeout(800)
    except Exception:
        pass


def settle_title(page: Page) -> None:
    """Wait for the selection's column to arrive in the pane."""
    try:
        page.wait_for_selector(".map-pane .lean-page__title", timeout=30000)
        page.wait_for_timeout(500)
    except Exception:
        pass


def pane_subject(page: Page) -> str | None:
    return page.evaluate("document.querySelector('.map-pane .lean-page__title')?.textContent ?? null")


def scroll_until_new(page: Page, before: str | None, steps: int = 8) -> str | None:
    """Scroll on until the pane shows another subject, or give up; returns what it shows."""
    now = pane_subject(page)
    for _ in range(steps):
        scroll_by(page, 700)
        page.wait_for_timeout(900)
        now = pane_subject(page)
        if now and now != before:
            break
    return now


def auto_manual(browser: Browser, base: str) -> None:
    """12: the Auto | Manual switch, rule by rule (docs/reader-design.md, States)."""
    page = open_page(browser, base, 1440, 900)
    settle_band(page)
    check(mode(page) == "Auto", "12 a first visit is Auto", f"mode {mode(page)}")
    scroll_by(page, 1200)
    page.wait_for_timeout(1000)
    # Clicking linked words selects them and turns the switch to Manual.
    if check(click_tie(page) is not None, "12 a linked phrase is in view to click"):
        check(mode(page) == "Manual", "12 a click on words turns the switch to Manual", f"mode {mode(page)}")
        # In Manual scrolling never changes the pane (once its column has arrived).
        settle_title(page)
        held = pane_subject(page)
        for _ in range(4):
            scroll_by(page, 700)
            page.wait_for_timeout(700)
        check(pane_subject(page) == held and mode(page) == "Manual", "12 scrolling in Manual leaves the pane as it was", f"{held!r} -> {pane_subject(page)!r}")
        # Auto lets go where the reader is, without moving the paper, and the pane then follows.
        y = scroll_y(page)
        centre_click(page, AUTO)
        page.wait_for_timeout(900)
        check(mode(page) == "Auto" and state(page) == "following", "12 Auto follows the paper again", f"mode {mode(page)}, state {state(page)}")
        check(abs(scroll_y(page) - y) <= 1, "12 Auto does not move the paper", f"scrollY {y} -> {scroll_y(page)}")
        before = pane_subject(page)
        after = scroll_until_new(page, before)
        check(mode(page) == "Auto" and after is not None and after != before, "12 after Auto, scrolling changes the pane", f"{before!r} -> {after!r}")
        # Manual, pressed while following, keeps what the pane shows.
        shown = pane_subject(page)
        if centre_click(page, MANUAL):
            page.wait_for_timeout(900)
            check(mode(page) == "Manual" and state(page) == "words", "12 Manual pins what the pane shows", f"mode {mode(page)}, state {state(page)}")
            check(pane_subject(page) == shown, "12 Manual keeps the same subject", f"{shown!r} -> {pane_subject(page)!r}")
            for _ in range(3):
                scroll_by(page, 700)
                page.wait_for_timeout(700)
            check(pane_subject(page) == shown, "12 after Manual, scrolling leaves the pane as it was", f"{shown!r} -> {pane_subject(page)!r}")
            # Escape is Auto.
            page.keyboard.press("Escape")
            page.wait_for_timeout(800)
            check(mode(page) == "Auto", "12 Escape turns the switch to Auto", f"mode {mode(page)}")
        else:
            check(False, "12 Manual is there to press while following")
        # The mode survives switching between Lean and Graph.
        check(click_tie(page) is not None, "12 a second linked phrase is in view to click")
        check(minimise_graph(page), "12 Minimise graph opens the separate views")
        page.wait_for_timeout(500)
        check(pane_tab(page, "Graph"), "12 the Graph tab can be selected")
        page.wait_for_timeout(1200)
        check(pane_tab(page, "Lean"), "12 the Lean tab can be selected")
        page.wait_for_timeout(900)
        check(mode(page) == "Manual", "12 Manual survives Graph and back to Lean", f"mode {mode(page)}")
    page.context.close()
    # A deep link to a numbered result opens in Manual.
    page = open_page(browser, base + "theorem-1.1/", 1440, 900)
    settle_band(page)
    check(mode(page) == "Manual", "12 a deep link opens in Manual", f"mode {mode(page)}, state {state(page)}")
    page.context.close()


def plain_words(browser: Browser, base: str) -> None:
    page = open_page(browser, base, 1440, 900)
    scroll_by(page, 900)
    # Following writes the reading place into the address once the paper rests; let it settle first.
    page.wait_for_timeout(1500)
    point = page.evaluate(PLAIN_POINT)
    if not check(point is not None, "6 plain words are in view to click"):
        page.context.close()
        return
    before, url = state(page), page.url
    page.mouse.click(point["x"], point["y"])
    page.wait_for_timeout(800)
    check(state(page) == before, "6 a click on plain words leaves the state", f"{before} -> {state(page)}")
    check(page.url == url, "6 a click on plain words leaves the address", f"{url} -> {page.url}")
    page.context.close()


PICK = r"""
(focus) => {
  for (const pk of document.querySelectorAll('.para-pick')) {
    const r = pk.getBoundingClientRect();
    if (r.width <= 0 || r.top < 150 || r.bottom > innerHeight - 150) continue;
    if (!(pk.getAttribute('aria-label') || '').includes('Select this paragraph')) continue;
    const y = r.top + r.height / 2;
    const ps = [...pk.closest('.part').querySelectorAll('.part__text p')];
    const near = ps.map((p) => [p, p.getBoundingClientRect()]).sort((a, b) => Math.abs(a[1].top - r.top) - Math.abs(b[1].top - r.top))[0];
    if (!near) continue;
    const ts = new Set([...near[0].querySelectorAll('[data-t]')].map((e) => e.dataset.t));
    if (!ts.size) continue;
    if (focus) pk.focus({ preventScroll: true });
    return { x: r.left + r.width / 2, y, marks: [...ts].map(Number), label: pk.getAttribute('aria-label') };
  }
  return null;
}
"""


def paragraph_pick(browser: Browser, base: str) -> None:
    for how in ("click", "Enter"):
        page = open_page(browser, base, 1440, 900)
        scroll_by(page, 1200)
        page.wait_for_timeout(1000)
        pick = page.evaluate(PICK, how == "Enter")
        if not check(pick is not None, f"7 ({how}) a paragraph's margin control is in view"):
            page.context.close()
            continue
        if how == "click":
            page.mouse.click(pick["x"], pick["y"])
        else:
            focused = page.evaluate("document.activeElement?.classList.contains('para-pick') ?? false")
            check(focused, "7 (Enter) the margin control takes focus")
            page.keyboard.press("Enter")
        page.wait_for_timeout(900)
        check(state(page) == "paragraph", f"7 ({how}) the margin control selects the paragraph", f"state {state(page)}")
        rows = page.evaluate("document.querySelectorAll('.para-links__list button').length")
        # One link's words can stand in several marks (a formula between them), so links are counted
        # from the paper's own index: each mark's first link (edition/ties/<slot>.json).
        with urllib.request.urlopen(f"{base}edition/ties/short.json") as r:
            segments = json.load(r)["segments"]
        linked = len({segments[t][2][0] for t in pick["marks"]})
        check(rows == linked, f"7 ({how}) the list has one row per linked passage", f"{rows} rows for {linked} linked passages")
        if rows:
            centre_click(page, ".para-links__list button")
            page.wait_for_timeout(900)
            check(state(page) == "words", f"7 ({how}) choosing the first row selects its words", f"state {state(page)}")
        page.context.close()


def side_by_side(browser: Browser, base: str) -> None:
    page = open_page(browser, base, 1100, 900)
    got = page.evaluate(
        """() => { const m = document.querySelector('.reader__map'), p = document.querySelector('.reader__paper') || document.querySelector('.part__text');
          const mr = m && m.getBoundingClientRect(), pr = p && p.getBoundingClientRect();
          const fixedOver = [...document.querySelectorAll('body *')].filter((e) => { const s = getComputedStyle(e); if (s.position !== 'fixed' || s.display === 'none' || s.visibility === 'hidden') return false;
              const r = e.getBoundingClientRect(); return r.width > 0 && r.height > 0 && pr && r.left < pr.right && r.right > pr.left && r.top < innerHeight && r.bottom > 0; }).map((e) => e.className);
          return { map: !!m && mr.width > 0 && mr.height > 0 && getComputedStyle(m).visibility !== 'hidden', mapLeft: mr && mr.left, paperRight: pr && pr.right, fixedOver, sheet: !!document.querySelector('.right-sheet') }; }"""
    )
    check(got["map"], "8 at 1100 the pane is visible")
    check(got["mapLeft"] is not None and got["paperRight"] is not None and got["mapLeft"] >= got["paperRight"], "8 at 1100 the pane stands right of the paper", f"pane left {got['mapLeft']}, paper right {got['paperRight']}")
    check(not got["sheet"], "8 at 1100 there is no sheet")
    check(not got["fixedOver"], "8 at 1100 nothing fixed covers the paper", str(got["fixedOver"]))
    page.context.close()


def phone(browser: Browser, base: str) -> None:
    page = open_page(browser, base, 390, 844, touch=True)
    scroll_by(page, 1200)
    point = click_tie(page, min_top=120, tap=True)
    if not check(point is not None, "9 a linked phrase is in view to tap"):
        page.context.close()
        return
    y0 = point["scroll_before"]
    # The place is where the selected words stand in the window: the strip above the paper may take
    # a second row for the selection's controls, and the page's anchoring then scrolls to hold them.
    mark_top = "(() => { const m = document.querySelector('.part__text [data-pin]'); return m ? m.getClientRects()[0].top : null; })()"
    at0 = page.evaluate(mark_top)
    sheet = page.evaluate(
        """() => { const s = document.querySelector('.right-sheet'); if (!s) return null; const r = s.getBoundingClientRect();
          const bar = document.querySelector('.topbar'); const top = Math.max(0, bar ? bar.getBoundingClientRect().bottom : 0);
          return { left: r.left, right: r.right, top: r.top, bottom: r.bottom, barBottom: top, w: document.documentElement.clientWidth, h: innerHeight }; }"""
    )
    if check(sheet is not None, "9 a tap on linked words opens the sheet"):
        covers = sheet["left"] <= 0.5 and sheet["right"] >= sheet["w"] - 0.5 and sheet["bottom"] >= sheet["h"] - 0.5 and sheet["top"] <= sheet["barBottom"] + 1
        check(covers, "9 the sheet covers the screen below the top bar", str(sheet))
    if not centre_click(page, ".right-sheet__back"):
        check(False, "9 the sheet has Back to paper")
        page.context.close()
        return
    page.wait_for_timeout(900)
    check(page.locator(".right-sheet").count() == 0, "9 Back to paper closes the sheet")
    at1 = page.evaluate(mark_top)
    check(at0 is not None and at1 is not None and abs(at1 - at0) <= 2, "9 Back to paper keeps the place", f"selected words at {at0} -> {at1} (scrollY {y0} -> {scroll_y(page)})")
    check(page.locator(".held-bar").count() > 0 and page.locator(".held-bar").first.is_visible(), "9 the held bar shows after Back to paper")
    scroll_by(page, 600)
    page.wait_for_timeout(600)
    check(page.locator(".right-sheet").count() == 0, "9 scrolling never reopens the sheet")
    if centre_click(page, ".held-bar__view"):
        page.wait_for_timeout(900)
        check(page.locator(".right-sheet").count() > 0, "9 the held bar's View reopens the sheet")
        centre_click(page, ".right-sheet__back")
        page.wait_for_timeout(900)
    else:
        check(False, "9 the held bar has View")
    if centre_click(page, ".held-bar__mode .mode-switch__side:first-child"):
        page.wait_for_timeout(900)
        check(page.locator(".held-bar").count() == 0, "9 the held bar's Auto removes the bar")
        check(page.evaluate("document.querySelectorAll('[data-pin]').length") == 0, "9 the held bar's Auto ends the selection")
    else:
        check(False, "9 the held bar has Auto")
    page.context.close()


def band_box(page: Page) -> dict | None:
    return page.evaluate("(() => { const r = document.querySelector('.subject-band')?.getBoundingClientRect(); return r ? { x: r.x, y: r.y, w: r.width, h: r.height } : null; })()")


def graph_fit(browser: Browser, base: str) -> None:
    page = open_page(browser, base, 1440, 900)
    scroll_by(page, 1200)
    click_tie(page)
    if not check(state(page) == "words", "10 words are selected before the graph", f"state {state(page)}"):
        page.context.close()
        return
    check(page.locator(".map-pane__local").is_visible(), "10 the selected Lean has a local graph")
    text = page.evaluate("document.querySelector('.subject-band')?.textContent")
    if not check(centre_click(page, ".map-pane__local button", "Fit"), "10 the local graph has Fit"):
        page.context.close()
        return
    page.wait_for_timeout(800)
    check(page.evaluate("document.querySelector('.subject-band')?.textContent") == text, "10 Fit leaves the subject band's words")
    if page.locator('[data-opens="list"]').count():
        before = band_box(page)
        centre_click(page, '[data-opens="list"]')
        page.wait_for_timeout(900)
        check(page.locator(".fg__list").count() > 0 and page.locator(".fg__list").first.is_visible(), "10 a large group opens as a list")
        after = band_box(page)
        moved = before and after and all(abs(before[k] - after[k]) <= 1 for k in ("x", "y", "w", "h"))
        check(bool(moved), "10 opening the list does not move the subject band", f"{before} -> {after}")
        centre_click(page, ".map-pane button", "Fit")
        page.wait_for_timeout(800)
        check(page.locator(".fg__list").count() > 0, "10 Fit leaves the member list open")
    else:
        print("ok   10 (no group opens as a list here; list checks skipped)")
    page.context.close()


NO_MOTION = "(s) => [...document.querySelectorAll(s)].every(e => e.getAnimations().length === 0)"


def reduced_motion(browser: Browser, base: str) -> None:
    page = open_page(browser, base, 1440, 900, reduced=True)
    scroll_by(page, 1200)
    click_tie(page)
    durations = page.evaluate("[...document.querySelectorAll('.part__text [data-t][data-pin]')].map(e => getComputedStyle(e).transitionDuration)")
    # The site sets every transition to 1ms under reduced motion (styles/base.css), so that code
    # waiting on a transition's end still hears it: nothing longer than that may remain.
    seconds = lambda part: float(part.strip()[:-2]) / 1000 if part.strip().endswith("ms") else float(part.strip()[:-1])
    still = bool(durations) and all(all(seconds(part) <= 0.001 for part in d.split(",")) for d in durations)
    check(still, "11 reduced motion: a selected mark's transition is at most 1ms", f"transition-duration {sorted(set(durations))}")
    check(page.locator(".map-pane__local").is_visible(), "11 reduced motion: the local graph is visible")
    if page.locator('[data-opens="list"]').count():
        centre_click(page, '[data-opens="list"]')
        page.wait_for_timeout(50)
        check(page.evaluate(NO_MOTION, ".fg__list, .fg__list *"), "11 reduced motion: the member list does not animate")
    page.context.close()

    page = open_page(browser, base, 390, 844, touch=True, reduced=True)
    scroll_by(page, 1200)
    click_tie(page, min_top=120, tap=True)
    page.wait_for_timeout(20)
    if page.locator(".right-sheet").count():
        check(page.evaluate(NO_MOTION, ".right-sheet, .right-sheet *"), "11 reduced motion: the sheet does not animate")
    else:
        check(False, "11 reduced motion: a tap opens the sheet")
    page.context.close()


GRAPH_STATE = """() => {
  const count = document.querySelector('.map-pane .mode-toggle__count');
  const tab = document.querySelector('.map-pane .mode-toggle button[aria-label="Graph"]');
  const few = document.querySelector('.map-pane__few');
  const pane = document.querySelector('.map-pane')?.getBoundingClientRect();
  const drawing = document.querySelector('.map-pane__graphview .map-pane__drawing')?.getBoundingClientRect();
  return {
    count: count ? Number(count.textContent.replace(/[^0-9]/g, '')) : null,
    dimmed: !!tab && tab.hasAttribute('data-empty'),
    few: few ? Number(few.dataset.neighbours) : null,
    line: document.querySelector('.map-pane__fewline')?.innerText ?? '',
    names: document.querySelectorAll('.map-pane__fewline button').length,
    canvas: document.querySelectorAll('.map-pane__graphview .fg[data-cards]').length,
    share: pane && drawing ? drawing.height / pane.height : 0,
    brief: !!document.querySelector('.map-pane__dock .lean-page__brief'),
    title: document.querySelector('.lean-page__title')?.innerText ?? '',
  };
}"""


def graph_earns_its_space(browser: Browser, base: str, none: str | None, few: str | None, many: str | None) -> None:
    """The Graph view by how many neighbours a declaration has: none, one to three, four or more."""
    for case, name in (("none", none), ("few", few), ("many", many)):
        if not name:
            continue
        page = open_page(browser, base + f"lean/{name}?v=graph", 1440, 900)
        page.wait_for_selector(".map-pane .mode-toggle__count", timeout=30000)
        page.wait_for_timeout(2500)
        got = page.evaluate(GRAPH_STATE)
        tag = f"12 graph, {case} ({name.rsplit('.', 1)[-1]}, {got['count']} neighbours)"
        if case == "none":
            check(got["count"] == 0 and got["dimmed"], f"{tag}: the tab says 0 and is dimmed", str(got))
            check(got["few"] == 0 and got["canvas"] == 0, f"{tag}: no canvas is drawn", str(got))
            check("Nothing in the recorded graph uses this or is used by it" in got["line"], f"{tag}: one line says so", got["line"][:120])
            check(bool(got["title"]), f"{tag}: the inspector stands under it", str(got))
        elif case == "few":
            check(got["count"] is not None and 1 <= got["count"] <= 3 and not got["dimmed"], f"{tag}: the tab carries the count", str(got))
            check(got["few"] == got["count"] and got["canvas"] == 0, f"{tag}: no canvas is drawn", str(got))
            check(got["names"] == got["count"], f"{tag}: each neighbour is named once", f"{got['names']} names: {got['line'][:160]}")
            before = got["title"]
            centre_click(page, ".map-pane__fewline button")
            page.wait_for_timeout(1500)
            check(page.evaluate(GRAPH_STATE)["title"] != before, f"{tag}: a name opens that declaration", before)
        else:
            check(got["count"] is not None and got["count"] >= 4, f"{tag}: the tab carries the count", str(got))
            check(got["canvas"] == 1 and got["few"] is None, f"{tag}: the canvas is drawn", str(got))
            check(got["share"] >= 0.55, f"{tag}: the drawing has most of the pane", f"{got['share']:.2f} of the pane's height")
            check(got["brief"], f"{tag}: the dock under it is the short card", str(got))
            centre_click(page, ".map-pane__dock .lean-page__brief button")
            page.wait_for_timeout(600)
            check(page.locator(".map-pane__dock .lean-page__scroll").count() == 1, f"{tag}: the short card opens to the whole card")
        page.context.close()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("base", help="a served library paper, such as http://127.0.0.1:47342/library/euler/")
    parser.add_argument("--headed", action="store_true", help="show the browser")
    parser.add_argument("--graph-none", help="a Lean declaration with no neighbour in the recorded graph")
    parser.add_argument("--graph-few", help="a Lean declaration with one to three neighbours")
    parser.add_argument("--graph-many", help="a Lean declaration with four or more neighbours")
    args = parser.parse_args()
    base = args.base if args.base.endswith("/") else args.base + "/"
    with sync_playwright() as p:
        browser = p.chromium.launch(headless=not args.headed, ignore_default_args=["--hide-scrollbars"])
        for step in (first_visit, select_and_views, plain_words, paragraph_pick, side_by_side, phone, graph_fit, reduced_motion, auto_manual):
            try:
                step(browser, base)
            except Exception as error:  # a step that cannot run is a failure, and the others still run
                check(False, f"{step.__name__} ran", repr(error)[:300])
        try:
            graph_earns_its_space(browser, base, args.graph_none, args.graph_few, args.graph_many)
        except Exception as error:
            check(False, "graph_earns_its_space ran", repr(error)[:300])
        browser.close()
    if FAILURES:
        print(f"\n{len(FAILURES)} check(s) failed")
        return 1
    print("\nall checks passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
