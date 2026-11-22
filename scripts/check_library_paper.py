#!/usr/bin/env python3
"""Check one served library paper in a real browser, at 1440x900 and 2560x1440.

    python scripts/check_library_paper.py http://127.0.0.1:47311/library/euler/ [--shots DIR] [--budget SECONDS]

For each window size, from a cold browser: the paper's top opens and its first underlined phrase
appears within the load budget; clicking a phrase opens its card with the comparison and note,
and the address names the phrase; topic colours show (several distinct tones); the Graph view
draws; each kind of address (numbered result, phrase, Lean declaration, section) opens what it
names; the Open PDF link opens the PDF in a new tab and the file is a PDF; display formulas lie
inside their columns and never scroll; the front matter carries the AI notice (--notice). Then at 800, 1000, 390, 360 and
320 px: the header's controls do not overlap and Search and Menu stay inside the window. A selected
result and a selected phrase, in both schemes, keep their words' contrast and a quiet amber mark.
A phrase at rest has a 1px underline, and a heavier one when hovered, focused or selected, in both
schemes. The statement counter and the next/previous controls (buttons, j, k) start from a selected
phrase, and from the reading line when nothing is selected.
Needs Playwright for Python with Chromium. Exits 1 if any check fails.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
import time
import urllib.request
from pathlib import Path

from playwright.sync_api import sync_playwright

SIZES = [(1440, 900), (2560, 1440)]


# Every display formula near the screen (fitted as it comes within 900px): its formula and
# equation number lie inside its column (measured from KaTeX's pieces and number, not from
# scrollWidth, which counts KaTeX's 2px strut past a number's edge), it does not scroll, and no
# "Scroll formula" control exists. A display shrunk below its floor offers Expand instead.
MATHS = """() => [...document.querySelectorAll('.prose .math-display')].filter(box => box.getClientRects().length && box.getBoundingClientRect().top < innerHeight + 600).map((box, i) => {
  const html = box.querySelector(':scope > .katex-display > .katex > .katex-html');
  const parts = html ? [...html.querySelectorAll(':scope > .katex-base, :scope > .katex-tag, :scope > .tag')] : [];
  const start = box.getBoundingClientRect().left + box.clientLeft - box.scrollLeft;
  const extent = parts.length ? Math.max(...parts.map(p => p.getBoundingClientRect().right - start)) : box.scrollWidth;
  const scroller = ['auto', 'scroll'].includes(getComputedStyle(box).overflowX) && box.scrollWidth > box.clientWidth + 1;
  const ok = extent <= box.clientWidth + 1 && !scroller && !document.querySelector('.math-cue__scroll');
  return ok ? null : `#${i} ${box.textContent.slice(-12)}: extent ${extent.toFixed(1)}, scrollWidth ${box.scrollWidth}, clientWidth ${box.clientWidth}`;
}).filter(Boolean)"""

# The front matter's line naming who made what, wherever this width puts it.
NOTICE = """() => [...document.querySelectorAll('.account-line, .front-credit')]
  .filter(e => e.offsetParent && e.getBoundingClientRect().width > 1 && e.getBoundingClientRect().left >= 0)
  .map(e => (e.closest('.outline') || e).textContent).join(' ')"""


# The selected words, as drawn: each selected element's text colour against the background it is
# actually read on (its own wash composited over every ancestor's, down to the first opaque one, on a
# canvas so that any CSS colour resolves), the wash's opacity, the line under it, and each selected
# display's fill and rule. Contrast follows WCAG 2.x relative luminance.
SELECTION = r"""() => {
  const ctx = Object.assign(document.createElement('canvas'), { width: 1, height: 1 }).getContext('2d', { willReadFrequently: true });
  const paint = (colours) => { ctx.clearRect(0, 0, 1, 1); for (const c of colours) { ctx.fillStyle = '#000'; ctx.fillStyle = c; ctx.fillRect(0, 0, 1, 1); } return [...ctx.getImageData(0, 0, 1, 1).data]; };
  const lum = ([r, g, b]) => [r, g, b].map(v => v / 255).map(v => v <= 0.04045 ? v / 12.92 : ((v + 0.055) / 1.055) ** 2.4).reduce((s, v, i) => s + v * [0.2126, 0.7152, 0.0722][i], 0);
  const ratio = (a, b) => { const [x, y] = [lum(a), lum(b)].sort((p, q) => q - p); return (x + 0.05) / (y + 0.05); };
  const behind = (el) => { const layers = []; for (let e = el; e; e = e.parentElement) { const c = getComputedStyle(e).backgroundColor; layers.unshift(c); if (paint([c])[3] === 255) break; } return layers; };
  const px = (v) => parseFloat(String(v).split(' ').pop()) || 0;
  const els = [...document.querySelectorAll('.paper .tie[data-pin]')];
  return {
    ground: paint(behind(document.querySelector('.paper'))),
    block: els.some(e => e.hasAttribute('data-pin-block')), runs: document.querySelectorAll('.part__ticks .tick-run').length,
    words: els.filter(e => !e.matches('.math-display')).map(e => {
      const s = getComputedStyle(e), bg = paint(behind(e));
      return { text: e.textContent.slice(0, 24), contrast: ratio(paint([s.color]).slice(0, 3), bg.slice(0, 3)), wash: paint([s.backgroundColor])[3] / 255, line: px(s.backgroundSize), block: e.hasAttribute('data-pin-block') };
    }),
    displays: els.filter(e => e.matches('.math-display')).map(e => {
      const s = getComputedStyle(e);
      return { fill: paint([s.backgroundColor])[3] / 255, image: s.backgroundImage, rule: (s.boxShadow.match(/(\d+(?:\.\d+)?)px 0px 0px 0px inset/) || [0, 0])[1] * 1 };
    }),
  };
}"""


def selection_checks(browser, base, args, check) -> None:
    """A selected result and a selected phrase, in both schemes at 1440x900: the words keep their
    contrast (7:1 in the dark scheme, 4.5:1 in the light), the wash stays faint, a phrase's amber line
    is 2px, a whole statement is one margin rule with its phrases' own topic lines, and a display is
    a thin rule with no fill and no line under it."""
    floors = {"dark": (7.0, 0.08), "light": (4.5, 0.10)}
    for scheme, (floor, wash) in floors.items():
        context = browser.new_context(viewport={"width": 1440, "height": 900}, color_scheme=scheme)
        page = context.new_page()
        for kind, path in ((("result", f"{args.result}/"),) if args.result else ()) + (("phrase", f"@{args.phrase}"),):
            tag = f"selection {scheme} {kind}"
            page.goto(base + path)
            page.wait_for_selector(".paper .tie", timeout=60000)
            if kind == "phrase":
                try:
                    page.wait_for_selector(".paper .tie[data-pin]", timeout=15000)
                except Exception:
                    pass
            page.wait_for_timeout(2500)
            if not page.locator(".paper .tie[data-pin]").count():
                # A numbered result may open on its statement with no phrase of its own to select (quartic).
                check(f"{tag} selected", kind == "result", f"nothing selected at {path}")
                continue
            got = page.evaluate(SELECTION)
            if args.shots:
                page.screenshot(path=str(args.shots / f"selection-{scheme}-{kind}.png"))
            words, displays = got["words"], got["displays"]
            low = min((w["contrast"] for w in words), default=None)
            # A selection may be a display alone (a formula has no run of words to measure).
            check(f"{tag} contrast", (low is None and displays) or (low is not None and low >= floor),
                  f"lowest {low and round(low, 2)}:1 (floor {floor}:1) over {len(words)} selected runs and {len(displays)} displays")
            heavy = [w for w in words if w["wash"] > wash + 0.005]
            check(f"{tag} faint wash", not heavy, f"wash above {wash:.0%}: {heavy[:2]}")
            thick = [w for w in words if w["line"] > 2]
            check(f"{tag} thin line", not thick, f"lines over 2px: {thick[:2]}")
            loud = [d for d in displays if d["fill"] > 0 or d["image"] != "none" or d["rule"] > 3]
            check(f"{tag} displays", not loud, f"a selected display with a fill, a line under it or a rule over 3px: {loud[:2]}")
            # A whole statement is one margin rule beside it, its phrases keeping their topic lines; a
            # phrase or sentence is a 2px amber line with no rule of its own.
            if got["block"]:
                check(f"{tag} one margin rule", got["runs"] >= 1 and all(w["block"] and w["line"] <= 1.5 for w in words),
                      f"runs={got['runs']} lines={sorted({w['line'] for w in words})}")
            else:
                check(f"{tag} phrase line", not got["runs"] and all(w["line"] == 2 for w in words),
                      f"runs={got['runs']} lines={sorted({w['line'] for w in words})}")
            print(f"{tag}: lowest contrast {low and round(low, 2)}:1, wash {max((w['wash'] for w in words), default=0):.3f}, "
                  f"{len(words)} runs, {len(displays)} displays", file=sys.stderr)
        context.close()


# Where the reader is, as the page shows it: the strip's counter, the statement each lit kind of
# mark names (a statement's first mark carries "…, statement N of M" while it is the keys' stop),
# the address, the pane's view and the scroll position.
STEP_STATE = r"""() => {
  const num = (el) => { const m = el && (el.getAttribute('aria-label') || '').match(/(\d+) of (\d+)/); return m ? Number(m[1]) : null; };
  const counter = document.querySelector('.reader-strip__steps .num')?.textContent ?? '';
  const m = counter.match(/(\d+) of (\d+)/);
  const graph = [...document.querySelectorAll('button[aria-pressed]')].find(b => b.textContent.trim() === 'Graph');
  return {
    counter: m ? Number(m[1]) : null, total: m ? Number(m[2]) : null, text: counter,
    pinned: num(document.querySelector('.paper .tie[data-pin][aria-label]')),
    lit: num(document.querySelector('.paper .tie[data-on][aria-label]')),
    anyPin: !!document.querySelector('.paper .tie[data-pin]'),
    url: location.href, graph: graph ? graph.getAttribute('aria-pressed') === 'true' : null, y: Math.round(scrollY),
  };
}"""

# A point on a mark's own words (not a Lean-name button or link inside it), on its first line.
WORDS_POINT = """e => {
    for (const r of e.getClientRects()) for (let x = r.left + 3; x < r.right - 2; x += 5) {
        const y = r.top + r.height / 2, hit = document.elementFromPoint(x, y);
        if (hit && e.contains(hit) && !hit.closest('button, a')) return {x, y};
    }
    return null;
}"""


def step_checks(browser, base, check) -> None:
    """The counter and the next/previous controls (buttons, j and k) follow a selected phrase, not the
    reading line, and both agree with the phrase the page lights at every step. Auto: nothing is
    selected and the reading line chooses the start. Manual: the second tied statement that can be
    clicked is selected and the page then scrolled away from it by hand, so that the reading line
    names another statement. Stepping lets go of the selection, keeps the pane's Graph view and the
    address of the statement stepped to, and leaves the page still once it has landed."""
    for mode in ("auto", "manual"):
        tag = f"steps {mode}"
        context = browser.new_context(viewport={"width": 1440, "height": 900})
        page = context.new_page()
        try:
            page.goto(base)
            page.wait_for_selector(".paper .tie[data-tone]", timeout=60000)
            page.wait_for_selector(".reader-strip__steps .num", timeout=30000)
            page.wait_for_timeout(2000)
            state = lambda: page.evaluate(STEP_STATE)
            total = state()["total"]
            if not total or total < 3:
                report_skip = f"{total} tied statements: nothing to step between"
                check(f"{tag} counter and selection agree", True, report_skip)
                continue

            def wait_counter(n):
                try:
                    page.wait_for_function("(n) => { const m = (document.querySelector('.reader-strip__steps .num')?.textContent ?? '').match(/(\\d+) of/); return m && Number(m[1]) === n; }", arg=n, timeout=8000)
                except Exception:
                    pass
                page.wait_for_timeout(1500)
                return state()

            def landed(name, want, before_view):
                got = wait_counter(want)
                page.wait_for_timeout(1500)
                still = state()
                lit = page.evaluate("""() => { const e = document.querySelector('.paper .tie[data-on][aria-label]'); if (!e) return null; const r = e.getBoundingClientRect(); return [Math.round(r.top), Math.round(r.bottom)]; }""")
                ok = (got["counter"] == want and got["lit"] == want and not got["anyPin"] and "/@" not in got["url"]
                      and abs(still["y"] - got["y"]) <= 4 and lit is not None and 0 <= lit[0] and lit[1] <= 900
                      and (before_view is not True or (got["graph"] is True and "v=graph" in got["url"])))
                check(f"{tag} {name}", ok, f"want {want}: counter {got['counter']}, lit {got['lit']}, pinned {got['anyPin']}, "
                      f"graph {got['graph']}, y {got['y']}->{still['y']}, lit at {lit}, {got['url']}")
                return got

            if mode == "auto":
                # Scroll by hand into the paper until the reading line follows an interior statement.
                start = None
                for _ in range(12):
                    page.mouse.wheel(0, 600)
                    got = wait_counter(-1)
                    if got["counter"] and 1 < got["counter"] < total:
                        start = got["counter"]
                        break
                if start is None:
                    check(f"{tag} counter and selection agree", False, f"no interior statement reached by scrolling: {state()}")
                    continue
                got = state()
                check(f"{tag} start follows the reading line", got["lit"] == start and not got["anyPin"], f"counter {start}, lit {got['lit']}")
                for name, act, want in (("next button", lambda: page.get_by_role("button", name="Next tied statement").click(), start + 1),
                                        ("previous button", lambda: page.get_by_role("button", name="Previous tied statement").click(), start),
                                        ("j", lambda: page.keyboard.press("j"), start + 1),
                                        ("k", lambda: page.keyboard.press("k"), start)):
                    act()
                    landed(name, want, None)
                continue

            # Manual: click phrases in reading order until one selects an interior statement.
            segments = page.eval_on_selector_all(".paper .tie[data-tone][data-t]:not(.math-display)", "els => [...new Set(els.map(e => e.dataset.t))]")
            start, mark = None, None
            for segment in segments[:80]:
                candidate = page.locator(f'.paper .tie[data-tone][data-t="{segment}"]').first
                candidate.evaluate("e => e.scrollIntoView({block: 'center'})")
                page.wait_for_timeout(300)
                point = candidate.evaluate(WORDS_POINT)
                if not point:
                    continue
                page.mouse.click(point["x"], point["y"])
                try:
                    page.wait_for_selector(".paper .tie[data-pin][aria-label]", timeout=5000)
                except Exception:
                    continue
                page.wait_for_timeout(800)
                got = state()
                if got["pinned"] and 1 < got["pinned"] < total:
                    start, mark = got["pinned"], candidate
                    break
            if start is None:
                check(f"{tag} counter and selection agree", False, "no interior statement could be selected")
                continue
            graph = page.get_by_role("button", name="Graph", exact=True)
            if graph.count():
                graph.first.click()
                page.wait_for_timeout(800)
            for name, act, want in (("next button", lambda: page.get_by_role("button", name="Next tied statement").click(), start + 1),
                                    ("previous button", lambda: page.get_by_role("button", name="Previous tied statement").click(), start),
                                    ("j", lambda: page.keyboard.press("j"), start + 1),
                                    ("k", lambda: page.keyboard.press("k"), start)):
                if not state()["anyPin"]:
                    # Select the statement again before each step, so every step starts from a selection.
                    cur = state()["lit"]
                    target = mark if cur == start else page.locator(".paper .tie[data-on][aria-label]").first
                    target.evaluate("e => e.scrollIntoView({block: 'center'})")
                    page.wait_for_timeout(300)
                    point = target.evaluate(WORDS_POINT)
                    page.mouse.click(point["x"], point["y"])
                    page.wait_for_selector(".paper .tie[data-pin][aria-label]", timeout=5000)
                    page.wait_for_timeout(800)
                selected = state()["pinned"]
                # Read on by hand, away from the selection: the reading line now names another statement.
                page.mouse.wheel(0, 1400)
                page.wait_for_timeout(2000)
                away = state()
                check(f"{tag} counter keeps the selection before {name}", away["counter"] == selected and away["pinned"] == selected,
                      f"selected {selected}, counter {away['counter']} after scrolling to y {away['y']}")
                view = away["graph"]
                act()
                landed(name, want, view)
        except Exception as error:  # noqa: BLE001 - a check, reported with its cause
            check(f"{tag} counter and selection agree", False, f"{type(error).__name__}: {error}")
        finally:
            context.close()


# A phrase's drawn underline: the line's height (background-size), whether a tint lies behind it,
# and the state it is in.
UNDERLINE = r"""(e) => {
  const s = getComputedStyle(e);
  const ctx = Object.assign(document.createElement('canvas'), { width: 1, height: 1 }).getContext('2d', { willReadFrequently: true });
  ctx.clearRect(0, 0, 1, 1); ctx.fillStyle = '#000'; ctx.fillStyle = s.backgroundColor; ctx.fillRect(0, 0, 1, 1);
  return { line: parseFloat(s.backgroundSize.split(' ').pop()) || 0, size: s.backgroundSize, tint: ctx.getImageData(0, 0, 1, 1).data[3] / 255,
           image: s.backgroundImage, focus: e.matches(':focus-visible'), hover: e.matches(':hover') };
}"""


def underline_checks(browser, base, args, check) -> None:
    """In both schemes at 1440x900, measured as drawn: a phrase at rest has a 1px underline and no tint;
    pointed at, keyboard-focused or selected it is heavier (hover and focus 2px over a light tint, a
    selected phrase 2px in amber, a selected whole statement its margin rule). Inside a selected whole
    statement the prose phrases keep the 1px resting line."""
    for scheme in ("dark", "light"):
        tag = f"underline {scheme}"
        context = browser.new_context(viewport={"width": 1440, "height": 900}, color_scheme=scheme)
        page = context.new_page()
        try:
            page.goto(base)
            page.wait_for_selector(".paper .tie[data-tone]", timeout=60000)
            page.wait_for_timeout(2500)
            resting = ".paper .tie[data-tone]:not(.math-display):not([data-pin]):not([data-decl]):not([data-point]):not([data-on])"
            # A phrase that is drawn (not inside a folded or hidden part), so it can be pointed at and focused.
            index = page.evaluate("""(sel) => { const els = [...document.querySelectorAll(sel)];
                const shown = els.findIndex((e, i) => i >= 2 && e.getClientRects().length > 0 && (!e.checkVisibility || e.checkVisibility({ visibilityProperty: true })));
                return shown < 0 ? 0 : shown; }""", resting)
            el = page.locator(resting).nth(index)
            el.evaluate("e => e.scrollIntoView({block: 'center'})")
            page.mouse.move(2, 450)
            page.wait_for_timeout(1200)
            el.evaluate("e => e.scrollIntoView({block: 'center'})")
            page.wait_for_timeout(400)
            rest = el.evaluate(UNDERLINE)
            check(f"{tag} rest 1px", rest["line"] == 1 and rest["tint"] == 0 and not rest["hover"], str(rest))
            if args.shots:
                box = el.bounding_box()
                if box:
                    page.screenshot(path=str(args.shots / f"underline-{scheme}-rest.png"),
                                    clip={"x": max(0, box["x"] - 40), "y": max(0, box["y"] - 24), "width": min(520, box["width"] + 80), "height": box["height"] + 48})
            point = el.evaluate(WORDS_POINT)
            page.mouse.move(point["x"], point["y"])
            page.wait_for_timeout(300)
            hover = el.evaluate(UNDERLINE)
            check(f"{tag} hover stronger", hover["hover"] and hover["line"] == 2 and 0 < hover["tint"] <= 0.2, str(hover))
            page.mouse.move(2, 450)
            # Keyboard focus: a key first, so that the focus that follows is shown as keyboard focus.
            page.keyboard.press("Shift")
            el.evaluate("e => { if (!e.hasAttribute('tabindex')) e.setAttribute('tabindex', '-1'); e.focus({ preventScroll: true }); }")
            page.wait_for_timeout(300)
            focus = el.evaluate(UNDERLINE)
            check(f"{tag} focus stronger", focus["focus"] and focus["line"] == 2 and focus["tint"] > 0, str(focus))
            el.evaluate("e => e.blur()")
            # Selected: the phrase the address names.
            page.goto(base + f"@{args.phrase}")
            page.wait_for_selector(".paper .tie[data-pin]", timeout=30000)
            page.mouse.move(2, 450)
            page.wait_for_timeout(1500)
            sel = page.evaluate("""(f) => { const fn = eval(f); const els = [...document.querySelectorAll('.paper .tie[data-pin]:not(.math-display)')];
                return { marks: els.map(fn), block: els.some(e => e.hasAttribute('data-pin-block')), runs: document.querySelectorAll('.part__ticks .tick-run').length }; }""", UNDERLINE)
            if sel["block"]:
                ok = sel["runs"] >= 1
            else:
                ok = bool(sel["marks"]) and all(m["line"] == 2 for m in sel["marks"])
            check(f"{tag} selected stronger", ok, f"block {sel['block']}, runs {sel['runs']}, lines {sorted({m['line'] for m in sel['marks']})}")
            if args.shots:
                page.screenshot(path=str(args.shots / f"underline-{scheme}-selected.png"))
            # A selected whole statement (a numbered result): its prose phrases keep the 1px resting line
            # under the faint wash, and one margin rule marks the selection.
            if args.result:
                page.goto(base + f"{args.result}/")
                page.wait_for_selector(".paper .tie", timeout=60000)
                page.mouse.move(2, 450)
                page.wait_for_timeout(2500)
                block = page.evaluate("""(f) => { const fn = eval(f); const els = [...document.querySelectorAll('.paper .tie[data-pin][data-pin-block]:not(.math-display)')];
                    return { marks: els.map(fn), runs: document.querySelectorAll('.part__ticks .tick-run').length }; }""", UNDERLINE)
                if block["marks"]:
                    check(f"{tag} selected statement keeps 1px lines", block["runs"] >= 1 and all(m["line"] == 1 for m in block["marks"]),
                          f"runs {block['runs']}, lines {sorted({m['line'] for m in block['marks']})}")
                else:
                    report_note = "the result opens with no whole statement selected"
                    check(f"{tag} selected statement keeps 1px lines", True, report_note)
        except Exception as error:  # noqa: BLE001
            check(f"{tag} rest 1px", False, f"{type(error).__name__}: {error}")
        finally:
            context.close()


def pdf_only_checks(page, base, tag, width, height, args, check, start) -> None:
    """A document read only in its PDF: the PDF opens with its phrases marked, no Text toggle, and a
    mark opens the phrase's card, Lean and graph; phrase, Lean and unknown addresses open what they name."""
    page.wait_for_selector(".pdf-view__mark[data-tone], .pdf-view__mark", timeout=60000)
    first = time.monotonic() - start
    check(f"{tag} load", first <= args.budget, f"first PDF mark after {first:.2f}s (budget {args.budget}s)")
    page.wait_for_load_state("networkidle")
    page.wait_for_timeout(1500)
    check(f"{tag} no text toggle", not page.locator(".view-toggle").count(), "a Text | PDF toggle on a PDF-only paper")
    check(f"{tag} AI notice shown", args.notice in page.evaluate(NOTICE), f"no front-matter line containing {args.notice!r}")
    marks = page.locator(".pdf-view__mark").count()
    check(f"{tag} marks on the PDF", marks >= 3, f"{marks} marks")
    if args.shots:
        args.shots.mkdir(parents=True, exist_ok=True)
        page.screenshot(path=str(args.shots / f"top-{tag}.png"))
    mark = page.locator(".pdf-view__mark").first
    mark.scroll_into_view_if_needed()
    mark.click()
    page.wait_for_function("() => /\\/@|[?&]n=/.test(location.href)", timeout=15000)
    card = page.locator(".phrase-card").first
    card.wait_for(timeout=15000)
    check(f"{tag} mark click", "AI-assessed" in card.inner_text(), page.url)
    page.get_by_role("button", name="Graph", exact=True).first.click()
    page.wait_for_selector(".map-pane__graphview .fg[data-cards]", timeout=15000)
    nodes = int(page.get_attribute(".map-pane__graphview .fg[data-cards]", "data-cards") or 0)
    check(f"{tag} graph view", nodes > 0, f"{nodes} cards drawn")
    if args.shots:
        page.screenshot(path=str(args.shots / f"phrase-{tag}.png"))
    page.goto(base + f"@{args.phrase}")
    page.wait_for_selector(".pdf-view__mark.is-selected", timeout=60000)
    # The PDF scrolls to the phrase once its pages are laid out: wait for the mark to arrive on screen.
    try:
        page.wait_for_function("(h) => { const r = document.querySelector('.pdf-view__mark.is-selected')?.getBoundingClientRect(); return !!r && r.top >= 0 && r.top <= h; }", arg=height, timeout=15000)
    except Exception:
        pass
    sel = page.locator(".pdf-view__mark.is-selected").first.bounding_box()
    check(f"{tag} address phrase", sel is not None and 0 <= sel["y"] <= height and page.url.endswith(f"@{args.phrase}"), page.url)
    page.goto(base + f"lean/{args.decl}")
    page.wait_for_timeout(4000)
    check(f"{tag} address lean", args.decl.rsplit(".", 1)[-1] in page.inner_text("body"), page.url)
    page.goto(base + "@no-such-phrase-here")
    page.wait_for_selector(".address-notice[data-missing]", timeout=60000)
    check(f"{tag} unknown phrase says not found", "Not found" in page.inner_text(".address-notice[data-missing]"), page.url)
    link = page.locator("a", has_text="Open PDF").first
    href = link.get_attribute("href") if link.count() else None
    check(f"{tag} open pdf link", bool(href and href.split("#")[0].endswith(".pdf") and link.get_attribute("target") == "_blank"), f"href={href}")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("base")
    ap.add_argument("--shots", type=Path)
    ap.add_argument("--budget", type=float, default=8.0)
    ap.add_argument("--phrase", default="e01.abstract.bounded-velocity")
    ap.add_argument("--result", default="theorem-1.1", help="a numbered result's address; empty for a paper with none (the SK short paper)")
    ap.add_argument("--decl", default="TorusEuler.EulerSingularityWitness")
    ap.add_argument("--section", default="5.6")
    ap.add_argument("--raw-check", action="append", default=[], help="a Lean name whose card must show no raw TeX")
    ap.add_argument("--notice", default="made with AI", help="words of the AI notice the front matter must show at every width")
    ap.add_argument("--no-pdf", action="store_true", help="the main document has no PDF: expect no Open PDF link and no toggle")
    ap.add_argument("--pdf-only", action="store_true", help="the paper is read only in its PDF: no Text toggle, the PDF view opens at its top")
    ap.add_argument("--notes-optional", action="store_true",
                    help="a phrase's declaration may have no reading note yet (the card then shows its comparison alone)")
    ap.add_argument("--companion", action="append", default=[], metavar="PAGE[/@ID]",
                    help="a companion page (or a phrase address on it) that must open its own text, never the edition error")
    args = ap.parse_args()
    base = args.base.rstrip("/") + "/"
    failures, report = [], {}

    def check(name, ok, detail=""):
        report[name] = {"ok": bool(ok), "detail": detail}
        if not ok:
            failures.append(f"{name}: {detail}")

    with sync_playwright() as pw:
        browser = pw.chromium.launch()
        for width, height in SIZES:
            tag = f"{width}x{height}"
            context = browser.new_context(viewport={"width": width, "height": height})
            page = context.new_page()
            errors = []
            page.on("pageerror", lambda e: errors.append(str(e)))
            start = time.monotonic()
            page.goto(base)
            if args.pdf_only:
                pdf_only_checks(page, base, tag, width, height, args, check, start)
                context.close()
                continue
            page.wait_for_selector(".paper .tie[data-tone]", timeout=60000)
            first = time.monotonic() - start
            page.wait_for_load_state("networkidle")
            check(f"{tag} load", first <= args.budget, f"first underlined phrase after {first:.2f}s (budget {args.budget}s)")
            page.wait_for_timeout(1500)
            bad = page.evaluate(MATHS)
            check(f"{tag} display maths fit without scrolling", not bad, "; ".join(bad[:3]))
            check(f"{tag} AI notice shown", args.notice in page.evaluate(NOTICE), f"no front-matter line containing {args.notice!r}")
            # The front matter says each sentence once, and says once that the links were made with AI.
            line = page.evaluate("() => [...document.querySelectorAll('.account-line, .front-credit')].map(e => e.textContent).join(' ')")
            said = [t.strip() for t in re.split(r"(?<=[.!?])\s+(?=[A-Z])", line.replace("Open PDF", ". Open PDF")) if t.strip()]
            repeated = sorted({t for t in said if said.count(t) > 1})
            ai = [t for t in said if re.search(r"\bwith AI\b", t)]
            check(f"{tag} front matter says each sentence once", not repeated and len(ai) <= 1, f"repeated {repeated[:2]}, AI sentences {len(ai)}")
            tones = page.eval_on_selector_all(".paper .tie[data-tone]", "els => new Set(els.map(e => e.dataset.tone)).size")
            check(f"{tag} topic colours", tones >= 3, f"{tones} distinct tones")
            if args.shots:
                args.shots.mkdir(parents=True, exist_ok=True)
                page.screenshot(path=str(args.shots / f"top-{tag}.png"))
            # Clicking a phrase opens its card and its Lean.
            # A phrase tied to Lean (its title names the Lean), centred so no sticky bar covers it.
            tie = page.locator('.paper .tie[data-tone][title*="Lean:"]').nth(1)
            tie.evaluate("e => e.scrollIntoView({block: 'center'})")
            page.wait_for_timeout(500)
            # A phrase that wraps over lines has a bounding box whose centre can fall between its
            # lines; click its first line, where a reader would.
            # A phrase may begin with a Lean name drawn as its own button, or a link; click its words,
            # the first point on it that is the phrase itself and not a control inside it.
            first = tie.evaluate("""e => {
                for (const r of e.getClientRects()) for (let x = r.left + 4; x < r.right - 2; x += 6) {
                    const y = r.top + r.height / 2, hit = document.elementFromPoint(x, y);
                    if (hit && e.contains(hit) && !hit.closest('button, a')) return {x, y};
                }
                const r = e.getClientRects()[0]; return {x: r.left + Math.min(8, r.width / 2), y: r.top + r.height / 2};
            }""")
            page.mouse.click(first["x"], first["y"])
            page.wait_for_function("() => /\\/@|[?&]n=|\\/(theorem|proposition|lemma|corollary|definition|remark|conjecture|problem|example|assumption|claim|step)-[0-9a-z.-]+\\//.test(location.href)", timeout=15000)
            card = page.locator(".phrase-card").first
            try:
                card.wait_for(timeout=15000)
            except Exception:
                if args.shots:
                    args.shots.mkdir(parents=True, exist_ok=True)
                    page.screenshot(path=str(args.shots / f"click-no-card-{tag}.png"))
                raise
            text = card.inner_text()
            # The card's notes load after it opens: wait for the note before reading the card.
            if not args.notes_optional:
                try:
                    page.wait_for_function("() => (document.querySelector('.phrase-card') || {}).innerText?.includes('Reading note')", timeout=10000)
                except Exception:
                    pass
            text = card.inner_text()
            check(f"{tag} phrase click", "AI-assessed" in text and (args.notes_optional or "Reading note" in text), page.url)
            page.get_by_role("button", name="Lean", exact=True).first.click()
            page.wait_for_selector(".phrase-card, .decl, pre, code", timeout=15000)
            check(f"{tag} phrase Lean", "v=lean" in page.url, page.url)
            page.get_by_role("button", name="Graph", exact=True).first.click()
            page.wait_for_timeout(1500)
            page.wait_for_selector(".map-pane__graphview .fg[data-cards]", timeout=15000)
            nodes = int(page.get_attribute(".map-pane__graphview .fg[data-cards]", "data-cards") or 0)
            check(f"{tag} graph view", nodes > 0, f"{nodes} cards drawn")
            if args.shots:
                page.screenshot(path=str(args.shots / f"phrase-{tag}.png"))
            # Each kind of address.
            for kind, path, expect in (
                *((("result", f"{args.result}/", "" if args.result.startswith("claim-") else "Theorem"),) if args.result else ()),
                ("phrase", f"@{args.phrase}", "AI-assessed"),
                ("lean", f"lean/{args.decl}", args.decl.rsplit(".", 1)[-1]),
            ):
                page.goto(base + path)
                page.wait_for_selector(".paper .tie", timeout=60000)
                # The card's words load after the paper; wait for them rather than a fixed time.
                try:
                    page.wait_for_function("(w) => document.body.innerText.includes(w)", arg=expect, timeout=15000)
                except Exception:
                    pass
                page.wait_for_timeout(500)
                body = page.inner_text("body")
                check(f"{tag} address {kind}", expect in body and page.url.rstrip("/").endswith(path.rstrip("/").split("?")[0]), page.url)
            page.goto(base + "#" + args.section)
            page.wait_for_selector(".paper .tie", timeout=60000)
            page.wait_for_timeout(2000)
            top = page.evaluate("(id) => document.getElementById(id)?.getBoundingClientRect().top ?? null", args.section)
            check(f"{tag} address section", top is not None and -50 <= top <= height, f"section top {top}")
            # A numbered result opens at its statement: its bold label is on screen and the lit phrase,
            # if any, is not an introduction before it.
            fresh = browser.new_context(viewport={"width": width, "height": height})
            probe = fresh.new_page()
            probe.goto(base + (f"{args.result}/" if args.result else ""))
            probe.wait_for_selector(".paper .tie", timeout=60000)
            probe.wait_for_timeout(2500)
            title = " ".join(w.capitalize() if i == 0 else w.upper() if re.fullmatch(r"[a-z](\.\d+)*", w) else w
                             for i, w in enumerate(args.result.split("-", 1)))
            place = probe.evaluate("""(title) => {
                const label = [...document.querySelectorAll('.paper strong')].find(s => s.textContent.trim().startsWith(title));
                const pin = document.querySelector('.paper .tie[data-pin]');
                const top = (el) => el ? Math.round(el.getBoundingClientRect().top) : null;
                return { label: top(label), pin: top(pin) };
            }""", title)
            # A result the paper prints without a number has no bold label to land on.
            if args.result and not args.result.startswith("claim-"):
                check(f"{tag} result lands on its statement", place["label"] is not None and 0 <= place["label"] <= height
                      and (place["pin"] is None or place["pin"] >= place["label"] - 2), f"{title}: {place}")
            # An address that names no phrase opens the paper with a "not found" line, never a guessed place.
            probe.goto(base + "@no-such-phrase-here")
            probe.wait_for_selector(".paper .tie", timeout=60000)
            probe.wait_for_timeout(2000)
            missing = probe.locator(".address-notice[data-missing]")
            check(f"{tag} unknown phrase says not found", missing.count() and "Not found" in missing.inner_text()
                  and not probe.locator(".paper .tie[data-pin]").count(), probe.url)
            # A retired phrase link opens its notice and lights no other phrase.
            with urllib.request.urlopen(base + "addresses.json") as response:
                retired = sorted(json.loads(response.read()).get("retired") or {})
            if retired:
                probe.goto(base + f"@{retired[0]}")
                probe.wait_for_selector(".paper .tie", timeout=60000)
                probe.wait_for_timeout(2000)
                notice = probe.locator(".address-notice--retired")
                said = notice.inner_text() if notice.count() else ""
                check(f"{tag} retired link opens its notice", "retired on" in said and not probe.locator(".paper .tie[data-pin]").count()
                      and probe.url.endswith(f"@{retired[0]}"), f"{probe.url}: {said!r}")
            fresh.close()
            # Open PDF.
            link = page.locator("a", has_text="Open PDF").first
            href = link.get_attribute("href") if link.count() else None
            target = link.get_attribute("target") if link.count() else None
            if args.no_pdf:
                # The main document has no PDF: the reader offers no Open PDF link.
                check(f"{tag} no open pdf link", href is None, f"href={href}")
            else:
                check(f"{tag} open pdf link", bool(href and href.split("#")[0].endswith(".pdf") and target == "_blank"), f"href={href} target={target}")
            if href:
                url = href if href.startswith("http") else page.url.split("/library/")[0] + href
                with urllib.request.urlopen(url.split("#")[0]) as response:
                    ctype = response.headers.get("Content-Type", "")
                    check(f"{tag} pdf served", response.status == 200 and "pdf" in ctype, f"{response.status} {ctype}")
            # The PDF/typeset toggle keeps the selected phrase and the place.
            if page.locator(".view-toggle").count():
                page.goto(base + f"@{args.phrase}?v=lean")
                page.wait_for_selector(".paper .tie", timeout=90000)
                try:
                    page.wait_for_selector(".phrase-card", timeout=60000)
                except Exception:
                    check(f"{tag} toggle setup", False, f"no phrase card at {page.url}")
                    context.close()
                    continue
                page.get_by_role("button", name="PDF", exact=True).click()
                page.wait_for_selector(".pdf-view__mark.is-selected", timeout=30000)
                page.wait_for_timeout(1500)
                sel = page.locator(".pdf-view__mark.is-selected").first.bounding_box()
                kept = "view=pdf" in page.url and f"@{args.phrase}" in page.url and "v=lean" in page.url
                check(f"{tag} toggle to pdf", kept and sel is not None and 0 <= sel["y"] <= height, f"{page.url} mark y={sel and round(sel['y'])}")
                if args.shots:
                    page.screenshot(path=str(args.shots / f"pdf-{tag}.png"))
                page.get_by_role("button", name="Text", exact=True).click()
                page.wait_for_timeout(2000)
                el = page.locator(".paper .tie[data-tone]").filter(has_text="").first
                back = "view=pdf" not in page.url and f"@{args.phrase}" in page.url
                check(f"{tag} toggle to text", back and page.locator(".phrase-card").count() > 0, page.url)
            # The whole map, from the header's Map link and from the pane after a phrase click.
            before = len(errors)
            page.goto(base + "map/")
            page.wait_for_timeout(4000)
            body = page.inner_text("body")
            check(f"{tag} map page", len(errors) == before and len(body.strip()) > 200 and not page.locator(".page-guard").count(), "; ".join(errors[before:][:2]) or f"{len(body)} characters")
            page.goto(base + f"@{args.phrase}?v=graph")
            page.wait_for_selector(".phrase-card", timeout=60000)
            whole = page.get_by_role("button", name="Whole proof map")
            if whole.count():
                before = len(errors)
                whole.first.click()
                page.wait_for_timeout(3000)
                check(f"{tag} whole proof map", len(errors) == before and not page.locator(".page-guard").count(), "; ".join(errors[before:][:2]))
                # An edge the layered map cannot route is drawn and counted, never dropped: every
                # dashed unroutable line has its count in the map's notes, and the counts agree.
                drawn = page.locator(".map-pane .link--unroutable").count()
                noted = page.eval_on_selector_all(".map-pane [data-unroutable-count]", "els => els.reduce((n, e) => n + Number(e.dataset.unroutableCount), 0)")
                check(f"{tag} unroutable edges counted", drawn == noted, f"{drawn} drawn, {noted} counted")
            # The graph's words state what the data records: no "not a step of the argument" for a
            # missing route, each side's count names its relations, and the key names every
            # relation a line on the drawing shows.
            page.goto(base + f"@{args.phrase}?v=graph")
            page.wait_for_selector(".fg", timeout=60000)
            page.wait_for_timeout(1500)
            words = page.evaluate("""() => {
                const fg = document.querySelector('.fg');
                const sides = [...fg.querySelectorAll('.fg__side')].map(s => [s.dataset.band, Number(s.dataset.total), (s.querySelector('.fg__sidekinds')?.textContent ?? '').trim()]);
                const lines = new Set([...fg.querySelectorAll('.fg__edge')].map(e => [...e.classList].find(c => c.startsWith('fg__edge--') && c !== 'fg__edge--group')?.slice(10)).filter(Boolean));
                const keyed = new Set([...fg.querySelectorAll('[data-key-kind]')].map(e => e.dataset.keyKind));
                return { text: document.querySelector('.map-pane')?.innerText ?? '', sides, lines: [...lines], keyed: [...keyed] };
            }""")
            claim = re.search(r"not a step of the paper", words["text"], re.I)
            check(f"{tag} graph says missing data, not a claim", not claim, "found 'Not a step of the paper'" if claim else "")
            unnamed = [band for band, total, how in words["sides"] if total and not re.match(r"\d+ (by|in) ", how)]
            check(f"{tag} graph counts name their relations", words["sides"] and not unnamed, f"sides {words['sides']}")
            unkeyed = [k for k in words["lines"] if k not in words["keyed"]]
            check(f"{tag} graph key names every line's relation", not unkeyed, f"lines {words['lines']}, key {words['keyed']}")
            # Cards render their mathematics: no raw $ or backslash command left in the text a reader sees.
            raw = []
            for name in [args.decl, *args.raw_check]:
                page.goto(base + f"lean/{name}")
                page.wait_for_selector(".paper .tie", timeout=90000)
                page.wait_for_timeout(2500)
                text = page.evaluate("""() => [...document.querySelectorAll('.phrase-card, .lean-reading-note, .lean-block__link, .comparator-mark')]
                    .map(e => { const c = e.cloneNode(true); c.querySelectorAll('.katex, code, pre').forEach(k => k.remove()); return c.innerText; }).join('\\n')""")
                found = re.findall(r"\$|\\[A-Za-z]+", text)
                if found:
                    raw.append(f"{name}: {sorted(set(found))[:5]}")
            check(f"{tag} cards typeset", not raw, "; ".join(raw[:3]))
            check(f"{tag} no page errors", not errors, "; ".join(errors[:3]))
            context.close()
        # A failure in the pane beside the paper stays in the pane: its code is made to throw, and the
        # paper, its phrases and the page itself must still be there, with the pane's own notice.
        ready = ".pdf-view__mark" if args.pdf_only else ".paper .tie[data-tone]"
        context = browser.new_context(viewport={"width": 1440, "height": 900})
        context.route(re.compile(r".*/assets/MapPane-[^/]*\.js$"), lambda route: route.fulfill(status=200, content_type="text/javascript", body="throw new Error('injected map pane failure');"))
        page = context.new_page()
        page.goto(base + f"@{args.phrase}?v=graph")
        page.wait_for_selector(ready, timeout=60000)
        try:
            page.wait_for_selector(".graph-boundary", timeout=15000)
            contained = True
        except Exception:
            contained = False
        kept = page.locator(".paper .tie, .pdf-view__mark").count() > 0 and not page.locator(".page-guard").count()
        check("pane failure contained", contained and kept, f"pane notice {contained}, paper kept {kept}")
        context.close()
        # Narrow windows and phones: the header's visible parts never overlap, Search and Menu lie
        # inside the window, nothing scrolls sideways, a formula that fits does not scroll, the AI
        # notice is in the front matter, and the paper's phrases are there to tap.
        for width, height in ((800, 700), (1000, 800), (390, 844), (360, 740), (320, 640)):
            tag = f"{width}x{height}"
            context = browser.new_context(viewport={"width": width, "height": height}, is_mobile=width < 500, has_touch=width < 500)
            page = context.new_page()
            page.goto(base)
            page.wait_for_selector(ready, timeout=60000)
            boxes = page.evaluate("""() => [...document.querySelector('.topbar').querySelectorAll('a, button')]
                .filter(e => e.offsetParent && getComputedStyle(e).visibility !== 'hidden')
                .map(e => { const r = e.getBoundingClientRect(); return [e.textContent.trim().slice(0, 24), r.left, r.right, r.top, r.bottom]; })
                .filter(b => b[2] - b[1] > 1)""")
            clash = [(a[0], b[0]) for i, a in enumerate(boxes) for b in boxes[i + 1:]
                     if a[1] < b[2] - 1 and b[1] < a[2] - 1 and a[3] < b[4] - 1 and b[3] < a[4] - 1]
            check(f"{tag} header", not clash, f"overlapping: {clash[:3]}")
            wide = page.evaluate("document.documentElement.scrollWidth - innerWidth")
            check(f"{tag} no sideways scroll", wide <= 1, f"{wide}px wider than the window")
            # Measured against the window asked for: a phone browser widens its layout to fit
            # what overflows, so innerWidth alone would follow a bar pushed off the screen.
            ways = page.evaluate("""() => ['.search-trigger', '.menu-toggle'].map(s => document.querySelector('.topbar ' + s))
                .filter(e => e && e.offsetParent).map(e => { const r = e.getBoundingClientRect(); return [e.className.split(' ').pop(), r.left, r.right, r.width, r.height]; })""")
            outside = [w for w in ways if w[1] < 0 or w[2] > width + 0.5 or w[3] < 24 or w[4] < 24]
            check(f"{tag} search and menu on screen", ways and not outside, f"{outside or 'no Search or Menu button'} in a {width}px window")
            page.wait_for_timeout(1500)
            bad = page.evaluate(MATHS)
            check(f"{tag} display maths fit without scrolling", not bad, "; ".join(bad[:3]))
            notice = page.evaluate(NOTICE)
            check(f"{tag} AI notice shown", args.notice in notice, f"no front-matter line containing {args.notice!r}")
            if args.shots:
                page.screenshot(path=str(args.shots / f"top-{tag}.png"))
            context.close()
        # The PDF view's strip: the paper's name, the Text and PDF toggle and the step controls never
        # overlap, at a laptop's width and in narrower windows.
        for width, height in (() if args.no_pdf else ((1440, 900), (1000, 800), (800, 700))):
            tag = f"{width}x{height} pdf"
            context = browser.new_context(viewport={"width": width, "height": height})
            page = context.new_page()
            page.goto(base + "?view=pdf&page=1")
            page.wait_for_selector(".pdf-view" if args.pdf_only else ".paper .tie, .reader-strip .view-toggle", timeout=60000)
            page.wait_for_timeout(1500)
            if args.pdf_only:
                check(f"{tag} no text toggle", not page.locator(".view-toggle").count(), "a Text | PDF toggle on a PDF-only paper")
            elif not page.locator(".reader-strip .view-toggle").count():
                # A main document with no PDF has no toggle and no PDF view to check.
                report[f"{tag} strip"] = {"ok": True, "detail": "no PDF: no Text | PDF toggle"}
                context.close()
                continue
            page.wait_for_timeout(1500)
            clash = page.evaluate("""() => {
                const els = [...document.querySelectorAll('.reader-strip .crumbs li, .reader-strip .reader-strip__hint, .reader-strip .view-toggle, .reader-strip > button, .reader-strip .reader-strip__steps, .reader-strip .sections-toggle')]
                  .filter(e => e.offsetParent && e.getBoundingClientRect().width > 1);
                const out = [];
                for (let i = 0; i < els.length; i++) for (let j = i + 1; j < els.length; j++) {
                  const a = els[i], b = els[j];
                  if (a.contains(b) || b.contains(a)) continue;
                  const r = a.getBoundingClientRect(), q = b.getBoundingClientRect();
                  if (r.left < q.right - 1 && q.left < r.right - 1 && r.top < q.bottom - 1 && q.top < r.bottom - 1)
                    out.push([a.className || a.textContent.slice(0, 20), b.className || b.textContent.slice(0, 20)]);
                }
                return out;
            }""")
            check(f"{tag} strip", not clash, f"overlapping: {clash[:3]}")
            if args.shots:
                page.screenshot(path=str(args.shots / f"pdf-strip-{width}x{height}.png"))
            context.close()
        if not args.pdf_only:
            selection_checks(browser, base, args, check)
            underline_checks(browser, base, args, check)
            step_checks(browser, base, check)
        # Each companion named opens its own text with its phrases, from its own edition, never the
        # edition error; a phrase address on one also opens that phrase's card.
        for width, height in SIZES:
            tag = f"{width}x{height}"
            context = browser.new_context(viewport={"width": width, "height": height})
            page = context.new_page()
            for address in args.companion:
                page.goto(base + (address if "/@" in address else address.rstrip("/") + "/"), wait_until="domcontentloaded")
                try:
                    page.wait_for_selector(".paper .tie[data-tone]", timeout=45000)
                    if "/@" in address:
                        page.wait_for_selector(".phrase-card", timeout=15000)
                except Exception:
                    pass
                body = page.inner_text("body")
                ties = page.eval_on_selector_all(".paper .tie[data-tone]", "els => els.length")
                card = page.evaluate("() => (document.querySelector('.phrase-card') || {}).textContent || ''") if "/@" in address else "-"
                check(f"{tag} companion {address}", ties > 0 and "different edition" not in body and bool(card.strip()),
                      f"{ties} phrases; edition error={'different edition' in body}; card={card[:60]!r}")
            context.close()
        browser.close()
    print(json.dumps(report, indent=1))
    if failures:
        print("\n".join(failures), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
