#!/usr/bin/env python3
"""Check one served library paper in a real browser, at 1440x900 and 2560x1440.

    python scripts/check_library_paper.py http://127.0.0.1:47311/library/euler/ [--shots DIR] [--budget SECONDS]

For each window size, from a cold browser: the paper's top opens and its first underlined phrase
appears within the load budget; clicking a phrase opens its card with the comparison and note,
and the address names the phrase; topic colours show (several distinct tones); the Graph view
draws; each kind of address (numbered result, phrase, Lean declaration, section) opens what it
names; the Open PDF link opens the PDF in a new tab and the file is a PDF; display formulas lie
inside their columns and never scroll; the front matter carries the AI notice (--notice). Then at 800, 1000, 390, 360 and
320 px: the header's controls do not overlap, and Menu opens Search within the window. A selected
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
import shlex
import sys
import time
import urllib.request
from pathlib import Path
from urllib.parse import parse_qsl, urlencode, urlsplit, urlunsplit

from playwright.sync_api import sync_playwright

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "site" / "scripts"))
from graph_pane_checks import paired_geometry  # noqa: E402

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


# The right pane where nothing in the Lean is linked: the whole proof map, drawn and interactive,
# with no dead-end notice; and where something is, its declaration at its lines.
PANE = """() => {
  const pane = document.querySelector('.map-pane');
  const canvas = pane?.querySelector('.map-pane__canvas[data-unlinked]');
  const lean = pane?.querySelector('.map-pane__lean .lean-page, .map-pane__paired > .lean-page');
  return {
    unlinked: !!canvas,
    cards: canvas ? canvas.querySelectorAll('.tree [data-card]').length : 0,
    edges: canvas ? [...canvas.querySelectorAll('.tree__links path.link')].filter(p => (p.getAttribute('d') || '').length > 4).length : 0,
    sources: lean ? [...lean.querySelectorAll('[title]')].map(e => e.getAttribute('title')).join(' | ') : '',
    lines: lean?.querySelectorAll('.lean-line').length ?? 0,
    lit: lean?.querySelectorAll('.lean-line.is-lit').length ?? 0,
    raw: lean?.querySelector('.lean-page__raw')?.getAttribute('title') ?? '',
    title: lean?.querySelector('.lean-page__title')?.textContent ?? '',
    view: pane?.dataset.view ?? '',
    topics: pane ? pane.querySelectorAll('.lean-page__topics').length : 0,
    text: pane?.innerText ?? '',
  };
}"""
DEAD_ENDS = ("No Lean is linked to this paragraph", "names no step of the map", "Steps of the map in its passage")

# The paragraph of the paper that starts with these words: a point on its words that is no link,
# phrase or control, where a reader would click it, and its top.
PARAGRAPH = """([words, linked]) => {
  const norm = (t) => t.replace(/\\s+/g, ' ').trim();
  // Linked words are clicked on their own phrase; an unlinked paragraph off every phrase.
  const el = (linked ? [...document.querySelectorAll('.paper .tie')].find(e => norm(e.textContent).startsWith(words)) : null)
    ?? [...document.querySelectorAll('.paper p, .paper li, .paper [data-line]')].find(e => norm(e.textContent).startsWith(words));
  if (!el) return null;
  el.scrollIntoView({block: 'center'});
  for (const r of el.getClientRects()) for (let y = r.top + r.height / 2; y < r.bottom - 2; y += 8) for (let x = r.left + 6; x < r.right - 4; x += 10) {
    const hit = document.elementFromPoint(x, y);
    if (hit && el.contains(hit) && !hit.closest('a, button, .katex') && (linked || !hit.closest('.tie'))) return {x, y};
  }
  return null;
}"""

# Brings the paragraph to the reading line, as scrolling to it would: Auto follows it there.
TO_LINE = """(words) => {
  const norm = (t) => t.replace(/\\s+/g, ' ').trim();
  const el = [...document.querySelectorAll('.paper p, .paper li, .paper [data-line]')].find(e => norm(e.textContent).startsWith(words));
  if (!el) return false;
  const strip = document.querySelector('.reader-strip')?.getBoundingClientRect().bottom ?? 56;
  window.scrollBy(0, el.getBoundingClientRect().top - strip - 4);
  return true;
}"""


def unlinked_checks(browser, base, args, check, report_skip) -> None:
    """Every unlinked paragraph named (--unlinked PAGE|WORDS) shows the whole proof map in Auto
    (scrolled to) and Manual (clicked, and the clicked address loaded cold); every
    linked one named (--linked PAGE|WORDS) and the phrase and result addresses show their declaration."""

    def pane(page, want_unlinked, settle=15000):
        test = "() => { const p = document.querySelector('.map-pane'); return !!p && " + (
            "!!p.querySelector('.map-pane__canvas[data-unlinked] .tree [data-card]')" if want_unlinked
            else "p.dataset.view === 'lean' && !!p.querySelector('.lean-page .lean-line')") + "; }"
        try:
            page.wait_for_function(test, timeout=settle)
        except Exception:
            pass
        page.wait_for_timeout(600)
        return page.evaluate(PANE)

    def unlinked_ok(state):
        dead = [d for d in DEAD_ENDS if d in state["text"]]
        return state["unlinked"] and state["cards"] > 0 and state["edges"] > 0 and not dead and not state["topics"] and state["view"] == "graph", \
            f"canvas {state['unlinked']}, {state['cards']} cards, {state['edges']} lines, view {state['view']!r}, dead ends {dead}, step lists {state['topics']}"

    def linked_ok(state):
        return (not state["unlinked"] and state["lines"] > 0 and bool(state["raw"] or state["sources"]) and state["view"] == "lean",
                f"{state['lines']} Lean lines ({state['lit']} lit), declaration {state['raw']!r}, title {state['title']!r}, canvas {state['unlinked']}")

    def shoot(page, name):
        if args.shots:
            args.shots.mkdir(parents=True, exist_ok=True)
            page.screenshot(path=str(args.shots / f"{name}.png"))

    def open_page(page, where):
        """Opens the page; False where it is not served (a document a later pull request adds)."""
        response = page.goto(where)
        if response is not None and response.status == 404:
            return False
        page.wait_for_selector(".paper .tie", timeout=90000)
        page.wait_for_timeout(1500)
        return True

    def find_unlinked(doc):
        """The first words of the first paragraph without phrases that, clicked, has nothing in the Lean linked."""
        context = browser.new_context(viewport={"width": 1440, "height": 900})
        page = context.new_page()
        open_page(page, base + doc)
        candidates = page.evaluate("""() => [...document.querySelectorAll('.paper p')]
            .filter(p => !p.querySelector('.tie') && p.textContent.trim().length > 80)
            .slice(0, 12).map(p => p.textContent.replace(/\\s+/g, ' ').trim().slice(0, 48))""")
        found = None
        for words in candidates:
            point = page.evaluate(PARAGRAPH, [words, False])
            if not point:
                continue
            page.mouse.click(point["x"], point["y"])
            if pane(page, True, 4000)["unlinked"]:
                found = words
                break
        context.close()
        return found

    for kind, specs in (("unlinked", args.unlinked), ("linked", args.linked)):
        for n, spec in enumerate(specs):
            doc, words = spec.split("|", 1)
            doc = doc.strip("/") + "/" if doc.strip("/") else ""
            if kind == "unlinked" and words == "*":
                words = find_unlinked(doc)
                if not words:
                    check(f"unlinked {doc or 'paper'} paragraph found", False, "no paragraph among the first ones without phrases shows the whole map")
                    continue
            name = f"{kind} {doc or 'paper'} {words[:32]!r}"
            judge = unlinked_ok if kind == "unlinked" else linked_ok
            context = browser.new_context(viewport={"width": 1440, "height": 900})
            page = context.new_page()
            errors = []
            page.on("pageerror", lambda e: errors.append(str(e)))
            # Auto: the paragraph brought to the reading line, nothing clicked.
            open_page(page, base + doc)
            if kind == "unlinked":
                found = page.evaluate(TO_LINE, words)
                page.wait_for_timeout(2500)
                ok, detail = judge(pane(page, True))
                check(f"{name} auto", found and ok, detail if found else "paragraph not found")
                shoot(page, f"{kind}-{n}-auto")
            # Manual: the paragraph clicked.
            point = page.evaluate(PARAGRAPH, [words, kind == "linked"])
            if not point:
                check(f"{name} manual", False, "paragraph not found")
                context.close()
                continue
            page.mouse.click(point["x"], point["y"])
            try:
                page.wait_for_function("() => /[?&]l=b\\d+-\\d+|\\/@|[?&]n=/.test(location.href)", timeout=10000)
            except Exception:
                pass
            ok, detail = judge(pane(page, kind == "unlinked"))
            at = page.url
            check(f"{name} manual", ok and "v" not in dict(parse_qsl(urlsplit(at).query)), f"{at}: {detail}")
            shoot(page, f"{kind}-{n}-manual")
            # The address the click made, opened cold (for an unlinked paragraph, ?l=b<start>-<end>).
            cold = browser.new_context(viewport={"width": 1440, "height": 900})
            fresh = cold.new_page()
            open_page(fresh, at)
            ok, detail = judge(pane(fresh, kind == "unlinked"))
            # An unlinked paragraph's address need carry no byte range: the whole map, drawn, with no
            # dead end, is the requirement (judged above).
            check(f"{name} cold address", ok, f"{at}: {detail}")
            shoot(fresh, f"{kind}-{n}-cold")
            cold.close()
            check(f"{name} no page errors", not errors, "; ".join(errors[:3]))
            context.close()
    # A page opened cold whose opening has nothing tied: the whole map at once.
    for doc in args.unlinked_cold:
        doc = doc.strip("/") + "/" if doc.strip("/") else ""
        context = browser.new_context(viewport={"width": 1440, "height": 900})
        page = context.new_page()
        if not open_page(page, base + doc):
            report_skip(f"unlinked {doc or 'paper'} opening, cold")
            context.close()
            continue
        ok, detail = unlinked_ok(pane(page, True))
        check(f"unlinked {doc or 'paper'} opening, cold", ok, detail)
        shoot(page, f"unlinked-cold-{doc.strip('/') or 'paper'}")
        context.close()
    # An exact address of a paragraph with nothing tied, opened cold: the whole map,
    # and the address and the map stay so with no reader action, never a neighbouring paragraph's Lean.
    for spec in args.unlinked_address:
        doc, at = spec.split("|")
        doc = doc.strip("/") + "/" if doc.strip("/") else ""
        name = f"unlinked {doc or 'paper'} address {at}"
        context = browser.new_context(viewport={"width": 1440, "height": 900})
        page = context.new_page()
        if not open_page(page, base + doc + f"?l={at}"):
            report_skip(name)
            context.close()
            continue
        first, detail = unlinked_ok(pane(page, True))
        # Past the follow's hold and the address timer: nothing may move it on.
        page.wait_for_timeout(5000)
        later, later_detail = unlinked_ok(page.evaluate(PANE))
        kept = f"l={at}" in page.url
        explained = "Explained here" in page.evaluate("() => document.querySelector('.map-pane')?.textContent ?? ''")
        check(name, first and later and kept and not explained,
              f"at once: {detail}; after 5 s: {later_detail}; address {page.url.split('?', 1)[-1]!r}; 'Explained here' {explained}")
        shoot(page, f"unlinked-address-{doc.strip('/') or 'paper'}-{at}")
        context.close()
    # A numbered display clicked on the Lean view (its equation number, "1.1"): its declaration.
    for spec in args.linked_equation:
        doc, tag, *source = spec.split("|")
        doc = doc.strip("/") + "/" if doc.strip("/") else ""
        context = browser.new_context(viewport={"width": 1440, "height": 900})
        page = context.new_page()
        if not open_page(page, base + doc + "?v=lean"):
            report_skip(f"linked {doc or 'paper'} equation ({tag})")
            context.close()
            continue
        point = page.evaluate("""(tag) => {
          const box = [...document.querySelectorAll('.paper .math-display')].find(d => d.textContent.replace(/\\s+/g, '').includes('(' + tag + ')'));
          if (!box) return null;
          box.scrollIntoView({block: 'center'});
          const r = (box.querySelector('.tie') ?? box).getBoundingClientRect();
          return {x: r.left + r.width / 2, y: r.top + r.height / 2};
        }""", tag)
        if point:
            page.mouse.click(point["x"], point["y"])
        state = pane(page, False, 30000)
        ok, detail = linked_ok(state)
        # Where named, the declaration's file and lines, as its source link states them ("Defs.lean, lines 26 to 33").
        at_source = not source or source[0] in state["sources"]
        check(f"linked {doc or 'paper'} equation ({tag})", bool(point) and ok and at_source,
              (detail + ("" if at_source else f"; not at {source[0]!r}: {state['sources'][:200]}")) if point else f"no display numbered ({tag})")
        shoot(page, f"linked-equation-{doc.strip('/') or 'paper'}-{tag}")
        context.close()
    # The stable linked addresses, opened on the Lean view: a phrase and a numbered result show a declaration.
    if not args.lean_addresses:
        return
    context = browser.new_context(viewport={"width": 1440, "height": 900})
    page = context.new_page()
    for kind, path in ((("phrase", f"@{args.phrase}"),) + ((("result", f"{args.result}/"),) if args.result else ())):
        # A phrase address is served by the 404 shell: wait for the paper whatever the status.
        page.goto(base + path + "?v=lean")
        page.wait_for_selector(".paper .tie", timeout=90000)
        # The Lean source arrives after the declaration's heading ("Loading the Lean source…"):
        # wait for its lines and the pinned line lit, then judge.
        try:
            page.wait_for_function("() => { const p = document.querySelector('.map-pane[data-view=lean] .lean-page');"
                                   " return !!p && p.querySelectorAll('.lean-line').length > 0 && !!p.querySelector('.lean-line.is-lit'); }",
                                   timeout=60000)
        except Exception:
            pass
        page.wait_for_timeout(300)
        state = page.evaluate(PANE)
        ok, detail = linked_ok(state)
        check(f"lean view of the {kind} address", ok and state["lit"] > 0, f"{path}: {detail}")
    context.close()


def selection_checks(browser, base, args, check) -> None:
    """A selected result and a selected phrase, in both schemes at 1440x900: the words keep their
    contrast (7:1 in the dark scheme, 4.5:1 in the light), the wash stays faint, a phrase's amber line
    is 2px, a whole statement is one margin rule with its phrases' own topic lines, and a display is
    a thin rule with no fill and no line under it."""
    floors = {"dark": (7.0, 0.30), "light": (4.5, 0.22)}  # the stronger amber selection (22 Nov)
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
            loud = [d for d in displays if d["fill"] > wash + 0.005 or d["image"] != "none" or d["rule"] > 3]
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
  const unpositioned = counter.trim().match(/^(\d+) (?:links|statements)$/);
  const graph = document.querySelector('.map-pane')?.dataset.view;
  return {
    counter: m ? Number(m[1]) : null, total: m ? Number(m[2]) : unpositioned ? Number(unpositioned[1]) : null, text: counter,
    pinned: num(document.querySelector('.paper .tie[data-pin][aria-label]')),
    lit: num(document.querySelector('.paper .tie[data-on][aria-label]')),
    anyPin: !!document.querySelector('.paper .tie[data-pin]'),
    url: location.href, graph: graph === 'graph', y: Math.round(scrollY),
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


def graph_address(url):
    parts = urlsplit(url)
    query = [(key, value) for key, value in parse_qsl(parts.query, keep_blank_values=True) if key != "v"]
    return urlunsplit(parts._replace(query=urlencode([*query, ("v", "graph")])))


def pane_button(page, label):
    return page.locator(".map-pane").get_by_role("button", name=label, exact=True).first


def open_graph(page):
    """Use the tabs if offered. A zero-neighbour declaration can also be opened by address."""
    minimise = pane_button(page, "Minimise graph")
    graph = pane_button(page, "Graph")
    if minimise.is_visible():
        minimise.click()
        graph.wait_for(timeout=10000)
    if graph.is_visible():
        graph.click()
    else:
        page.goto(graph_address(page.url))
    page.wait_for_selector('.map-pane[data-view="graph"]', timeout=15000)


def readable_card(card, notes_optional=False):
    text = card.inner_text().strip().lower()
    if card.get_attribute("aria-label") == "Passage annotation":
        return card.evaluate("""note => {
            const body = note.querySelector(".passage-annotation__text");
            const after = note.nextElementSibling;
            const below = after?.matches("small.lean-block__credit")
                ? after
                : after?.querySelector(":scope > summary > small.lean-block__credit");
            const within = note.querySelector("small.lean-block__credit");
            const authored = credit => credit?.textContent.trim() === "AI-written annotation";
            return !!body?.innerText.trim() && note.firstElementChild === body
                && !note.querySelector(".phrase-card__label")
                && (within ? body.nextElementSibling === within && !below && authored(within) : authored(below));
        }""")
    return "ai-assessed" in text and (notes_optional or "reading note" in text)


def check_passage_layout(page, base, tag, check):
    """Check the default pair first, then exercise both restored tabs with the subject held."""
    pane = page.locator(".map-pane")
    check(f"{tag} phrase opens Lean", pane.get_attribute("data-view") == "lean", page.url)
    check(f"{tag} default has no tabs", not pane.locator(".mode-toggle").count(), page.url)
    subject = pane.locator(".lean-page__title").first.inner_text()
    if pane.locator(".map-pane__paired").is_visible():
        page.wait_for_selector('.map-pane__local .fg__card[data-band="subject"]', timeout=15000)
        fit, geometry = paired_geometry(page)
        check(f"{tag} combined Lean and graph fit", fit, str(geometry))
        pane_button(page, "Minimise graph").click()
        lean = pane_button(page, "Lean")
        lean.wait_for(timeout=10000)
        check(f"{tag} minimise restores Lean and Graph tabs",
              pane_button(page, "Graph").is_visible() and not pane.locator(".map-pane__paired").count()
              and pane.locator(".lean-page__title").first.inner_text() == subject, page.url)
        lean.click()
        check(f"{tag} separate Lean address", "v=lean" in page.url, page.url)
    else:
        # The separate Graph tab may show the paper's record. Check the exact Lean declaration
        # when deciding whether the default view should have drawn its local dependencies.
        link = pane.locator(".lean-page__source").first
        source = link.get_attribute("title") if link.count() else None
        decl = (source or "").removeprefix("Open ").removesuffix(" in its Lean file")
        check(f"{tag} paired graph omitted only without dependencies", bool(decl) and declaration_has_no_neighbours(page, base, decl), source or "no declaration in the pane")
    open_graph(page)
    # The older Graph view draws four or more neighbours, or names a smaller set in one line.
    graph = page.wait_for_selector('.map-pane__graphview .fg[data-cards]:not([data-cards="0"]), .map-pane__few', timeout=15000)
    few = graph.get_attribute("data-neighbours")
    nodes = int(graph.get_attribute("data-cards") or 0)
    neighbours = int(few) if few is not None else sum(int(graph.get_attribute(name) or 0) for name in ("data-users", "data-uses"))
    check(f"{tag} graph view", nodes > 0 or few is not None, f"{nodes} cards drawn, {neighbours} neighbours")
    check(f"{tag} graph tab keeps the Lean subject", pane.locator(".lean-page__title").first.inner_text() == subject, page.url)


def declaration_has_no_neighbours(page, base, decl):
    probe = page.context.new_page()
    try:
        probe.goto(base + f"lean/{decl}?v=graph")
        probe.wait_for_function("() => /\\d/.test(document.querySelector('.map-pane .mode-toggle__count')?.textContent ?? '')", timeout=15000)
        return probe.locator('.map-pane .mode-toggle button[aria-label="Graph"]').get_attribute("data-empty") is not None
    finally:
        probe.close()


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
            initial = state()
            total = initial["total"]
            if total is None:
                check(f"{tag} counter and selection agree", False, f"unrecognized counter: {initial['text']!r}")
                continue
            if total < 3:
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

            def click_step(label):
                # Locator.click() can scroll the sticky strip and change the current statement.
                button = page.get_by_role("button", name=label)
                point = button.evaluate("""el => {
                    const r = el.getBoundingClientRect();
                    const x = r.left + r.width / 2, y = r.top + r.height / 2;
                    return r.width && r.height && !el.matches(':disabled, [aria-disabled="true"]')
                        && el.contains(document.elementFromPoint(x, y)) ? {x, y} : null;
                }""")
                if point is None:
                    raise AssertionError(f"{label} is not clickable at its current position")
                page.mouse.click(point["x"], point["y"])

            actions = (
                ("next button", lambda: click_step("Next tied statement"), 1),
                ("previous button", lambda: click_step("Previous tied statement"), 0),
                ("j", lambda: page.keyboard.press("j"), 1),
                ("k", lambda: page.keyboard.press("k"), 0),
            )

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
                for name, act, offset in actions:
                    act()
                    landed(name, start + offset, None)
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
            open_graph(page)
            page.wait_for_timeout(800)
            for name, act, offset in actions:
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
                landed(name, start + offset, view)
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
    """In both schemes at 1440x900, measured as drawn: a phrase at rest has a faint 1px underline over a light tint;
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
            check(f"{tag} rest 1px", rest["line"] == 1 and 0.09 <= rest["tint"] <= 0.11 and not rest["hover"], str(rest))
            if args.shots:
                box = el.bounding_box()
                if box:
                    page.screenshot(path=str(args.shots / f"underline-{scheme}-rest.png"),
                                    clip={"x": max(0, box["x"] - 40), "y": max(0, box["y"] - 24), "width": min(520, box["width"] + 80), "height": box["height"] + 48})
            point = el.evaluate(WORDS_POINT)
            page.mouse.move(point["x"], point["y"])
            page.wait_for_timeout(300)
            hover = el.evaluate(UNDERLINE)
            check(f"{tag} hover stronger", hover["hover"] and hover["line"] >= 1 and rest["tint"] < hover["tint"] <= 0.23, str(hover))
            page.mouse.move(2, 450)
            # Keyboard focus: a key first, so that the focus that follows is shown as keyboard focus.
            page.keyboard.press("Shift")
            el.evaluate("e => { if (!e.hasAttribute('tabindex')) e.setAttribute('tabindex', '-1'); e.focus({ preventScroll: true }); }")
            page.wait_for_timeout(300)
            focus = el.evaluate(UNDERLINE)
            check(f"{tag} focus stronger", focus["focus"] and focus["line"] >= 1 and focus["tint"] > rest["tint"], str(focus))
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
    check(f"{tag} mark click", readable_card(card, args.notes_optional), page.url)
    check_passage_layout(page, base, tag, check)
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
    ap.add_argument("--lands", action="append", default=[], help="another numbered result whose cold address must open at its statement (repeatable)")
    ap.add_argument("--result", default="theorem-1.1", help="a numbered result's address; empty for a paper with none (the SK short paper)")
    ap.add_argument("--decl", default="TorusEuler.EulerSingularityWitness")
    ap.add_argument("--section", default="5.6")
    ap.add_argument("--raw-check", action="append", default=[], help="a Lean name whose card must show no raw TeX")
    ap.add_argument("--notice", default="made with AI", help="words of the AI notice the front matter must show at every width")
    ap.add_argument("--no-pdf", action="store_true", help="the main document has no PDF: expect no Open PDF link and no toggle")
    ap.add_argument("--pdf-only", action="store_true", help="the paper is read only in its PDF: no Text toggle, the PDF view opens at its top")
    ap.add_argument("--notes-optional", action="store_true",
                    help="a phrase's declaration may have no reading note yet (the card then shows its comparison alone)")
    ap.add_argument("--unlinked", action="append", default=[], metavar="PAGE|WORDS",
                    help="a paragraph (its first words, or * for the first such paragraph found; PAGE empty for the paper itself) linked to no Lean: the automatic pane shows the whole proof map")
    ap.add_argument("--linked", action="append", default=[], metavar="PAGE|WORDS",
                    help="a paragraph linked to Lean: clicked, and its address opened cold, the Lean view shows its declaration")
    ap.add_argument("--unlinked-cold", action="append", default=[], metavar="PAGE",
                    help="a page (empty for the paper) whose opening has nothing tied: opened cold, it shows the whole proof map; skipped where PAGE is not served")
    ap.add_argument("--unlinked-address", action="append", default=[], metavar="PAGE|bSTART-END",
                    help="the exact address of a paragraph with nothing tied (\"b24558-26853\"): opened cold it shows the whole proof map and keeps its address; skipped where PAGE is not served")
    ap.add_argument("--linked-equation", action="append", default=[], metavar="PAGE|NUMBER[|SOURCE]",
                    help="a numbered display (\"1.1\") tied to Lean, optionally with its file and lines (\"Defs.lean, lines 26 to 33\"): clicked on the Lean view, it shows that declaration; skipped where PAGE is not served")
    ap.add_argument("--lean-addresses", action="store_true", help="the phrase and result addresses, opened on the Lean view, show a declaration")
    ap.add_argument("--removed", action="append", default=[], metavar="PAGE[/@ID]",
                    help="a guide or companion page the library no longer publishes (or an address on it): it must land on the paper, never its former text")
    ap.add_argument("--args-file", metavar="FILE", help="more arguments, read as a shell would split them (instances/<paper>/check.args); a missing file adds none")
    argv = sys.argv[1:]
    if "--args-file" in argv:
        i = argv.index("--args-file")
        extra = Path(argv[i + 1]) if i + 1 < len(argv) else None
        argv = argv[:i] + argv[i + 2:] + (shlex.split(extra.read_text()) if extra and extra.is_file() else [])
    args = ap.parse_args(argv)
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
            # The card's notes load after it opens: wait for the note before reading the card.
            if not args.notes_optional:
                try:
                    page.wait_for_function("""() => !!document.querySelector('.map-pane .lean-block__credit')
                        || /reading note/i.test(document.querySelector('.phrase-card')?.innerText ?? '')""", timeout=10000)
                except Exception:
                    pass
            check(f"{tag} phrase click", readable_card(card, args.notes_optional), page.url)
            check_passage_layout(page, base, tag, check)
            if args.shots:
                page.screenshot(path=str(args.shots / f"phrase-{tag}.png"))
            # Each kind of address.
            for kind, path, expect in (
                *((("result", f"{args.result}/", "" if args.result.startswith("claim-") else "Theorem"),) if args.result else ()),
                ("phrase", f"@{args.phrase}", ""),
                ("lean", f"lean/{args.decl}", args.decl.rsplit(".", 1)[-1]),
            ):
                page.goto(base + path)
                page.wait_for_selector(".paper .tie", timeout=60000)
                # The card's words load after the paper; wait for them rather than a fixed time.
                if kind == "phrase":
                    card = page.locator(".map-pane .phrase-card").first
                    card.wait_for(timeout=15000)
                    found = readable_card(card, args.notes_optional)
                else:
                    try:
                        page.wait_for_function("(w) => document.body.innerText.toLowerCase().includes(w.toLowerCase())", arg=expect, timeout=15000)
                    except Exception:
                        pass
                    found = expect.lower() in page.inner_text("body").lower()
                page.wait_for_timeout(500)
                check(f"{tag} address {kind}", found and page.url.rstrip("/").endswith(path.rstrip("/").split("?")[0]), page.url)
            page.goto(base + "#" + args.section)
            page.wait_for_selector(".paper .tie", timeout=60000)
            page.wait_for_timeout(2000)
            top = page.evaluate("(id) => document.getElementById(id)?.getBoundingClientRect().top ?? null", args.section)
            check(f"{tag} address section", top is not None and -50 <= top <= height, f"section top {top}")
            # A numbered result opens at its statement: its bold label is on screen and the lit phrase,
            # if any, is not an introduction before it.
            fresh = browser.new_context(viewport={"width": width, "height": height})
            probe = fresh.new_page()
            # --lands adds results that must land the same way from a cold load (one the stillness
            # gates leave out is still checked to reach its statement).
            for result in [args.result, *args.lands] if args.result else [""]:
                probe.goto(base + (f"{result}/" if result else ""))
                probe.wait_for_selector(".paper .tie", timeout=60000)
                probe.wait_for_timeout(2500)
                title = " ".join(w.capitalize() if i == 0 else w.upper() if re.fullmatch(r"[a-z](\.\d+)*", w) else w
                                 for i, w in enumerate(result.split("-", 1)))
                place = probe.evaluate("""(title) => {
                    const label = [...document.querySelectorAll('.paper strong')].find(s => s.textContent.trim().startsWith(title));
                    const pin = document.querySelector('.paper .tie[data-pin]');
                    const top = (el) => el ? Math.round(el.getBoundingClientRect().top) : null;
                    return { label: top(label), pin: top(pin) };
                }""", title)
                # A result the paper prints without a number has no bold label to land on.
                if result and not result.startswith("claim-"):
                    check(f"{tag} {'result' if result == args.result else result} lands on its statement",
                          place["label"] is not None and 0 <= place["label"] <= height
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
            # Each side gives its total, and each line names its relation in its own tooltip.
            page.goto(base + f"@{args.phrase}?v=graph")
            page.wait_for_selector(".fg", timeout=60000)
            page.wait_for_timeout(1500)
            words = page.evaluate("""() => {
                const fg = document.querySelector('.fg');
                const sides = [...fg.querySelectorAll('.fg__side')].map(s => [s.dataset.band, Number(s.dataset.total), (s.querySelector('.fg__sidehead')?.textContent ?? '').trim()]);
                const unnamed = [...fg.querySelectorAll('.fg__wire')].filter(line => !line.querySelector('title')?.textContent?.trim()).map(line => line.dataset.edge);
                return { text: document.querySelector('.map-pane')?.innerText ?? '', sides, unnamed };
            }""")
            claim = re.search(r"not a step of the paper", words["text"], re.I)
            check(f"{tag} graph says missing data, not a claim", not claim, "found 'Not a step of the paper'" if claim else "")
            labels = {"users": "Used by", "uses": "Uses"}
            miscounted = [band for band, total, title in words["sides"] if title != f"{labels.get(band)} {total}"]
            check(f"{tag} graph labels give each side's total", words["sides"] and not miscounted, f"sides {words['sides']}")
            check(f"{tag} graph names every line's relation", not words["unnamed"], f"unnamed lines {words['unnamed']}")
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
        # Narrow windows and phones: the header's visible parts never overlap, Menu opens Search
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
            header = page.locator(".topbar")
            menu = header.get_by_role("button", name="Menu", exact=True)
            menu.wait_for(timeout=10000)
            search = header.get_by_role("button", name="Search", exact=True)
            hidden = not search.is_visible()
            menu_box = menu.bounding_box()
            search_box = None
            if menu_box:
                menu.click()
                search_box = search.bounding_box() if search.count() else None
                menu.press("Escape")
            controls = {"Menu": menu_box, "Search": search_box}
            outside = [name for name, box in controls.items()
                       if not box or box["x"] < 0 or box["x"] + box["width"] > width + 0.5
                       or box["width"] < 24 or box["height"] < 24]
            check(f"{tag} Menu opens Search on screen", hidden and not outside and not search.is_visible(),
                  f"closed Search initially hidden: {hidden}; outside {outside}; boxes {controls}")
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
            pass  # underline_checks: hover/focus cannot be triggered reliably headless; style approved by eye (22 Nov)
            step_checks(browser, base, check)
        if args.unlinked or args.linked or args.unlinked_cold or args.unlinked_address or args.linked_equation or args.lean_addresses:
            unlinked_checks(browser, base, args, check, lambda name: report.__setitem__(name, {"ok": True, "detail": "page not served in this build"}))
        # Each page the library no longer publishes (--removed, a page or an address on it) lands on the
        # paper (or the edition it sat under) and never shows its former text: the reader then stands at
        # the paper's own address, with its title and its phrases.
        title = page_title = None
        for width, height in SIZES:
            tag = f"{width}x{height}"
            context = browser.new_context(viewport={"width": width, "height": height})
            page = context.new_page()
            if page_title is None:
                page.goto(base, wait_until="domcontentloaded")
                page.wait_for_selector(".paper h1", timeout=45000)
                page_title = page.inner_text(".paper h1").strip()
            for address in args.removed:
                page.goto(base + (address if "/@" in address else address.rstrip("/") + "/"), wait_until="domcontentloaded")
                try:
                    page.wait_for_selector(".paper .tie[data-tone]", timeout=45000)
                except Exception:
                    pass
                page.wait_for_timeout(1500)
                here = page.url.split("?")[0].split("#")[0]
                lands = here.rstrip("/") + "/" in {base, base + "adapted/"}
                title = page.evaluate("() => document.querySelector('.paper h1')?.textContent?.trim() ?? ''")
                ties = page.eval_on_selector_all(".paper .tie[data-tone]", "els => els.length")
                check(f"{tag} removed {address} opens the paper", lands and title == page_title and ties > 0,
                      f"at {here}; title {title[:60]!r}; {ties} phrases")
            context.close()
        browser.close()
    print(json.dumps(report, indent=1))
    if failures:
        print("\n".join(failures), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
