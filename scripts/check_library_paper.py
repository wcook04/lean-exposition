#!/usr/bin/env python3
"""Check one served library paper in a real browser, at 1440x900 and 2560x1440.

    python scripts/check_library_paper.py http://127.0.0.1:47311/library/euler/ [--shots DIR] [--budget SECONDS]

For each window size, from a cold browser: the paper's top opens and its first underlined phrase
appears within the load budget; clicking a phrase opens its card with the comparison and note,
and the address names the phrase; topic colours show (several distinct tones); the Graph view
draws; each kind of address (numbered result, phrase, Lean declaration, section) opens what it
names; the Open PDF link opens the PDF in a new tab and the file is a PDF; display formulas lie
inside their columns and never scroll; the front matter carries the AI notice (--notice). Then at 800, 1000, 390, 360 and
320 px: the header's controls do not overlap and Search and Menu stay inside the window.
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
            page.wait_for_selector(".paper .tie[data-tone]", timeout=60000)
            first = time.monotonic() - start
            page.wait_for_load_state("networkidle")
            check(f"{tag} load", first <= args.budget, f"first underlined phrase after {first:.2f}s (budget {args.budget}s)")
            page.wait_for_timeout(1500)
            bad = page.evaluate(MATHS)
            check(f"{tag} display maths fit without scrolling", not bad, "; ".join(bad[:3]))
            check(f"{tag} AI notice shown", args.notice in page.evaluate(NOTICE), f"no front-matter line containing {args.notice!r}")
            # The front matter says each sentence once, and says once that the links were made with AI.
            line = page.evaluate("() => document.querySelector('.account-line')?.textContent ?? ''")
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
            tie = page.locator(".paper .tie[data-tone]").nth(1)
            tie.scroll_into_view_if_needed()
            # A phrase that wraps over lines has a bounding box whose centre can fall between its
            # lines; click its first line, where a reader would.
            first = tie.evaluate("e => { const r = e.getClientRects()[0]; return {x: r.left + Math.min(8, r.width / 2), y: r.top + r.height / 2}; }")
            page.mouse.click(first["x"], first["y"])
            page.wait_for_function("() => /\\/@|[?&]n=/.test(location.href)", timeout=15000)
            card = page.locator(".phrase-card").first
            card.wait_for(timeout=15000)
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
            # Four or more neighbours are drawn; fewer are named in one line over the Lean, with no canvas.
            page.wait_for_selector(".map-pane__graphview .fg[data-cards], .map-pane__few", timeout=15000)
            few = page.get_attribute(".map-pane__few", "data-neighbours") if page.locator(".map-pane__few").count() else None
            nodes = int(page.get_attribute(".map-pane__graphview .fg[data-cards]", "data-cards") or 0) if few is None else 0
            check(f"{tag} graph view", nodes > 0 or few is not None, f"{nodes} cards drawn" if few is None else f"{few} neighbours, named without a drawing")
            if args.shots:
                page.screenshot(path=str(args.shots / f"phrase-{tag}.png"))
            # Each kind of address.
            for kind, path, expect in (
                *((("result", f"{args.result}/", "Theorem"),) if args.result else ()),
                ("phrase", f"@{args.phrase}", "AI-assessed"),
                ("lean", f"lean/{args.decl}", args.decl.rsplit(".", 1)[-1]),
            ):
                page.goto(base + path)
                page.wait_for_selector(".paper .tie", timeout=60000)
                page.wait_for_timeout(2000)
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
            if args.result:
                check(f"{tag} result lands on its statement", place["label"] is not None and 0 <= place["label"] <= height
                      and (place["pin"] is None or place["pin"] >= place["label"] - 2), f"{title}: {place}")
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
        context = browser.new_context(viewport={"width": 1440, "height": 900})
        context.route(re.compile(r".*/assets/MapPane-[^/]*\.js$"), lambda route: route.fulfill(status=200, content_type="text/javascript", body="throw new Error('injected map pane failure');"))
        page = context.new_page()
        page.goto(base + f"@{args.phrase}?v=graph")
        page.wait_for_selector(".paper .tie[data-tone]", timeout=60000)
        try:
            page.wait_for_selector(".graph-boundary", timeout=15000)
            contained = True
        except Exception:
            contained = False
        kept = page.locator(".paper .tie").count() > 0 and not page.locator(".page-guard").count()
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
            page.wait_for_selector(".paper .tie[data-tone]", timeout=60000)
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
        for width, height in ((1440, 900), (1000, 800), (800, 700)):
            tag = f"{width}x{height} pdf"
            context = browser.new_context(viewport={"width": width, "height": height})
            page = context.new_page()
            page.goto(base + "?view=pdf&page=1")
            page.wait_for_selector(".paper .tie, .reader-strip .view-toggle", timeout=60000)
            page.wait_for_timeout(1500)
            if not page.locator(".reader-strip .view-toggle").count():
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
