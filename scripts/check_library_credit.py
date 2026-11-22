#!/usr/bin/env python3
"""Check a served library paper's reading copy, credit, statement cards, companions and PDF in a browser.

    python scripts/check_library_credit.py BASE --credit-file FILE --statement ID --shots DIR [--companion SLOT ...]

At 1440x900 and 2560x1440: the paper opens and KaTeX renders; the credit line (read from FILE, exactly)
appears exactly once on the paper's page and once on About, and on no companion page; a click on a
numbered statement opens its card with an AI-assessed comparison and its Lean declaration; topic
colours show (several distinct tones); Open PDF opens a new tab on a file served as application/pdf;
the PDF toggle shows the authors' page; each companion opens with phrase ties. Exits 1 on any failure.
"""
from __future__ import annotations

import argparse
import json
import sys
import urllib.request
from pathlib import Path

from playwright.sync_api import sync_playwright

ap = argparse.ArgumentParser()
ap.add_argument("base")
ap.add_argument("--credit-file", type=Path, required=True)
ap.add_argument("--statement", required=True, help="the bold label of a numbered statement, e.g. \"Theorem 1.1.\"")
ap.add_argument("--shots", type=Path, required=True)
ap.add_argument("--section", help="the section that states --statement, opened before the click (e.g. 1.1)")
ap.add_argument("--our-tie", help="a phrase whose card shows our own Lean statement beside the authors'")
ap.add_argument("--companion-phrase", nargs=2, metavar=("PAGE", "ID"), help="a phrase of a companion page: /<page>/@<id> opens its card")
ap.add_argument("--companion-lean", nargs=2, metavar=("PAGE", "NAME"), help="/<page>/lean/<name> opens that Lean card")
ap.add_argument("--moved", nargs=3, metavar=("OLD", "ID", "NEW"), help="a moved page: /<old>/ shows /<new>/, and /<old>/@<id> opens the phrase at /<new>/@<id>")
ap.add_argument("--later-check", nargs=2, metavar=("PAGE", "PASSAGE"), help="a passage that mentions a later check shows it after the passage")
ap.add_argument("--far-phrase", help="words from far down the paper: the browser's find must reach them from the top")
ap.add_argument("--statement-tie", help="a tie id on a numbered statement: its address alone must open its card and Lean")
ap.add_argument("--companion", action="append", default=[])
a = ap.parse_args()
base = a.base.rstrip("/") + "/"
credit = a.credit_file.read_text().strip()
report, failures = {}, []


def check(name, ok, detail=""):
    report[name] = {"ok": bool(ok), "detail": str(detail)[:300]}
    if not ok:
        failures.append(f"{name}: {detail}")


a.shots.mkdir(parents=True, exist_ok=True)
with sync_playwright() as pw:
    browser = pw.chromium.launch()
    for w, h in [(1440, 900), (2560, 1440)]:
        tag = f"{w}x{h}"
        ctx = browser.new_context(viewport={"width": w, "height": h})
        page = ctx.new_page()
        errors = []
        page.on("pageerror", lambda e: errors.append(str(e)))
        page.goto(base, wait_until="domcontentloaded")
        page.wait_for_selector(".paper .tie[data-tone]", timeout=60000)
        page.wait_for_load_state("networkidle")
        katex = page.eval_on_selector_all(".paper .katex", "els => els.length")
        raw = page.evaluate("() => (document.querySelector('.paper').innerText.match(/\\\\(frac|mathbb|partial)\\b/g) || []).length")
        check(f"{tag} katex", katex > 50 and raw == 0, f"{katex} KaTeX formulas, {raw} raw TeX commands in the text")
        body = page.inner_text("body")
        check(f"{tag} credit once on paper", body.count(credit) == 1, f"{body.count(credit)} times")
        check(f"{tag} anthropic sentence once", body.count("thanks Anthropic") == 1, f"{body.count('thanks Anthropic')} times")
        page.screenshot(path=str(a.shots / f"paper-top-{tag}.png"))
        # Find in page reaches text far from where the reader opened, and reveals it typeset.
        if a.far_phrase:
            found = page.evaluate("""(phrase) => {
                const inText = document.querySelector('.paper').textContent.includes(phrase);
                const hit = window.find(phrase, false, false, true);
                const sel = getSelection();
                const node = sel && sel.anchorNode;
                const el = node && (node.nodeType === 1 ? node : node.parentElement);
                if (el) el.scrollIntoView({ block: 'center' });
                return { inText, hit, inPaper: !!(el && el.closest('.paper')), part: el && el.closest('.part') ? Number(el.closest('.part').dataset.part) : null };
            }""", a.far_phrase)
            page.wait_for_timeout(3000)
            typeset = found["part"] is not None and page.evaluate(
                "(i) => !document.querySelector(`.part[data-part=\"${i}\"]`).classList.contains('part--pending')", found["part"])
            check(f"{tag} find in page", found["inText"] and found["hit"] and found["inPaper"] and typeset, f"{found}, typeset after reveal: {typeset}")
        # Topic colours across the whole paper.
        seen = set()
        for k in range(12):
            page.evaluate("(k) => window.scrollTo(0, document.body.scrollHeight * k / 12)", k)
            page.wait_for_timeout(400)
            seen |= set(page.eval_on_selector_all(".paper .tie[data-tone]", "els => els.map(e => getComputedStyle(e).textDecorationColor + '|' + e.dataset.tone)"))
        tones = len({x.split("|")[1] for x in seen})
        check(f"{tag} topic colours", tones >= 6, f"{tones} distinct tones")
        # Open PDF.
        link = page.locator("a", has_text="Open PDF").first
        href, target = link.get_attribute("href"), link.get_attribute("target")
        url = href if href.startswith("http") else base.split("/library/")[0] + href
        with urllib.request.urlopen(url.split("#")[0]) as r:
            check(f"{tag} open pdf", target == "_blank" and r.status == 200 and r.headers.get("Content-Type", "").startswith("application/pdf"),
                  f"{href} target={target} {r.status} {r.headers.get('Content-Type')}")
        # A statement click opens its card, comparison and Lean. The reader renders the text near the
        # reader, so the check opens the paper at the statement's section first.
        page.goto(base + (f"#{a.section}" if a.section else ""), wait_until="domcontentloaded")
        page.wait_for_selector(".paper .tie[data-tone]", timeout=60000)
        el = page.locator(".paper .tie", has_text=a.statement).first
        el.wait_for(timeout=30000)
        el.scroll_into_view_if_needed()
        el.click()
        page.wait_for_selector(".phrase-card", timeout=60000)
        page.wait_for_timeout(2500)
        card = page.locator(".phrase-card").first.inner_text()
        check(f"{tag} statement card", "AI-assessed" in card and ("Lean states" in card or "Lean says" in card or "same" in card.lower()), card[:200])
        page.screenshot(path=str(a.shots / f"statement-card-{tag}.png"))
        page.get_by_role("button", name="Lean", exact=True).first.click()
        page.wait_for_timeout(2500)
        code = page.eval_on_selector_all("pre, .code, .lean-code, code", "els => els.map(e => e.innerText).join('\\n')")
        check(f"{tag} statement lean", "v=lean" in page.url and ("theorem" in code or "def " in code or "structure" in code), page.url)
        page.screenshot(path=str(a.shots / f"statement-lean-{tag}.png"))
        # The statement's phrase address, with no view named, opens the same card and Lean as a click.
        if a.statement_tie:
            page.goto(base + f"@{a.statement_tie}", wait_until="domcontentloaded")
            page.wait_for_selector(".paper .tie[data-tone]", timeout=60000)
            page.wait_for_timeout(4000)
            card = page.evaluate("() => (document.querySelector('.phrase-card') || {}).innerText || ''")
            pane = page.evaluate("() => (document.querySelector('.lean-page') || {}).innerText || ''")
            check(f"{tag} statement address", "AI-assessed" in card and "No Lean linked" not in pane, pane[:160])
            page.screenshot(path=str(a.shots / f"statement-address-{tag}.png"))
        # Click a statement in the text itself.
        page.goto(base, wait_until="domcontentloaded")
        page.wait_for_selector(".paper .tie[data-tone]", timeout=60000)
        tie = page.locator(".paper .tie[data-tone]").nth(3)
        tie.scroll_into_view_if_needed()
        tie.click()
        page.wait_for_selector(".phrase-card", timeout=20000)
        page.wait_for_timeout(1500)
        check(f"{tag} click in text opens card", "AI-assessed" in page.locator(".phrase-card").first.inner_text(), page.url)
        page.screenshot(path=str(a.shots / f"click-{tag}.png"))
        # The graph at Proposition B.14 (route 3): the uses the paper's text states are dashed, keyed, and answer
        # the pointer with their sentence.
        page.goto(base + "proposition-b.14/?v=graph", wait_until="domcontentloaded")
        page.wait_for_selector(".fg__card", timeout=60000)
        page.wait_for_timeout(2500)
        dashed = page.eval_on_selector_all(".fg__edge--paper", "els => els.length")
        key = page.evaluate("() => (document.querySelector('.fg__key') || {}).innerText || ''")
        why = ""
        if page.locator(".fg__edge-hit").count():
            page.locator(".fg__edge-hit").first.dispatch_event("click")
            page.wait_for_timeout(500)
            why = page.evaluate("() => (document.querySelector('.fg__edge-why') || {}).innerText || ''")
        check(f"{tag} paper-logic edges", dashed > 0 and "the paper's proof uses this" in key and "Read it in the paper" in why,
              f"{dashed} dashed; key: {key[:80]}; why: {why[:120]}")
        page.screenshot(path=str(a.shots / f"graph-routes-{tag}.png"))
        # PDF view.
        page.goto(base + "?view=pdf&page=1", wait_until="domcontentloaded")
        page.wait_for_timeout(5000)
        canv = page.eval_on_selector_all("canvas", "els => els.length")
        check(f"{tag} pdf view", canv > 0, f"{canv} canvases")
        page.screenshot(path=str(a.shots / f"pdf-view-{tag}.png"))
        # About.
        page.goto(base + "about/", wait_until="domcontentloaded")
        page.wait_for_timeout(2500)
        about = page.inner_text("body")
        check(f"{tag} about credit once", about.count(credit) == 1, f"{about.count(credit)} times")
        check(f"{tag} about licence", "none stated by the authors; hosted with credit to them, to Anthropic and to their repository" in about, "")
        check(f"{tag} about AI", "AI-assessed" in about and "AI-drafted" in about and "No mathematician has reviewed" in about, "")
        page.screenshot(path=str(a.shots / f"about-{tag}.png"), full_page=True)
        if a.our_tie:
            page.goto(base + f"@{a.our_tie}?v=lean", wait_until="domcontentloaded")
            page.wait_for_selector(".paper .tie[data-tone]", timeout=60000)
            page.wait_for_timeout(4000)
            ours = page.evaluate("() => [...document.querySelectorAll('.ours')].map(e => e.innerText).join(' | ')")
            check(f"{tag} our statement", "Our statement, proved from the authors' Lean library" in ours and "Not the authors' Lean" in ours, ours[:200])
            badge = page.evaluate("() => [...document.querySelectorAll('.ours__checked a')].map(e => e.href)")
            check(f"{tag} our statement's Comparator badge", "pending" not in ours and any("/actions/runs/" in h for h in badge), badge)
            page.screenshot(path=str(a.shots / f"ours-{tag}.png"))
        if a.companion_phrase:
            cp, cid = a.companion_phrase
            page.goto(base + f"{cp}/@{cid}", wait_until="domcontentloaded")
            page.wait_for_selector(".paper .tie[data-tone]", timeout=60000)
            page.wait_for_timeout(4000)
            card = page.evaluate("() => (document.querySelector('.phrase-card') || {}).innerText || ''")
            check(f"{tag} companion phrase address", "AI-assessed" in card or "Topic" in card, f"{page.url} {card[:120]}")
            page.screenshot(path=str(a.shots / f"companion-phrase-{tag}.png"))
        if a.companion_lean:
            cp, name = a.companion_lean
            page.goto(base + f"{cp}/lean/{name}", wait_until="domcontentloaded")
            page.wait_for_selector(".paper", timeout=60000)
            page.wait_for_timeout(5000)
            pane = page.evaluate("() => (document.querySelector('.lean-page') || {}).innerText || ''")
            short = name.rsplit(".", 1)[-1]
            check(f"{tag} companion lean address", short in pane, f"{page.url} {pane[:120]}")
        if a.moved:
            old, mid, new = a.moved
            page.goto(base + f"{old}/", wait_until="domcontentloaded")
            page.wait_for_selector(".paper .tie[data-tone]", timeout=60000)
            page.wait_for_timeout(1500)
            check(f"{tag} moved page", page.url.split("?")[0].rstrip("/").endswith(f"/{new}"), page.url)
            page.goto(base + f"{old}/@{mid}", wait_until="domcontentloaded")
            page.wait_for_selector(".paper .tie[data-tone]", timeout=60000)
            page.wait_for_timeout(4000)
            card = page.evaluate("() => (document.querySelector('.phrase-card') || {}).innerText || ''")
            check(f"{tag} moved phrase address", page.url.split("?")[0].endswith(f"/{new}/@{mid}") and ("AI-assessed" in card or "Topic" in card),
                  f"{page.url} {card[:120]}")
        if a.later_check:
            cp, anchor = a.later_check
            page.goto(base + f"{cp}/", wait_until="domcontentloaded")
            page.wait_for_selector(".paper .tie[data-tone]", timeout=60000)
            note = page.evaluate("(a) => (document.querySelector(`[data-passage=\"${a}\"] .later-check`) || {}).innerText || ''", anchor)
            check(f"{tag} later check beside its passage", "1,923" in note and "No mathematical statement differs" in note, note[:160])
        for slot in a.companion:
            page.goto(base + f"{slot}/", wait_until="domcontentloaded")
            page.wait_for_selector(".paper .tie[data-tone]", timeout=60000)
            page.wait_for_timeout(1500)
            text = page.inner_text("body")
            n = page.eval_on_selector_all(".paper .tie", "els => els.length")
            wide = page.evaluate("document.documentElement.scrollWidth - innerWidth")
            check(f"{tag} companion {slot}", n > 10 and "thanks Anthropic" not in text and wide <= 1,
                  f"{n} ties; anthropic={'thanks Anthropic' in text}; {wide}px sideways")
            page.screenshot(path=str(a.shots / f"companion-{slot}-{tag}.png"))
        # The whole proof map, as its own page and from the graph pane's button: it draws, with no page error.
        before = len(errors)
        page.goto(base + "map/", wait_until="domcontentloaded")
        page.wait_for_timeout(6000)
        drawn = page.evaluate("() => document.querySelectorAll('canvas, svg, .tree, .map').length")
        check(f"{tag} map page", drawn > 0 and len(errors) == before, f"{drawn} drawn; errors: {errors[before:][:2]}")
        page.screenshot(path=str(a.shots / f"map-{tag}.png"))
        before = len(errors)
        page.goto(base + "theorem-1.1/?v=graph", wait_until="domcontentloaded")
        page.wait_for_selector(".fg__card", timeout=60000)
        whole = page.locator("button", has_text="Whole proof map")
        found = whole.count() > 0
        if found:
            whole.first.click()
            page.wait_for_timeout(5000)
        check(f"{tag} whole proof map", found and len(errors) == before, f"errors: {errors[before:][:2]}")
        page.screenshot(path=str(a.shots / f"whole-map-{tag}.png"))
        check(f"{tag} no page errors", not errors, "; ".join(errors[:3]))
        ctx.close()
    browser.close()
print(json.dumps(report, indent=1))
if failures:
    print("\n".join(failures), file=sys.stderr)
    sys.exit(1)
