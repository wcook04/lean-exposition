#!/usr/bin/env python3
"""Check a served library paper's adapted edition in a real browser.

    python scripts/check_adapted_edition.py http://127.0.0.1:47311/library/euler/ --shots DIR [--credit TEXT]

At 390, 800, 1024, 1100, 1440, 2000 and 2560 px wide: the edition opens with its one-line credit (the
credit's first sentence and that every change is marked) beside a link to the authors' paper, and About
carries the whole credit (the paper's own document.credit, or --credit); the switch "Authors' paper / Adapted edition" stands in the strip, the
page never scrolls sideways, and a change mark opens a Selected change with the authors' text, the
edition's, the kind, the note and the sources. At 1440: every change of the change map shows as a
mark on the page (the page is read top to bottom), "Show changes" lists every change, the switch
keeps the place by paragraph in both directions and says when a paragraph has no counterpart, the
authors' paper carries no change marks, the PDF with changes marked opens and its bars are marks
in the PDF view, and the browser's find reaches the edition's own words far down the page.
Screenshots of the switch, an opened mark, Show changes and the credit go to --shots.
Exits 1 if any check fails.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
import urllib.request
from pathlib import Path
from urllib.parse import urlsplit

from playwright.sync_api import sync_playwright

WIDTHS = [(390, 844), (800, 800), (1024, 800), (1100, 900), (1440, 900), (2000, 1200), (2560, 1440)]

ap = argparse.ArgumentParser()
ap.add_argument("base")
ap.add_argument("--shots", type=Path, required=True)
ap.add_argument("--slug", default="adapted")
ap.add_argument("--slot", default="adapted", help="the edition's document slot")
ap.add_argument("--paper", help="the library paper (default: read from the address, /library/<paper>/)")
ap.add_argument("--credit", help="the edition's credit (default: its document.credit in instances/<paper>/adapted/edition.json)")
ap.add_argument("--far", help="words of the edition far down its page, for find (default: the first words of its last change)")
ap.add_argument("--widths", type=int, nargs="*", help="only these window widths (default: all seven)")
a = ap.parse_args()
if a.widths:
    WIDTHS = [(w, h) for w, h in WIDTHS if w in a.widths]
base = a.base.rstrip("/") + "/"
if not a.credit:
    # The paper's own credit line, as its adapted edition declares it.
    paper = a.paper or base.split("/library/", 1)[1].strip("/")
    a.credit = json.loads((Path(__file__).resolve().parents[1] / "instances" / paper / "adapted/edition.json").read_text())["document"]["credit"]
edition = base + a.slug + "/"
origin = base.split("/library/")[0]
a.shots.mkdir(parents=True, exist_ok=True)
# The edition's slot and page: its document in the paper's instance data.
with urllib.request.urlopen(base + "changes/" + a.slot + ".json") as r:
    changes = json.load(r)
ids = [c["id"] for c in changes["changes"]]
if not a.far:
    import re
    words = re.sub(r"\$[^$]*\$|[*_\[\]]|\([^)]*\)", " ", changes["changes"][-1]["adapted_text"]).split()
    a.far = " ".join(words[:4])
failures, report = [], {}


def check(name, ok, detail=""):
    report[name] = {"ok": bool(ok), "detail": str(detail)[:400]}
    print(("ok   " if ok else "FAIL ") + name + (f": {str(detail)[:200]}" if not ok or detail else ""))
    if not ok:
        failures.append(name)


def settle(page):
    page.wait_for_selector(".paper .part__text [data-line]", state="attached", timeout=60000)
    page.wait_for_load_state("networkidle")
    page.wait_for_timeout(800)


OVERFLOW = "() => Math.max(document.documentElement.scrollWidth, document.body.scrollWidth) - window.innerWidth"
# The paragraph at the reading line (under the top bar and the strip), by its words.
# The reader's reading line: under the top bar and the strip (ReaderPage's readingTop), as the switch reads it.
AT_LINE = """() => { const css = (n) => parseFloat(getComputedStyle(document.documentElement).getPropertyValue(n));
  const strip = document.querySelector('.reader-strip'); const t = (css('--reader-top') || css('--topbar-h') || 56) + (strip ? strip.offsetHeight : 0) + 24;
  const col = document.querySelector('.paper').getBoundingClientRect(); const x = col.left + Math.min(col.width / 2, 200);
  for (let y = t; y < innerHeight; y += 12) { let b = document.elementFromPoint(x, y)?.closest('.part__text [data-line]');
    if (!b) continue; for (let u = b.parentElement.closest('.part__text [data-line]'); u; u = u.parentElement.closest('.part__text [data-line]')) b = u;
    return b.dataset.line + '|' + b.textContent.trim().slice(0, 60); } return ''; }"""
HEAD = """() => [...document.querySelectorAll('.front-credit')]
  .filter(e => e.offsetParent && e.getBoundingClientRect().width > 1).map(e => e.innerText).join(' ')"""
# The reader's one-line edition credit (site.ts editionCreditLine): the credit's first sentence, then this.
first = re.split(r"(?<=[a-z0-9)\]'’][.!?])\s+(?=[A-Z])", a.credit)[0].strip().rstrip(".!?")
short_credit = f"{first}; every change is marked."

with sync_playwright() as pw:
    browser = pw.chromium.launch()
    # A successful status alone can hide a copied 404 shell. The canonical document must
    # keep its opening and authors' link while the app's modules are still unavailable.
    with browser.new_context() as first_paint:
        first_paint.route("**/*.js", lambda route: route.abort())
        opening = first_paint.new_page()
        response = opening.goto(edition, wait_until="domcontentloaded")
        check("adapted first screen is a real document", response is not None and response.ok
              and opening.locator(".paper .part__text").count() > 0 and "Page not found" not in opening.title())
        check("adapted first screen links to the authors' paper",
              opening.get_by_role("link", name="Read the authors’ paper").count() == 1)
        canonical = opening.locator('link[rel="canonical"]')
        href = canonical.get_attribute("href") if canonical.count() == 1 else None
        check("the adapted edition has its own canonical address",
              urlsplit(href or "").path == urlsplit(edition).path)
    for w, h in WIDTHS:
        tag = f"{w}"
        ctx = browser.new_context(viewport={"width": w, "height": h})
        page = ctx.new_page()
        errors: list[str] = []
        page.on("pageerror", lambda e: errors.append(str(e)))
        page.goto(edition, wait_until="domcontentloaded")
        settle(page)
        head = page.evaluate(HEAD).replace("\u2019", "'")
        # The front matter says the edition's credit in one line (its first sentence, and that every
        # change is marked), in place of the credit note; About carries the whole credit.
        check(f"{tag} the edition's one-line credit in the front matter", short_credit in head, head[:300])
        check(f"{tag} link to the authors' paper beside it", page.locator("a", has_text="Read the authors’ paper").count() >= 1)
        switch = page.locator(".edition-switch")
        check(f"{tag} switch in the strip", switch.count() == 1 and switch.locator("button[aria-pressed=true]").inner_text() == "Adapted edition",
              switch.inner_text() if switch.count() else "absent")
        check(f"{tag} no sideways scroll at the top", page.evaluate(OVERFLOW) <= 0, page.evaluate(OVERFLOW))
        page.screenshot(path=str(a.shots / f"credit-switch-{tag}.png"))
        # A marked paragraph, opened.
        page.goto(edition + "#1.1", wait_until="domcontentloaded")
        settle(page)
        mark = page.locator("[data-change-open]").first
        mark.wait_for(timeout=30000)
        mark.scroll_into_view_if_needed()
        page.wait_for_timeout(300)
        cid = mark.get_attribute("data-change-open")
        check(f"{tag} no sideways scroll beside a mark", page.evaluate(OVERFLOW) <= 0, page.evaluate(OVERFLOW))
        mark.click()
        card = page.locator(".change-card")
        card.wait_for(timeout=15000)
        text = card.inner_text()
        row = next(c for c in changes["changes"] if c["id"] == cid)
        check(f"{tag} opened mark shows both texts, kind, note, sources",
              "In the authors’ paper" in text and "In the adapted edition" in text and row["note"].split("$")[0][:40] in text
              and "Kind" in text and ("Source" in text) and cid in text, text[:300])
        check(f"{tag} no sideways scroll with the change open", page.evaluate(OVERFLOW) <= 0, page.evaluate(OVERFLOW))
        page.screenshot(path=str(a.shots / f"mark-opened-{tag}.png"))
        check(f"{tag} no page errors", not errors, errors[:3])
        if w != 1440:
            ctx.close()
            continue

        # About carries the edition's whole credit, verbatim.
        page.goto(base + "about/", wait_until="domcontentloaded")
        settle(page)
        about = page.evaluate("() => document.getElementById('about-adapted')?.closest('section')?.innerText ?? ''").replace("\u2019", "'")
        check("1440 About carries the credit verbatim", a.credit in about, about[:300])

        # Every change shows as a mark: read the page top to bottom.
        page.goto(edition, wait_until="domcontentloaded")
        settle(page)
        seen, height, y = set(), page.evaluate("document.body.scrollHeight"), 0
        while y < height:
            page.evaluate("(y) => window.scrollTo(0, y)", y)
            page.wait_for_timeout(120)
            seen |= set(page.eval_on_selector_all("[data-change-open]", "els => els.map(e => e.dataset.changeOpen)"))
            y += 700
            height = page.evaluate("document.body.scrollHeight")
        # The credit note's paragraph gives way to the one-line credit in the front matter (engine.ts), so
        # the edition-credit change is said by that line rather than by a mark.
        credit_ids = {c["id"] for c in changes["changes"] if c["kind"] == "edition-credit"}
        check("1440 every change is a visible mark", set(ids) - credit_ids <= seen, sorted(set(ids) - credit_ids - seen))
        check("1440 no mark without a change", seen <= set(ids), sorted(seen - set(ids)))
        # Show changes lists every change.
        page.goto(edition, wait_until="domcontentloaded")
        settle(page)
        page.get_by_role("button", name="Show changes").click()
        page.locator(".change-list").wait_for(timeout=15000)
        rows = page.locator(".change-list__row").count()
        check("1440 Show changes lists every change", rows == len(ids), f"{rows} rows for {len(ids)} changes")
        page.screenshot(path=str(a.shots / "show-changes-1440.png"))
        page.locator(".change-list__row").nth(20).click()
        page.locator(".change-card").wait_for(timeout=15000)
        page.wait_for_timeout(1500)
        want = next(c for c in changes["changes"] if c["id"] == ids[20])
        landed = page.evaluate(AT_LINE)
        check("1440 a listed change opens its passage", landed.split("|")[0] == str(want["adapted_lines"][0][0]),
              f"landed on {landed!r}, wanted {ids[20]} at line {want['adapted_lines'][0][0]}")

        # The switch keeps the place by paragraph: an unchanged paragraph, there and back.
        # From a changed paragraph (opened from the list), to the authors' paragraph it replaces and back.
        page.locator(".change-card button", has_text="Close").click()
        page.wait_for_timeout(500)
        before = page.evaluate(AT_LINE)
        page.locator(".edition-switch button", has_text="Authors’ paper").click()
        page.wait_for_url(lambda u: "/adapted/" not in u, timeout=15000)
        settle(page)
        page.wait_for_timeout(1500)
        after = page.evaluate(AT_LINE)
        check("1440 switch to the authors' paper keeps the paragraph", after.split("|")[0] == str(want["authors_lines"][0][0]),
              f"{before!r} -> {after!r}, wanted line {want['authors_lines'][0][0]}")
        check("1440 the authors' paper carries no change marks", page.locator("[data-change], [data-change-open]").count() == 0)
        authors_head = page.evaluate(HEAD).replace("\u2019", "'")
        check("1440 the authors' paper keeps its own credit", short_credit not in authors_head and a.credit not in authors_head
              and "Paper and Lean by" in authors_head, authors_head[:300])
        page.screenshot(path=str(a.shots / "switched-to-authors-1440.png"))
        page.locator(".edition-switch button", has_text="Adapted edition").click()
        page.wait_for_url(lambda u: "/adapted/" in u, timeout=15000)
        settle(page)
        page.wait_for_timeout(1500)
        back = page.evaluate(AT_LINE)
        check("1440 switch back keeps the paragraph", back.split("|")[0] == before.split("|")[0], f"{before!r} -> {back!r}")
        # A paragraph the edition adds has no counterpart: the switch says so.
        added = next(c for c in changes["changes"] if not c["replaced"] and not c.get("text_unchanged") and c["kind"] != "edition-credit")
        page.goto(edition, wait_until="domcontentloaded")
        settle(page)
        page.get_by_role("button", name="Show changes").click()
        page.locator(".change-list__row").nth(ids.index(added["id"])).click()
        page.wait_for_timeout(2500)
        page.locator(".change-card button", has_text="Close").click()
        page.wait_for_timeout(300)
        at_added = page.evaluate(AT_LINE)
        page.locator(".edition-switch button", has_text="Authors’ paper").click()
        page.wait_for_url(lambda u: "/adapted/" not in u, timeout=15000)
        settle(page)
        page.wait_for_timeout(800)
        notice = page.locator(".reader-notice").all_inner_texts()
        check("1440 an added paragraph says it has no counterpart", any("no counterpart in the authors’ paper" in n for n in notice), f"{notice} from {at_added!r}, the change at {added['adapted_lines']}")
        # Find in page reaches the edition's words far down.
        page.goto(edition, wait_until="domcontentloaded")
        settle(page)
        found = page.evaluate("""(phrase) => { const inText = document.querySelector('.paper').textContent.includes(phrase);
          const hit = window.find(phrase, false, false, true); return { inText, hit }; }""", a.far)
        check("1440 find in page reaches the edition's own words", found["inText"] and found["hit"], found)

        # In a paper with figures, the PDF has only a page for many text blocks.
        # A round trip on that page must restore the original block and its offset.
        page.goto(edition, wait_until="domcontentloaded")
        settle(page)
        figure = page.locator(".paper figure").first
        if figure.count():
            center = "el => el.scrollIntoView({block:'center', behavior:'instant'})"
            figure.evaluate(center)
            figure.locator("img").first.wait_for(state="visible", timeout=15000)
            figure.evaluate(center)
            page.wait_for_timeout(1600)
            before_line = page.evaluate(AT_LINE)
            before_y = figure.bounding_box()["y"]
            depth = page.evaluate("history.length")
            # Locator.click() can scroll the paper to center a sticky button before
            # dispatching input. A reader clicks where the button already is.
            def click_view(name):
                box = page.get_by_role("button", name=name, exact=True).bounding_box()
                page.mouse.click(box["x"] + box["width"] / 2, box["y"] + box["height"] / 2)

            click_view("PDF")
            page.locator(".pdf-view__page canvas").first.wait_for(state="attached", timeout=60000)
            click_view("Text")
            page.wait_for_timeout(1200)
            after_line = page.evaluate(AT_LINE)
            after_y = figure.bounding_box()["y"]
            check("1440 PDF round trip keeps the paragraph and figure in place",
                  before_line == after_line and abs(before_y - after_y) < 5,
                  f"{before_line!r} at {before_y:.1f} -> {after_line!r} at {after_y:.1f}")
            check("1440 PDF round trip uses the same history entry", page.evaluate("history.length") == depth)

        # The PDF with changes marked: its link, the file, and its bars as marks in the PDF view.
        link = page.locator("a.pdf-link", has_text="PDF with changes marked").first
        href = link.get_attribute("href")
        with urllib.request.urlopen(origin + href.split("#")[0] if href.startswith("/") else href.split("#")[0]) as r:
            check("1440 PDF with changes marked is served", r.status == 200 and r.headers.get("Content-Type", "").startswith("application/pdf")
                  and link.get_attribute("target") == "_blank", href)
        page.goto(edition + "?view=pdf&page=2", wait_until="domcontentloaded")
        page.wait_for_selector(".pdf-view__page", timeout=60000)
        page.wait_for_timeout(3000)
        bars = page.locator(".pdf-view__change").count()
        check("1440 change bars are marks in the PDF view", bars >= len(ids) - 6, f"{bars} bar marks")
        page.locator(".pdf-view__change").first.click()
        page.locator(".change-card").wait_for(timeout=15000)
        page.screenshot(path=str(a.shots / "pdf-change-1440.png"))
        ctx.close()
    browser.close()

(a.shots / "report.json").write_text(json.dumps(report, indent=1, ensure_ascii=False))
print(f"{len(report) - len(failures)} of {len(report)} checks passed")
sys.exit(1 if failures else 0)
