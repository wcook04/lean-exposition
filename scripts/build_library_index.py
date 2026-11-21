#!/usr/bin/env python3
"""Write the library's one home page, its catalog and its search data.

Usage: build_library_index.py OUT [PAPER...]
OUT is the published library (a checkout of wcook04/library, or a folder served as /library/).
It receives index.html, 404.html, catalog.json and _index/ (the page's stylesheet, script, fonts
and one search file per published paper). With PAPER names, only those library papers are
listed as read here (the ones published); without, every instance.

What the page lists, in order, is scripts/build_library_index_assets/papers.json: the papers
built here from instances/<paper>/ and the papers still on their current sites. A library
paper's title, authors, credit and pages come from its instance.json and its counts and search
data from its published edition under OUT/<paper>/edition/. The header, type and colours are
the reader's own: the tokens (site/src/styles/tokens.css) and the family lockup
(site/src/styles/family.css) are read from the engine, and the fonts are copied from a
published paper's assets. The page loads nothing from another host.
"""
from __future__ import annotations

import html
import json
import re
import shutil
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ASSETS = ROOT / "scripts" / "build_library_index_assets"
BASE = "/library/"
SITE_URL = "https://wcook04.github.io/library/"
ROLE_STATES = {"statement", "states"}

# The reader's fonts, as the published papers ship them (fontsource subsets, hashed by Vite).
# Unicode ranges are fontsource's, so a page that prints no Greek never downloads the Greek face.
LATIN = "U+0000-00FF,U+0131,U+0152-0153,U+02BB-02BC,U+02C6,U+02DA,U+02DC,U+0304,U+0308,U+0329,U+2000-206F,U+20AC,U+2122,U+2191,U+2193,U+2212,U+2215,U+FEFF,U+FFFD"
LATIN_EXT = "U+0100-02BA,U+02BD-02C5,U+02C7-02CC,U+02CE-02D7,U+02DD-02FF,U+0304,U+0308,U+0329,U+1D00-1DBF,U+1E00-1E9F,U+1EF2-1EFF,U+2020,U+20A0-20AB,U+20AD-20C4,U+2113,U+2C60-2C7F,U+A720-A7FF"
GREEK = "U+0370-0377,U+037A-037F,U+0384-038A,U+038C,U+038E-03A1,U+03A3-03FF"
FONTS = [
    # (family, weight, style, file stem, unicode range)
    ("STIX Two Text", "400", "normal", "stix-two-text-latin-400-normal", LATIN),
    ("STIX Two Text", "400", "normal", "stix-two-text-latin-ext-400-normal", LATIN_EXT),
    ("STIX Two Text", "400", "normal", "stix-two-text-greek-400-normal", GREEK),
    ("STIX Two Text", "500", "normal", "stix-two-text-latin-500-normal", LATIN),
    ("STIX Two Text", "500", "normal", "stix-two-text-latin-ext-500-normal", LATIN_EXT),
    ("Source Sans 3 Variable", "200 900", "normal", "source-sans-3-latin-wght-normal", LATIN),
    ("Source Sans 3 Variable", "200 900", "normal", "source-sans-3-latin-ext-wght-normal", LATIN_EXT),
]


def esc(text: str) -> str:
    return html.escape(text, quote=True)


def names(people: list[str]) -> str:
    return people[0] if len(people) < 2 else f"{', '.join(people[:-1])} and {people[-1]}"


def n(value: int) -> str:
    return f"{value:,}"


def plain_tex(text: str) -> str:
    """A passage of the paper as searchable, readable text: no markup, no TeX delimiters."""
    text = re.sub(r"<!--.*?-->", " ", text, flags=re.S)
    text = re.sub(r"<[^>]+>", " ", text)
    text = re.sub(r"\[([^\]]*)\]\([^)]*\)", r"\1", text)
    text = text.replace("**", "").replace("$$", " ").replace("$", "")
    text = re.sub(r"\\(left|right|big|Big|bigl|bigr|Bigl|Bigr|,|;|!|quad|qquad)\b", " ", text)
    text = re.sub(r"\\(mathrm|mathbf|mathcal|mathbb|operatorname|text|textbf|emph|mathit|boldsymbol)\{([^{}]*)\}", r"\2", text)
    text = re.sub(r"\\(begin|end)\{[^}]*\}|\\tag\{[^}]*\}|\\label\{[^}]*\}", " ", text)
    for tex, uni in TEX_SYMBOLS.items():
        text = re.sub(r"\\" + re.escape(tex) + r"(?![A-Za-z])", uni, text)
    text = re.sub(r"\\([A-Za-z]+)", r"\1", text)
    text = re.sub(r"\^\{?([0-9+\-]+)\}?", lambda m: m[1].translate(SUPERSCRIPT), text)
    text = text.replace("{", "").replace("}", "")
    return re.sub(r"\s+", " ", text).strip()


SUPERSCRIPT = str.maketrans("0123456789+-", "⁰¹²³⁴⁵⁶⁷⁸⁹⁺⁻")

TEX_SYMBOLS = {
    "infty": "∞", "in": "∈", "notin": "∉", "le": "≤", "leq": "≤", "ge": "≥", "geq": "≥", "ne": "≠", "neq": "≠",
    "cdot": "·", "times": "×", "to": "→", "mapsto": "↦", "partial": "∂", "nabla": "∇", "sum": "∑", "int": "∫",
    "subseteq": "⊆", "subset": "⊂", "cup": "∪", "cap": "∩", "approx": "≈", "sim": "∼", "lesssim": "≲", "gtrsim": "≳",
    "alpha": "α", "beta": "β", "gamma": "γ", "delta": "δ", "epsilon": "ε", "varepsilon": "ε", "zeta": "ζ", "eta": "η",
    "theta": "θ", "kappa": "κ", "lambda": "λ", "mu": "μ", "nu": "ν", "xi": "ξ", "pi": "π", "rho": "ρ", "sigma": "σ",
    "tau": "τ", "phi": "φ", "varphi": "φ", "chi": "χ", "psi": "ψ", "omega": "ω", "Gamma": "Γ", "Delta": "Δ",
    "Theta": "Θ", "Lambda": "Λ", "Sigma": "Σ", "Phi": "Φ", "Psi": "Ψ", "Omega": "Ω", "langle": "⟨", "rangle": "⟩",
    "ldots": "…", "dots": "…", "cdots": "⋯", "pm": "±", "mid": "|", "|": "‖", "quad": " ", "qquad": " ",
}


# ---------------------------------------------------------------------------- library papers

def edition_files(out: Path, paper: str) -> dict:
    root = out / paper / "edition"
    index = root / "index.json"
    return json.loads(index.read_text()) if index.exists() else {}


def library_facts(out: Path, inst: dict) -> tuple[dict, dict]:
    """Counts and search rows for one published library paper, from its edition."""
    paper = inst["id"]
    root = out / paper / "edition"
    index = edition_files(out, paper)
    base = f"{BASE}{paper}"
    phrases = statements = 0
    lean: set[str] = set()
    rows_statements: list[list[str]] = []
    slot_slug = {d["slot"]: d.get("slug", "") for d in inst["documents"]}
    bodies: dict[str, bytes] = {}
    for doc in inst["documents"]:
        doc_file = index.get("documents", {}).get(doc["slot"])
        bodies[doc["slot"]] = (root / doc_file).read_bytes() if doc_file and (root / doc_file).exists() else b""
    for doc in inst["documents"]:
        ties_path = root / "ties" / f"{doc['slot']}.json"
        if not ties_path.exists():
            continue
        ties = json.loads(ties_path.read_text()).get("ties", [])
        body = bodies[doc["slot"]]
        seen: set[str] = set()
        for tie in ties:
            pid = tie.get("phrase")
            if pid in seen:
                continue
            seen.add(pid)
            phrases += 1
            for row in tie.get("rows") or []:
                if row.get("name"):
                    lean.add(row["name"])
            if tie.get("name"):
                lean.add(tie["name"])
            if tie.get("role") in ROLE_STATES:
                statements += 1
                at = re.match(r"b(\d+)-(\d+)$", tie.get("at", ""))
                text = plain_tex(body[int(at[1]):int(at[2])].decode("utf8", "replace")) if at and body else ""
                if text:
                    page = f"/{slot_slug[doc['slot']]}" if slot_slug.get(doc["slot"]) else ""
                    rows_statements.append([tie.get("plain") or "", text, f"{base}{page}/@{pid}"])
    # Each numbered result once, in the authors' numbering, before the phrases.
    results: list[list[str]] = []
    core = root / "alignment" / "core.json"
    plain_titles: dict[str, str] = {}
    if core.exists():
        core_data = json.loads(core.read_text())
        plain_titles = core_data.get("names", {}) or {}
        # A paper that moved in from its own reader keeps its records' ids; its numbered results are
        # the records alignment/results.json names, at their addresses.
        named = ROOT / "instances" / paper / "alignment" / "results.json"
        by_record = {}
        if named.exists():
            by_record = {row["record"]: address for address, row in json.loads(named.read_text())["results"].items() if row.get("record")}
        for rid, record in core_data.get("records", {}).items():
            if by_record and rid not in by_record:
                continue
            slug = by_record.get(rid) or (rid.split(".", 1)[1] if "." in rid else rid)
            # The excerpt is the result's canonical target, its statement block: a "statement" slice
            # first, then a "definition", and only then another non-mention. An introduction before
            # the result is never offered as the result's words.
            stated = [s for s in record.get("statements", []) if s.get("role") != "mention"]
            rank = {"statement": 0, "definition": 1}
            first = min(stated, key=lambda s: (rank.get(s.get("role"), 2), s.get("start_byte", 0)), default=None)
            if first:
                body = bodies.get(first.get("paper", ""), b"")
                text = first.get("markdown") or (body[first["start_byte"]:first["end_byte"]].decode("utf8", "replace")
                                                 if body and "start_byte" in first else "")
                results.append([record.get("short", slug), plain_tex(text), f"{base}/{slug}/"])
    rows_lean: list[list[str]] = []
    names_path = root / "lean" / "names.json"
    if names_path.exists():
        for row in json.loads(names_path.read_text()).get("names", []):
            name = row[0]
            rows_lean.append([name, plain_titles.get(name, "")] if plain_titles.get(name) else [name])
    counts = {"phrases": phrases, "statements": statements, "lean": len(lean)}
    search = {"schema": "library-search/1", "paper": paper, "lean_base": f"{base}/lean/", "statements": results + rows_statements, "lean": rows_lean}
    return counts, search


def strip(colours_file: Path, phrases_file: Path | None) -> list[dict]:
    """The paper's topic colours in their stored order, each weighted by its phrases."""
    if not colours_file.exists():
        return []
    data = json.loads(colours_file.read_text())
    weight: dict[str, int] = {}
    if phrases_file and phrases_file.exists():
        for tie in json.loads(phrases_file.read_text()).get("ties", []):
            weight[tie.get("topic")] = weight.get(tie.get("topic"), 0) + 1
    out = []
    for part in data.get("parts", []):
        family_names = {f["id"]: f["name"] for f in part.get("families", [])}
        for topic, row in sorted(part.get("topics", {}).items(), key=lambda kv: kv[1]["index"]):
            out.append({"topic": topic, "family": family_names.get(row["family"], ""), "light": row["light"], "dark": row["dark"],
                        "weight": max(weight.get(topic, 0), 1)})
    return out


def main_slot(inst: dict) -> str:
    return next(d for d in inst["documents"] if d.get("main"))["slot"]


# ---------------------------------------------------------------------------- page

def strip_html(segments: list[dict]) -> str:
    if not segments:
        return ""
    families = []
    for s in segments:
        if s["family"] and s["family"] not in families:
            families.append(s["family"])
    label = "Topic colours of its underlined phrases: " + "; ".join(families) + "."
    cells = "".join(
        f'<i style="flex-grow:{s["weight"]};--c-l:{s["light"]};--c-d:{s["dark"]}" title="{esc(s["family"])}"></i>' for s in segments)
    return f'<div class="strip" role="img" aria-label="{esc(label)}">{cells}</div>'


def counts_sentence(entry: dict) -> str:
    if entry.get("counts_sentence"):
        return entry["counts_sentence"]
    c = entry.get("counts") or {}
    if not c.get("phrases"):
        return ""
    s = f"Links {n(c['phrases'])} phrases to {n(c['lean'])} Lean declarations"
    if c.get("statements"):
        s += f"; {n(c['statements'])} of the phrases state a result"
    return s + "."


def outbound(href: str) -> bool:
    return not href.startswith(BASE)


WORDS = {1: "one", 2: "two", 3: "three", 4: "four", 5: "five", 6: "six", 7: "seven", 8: "eight", 9: "nine"}


def comparator_line(paper: str) -> str | None:
    """One sentence from the paper's Comparator receipt (instances/<paper>/generated/comparator/receipt.json)."""
    path = ROOT / "instances" / paper / "generated/comparator/receipt.json"
    if not path.is_file():
        return None
    r = json.loads(path.read_text())
    accepted = (r.get("accepted") or {}).get("theorem_names") or []
    if not accepted:
        return None
    controls = (1 if r.get("rejected_control") else 0) + len(r.get("other_rejected_controls") or {})
    n = lambda k: WORDS.get(k, str(k))
    line = (f"Comparator accepted the main theorem's Lean against the authors' definitions with {n(len(r.get('kernels') or []))} kernels"
            f" and only the axioms {', '.join(r.get('permitted_axioms') or [])}.")
    if controls:
        line += f" {n(controls).capitalize()} altered statements were rejected."
    return line


def entry_html(entry: dict) -> str:
    href = entry["href"]
    away = outbound(href)
    arrow = '<span class="out" aria-hidden="true">\u2197</span>' if away else ""
    title = f'<h3 class="paper__title"><a href="{esc(href)}">{esc(entry["title"])}{arrow}</a></h3>'
    by = f'<p class="paper__by">By {esc(names(entry["authors"]))}</p>'
    sentence = f'<p class="paper__what">{esc(entry["sentence"])}</p>' if entry.get("sentence") else ""
    pages = entry.get("pages") or []
    pages_html = ""
    if pages:
        links = "".join(f'<li><a href="{esc(p["href"])}">{esc(p["title"])}</a></li>' for p in pages)
        pages_html = f'<div class="paper__pages"><span class="paper__pages-label">{esc(entry.get("pages_label", "Also"))}</span><ul>{links}</ul></div>'
    facts = []
    cs = counts_sentence(entry)
    if cs:
        facts.append(f'<p class="paper__counts">{esc(cs)}</p>')
    if entry.get("comparator"):
        facts.append(f'<p class="paper__comparator">{esc(entry["comparator"])}</p>')
    if entry.get("credit"):
        facts.append(f'<p class="paper__credit">{esc(entry["credit"])}</p>')
    if entry.get("where"):
        facts.append(f'<p class="paper__where">{esc(entry["where"])}</p>')
    meta = f'<div class="paper__meta">{strip_html(entry.get("strip") or [])}{"".join(facts)}</div>'
    return (f'<li class="paper" id="{esc(entry["id"])}"><div class="paper__main">{title}{by}{sentence}{pages_html}</div>{meta}</li>')


LOCKUP = """<span class="fam-lockup">
<a class="fam-lockup__home" href="https://wcook04.github.io/" rel="author" title="All of Will Cook's websites and videos"><img src="{base}_index/plectis.svg" alt="" width="26" height="26"><span class="fam-lockup__owner" translate="no">Will Cook</span></a>
<span class="fam-lockup__rule" aria-hidden="true"></span>
<a class="fam-lockup__site" href="{base}" aria-label="Reading library, front page" aria-current="page"><svg viewBox="0 0 32 32" aria-hidden="true" class="wordmark__mark"><path d="M4 27 L4 5 M4 27 L28 27" fill="none" stroke-width="2" stroke-linecap="round"/><path d="M5 26 C10 22 13 17 16 14 C19 11 22 9 27 6" fill="none" stroke-width="2.6" stroke-linecap="round"/><circle cx="16" cy="14" r="3"/></svg><span class="fam-lockup__name" translate="no">Reading library</span></a>
</span>"""

SCHEME = """<button type="button" class="scheme-toggle" aria-label="Switch to dark colours" data-scheme-toggle>
<svg class="scheme-toggle__moon" viewBox="0 0 16 16" width="16" height="16" aria-hidden="true"><path d="M13.2 10.1A5.6 5.6 0 0 1 5.9 2.8a5.6 5.6 0 1 0 7.3 7.3z" fill="none" stroke="currentColor" stroke-width="1.4" stroke-linejoin="round"/></svg>
<svg class="scheme-toggle__sun" viewBox="0 0 16 16" width="16" height="16" aria-hidden="true"><g fill="none" stroke="currentColor" stroke-width="1.4" stroke-linecap="round"><circle cx="8" cy="8" r="3.2"/><path d="M8 1.5v1.6M8 12.9v1.6M1.5 8h1.6M12.9 8h1.6M3.4 3.4l1.1 1.1M11.5 11.5l1.1 1.1M3.4 12.6l1.1-1.1M11.5 4.5l1.1-1.1"/></g></svg>
</button>"""


def search_scope(papers: list[dict]) -> str:
    """What the library search covers, with its denominators: the papers whose contents are indexed
    (statements and Lean names) and those matched by title, authors and summary only."""
    full = sum(1 for p in papers if p.get("shard"))
    titles = len(papers) - full
    paper = lambda k: f"{k} paper" if k == 1 else f"{k} papers"
    parts = [f"{paper(full)}’ contents indexed (statements and Lean names)" if full != 1 else "1 paper’s contents indexed (statements and Lean names)"]
    if titles:
        parts.append(f"{titles} by title, authors and summary only")
    return "Covers " + ", ".join(parts) + "."


def page_html(entries: list[dict], search_meta: dict, missing: bool, asset_hash: str) -> str:
    items = "\n".join(entry_html(e) for e in entries)
    data = json.dumps(search_meta, ensure_ascii=False).replace("</", "<\\/")
    notice = '<p class="notice">There is no page at this address. These are the papers.</p>' if missing else ""
    count = len(entries)
    scope = search_scope(search_meta["papers"])
    return f"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Reading library</title>
<meta name="description" content="Mathematics papers read beside their Lean proofs: {count} papers, from fluid blow-up to the PCP theorem, each phrase linked to the Lean that states it.">
<meta name="author" content="Will Cook">
<link rel="canonical" href="{SITE_URL}">
<meta name="color-scheme" content="light dark">
<meta name="theme-color" content="#f8f0e2" media="(prefers-color-scheme: light)">
<meta name="theme-color" content="#1c1526" media="(prefers-color-scheme: dark)">
<link rel="icon" href="{BASE}_index/favicon.svg" type="image/svg+xml">
<script>try{{var s=localStorage.getItem("lx-theme");if(s==="light"||s==="dark")document.documentElement.setAttribute("data-theme",s)}}catch(e){{}}</script>
<link rel="preload" href="{BASE}_index/fonts/stix-two-text-latin-400-normal.woff2" as="font" type="font/woff2" crossorigin>
<link rel="preload" href="{BASE}_index/fonts/source-sans-3-latin-wght-normal.woff2" as="font" type="font/woff2" crossorigin>
<link rel="stylesheet" href="{BASE}_index/index.css?v={asset_hash}">
<script type="module" src="{BASE}_index/index.js?v={asset_hash}"></script>
</head>
<body>
<header class="topbar">
<a class="skip-link" href="#main">Skip to content</a>
<div class="topbar__inner">
{LOCKUP.format(base=BASE)}
<div class="topbar__tools">{SCHEME}</div>
</div>
</header>
<main id="main" tabindex="-1">
<section class="intro" aria-labelledby="library-title">
{notice}
<h1 id="library-title">Mathematics papers, read beside their Lean</h1>
<p class="lede">Each phrase that a Lean declaration states is underlined in its paper. Click it and that Lean opens beside the text, with a plain title, a comparison and a reading note.</p>
<form class="search" role="search" action="{BASE}" onsubmit="return false">
<label class="search__label" for="q">Search the papers</label>
<p class="search__scope" id="search-scope">{esc(scope)}</p>
<div class="search__field">
<svg viewBox="0 0 16 16" width="18" height="18" aria-hidden="true"><circle cx="7" cy="7" r="4.6" fill="none" stroke="currentColor" stroke-width="1.5"/><path d="M10.4 10.4 L14 14" stroke="currentColor" stroke-width="1.5" stroke-linecap="round"/></svg>
<input id="q" name="q" type="search" autocomplete="off" spellcheck="false" placeholder="vorticity, Lemma 2.1, Navier–Stokes, theorem11" aria-describedby="search-scope search-status">
<kbd class="kbd" aria-hidden="true">/</kbd>
</div>
<p id="search-status" class="search__status" aria-live="polite"></p>
<div id="search-results" class="results" hidden></div>
</form>
<p class="caveat">The links from the text to the Lean, the plain titles, the reading notes and the comparisons were made with AI. The authors and other mathematicians have not reviewed them.</p>
</section>
<section class="papers" aria-labelledby="papers-title">
<h2 id="papers-title">The papers</h2>
<ol class="paper-list">
{items}
</ol>
</section>
</main>
<footer class="foot">
<p>Hosted by <a href="https://wcook04.github.io/">Will Cook</a>. Each paper is its authors’ work and is credited in full on its own page. The reader is <a href="https://github.com/wcook04/lean-exposition">lean-exposition</a>, under the MIT licence.</p>
</footer>
<script type="application/json" id="library-data">{data}</script>
</body>
</html>
"""


def copy_fonts(out: Path, papers: list[str]) -> None:
    dest = out / "_index" / "fonts"
    dest.mkdir(parents=True, exist_ok=True)
    node = ROOT / "site" / "node_modules"
    for _, _, _, stem, _ in FONTS:
        target = dest / f"{stem}.woff2"
        found = None
        for paper in papers:
            hits = sorted((out / paper / "assets").glob(f"{stem}-*.woff2"))
            if hits:
                found = hits[0]
                break
        if not found:
            for package in ("@fontsource/stix-two-text", "@fontsource-variable/source-sans-3"):
                candidate = node / package / "files" / f"{stem}.woff2"
                if candidate.exists():
                    found = candidate
        if found:
            shutil.copyfile(found, target)
        elif not target.exists():
            print(f"library index: no font file {stem}; the page falls back to its local faces")


def font_css() -> str:
    return "\n".join(
        f'@font-face{{font-family:"{fam}";font-style:{style};font-display:swap;font-weight:{w};'
        f'src:url({BASE}_index/fonts/{stem}.woff2) format("woff2");unicode-range:{rng}}}'
        for fam, w, style, stem, rng in FONTS)


def write_assets(out: Path) -> str:
    target = out / "_index"
    target.mkdir(parents=True, exist_ok=True)
    styles = ROOT / "site" / "src" / "styles"
    css = "\n".join([
        "/* Generated by scripts/build_library_index.py: the reader's tokens and family lockup, then the index's own rules. */",
        font_css(),
        (styles / "tokens.css").read_text(),
        (styles / "base.css").read_text(),
        (styles / "family.css").read_text(),
        (ASSETS / "index.css").read_text(),
    ])
    (target / "index.css").write_text(css)
    js = (ASSETS / "index.js").read_text()
    (target / "index.js").write_text(js)
    for name in ("plectis.svg", "favicon.svg"):
        shutil.copyfile(ROOT / "site" / "public" / name, target / name)
    import hashlib
    return hashlib.sha256((css + js).encode()).hexdigest()[:10]


def main() -> None:
    out = Path(sys.argv[1])
    only = set(sys.argv[2:])
    instances = {}
    for path in sorted((ROOT / "instances").glob("*/instance.json")):
        inst = json.loads(path.read_text())
        if only and inst["id"] not in only:
            continue
        instances[inst["id"]] = inst
    listing = json.loads((ASSETS / "papers.json").read_text())["papers"]
    listed = {p["id"] for p in listing if p.get("library")}
    # A library paper published but not yet in papers.json is listed after the others, without a sentence.
    listing += [{"id": pid, "library": True} for pid in instances if pid not in listed]

    out.mkdir(parents=True, exist_ok=True)
    (out / "_index" / "search").mkdir(parents=True, exist_ok=True)
    entries: list[dict] = []
    shards: dict[str, str] = {}
    titles: list[dict] = []
    for item in listing:
        if item.get("library"):
            inst = instances.get(item["id"])
            if not inst:
                continue
            paper = inst["id"]
            main_doc = next(d for d in inst["documents"] if d.get("main"))
            pages = [{"title": d["title"], "href": f"{BASE}{paper}/{d['slug']}/"} for d in inst["documents"] if not d.get("main") and d.get("slug")]
            pdf = (main_doc.get("pdf") or {}).get("url")
            if pdf:
                pages.append({"title": "The authors’ PDF", "href": pdf})
            counts, search = library_facts(out, inst) if (out / paper / "edition").exists() else ({}, None)
            slot = main_slot(inst)
            alignment = ROOT / "instances" / paper / "alignment"
            entry = {
                "id": paper, "title": inst["title"], "authors": inst["authors"], "href": f"{BASE}{paper}/",
                "sentence": item.get("sentence", ""), "credit": inst.get("companion_credit", ""),
                "counts": counts, "pages": pages, "comparator": item.get("comparator") or comparator_line(paper),
                "strip": strip(alignment / f"colours-{slot}.json", alignment / f"phrases-{slot}.json"),
            }
            if search:
                (out / "_index" / "search" / f"{paper}.json").write_text(json.dumps(search, ensure_ascii=False, separators=(",", ":")))
                shards[paper] = f"{BASE}_index/search/{paper}.json"
        else:
            entry = dict(item)
            if item.get("colours"):
                entry["strip"] = strip(ROOT / item["colours"], ROOT / item["colour_phrases"] if item.get("colour_phrases") else None)
        entries.append(entry)
        titles.append({"id": entry["id"], "title": entry["title"], "authors": names(entry["authors"]), "sentence": entry.get("sentence", ""),
                       "href": entry["href"], "here": not outbound(entry["href"]), "shard": shards.get(entry["id"]),
                       "pages": entry.get("pages", [])})

    asset_hash = write_assets(out)
    copy_fonts(out, list(instances))
    meta = {"papers": titles}
    (out / "index.html").write_text(page_html(entries, meta, False, asset_hash))

    catalog = {"schema": "library-catalog/2", "papers": [
        {"id": e["id"], "title": e["title"], "authors": e["authors"], "href": e["href"], "here": not outbound(e["href"]),
         "sentence": e.get("sentence", ""), "counts": e.get("counts") or {}, "comparator": e.get("comparator"),
         "pages": e.get("pages", []), "search": shards.get(e["id"])}
        for e in entries]}
    (out / "catalog.json").write_text(json.dumps(catalog, indent=1, ensure_ascii=False) + "\n")

    # GitHub Pages answers every missing path with this one file. An address inside a paper
    # (a phrase /@id or a Lean name /lean/<name>) is that paper's reader: load the paper's own
    # shell in place, at the same address. Anything else gets the list of papers.
    ids = json.dumps(sorted(instances))
    boot = (f"<script>(function(){{var ids={ids};var m=location.pathname.match(/^\\/library\\/([a-z0-9-]+)\\//);"
            "if(!m||ids.indexOf(m[1])<0)return;document.documentElement.style.visibility='hidden';"
            "fetch('/library/'+m[1]+'/404.html').then(function(r){return r.ok?r.text():null}).then(function(t){"
            "if(!t){document.documentElement.style.visibility='';return}document.open();document.write(t);document.close();})"
            ".catch(function(){document.documentElement.style.visibility=''});})();</script>")
    missing = page_html(entries, meta, True, asset_hash).replace('<meta name="author"', '<meta name="robots" content="noindex">\n<meta name="author"')
    (out / "404.html").write_text(missing.replace("</head>", boot + "\n</head>"))
    (out / ".nojekyll").write_text("")
    print(f"library index: {len(entries)} paper(s), {len(shards)} read here")


if __name__ == "__main__":
    main()
