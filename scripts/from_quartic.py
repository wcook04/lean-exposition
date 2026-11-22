#!/usr/bin/env python3
"""Convert the quartic reader's reading data into a library instance (instances/quartic/).

    from_quartic.py QUARTIC_CHECKOUT [--out instances/quartic] [--work DIR]

QUARTIC_CHECKOUT is a checkout of wcook04/quartic-query-lean. Its reader shows three papers
written for it, each with a phrase layer (docs/reading_phrases/<paper>.json): the expert
companion, which the reader opens on and which is the main document here, the worked exposition
and the full proof reconstruction. Each phrase layer is bound to its manuscript's SHA-256; this
script refuses a layer whose manuscript has changed.

The papers are Pandoc Markdown. One text transformation, applied alike to each manuscript and to
every quote of its phrase ties, puts them in the reader's dialect: citations become author-date
links to the paper's own reference list (rendered by Pandoc's citeproc, as the quartic reader
does), bracketed spans and heading identifiers become anchors, footnotes become numbered notes,
and links between the three papers become library addresses. The rest of the paper (front matter,
Pandoc divs, print-only TeX) is rewritten around the ties, never inside them.

The instance itself is then written by scripts/from_proof_reader.py, from a page in Proof
Reader's layout that this script assembles in --work: the reading copies, the numbered results
of the expert companion with the Lean compared with OpenAI's statements they restate
(corpus/ties.json), and Lean's recorded dependencies (corpus/reading_dependencies.json). Its phrase
files are then replaced by the quartic ties themselves, with their topics, families, stored
colours, titles, reading notes and comparisons unchanged, and its credit by the quartic reader's.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import shutil
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
PAPER = "quartic"
BASE = f"/library/{PAPER}/"
# The three papers: quartic id, engine slot, manuscript, bibliography, library page slug, noun.
DOCS = [
    ("expert", "short", "expert_companion.md", "expert_companion.bib", "", "companion"),
    ("exposition", "expository", "exposition.md", "exposition.bib", "exposition", "exposition"),
    ("reconstruction", "long", "reasoning_record.md", "reasoning_record.bib", "reconstruction", "reconstruction"),
]
SLUG_OF_FILE = {d[2]: d[4] for d in DOCS}
KIND = {"thm": "Theorem", "lem": "Lemma", "prop": "Proposition", "cor": "Corollary", "def": "Definition"}
RELATION = {"exact": "same", "stronger": "stronger", "partial": "weaker"}
# The quartic reader's own credit, as its home page and About give it.
CREDIT = [
    "The theorem and construction are OpenAI’s, published with no Lean formalization. The three accounts and "
    "the Lean development were written by AI systems under Will Cook’s direction. No human expert has reviewed them.",
    "Lean reports each declaration’s statement, dependencies and axioms. The links between paper passages and Lean, "
    "and the judgments that a statement matches exactly, more strongly or only in part, were written and reviewed by "
    "AI agents; no person has checked them.",
]
COMPANION_CREDIT = ("The theorem and its proof are OpenAI’s. AI systems wrote the three accounts, the Lean and the links "
                    "between them, under Will Cook’s direction.")
CITE_GROUP = re.compile(r"\[([^\[\]]*?-?@[A-Za-z][^\[\]]*)\](?![(\[{])")
CITE_KEY = re.compile(r"-?@([A-Za-z][\w:.#$%&+?<>~/-]*[\w])")


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def pandoc(args: list[str], text: str) -> str:
    return subprocess.run(["pandoc", *args], input=text, capture_output=True, text=True, check=True).stdout


class Transform:
    """The text transformation shared by a manuscript and its ties' quotes."""

    def __init__(self, body: str, bib: Path | None):
        self.groups: dict[str, str] = {}
        self.references: list[tuple[str, str]] = []
        groups = sorted({m.group(0) for m in CITE_GROUP.finditer(body)})
        if groups and bib and bib.is_file():
            self._citations(groups, bib)
        labels = re.findall(r"^\[\^([^\]]+)\]:", body, re.M)
        self.footnotes = {label: k + 1 for k, label in enumerate(labels)}

    def _citations(self, groups: list[str], bib: Path) -> None:
        doc = "\n\n".join(f"CITEGROUP{k}: {g}" for k, g in enumerate(groups))
        args = ["--citeproc", f"--bibliography={bib}", "--from=markdown", "--wrap=none"]
        plain = pandoc([*args, "--to=plain"], doc)
        rendered = {}
        for line in plain.splitlines():
            m = re.match(r"^CITEGROUP(\d+): (.*)$", line)
            if m:
                rendered[int(m.group(1))] = m.group(2).strip()
        for k, group in enumerate(groups):
            text = rendered[k]
            keys = [m.group(1) for m in CITE_KEY.finditer(group)]
            inner = text[1:-1] if text.startswith("(") and text.endswith(")") else text
            pieces = inner.split("; ")
            # As Pandoc links them: the name and year of each work, the locator after the link.
            def one(piece, key):
                m = re.match(r"^(.*?\d{4}[a-z]?)(.*)$", piece)
                return f"[{m.group(1)}](#cite-{key}){m.group(2)}" if m else f"[{piece}](#cite-{key})"
            if len(pieces) == len(keys):
                linked = "; ".join(one(p, key) for p, key in zip(pieces, keys))
            else:
                linked = f"[{inner}](#cite-{keys[0]})"
            self.groups[group] = f"({linked})" if inner is not text else linked
        refs = pandoc([*args, "--to=markdown-citations"], doc)
        for m in re.finditer(r"^::: \{#ref-(\S+) \.csl-entry\}\n(.*?)\n:::", refs, re.M | re.S):
            self.references.append((m.group(1), " ".join(m.group(2).split())))

    def __call__(self, s: str) -> str:
        s = CITE_GROUP.sub(lambda m: self.groups.get(m.group(0), m.group(0)), s)
        # Bracketed spans: `[]{#answer-1}` and `[words]{#id}` keep their identifier as an anchor.
        def span(m):
            ident = re.search(r"#([\w:.-]+)", m.group(2))
            return (f'<a id="{ident.group(1)}"></a>' if ident else "") + m.group(1)
        s = re.sub(r"\[([^\[\]]*)\]\{([^}]*)\}", span, s)
        s = re.sub(r"\[\^([^\]]+)\](?!:)", lambda m: (
            f'<sup class="footnote-ref"><a href="#fn-{m.group(1)}" id="fnref-{m.group(1)}">{self.footnotes.get(m.group(1), "?")}</a></sup>'), s)
        # The source's own passage and claim markers stay as comments some ties are placed after, renamed
        # so that they are not read as this reader's passage markers.
        s = re.sub(r"<!-- (/?)(passage|claim):([^ >]*) -->", r"<!-- quartic-\2 \1\3 -->", s)
        # Figures: one flat figures/ folder, without Pandoc's attributes.
        s = re.sub(r"(\]\(figures/[^)\s]+\))\{[^{}]*\}", r"\1", s)
        s = re.sub(r"\]\(figures/(?:[^)/\s]+/)*([^)/\s]+)\)", r"](figures/\1)", s)
        # Links between the three papers become their library addresses.
        def link(m):
            slug, anchor = SLUG_OF_FILE[m.group(1)], m.group(2) or ""
            return f"]({BASE}{slug + '/' if slug else ''}{anchor})"
        s = re.sub(r"\]\((" + "|".join(re.escape(f) for f in SLUG_OF_FILE) + r")(#[^)\s]*)?\)", link, s)
        return s


def front_matter(text: str) -> tuple[dict, str]:
    m = re.match(r"^---\n(.*?)\n---\n", text, re.S)
    if not m:
        return {}, text
    meta, lines, key = {}, m.group(1).split("\n"), None
    for line in lines:
        km = re.match(r"^([A-Za-z-]+):\s*(.*)$", line)
        if km:
            key, value = km.group(1), km.group(2)
            meta[key] = json.loads(value) if value.startswith('"') else ("" if value in ("|", "") else value)
        elif key and line.startswith("  "):
            meta[key] = (meta[key] + "\n" if meta[key] else "") + line[2:]
    return meta, text[m.end():]


def manuscript(body: str, meta: dict, t: Transform) -> str:
    """The reading copy: the transformed text, with Pandoc's print furniture rewritten around it."""
    out = []
    if meta.get("title"):
        out += [f"# {meta['title']}", ""]
        if meta.get("subtitle"):
            out += [f"*{meta['subtitle']}*", ""]
        byline = " · ".join(x for x in (meta.get("author"), meta.get("date")) if x)
        if byline:
            out += [byline, ""]
        if meta.get("abstract"):
            out += ["**Abstract.** " + t(meta["abstract"].strip()), ""]
    notes: dict[str, str] = {}
    lines, k, depth = body.split("\n"), 0, []
    while k < len(lines):
        line = lines[k]
        if line.strip() == "```{=latex}":  # print-only TeX
            while k < len(lines) and lines[k].strip() != "```":
                k += 1
            k += 1
            continue
        if re.match(r"^\\(clearpage|newpage|tableofcontents|setcounter)\b", line):  # print-only TeX
            k += 1
            continue
        fn = re.match(r"^\[\^([^\]]+)\]:\s*(.*)$", line)
        if fn:
            text = [fn.group(2)]
            while k + 1 < len(lines) and lines[k + 1].startswith("    "):
                k += 1
                text.append(lines[k].strip())
            notes[fn.group(1)] = t(" ".join(text))
            k += 1
            continue
        div = re.match(r"^:{3,}\s*(?:\{([^}]*)\}|([\w-]+))?\s*$", line)
        if div:
            attrs = div.group(1) or (("." + div.group(2)) if div.group(2) else None)
            if attrs is None:  # a closing fence
                kind = depth.pop() if depth else "div"
                if kind != "refs":
                    out.append("</div>")
            elif "#refs" in attrs:
                depth.append("refs")
                for key, entry in t.references:
                    out += [f'<a id="cite-{key}"></a>{entry}', ""]
            else:
                classes = " ".join(re.findall(r"\.([\w-]+)", attrs))
                title = re.search(r'title="([^"]*)"', attrs)
                out += [f'<div class="{classes}"' + (f' title="{title.group(1)}"' if title else "") + ">", ""]
                depth.append("div")
            k += 1
            continue
        heading = re.match(r"^(#{1,6} .*?)\s*\{([^}]*)\}\s*$", line)
        if heading:
            ident = re.search(r"#([\w:.-]+)", heading.group(2))
            if ident:
                out += [f'<a id="{ident.group(1)}"></a>', ""]
            line = heading.group(1)
        out.append(t(line))
        k += 1
    text = "\n".join(out).rstrip("\n") + "\n"
    if notes:
        text += "\n## Notes\n\n" + "\n\n".join(
            f'<a id="fn-{label}"></a>**{t.footnotes[label]}.** {note} [↩](#fnref-{label})' for label, note in notes.items()) + "\n"
    return text


def results_of(text: str) -> list[tuple[str, str, str, str]]:
    """The expert companion's numbered results: (address, title, section, OpenAI statement id)."""
    out, section = [], None
    for line in text.split("\n"):
        h = re.match(r"^#{2,3} (\d+(?:\.\d+)*)\.?\s", line)
        if h:
            section = h.group(1)
        m = re.match(r"^\*\*(Theorem|Proposition|Lemma|Corollary|Definition) (\d+)\*\*\s*\(([^)]*?)\[@OpenAI2026, (\w+) ([\dA-Z.]+)", line)
        if m:
            kind = next(k for k, v in KIND.items() if v == m.group(4))
            out.append((f"{m.group(1).lower()}-{m.group(2)}", f"{m.group(1)} {m.group(2)}", section, f"{kind}-{m.group(5)}"))
    return out


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("quartic", type=Path)
    ap.add_argument("--out", type=Path, default=ROOT / "instances" / PAPER)
    ap.add_argument("--work", type=Path, required=True, help="a scratch folder for the assembled pages")
    ap.add_argument("--lean-exposition", default="lean-exposition")
    ap.add_argument("--comparator-run", help="the GitHub Actions run that wrote the current Comparator receipts (its URL)")
    ap.add_argument("--comparator-artifact", type=Path,
                    help="that run's downloaded evidence artifact; every current receipt's file name and log hash must appear in it")
    ap.add_argument("--pdf", action="append", default=[], metavar="PAPER=FILE",
                    help="an accepted PDF of one paper (expert, exposition or reconstruction) rendered from the current manuscript")
    args = ap.parse_args()
    q = args.quartic.resolve()
    commit = subprocess.run(["git", "-C", str(q), "rev-parse", "HEAD"], capture_output=True, text=True, check=True).stdout.strip()
    repo = "https://github.com/wcook04/quartic-query-lean"
    shutil.rmtree(args.work, ignore_errors=True)
    layers, texts, transforms = {}, {}, {}
    for pid, slot, md, bib, slug, noun in DOCS:
        layer = json.loads((q / "docs/reading_phrases" / f"{pid}.json").read_text())
        source = (q / layer["manuscript"]).read_bytes()
        if sha(source) != layer["manuscript_sha256"]:
            raise SystemExit(f"{pid}: {layer['manuscript']} no longer matches the phrase layer's manuscript_sha256")
        meta, body = front_matter(source.decode("utf-8"))
        t = Transform(body + "\n" + meta.get("abstract", ""), q / "docs" / bib)
        layers[pid], transforms[pid] = layer, t
        texts[pid] = manuscript(body, meta, t)
        page = args.work / pid
        page.mkdir(parents=True)
        (page / "paper.md").write_text(texts[pid])
        figures = sorted({m.group(1) for m in re.finditer(r"\]\(figures/((?:[^)/]+/)*[^)/]+)\)", body)})
        for rel in figures:
            target = page / "figures" / Path(rel).name
            if target.exists():
                raise SystemExit(f"{pid}: two figures named {target.name}")
            target.parent.mkdir(exist_ok=True)
            shutil.copyfile(q / "docs/figures" / rel, target)
        title = meta.get("title") or re.match(r"^# (.*?)(?:\s*\{.*\})?$", body.lstrip(), re.M).group(1)
        topics = [{"id": tp["id"], "name": tp["name"], "description": tp.get("description", "")} for tp in layer["topics"]]
        (page / "paper.toml").write_text(
            f'[paper]\ntitle = {json.dumps(title)}\nshort_title = {json.dumps(title)}\nmarkdown = "paper.md"\n'
            f'url = "{repo}/blob/{commit}/{layer["manuscript"]}"\nauthors = ["AI systems under the direction of Will Cook"]\n'
            f'noun = "{noun}"\nlicence = "Apache-2.0"\n\n[lean]\nproject = {json.dumps(str(q / "lean"))}\n'
            f'source = "{repo}/tree/{commit}/lean"\nmodules = ["QuarticQuery", "QuarticCorpus"]\n'
            f'scope = "The Quartic project’s Lean, at {commit[:7]}: the QuarticQuery development and the QuarticCorpus statement files. '
            f'Each declaration’s dependencies shown here are Lean’s own report from the compiled modules."\n')
        links = {"passages": [], "topics": topics, "families": [], "plain": {}, "notes": {}, "claims": [], "fidelity": {}, "show_also": []}
        if pid == "expert":
            # The numbered results, each with the Lean compared with the OpenAI statement it restates.
            compared = json.loads((q / "corpus/ties.json").read_text())
            for address, rtitle, section, statement in results_of(body):
                # The leading comparison, as the quartic results index shows it: an exact match, else a
                # stronger one, else a partial one, preferring one with no open assumption.
                rank = lambda r: {"exact": 0, "stronger": 1}.get(r["relation"], 2 + bool(r.get("open_assumptions")))
                rows = [r for r in compared.get(statement, []) if r.get("relation") in RELATION]
                rows = [r for r in rows if rank(r) == min(map(rank, rows))]
                links["claims"].append({"id": address, "title": rtitle, "section": section, "passage": None,
                                        "lean": [r["declaration"] for r in rows]})
                for r in rows:
                    links["fidelity"].setdefault(r["declaration"], {
                        "verdict": RELATION[r["relation"]],
                        "text": f"Compared with OpenAI’s {KIND[statement.split('-')[0]]} {statement.split('-', 1)[1]}: {r.get('note', '').strip()}".strip()})
            deps = json.loads((q / "corpus/reading_dependencies.json").read_text())["nodes"]
            (page / "generated").mkdir()
            (page / "generated/lean.json").write_text(json.dumps({"declarations": [
                {"name": n, "type_dependencies": sorted(set(d.get("type", [])) | set(d.get("structural", []))),
                 "value_dependencies": sorted(d.get("value", [])), "axioms": None} for n, d in sorted(deps.items())]}))
        (page / "links.json").write_text(json.dumps(links, ensure_ascii=False, indent=1))
    companions = []
    for pid, slot, md, bib, slug, noun in DOCS[1:]:
        title = json.loads(json.dumps(re.search(r'title = (".*")', (args.work / pid / "paper.toml").read_text()).group(1)))
        companions += ["--companion", f"{slot}={args.work / pid}|{slug}|{json.loads(title)}"]
    subprocess.run([sys.executable, str(HERE / "from_proof_reader.py"), str(args.work / "expert"), "--paper", PAPER,
                    "--out", str(args.out), "--source-commit", commit, "--goal", "theorem-1", "--slot", "short",
                    "--partial", "--lean-exposition", args.lean_exposition, *companions], check=True, stdout=subprocess.DEVNULL)
    out = args.out
    # ---- the quartic ties, titles, notes and colours, in place of the converter's empty phrase layers
    families_all = []
    for pid, slot, md, bib, slug, noun in DOCS:
        layer, t = layers[pid], transforms[pid]
        stored = json.loads((q / "docs/reading_phrases" / f"colours-{pid}.json").read_text())
        family_of = {tid: f["id"] for f in stored["families"] for tid in f["topics"]}
        families = [{"id": f["id"], "name": f["name"]} for f in stored["families"]]
        topics = [{"id": tp["id"], "name": tp["name"], "description": tp.get("description", ""), "family": family_of[tp["id"]]}
                  for tp in layer["topics"]]
        ties = []
        for tie in layer["ties"]:
            row = {k: (t(v) if k in ("from", "to", "after") else v) for k, v in tie.items()}
            row["lean"] = [{**r, "file": r["file"].removeprefix("lean/")} for r in tie["lean"]]
            ties.append(row)
        def text_of(v):
            return v["title"] if isinstance(v, dict) else (v[0] if isinstance(v, list) else v)
        titles = {k: text_of(v) for k, v in layer["titles"].items()}
        most = max(len(v.split()) for v in titles.values())
        paper_text = (out / "papers" / slot / "paper.md").read_text()
        phrases = {
            "schema": "phrase-ties/1", "paper": slot,
            "meaning": ("Each tie names the phrase of the paper that a Lean declaration states, carried unchanged from the quartic "
                        f"reader's phrase layer ({repo} {commit[:12]}, docs/reading_phrases/{pid}.json). Titles, reading notes, "
                        "topics and comparisons are AI-drafted or AI-assessed; no person has checked them."),
            "families": families,
            "topic_order": [tp["id"] for tp in layer["topics"]],
            "parts": [{"name": "", "lines": [1, paper_text.count("\n") + 1], "source_commit": commit, "topics": topics,
                       "titles": dict(sorted(titles.items())), "notes": dict(sorted(layer["notes"].items())),
                       "title_words": [2, max(6, most)]}],
            "ties": ties, "removed": layer.get("removed", []),
        }
        (out / f"alignment/phrases-{slot}.json").write_text(json.dumps(phrases, indent=1, ensure_ascii=False) + "\n")
        (out / f"alignment/colours-{slot}.json").write_text(json.dumps({
            "schema": "topic-colours/1", "paper": slot,
            "meaning": "The quartic reader's stored topic colours, carried unchanged: each family one hue, each topic one shade of it.",
            "stored_from": f"{repo} {commit[:12]} docs/reading_phrases/colours-{pid}.json",
            "parts": [{k: stored[k] for k in ("key", "shared_by", "lightness", "chroma", "families", "topics")}]},
            indent=1, ensure_ascii=False) + "\n")
        if pid == "expert":
            families_all, topics_main = families, topics
    # Plain titles of two to six words, for the places that show a short name.
    names = {}
    for pid, *_ in DOCS:
        for k, v in layers[pid]["titles"].items():
            v = v["title"] if isinstance(v, dict) else (v[1] if isinstance(v, list) else v)  # the plain rendering
            if 2 <= len(v.split()) <= 6 and "$" not in v:
                names.setdefault(k, v)
    known = {n for p in (out / "alignment").glob("phrases-*.json") for tie in json.loads(p.read_text())["ties"] for n in [r["name"] for r in tie["lean"]]}
    (out / "alignment/names.json").write_text(json.dumps({"schema": 1, "names": {k: v for k, v in sorted(names.items()) if k in known}},
                                                        indent=1, ensure_ascii=False) + "\n")
    # ---- accepted PDFs: only a render bound to the current manuscript (--pdf PAPER=FILE, its source hash
    # checked against the PDF's sidecar by the caller). The quartic reader publishes none for the current
    # text, so by default no document has a PDF and the reader shows no Text | PDF toggle.
    pdfs = {}
    for spec in args.pdf:
        pid, path = spec.split("=", 1)
        slot = next(d[1] for d in DOCS if d[0] == pid)
        data = Path(path).read_bytes()
        (out / "papers" / slot / "paper.pdf").write_bytes(data)
        pdfs[slot] = {"file": "paper.pdf", "sha256": sha(data), "bytes": len(data)}
    # ---- the instance: the quartic reader's own titles, credit and pages
    inst = json.loads((out / "instance.json").read_text())
    expert_title = re.search(r"^# (.*)$", texts["expert"], re.M).group(1)
    inst.update({
        "title": expert_title, "short_title": "Quartic query separation",
        "authors": ["AI systems under the direction of Will Cook"],
        "venue": f"The quartic reader's three accounts of OpenAI's nearly quartic separation, from {repo.removeprefix('https://github.com/')} at {commit[:7]}",
        # The header and About carry the quartic reader's two credit paragraphs, exactly, then the
        # library's one sentence saying what was made with AI; each companion page carries the home
        # page's own one-line credit.
        "credit_lines": CREDIT, "companion_credit": COMPANION_CREDIT, "licence": "Apache-2.0",
        "host": "Hosted by Will Cook in his reading library.",
        "review": ("The links from the text to the Lean, the titles, the reading notes and the comparisons were made with AI. "
                   "No mathematician has reviewed them."),
        "families": families_all, "topics": topics_main, "topic_order": [tp["id"] for tp in topics_main],
        "main_lean": "QuarticQuery.theorem_1_1_unconditional",
    })
    inst["source"] = {"quartic": {"repository": repo, "commit": commit}, "upstream": {"repository": repo, "commit": commit,
                      "paper": "https://github.com/openai/math/tree/main/preprints/A-Nearly-Quartic-Separation-Between-Randomized-and-Quantum-Query-Complexity-October-5-2026"},
                      "lean_scope": inst["source"].get("lean_scope", "")}
    docs = []
    for pid, slot, md, bib, slug, noun in DOCS:
        doc = next(d for d in inst["documents"] if d["slot"] == slot)
        doc.update({"id": "paper" if slot == "short" else pid, "slug": slug, "noun": noun,
                    "title": re.search(r"^# (.*)$", texts[pid], re.M).group(1)})
        if slot in pdfs:
            doc["pdf"] = pdfs[slot]
        docs.append(doc)
    inst["documents"] = docs
    (out / "instance.json").write_text(json.dumps(inst, indent=1, ensure_ascii=False) + "\n")
    # ---- results the main theorem's Lean does not reach, with the reason (checked by check_instance.py)
    deps = json.loads((q / "corpus/reading_dependencies.json").read_text())["nodes"]
    seen, stack = {inst["main_lean"]}, [inst["main_lean"]]
    while stack:
        d = deps.get(stack.pop(), {})
        for n in d.get("type", []) + d.get("value", []) + d.get("structural", []):
            if n not in seen:
                seen.add(n)
                stack.append(n)
    apart = {}
    for address, row in json.loads((out / "alignment/results.json").read_text())["results"].items():
        if address != "theorem-1" and not any(n in seen for n in row["lean"]):
            names = " and ".join(n.removeprefix("QuarticQuery.") for n in row["lean"])
            apart[f"{PAPER}.{address}"] = (
                f"Lean's recorded dependencies of {inst['main_lean'].removeprefix('QuarticQuery.')} (corpus/reading_dependencies.json "
                f"at {commit[:7]}) do not reach {names}, the Lean compared with the OpenAI statement that {row['title']} restates: "
                "the main theorem's Lean proves what it needs by its own route, and this theorem states the result separately.")
    (out / "authored").mkdir(exist_ok=True)
    (out / "authored/check.json").write_text(json.dumps({"not_joined": apart}, indent=1, ensure_ascii=False) + "\n")
    # ---- the redirect table for the old reader's addresses: OpenAI statements to the results restating them
    results = json.loads((out / "alignment/results.json").read_text())["results"]
    statement_to_result = {}
    for address, rtitle, section, statement in results_of(front_matter((q / "docs/expert_companion.md").read_text())[1]):
        if address in results:
            statement_to_result[statement] = address
    # The old reader's passage selections (s=), from every edition gh-pages still serves, each placed by
    # its quoted opening words on its paragraph of the library's reading copy (?l=b<start>-<end>, in the
    # copy's UTF-8 bytes), and its anchors (a=): explicit ids, Pandoc's heading ids and reference entries.
    selections, anchors = {}, {}
    ref = "origin/gh-pages"
    listing = subprocess.run(["git", "-C", str(q), "ls-tree", "--name-only", f"{ref}:reading-api/v1/"], capture_output=True, text=True).stdout.split()
    for name in sorted(n for n in listing if n.startswith("edition-")):
        manifest = json.loads(subprocess.run(["git", "-C", str(q), "show", f"{ref}:reading-api/v1/{name}"], capture_output=True, text=True, check=True).stdout)
        for pid, slot, *_ in DOCS:
            entry = manifest["resources"].get(f"selection/{pid}.json")
            if not entry:
                continue
            rows = json.loads(subprocess.run(["git", "-C", str(q), "show", f"{ref}:reading-api/v1/{entry['href']}"], capture_output=True, text=True, check=True).stdout)
            text = (out / "papers" / slot / "paper.md").read_text()
            for row in rows if isinstance(rows, list) else []:
                if row["id"] in selections.get(pid, {}) or not row.get("quote"):
                    continue
                at = text.find(transforms[pid](row["quote"]))
                if at < 0:
                    continue
                start = text.rfind("\n\n", 0, at) + 2 if text.rfind("\n\n", 0, at) >= 0 else 0
                stop = text.find("\n\n", at)
                stop = len(text) if stop < 0 else stop
                b0, b1 = len(text[:start].encode()), len(text[:stop].encode())
                selections.setdefault(pid, {})[row["id"]] = f"b{b0}-{b1}"
    for pid, slot, *_ in DOCS:
        text = (out / "papers" / slot / "paper.md").read_text()
        table, seen = {}, {}
        for ident in re.findall(r'<a id="([^"]+)"', text):
            table[ident] = ident
        for key in re.findall(r'<a id="cite-([^"]+)"', text):
            table[f"ref-{key}"] = f"cite-{key}"
        for m in re.finditer(r"^#{1,6} (.+)$", text, re.M):
            heading = m.group(1).strip()
            ident = re.sub(r"[^\w\s.-]", "", re.sub(r"[*_`$\\]", "", heading).lower())
            ident = re.sub(r"\s+", "-", ident).lstrip("0123456789.-") or "section"
            n = seen.get(ident, 0)
            seen[ident] = n + 1
            ident = ident if n == 0 else f"{ident}-{n}"
            sys.path.insert(0, str(HERE))
            from from_proof_reader import section_number
            table.setdefault(ident, section_number(heading) or ident)
        anchors[pid] = table
    (out / "generated/redirects.json").write_text(json.dumps({
        "schema": 1,
        "meaning": ("The old quartic reader's addresses and their library places: OpenAI statement ids (st=) and the "
                    "expert companion result that restates each, passage selections (s=) as byte ranges of each reading "
                    "copy, and anchors (a=)."),
        "statements": statement_to_result,
        "papers": {pid: slug for pid, _, _, _, slug, _ in DOCS},
        "selections": selections, "anchors": anchors}, indent=1, ensure_ascii=False) + "\n")
    # ---- the browser checks' arguments for this paper (CI reads them: .github/workflows/library.yml)
    (out / "check.args").write_text("--phrase a-family --result theorem-1 --decl QuarticQuery.theorem_1_1_unconditional "
                                    "--section 4.2 --notice reviewed --no-pdf\n")
    comparator(q, out, commit, args)
    levels(q, out, transforms)
    print(f"quartic: {sum(len(l['ties']) for l in layers.values())} ties over 3 papers, {len(results)} results, commit {commit[:12]}")
    return 0


def edition_resource(q: Path, revision: str, name: str):
    """A resource of the newest gh-pages edition built from `revision`, as the old reader served it."""
    ref = "origin/gh-pages"
    def show(path):
        return subprocess.run(["git", "-C", str(q), "show", f"{ref}:reading-api/v1/{path}"], capture_output=True, check=True).stdout
    names = subprocess.run(["git", "-C", str(q), "ls-tree", "--name-only", f"{ref}:reading-api/v1/"], capture_output=True, text=True,
                           check=True).stdout.split()
    for edition in sorted(n for n in names if n.startswith("edition-")):
        manifest = json.loads(show(edition))
        if manifest.get("revision") == revision and name in manifest["resources"]:
            return json.loads(show(manifest["resources"][name]["href"]))
    raise SystemExit(f"no gh-pages edition of {revision[:12]} carries {name}")


def comparator(q: Path, out: Path, commit: str, args) -> None:
    """Quartic's Comparator evidence, as its reader showed it (the edition's comparator-evidence.json):
    each positive configuration whose latest receipt passed for the current sources, with its receipt
    file and its rejected controls, carried unchanged into generated/comparator/receipts/. The receipt
    the reader shows (generated/comparator/receipt.json) lists one entry per configuration; What ran
    lists each receipt (generated/comparator/runs/, an evidence record of kind comparator)."""
    evidence = edition_resource(q, commit, "comparator-evidence.json")
    folder = out / "generated/comparator"
    shutil.rmtree(folder, ignore_errors=True)
    run_url, basis = None, None
    receipts = {}
    for config, run in evidence["runs"].items():
        for path in [run["receipt"], *(c["receipt"] for c in run["rejected_controls"])]:
            receipts[path] = json.loads((q / path).read_text())
    if args.comparator_run:
        if not args.comparator_artifact:
            raise SystemExit("--comparator-run needs --comparator-artifact, to check that the run wrote these receipts")
        blob = b"".join(f.read_bytes() for f in args.comparator_artifact.rglob("*") if f.is_file())
        absent = [p for p, r in receipts.items() if Path(p).name.encode() not in blob or r["log_sha256"].encode() not in blob]
        if absent:
            raise SystemExit(f"{len(absent)} receipt(s) not in the run's artifact, e.g. {absent[0]}")
        run_url = args.comparator_run
        basis = (f"The run's evidence artifact carries all {len(receipts)} receipt files below, each with the same log hash; "
                 "the receipts themselves do not name the run.")
    files = {}
    for path, body in receipts.items():
        data = (q / path).read_bytes()
        (folder / "receipts").mkdir(parents=True, exist_ok=True)
        (folder / "receipts" / Path(path).name).write_bytes(data)
        files[f"receipts/{Path(path).name}"] = sha(data)
    def words(config: str) -> str:
        stem = Path(config).stem.removeprefix("negative-")
        return re.sub(r"(?<=[a-z])(?=[A-Z])", " ", stem).replace("-", " ").lower()
    runs, applies, ledger = [], {}, []
    for decl, rows in evidence["declarations"].items():
        for row in rows:
            if row["link"] == "solution_applies":
                applies.setdefault(row["run"], {})[decl] = row["target"]
    for config, run in sorted(evidence["runs"].items(), key=lambda kv: kv[1]["name"]):
        receipt = receipts[run["receipt"]]
        paranoid = bool(receipt.get("paranoid"))
        kernels = ["Lean’s default kernel"] + (["every external checker bundled with Lean (--paranoid)"] if paranoid else [])
        controls = []
        for c in run["rejected_controls"]:
            r = receipts[c["receipt"]]
            controls.append({"change": f"{words(c['configuration'])} ({Path(c['configuration']).name})",
                             "output": [f"rejected as expected ({r.get('expected_diagnostic', 'exit ' + str(r.get('exit_code')))})"],
                             "receipt": f"receipts/{Path(c['receipt']).name}"})
        runs.append({
            "name": run["name"], "configuration": config.removeprefix("lean/"),
            **({"run": run_url} if run_url else {}), "date": run["ran_at"][:10], "commit": receipt["commit"],
            "kernels": kernels, "permitted_axioms": run["permitted_axioms"],
            "mode": f"{receipt['tool']}{', with --paranoid' if paranoid else ''}",
            "receipt": f"receipts/{Path(run['receipt']).name}",
            "accepted": {"theorem_names": run["theorem_names"]},
            **({"applies": applies[config]} if config in applies else {}),
            "rejected_controls": controls})
        ledger.append({
            "record_type": "comparator_receipt", "entry_id": run["name"],
            "run": {"repository": "wcook04/quartic-query-lean", **({"url": run_url, "run_id": run_url.rstrip("/").rsplit("/", 1)[-1]} if run_url else {}),
                    "commit": receipt["commit"], "date": run["ran_at"][:10]},
            "theorem_pairs": [{"challenge": n} for n in run["theorem_names"]], "kernels": kernels,
            "axioms": run["permitted_axioms"], "outcome": "accepted" if receipt["status"] == "passed" else receipt["status"],
            "receipt": f"receipts/{Path(run['receipt']).name}"})
    (folder / "runs").mkdir(parents=True, exist_ok=True)
    names = []
    for row in ledger:
        name = f"{re.sub(r'[^A-Za-z0-9-]+', '-', row['entry_id'])}.json"
        (folder / "runs" / name).write_text(json.dumps(row, indent=1, ensure_ascii=False) + "\n")
        names.append(name)
    (folder / "runs/index.json").write_text(json.dumps({"record_type": "receipt_index", "receipts": names}, indent=1) + "\n")
    accepted = sum(len(r["accepted"]["theorem_names"]) for r in runs)
    (folder / "receipt.json").write_text(json.dumps({
        "schema": 1,
        "what": (f"Comparator checked {accepted} theorem statements in {len(runs)} configurations against challenge files that hold "
                 "the project’s own frozen definitions and statements, and rejected every altered control. The Unconditional "
                 "configuration accepts the main theorem’s four statements, the family with no hypothesis among them, and was also "
                 "run with --paranoid. Comparator compares each solution with its challenge statement; whether that statement "
                 "says what the paper says is the comparison shown on each step."),
        "against": "the project’s frozen challenge statements",
        **({"run": run_url, "run_basis": basis} if run_url else {}),
        "date": max(r["date"] for r in runs), "commit": runs[0]["commit"],
        "runs": runs}, indent=1, ensure_ascii=False) + "\n")
    files["receipt.json"] = sha((folder / "receipt.json").read_bytes())
    for name in names + ["index.json"]:
        files[f"runs/{name}"] = sha((folder / "runs" / name).read_bytes())
    # What ran: one evidence record naming the receipt index. The graph's hash is bound in each paper's
    # mapping, so the mappings are rebound to the new graph.
    graph_path = out / "evidence-graph.json"
    graph = json.loads(graph_path.read_text())
    graph["evidence"] = [e for e in graph["evidence"] if e["id"] != "comparator_runs"] + [{
        # An outside run, observed: this tool ran nothing, so the record is a platform observation that
        # ran nothing here; each receipt it lists carries its own outcome.
        "id": "comparator_runs", "kind": "platform_observation", "status": "not_run",
        "command": ["lake", "comparator", "--config", "<each configuration>"], "tool": runs[0]["mode"],
        "source_ids": ["upstream"], "subject_ids": [graph["selected_goals"][0]],
        "details": f"{len(runs)} Comparator configurations accepted; their receipts are listed one by one in What ran.",
        "receipt_path": "generated/comparator/runs/index.json",
        "receipt_sha256": sha((folder / "runs/index.json").read_bytes())}]
    old = sha(graph_path.read_bytes())
    graph_bytes = (json.dumps(graph, indent=1, ensure_ascii=False) + "\n").encode()
    graph_path.write_bytes(graph_bytes)
    for mapping in (out / "papers").glob("*/*.json"):
        if mapping.name in ("correspondence.json", "absent.json"):
            text = mapping.read_text()
            if old in text:
                mapping.write_text(text.replace(old, sha(graph_bytes)))
    inst = json.loads((out / "instance.json").read_text())
    inst["comparator"] = {"files": dict(sorted(files.items())), "receipt": "receipt.json"}
    inst.setdefault("reader", {})["publish_receipts"] = True
    (out / "instance.json").write_text(json.dumps(inst, indent=1, ensure_ascii=False) + "\n")


LEVELS = {"short": "Expert companion", "expository": "Worked exposition", "long": "Full proof reconstruction"}


def levels(q: Path, out: Path, transforms: dict) -> None:
    """Compare's three levels: each numbered result stated in the expert companion, the reconstruction
    (the paragraph after the source's own claim marker for the OpenAI statement it restates) and the
    exposition (a phrase that states the result's Lean)."""
    batch_path = out / "alignment/m1-results.json"
    batch = json.loads(batch_path.read_text())
    record = (out / "papers/long/paper.md").read_text()
    expo = json.loads((out / "alignment/phrases-expository.json").read_text())["ties"]
    recon = json.loads((out / "alignment/phrases-long.json").read_text())["ties"]
    sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
    from lean_exposition.alignment import _math_spans
    statements = {a: s for a, _, _, s in results_of(front_matter((q / "docs/expert_companion.md").read_text())[1])}
    found = {"long": 0, "expository": 0}
    for rid, row in batch["records"].items():
        address = rid.split(".", 1)[1]
        statement = statements.get(address)
        names = {r["name"] for r in row["lean"]}
        marker = record.find(f"<!-- quartic-claim {statement} -->") if statement else -1
        if marker >= 0:
            begin = record.find("\n", marker) + 1
            while record[begin:begin + 1] == "\n":
                begin += 1
            stop = begin
            while True:  # to the paragraph's end, never inside a display
                nxt = record.find("\n\n", stop)
                stop = len(record) if nxt < 0 else nxt
                body = record[begin:stop]
                if nxt < 0 or (body.count("$$") % 2 == 0 and body.count("\\[") == body.count("\\]")):
                    break
                stop = nxt + 2
            stop = min(stop, begin + 1700)
            spans = _math_spans(record[begin:stop])
            def edge(cut, forward):
                for x, y, _ in spans:
                    if x < cut - begin < y:
                        return begin + (y if forward else x)
                return cut
            grow = 0
            while True:
                a = edge(begin + min(80 + grow, stop - begin), True)
                b = edge(stop - min(60 + grow, stop - begin), False)
                first, last = record[begin:a], record[b:stop]
                if (record.count(first) == 1 and record.find(last, begin) + len(last) == stop) or a >= stop:
                    break
                grow += 20
            row["statements"].append({"paper": "long", "role": "statement", "from": first, "to": last, "origin": "ai"})
            found["long"] += 1
        # Otherwise a phrase of that paper tied to the result's Lean: one that states it is the result's
        # statement there; one the Lean contains, or states a part of, explains it.
        for slot, ties in (("long", recon), ("expository", expo)):
            if any(st["paper"] == slot for st in row["statements"]):
                continue
            rank = {"states": 0, "contains": 1, "part": 2}
            best = sorted(((rank[r["relation"]], k, t) for k, t in enumerate(ties) for r in t["lean"]
                           if r["name"] in names and r["relation"] in rank and t["role"] in ("statement", "definition")),
                          key=lambda x: (x[0], x[1]))
            if not best:
                continue
            level, _, tie = best[0]
            row["statements"].append({"paper": slot, "role": "statement" if level == 0 else "explanation",
                                      "from": tie["from"], "to": tie["to"],
                                      **({"after": tie["after"]} if tie.get("after") else {}), "origin": "ai"})
            found[slot] += 1
    batch_path.write_text(json.dumps(batch, indent=1, ensure_ascii=False) + "\n")
    inst = json.loads((out / "instance.json").read_text())
    inst["levels"] = ["expository", "short", "long"]
    inst["level_names"] = LEVELS
    (out / "instance.json").write_text(json.dumps(inst, indent=1, ensure_ascii=False) + "\n")
    print(f"compare: {found['long']} results placed in the reconstruction, {found['expository']} in the exposition")


if __name__ == "__main__":
    sys.exit(main())
