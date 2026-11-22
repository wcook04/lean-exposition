#!/usr/bin/env python3
"""Stage a Proof Reader-shaped page from a checked reading copy and its held statement ties.

The checked reading copy (paper.md, with \\tag{n} numbers and bold statement labels) and a
held-ties file (tie id -> topic, comparisons, and an anchor: {kind: equation, tag} or
{kind: statement, label}) become a page folder that scripts/from_proof_reader.py converts:

    paper.toml   the Proof Reader page's own, reading paper.md, Lean project = the staged closure
    paper.md     the reading copy, unchanged; figures/ beside it
    links.json   one passage per held tie, quoting the display that carries its tag (the whole
                 $$...$$) or the statement from its bold label to the end of its paragraph or the
                 first display, whichever comes first; tie ids are the held ids, unchanged
    lean/        the Lean modules the ties and claims name, and their import closure, unchanged

Topics, families, plain titles and reading notes come from the Proof Reader pages given with
--also (the first page that has a value wins). Usage:

  stage_held_ties.py --copy DIR --page PROOF_READER/papers/navier-stokes-paper \\
      --also PROOF_READER/papers/navier-stokes ... --out STAGE
"""
import argparse, json, re, shutil
from pathlib import Path

ap = argparse.ArgumentParser()
ap.add_argument("--copy", type=Path, required=True, help="folder with paper.md, figures/, paper_ties_held.json")
ap.add_argument("--page", type=Path, required=True, help="the Proof Reader page of the paper (paper.toml, links.json, lean/)")
ap.add_argument("--also", type=Path, action="append", default=[], help="Proof Reader pages for topics, titles and notes")
ap.add_argument("--out", type=Path, required=True)
ap.add_argument("--sentences", type=Path, help="library-data folder: passages.json, statement_ties.json, "
                "paper_declarations.json, statement_file_declarations.json, families_topics.json")
a = ap.parse_args()

md = (a.copy / "paper.md").read_text()
held = json.loads((a.copy / "paper_ties_held.json").read_text())
sent = None
if a.sentences:
    # The audited statement ties replace the held ones; a replaced tie is carried by phrase passages.
    held = json.loads((a.sentences / "statement_ties.json").read_text())
    sent = {name: json.loads((a.sentences / f"{name}.json").read_text()) for name in
            ("passages", "paper_declarations", "statement_file_declarations", "families_topics")}
links = json.loads((a.page / "links.json").read_text())
pages = [a.page, *a.also]
extra = [json.loads((p / "links.json").read_text()) for p in a.also]


def inline(text: str) -> str:
    """Notes set displays as $$...$$; the cards typeset $...$ only, so a display becomes $\\displaystyle ...$."""
    display = lambda m: "$\\displaystyle " + " ".join(m.group(1).split()) + "$"
    text = re.sub(r"\$\$(.+?)\$\$", display, text, flags=re.S)
    text = re.sub(r"\\\[(.+?)\\\]", display, text, flags=re.S)
    return re.sub(r"\\\((.+?)\\\)", lambda m: "$" + m.group(1) + "$", text, flags=re.S)


def unique(pattern: str, what: str) -> re.Match:
    hits = list(re.finditer(pattern, md))
    if len(hits) != 1:
        raise SystemExit(f"{what}: {len(hits)} matches in the reading copy")
    return hits[0]


import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
from lean_exposition.alignment import _math_spans  # noqa: E402

MATH = [(x, y) for x, y, _ in _math_spans(md)]


def snapped(start: int, stop: int) -> tuple[int, int]:
    """Widen a quote to whole formulas, and end it at its paragraph: a tie never cuts a formula."""
    for _ in range(3):
        for x, y in MATH:
            if x < start < y:
                start = x
            if x < stop < y:
                stop = y
        cut, at = None, start
        while True:
            br = md.find("\n\n", at, stop)
            if br < 0:
                break
            if not any(x <= br < y for x, y in MATH):
                cut = br
                break
            at = br + 2
        if cut is not None:
            stop = cut
    return start, stop


passages, redirects = [], {}
for tid, t in held.items():
    anchor = t["anchor"]
    if t.get("audit", {}).get("verdict") == "replaced" and t.get("replacement_passages"):
        redirects[tid] = t["replacement_passages"][0]
        continue
    if anchor.get("quote") and not anchor.get("label"):
        # The audit's exact quote of the tie, widened to whole formulas and kept in its paragraph.
        if md.count(anchor["quote"]) != 1:
            raise SystemExit(f"{tid}: anchor quote occurs {md.count(anchor['quote'])} times in the reading copy")
        start = md.index(anchor["quote"])
        start, stop = snapped(start, start + len(anchor["quote"]))
    elif anchor.get("tag"):
        m = unique(r"\\tag\{" + re.escape(anchor["tag"]) + r"\}", tid)
        start = md.rfind("$$", 0, m.start())
        stop = md.find("$$", m.end()) + 2
    else:
        m = unique(r"\*\*" + re.escape(anchor["label"]) + r"(?![0-9])(?!\.[0-9])", tid)
        start = m.start()
        if sent:
            # With sentence ties, a statement's tie is its bold label; its sentences carry their own ties.
            stop = md.find("**", m.end()) + 2
        else:
            ends = [x for x in (md.find("\n\n", start), md.find("$$", start)) if x > 0]
            stop = min(ends) if ends else len(md)
    quote = md[start:stop].rstrip()
    comparisons = t.get("comparisons", [])
    passages.append({"id": tid, "role": "states", "quote": quote, "topic": t["topic"],
                     "lean": list(dict.fromkeys(c["lean"] for c in comparisons)),
                     "comparisons": [{"lean": c["lean"], "fidelity": c["fidelity"], "note": inline(c.get("note", ""))} for c in comparisons]})

widened = []
if sent:
    for p in sent["passages"]:
        if md.count(p["quote"]) != 1:
            raise SystemExit(f"{p['id']}: quote occurs {md.count(p['quote'])} times in the reading copy")
        at = md.index(p["quote"])
        start, stop = snapped(at, at + len(p["quote"]))
        quote = md[start:stop].rstrip()
        if quote != p["quote"]:
            widened.append(p["id"])
        if md.count(quote) != 1:
            raise SystemExit(f"{p['id']}: widened quote is not unique")
        passages.append({"id": p["id"], "role": p["role"], "quote": quote, "topic": p["topic"],
                         "lean": list(dict.fromkeys(p.get("lean", []) + [c["lean"] for c in p.get("comparisons", [])])),
                         "comparisons": [{"lean": c["lean"], "fidelity": c["fidelity"], "note": inline(c.get("note", ""))}
                                         for c in p.get("comparisons", [])]})
claims = [dict(c, passage=redirects.get(c.get("passage"), c.get("passage"))) for c in links["claims"]]
out_links = {"schema": 1, "claims": claims, "passages": passages, "redirects": redirects,
             "families": next((x["families"] for x in extra if x.get("families")), []),
             "topics": next((x["topics"] for x in extra if x.get("topics")), []),
             "plain": {}, "notes": {}, "fidelity": links.get("fidelity", {})}
if sent:
    out_links["families"] = sent["families_topics"]["families"]
    out_links["topics"] = sent["families_topics"]["topics"]
    # Notes set displays as $$...$$; the cards typeset $...$ only, so a display becomes $\displaystyle ...$.
    for source in ("paper_declarations", "statement_file_declarations"):
        for row in sent[source].values():
            for key in ("note", "summary"):
                if row.get(key):
                    row[key] = inline(row[key])
    # Titles and notes: the paper's 632 linked declarations first, then the readable statement files'.
    for source in ("paper_declarations", "statement_file_declarations"):
        for name, row in sent[source].items():
            if row.get("title"):
                out_links["plain"].setdefault(name, row["title"])
            if row.get("note"):
                out_links["notes"].setdefault(name, {"text": row["note"], **({"summary": row["summary"]} if row.get("summary") else {})})
topic_ids = {t["id"] for t in out_links["topics"]}
bad = sorted({p["topic"] for p in passages} - topic_ids)
if bad:
    raise SystemExit(f"topics not in the topic list: {bad}")
named = {n for p in passages for n in p["lean"]} | {n for c in links["claims"] for n in c.get("lean", [])}
if sent:
    named |= set(sent["statement_file_declarations"])
# Plain titles: the paper page's own, and for the declarations the ties name, the first other page's.
if not sent:
    out_links["plain"].update(links.get("plain", {}))
for src in extra:
    for k, v in src.get("plain", {}).items():
        if k in named:
            out_links["plain"].setdefault(k, v)
for src in [links, *extra]:
    for k, v in src.get("notes", {}).items():
        if k in named:
            out_links["notes"].setdefault(k, v)

# The Lean: the modules that hold the named declarations, and their import closure in the project.
lean_dir = a.page / "lean"
index = json.loads((a.page / "generated/lean.json").read_text())
module_of = {d["name"]: d["module"] for d in index["declarations"]}
named = {n for p in passages for n in p["lean"]} | {n for c in links["claims"] for n in c.get("lean", [])}
missing = sorted(n for n in named if n not in module_of)
todo = sorted({module_of[n] for n in named if n in module_of})
seen = set()
while todo:
    mod = todo.pop()
    if mod in seen:
        continue
    path = lean_dir / (mod.replace(".", "/") + ".lean")
    if not path.is_file():
        continue
    seen.add(mod)
    for imp in re.findall(r"^import\s+(\S+)", path.read_text(), re.M):
        if (lean_dir / (imp.replace(".", "/") + ".lean")).is_file():
            todo.append(imp)

if a.out.exists():
    shutil.rmtree(a.out)
(a.out / "lean").mkdir(parents=True)
# Every module of the authors' Breakdown library, not only the closure the ties need: companion pages
# (the library guides) read all of it.
seen |= {str(f.relative_to(lean_dir).with_suffix("")).replace("/", ".") for f in (lean_dir / "Breakdown").rglob("*.lean")}
for mod in sorted(seen):
    rel = mod.replace(".", "/") + ".lean"
    (a.out / "lean" / rel).parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(lean_dir / rel, a.out / "lean" / rel)
for name in ("lean-toolchain", "lakefile.toml", "lake-manifest.json"):
    if (lean_dir / name).is_file():
        shutil.copyfile(lean_dir / name, a.out / "lean" / name)
shutil.copytree(a.copy / "figures", a.out / "figures")
# Lean's own report (dependencies, axioms) travels with the page for the converter's lean facts.
(a.out / "generated").mkdir()
# The paper page's report holds the modules it links to; the other pages' reports add the rest, by name.
report = json.loads((a.page / "generated/lean.json").read_text())
have = {d["name"] for d in report["declarations"]}
for extra_page in a.also:
    path = extra_page / "generated/lean.json"
    if not path.is_file():
        continue
    other = json.loads(path.read_text())
    for d in other.get("declarations", []):
        if d["name"] not in have:
            have.add(d["name"])
            report["declarations"].append(d)
    report["modules"] = sorted(set(report.get("modules", [])) | set(other.get("modules", [])))
report["selection"] = (report.get("selection", "") + " Rows of the other Navier–Stokes pages' reports are added by name, unchanged.").strip()
(a.out / "generated/lean.json").write_text(json.dumps(report, ensure_ascii=False))
(a.out / "paper.md").write_text(md)
toml = (a.page / "paper.toml").read_text()
toml = toml.replace('[paper]\n', '[paper]\nmarkdown = "paper.md"\n', 1)
(a.out / "paper.toml").write_text(toml)
if a.sentences:
    # Optional reading aids, carried unchanged for the reader's later design pass: what the Lean does
    # in each section and statement file, the conventions, and the cards to start from.
    (a.out / "notes").mkdir(exist_ok=True)
    for source, name in (("reading_aids.json", "section-aids.json"), ("glossary.json", "glossary.json"),
                         ("showcase.json", "showcase.json")):
        if (a.sentences / source).is_file():
            shutil.copyfile(a.sentences / source, a.out / "notes" / name)
    # Our own Lean statements (proved from the authors' library), and the comparisons they add to
    # existing cards: carried as one file, shown apart from the authors' Lean.
    ours = a.sentences / "our_lean"
    if (ours / "declarations.json").is_file():
        (a.out / "notes" / "ours.json").write_text(json.dumps({
            "schema": 1,
            "meaning": "Our own Lean statements, proved from the authors' Lean library; not the authors' Lean.",
            "declarations": json.loads((ours / "declarations.json").read_text()),
            "comparisons": json.loads((ours / "ties.json").read_text())["comparisons"],
            # Later checks readers may ask about, keyed by the Lean constant they concern.
            **({"checks": json.loads((ours / "checks.json").read_text())} if (ours / "checks.json").is_file() else {}),
            # Forms stated but not yet proved, each with what a proof still needs.
            **({"open_targets": json.loads((ours / "open_targets.json").read_text())["open_targets"]}
               if (ours / "open_targets.json").is_file() else {})},
            ensure_ascii=False))
if a.sentences and (a.sentences / "ENCODING.md").is_file():
    # The guide to how the Lean encodes the paper's objects, published as it stands.
    (a.out / "guide.md").write_text((a.sentences / "ENCODING.md").read_text())
(a.out / "links.json").write_text(json.dumps(out_links, ensure_ascii=False, indent=1))
print(json.dumps({"passages": len(passages), "widened_to_whole_formulas": len(widened), "claims": len(links["claims"]), "lean_modules": len(seen),
                  "named": len(named), "named_not_in_report": missing[:20], "plain": len(out_links["plain"]),
                  "notes": len(out_links["notes"])}, indent=1))
