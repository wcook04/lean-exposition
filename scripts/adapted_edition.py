#!/usr/bin/env python3
"""Make an adapted edition of a library paper: a second document of the same instance.

An adapted edition is a changed version of the authors' text, set beside it. Every changed
paragraph of its TeX starts with a `% CHANGE <id>` comment, and a public change map
(CHANGES.json) has one row per mark: {id, part, kind, authors, ours, sources, note, status},
where `authors` names the authors' paragraphs ("<heading>#<block>", Proof Reader's paragraph
ids) that the change replaces or sits beside.

    adapted_edition.py convert --paper euler --edition DIR --authors-source DIR \
        --reading-copy PROOF_READER/papers/euler/tools/reading_copy.py --pdf MARKED.pdf \
        [--aux-pdf MARKED_AUX.pdf] [--published]
    adapted_edition.py stage <paper>     put an enabled edition into its document slot, for a build
    adapted_edition.py unstage <paper>   take it out again, restoring the slot's placeholder files
    adapted_edition.py enabled <paper>   exit 0 when the edition is to be built (published, or LX_PREVIEW_ADAPTED=1)

`convert` sets the edition's reading copy from its TeX exactly as the authors' reading copy was
set from theirs (Proof Reader's reading_copy.py), aligns the two texts paragraph by paragraph,
gives each changed paragraph its change, carries every phrase tie whose paragraph is unchanged,
and checks that every change is marked. It writes instances/<paper>/adapted/:

    edition.json      the document entry (kind "adapted", of the main document) and the flag
                      `published`; while it is false a build leaves the edition out
    paper.md          the reading copy, with passage markers and section anchors
    correspondence.json, references.json, phrases.json, figures/
    changes.json      adapted-changes/1: every change with both texts, and the paragraph alignment
    paper.pdf         the edition's PDF with changes marked; aux.pdf the auxiliary note's

It stops, writing nothing, unless: the authors' reading copy is reproduced byte for byte from
their TeX; every `% CHANGE` mark has a CHANGES.json row and the reverse; every paragraph that
differs from the authors' text belongs to a change; every change shows in at least one paragraph
of the edition; and no TeX line differs from the authors' source outside a marked paragraph.
"""
from __future__ import annotations

import argparse
import difflib
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))
sys.path.insert(0, str(ROOT / "scripts"))
MARK = re.compile(r"^% CHANGE (\S+)\s*$")
PUBLIC_FIELDS = ("id", "part", "kind", "authors", "ours", "sources", "note", "status")
STAGED = (("paper.md", "papers/{slot}/paper.md"), ("correspondence.json", "papers/{slot}/correspondence.json"),
          ("paper.pdf", "papers/{slot}/paper.pdf"), ("figures", "papers/{slot}/figures"),
          ("phrases.json", "alignment/phrases-{slot}.json"), ("references.json", "alignment/references-{slot}.json"),
          ("changes.json", "alignment/changes-{slot}.json"),
          # Written by the build (site/scripts/topic-colours.ts); removed again when the edition is unstaged.
          ("colours.json", "alignment/colours-{slot}.json"))


# Words of a private build that must never reach a public change map: transcription paragraph ids,
# review-card ids, local file names of the literature, and dotted names from the Lean (a Lean file's
# path, as a source, is the authors' own place and may stand).
PRIVATE_WORDS = (("a transcription paragraph id", re.compile(r"\bp[0-9]{4}\b")),
                 ("a local file name", re.compile(r"(?<![/\w.-])(?:[\w.-]+\.pdf:|\d+\.pdf\b)")),
                 ("a review-card id", re.compile(r"\bac-[0-9]|p::")),
                 ("a dotted Lean name", re.compile(r"\b[A-Z][A-Za-z0-9_']*\.(?!(?:lean|md|json|toml|tex|py)\b)[A-Za-z_][A-Za-z0-9_']*\b")))


def private_words(changes: list[dict]) -> list[str]:
    """The change map's sources and notes, read for words that belong to the private build."""
    problems = []
    for c in changes:
        texts = [("note", c.get("note") or "")] + [("source", " ".join(str(s.get(k) or "") for k in ("ref", "where", "title")))
                                                    for s in c.get("sources", [])]
        for field, text in texts:
            for what, pattern in PRIVATE_WORDS:
                m = pattern.search(text)
                if m:
                    problems.append(f"{c['id']}: its {field} has {what} ({m.group(0)!r})")
    return problems


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def dumps(value) -> str:
    return json.dumps(value, ensure_ascii=False, indent=1) + "\n"


# ------------------------------------------------------------------ TeX: marks and the source diff

def tex_files(root: Path) -> list[str]:
    return sorted(p.relative_to(root).as_posix() for p in root.rglob("*.tex"))


def marks_in(root: Path) -> list[tuple[str, int, str]]:
    """Every `% CHANGE <id>` line: (file, line number from 1, id), in file order."""
    out = []
    for rel in tex_files(root):
        for k, line in enumerate((root / rel).read_text(encoding="utf-8").splitlines(), 1):
            m = MARK.match(line)
            if m:
                out.append((rel, k, m.group(1)))
    return out


def paragraphs(lines: list[str]) -> list[tuple[int, int]]:
    """TeX paragraphs: runs of non-blank lines, as [start, stop) line indices."""
    out, start = [], None
    for k, line in enumerate(lines + [""]):
        if line.strip() and start is None:
            start = k
        elif not line.strip() and start is not None:
            out.append((start, k))
            start = None
    return out


def unmarked_tex_changes(authors: Path, edition: Path) -> tuple[list[str], dict[str, int]]:
    """Every TeX paragraph of the edition that differs from the authors' source must be one a
    `% CHANGE` mark opens, or follow one directly in the same run of changed paragraphs; and every
    mark must open a paragraph that differs. Returns the problems and, per mark, how many changed
    TeX paragraphs it covers."""
    problems, covered = [], {}
    own = set(tex_files(authors))
    for rel in tex_files(edition):
        new = (edition / rel).read_text(encoding="utf-8").splitlines()
        old = (authors / rel).read_text(encoding="utf-8").splitlines() if rel in own else []
        # The marks themselves are comments; the comparison is of everything else.
        mark_at, body = {}, []
        for line in new:
            m = MARK.match(line)
            if m:
                mark_at[len(body)] = m.group(1)
            else:
                body.append(line)
        changed = set()
        paras = paragraphs(body)
        para_of = {k: n for n, (a, b) in enumerate(paras) for k in range(a, b)}
        is_changed = [False] * len(paras)
        for tag, i1, i2, j1, j2 in difflib.SequenceMatcher(None, old, body, autojunk=False).get_opcodes():
            if tag == "equal":
                continue
            text_lines = [k for k in range(j1, j2) if body[k].strip()]
            for k in text_lines:
                is_changed[para_of[k]] = True
            if not text_lines:
                # A cut, or only blank lines added or removed: the paragraph the cut was made in, or
                # the one before the blank lines.
                before = [n for n, (a, b) in enumerate(paras) if a < max(j1, 1) and a <= j1]
                if before:
                    is_changed[before[-1]] = True
        opener = {}
        for at, cid in mark_at.items():
            # A mark opens the paragraph that starts at or after it.
            n = next((n for n, (a, b) in enumerate(paras) if a >= at), None)
            if n is None:
                problems.append(f"{rel}: mark {cid} opens no paragraph")
                continue
            opener[n] = cid
            if not is_changed[n]:
                problems.append(f"{rel}: mark {cid} opens a paragraph that is the same as the authors'")
        current = None
        for n, ch in enumerate(is_changed):
            if n in opener:
                current = opener[n]
            if not ch:
                current = None
                continue
            if current is None:
                a, b = paras[n]
                problems.append(f"{rel}: lines {a + 1}-{b} differ from the authors' source with no CHANGE mark")
                continue
            covered[current] = covered.get(current, 0) + 1
    return problems, covered


# ------------------------------------------------------------------ reading copies

def reading_copy(script: Path, source: Path, scratch: Path, name: str) -> tuple[str, Path]:
    """Set a reading copy from a TeX tree laid out as the authors' manuscript/source, with Proof
    Reader's reading_copy.py run unchanged in a scratch page folder. Returns the Markdown and its
    figures folder."""
    page = scratch / name / "papers/euler"
    (page / "tools").mkdir(parents=True)
    shutil.copy(script, page / "tools/reading_copy.py")
    up = scratch / name / "up/manuscript/source"
    shutil.copytree(source, up, ignore=shutil.ignore_patterns("CHANGES.json"))
    (scratch / "no-ties.json").write_text('{"ties": []}\n')
    run = subprocess.run([sys.executable, str(page / "tools/reading_copy.py"), str(scratch / name / "up"), str(scratch / "no-ties.json")],
                         capture_output=True, text=True)
    if run.returncode:
        raise SystemExit(f"reading_copy.py failed on {name}:\n{run.stderr[-2000:]}")
    return (page / "paper.md").read_text(encoding="utf-8"), page / "figures"


def source_blocks(md: str, scratch: Path) -> list[dict]:
    path = scratch / f"blocks-{sha(md.encode())[:12]}.md"
    path.write_text(md, encoding="utf-8")
    run = subprocess.run(["node", str(ROOT / "site/scripts/source-blocks.mjs"), str(path)], capture_output=True, text=True, check=True)
    return json.loads(run.stdout)


def placed_blocks(plain: str, marked: str, scratch: Path) -> list[dict]:
    """The paragraphs of a reading copy, with ids from its plain form and places in its marked form
    (the library's paper.md, which only adds passage markers and anchors between paragraphs)."""
    lines = plain.split("\n")
    out, cursor = [], 0
    offsets = [0]
    for line in marked.split("\n"):
        offsets.append(offsets[-1] + len(line.encode("utf-8")) + 1)
    for b in source_blocks(plain, scratch):
        text = "\n".join(lines[b["line"] - 1:b["end_line"] - 1]).rstrip("\n")
        at = marked.find(text, cursor)
        if at < 0:
            raise SystemExit(f"paragraph {b['heading']}#{b['block']} not found in the library's reading copy")
        cursor = at + len(text)
        line = marked.count("\n", 0, at) + 1
        start_byte = len(marked[:at].encode("utf-8"))
        out.append({"id": f"{b['heading']}#{b['block']}", "kind": b["kind"], "text": text,
                    "lines": [line, line + text.count("\n") + 1],
                    "bytes": [start_byte, start_byte + len(text.encode("utf-8"))]})
    return out


# ------------------------------------------------------------------ changes onto paragraphs

def assign(changes: list[dict], authors: list[dict], adapted: list[dict]) -> tuple[list[dict], list[list], list[str]]:
    """Align the two texts paragraph by paragraph and give every differing paragraph of the
    edition its change. Returns the alignment rows, each change's adapted paragraph indices, and
    the problems."""
    problems = []
    by_id = {b["id"]: i for i, b in enumerate(authors)}
    owner = {}
    for c in changes:
        for a in c["authors"]:
            if a not in by_id:
                problems.append(f"{c['id']}: no paragraph {a} in the authors' text")
            owner.setdefault(by_id.get(a), []).append(c["id"])
    sm = difflib.SequenceMatcher(None, [b["text"] for b in authors], [b["text"] for b in adapted], autojunk=False)
    rows, shown = [], {c["id"]: [] for c in changes}
    replaced = {c["id"]: [] for c in changes}
    first_section = next((i for i, b in enumerate(authors) if re.match(r"\d", b["id"])), 0)
    for tag, i1, i2, j1, j2 in sm.get_opcodes():
        if tag == "equal":
            rows += [{"authors": authors[i]["id"], "adapted": adapted[j]["id"], "change": None}
                     for i, j in zip(range(i1, i2), range(j1, j2))]
            continue
        claim = list(dict.fromkeys(cid for i in range(i1, i2) for cid in owner.get(i, [])))
        if not claim and i1 == i2:
            # Added paragraphs: the change that names a paragraph beside the place, or, before
            # the first section, the edition's credit.
            near = [cid for i in (i1 - 1, i1) for cid in owner.get(i, [])]
            near = [cid for cid in near if not shown[cid]]
            credit = [c["id"] for c in changes if c["kind"] == "edition-credit" and not c["authors"]]
            claim = near[:1] or (credit if i1 <= first_section else [])
        if not claim:
            problems.append(f"paragraphs {[a['id'] for a in authors[i1:i2]]} -> {[b['id'] for b in adapted[j1:j2]]} differ with no change")
            continue
        if len(claim) == 1:
            pick = {j: claim[0] for j in range(j1, j2)}
        elif i2 - i1 == j2 - j1:
            # As many paragraphs on each side: each keeps its place, with the change of its authors' paragraph.
            pick = {}
            for i, j in zip(range(i1, i2), range(j1, j2)):
                mine = owner.get(i, [])
                if len(mine) != 1:
                    problems.append(f"paragraph {authors[i]['id']} has {len(mine)} changes in a run of {len(claim)}")
                    continue
                pick[j] = mine[0]
        else:
            problems.append(f"changes {claim} share a run of {i2 - i1} -> {j2 - j1} paragraphs; cannot place each")
            continue
        for j, cid in pick.items():
            shown[cid].append(j)
        for i in range(i1, i2):
            for cid in owner.get(i, []):
                replaced[cid].append(i)
        # The alignment: a paragraph of the authors' and one of the edition's, side by side while both last.
        for k in range(max(i2 - i1, j2 - j1)):
            i, j = i1 + k, j1 + k
            rows.append({"authors": authors[i]["id"] if i < i2 else None, "adapted": adapted[j]["id"] if j < j2 else None,
                         "change": pick.get(j) if j < j2 else (owner.get(i) or [None])[0]})
    # A change the reading copy does not show (a change to the TeX's build lines alone) is marked
    # on the paragraph it names, which reads the same in both texts.
    pair = {r["authors"]: r["adapted"] for r in rows if r["authors"] and r["adapted"]}
    adapted_at = {b["id"]: j for j, b in enumerate(adapted)}
    for c in changes:
        if shown[c["id"]]:
            continue
        hosts = [adapted_at[pair[a]] for a in c["authors"] if a in pair]
        if hosts:
            shown[c["id"]] = hosts[:1]
            c["text_unchanged"] = True
        else:
            problems.append(f"{c['id']}: shows in no paragraph of the edition")
    for c in changes:
        c["_replaced"] = sorted(set(replaced[c["id"]]))
    return rows, [sorted(set(shown[c["id"]])) for c in changes], problems


# ------------------------------------------------------------------ phrase ties carried over

def carry_ties(ties: list[dict], authors_md: str, adapted_md: str, authors: list[dict], adapted: list[dict], rows: list[dict]):
    """Each phrase tie whose paragraph is unchanged, placed at the same words of the edition."""
    from lean_exposition.alignment import _phrase_span
    pair = {r["authors"]: r["adapted"] for r in rows if r["authors"] and r["adapted"] and r["change"] is None}
    a_by, e_by = {b["id"]: b for b in authors}, {b["id"]: b for b in adapted}
    a_bytes, e_bytes = authors_md.encode("utf-8"), adapted_md.encode("utf-8")
    carried, dropped = [], []

    def byte_of(text: str, char: int) -> int:
        return len(text[:char].encode("utf-8"))

    for tie in ties:
        try:
            s, e = _phrase_span(authors_md, tie)
        except ValueError:
            dropped.append((tie["id"], "not placed in the authors' text"))
            continue
        sb = byte_of(authors_md, s)
        home = next((b for b in authors if b["bytes"][0] <= sb < b["bytes"][1]), None)
        if home is None or home["id"] not in pair:
            dropped.append((tie["id"], "its paragraph is changed" if home else "outside any paragraph"))
            continue
        twin = e_by[pair[home["id"]]]
        want = twin["bytes"][0] + (sb - home["bytes"][0])
        row = {k: v for k, v in tie.items()}
        try:
            got = byte_of(adapted_md, _phrase_span(adapted_md, row)[0])
        except ValueError:
            got = None
        if got != want:
            # Pin it with the shortest text before it that occurs once in the edition.
            start_char = len(e_bytes[:want].decode("utf-8"))
            fixed = None
            for n in (24, 48, 96, 192, 384):
                after = adapted_md[max(0, start_char - n):start_char]
                if after and adapted_md.count(after) == 1:
                    trial = {**row, "after": after}
                    try:
                        if byte_of(adapted_md, _phrase_span(adapted_md, trial)[0]) == want:
                            fixed = trial
                            break
                    except ValueError:
                        pass
            if not fixed:
                dropped.append((tie["id"], "not placed at its words in the edition"))
                continue
            row = fixed
        carried.append(row)
    return carried, dropped


# ------------------------------------------------------------------ convert

def convert(args) -> None:
    from from_proof_reader import reading_copy as library_copy, references
    inst = ROOT / "instances" / args.paper
    instance = json.loads((inst / "instance.json").read_text())
    main_doc = next(d for d in instance["documents"] if d.get("main"))
    slot = args.slot
    if slot in {d["slot"] for d in instance["documents"]} or args.slug in {d.get("slug") for d in instance["documents"]}:
        raise SystemExit(f"slot {slot} is taken by another document of {args.paper}")
    rows_in = json.loads((args.edition / "CHANGES.json").read_text())
    changes = [{k: r[k] for k in PUBLIC_FIELDS} for r in rows_in]
    problems = private_words(changes)
    marks = marks_in(args.edition)
    mark_ids = [m[2] for m in marks]
    ids = [c["id"] for c in changes]
    if len(set(mark_ids)) != len(mark_ids):
        problems.append("a CHANGE id is used twice in the TeX")
    if sorted(mark_ids) != sorted(ids):
        problems.append(f"marks without a row: {sorted(set(mark_ids) - set(ids))}; rows without a mark: {sorted(set(ids) - set(mark_ids))}")
    for c in changes:
        where = next((m for m in marks if m[2] == c["id"]), None)
        if where and where[0] != c["ours"]:
            problems.append(f"{c['id']}: marked in {where[0]}, listed in {c['ours']}")
    tex_problems, _ = unmarked_tex_changes(args.authors_source, args.edition)
    problems += tex_problems

    with tempfile.TemporaryDirectory(prefix="adapted-", dir=args.scratch) as tmp:
        scratch = Path(tmp)
        authors_plain, _ = reading_copy(args.reading_copy, args.authors_source, scratch, "authors")
        adapted_plain, figures = reading_copy(args.reading_copy, args.edition, scratch, "adapted")
        authors_md = (inst / "papers" / main_doc["slot"] / "paper.md").read_text(encoding="utf-8")
        # The library's copy only adds passage markers and anchors between paragraphs, and how it adds
        # them may have changed since the paper was converted; the words must be the same.
        bare = lambda text: re.sub(r"\n{3,}", "\n\n", re.sub(r'^(<!-- /?passage:[^>]* -->|<a id="[^"]*"></a>)\n', "", text, flags=re.M)).strip()
        if bare(library_copy(authors_plain, [])[0]) != bare(authors_md):
            raise SystemExit("the authors' reading copy is not reproduced from their TeX; the alignment would not hold")
        adapted_md, sections, _ = library_copy(adapted_plain, [])
        # The sections are the authors', in the same order; their passages keep the authors' names, which
        # the library's converter may since have spelled differently.
        authors_order = re.findall(r"^<!-- passage:(\S+) -->$", authors_md, re.M)
        if len(authors_order) != len(sections):
            raise SystemExit(f"the edition has {len(sections)} sections, the authors' text {len(authors_order)}")
        for sec, name in zip(sections, authors_order):
            if sec["anchor"] != name:
                adapted_md = adapted_md.replace(f"<!-- passage:{sec['anchor']} -->", f"<!-- passage:{name} -->", 1)
                adapted_md = adapted_md.replace(f"<!-- /passage:{sec['anchor']} -->", f"<!-- /passage:{name} -->", 1)
                sec["anchor"] = name
        authors_blocks = placed_blocks(authors_plain, authors_md, scratch)
        adapted_blocks = placed_blocks(adapted_plain, adapted_md, scratch)
        rows, shown, assign_problems = assign(changes, authors_blocks, adapted_blocks)
        problems += assign_problems
        if problems:
            raise SystemExit("not every change is marked:\n  " + "\n  ".join(problems))

        phrases = json.loads((inst / f"alignment/phrases-{main_doc['slot']}.json").read_text())
        carried, dropped = carry_ties(phrases["ties"], authors_md, adapted_md, authors_blocks, adapted_blocks, rows)

        out = inst / "adapted"
        if out.exists():
            shutil.rmtree(out)
        (out / "figures").mkdir(parents=True)
        for fig in sorted(figures.iterdir()):
            shutil.copy(fig, out / "figures" / fig.name)
    (out / "paper.md").write_text(adapted_md, encoding="utf-8")
    data = adapted_md.encode("utf-8")

    # The paper mapping: the authors' passages, section by section, over the edition's text.
    corr = json.loads((inst / "papers" / main_doc["slot"] / "correspondence.json").read_text())
    by_anchor = {p["anchor"]: p for p in corr["passages"]}
    data = adapted_md.encode("utf-8")
    passages, cursor = [], 0
    for sec in sections:
        marker, end = f"<!-- passage:{sec['anchor']} -->", f"<!-- /passage:{sec['anchor']} -->"
        start = adapted_md.index(marker, cursor) + len(marker)
        stop = adapted_md.index(end, start)
        cursor = stop
        if sec["anchor"] not in by_anchor:
            raise SystemExit(f"section {sec['anchor']} of the edition has no section in the authors' text")
        passages.append({**by_anchor[sec["anchor"]], "text_sha256": sha(adapted_md[start:stop].encode("utf-8"))})
    corr.update(stage=slot, path=f"papers/{slot}.md", content_sha256=sha(data), passages=passages,
                review_notes=["An adapted edition of the authors' paper: its sections and numbered results are the authors'; "
                              "every change is marked, and no change has been reviewed by the authors."])
    (out / "correspondence.json").write_text(dumps(corr))
    (out / "references.json").write_text(dumps(references(adapted_md, slot)))
    part = dict(phrases["parts"][0])
    part["lines"] = [1, adapted_md.count("\n") + 1]
    (out / "phrases.json").write_text(dumps({**phrases, "paper": slot, "parts": [part], "ties": carried, "removed": [],
                                              "meaning": phrases["meaning"] + " In the adapted edition, a tie is carried only where its paragraph is the authors' unchanged."}))

    a_by = {b["id"]: b for b in authors_blocks}
    for c, js in zip(changes, shown):
        c["adapted"] = [adapted_blocks[j]["id"] for j in js]
        c["adapted_lines"] = [adapted_blocks[j]["lines"] for j in js]
        c["adapted_bytes"] = [adapted_blocks[j]["bytes"] for j in js]
        c["adapted_text"] = "\n\n".join(adapted_blocks[j]["text"] for j in js)
        was = [authors_blocks[i]["id"] for i in c.pop("_replaced")]
        c["replaced"] = was
        c["authors_text"] = "\n\n".join(a_by[a]["text"] for a in was) if was else ""
        c["authors_lines"] = [a_by[a]["lines"] for a in was]
    order = {b["id"]: j for j, b in enumerate(adapted_blocks)}
    changes.sort(key=lambda c: (order[c["adapted"][0]], c["id"]))
    (out / "changes.json").write_text(dumps({
        "schema": "adapted-changes/1", "paper": args.paper, "authors": main_doc["slot"], "adapted": slot,
        "meaning": "Every change of the adapted edition, in the order of its text: the public change map's fields, the "
                   "authors' paragraphs it replaces (`replaced`, with their text) and the edition's paragraphs that show it "
                   "(`adapted`, with lines and bytes of the edition's paper.md). `paragraphs` aligns the two texts paragraph "
                   "by paragraph; `change` is null where the paragraph is the authors' unchanged.",
        "changes": changes,
        "paragraphs": [{**r, "authors_lines": a_by[r["authors"]]["lines"] if r["authors"] else None,
                        "adapted_lines": adapted_blocks[order[r["adapted"]]]["lines"] if r["adapted"] else None} for r in rows],
        "ties": {"carried": len(carried), "not_carried": len(dropped)}}))

    pdf = args.pdf.read_bytes()
    shutil.copy(args.pdf, out / "paper.pdf")
    # Read as a companion document of the paper (its own page and slot, docs/library-architecture.md),
    # marked as the adapted edition of the main document.
    document = {"id": "adapted", "slot": slot, "slug": args.slug, "kind": "companion", "adapted": True, "of": main_doc["id"],
                "title": main_doc["title"], "noun": "adapted edition",
                "group": "edition", "group_title": "Adapted edition", "order": 0,
                "credit": args.credit, "published": bool(args.published),
                "pdf": {"file": "paper.pdf", "name": "adapted-edition-marked.pdf", "label": "PDF with changes marked",
                        "sha256": sha(pdf), "bytes": len(pdf)}}
    if args.aux_pdf:
        aux = args.aux_pdf.read_bytes()
        shutil.copy(args.aux_pdf, out / "aux.pdf")
        document["aux_pdf"] = {"file": "aux.pdf", "name": "adapted-auxiliary-note-marked.pdf",
                               "label": "Auxiliary note, PDF with changes marked", "sha256": sha(aux), "bytes": len(aux)}
    (out / "edition.json").write_text(dumps({"schema": "adapted-edition/1", "published": bool(args.published), "document": document}))
    print(f"adapted edition of {args.paper}: {len(changes)} changes on {sum(len(c['adapted']) for c in changes)} paragraphs, "
          f"{len(carried)} phrase ties carried, {len(dropped)} not carried (their paragraphs changed); "
          f"published={bool(args.published)}")


# ------------------------------------------------------------------ build staging

def edition(paper: str) -> dict | None:
    path = ROOT / "instances" / paper / "adapted/edition.json"
    return json.loads(path.read_text()) if path.is_file() else None


def enabled(paper: str) -> bool:
    e = edition(paper)
    return bool(e and (e.get("published") or os.environ.get("LX_PREVIEW_ADAPTED") == "1"))


def stage(paper: str) -> None:
    inst = ROOT / "instances" / paper
    slot = edition(paper)["document"]["slot"]
    taken = {d["slot"]: d.get("id") for d in json.loads((inst / "instance.json").read_text())["documents"]}
    if slot in taken:
        # Never displace a document the paper already reads in this slot.
        raise SystemExit(f"the adapted edition's slot {slot} is taken by {paper}'s document {taken[slot]!r}; "
                         f"convert it into a free slot (--slot) before building it")
    keep = inst / "adapted/.staged"
    if keep.exists():
        unstage(paper)
    keep.mkdir()
    for name in ("absent.md", "absent.json"):
        p = inst / "papers" / slot / name
        if p.exists():
            shutil.move(p, keep / name)
    for src, dst in STAGED:
        s, d = inst / "adapted" / src, inst / dst.format(slot=slot)
        if d.exists():
            backup = keep / dst.format(slot=slot).replace("/", "__")
            shutil.move(d, backup)
        if s.is_dir():
            shutil.copytree(s, d)
        elif s.exists():
            d.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy(s, d)
    # The build recomputes the topic colours of every paper that shares a topic list, and with the
    # edition staged the authors' colour file counts one more sharer. Keep the files as they were.
    kept = keep / "kept"
    kept.mkdir()
    for f in [*sorted((inst / "alignment").glob("colours-*.json")), ROOT / "site/tests/fixtures/topic-colours.json"]:
        if f.is_file():
            shutil.copy(f, kept / f.relative_to(ROOT).as_posix().replace("/", "__"))
    print(f"staged the adapted edition of {paper} in slot {slot}")


def unstage(paper: str) -> None:
    inst = ROOT / "instances" / paper
    keep = inst / "adapted/.staged"
    if not keep.exists():
        return
    slot = edition(paper)["document"]["slot"]
    for src, dst in STAGED:
        d = inst / dst.format(slot=slot)
        if d.is_dir():
            shutil.rmtree(d)
        elif d.exists():
            d.unlink()
    if (keep / "kept").is_dir():
        for f in (keep / "kept").iterdir():
            shutil.copy(f, ROOT / f.name.replace("__", "/"))
        shutil.rmtree(keep / "kept")
    for f in keep.iterdir():
        target = inst / "papers" / slot / f.name if f.name.startswith("absent.") else inst / f.name.replace("__", "/")
        shutil.move(f, target)
    keep.rmdir()


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    c = sub.add_parser("convert")
    c.add_argument("--paper", required=True)
    c.add_argument("--edition", type=Path, required=True, help="the edition's TeX, laid out as the authors' manuscript/source, with CHANGES.json")
    c.add_argument("--authors-source", type=Path, required=True, help="the authors' manuscript/source")
    c.add_argument("--reading-copy", type=Path, required=True, help="Proof Reader's papers/<page>/tools/reading_copy.py")
    c.add_argument("--pdf", type=Path, required=True, help="the edition's PDF with changes marked")
    c.add_argument("--aux-pdf", type=Path)
    c.add_argument("--slot", default="adapted", help="the edition's own document slot (a companion page name)")
    c.add_argument("--slug", default="adapted")
    c.add_argument("--credit", required=True, help="the edition's credit sentence, verbatim")
    c.add_argument("--published", action="store_true", help="build and publish the edition (off: a build leaves it out)")
    c.add_argument("--scratch", type=Path, default=None)
    for name in ("stage", "unstage", "enabled"):
        sub.add_parser(name).add_argument("paper")
    args = ap.parse_args()
    if args.cmd == "convert":
        convert(args)
    elif args.cmd == "stage":
        stage(args.paper)
    elif args.cmd == "unstage":
        unstage(args.paper)
    else:
        sys.exit(0 if enabled(args.paper) else 1)


if __name__ == "__main__":
    main()
