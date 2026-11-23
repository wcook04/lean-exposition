#!/usr/bin/env python3
"""Build the RH PDF and its linked Lean into the Library's native reader assets."""
from __future__ import annotations

import argparse
from collections import defaultdict
from contextlib import ExitStack, contextmanager
from hashlib import sha256
import json
import os
from pathlib import Path
import runpy
import shutil
import subprocess
from tempfile import TemporaryDirectory
from urllib.parse import urlencode

from lean_exposition.alignment import FIDELITY, FIDELITY_KEYS
from lean_exposition.bundle import scaffold
from lean_exposition.contracts import encoded
from lean_exposition.proof_index import ProofIndex
from lean_exposition.proof_sources import ProofSources

ROOT = Path(__file__).resolve().parents[1]
INSTANCE = ROOT / "instances/riemann-hypothesis"
SITE = ROOT / "site"
GOAL = "rh.result"
VERDICTS = FIDELITY - {"held", "unassessed"}
STATEMENT_RELATIONS = {"same": "states", "stronger": "contains", "weaker": "part"}


def read(file):
    return json.loads(file.read_bytes())


def write(file, data):
    file.parent.mkdir(parents=True, exist_ok=True)
    file.write_text(json.dumps(data, ensure_ascii=False) + "\n", encoding="utf-8")


def record(name):
    return "lean." + sha256(name.encode()).hexdigest()[:24]


def graph_for(reader, manifest, proof, catalogue, names, archive_runs):
    upstream, revision = manifest["lean"]["upstream"], manifest["lean"]["revision"]
    paper = manifest["paper"]
    root = reader["root"]
    sources = [
        {"id": "paper", "kind": "repository", "url": paper["repository"], "license": paper["license"],
         "revision": paper["revision"], "redistribution": "reference_only"},
        {"id": "lean", "kind": "repository", "url": upstream, "license": "NOASSERTION",
         "revision": revision, "redistribution": "reference_only"},
        {"id": "compiled", "kind": "repository", "url": manifest["lean"]["dataset"], "license": "NOASSERTION",
         "revision": "v0.2.1", "redistribution": "reference_only"},
    ]
    evidence, log_sources, receipt_files = [], {}, {}
    by_declaration = defaultdict(list)
    declaration_reports = {"rh.archive.statements": "print_href", "rh.archive.replay": "replay_href"}
    if archive_runs["paper_revision"] != paper["revision"]:
        raise ValueError("RH archive checks use a different paper revision")
    for run in archive_runs["runs"]:
        if (run["commit"], run["repository"]) != (paper["revision"], paper["repository"]):
            raise ValueError("RH archive run uses a different source")
        report = declaration_reports.get(run["id"])
        targets = [{"record": record(name), "name": name, "url": row["archive_check"][report]}
                   for name, row in catalogue.items() if report and "archive_check" in row]
        if targets:
            run = {**run, "targets": targets}
            for target in targets:
                by_declaration[target["name"]].append(run["id"])
        source_ids = []
        for log in run["logs"]:
            source_id = "rh.archive.log." + sha256(log["path"].encode()).hexdigest()[:24]
            log_sources[source_id] = {"id": source_id, "kind": "file", "url": log["url"],
                                      "license": "NOASSERTION", "revision": run["commit"],
                                      "redistribution": "reference_only", "sha256": log["sha256"]}
            source_ids.append(source_id)
        path = f'{run["id"]}.json'
        receipt_files[path] = encoded(run)
        evidence.append({
            "id": run["id"], "kind": "platform_observation", "status": run["status"], "tool": run["tool"],
            "source_ids": source_ids, "subject_ids": [GOAL, *(target["record"] for target in targets)], "command": run["command"],
            "details": f'{run["date"]}. {run["outcome"]}. {run["shows"]} {run["does_not_show"]}',
            "receipt_path": f"verification/{path}", "receipt_sha256": sha256(receipt_files[path]).hexdigest(),
        })
    sources.extend(log_sources.values())
    goal = {"id": GOAL, "kind": "goal", "label": "Riemann Hypothesis", "status": "unverified",
            "source_id": "paper", "locator": "§2.3", "statement": "The Riemann Hypothesis as stated in the paper.",
            "assumption_ids": [], "evidence_ids": [item["id"] for item in evidence], "citation_ids": []}
    nodes = [goal] + [
        {"id": record(row["name"]), "kind": "declaration", "label": names[row["name"]], "status": "unverified",
         "source_id": "lean", "declaration": row["name"], "locator": f'{row["path"]}:{row["line"]}',
         "statement": names[row["name"]], "assumption_ids": [], "evidence_ids": by_declaration[row["name"]], "citation_ids": []}
        for row in catalogue.values()
    ]
    edges = {(GOAL, record(root), "formalizes"): [root]}
    for row in catalogue.values():
        if not row["in_proof"]:
            continue
        # Follow the actual predecessor chain in the compiled index. A visible
        # edge may pass through declarations outside the paper's catalogue.
        route = proof.neighbourhood(row["name"], 0, 1)["route"][::-1]
        for target in row["uses"]:
            edges[(record(row["name"]), record(target), "supports")] = [row["name"], target]
        seen = [i for i, name in enumerate(route) if name in catalogue]
        for first, last in zip(seen, seen[1:]):
            use, used = route[first], route[last]
            edges.setdefault((record(use), record(used), "supports"), route[first:last + 1])
    return {
        "schema_version": "1.2", "id": "rh-paper-library", "title": paper["title"], "extraction_status": "not_run",
        "selected_goals": [GOAL], "scope": "The displayed map projects the compiled closure onto declarations linked from the paper.",
        "sources": sources, "nodes": nodes, "citations": [], "evidence": evidence, "notes": [],
        "edges": [{"from": left, "to": right, "kind": kind, "evidence_ids": []} for left, right, kind in edges],
    }, {"→".join(key): {
        "route": route,
        "statement_use": key[2] == "supports" and len(route) == 2
        and "type" in catalogue[route[0]]["reference_kinds"].get(route[1], []),
    } for key, route in edges.items()}, receipt_files


def statement_reviews(reviews, manifest):
    """Read AI source comparisons bound to the two revisions they compare."""
    for source in ("paper", "lean"):
        if reviews[f"{source}_revision"] != manifest[source]["revision"]:
            raise ValueError(f"RH statement comparisons use a different {source} revision")
    result = {}
    for row in reviews["reviews"]:
        key = (row["passage"], row["name"])
        note = row["note"]
        fidelity = row.get("fidelity")
        if key in result or not isinstance(note, str) or not note.strip():
            raise ValueError(f"Invalid or duplicate RH review for {key}")
        if fidelity is None:
            result[key] = {"note": note}
        elif fidelity in VERDICTS:
            result[key] = {"fidelity": fidelity, "fidelity_note": note, "fidelity_source": "ai"}
        else:
            raise ValueError(f"Unknown RH statement fidelity {fidelity!r} for {key}")
        if "explanation" in row:
            result[key]["explanation"] = row["explanation"]
    return result


def reading_data(paper, assets, catalogue, names, main, reviews):
    marks = assets["pdf-marks.json"]
    links = assets["passages.json"]["passages"]
    annotations = assets["annotations.json"]["annotations"]
    topics = assets["topics.json"]
    notes = assets["lean-notes.json"]
    lines = assets["lean-lines.json"]["modules"]
    tone = {topic["id"]: topic["tone"] for topic in topics["topics"]}
    records = {}
    for name, row in catalogue.items():
        records[record(name)] = {"short": names[name], "lean": [{
            "name": name, "module": row["module"], "line": row["line"], "end_line": row["end_line"],
            "lines": [row["line"], row["signature_end_line"]], "relation": "part", "note": "",
        }], "statements": []}
    records[GOAL] = {
        "short": "Riemann Hypothesis",
        "lean": [{**records[record(main)]["lean"][0], "relation": "states"}],
        "statements": [],
    }
    ties, ranges, places = [], [], {}
    kept = {}
    unused_reviews = set(reviews)
    for id_, mark in sorted(marks["marks"].items(), key=lambda pair: tuple(map(int, pair[1]["at"][1:].split("-")))):
        link = links.get(id_) or annotations[id_]
        role = "mention" if link["role"] == "reference" else link["role"]
        targets = link["lean"] if isinstance(link["lean"], list) else [link["lean"]]
        rows = []
        for target in targets:
            if not target or target["name"] not in catalogue:
                continue
            key = (id_, target["name"])
            review = reviews.get(key, {})
            unused_reviews.discard(key)
            note = target.get("focus_note", "")
            relation = "part"
            if role == "mention":
                relation = None
            elif role == "statement":
                relation = STATEMENT_RELATIONS.get(review.get("fidelity"))
            if "note" in review:
                note = " ".join(part for part in (review["note"], note) if part)
            elif role == "mention" and not note and not review:
                note = f'This paper reference links to `{target["name"].rsplit(".", 1)[-1]}` in Lean.'
            left, right = target["lines"]
            rows.append({
                "name": target["name"], "module": target["module"], "line": left, "end_line": right,
                "lines": target.get("focus_lines") or target.get("statement_lines") or [left, right],
                "exact_lines": bool(target.get("focus_lines")), "relation": relation,
                "plain": names[target["name"]], "note": note,
                **({"source_review": True} if "note" in review else {}),
                **{key: value for key, value in review.items() if key in FIDELITY_KEYS},
                **({"proof_lines": target["proof_lines"]} if "proof_lines" in target else {}),
            })
        if not rows:
            continue
        name = rows[0]["name"]
        rid = GOAL if id_ == "st:rh" else record(name)
        start, end = map(int, mark["at"][1:].split("-"))
        kept[id_] = {**mark, "record": rid}
        places[id_] = [len(ties), start, end]
        ranges.append((start, end))
        explanation = reviews.get((id_, name), {}).get("explanation")
        ties.append({
            "record": rid, "role": role, "name": name, "plain": names[name], "module": rows[0]["module"],
            "lean": True, "lines": rows[0]["lines"], "relation": rows[0]["relation"], "rows": rows,
            "anchor": None, "at": mark["at"], "phrase": id_, "section": link["section"],
            "topic": link["topic"], "tone": tone.get(link["topic"]),
            **{key: value for key, value in rows[0].items() if key in FIDELITY_KEYS},
            **({"explanation": explanation} if explanation else {}),
        })
        excerpt = paper[start:end].decode()
        if id_ == "st:rh":
            # The PDF text layer orders the denominator before the numerator.
            # Preserve its byte addresses and typeset the fraction from the pinned TeX.
            excerpt = excerpt.replace("Re s = 2 1 .", r"$\operatorname{Re}s=\tfrac{1}{2}$.")
        for target in rows:
            target_record = record(target["name"])
            statement = {
                "paper": "short", "role": role, "markdown": excerpt, "start_byte": start,
                "end_byte": end, "at": mark["at"], "lean": rows, "lean_source": "statement", "anchor": None,
                "section": link["section"], "heading_id": None,
            }
            records[target_record]["statements"].append(statement)
            if rid == GOAL and target["name"] == main:
                records[GOAL]["statements"].append(statement)
    if unused_reviews:
        raise ValueError(f"RH statement comparisons refer to missing ties: {sorted(unused_reviews)}")
    canonical = {record(row["name"]): places[row["canonical"]] for rows in lines.values() for row in rows if row["canonical"] in places}
    if "st:rh" in places:
        canonical[GOAL] = places["st:rh"]
    points = sorted({point for span in ranges for point in span})
    segments = []
    for left, right in zip(points, points[1:]):
        covering = [index for index, (a, b) in enumerate(ranges) if a <= left < right <= b]
        if covering:
            segments.append([left, right, sorted(covering, key=lambda i: ranges[i][1] - ranges[i][0])])
    line_annotations = {}
    for module, rows in lines.items():
        line_annotations[module] = []
        for row in rows:
            sources = notes["sources"].get(row["name"], [])
            line_annotations[module].extend(
                {"lines": source["lean_lines"], "title": source["title"],
                 "text": source.get("reading_note", source["markdown"]),
                 **({"adapted": True} if "reading_note" in source else {}),
                 "url": source["url"], "authors": source["authors"], "licence": source["license"]}
                for source in sources if source.get("lean_lines")
            )
            for link in row["links"]:
                if link["precision"] == "reviewed_span" and link["mark"] in kept:
                    mark = kept[link["mark"]]
                    line_annotations[module].append({"lines": link["lines"], "title": "Read the linked PDF passage",
                                                     "at": mark["at"], "record": mark["record"]})
        if not line_annotations[module]:
            del line_annotations[module]
    page_starts = [0] + [i + 1 for i, byte in enumerate(paper) if byte == 12]
    if len(page_starts) != len(marks["pages"]):
        raise ValueError("Paper text and PDF index have different page counts")
    sections = [
        {**section, "section": section["section"] or f"unnumbered-{i}"}
        for i, section in enumerate(assets["sections.json"]["sections"])
    ]
    marks = {**marks, "marks": kept, "sections": sections, "pageStarts": page_starts}
    return (
        {"records": records, "dictionary": [], "names": names},
        {"layer": "phrases", "topics": topics["topics"], "families": topics["families"],
         "canonical": canonical, "segments": segments, "ties": ties, "passages": [],
         "meaning": "Ties locate the archived PDF and Lean. An AI source comparison is shown where one was recorded."},
        marks,
        line_annotations,
    )


@contextmanager
def staged(path, replacement, temporary):
    """Supply a generated input to the existing build and restore the previous path."""
    old = temporary / f"saved-{len(list(temporary.iterdir()))}"
    present = path.exists() or path.is_symlink()
    path.parent.mkdir(parents=True, exist_ok=True)
    if present:
        path.rename(old)
    try:
        path.symlink_to(replacement, target_is_directory=replacement.is_dir())
        yield
    finally:
        path.unlink(missing_ok=True)
        if present:
            old.rename(path)


PUBLIC_SLUG = "riemann-hypothesis-reader"


def build(paper_dir, index_dir, lean_checkout, *, public=False):
    paper_dir = paper_dir.resolve()
    manifest = read(paper_dir / "manifest.json")
    reader_file = INSTANCE / "reader.json"
    reader = read(reader_file)
    proof = ProofIndex(index_dir)
    sources = ProofSources(lean_checkout, paper_dir, proof, reader_config=reader_file)
    for file, digest in manifest["files"].items():
        if sha256((paper_dir / file).read_bytes()).hexdigest() != digest:
            raise ValueError(f"{file} does not match the paper manifest")
    assets = {file: read(paper_dir / file) for file in manifest["files"] if file.endswith(".json")}
    catalogue = {row["name"]: row for row in sources.names()["declarations"]}
    names = {name: row["display_title"] for name, row in catalogue.items()}
    graph, steps, receipt_files = graph_for(reader, manifest, proof, catalogue, names, assets["archive-runs.json"])
    text = (paper_dir / "paper.txt").read_bytes()
    reviews = statement_reviews(read(INSTANCE / "statement-comparisons.json"), manifest)
    alignment, ties, marks, line_annotations = reading_data(text, assets, catalogue, names, reader["root"], reviews)
    alignment["steps"] = steps
    paper = manifest["paper"]
    lean = manifest["lean"]
    first_statement = marks["marks"]["st:rh"]
    start = "?" + urlencode({"n": GOAL, "l": first_statement["at"], "v": "lean",
                              "view": "pdf", "page": first_statement["boxes"][0][0]})
    overview_page = next(section["page"] for section in assets["sections.json"]["sections"] if section["section"] == "3")
    config = {
        "schema": "library-instance/1", "id": INSTANCE.name, "title": paper["title"], "short_title": "The Riemann Hypothesis",
        "description": "Read Qui Vincit and Fable’s account of Alpöge’s Riemann Hypothesis formalization with links from the paper to the Lean statements and proof dependencies.",
        "authors": paper["authors"], "venue": f'Version {paper["version"]}', "licence": paper["license"],
        "credit_lines": [f'The paper by {" and ".join(paper["authors"])} is shared under {paper["license"]}.'],
        "host": ("Independent reader by Will Cook, candidate edition." if public else
                 "Hosted by Will Cook in his reading library."),
        "review": "Select a highlighted passage to see the corresponding Lean and what the passage does in the argument. AI-assisted comparisons describe how the paper and Lean statements line up. What ran links to the recorded archive checks.",
        "goal": GOAL, "main_lean": reader["root"],
        "levels": ["short"], "level_names": {"short": "Paper"},
        "families": assets["topics.json"]["families"], "topics": assets["topics.json"]["topics"],
        "topic_order": [topic["id"] for topic in assets["topics.json"]["topics"]],
        "source": {"upstream": {"repository": paper["repository"], "commit": paper["revision"],
                                "paper": f'{paper["repository"]}/blob/{paper["revision"]}/paper/main.pdf'},
                   "lean": {"authors": "Levent Alpöge with Claude", "repository": lean["upstream"], "commit": lean["revision"]},
                   "lean_scope": "The whole proof map uses James Shore’s compiled dependency data and displays declarations linked from the paper. A line may represent a chain through declarations omitted from the map. Open a statement’s Graph pane to see its immediate Lean dependencies."},
        "about": [{
            "heading": "Where to start",
            "paragraphs": [
                "Start with Statement 2.1, where the authors spell out the Riemann Hypothesis. "
                "Section 3 then separates the problem into an analytic half and an arithmetic half. "
                "The arithmetic half establishes a bound for a weighted count of prime powers. "
                "The analytic half uses the bound to rule out zeros of Dirichlet $L$-functions to the right of the critical line, with a pole exception for the trivial character at $s=1$.",
                "In Section 4, watch for the two errors $x/m$ and $m$. "
                "Here $x$ is the scale of the count and $m$ is the length of the theta-lift chain. "
                "Choosing $m$ near $\\sqrt{x}$ balances those terms. The bound on the ranks of the lattices controls the third error term. "
                "The windowed Landau theorem is the step from the bound on prime powers to nonvanishing.",
            ],
            "links": [
                {"label": "Read Statement 2.1 beside its Lean", "href": start},
                {"label": "Read Section 3, The shape of the proof", "href": f"?view=pdf&page={overview_page}#pdf-section-3"},
                {"label": "Open the whole proof map", "href": "map/"},
            ],
        }],
        "documents": [{"id": "paper", "slot": "short", "slug": "", "noun": "paper", "main": True, "pdf_only": True,
                       "title": paper["title"], "pdf": {"file": "paper.pdf", "sha256": manifest["files"]["paper.pdf"],
                                                       "bytes": (paper_dir / "paper.pdf").stat().st_size}}],
        "reader": {"publish_receipts": True, "lean": {"owner": "Alpöge’s", "ownerSource": "the pinned Lean community import"}},
    }
    scratch = ROOT / "build"
    scratch.mkdir(exist_ok=True)
    with TemporaryDirectory(prefix="rh-library-", dir=scratch) as tmp:
        work = Path(tmp)
        bundle = work / "bundle"
        edition = work / "edition"
        verification = work / "verification"
        verification.mkdir()
        for file, content in receipt_files.items():
            (verification / file).write_bytes(content)
        scaffold(graph, bundle)
        exporter = runpy.run_path(str(SITE / "scripts/export-static.py"))
        exporter["export"](bundle, edition, oracle=work / "oracle")
        index = read(edition / "index.json")
        # The native paper lens reads each node's direct passage count.
        summary_file = edition / "rh-paper-nodes.json"
        cards = read(edition / index["summaries_by_table"]["nodes"])
        for card in cards:
            count = len(alignment["records"][card["id"]]["statements"])
            if count:
                card["papers"] = [{"stage": "short", "roles": ["mapped_claim"], "direct_passage_count": count}]
        write(summary_file, cards)
        index["summaries_by_table"]["nodes"] = summary_file.name
        for route, file, payload in (
            ("/alignment", "alignment.json", alignment),
            ("/alignment/core", "alignment/core.json", exporter["alignment_core"](alignment)),
            ("/ties/short", "ties/short.json", ties),
            ("/lean/modules", "lean/modules.json", sources.modules()),
            ("/lean/names", "lean/names.json", {key: sources.names()[key] for key in ("modules", "names")}),
        ):
            write(edition / file, payload)
            index["responses"][route] = file
        for slot in ("long", "short", "expository"):
            file = f"alignment/{slot}.json"
            write(edition / file, exporter["alignment_paper"](alignment, slot))
            index["responses"][f"/alignment/{slot}"] = file
        for rid, row in alignment["records"].items():
            file = f"alignment/record/{rid}.json"
            write(edition / file, row)
            index["responses"]["/alignment/record?" + urlencode({"id": rid})] = file
        (edition / "paper.txt").write_bytes(text)
        index["documents"]["short"] = "paper.txt"
        index["proof_source"] = sources.metadata
        if public:
            # The capture carries metadata only. Browsers fetch the original bytes from the
            # immutable upstream revision when the reader opens a module.
            owner_repo = manifest["lean"]["upstream"].removeprefix("https://github.com/").rstrip("/")
            index["proof_source"]["raw_base"] = (
                f'https://raw.githubusercontent.com/{owner_repo}/{manifest["lean"]["revision"]}/'
            )
            for name in sources.names()["modules"]:
                descriptor = sources.module(name)
                del descriptor["source"]
                file = f'lean/module/{sha256(name.encode()).hexdigest()}.json'
                write(edition / file, descriptor)
                index["responses"]["/lean/module?" + urlencode({"name": name})] = file
        write(edition / "index.json", index)
        write(work / "pdf-marks/short.json", marks)
        write(work / "lean-line-annotations.json", line_annotations)
        write(work / "instance.json", config)
        write(work / "addresses.json", {"phrases": {
            tie["phrase"]: {"record": tie["record"], "at": tie["at"]} for tie in ties["ties"]
        }, "results": {}, "pages": {}})
        write(work / "alignment/records.json", {"records": alignment["records"]})
        for slot in ("long", "short", "expository"):
            write(work / f"alignment/references-{slot}.json", {
                "paper": slot, "references": [], "targets": {}, "sources": {},
            })
        doc = work / "papers/short"
        doc.mkdir(parents=True)
        (doc / "paper.pdf").symlink_to(paper_dir / "paper.pdf")
        with ExitStack() as stack:
            for path, replacement in {
                INSTANCE / "evidence-graph.json": bundle / "graph.json",
                INSTANCE / "verification": verification,
                INSTANCE / "alignment": work / "alignment",
                INSTANCE / "papers": work / "papers",
                SITE / "src/instances/library/current.json": work / "instance.json",
                SITE / "public/edition": edition,
                SITE / "public/pdf-marks": work / "pdf-marks",
                SITE / "public/lean-notes.json": paper_dir / "lean-notes.json",
                SITE / "public/lean-line-annotations.json": work / "lean-line-annotations.json",
                SITE / "public/addresses.json": work / "addresses.json",
            }.items():
                stack.enter_context(staged(path, replacement, work))
            subprocess.run(["npm", "run", "build"], cwd=SITE, check=True, env={
                **os.environ, "LX_INSTANCE": "library", "VITE_STATIC_EDITION": "true",
                "VITE_BASE_PATH": f"/{PUBLIC_SLUG}/" if public else f"/library/{INSTANCE.name}/",
                "VITE_PROOF_SOURCE": "true",
                **({"LX_SITE_URL": f"https://wcook04.github.io/{PUBLIC_SLUG}/"} if public else {}),
            })
        # Vite copies public inputs. Keep the shell at the normal Library root.
        dist = SITE / "dist"
        shutil.copyfile(dist / "read/short/index.html", dist / "index.html")
    print(f"RH Library reader built in {SITE / 'dist'}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--paper", type=Path, default=INSTANCE / "edition/paper")
    parser.add_argument("--proof-index", type=Path, required=True)
    parser.add_argument("--lean-source", type=Path, required=True)
    parser.add_argument("--public", action="store_true", help="build the standalone Pages candidate with upstream Lean fetches")
    args = parser.parse_args()
    build(args.paper, args.proof_index, args.lean_source, public=args.public)
