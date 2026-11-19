#!/usr/bin/env python3
"""Build examples/erdos257/evidence-graph.json (graph schema 1.2) deterministically.

Inputs, all read-only:
  * the pinned export of wcook04/plectis-erdos at 3368d1e (`--export`): the papers'
    evidence mapping evidence/paper_evidence.json, the Comparator receipts it
    cites, and the three papers' PDF and TeX bytes;
  * `--whatran`: workflow_runs.json and receipts.json, the GitHub Actions run
    records gathered with `gh` on 19 November 2026;
  * examples/erdos257/authored/argument.json: the steps of the proofs and which
    step uses which, written by an AI agent from the pinned papers;
  * the vendored Lean tree and source-lock.json in this example.

Mechanical records (paper results, Lean declarations and the edges between them)
are copied from the evidence mapping. Authored records and edges come only from
argument.json. Outputs: evidence-graph.json, authored/evidence-status.json and
the files under verification/. Rerunning with the same inputs gives the same bytes.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import shutil
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]
REPO = "https://github.com/wcook04/plectis-erdos"
REV = "3368d1e69467aec111eb3244843ad3542171ff96"
LEAN_PIN = "436f55ebdafa67e4af0fff79f621c13f2ded12bf"
CORPUS = "https://github.com/wcook04/plectis-erdos-lean"
CORPUS_REV = "cc7e541cf2081c6fef5a5e377d52e365e33b01eb"
RAW = f"https://raw.githubusercontent.com/wcook04/plectis-erdos/{REV}/"
SHORT_ID = "erdos-257-mersenne-support-subseries"
LONG_ID = "erdos257-mersenne-reasoning-surface"
PAPERS = {
    "short": ("paper/257/erdos-257-mersenne-support-subseries", "Irrationality criteria for Lambert subseries"),
    "expository": ("paper/257/erdos257-expository-sums-never-fractions", "Why certain sums of 1/(2^n-1) are irrational"),
    "long": ("paper/257/erdos257-mersenne-reasoning-surface",
             "Reciprocal Mersenne subseries: support criteria, finite arithmetic and conditional orbit problems"),
}
# Short-paper results whose long-record statement is the same mathematical
# statement (compared side by side): one record carries both labels.
SAME_STATEMENT = {"thm:variable-fractional-cover": "thm:257-variable-fractional-cover",
                  "res:mixed-supports": "thm:257-mixed-supports"}
# A long-record result that shares a declaration with a short-paper result but
# states something different; joined by a `cites` edge with a note.
OVERLAP = {"thm:257-weighted": ("res:weighted-support",
           "The long record's Theorem 1.1 and the short paper's Theorem 1.2 share the fixed-base "
           "irrationality clause and the Lean declaration divisibilityWeightedClaim. The long "
           "statement adds cofinal returns $0<\\Delta_{b,A}(m)<\\varepsilon$; the short statement "
           "adds the base-two condition (W) at every base and heredity. Neither printed statement "
           "contains the other, so the two are kept as separate records joined by this reference.")}
GOALS = ["short.res-mixed-supports", "short.res-weighted-support", "short.thm-variable-fractional-cover",
         "short.res-reciprocal-support", "short.res-period"]
AI = "Claude (Anthropic), an AI agent"
AI_SCOPE = (f"Scope: written by {AI} from the pinned papers at {REV[:12]}; "
            "no independent review of this edge has been recorded.")
MAPPING_TOOL = "Copied from the papers' evidence mapping (plectis-paper-evidence/2); no review by this example"
LITERATURE = {
    "erdos1948": ("P. Erdős, On arithmetical properties of Lambert series, J. Indian Math. Soc. 12 (1948), 63–66",
                  "urn:bibliography:erdos1948-lambert-series", "1948"),
    "erdos1968": ("P. Erdős, On the irrationality of certain series, Math. Student 36 (1968), 222–226 (issued 1969)",
                  "https://users.renyi.hu/~p_erdos/1969-09.pdf", "1968"),
    "erdos1975": ("P. Erdős, Some problems and results on the irrationality of the sum of infinite series, J. Math. Sci. 10 (1975), 1–7",
                  "urn:bibliography:erdos1975-irrationality-infinite-series", "1975"),
    "duverneytachiya": ("D. Duverney and Y. Tachiya, Refinement of the Chowla–Erdős method and linear independence of certain Lambert series, Forum Math. 31 (2019), no. 6, 1557–1566",
                        "https://doi.org/10.1515/forum-2018-0299", "2019"),
    "taoteravainen2025": ("T. Tao and J. Teräväinen, Quantitative correlations and some problems on prime factors of consecutive integers, arXiv:2512.01739v2",
                          "https://arxiv.org/abs/2512.01739v2", "arXiv:2512.01739v2"),
    "kanekosuzukitachiya": ("H. Kaneko, Y. Suzuki and Y. Tachiya, Refinements of Erdős's irrationality criterion for certain sparse infinite series, arXiv:2601.20743v1 (2026)",
                            "https://arxiv.org/abs/2601.20743v1", "arXiv:2601.20743v1"),
    "lucatachiya2014independence": ("F. Luca and Y. Tachiya, Linear independence of certain Lambert series, Proc. Amer. Math. Soc. 142 (2014), no. 10, 3411–3419",
                                    "https://doi.org/10.1090/S0002-9939-2014-12102-2", "2014"),
    "vanassche2001": ("W. Van Assche, Little q-Legendre polynomials and irrationality of certain Lambert series, Ramanujan J. 5 (2001), 295–310",
                      "https://doi.org/10.1023/A:1012930828917", "2001"),
}
CITATION_LOCATORS = {  # citation id -> (source, locator)
    "erdos1948": ("erdos1948", "the full series at every integer base"),
    "erdos1968_p222": ("erdos1968", "p. 222: pairwise coprime supports of finite reciprocal sum; the remark that coprimality can be removed, without details"),
    "erdos1968_p226": ("erdos1968", "p. 226: fractional parts of powers times the value of the series"),
    "erdos1975": ("erdos1975", "Theorem 1"),
    "duverneytachiya": ("duverneytachiya", "Section 2, (2.3)–(2.9); Corollary 1.2 and Example 1.1, p. 4 of the author preprint"),
    "taoteravainen2025": ("taoteravainen2025", "Theorem 1.3, p. 4"),
    "kanekosuzukitachiya": ("kanekosuzukitachiya", "Theorems 1 and 3"),
    "lucatachiya2014independence": ("lucatachiya2014independence", "linear-independence results cited for perfect powers"),
    "vanassche2001": ("vanassche2001", "Lemma 1 and (34)–(35)"),
}


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def dumps(value) -> str:
    return json.dumps(value, indent=2, ensure_ascii=False) + "\n"


def write(path: Path, text: str) -> str:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")
    return sha(text.encode("utf-8"))


def tex_markdown(text: str) -> str:
    """GitHub math dialect of the evidence mapping -> $...$ / $$...$$ for the reader."""
    text = re.sub(r"\$`(.+?)`\$", lambda m: "$" + m.group(1) + "$", text, flags=re.S)
    text = re.sub(r"``` math\n(.*?)\n```", lambda m: "$$\n" + m.group(1).strip() + "\n$$", text, flags=re.S)
    text = re.sub(r"\\label\{[^}]*\}", "", text)
    text = re.sub(r"\\(begin|end)\{equation\*?\}", "", text)
    return re.sub(r"\n\s*\n(?=\s*\$\$)", "\n", text).strip()


def flat(value) -> list[str]:
    if value is None:
        return []
    if isinstance(value, str):
        return [value]
    return [item for part in value for item in flat(part)]


def record_id(side: str, label: str) -> str:
    return f"{side}." + re.sub(r"[^A-Za-z0-9.-]+", "-", label).strip("-")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--export", type=Path, required=True)
    parser.add_argument("--whatran", type=Path, required=True)
    args = parser.parse_args()
    export, whatran = args.export, args.whatran
    mapping_bytes = (export / "evidence/paper_evidence.json").read_bytes()
    mapping = json.loads(mapping_bytes)
    papers = {p["paper_id"]: p for p in mapping["papers"]}
    short_rows = papers[SHORT_ID]["results"]
    long_rows = papers[LONG_ID]["results"]
    argument_bytes = (HERE / "authored/argument.json").read_bytes()
    argument = json.loads(argument_bytes)
    lock = json.loads((HERE / "source-lock.json").read_text())
    locked = {row["path"]: row for row in lock["files"]}

    sources, citations, nodes, edges, evidence, notes = {}, {}, {}, [], {}, []

    def source(sid, **row):
        sources[sid] = {"id": sid, **row}

    def cite(cid, title, url, source_id, locator):
        citations[cid] = {"id": cid, "title": title, "url": url, "source_id": source_id, "locator": locator}

    def node(nid, kind, label, status, **extra):
        if nid in nodes:
            raise SystemExit(f"duplicate node {nid}")
        nodes[nid] = {"id": nid, "kind": kind, "label": label, "status": status,
                      "assumption_ids": [], "evidence_ids": [], "citation_ids": [], **extra}

    def ev(eid, kind, status, tool, details, *, sources_=(), subjects=(), command=(), receipt=None):
        if eid in evidence:
            raise SystemExit(f"duplicate evidence {eid}")
        evidence[eid] = {"id": eid, "kind": kind, "status": status, "command": list(command), "tool": tool,
                         "source_ids": sorted(set(sources_)), "subject_ids": sorted(set(subjects)),
                         "details": details}
        if receipt:
            evidence[eid]["receipt_path"], evidence[eid]["receipt_sha256"] = receipt

    def edge(src, dst, kind, evidence_ids):
        edges.append({"from": src, "to": dst, "kind": kind, "evidence_ids": sorted(set(evidence_ids))})

    # ---- sources: papers, mapping, repositories, literature, authored file
    for stage, (stem, title) in PAPERS.items():
        for ext in ("pdf", "tex"):
            data = (export / f"{stem}.{ext}").read_bytes()
            source(f"paper.{stage}.{ext}", kind="file", url=RAW + f"{stem}.{ext}", revision=REV,
                   license="CC-BY-4.0", redistribution="reference_only", sha256=sha(data))
    source("evidence_mapping", kind="file", url=RAW + "evidence/paper_evidence.json", revision=REV,
           license="Apache-2.0", redistribution="reference_only", sha256=sha(mapping_bytes))
    for name in ("evidence/comparator/associations.json", "evidence/erdos-257-mersenne-support-subseries.md"):
        source("evidence." + Path(name).stem, kind="file", url=RAW + name, revision=REV, license="Apache-2.0",
               redistribution="reference_only", sha256=sha((export / name).read_bytes()))
    source("plectis_erdos", kind="repository", url=REPO, revision=REV, license="Apache-2.0",
           redistribution="reference_only")
    source("plectis_erdos_lean_pin", kind="repository", url=REPO, revision=LEAN_PIN, license="Apache-2.0",
           redistribution="reference_only")
    source("comparator_corpus", kind="repository", url=CORPUS, revision=CORPUS_REV, license="Apache-2.0",
           redistribution="reference_only")
    for lid, (title, url, revision) in LITERATURE.items():
        source(f"literature.{lid}", kind="literature", url=url, revision=revision, license="NOASSERTION",
               redistribution="reference_only")
    source("authored_argument", kind="file", url="urn:sha256:" + sha(argument_bytes), revision=sha(argument_bytes),
           license="Apache-2.0", redistribution="original", sha256=sha(argument_bytes), path="authored/argument.json")
    for cid, (lid, locator) in CITATION_LOCATORS.items():
        cite(cid, LITERATURE[lid][0], LITERATURE[lid][1], f"literature.{lid}", locator)

    def lean_source(path: str) -> str:
        local = "upstream/" + path
        if local not in locked:
            raise SystemExit(f"declaration file not vendored: {path}")
        sid = "lean:" + path[len("lean/"):]
        if sid not in sources:
            source(sid, kind="file", url=RAW + path, revision=REV, license="Apache-2.0",
                   redistribution="vendored", sha256=locked[local]["sha256"], path=local)
        return sid

    def paper_cite(stage, cid, locator, page=None):
        stem, title = PAPERS[stage]
        cite(cid, title, RAW + f"{stem}.pdf" + (f"#page={page}" if page else ""), f"paper.{stage}.pdf", locator)
        return cid

    # ---- local verification records (this example)
    from lean_exposition.intake import audit_sources
    audit = audit_sources(lock, HERE)
    audit_sha = write(HERE / "verification/audit-sources.json",
                      dumps({"command": ["lean-exposition", "audit-sources", "examples/erdos257/source-lock.json",
                                         "--root", "examples/erdos257"], "result": audit}))
    not_run = {
        "recorded_by": AI,
        "date": "2026-11-19",
        "not_run": [
            {"check": "lake build", "reason": "Not run for this example: the machine had about 3 GB of free disk, too little for Mathlib and the build. The vendored Lean is a subset of the repository and is not a complete Lake package."},
            {"check": "Comparator", "reason": "Not run for this example: comparator, landrun and lean4export are not installed on the machine."},
            {"check": "lean-exposition extract", "reason": "Not run: it needs a built Lean project."},
        ],
        "what_was_run": "lean-exposition audit-sources (byte hashes of the vendored files) and lean-exposition lean-index (a source-text scan, not an elaboration).",
    }
    not_run_sha = write(HERE / "verification/not-run-locally.json", dumps(not_run))
    lean_sources_all = []
    ev("source_bytes_audited", "source_hash", "passed", "lean-exposition audit-sources",
       f"All {audit['files']} locked files ({audit['bytes']} bytes) under examples/erdos257/upstream match the SHA-256 and byte length recorded in source-lock.json at {REV}. This checks bytes only.",
       sources_=["plectis_erdos"], command=["lean-exposition", "audit-sources", "examples/erdos257/source-lock.json", "--root", "examples/erdos257"],
       receipt=("verification/audit-sources.json", audit_sha))
    for eid, kind, cmd, text in (
        ("lean_build_not_run_locally", "lean_build", ["lake", "build"],
         "No Lean build was run for this example. Builds recorded by the repository's own GitHub Actions workflows are kept as platform observations."),
        ("comparator_not_run_locally", "comparator", ["comparator"],
         "No Comparator check was run for this example. The replay receipts of run 35935225572 are kept as platform observations."),
        ("extraction_not_run_locally", "extraction", ["lean-exposition", "extract"],
         "No dependency extraction was run; the Lean index is a source-text scan."),
    ):
        ev(eid, kind, "not_run", "not run for this example", text, sources_=["plectis_erdos"], command=cmd,
           receipt=("verification/not-run-locally.json", not_run_sha))

    # ---- mechanical records: results and their declarations
    status_sidecar = {}
    declarations = {}

    def add_declaration(row, unfold_of=None):
        name = row["name"]
        nid = "lean." + name
        if nid in nodes:
            return nid
        sid = lean_source(row["path"])
        lean_sources_all.append(sid)
        statement = row.get("statement") or row.get("text")
        cid = f"cite.{nid}"
        cite(cid, name, f"{REPO}/blob/{LEAN_PIN}/{row['path']}#L{row['line']}", sid, f"{row['path']}, line {row['line']}")
        node(nid, "declaration", name, "unverified", source_id=sid, declaration=name, statement=statement,
             locator=f"{row['path']}, line {row['line']}", citation_ids=[cid],
             evidence_ids=["source_bytes_audited", "lean_build_not_run_locally", "comparator_not_run_locally",
                           "extraction_not_run_locally"],
             boundary=("Status unverified in this example: no build or extraction receipt of this tool binds "
                       "it. Outside observations are listed among its evidence."))
        declarations[nid] = row
        return nid

    def add_result(side, row, *, extra_rows=()):
        nid = record_id(side, row["label"])
        all_rows = [(side, row), *extra_rows]
        kind = "goal" if nid in GOALS else "claim"
        cids = []
        for s, r in all_rows:
            stage = "short" if s == "short" else "long"
            cids.append(paper_cite(stage, f"cite.{record_id(s, r['label'])}",
                                   f"{r['printed_kind']} {r['number']}, p. {r['page']} (label {r['label']}; {r['source']})",
                                   r["page"]))
        locator = "; ".join(f"{'Short paper' if s == 'short' else 'Long record'} {r['printed_kind']} {r['number']}, "
                            f"p. {r['page']}, label {r['label']}" for s, r in all_rows)
        status_sidecar[nid] = [{
            "paper": "short" if s == "short" else "long", "label": r["label"], "anchor": r["anchor"],
            "printed": f"{r['printed_kind']} {r['number']}", "page": r["page"], "tex_source": r["source"],
            "title": r["title"], "lean_status": r["lean"]["status"], "relation_note": r["lean"].get("relation_note"),
            "reason": r["lean"].get("reason"), "comparator_status": r["comparator"]["status"],
            "declarations": [{"name": d["name"], "path": d["path"], "line": d["line"],
                              "unfolds": [{"name": u["name"], "path": u["path"], "line": u["line"]} for u in d.get("unfolds", [])]}
                             for d in r["lean"]["declarations"]],
            "statement_sha256": r["statement_sha256"]} for s, r in all_rows]
        title = row["title"]
        printed = f"{row['printed_kind']} {row['number']}" + (f" ({title})" if title else "")
        label = printed if side == "short" else f"Long record {printed}"
        boundary = {"exact": "The evidence mapping records a Lean proof of exactly this statement.",
                    "exact_or_stronger": "The evidence mapping records a Lean statement that implies the printed one.",
                    "none": "The evidence mapping records no Lean proof of the whole statement."}
        statuses = sorted({r["lean"]["status"] for _, r in all_rows})
        node(nid, kind, label, "unverified", source_id=f"paper.{'short' if side == 'short' else 'long'}.pdf",
             locator=locator, statement=tex_markdown(row["statement_markdown"]), citation_ids=cids,
             boundary=" ".join(boundary[s] for s in statuses) + " Lean status per paper is kept in authored/evidence-status.json.")
        decls = []
        for _, r in all_rows:
            for d in r["lean"]["declarations"]:
                decls.append(add_declaration(d))
                for u in d.get("unfolds", []):
                    decls.append(add_declaration(u))
        if decls:
            eid = f"mapping.{nid}"
            notes_text = " ".join(f"{'Short paper' if s == 'short' else 'Long record'} {r['label']}: lean.status {r['lean']['status']}."
                                  + (f" Relation note: {r['lean']['relation_note']}" if r['lean'].get('relation_note') else "")
                                  for s, r in all_rows)
            ev(eid, "semantic_review", "not_run", MAPPING_TOOL,
               f"The papers' evidence mapping names these Lean declarations for {label}. {notes_text} "
               f"Sources: evidence/paper_evidence.json at {REV[:12]}. Scope: copied from the papers' evidence mapping; "
               "this example did not review the correspondence.",
               sources_=["evidence_mapping"], subjects=[nid, *decls])
            nodes[nid]["evidence_ids"].append(eid)
            for d in dict.fromkeys(decls):
                edge(nid, d, "formalizes", [eid])
        return nid

    long_by_label = {r["label"]: r for r in long_rows}
    merged_long = set(SAME_STATEMENT.values())
    for row in short_rows:
        extra = [("long", long_by_label[SAME_STATEMENT[row["label"]]])] if row["label"] in SAME_STATEMENT else []
        add_result("short", row, extra_rows=extra)
    for row in long_rows:
        if row["label"] not in merged_long:
            add_result("long", row)
    for long_label, (short_label, note) in OVERLAP.items():
        a, b = record_id("long", long_label), record_id("short", short_label)
        eid = f"relation.{a}.{b}"
        ev(eid, "semantic_review", "not_run", f"Statement comparison written by {AI}",
           f"{note} {AI_SCOPE}", sources_=["paper.short.pdf", "paper.long.pdf"], subjects=[a, b])
        edge(a, b, "cites", [eid])

    # ---- authored records
    for lit in argument["literature"]:
        node(lit["id"], "claim", lit["label"], "external", source_id=f"literature.{CITATION_LOCATORS[lit['citation']][0]}",
             locator=lit["locator"], statement=lit["statement"], citation_ids=[lit["citation"]],
             boundary=f"Cited result; not proved in these papers. Quoted from the {lit['quoted_in']}.")
    exp_stem, exp_title = PAPERS["expository"]
    for step in argument["steps"] + argument["open"]:
        stage = step["source"]
        cid = paper_cite(stage, f"cite.{step['id']}", step["locator"])
        node(step["id"], "claim", step["label"], step.get("status", "unverified"), source_id=f"paper.{stage}.pdf",
             locator=step["locator"], statement=step["statement"], citation_ids=[cid],
             boundary=step.get("boundary", f"A step of the argument, written by {AI} from the paper's own wording."))
    paper_cite("expository", "cite.exp.thm-main", "Theorem 1, p. 2 (label thm:main)", 2)
    node("exp.thm-main", "claim", "Exposition Theorem 1 (base two, reciprocal-summable exponents)", "unverified",
         source_id="paper.expository.pdf", locator="Exposition Theorem 1, p. 2, label thm:main",
         statement=("Let $n_1<n_2<\\dots$ be an infinite sequence of positive integers. If $\\sum_{k=1}^{\\infty}1/n_k<\\infty$, "
                    "then $\\sum_{k=1}^{\\infty}\\frac1{2^{n_k}-1}$ is irrational."),
         citation_ids=["cite.exp.thm-main"],
         boundary="The exposition has no evidence mapping. Its Appendix A.6 names the Lean theorem irrational_erdosSupportSeries_of_summable_reciprocal, which states every integer base b ≥ 2.")
    ev("relation.exp.thm-main.short.res-reciprocal-support", "semantic_review", "not_run", f"Statement comparison written by {AI}",
       "The exposition's Theorem 1 is the case $b=2$ of the short paper's Theorem A.1; Appendix A.5 of the exposition cites "
       "\"[shortpaper, Theorem A.1]\" for every integer base. " + AI_SCOPE,
       sources_=["paper.expository.pdf", "paper.short.pdf"], subjects=["exp.thm-main", "short.res-reciprocal-support"])
    edge("exp.thm-main", "short.res-reciprocal-support", "cites", ["relation.exp.thm-main.short.res-reciprocal-support"])

    def authored_edge(src, dst, kind, text, stage):
        if src not in nodes or dst not in nodes:
            raise SystemExit(f"unknown endpoint in {src} -> {dst}")
        eid = f"warrant.{src}.{dst}"
        ev(eid, "semantic_review", "not_run", f"Argument edge written by {AI}; independent semantic acceptance not run",
           f"{text} Sources: {PAPERS[stage][1]}, pinned at {REV[:12]}. {AI_SCOPE}",
           sources_=[f"paper.{stage}.pdf", "authored_argument"], subjects=[src, dst])
        edge(src, dst, kind, [eid])

    stage_of = {s["id"]: s["source"] for s in argument["steps"] + argument["open"]}
    for step in argument["steps"]:
        for use in step.get("uses", []):
            authored_edge(step["id"], use["to"], "supports", use["warrant"], step["source"])
    for src, uses in argument["results"].items():
        for use in uses:
            authored_edge(src, use["to"], "supports", use["warrant"], "expository" if src.startswith("exp.") else "short")
    for src, uses in argument["open_uses"].items():
        for use in uses:
            authored_edge(src, use["to"], "cites", use["warrant"], stage_of[src])
    for credit in argument["credits"]:
        authored_edge(credit["from"], credit["to"], "cites", credit["note"],
                      "expository" if credit["from"].startswith("exp.") else "short")
    for nid, cids in argument["result_citations"].items():
        for cid in cids:
            if cid not in citations:
                raise SystemExit(f"unknown citation {cid}")
            if cid not in nodes[nid]["citation_ids"]:
                nodes[nid]["citation_ids"].append(cid)

    # ---- outside observations: Comparator replay receipts and GitHub Actions runs
    receipts_meta = {r["entry"]: r for r in json.loads((whatran / "receipts.json").read_text())["receipts"]}
    by_entry = {}
    for row in short_rows + long_rows:
        for check in (row["comparator"].get("checks") or []):
            by_entry.setdefault(check["entry"], {"receipt": check["receipt"], "declarations": set(), "pairs": set()})
            by_entry[check["entry"]]["declarations"].add("lean." + check["declaration"])
            by_entry[check["entry"]]["pairs"].add((check["declaration"], check["challenge"]["declaration"],
                                                   check["solution"]["declaration"]))
    index_rows = []
    for entry in sorted(by_entry):
        info = by_entry[entry]
        data = (export / info["receipt"]).read_bytes()
        local = f"verification/comparator/{Path(info['receipt']).name}"
        (HERE / local).parent.mkdir(parents=True, exist_ok=True)
        (HERE / local).write_bytes(data)
        receipt = json.loads(data)
        outcome = receipt["verification"]["outcome"]
        status = {"passed": "passed", "failed": "failed"}.get(outcome, "unavailable")
        kernels = receipt.get("kernel_acceptance", {})
        subjects = sorted(d for d in info["declarations"] if d in nodes)
        row = {"entry": entry, "receipt_path": local, "receipt_sha256": sha(data),
               "repository": receipt["github"]["repository"], "workflow": receipt["github"]["workflow"],
               "run_id": receipt["github"]["run_id"], "run_attempt": receipt["github"]["run_attempt"],
               "url": f"{CORPUS}/actions/runs/{receipt['github']['run_id']}", "commit": receipt["github"]["sha"],
               "date": receipt["generated_at"], "outcome": outcome, "kernels": kernels,
               "axioms": receipt.get("permitted_axioms"), "lean_toolchain": receipt.get("lean_toolchain"),
               "comparator_lean_toolchain": receipt.get("comparator_lean_toolchain"),
               "theorem_count": receipt.get("theorem_count"),
               "declarations": [d[len("lean."):] for d in subjects],
               "pairs": [{"declaration": a, "challenge": b, "solution": c} for a, b, c in sorted(info["pairs"])],
               "not_established": receipt.get("not_established")}
        index_rows.append(row)
        ev(f"comparator_replay.{entry}", "platform_observation", status,
           "Comparator replay on GitHub Actions (workflow palomar-replay.yml, wcook04/plectis-erdos-lean); outside observation",
           f"Corpus entry {entry}, run {row['run_id']} attempt {row['run_attempt']} at {row['commit']}, receipt written {row['date']}: "
           f"outcome {outcome}; Lean default kernel {'accepted' if kernels.get('lean_default') else 'not recorded as accepted'}, "
           f"nanoda {'accepted' if kernels.get('nanoda') else 'not recorded as accepted'}; permitted axioms {', '.join(row['axioms'] or [])}. "
           f"It compares {row['theorem_count']} Challenge/Solution theorem pairs; the subjects are the declarations the evidence mapping associates with this entry. "
           "This example did not rerun it. The receipt lists as not established: " + "; ".join(flat(row["not_established"])) + ".",
           sources_=["comparator_corpus"], subjects=subjects, receipt=(local, row["receipt_sha256"]))
        for d in subjects:
            nodes[d]["evidence_ids"].append(f"comparator_replay.{entry}")
    write(HERE / "verification/comparator-replay-35935225572.json",
          dumps({"what": "Comparator replay receipts of run 35935225572 that the papers' evidence mapping cites, one row per corpus entry.",
                 "run": {"repository": "wcook04/plectis-erdos-lean", "run_id": "35935225572",
                         "url": f"{CORPUS}/actions/runs/35935225572", "commit": CORPUS_REV,
                         "attempts": [{"attempt": 1, "conclusion": "failure",
                                       "note": "shard-03 (E1049 entries, not #257) stopped by a runner shutdown; the shards holding the E257 entries succeeded and wrote these receipts"},
                                      {"attempt": 2, "conclusion": "success", "note": "re-run of the failed shard; 21 of 21 jobs succeeded"}]},
                 "entries": index_rows}))

    runs = json.loads((whatran / "workflow_runs.json").read_text())
    pe = runs["plectis_erdos"]["selected_runs_with_jobs"]
    pl = runs["plectis_erdos_lean"]
    # Runs whose checked-out lean/ErdosProblems/Erdos257, lean/ErdosProblems/Erdos249 and
    # lean/Erdos249257 trees have the same Git tree hashes as the pin (checked with the GitHub
    # contents API on 19 November 2026), and whose jobs compiled Lean.
    chosen = [("lean_ci_pin_PR302_head_pass", "Lean CI (PR #302 head; the nearest full CI run to the pin)"),
              ("lean_ci_PR366_last_lean_touch_pass", "Lean CI (PR #366 head); its build job took 31 s, and whether Lean work was skipped was not established"),
              ("lean_ci_PR431_head_before_main_tip_pass", "Lean CI (PR #431 head, merged as 3368d1e)"),
              ("coverage_pin_merge_b034152", "Compile the paper-coverage Lean modules (at the merge of the pin)"),
              ("coverage_last_lean_touch_3542f64", "Compile the paper-coverage Lean modules"),
              ("coverage_latest", "Compile the paper-coverage Lean modules"),
              ("cache_warm_main_tip_pass", "Warm the main Lean cache (main tip 3368d1e)")]
    run_rows = []
    for key, what in chosen:
        r = pe[key]
        run_rows.append({"repository": "wcook04/plectis-erdos", "key": key, "description": what, **{
            k: r.get(k) for k in ("run_id", "name", "event", "head_branch", "head_sha", "conclusion", "run_attempt",
                                  "created_at", "updated_at", "url", "jobs")}})
    for r in pl["runs_at_evidence_commit_cc7e541"]:
        if r["name"] in ("Lean Convenience", "Lean Release Gate"):
            run_rows.append({"repository": "wcook04/plectis-erdos-lean", "key": f"corpus_build_{r['run_id']}",
                             "description": f"{r['name']} at the Comparator corpus commit", **{
                k: r.get(k) for k in ("run_id", "name", "event", "head_branch", "head_sha", "conclusion", "run_attempt",
                                      "created_at", "updated_at")},
                "url": f"{CORPUS}/actions/runs/{r['run_id']}", "jobs": None})
    rp = pl["selected_runs_with_jobs"]["replay_35935225572"]
    run_rows.append({"repository": "wcook04/plectis-erdos-lean", "key": "replay_35935225572_attempt1",
                     "description": "Palomar Comparator replay, attempt 1: failed in shard-03 (E1049 entries, not #257) after a runner shutdown",
                     "run_id": rp["run_id"], "name": rp["name"], "event": rp["event"], "head_branch": rp["head_branch"],
                     "head_sha": rp["head_sha"], "conclusion": "failure", "run_attempt": 1, "created_at": rp["created_at"],
                     "updated_at": "2026-09-24T01:13:00Z", "url": rp["url"], "jobs": None})
    run_rows.append({"repository": "wcook04/plectis-erdos-lean", "key": "replay_35935225572_attempt2",
                     "description": "Palomar Comparator replay, attempt 2: re-ran the failed shard; the run the papers pin",
                     **{k: rp.get(k) for k in ("run_id", "name", "event", "head_branch", "head_sha", "conclusion",
                                               "run_attempt", "created_at", "updated_at", "url", "jobs")}})
    runs_sha = write(HERE / "verification/actions-runs.json",
                     dumps({"what": ("GitHub Actions runs that compiled or checked the #257 Lean at the pinned trees, "
                                     "copied from run records gathered with gh on 2026-11-19. Outcomes are the platform's "
                                     "recorded conclusions; this example reran none of them."),
                            "pin_trees": {"lean/ErdosProblems/Erdos257": "151977adf68a9570422f303740c96ec288bf61f0",
                                          "lean/ErdosProblems/Erdos249": "4b7cad9d0bbc618b7183670f43c606e5d5bcff0d",
                                          "lean/Erdos249257": "916ebf6358fac94ef8d41e55442abb9610481983"},
                            "runs": run_rows}))
    shows = {
        "lean_ci": ("Lean CI built the library roots Erdos249257 and ErdosProblems and ran its axiom audits and Comparator units at a commit whose #257 Lean trees equal the pin's.",
                    "Its build reused cached outputs; which vendored modules were compiled in this run, and whether each paper statement is right, is not shown."),
        "coverage": ("The paper-coverage Lean modules compiled at a commit whose #257 Lean trees equal the pin's.",
                     "It prints no axioms and runs no Comparator; it does not show that the statements match the papers."),
        "warm": ("The main tip 3368d1e built its supported roots and saved the Lean cache.",
                 "It prints no axioms and runs no Comparator."),
        "corpus": ("The Comparator corpus built at its evidence commit cc7e541.",
                   "A build of the corpus; it is not a Comparator verdict."),
        "replay": ("Comparator replayed every corpus entry, Challenge against Solution, with the Lean default kernel and nanoda.",
                   "Whether each Challenge statement says what the papers say."),
    }
    for row in run_rows:
        status = {"success": "passed", "failure": "failed"}.get(row["conclusion"], "unavailable")
        family = ("replay" if "replay" in row["key"] else "corpus" if row["key"].startswith("corpus") else
                  "coverage" if row["key"].startswith("coverage") else "warm" if row["key"].startswith("cache") else "lean_ci")
        receipt_doc = {"record_type": "github_actions_run", "workflow": row["name"], "repository": row["repository"],
                       "run_id": int(row["run_id"]), "run_attempt": int(row["run_attempt"]), "url": row["url"],
                       "commit": row["head_sha"], "branch": row["head_branch"], "event": row["event"],
                       "started_at": row["created_at"], "completed_at": row["updated_at"],
                       "conclusion": row["conclusion"], "shows": shows[family][0], "does_not_show": shows[family][1],
                       "description": row["description"], "jobs": row.get("jobs")}
        if row["key"] == "replay_35935225572_attempt1":
            receipt_doc["shows"] = "The first attempt failed in shard-03, which holds E1049 entries, after a runner shutdown; the shards holding the E257 entries succeeded and wrote their receipts."
            receipt_doc["does_not_show"] = "Nothing about #257 failed in this attempt; the run passed on its second attempt."
        receipt_rel = f"verification/actions/{row['key']}.json"
        receipt_hash = write(HERE / receipt_rel, dumps(receipt_doc))
        jobs = "; ".join(f"{j['name']} {j['conclusion']}" for j in row.get("jobs") or [])
        ev(f"actions.{row['key']}", "platform_observation", status,
           f"GitHub Actions workflow \"{row['name']}\" on {row['repository']}; outside observation",
           f"{row['description']}. Run {row['run_id']} attempt {row['run_attempt']}, {row['event']} on {row['head_branch']} at "
           f"{row['head_sha']}, {row['created_at']} to {row['updated_at']}: conclusion {row['conclusion']}. {('Jobs: ' + jobs + '.') if jobs else ''} "
           f"URL: {row['url']}. This example did not rerun it.",
           sources_=["plectis_erdos" if row["repository"].endswith("plectis-erdos") else "comparator_corpus"],
           receipt=(receipt_rel, receipt_hash))

    for nid in nodes:
        nodes[nid]["evidence_ids"] = sorted(set(nodes[nid]["evidence_ids"]))
        nodes[nid]["citation_ids"] = sorted(set(nodes[nid]["citation_ids"]))
    evidence["source_bytes_audited"]["subject_ids"] = sorted(n for n in nodes if nodes[n]["kind"] == "declaration")
    evidence["source_bytes_audited"]["source_ids"] = sorted({"plectis_erdos", *lean_sources_all})

    notes.extend([
        f"Records of printed results, Lean declarations and the formalizes edges between them are copied from evidence/paper_evidence.json at {REV}; their evidence records carry the tool string \"{MAPPING_TOOL}\".",
        f"Records whose ids begin step., exp.step., context., lit., open. and problem., and every supports or cites edge between records, were written by {AI} from the pinned papers (authored/argument.json); each such edge has its own semantic_review record with status not_run.",
        "Every node has status unverified, open or external: no Lean build or extraction was run by this tool, so no declaration is kernel_checked here. Builds and Comparator runs made by the repository's own GitHub Actions workflows are platform_observation records.",
        "The two short-paper results Theorem 3.1 and Theorem 4.1 have the same statements as long-record Theorems 1.3 and 1.4 and share one record each; short Theorem 1.2 and long Theorem 1.1 differ and are separate records joined by a cites edge.",
        "Erdős Problem #257 is open. The papers prove sufficient conditions for irrationality; none of them characterises the supports in the problem.",
    ])
    graph = {
        "schema_version": "1.2",
        "id": "erdos257-lambert-subseries",
        "title": "Irrationality criteria for Lambert subseries (Erdős Problem #257)",
        "selected_goals": GOALS,
        "sources": [sources[k] for k in sorted(sources)],
        "citations": [citations[k] for k in sorted(citations)],
        "nodes": [nodes[k] for k in sorted(nodes)],
        "edges": sorted(edges, key=lambda e: (e["from"], e["to"], e["kind"])),
        "evidence": [evidence[k] for k in sorted(evidence)],
        "scope": ("Three papers on Erdős Problem #257 by W. Cook, pinned at wcook04/plectis-erdos "
                  f"{REV}: the short paper, the exposition and the long record; the Lean declarations their "
                  f"evidence mapping cites at {LEAN_PIN}; and the Comparator replay of corpus commit {CORPUS_REV}. "
                  "The problem itself remains open."),
        "extraction_status": "not_run",
        "notes": notes,
    }
    write(HERE / "evidence-graph.json", dumps(graph))
    write(HERE / "authored/evidence-status.json",
          dumps({"what": ("Per-record Lean status, relation note and Comparator status copied from the papers' evidence "
                          "mapping, keyed by graph record id. The graph schema has no field for them."),
                 "source": f"evidence/paper_evidence.json at {REV}", "records": status_sidecar}))
    print(json.dumps({"nodes": len(nodes), "edges": len(edges), "evidence": len(evidence),
                      "sources": len(sources), "citations": len(citations)}))


if __name__ == "__main__":
    main()
