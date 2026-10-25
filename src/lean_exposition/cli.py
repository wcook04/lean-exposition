"""Local command-line interface with optional read-only public-source intake."""
from __future__ import annotations

import argparse
from collections import defaultdict
import json
import sys
import textwrap
from pathlib import Path

from .bundle import STAGES, check_bundle, export_bundle, scaffold
from .contracts import ContractError, read_json, select, validate_graph, write_json
from .consumer import inspect_bundle, inspect_graph, project_corpus, project_graph, project_paper, query_papers
from .extraction import to_graph
from .intake import audit_sources, fetch
from .prove2me import intake_prove2me
from .verification import VerificationError, check_build, extract_dependencies, verify_comparator


def parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(prog="lean-exposition", description="Inspect pinned Lean evidence, prepare scaffolds and package authored exposition.")
    p.add_argument("--version", action="version", version="%(prog)s 0.1.0")
    commands = p.add_subparsers(dest="command", required=True)
    for name in ("validate", "select", "scaffold"):
        cmd = commands.add_parser(name)
        cmd.add_argument("graph", type=Path)
        if name != "validate":
            cmd.add_argument("--out", type=Path, required=True)
        if name == "select":
            cmd.add_argument("--goal", action="append", required=True)
    for name in ("check-bundle", "export"):
        cmd = commands.add_parser(name)
        cmd.add_argument("bundle", type=Path)
        if name == "export":
            cmd.add_argument("--out", type=Path, required=True)
    cmd = commands.add_parser("inspect", help="Inspect a graph and its distinct argument/platform closures")
    cmd.add_argument("graph", type=Path)
    cmd.add_argument("--goal", action="append")
    cmd.add_argument("--view", choices=("declarations", "arguments", "citations", "platform", "provenance"))
    cmd.add_argument("--direction", choices=("prerequisites", "consumers"), default="prerequisites")
    cmd.add_argument("--include-assumptions", action="store_true")
    cmd = commands.add_parser("inspect-bundle", help="Inspect a validated directory or ZIP bundle")
    cmd.add_argument("bundle", type=Path)
    cmd.add_argument("--paper", choices=STAGES, help="Project one paper and its graph correspondence")
    cmd.add_argument("--passage", action="append", help="Select a passage anchor (repeatable; requires --paper)")
    cmd = commands.add_parser("inspect-corpus", help="Read the full recorded corpus and shared paper subgraphs")
    cmd.add_argument("bundle", type=Path)
    cmd.add_argument("--expect-manifest", help="Require this exact manifest SHA-256 (64 lowercase hex characters)")
    cmd = commands.add_parser("query-papers", help="Query source-bound paper, section and passage correspondence")
    cmd.add_argument("bundle", type=Path)
    cmd.add_argument("--paper", choices=STAGES, help="Limit to one paper; omitted means all three")
    cmd.add_argument("--passage", action="append", help="Passage anchor (repeatable; requires --paper)")
    cmd.add_argument("--section", action="append", help="Exact section ref from a paper view (repeatable; requires --paper)")
    cmd.add_argument("--node", action="append", help="Find passages mapped to a graph node (repeatable)")
    cmd.add_argument("--relation", choices=("direct", "prerequisites"), default="direct",
                     help="Match direct mapping fields or their recorded prerequisite reachability")
    cmd.add_argument("--expect-manifest", help="Require this exact manifest SHA-256 (64 lowercase hex characters)")
    cmd.add_argument("--format", choices=("json", "text"), default="json",
                     help="Full JSON (default), or a reader summary of the same validated query")
    cmd = commands.add_parser("assemble", help="Validate and package existing paper/mapping pairs")
    cmd.add_argument("graph", type=Path)
    for stage in ("long", "short", "expository"):
        cmd.add_argument("--" + stage, nargs=2, type=Path, required=True, metavar=("MARKDOWN", "MAPPING"))
    cmd.add_argument("--out", type=Path, required=True)
    for name in ("audit-sources", "fetch"):
        cmd = commands.add_parser(name)
        cmd.add_argument("lock", type=Path)
        cmd.add_argument("--root" if name == "audit-sources" else "--out", type=Path, required=True)
    cmd = commands.add_parser("extract", help="Run the packaged Lean extractor on trusted prebuilt modules")
    cmd.add_argument("project", type=Path)
    cmd.add_argument("--module", required=True)
    cmd.add_argument("--goal", action="append", required=True)
    cmd.add_argument("--module-prefix", action="append")
    cmd.add_argument("--build", action="store_true", help="Run Lake build first and bind a separate receipt")
    cmd.add_argument("--timeout", type=float, default=120)
    cmd.add_argument("--max-declarations", type=int, default=1000)
    cmd.add_argument("--out", type=Path, required=True)
    cmd = commands.add_parser("comparator", help="Run a version-compatible real Comparator")
    cmd.add_argument("project", type=Path)
    cmd.add_argument("--config", required=True)
    cmd.add_argument("--timeout", type=float, default=120)
    cmd.add_argument("--legacy", action="store_true", help="Use lake env comparator CONFIG (pre-4.35 tool installed separately)")
    cmd.add_argument("--out", type=Path, required=True)
    cmd = commands.add_parser("prove2me", help="Read a public theorem and its public decomposition from Prove2Me")
    cmd.add_argument("url")
    cmd.add_argument("--out", type=Path, required=True)
    cmd.add_argument("--credentials", type=Path)
    cmd.add_argument("--max-nodes", type=int, default=100)
    cmd.add_argument("--max-depth", type=int, default=10)
    cmd.add_argument("--timeout", type=float, default=30)
    return p


def run(args):
    if args.command == "validate":
        return validate_graph(read_json(args.graph))
    if args.command == "inspect":
        if args.view is not None:
            return project_graph(args.graph.read_bytes(), args.view, args.goal,
                                 direction=args.direction, include_assumptions=args.include_assumptions)
        if args.direction != "prerequisites" or args.include_assumptions:
            raise ContractError("direction and assumption options require --view")
        return inspect_graph(read_json(args.graph), args.goal)
    if args.command == "inspect-bundle":
        if args.passage is not None and args.paper is None:
            raise ContractError("--passage requires --paper")
        if args.paper is not None:
            return project_paper(args.bundle, args.paper, args.passage)
        return inspect_bundle(args.bundle)
    if args.command == "inspect-corpus":
        return project_corpus(args.bundle, expected_manifest_sha256=args.expect_manifest)
    if args.command == "assemble":
        from .bundle import assemble_bundle
        return assemble_bundle(args.graph, {s: tuple(getattr(args, s))
                               for s in ("long", "short", "expository")}, args.out)
    if args.command == "query-papers":
        return query_papers(args.bundle, stage=args.paper, passages=args.passage,
                            section_refs=args.section, node_ids=args.node, relation=args.relation,
                            expected_manifest_sha256=args.expect_manifest)
    if args.command == "select":
        graph = select(read_json(args.graph), args.goal)
        if args.out.exists():
            raise ContractError("output already exists")
        write_json(args.out, graph)
        return validate_graph(graph)
    if args.command == "scaffold":
        return scaffold(read_json(args.graph), args.out)
    if args.command == "check-bundle":
        return check_bundle(args.bundle)
    if args.command == "export":
        return export_bundle(args.bundle, args.out)
    if args.command == "audit-sources":
        return audit_sources(read_json(args.lock), args.root)
    if args.command == "fetch":
        return fetch(read_json(args.lock), args.out)
    if args.command == "prove2me":
        return intake_prove2me(args.url, args.out, credentials=args.credentials,
                              max_nodes=args.max_nodes, max_depth=args.max_depth,
                              timeout=args.timeout)
    if args.command == "extract":
        if args.out.exists():
            raise ContractError("output already exists")
        build = check_build(args.project, args.module, timeout=args.timeout) if args.build else None
        if build and build["status"] != "passed":
            raise VerificationError("requested build did not pass", build)
        report = extract_dependencies(args.project, args.module, args.goal,
                    module_prefixes=args.module_prefix, timeout=args.timeout, max_declarations=args.max_declarations)
        graph = to_graph(report, args.project, build)
        write_json(args.out, graph)
        return validate_graph(graph)
    if args.command == "comparator":
        if args.out.exists():
            raise ContractError("output already exists")
        command = ("lake", "env", "comparator") if args.legacy else None
        receipt = verify_comparator(args.project, args.config, command=command, timeout=args.timeout)
        write_json(args.out, receipt)
        if receipt["status"] != "passed":
            raise VerificationError("Comparator did not pass; receipt saved", receipt)
        return receipt
    raise ContractError("unknown command")


def _display_text(value: str) -> str:
    """Keep source text on one terminal line without interpreting controls."""
    return "".join(
        f"\\u{ord(character):04x}" if ord(character) < 32 or 127 <= ord(character) < 160
        or character in "\u2028\u2029\u202a\u202b\u202c\u202d\u202e\u2066\u2067\u2068\u2069"
        else character for character in value
    )


def _paper_query_text(result: dict) -> str:
    """A presentation of one query result; never re-read or re-query its input.

    The public JSON response, cache identity and evidence remain authoritative.
    This navigation summary intentionally omits full prose and source records.
    """
    display = _display_text

    def names(values):
        return ", ".join(display(value) for value in values) or "(none recorded)"

    def span(value):
        return (f"bytes [{value['start_byte']}, {value['end_byte']}); "
                f"lines {value['start_line']}-{value['end_line']}")

    lines = [
        "Paper query: reader summary of recorded correspondence",
        "Full passage text, source records and evidence details: use --format json (the default).",
        f"Manifest SHA-256: {result['snapshot']['manifest_sha256']}",
        f"Graph SHA-256: {result['snapshot']['graph_sha256']}",
        f"Relation: {result['query']['relation']}; matched passages: {result['match_count']}",
        "Semantic certification: false; completeness beyond recorded relations: unknown.",
        f"Recorded extraction: {display(result['coverage']['recorded_extraction_status'])}; "
        "external source/receipt bytes opened by this query: false.",
        "Witnesses show recorded paths; a mapping or path is not a proof or an explanation-quality judgment.",
    ]
    if result['match_count'] == 0:
        lines.append(display(result['coverage']['empty_result_meaning']))
    evidence = {}
    for paper in result['papers']:
        view = paper['view']
        passages = {p['anchor']: p for p in view['paper']['passages']}
        boundary = paper['support_boundary']
        lines.extend([
            "", f"{paper['stage']}: {len(paper['matches'])} matching passage(s); "
            f"paper state {view['state']}; review state {view['review_state']}",
        ])
        for match in paper['matches']:
            passage = passages[match['anchor']]
            lines.extend([
                f"  {display(match['anchor'])} ({span(passage['content_span'])})",
                f"    Mapping class: {display(match['evidence_class'])}",
                f"    Mapping rationale: {display(passage['rationale'])}",
            ])
            for witness in match['witnesses']:
                route = display(witness['root_node_id'])
                for link in witness['links']:
                    route += f" --{link['kind']}--> {display(link['to_node_id'])}"
                if not witness['links']:
                    route += " (direct mapping)"
                lines.append(f"    Recorded path from {witness['root_mapping_field']}: {route}")
            for overlap in match['section_overlaps']:
                lines.append(f"    Selected section overlap: {span(overlap['overlap_span'])}")
            if match['whole_passage_extends_beyond_selected_sections']:
                lines.append("    The whole matched passage extends beyond the selected section(s); its requirements are retained.")
        additional = sorted(set(boundary['retained_node_ids']) - set(boundary['seed_node_ids']))
        lines.extend([
            f"  Mapped claims: {names(boundary['mapped_claim_ids'])}",
            f"  Mapped assumptions: {names(boundary['mapped_assumption_ids'])}",
            f"  Additional recorded prerequisites ({len(additional)}): {names(additional)}",
            f"  Required assumption records: {names(boundary['required_assumption_ids'])}",
            f"  Unresolved-status records in this closure: {len(boundary['unresolved_node_ids'])}",
            f"  Graph nodes outside this closure: {len(boundary['outside_closure_node_ids'])} "
            "(retained in the bundle; not inferred irrelevant).",
            f"  Other mapped passages outside this selection: {names(view['selection']['omitted_by_selector'])}",
            "  Unmapped prose remains in the paper; no mathematical coverage is inferred for it.",
        ])
        for row in view['graph']['records']['evidence']:
            evidence[row['ref']] = row['record']
    grouped = defaultdict(list)
    for record in evidence.values():
        grouped[(record['kind'], record['status'])].append(record)
    lines.extend([
        "", "Evidence associated with the selected closures (distinct records, not proof verdicts):",
        "Associated means referenced by a retained node/link or naming a retained subject. A record may also "
        "name outside subjects; those subjects are not added as prerequisites.",
    ])
    if not grouped:
        lines.append("  (none recorded for these selections; no check is inferred to have run)")
    for (kind, status), records in sorted(grouped.items()):
        records.sort(key=lambda row: row['id'])
        lines.append(f"  {kind} / {status}: {len(records)}; {names([r['id'] for r in records])}")
        if kind in {"comparator", "lean_build", "extraction", "platform_observation"}:
            for record in records:
                lines.append(f"    {display(record['id'])}: {display(record['details'])}")
                receipt = record.get('receipt', {})
                observations = [f"{field}={display(str(receipt[field]))}"
                                for field in ('status', 'process_status') if field in receipt]
                if observations:
                    lines.append("      Recorded receipt: " + ", ".join(observations))
    lines.append("Other evidence remains in the bundle. Successful byte checks do not accept mathematics or a reader's understanding.")
    return "\n".join(
        textwrap.fill(line, width=110, subsequent_indent=" " * (len(line) - len(line.lstrip()) + 2),
                      break_long_words=False, break_on_hyphens=False)
        if line else "" for line in lines
    )


def main(argv=None) -> int:
    args = parser().parse_args(argv)
    try:
        result = run(args)
    except VerificationError as exc:
        print(json.dumps({"error": str(exc), "receipt": exc.receipt}, indent=2), file=sys.stderr)
        return 2
    except (ContractError, OSError, ValueError, KeyError, TypeError) as exc:
        print(json.dumps({"error": str(exc)}, indent=2), file=sys.stderr)
        return 1
    if args.command == "query-papers" and args.format == "text":
        print(_paper_query_text(result))
    else:
        print(json.dumps(result, indent=2, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
