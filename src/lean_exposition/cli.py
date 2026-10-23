"""Local command-line interface with optional read-only public-source intake."""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

from .bundle import check_bundle, export_bundle, scaffold
from .contracts import ContractError, read_json, select, validate_graph, write_json
from .consumer import inspect_bundle, inspect_graph
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
    cmd = commands.add_parser("inspect-bundle", help="Inspect a validated directory or ZIP bundle")
    cmd.add_argument("bundle", type=Path)
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
        return inspect_graph(read_json(args.graph), args.goal)
    if args.command == "inspect-bundle":
        return inspect_bundle(args.bundle)
    if args.command == "assemble":
        from .bundle import assemble_bundle
        return assemble_bundle(args.graph, {s: tuple(getattr(args, s))
                               for s in ("long", "short", "expository")}, args.out)
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
    print(json.dumps(result, indent=2, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
