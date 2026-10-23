#!/usr/bin/env python3
"""Read a lean-exposition ZIP using only Python's standard library.

This example checks transport integrity and selected metadata bindings. It does
not implement the complete graph/artifact contract or certify mathematics.
"""
from __future__ import annotations

import argparse
import hashlib
import io
import json
import math
from pathlib import Path
import re
import stat
import sys
import zipfile
import zlib


STAGES = ("long", "short", "expository")
PAYLOAD_NAMES = {"graph.json"} | {
    f"papers/{stage}.{extension}" for stage in STAGES for extension in ("md", "json")
}
MEMBER_NAMES = PAYLOAD_NAMES | {"manifest.json"}
MAX_MEMBER_BYTES = 32 * 1024 * 1024
MAX_BUNDLE_BYTES = 64 * 1024 * 1024
MAX_ARCHIVE_BYTES = 65 * 1024 * 1024


class BundleError(ValueError):
    """The archive cannot be read as this supported bundle format."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise BundleError(message)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def json_object(data: bytes, name: str) -> dict:
    def pairs(items):
        result = {}
        for key, value in items:
            require(key not in result, f"{name}: duplicate JSON key {key!r}")
            result[key] = value
        return result

    def constant(value):
        raise BundleError(f"{name}: non-finite JSON number {value}")

    def number(value):
        result = float(value)
        require(math.isfinite(result), f"{name}: non-finite JSON number")
        return result

    try:
        result = json.loads(data.decode("utf-8"), object_pairs_hook=pairs,
                            parse_constant=constant, parse_float=number)
    except BundleError:
        raise
    except (UnicodeError, ValueError, RecursionError) as exc:
        raise BundleError(f"{name}: malformed UTF-8 JSON") from exc
    require(isinstance(result, dict), f"{name}: expected a JSON object")
    require(result.get("schema_version") == "1.0", f"{name}: unsupported schema version")
    return result


def text(value, label: str) -> str:
    require(isinstance(value, str) and bool(value), f"{label}: expected nonempty text")
    return value


def identifiers(value, label: str) -> list[str]:
    require(isinstance(value, list), f"{label}: expected an ID list")
    for item in value:
        text(item, label)
    require(len(value) == len(set(value)), f"{label}: duplicate IDs")
    return value


def records(value, label: str) -> list[dict]:
    require(isinstance(value, list) and all(isinstance(row, dict) for row in value),
            f"{label}: expected an object list")
    identifiers([row.get("id") for row in value], label)
    return value


def capture(path: Path) -> tuple[dict[str, bytes], str]:
    """Capture bounded bytes; never extract members or follow paths in the ZIP."""
    with path.open("rb") as stream:
        archive_bytes = stream.read(MAX_ARCHIVE_BYTES + 1)
    require(len(archive_bytes) <= MAX_ARCHIVE_BYTES, "archive exceeds 65 MiB limit")
    try:
        with zipfile.ZipFile(io.BytesIO(archive_bytes)) as archive:
            members = archive.infolist()
            names = [member.filename for member in members]
            require(len(names) == len(set(names)), "duplicate ZIP members")
            require(set(names) == MEMBER_NAMES, "ZIP must contain exactly the eight bundle files")
            require(sum(member.file_size for member in members) <= MAX_BUNDLE_BYTES,
                    "uncompressed bundle exceeds 64 MiB limit")
            payload = {}
            for member in members:
                name = member.filename
                require(member.orig_filename == name, f"unsafe member name: {name!r}")
                mode = stat.S_IFMT(member.external_attr >> 16)
                require(not member.is_dir() and not (member.external_attr & 0x10)
                        and mode in (0, stat.S_IFREG), f"not a regular ZIP member: {name}")
                require(not member.flag_bits & 1, f"encrypted ZIP member: {name}")
                require(member.compress_type in (zipfile.ZIP_STORED, zipfile.ZIP_DEFLATED),
                        f"unsupported ZIP compression: {name}")
                require(member.file_size <= MAX_MEMBER_BYTES, f"member exceeds 32 MiB limit: {name}")
                with archive.open(member) as stream:
                    content = stream.read(MAX_MEMBER_BYTES + 1)
                require(len(content) == member.file_size and len(content) <= MAX_MEMBER_BYTES,
                        f"member size mismatch: {name}")
                payload[name] = content
    except (zipfile.BadZipFile, zipfile.LargeZipFile, EOFError, NotImplementedError,
            RuntimeError, zlib.error) as exc:
        raise BundleError(f"malformed or unsupported ZIP: {exc}") from exc
    return payload, sha256(archive_bytes)


def read_bundle(path: Path) -> dict:
    """Return recorded goals/evidence/paper states after transport checks."""
    payload, archive_hash = capture(path)
    manifest = json_object(payload["manifest.json"], "manifest.json")
    require(set(manifest) == {"schema_version", "bundle_id", "bundle_version", "graph",
                              "documents", "files", "status", "publication"},
            "manifest fields differ from bundle 0.1.0")
    require(manifest["bundle_version"] == "0.1.0", "unsupported bundle version")
    require(manifest["graph"] == "graph.json", "manifest must select graph.json")
    require(manifest["publication"] == "local_only", "unsupported publication mode")
    require(manifest["documents"] == [{"stage": s, "mapping": f"papers/{s}.json"} for s in STAGES],
            "manifest must select the three paper mappings in stage order")
    files = manifest["files"]
    require(isinstance(files, list) and len(files) == 7, "manifest must hash seven payload files")
    hashes = {}
    for row in files:
        require(isinstance(row, dict) and set(row) == {"path", "sha256"}, "invalid manifest file record")
        name = text(row["path"], "manifest file path")
        require(name in PAYLOAD_NAMES and name not in hashes, f"unexpected or duplicate manifest path: {name}")
        expected = text(row["sha256"], f"{name} hash")
        require(re.fullmatch(r"[0-9a-f]{64}", expected) is not None, f"invalid SHA-256: {name}")
        require(sha256(payload[name]) == expected, f"hash mismatch: {name}")
        hashes[name] = expected

    graph = json_object(payload["graph.json"], "graph.json")
    graph_id = text(graph.get("id"), "graph ID")
    require(manifest["bundle_id"] == graph_id, "bundle identity differs from graph")
    title = text(graph.get("title"), "graph title")
    scope = text(graph.get("scope"), "graph scope")
    graph_notes = identifiers(graph.get("notes"), "graph notes")
    goals = identifiers(graph.get("selected_goals"), "selected goals")
    require(bool(goals), "at least one selected goal is required")
    nodes = {row["id"]: row for row in records(graph.get("nodes"), "nodes")}
    require(set(goals) <= set(nodes), "selected goal is absent from graph nodes")
    selected = [{"id": goal, "label": text(nodes[goal].get("label"), f"{goal} label")} for goal in goals]
    evidence = []
    for row in records(graph.get("evidence"), "evidence"):
        evidence.append({key: text(row.get(key), f"evidence {row['id']} {key}")
                         for key in ("id", "kind", "status", "details")})

    papers = []
    for stage in STAGES:
        name = f"papers/{stage}.json"
        paper = json_object(payload[name], name)
        require(paper.get("stage") == stage and paper.get("path") == f"papers/{stage}.md",
                f"{name}: stage/path binding differs")
        require(paper.get("graph_sha256") == hashes["graph.json"], f"{name}: graph hash binding differs")
        require(paper.get("content_sha256") == hashes[f"papers/{stage}.md"], f"{name}: content hash binding differs")
        require(paper.get("selected_goal_ids") == goals, f"{name}: selected goals differ")
        state = paper.get("state")
        review = paper.get("review_state")
        require(state in ("scaffold", "draft", "reviewed"), f"{name}: unknown paper state")
        require(review in ("not_reviewed", "needs_revision", "accepted"), f"{name}: unknown review state")
        notes = paper.get("review_notes")
        require(isinstance(notes, list) and all(isinstance(note, str) and note for note in notes),
                f"{name}: invalid review notes")
        papers.append({"stage": stage, "path": paper["path"], "state": state,
                       "review_state": review, "review_notes": notes})
    state = "scaffold" if all(p["state"] == "scaffold" for p in papers) else "authored"
    require(manifest["status"] == state, "bundle status differs from paper states")
    return {
        "bundle_id": graph_id, "schema_version": "1.0", "bundle_version": "0.1.0",
        "title": title, "scope": scope, "notes": graph_notes,
        "archive_sha256": archive_hash, "manifest_sha256": sha256(payload["manifest.json"]),
        "selected_goals": selected, "evidence": evidence, "papers": papers,
        "status": state, "transport_integrity": True,
        "full_contract_validation": False, "semantic_certification": False,
    }


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("archive", type=Path, help="bundle ZIP; read in memory without extraction")
    args = parser.parse_args(argv)
    try:
        result = read_bundle(args.archive)
    except (BundleError, OSError, ValueError, RecursionError) as exc:
        print(json.dumps({"error": str(exc)}), file=sys.stderr)
        return 1
    print(json.dumps(result, indent=2, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
