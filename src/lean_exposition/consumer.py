"""Read-only views of the existing graph and versioned explanation bundle."""
from __future__ import annotations

import copy
from pathlib import Path

from .bundle import STAGES, load_bundle
from .contracts import ARGUMENT_EDGES, decode_json, digest, select, validate_graph


def inspect_graph(graph: dict, goals: list[str] | None = None) -> dict:
    """Describe every record, marking its relationship to the chosen goals.

    Selection changes only this view. Evidence outside the selection stays visible;
    a relevance flag never changes an evidence kind, status or certification claim.
    """
    selected = select(graph, goals) if goals is not None else graph
    summary = validate_graph(selected)
    argument = set(summary["argument_closure"])
    platform = set(summary["platform_closure"])

    def related_evidence(node_ids: set[str], edge_kinds: set[str]) -> set[str]:
        identifiers = {
            evidence_id
            for node in selected["nodes"] if node["id"] in node_ids
            for evidence_id in node["evidence_ids"]
        }
        identifiers.update(
            evidence_id
            for edge in selected["edges"]
            if edge["from"] in node_ids and edge["kind"] in edge_kinds
            for evidence_id in edge["evidence_ids"]
        )
        identifiers.update(
            item["id"] for item in selected["evidence"]
            if node_ids.intersection(item["subject_ids"])
        )
        return identifiers

    argument_evidence = related_evidence(argument, ARGUMENT_EDGES | {"cites"})
    platform_evidence = related_evidence(platform, {"platform_decomposition"})
    result = copy.deepcopy(summary)
    result.update({
        "schema_version": selected["schema_version"],
        "title": selected["title"],
        "scope": selected["scope"],
        "notes": copy.deepcopy(selected["notes"]),
        "nodes": [
            {
                **copy.deepcopy(node),
                "selected": node["id"] in selected["selected_goals"],
                "in_argument_closure": node["id"] in argument,
                "in_platform_closure": node["id"] in platform,
            }
            for node in sorted(selected["nodes"], key=lambda row: row["id"])
        ],
        "edges": copy.deepcopy(sorted(
            selected["edges"], key=lambda row: (row["from"], row["to"], row["kind"])
        )),
        "evidence": [
            {
                **copy.deepcopy(item),
                "relevant_to_argument": item["id"] in argument_evidence,
                "relevant_to_platform": item["id"] in platform_evidence,
            }
            for item in sorted(selected["evidence"], key=lambda row: row["id"])
        ],
        "sources": copy.deepcopy(sorted(selected["sources"], key=lambda row: row["id"])),
        "citations": copy.deepcopy(sorted(selected["citations"], key=lambda row: row["id"])),
    })
    return result


def inspect_bundle(path: Path) -> dict:
    """Inspect one validated capture without extracting ZIP members or reading sources."""
    payload = load_bundle(path)
    manifest = decode_json(payload["manifest.json"])
    graph = decode_json(payload["graph.json"])
    papers = []
    for stage in STAGES:
        mapping = decode_json(payload[f"papers/{stage}.json"])
        papers.append({"mapping_path": f"papers/{stage}.json", **mapping})
    return {
        "schema_version": manifest["schema_version"],
        "bundle_version": manifest["bundle_version"],
        "bundle_id": manifest["bundle_id"],
        "status": manifest["status"],
        "publication": manifest["publication"],
        "manifest_sha256": digest(payload["manifest.json"]),
        "files": copy.deepcopy(manifest["files"]),
        "contract_valid": True,
        "semantic_certification": False,
        "graph": inspect_graph(graph),
        "papers": papers,
        "external_resources": {
            "sources": [
                {**copy.deepcopy(source), "included": False}
                for source in sorted(graph["sources"], key=lambda row: row["id"])
            ],
            "receipts": [
                {
                    "evidence_id": item["id"],
                    "path": item["receipt_path"],
                    "sha256": item["receipt_sha256"],
                    "included": False,
                }
                for item in sorted(graph["evidence"], key=lambda row: row["id"])
                if "receipt_path" in item
            ],
        },
    }
