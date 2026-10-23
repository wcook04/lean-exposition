"""Independent contract regressions using synthetic content only."""
from __future__ import annotations

import json
import tempfile
import unittest
import zipfile
from pathlib import Path
from unittest.mock import patch

from lean_exposition import bundle
from lean_exposition.contracts import (
    ContractError, digest, encoded, read_json, validate_artifact,
    write_json,
)


def synthetic_graph():
    def node(name, kind, status, assumptions=(), citations=()):
        return {
            "id": name, "kind": kind, "label": name, "status": status,
            "assumption_ids": list(assumptions), "evidence_ids": [],
            "citation_ids": list(citations),
        }

    return {
        "schema_version": "1.0", "id": "synthetic-review",
        "title": "Synthetic contract review", "selected_goals": ["goal"],
        "sources": [{
            "id": "public", "kind": "synthetic",
            "url": "https://example.org/synthetic", "revision": "fixture-v1",
            "license": "CC0-1.0", "redistribution": "original",
        }],
        "citations": [{
            "id": name, "title": name, "url": "https://example.org/synthetic",
            "source_id": "public", "locator": name,
        } for name in ("goal-credit", "prerequisite-credit")],
        "nodes": [
            node("goal", "claim", "conditional", ["assumption"], ["goal-credit"]),
            node("prerequisite", "claim", "unverified", citations=["prerequisite-credit"]),
            node("assumption", "assumption", "axiom"),
        ],
        "edges": [{"from": "goal", "to": "prerequisite", "kind": "supports", "evidence_ids": []}],
        "evidence": [], "scope": "Synthetic review fixture only.",
        "extraction_status": "fixture", "notes": [],
    }


def synthetic_artifact(graph):
    passage = "\nA synthetic claim depending on its recorded assumption and prerequisite.\n"
    content = ("<!-- passage:result -->" + passage + "<!-- /passage:result -->\n").encode()
    artifact = {
        "schema_version": "1.0", "stage": "long", "state": "draft",
        "path": "papers/long.md", "content_sha256": digest(content),
        "graph_sha256": digest(encoded(graph)), "selected_goal_ids": ["goal"],
        "claim_ids": ["goal"], "citation_ids": ["goal-credit", "prerequisite-credit"],
        "assumption_ids": ["assumption"], "unresolved_ids": ["goal", "prerequisite"],
        "passages": [{
            "anchor": "result", "text_sha256": digest(passage.encode()),
            "claim_ids": ["goal"], "citation_ids": ["goal-credit", "prerequisite-credit"],
            "assumption_ids": ["assumption"], "evidence_class": "source_argument",
            "rationale": "Synthetic binding for an independently authored regression.",
        }],
        "review_state": "not_reviewed", "review_notes": [],
    }
    return artifact, content


class AdversarialContractTests(unittest.TestCase):
    def test_complete_synthetic_binding_is_valid(self):
        graph = synthetic_graph()
        artifact, content = synthetic_artifact(graph)
        validate_artifact(artifact, graph, digest(encoded(graph)), content)

    def test_artifact_preserves_citations_from_prerequisite_closure(self):
        graph = synthetic_graph()
        artifact, content = synthetic_artifact(graph)
        artifact["citation_ids"] = ["goal-credit"]
        artifact["passages"][0]["citation_ids"] = ["goal-credit"]
        with self.assertRaises(ContractError):
            validate_artifact(artifact, graph, digest(encoded(graph)), content)

    def test_passage_preserves_claim_assumptions(self):
        graph = synthetic_graph()
        artifact, content = synthetic_artifact(graph)
        artifact["passages"][0]["assumption_ids"] = []
        with self.assertRaises(ContractError):
            validate_artifact(artifact, graph, digest(encoded(graph)), content)

    def test_passage_preserves_claim_citations(self):
        graph = synthetic_graph()
        artifact, content = synthetic_artifact(graph)
        artifact["passages"][0]["citation_ids"] = []
        with self.assertRaises(ContractError):
            validate_artifact(artifact, graph, digest(encoded(graph)), content)

    def test_manifest_replacement_cannot_export_unchecked_file(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "bundle"
            bundle.scaffold(synthetic_graph(), root)
            original_check = bundle.check_bundle

            def replace_after_check(path):
                checked = original_check(path)
                data = b"UNEXPECTED FILE\n"
                (root / "unexpected.txt").write_bytes(data)
                manifest = read_json(root / "manifest.json")
                manifest["files"].append({"path": "unexpected.txt", "sha256": digest(data)})
                write_json(root / "manifest.json", manifest)
                return checked

            destination = Path(tmp) / "export.zip"
            with patch.object(bundle, "check_bundle", side_effect=replace_after_check):
                try:
                    bundle.export_bundle(root, destination)
                except ContractError:
                    return  # Rejecting a changed snapshot is also safe.
            with zipfile.ZipFile(destination) as archive:
                self.assertNotIn("unexpected.txt", archive.namelist())

    def test_export_preserves_manifest_bytes(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "bundle"
            bundle.scaffold(synthetic_graph(), root)
            manifest = read_json(root / "manifest.json")
            source_bytes = (json.dumps(manifest, separators=(",", ":")) + "\n").encode()
            (root / "manifest.json").write_bytes(source_bytes)
            destination = Path(tmp) / "export.zip"
            bundle.export_bundle(root, destination)
            with zipfile.ZipFile(destination) as archive:
                self.assertEqual(archive.read("manifest.json"), source_bytes)


if __name__ == "__main__":
    unittest.main()
