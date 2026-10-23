"""Independent graph attacks using synthetic records, never real Lean checks."""
from __future__ import annotations

import copy
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from lean_exposition.contracts import (
    ContractError, closure, digest, encoded, local_path, select,
    validate_artifact, validate_graph,
)
from lean_exposition.extraction import to_graph
from test_adversarial import synthetic_artifact, synthetic_graph
from test_core_review import extraction_fixture


def synthetic_node(identifier, *, kind="claim", status="unverified",
                   assumptions=(), citations=()):
    return {
        "id": identifier, "kind": kind, "label": identifier, "status": status,
        "assumption_ids": list(assumptions), "evidence_ids": [],
        "citation_ids": list(citations),
    }


def graph_with_cited_claim():
    graph = synthetic_graph()
    graph["citations"].append({
        "id": "cited-credit", "title": "Synthetic cited claim",
        "url": "https://example.org/synthetic-cited", "source_id": "public",
        "locator": "Synthetic cited claim",
    })
    graph["nodes"].extend([
        synthetic_node("cited-claim", assumptions=["cited-assumption"],
                       citations=["cited-credit"]),
        synthetic_node("cited-assumption", kind="assumption", status="axiom"),
        synthetic_node("cited-prerequisite", status="open"),
    ])
    graph["edges"].extend([
        {"from": "goal", "to": "cited-claim", "kind": "cites", "evidence_ids": []},
        {"from": "cited-claim", "to": "cited-prerequisite", "kind": "supports",
         "evidence_ids": []},
    ])
    return graph


class ReceiptPurposeAdversarialTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        report, build = extraction_fixture(self.root)
        # to_graph exercises conversion only; these fixtures did not run Lean.
        self.graph = to_graph(report, self.root, build)

    def test_valid_synthetic_receipts_do_not_confer_semantic_certification(self):
        self.assertFalse(validate_graph(self.graph)["semantic_certification"])

    def test_successful_receipt_cannot_be_repurposed(self):
        for evidence_id, wrong_purpose in (
            ("build", "elaboration_process"), ("extract", "lean_build"),
            ("build", "comparator"), ("extract", "platform_observation"),
        ):
            with self.subTest(evidence=evidence_id, purpose=wrong_purpose):
                graph = copy.deepcopy(self.graph)
                item = next(e for e in graph["evidence"] if e["id"] == evidence_id)
                item["receipt"]["evidence_kind"] = wrong_purpose
                with self.assertRaises(ContractError):
                    validate_graph(graph)

    def test_successful_receipt_requires_an_explicit_purpose(self):
        for evidence_id in ("build", "extract"):
            with self.subTest(evidence=evidence_id):
                graph = copy.deepcopy(self.graph)
                item = next(e for e in graph["evidence"] if e["id"] == evidence_id)
                del item["receipt"]["evidence_kind"]
                with self.assertRaises(ContractError):
                    validate_graph(graph)

    def test_receipt_command_cannot_disagree_with_evidence_command(self):
        for evidence_id in ("build", "extract"):
            with self.subTest(evidence=evidence_id):
                graph = copy.deepcopy(self.graph)
                item = next(e for e in graph["evidence"] if e["id"] == evidence_id)
                item["receipt"]["command"] = ["synthetic-unrelated-check"]
                with self.assertRaises(ContractError):
                    validate_graph(graph)

    def test_matching_source_files_cannot_hide_a_different_project_snapshot(self):
        for evidence_id in ("build", "extract"):
            with self.subTest(evidence=evidence_id):
                graph = copy.deepcopy(self.graph)
                item = next(e for e in graph["evidence"] if e["id"] == evidence_id)
                # This extra input is not a source node: comparing only cited
                # source bytes would overlook the disagreement between runs.
                item["receipt"]["source_hashes"]["SyntheticSupport.lean"] = digest(b"synthetic extra input")
                with self.assertRaises(ContractError):
                    validate_graph(graph)

    def test_matching_snapshot_cannot_hide_a_different_built_module(self):
        graph = copy.deepcopy(self.graph)
        build = next(e for e in graph["evidence"] if e["id"] == "build")
        build["receipt"]["module"] = "SyntheticOtherModule"
        with self.assertRaises(ContractError):
            validate_graph(graph)

    def test_source_drift_cannot_retain_a_successful_graph_receipt(self):
        for evidence_id in ("build", "extract"):
            with self.subTest(evidence=evidence_id):
                graph = copy.deepcopy(self.graph)
                item = next(e for e in graph["evidence"] if e["id"] == evidence_id)
                item["receipt"]["source_changed"] = True
                with self.assertRaises(ContractError):
                    validate_graph(graph)


class ObligationAndClosureAdversarialTests(unittest.TestCase):
    def test_a_claim_cannot_hide_its_unresolved_status_as_an_axiom(self):
        graph = synthetic_graph()
        graph["nodes"][0]["status"] = "axiom"
        with self.assertRaises(ContractError):
            validate_graph(graph)

    def test_relabeling_sorry_does_not_remove_its_unresolved_obligation(self):
        for identifier, declaration in (("sorryAx", None), ("renamed-sorry", "sorryAx")):
            with self.subTest(identifier=identifier):
                graph = synthetic_graph()
                sorry = synthetic_node(identifier, kind="assumption", status="axiom")
                if declaration is not None:
                    sorry["declaration"] = declaration
                graph["nodes"].append(sorry)
                graph["nodes"][0]["assumption_ids"].append(identifier)
                try:
                    summary = validate_graph(graph)
                except ContractError:
                    continue  # Rejecting the misleading record is also safe.
                self.assertIn(identifier, summary["unresolved"])
                artifact, content = synthetic_artifact(graph)
                artifact["assumption_ids"].append(identifier)
                artifact["passages"][0]["assumption_ids"].append(identifier)
                # Keeping it as an assumption must not permit omitting the
                # separate unresolved-obligation record.
                with self.assertRaises(ContractError):
                    validate_artifact(artifact, graph, digest(encoded(graph)), content)

    def test_cycles_through_edges_and_assumptions_have_a_finite_full_closure(self):
        graph = synthetic_graph()
        graph["edges"].append({
            "from": "prerequisite", "to": "goal", "kind": "supports", "evidence_ids": [],
        })
        graph["nodes"][2]["assumption_ids"] = ["second-assumption"]
        graph["nodes"].append(synthetic_node(
            "second-assumption", kind="assumption", status="axiom", assumptions=["assumption"],
        ))
        expected = {"goal", "prerequisite", "assumption", "second-assumption"}
        self.assertEqual(closure(graph), expected)
        summary = validate_graph(graph)
        self.assertEqual(set(summary["argument_closure"]), expected)
        self.assertEqual(summary["assumptions"], ["assumption", "second-assumption"])
        self.assertEqual(summary["unresolved"], ["goal", "prerequisite"])

    def test_select_preserves_adjacent_open_nodes_and_failed_evidence(self):
        graph = synthetic_graph()
        graph["nodes"].append(synthetic_node("adjacent-open", status="open"))
        graph["evidence"].append({
            "id": "synthetic-failure", "kind": "source_hash", "status": "failed",
            "command": ["synthetic-hash-check"], "tool": "synthetic-fixture",
            "source_ids": ["public"], "subject_ids": ["adjacent-open"],
            "details": "Synthetic failure for validator testing; no check was run.",
        })
        original = copy.deepcopy(graph)
        result = select(graph, ["prerequisite"])
        expected = copy.deepcopy(original)
        expected["selected_goals"] = ["prerequisite"]
        self.assertEqual(result, expected)
        self.assertEqual(graph, original)
        summary = validate_graph(result)
        self.assertEqual(summary["failed_evidence"], ["synthetic-failure"])
        self.assertEqual(summary["argument_closure"], ["prerequisite"])
        # Nested edits to the selection must not mutate the original graph.
        result["nodes"][0]["label"] = "Edited selection label"
        result["sources"][0]["revision"] = "synthetic-new-revision"
        self.assertEqual(graph, original)

    def test_citation_closure_is_separate_from_argument_assumptions(self):
        graph = graph_with_cited_claim()
        summary = validate_graph(graph)
        self.assertEqual(set(summary["argument_closure"]), {"goal", "prerequisite", "assumption"})
        self.assertEqual(summary["assumptions"], ["assumption"])
        self.assertEqual(summary["unresolved"], ["goal", "prerequisite"])
        self.assertEqual(closure(graph, edge_kinds={"cites"}), {"goal", "cited-claim"})
        self.assertEqual(closure(graph, edge_kinds=set()), {"goal"})


class CitationPreservationAdversarialTests(unittest.TestCase):
    def setUp(self):
        self.graph = graph_with_cited_claim()
        self.artifact, self.content = synthetic_artifact(self.graph)
        self.artifact["citation_ids"].append("cited-credit")
        self.artifact["passages"][0]["citation_ids"].append("cited-credit")

    def test_cited_credit_is_preserved_without_importing_cited_assumptions(self):
        validate_artifact(self.artifact, self.graph, digest(encoded(self.graph)), self.content)
        self.assertNotIn("cited-assumption", self.artifact["assumption_ids"])
        self.assertNotIn("cited-prerequisite", self.artifact["unresolved_ids"])

    def test_document_cannot_drop_credit_reached_through_a_cites_edge(self):
        self.artifact["citation_ids"].remove("cited-credit")
        self.artifact["passages"][0]["citation_ids"].remove("cited-credit")
        with self.assertRaises(ContractError):
            validate_artifact(self.artifact, self.graph, digest(encoded(self.graph)), self.content)

    def test_passage_cannot_drop_credit_while_document_keeps_it(self):
        self.artifact["passages"][0]["citation_ids"].remove("cited-credit")
        with self.assertRaises(ContractError):
            validate_artifact(self.artifact, self.graph, digest(encoded(self.graph)), self.content)


class ReferencePathPortabilityAdversarialTests(unittest.TestCase):
    def test_graph_references_do_not_consult_an_unrelated_working_directory(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            project, unrelated = root / "project", root / "unrelated"
            project.mkdir()
            unrelated.mkdir()
            report, build = extraction_fixture(project)
            graph = to_graph(report, project, build)
            build_item = next(e for e in graph["evidence"] if e["id"] == "build")
            build_item["receipt_path"] = "receipts/build.json"
            build_item["receipt_sha256"] = digest(encoded(build_item["receipt"]))
            (unrelated / "Minimal.lean").symlink_to(project / "Minimal.lean")
            (unrelated / "lean-toolchain").symlink_to(project / "lean-toolchain")
            (unrelated / "receipts").symlink_to(project, target_is_directory=True)
            expected = validate_graph(graph)
            with patch("lean_exposition.contracts.Path.cwd", return_value=unrelated):
                self.assertEqual(validate_graph(graph), expected)
            # Filesystem consumers must still enforce symlink isolation when
            # given the actual root; portable references do not relax this.
            with self.assertRaises(ContractError):
                local_path(unrelated, "Minimal.lean")

    def test_graph_source_and_receipt_paths_reject_nonportable_spelling(self):
        invalid = ("../outside.lean", "/absolute.lean", "C:\\outside.lean",
                   "folder\\source.lean", "a/../source.lean", "a//source.lean")
        for field in ("source", "receipt"):
            for path in invalid:
                with self.subTest(field=field, path=path):
                    graph = synthetic_graph()
                    if field == "source":
                        graph["sources"][0].update(path=path, sha256=digest(b"synthetic"))
                    else:
                        graph["evidence"].append({
                            "id": "external-receipt", "kind": "source_hash", "status": "not_run",
                            "command": [], "tool": "synthetic-fixture", "source_ids": ["public"],
                            "subject_ids": ["goal"], "details": "Synthetic reference only.",
                            "receipt_path": path, "receipt_sha256": digest(b"synthetic"),
                        })
                    with self.assertRaises(ContractError):
                        validate_graph(graph)


if __name__ == "__main__":
    unittest.main()
