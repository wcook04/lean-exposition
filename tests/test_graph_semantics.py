"""Graph invariants exercised with synthetic records, not verification results."""
from __future__ import annotations

import copy
import tempfile
import unittest
from pathlib import Path

from lean_exposition.contracts import (
    ContractError, closure, digest, encoded, portable_path, required_citation_ids, select,
    validate_graph,
)
from lean_exposition.extraction import to_graph
from test_adversarial import synthetic_graph
from test_core_review import extraction_fixture, rebind


class FormalProjectionTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.report, self.build = extraction_fixture(self.root)
        self.graph = to_graph(self.report, self.root, self.build)

    def test_extraction_subject_source_cannot_be_removed(self):
        self.graph["evidence"][0]["source_ids"] = ["environment"]
        with self.assertRaisesRegex(ContractError, "subject's source"):
            validate_graph(self.graph)

    def test_successful_extraction_requires_report_hash(self):
        for value in (None, "not-a-content-hash", 123):
            with self.subTest(value=value):
                graph = copy.deepcopy(self.graph)
                graph["evidence"][0]["receipt"]["report_sha256"] = value
                with self.assertRaisesRegex(ContractError, "report content hash"):
                    validate_graph(graph)

    def test_partial_cannot_be_promoted_without_new_projection(self):
        self.report["declarations"][0]["value_dependencies"] = ["outside"]
        self.report["external_dependencies"] = [
            {"name": "outside", "kind": "theorem", "module": "Init"}
        ]
        rebind(self.report)
        graph = to_graph(self.report, self.root, self.build)
        self.assertEqual(graph["extraction_status"], "partial")
        graph["extraction_status"] = "complete"
        with self.assertRaisesRegex(ContractError, "projection differs"):
            validate_graph(graph)

    def test_inspection_boundary_is_receipt_bound(self):
        self.graph["nodes"][0]["boundary"] = "A different inspection claim."
        with self.assertRaisesRegex(ContractError, "projection differs"):
            validate_graph(self.graph)

    def test_human_label_and_graph_notes_remain_editable(self):
        self.graph["nodes"][0]["label"] = "An explanatory name"
        self.graph["notes"].append("An additional reading suggestion.")
        validate_graph(self.graph)

    def test_normalized_receipt_retains_original_command_binding(self):
        for target in ("extract", "build"):
            with self.subTest(target=target):
                report, build = copy.deepcopy(self.report), copy.deepcopy(self.build)
                receipt = report["receipt"] if target == "extract" else build
                original = ["/synthetic/toolchain/bin/lake", *receipt["command"][1:]]
                command_hash = digest(encoded({"command": original}))
                receipt.update(command_sha256=command_hash, command_paths_redacted=True)
                graph = to_graph(report, self.root, build)
                public = next(e["receipt"] for e in graph["evidence"] if e["id"] == target)
                self.assertEqual(public["command_sha256"], command_hash)
                self.assertTrue(public["command_paths_redacted"])
                self.assertNotIn(b"/synthetic/toolchain", encoded(graph))
                validate_graph(graph)

    def test_saved_diagnostic_hashes_survive_receipt_translation(self):
        for stream in ("stdout", "stderr"):
            raw = self.report["receipt"].pop(stream)
            self.report["receipt"][stream + "_sha256"] = digest(raw.encode())
        graph = to_graph(self.report, self.root, self.build)
        receipt = graph["evidence"][0]["receipt"]
        for stream in ("stdout", "stderr"):
            self.assertEqual(receipt[stream + "_sha256"], self.report["receipt"][stream + "_sha256"])
            self.assertNotIn(stream, receipt)

    def test_second_redaction_keeps_original_invocation_hash(self):
        receipt = self.report["receipt"]
        original = ["/synthetic/bin/lean", "--run", "/synthetic/tmp/LeanExpositionDriver.lean"]
        original_hash = digest(encoded({"command": original}))
        receipt.update(command=[original[0], "--run", "LeanExpositionDriver.lean"],
                       command_sha256=original_hash, command_paths_redacted=True)
        graph = to_graph(self.report, self.root, self.build)
        public = graph["evidence"][0]["receipt"]
        self.assertEqual(public["command_sha256"], original_hash)
        self.assertEqual(public["command"], ["lean", "--run", "LeanExpositionDriver.lean"])
        self.assertNotIn(b"/synthetic/", encoded(graph))

    def test_invalid_original_command_hash_is_rejected(self):
        self.report["receipt"]["command_sha256"] = "not-a-hash"
        with self.assertRaisesRegex(ContractError, "invalid receipt command_sha256"):
            to_graph(self.report, self.root, self.build)

    def test_raw_diagnostics_determine_output_hashes(self):
        self.report["receipt"]["stdout_sha256"] = "0" * 64
        graph = to_graph(self.report, self.root, self.build)
        self.assertEqual(graph["evidence"][0]["receipt"]["stdout_sha256"],
                         digest(self.report["receipt"]["stdout"].encode()))

    def test_absent_diagnostics_do_not_claim_empty_outputs(self):
        for stream in ("stdout", "stderr"):
            self.report["receipt"].pop(stream)
        graph = to_graph(self.report, self.root, self.build)
        self.assertNotIn("stdout_sha256", graph["evidence"][0]["receipt"])
        self.assertNotIn("stderr_sha256", graph["evidence"][0]["receipt"])

    def test_invalid_saved_diagnostic_hashes_are_rejected(self):
        for value in (None, 12, "", "not-a-hash", "0" * 63):
            with self.subTest(value=value):
                report = copy.deepcopy(self.report)
                del report["receipt"]["stdout"]
                report["receipt"]["stdout_sha256"] = value
                with self.assertRaisesRegex(ContractError, "invalid receipt stdout_sha256"):
                    to_graph(report, self.root, self.build)

    def test_process_returncode_cannot_be_boolean(self):
        self.graph["evidence"][0]["receipt"]["returncode"] = False
        with self.assertRaises(ContractError):
            validate_graph(self.graph)

    def test_unlinked_failed_build_still_conflicts_with_checked_subject(self):
        failed = copy.deepcopy(self.graph["evidence"][1])
        failed.update(id="failed-build", status="failed")
        failed["receipt"].update(status="failed", returncode=1)
        self.graph["evidence"].append(failed)
        self.assertNotIn("failed-build", self.graph["nodes"][0]["evidence_ids"])
        with self.assertRaisesRegex(ContractError, "conflicting Lean build"):
            validate_graph(self.graph)


class SelectionSemanticsTests(unittest.TestCase):
    def test_reference_paths_reject_windows_device_and_ambiguous_names(self):
        for name in ("CON", "a/aux.lean", "LPT1.txt", "COM¹.lean", "a/file.", "a/file ",
                     "a/what?.lean", 'a/quoted".lean', "a/star*.lean", "a/pipe|.lean"):
            with self.subTest(name=name), self.assertRaises(ContractError):
                portable_path(name)
        self.assertEqual(str(portable_path("src/Lean.Module.lean")), "src/Lean.Module.lean")

    def test_selected_goal_list_is_owned_by_result(self):
        goals = ["goal"]
        selected = select(synthetic_graph(), goals)
        goals[:] = ["missing"]
        self.assertEqual(selected["selected_goals"], ["goal"])
        validate_graph(selected)

    def test_closure_rejects_phantom_nodes_in_each_traversal(self):
        for kind in ("supports", "platform_decomposition", "cites"):
            graph = synthetic_graph()
            graph["edges"] = [{"from": "goal", "to": "missing", "kind": kind, "evidence_ids": []}]
            with self.subTest(kind=kind), self.assertRaisesRegex(ContractError, "closure edge endpoint"):
                closure(graph, edge_kinds={kind})

    def test_unknown_closure_edge_filter_is_rejected(self):
        with self.assertRaisesRegex(ContractError, "closure edge kind"):
            closure(synthetic_graph(), edge_kinds={"unknown_dependency"})

    def test_citation_cycle_preserves_credit_without_importing_assumptions(self):
        graph = synthetic_graph()
        graph["nodes"][0]["assumption_ids"] = []
        graph["nodes"][1]["assumption_ids"] = ["assumption"]
        graph["edges"] = [
            {"from": "goal", "to": "prerequisite", "kind": "cites", "evidence_ids": []},
            {"from": "prerequisite", "to": "goal", "kind": "cites", "evidence_ids": []},
        ]
        self.assertEqual(closure(graph), {"goal"})
        self.assertEqual(required_citation_ids(graph), {"goal-credit", "prerequisite-credit"})
        self.assertEqual(validate_graph(graph)["assumptions"], [])


class PlatformEvidenceTests(unittest.TestCase):
    def graph(self):
        graph = synthetic_graph()
        graph["edges"][0].update(kind="platform_decomposition", evidence_ids=["observed"])
        for index, node in enumerate(graph["nodes"][:2], 1):
            node["source_id"] = "public"
            node["platform"] = {
                "provider": "prove2me", "id": f"00000000-0000-0000-0000-{index:012d}",
                "entity": "theorem", "status": "Open", "visibility": "public",
            }
        graph["evidence"] = [{
            "id": "observed", "kind": "platform_observation", "status": "passed",
            "command": ["synthetic-observation"], "tool": "synthetic fixture",
            "source_ids": ["public"], "subject_ids": ["goal", "prerequisite"],
            "details": "Synthetic relation for contract validation only.",
        }]
        return graph

    def test_platform_relation_stays_separate_from_argument(self):
        summary = validate_graph(self.graph())
        self.assertEqual(summary["platform_closure"], ["goal", "prerequisite"])
        self.assertEqual(summary["argument_closure"], ["assumption", "goal"])

    def test_platform_relation_requires_observation_binding(self):
        for change in (
            lambda g: g["edges"][0].update(evidence_ids=[]),
            lambda g: g["evidence"][0].update(kind="semantic_review"),
            lambda g: g["evidence"][0].update(status="failed"),
            lambda g: g["evidence"][0].update(subject_ids=["goal"]),
            lambda g: g["evidence"][0].update(source_ids=[]),
        ):
            graph = self.graph()
            change(graph)
            with self.subTest(graph=graph["evidence"]), self.assertRaisesRegex(ContractError, "platform observation"):
                validate_graph(graph)

    def test_arbitrary_claims_cannot_be_called_platform_decomposition(self):
        graph = self.graph()
        del graph["nodes"][0]["platform"]
        with self.assertRaisesRegex(ContractError, "platform endpoints"):
            validate_graph(graph)


class ComparatorEvidenceTests(unittest.TestCase):
    def graph(self):
        graph = synthetic_graph()
        config_hash = digest(b"synthetic comparator configuration")
        graph["sources"].append({
            "id": "config", "kind": "synthetic", "url": "urn:synthetic:config",
            "revision": config_hash, "sha256": config_hash, "path": "comparator.json",
            "license": "CC0-1.0", "redistribution": "original",
        })
        graph["evidence"] = [{
            "id": "comparison", "kind": "comparator", "status": "passed",
            "command": ["comparator", "comparator.json"], "tool": "synthetic fixture",
            "source_ids": ["config"], "subject_ids": ["goal"],
            "details": "Synthetic invocation receipt, not an actual verification result.",
            "receipt": {
                "evidence_kind": "comparator", "status": "passed", "returncode": 0,
                "command": ["comparator", "comparator.json"], "source_changed": False,
                "config_sha256": config_hash, "source_hashes": {"lean-toolchain": digest(b"synthetic pin")},
            },
        }]
        return graph

    def test_comparator_receipt_does_not_promote_claim(self):
        graph = self.graph()
        summary = validate_graph(graph)
        self.assertIn("goal", summary["unresolved"])
        self.assertFalse(summary["semantic_certification"])

    def test_empty_passed_comparator_receipt_is_rejected(self):
        graph = self.graph()
        graph["evidence"][0]["receipt"] = {}
        with self.assertRaises(ContractError):
            validate_graph(graph)

    def test_comparator_configuration_is_bound_to_source(self):
        graph = self.graph()
        graph["evidence"][0]["receipt"]["config_sha256"] = "0" * 64
        with self.assertRaisesRegex(ContractError, "configuration must match"):
            validate_graph(graph)


if __name__ == "__main__":
    unittest.main()
