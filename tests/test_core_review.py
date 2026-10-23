"""Synthetic adversarial checks of evidence binding, without claiming a Lean run."""
from __future__ import annotations

import copy
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from lean_exposition import bundle
from lean_exposition.contracts import (
    ContractError, closure, decode_json, digest, encoded, local_path,
    read_json, validate_artifact, validate_graph, write_json,
)
from lean_exposition.extraction import to_graph
from lean_exposition.intake import validate_lock
from test_adversarial import synthetic_artifact, synthetic_graph


def extraction_fixture(root: Path):
    (root / "Minimal.lean").write_bytes(b"theorem result : True := True.intro\n")
    (root / "lean-toolchain").write_bytes(b"leanprover/lean4:v4.35.0\n")
    hashes = {name: digest((root / name).read_bytes())
              for name in ("Minimal.lean", "lean-toolchain")}
    report = {
        "schema_version": 2, "module": "Minimal", "roots": ["result"],
        "module_prefixes": ["Minimal"], "scope_complete": True,
        "declarations": [{
            "name": "result", "kind": "theorem", "type": "True",
            "type_dependencies": [], "value_dependencies": [],
            "structural_dependencies": [], "axioms": [], "has_sorry": False,
            "is_unsafe": False, "is_partial": False,
            "body_available": True, "source": {"module": "Minimal", "line": 1},
        }],
        "external_dependencies": [], "missing_declarations": [],
        "unexpanded_declarations": [], "unavailable_bodies": [],
        "evidence_kind": "elaborated_expression_dependencies",
    }
    report["receipt"] = {
        "status": "passed", "returncode": 0, "command": ["lake", "env", "lean", "--stdin"],
        "module": "Minimal", "source_hashes": hashes, "source_changed": False,
        "report_schema_version": 2,
        "stdout": "synthetic diagnostic", "stderr": "",
        "report_sha256": digest(encoded(report)),
        "evidence_kind": "elaboration_process",
    }
    build = {
        "status": "passed", "returncode": 0, "command": ["lake", "build", "Minimal"],
        "module": "Minimal", "source_hashes": hashes.copy(), "source_changed": False,
        "stdout": "synthetic diagnostic", "stderr": "", "evidence_kind": "lean_build",
    }
    return report, build


def rebind(report):
    report["receipt"]["report_sha256"] = digest(encoded({k: v for k, v in report.items() if k != "receipt"}))


class ExtractionBindingTests(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.root = Path(tmp.name)
        self.report, self.build = extraction_fixture(self.root)

    def test_extraction_and_build_are_distinct(self):
        extracted = to_graph(self.report, self.root)
        self.assertEqual(extracted["nodes"][0]["status"], "unverified")
        built = to_graph(self.report, self.root, self.build)
        self.assertEqual(built["nodes"][0]["status"], "kernel_checked")
        self.assertFalse(validate_graph(built)["semantic_certification"])

    def test_unsafe_and_partial_declarations_keep_build_evidence_without_promotion(self):
        for flag in ("is_unsafe", "is_partial"):
            with self.subTest(flag=flag):
                report = copy.deepcopy(self.report)
                report["declarations"][0][flag] = True
                rebind(report)
                graph = to_graph(report, self.root, self.build)
                self.assertEqual(graph["nodes"][0]["status"], "unverified")
                self.assertIn("build", graph["nodes"][0]["evidence_ids"])
                graph["nodes"][0]["status"] = "kernel_checked"
                with self.assertRaises(ContractError):
                    validate_graph(graph)

    def test_opaque_partiality_is_unknown_and_cannot_be_promoted(self):
        report = copy.deepcopy(self.report)
        report["declarations"][0].update(kind="opaque", is_partial=None)
        rebind(report)
        graph = to_graph(report, self.root, self.build)
        node = graph["nodes"][0]
        self.assertIsNone(node["is_partial"])
        self.assertEqual(node["status"], "unverified")
        self.assertIn("build", node["evidence_ids"])
        node["status"] = "kernel_checked"
        with self.assertRaisesRegex(ContractError, "safe declaration classification"):
            validate_graph(graph)

        report["declarations"][0]["is_partial"] = False
        rebind(report)
        with self.assertRaisesRegex(ContractError, "null for opaque"):
            to_graph(report, self.root, self.build)

    def test_public_failed_build_keeps_launch_stage_without_diagnostics(self):
        failed = copy.deepcopy(self.build)
        failed.update(status="unavailable", returncode=None, stdout="", stderr="private path",
                      failure_stage="process_launch", error_type="PermissionError", errno=13)
        graph = to_graph(self.report, self.root, failed)
        public = next(item["receipt"] for item in graph["evidence"] if item["id"] == "build")
        self.assertEqual((public["failure_stage"], public["error_type"], public["errno"]),
                         ("process_launch", "PermissionError", 13))
        self.assertNotIn("stderr", public)
        validate_graph(graph)
        failed["failure_stage"] = "/private/host/path"
        with self.assertRaisesRegex(ContractError, "invalid receipt failure_stage"):
            to_graph(self.report, self.root, failed)

    def test_extraction_process_receipt_cannot_stand_in_for_a_build(self):
        with self.assertRaisesRegex(ContractError, "lean_build evidence"):
            to_graph(self.report, self.root, self.report["receipt"])

    def test_build_receipt_cannot_stand_in_for_an_extraction_process(self):
        self.report["receipt"]["evidence_kind"] = "lean_build"
        with self.assertRaisesRegex(ContractError, "elaboration_process evidence"):
            to_graph(self.report, self.root)

    def test_unavailable_body_retains_its_inspection_boundary(self):
        self.report["declarations"][0]["body_available"] = False
        self.report["unavailable_bodies"] = ["result"]
        self.report["scope_complete"] = False
        rebind(self.report)
        graph = to_graph(self.report, self.root)
        self.assertEqual(graph["extraction_status"], "partial")
        self.assertEqual(graph["nodes"][0]["status"], "unverified")
        self.assertIn("Declaration body unavailable", graph["nodes"][0]["boundary"])
        self.assertIn("axiom inspection are incomplete", graph["nodes"][0]["boundary"])

    def test_unavailable_body_and_successful_build_remain_distinct(self):
        self.report["declarations"][0]["body_available"] = False
        self.report["unavailable_bodies"] = ["result"]
        self.report["scope_complete"] = False
        rebind(self.report)
        graph = to_graph(self.report, self.root, self.build)
        self.assertEqual(graph["extraction_status"], "partial")
        self.assertEqual(graph["nodes"][0]["status"], "kernel_checked")
        self.assertIn("Declaration body unavailable", graph["nodes"][0]["boundary"])

    def test_unavailable_dependency_marks_consumer_axiom_inspection(self):
        dependency = copy.deepcopy(self.report["declarations"][0])
        dependency.update(name="support", body_available=False)
        self.report["declarations"].append(dependency)
        self.report["declarations"][0]["value_dependencies"] = ["support"]
        self.report["unavailable_bodies"] = ["support"]
        self.report["scope_complete"] = False
        rebind(self.report)
        graph = to_graph(self.report, self.root, self.build)
        nodes = {n["id"]: n for n in graph["nodes"]}
        self.assertIn("A dependency body is unavailable", nodes["result"]["boundary"])
        self.assertIn("axiom inspection are incomplete", nodes["result"]["boundary"])
        self.assertIn("Declaration body unavailable", nodes["support"]["boundary"])
        self.assertEqual(nodes["result"]["status"], "kernel_checked")

    def test_body_flag_marks_partial_even_if_summary_omits_it(self):
        self.report["declarations"][0]["body_available"] = False
        rebind(self.report)
        with self.assertRaisesRegex(ContractError, "claims complete scope"):
            to_graph(self.report, self.root)
        self.report["scope_complete"] = False
        rebind(self.report)
        graph = to_graph(self.report, self.root)
        self.assertEqual(graph["extraction_status"], "partial")
        self.assertIn("Declaration body unavailable", graph["nodes"][0]["boundary"])

    def test_primitive_without_body_has_no_missing_proof_body(self):
        self.report["declarations"][0].update(kind="inductive", body_available=False)
        rebind(self.report)
        graph = to_graph(self.report, self.root)
        self.assertEqual(graph["extraction_status"], "complete")
        self.assertEqual(graph["nodes"][0]["boundary"], "Elaborated type/proof references; theorem hypotheses remain in the displayed type.")

    def test_direct_translation_rejects_malformed_raw_report(self):
        for field, value in (("scope_complete", "false"), ("schema_version", True)):
            with self.subTest(field=field):
                report = copy.deepcopy(self.report)
                report[field] = value
                rebind(report)
                with self.assertRaises(ContractError):
                    to_graph(report, self.root)

    def test_direct_translation_rejects_nonencodable_report(self):
        for metadata in (False, True):
            with self.subTest(metadata=metadata):
                report = copy.deepcopy(self.report)
                if metadata:
                    report["note"] = "\ud800"
                else:
                    report["declarations"][0]["type"] = "\ud800"
                with self.assertRaisesRegex(ContractError, "UTF-8"):
                    to_graph(report, self.root)

    def test_incomplete_dependency_inventory_remains_partial(self):
        self.report["scope_complete"] = False
        self.report["declarations"][0]["value_dependencies"] = ["unclassified"]
        rebind(self.report)
        graph = to_graph(self.report, self.root)
        self.assertEqual(graph["extraction_status"], "partial")
        self.assertIn("unclassified", validate_graph(graph)["unresolved"])

    def test_custom_source_directory_fails_with_the_expected_module_path(self):
        (self.root / "src").mkdir()
        (self.root / "Minimal.lean").rename(self.root / "src/Minimal.lean")
        hashes = self.report["receipt"]["source_hashes"]
        hashes["src/Minimal.lean"] = hashes.pop("Minimal.lean")
        with self.assertRaisesRegex(ContractError, "selected module source unavailable: Minimal.lean"):
            to_graph(self.report, self.root)

    def test_failed_extraction_cannot_be_translated_as_success(self):
        self.report["receipt"]["status"] = "failed"
        with self.assertRaisesRegex(ContractError, "successful process"):
            to_graph(self.report, self.root)

    def test_modified_report_cannot_reuse_a_receipt(self):
        self.report["declarations"][0]["type"] = "False"
        with self.assertRaisesRegex(ContractError, "report differs"):
            to_graph(self.report, self.root)

    def test_modified_source_cannot_reuse_a_receipt(self):
        (self.root / "Minimal.lean").write_bytes(b"theorem result : False := by sorry\n")
        with self.assertRaisesRegex(ContractError, "source differs"):
            to_graph(self.report, self.root)

    def test_build_of_different_module_cannot_certify_this_module(self):
        self.build["module"] = "Unrelated"
        with self.assertRaisesRegex(ContractError, "different Lean module"):
            to_graph(self.report, self.root, self.build)

    def test_failed_build_does_not_change_extraction_status(self):
        self.build.update(status="failed", returncode=1)
        graph = to_graph(self.report, self.root, self.build)
        self.assertEqual(graph["nodes"][0]["status"], "unverified")
        self.assertEqual(validate_graph(graph)["failed_evidence"], ["build"])

    def test_raw_diagnostics_and_absolute_command_paths_are_not_embedded(self):
        self.build["command"][0] = "/synthetic/toolchain/bin/lake"
        self.report["receipt"]["stderr"] = "synthetic diagnostic with local information"
        self.report["receipt"]["local_note"] = "synthetic diagnostic metadata"
        graph = to_graph(self.report, self.root, self.build)
        self.assertNotIn(b"synthetic diagnostic", encoded(graph))
        self.assertNotIn(b"/synthetic/toolchain", encoded(graph))
        self.assertTrue(graph["evidence"][1]["receipt"]["command_paths_redacted"])

    def test_floating_toolchain_is_not_a_pin(self):
        (self.root / "lean-toolchain").write_bytes(b"leanprover/lean4:stable\n")
        self.report["receipt"]["source_hashes"]["lean-toolchain"] = digest((self.root / "lean-toolchain").read_bytes())
        with self.assertRaisesRegex(ContractError, "pin a release"):
            to_graph(self.report, self.root)

    def test_missing_selected_root_is_retained_as_unresolved(self):
        self.report["roots"].append("unexpanded")
        self.report["unexpanded_declarations"] = ["unexpanded"]
        self.report["scope_complete"] = False
        rebind(self.report)
        graph = to_graph(self.report, self.root)
        self.assertEqual(graph["extraction_status"], "partial")
        self.assertIn("unexpanded", validate_graph(graph)["unresolved"])

    def test_sorry_inventory_cannot_be_hidden_by_flag(self):
        self.report["declarations"][0]["axioms"] = ["sorryAx"]
        rebind(self.report)
        with self.assertRaisesRegex(ContractError, "sorry inventory"):
            to_graph(self.report, self.root, self.build)

    def test_english_claim_cannot_be_kernel_checked(self):
        graph = to_graph(self.report, self.root, self.build)
        graph["nodes"][0]["kind"] = "claim"
        with self.assertRaisesRegex(ContractError, "formal (declarations|graph projection)"):
            validate_graph(graph)

    def test_edited_statement_cannot_keep_extraction_binding(self):
        graph = to_graph(self.report, self.root, self.build)
        graph["nodes"][0]["statement"] = "False"
        with self.assertRaisesRegex(ContractError, "projection differs"):
            validate_graph(graph)

    def test_removed_dependency_cannot_keep_extraction_binding(self):
        self.report["declarations"][0]["value_dependencies"] = ["support"]
        self.report["external_dependencies"] = [{"name": "support", "kind": "theorem", "module": "Init"}]
        rebind(self.report)
        graph = to_graph(self.report, self.root, self.build)
        graph["edges"] = []
        with self.assertRaisesRegex(ContractError, "projection differs"):
            validate_graph(graph)

    def test_environment_hash_cannot_be_changed_independently(self):
        graph = to_graph(self.report, self.root, self.build)
        graph["sources"][-1]["sha256"] = "0" * 64
        with self.assertRaisesRegex(ContractError, "environment identity"):
            validate_graph(graph)

    def test_prose_label_can_be_edited_without_changing_formal_binding(self):
        graph = to_graph(self.report, self.root, self.build)
        graph["nodes"][0]["label"] = "A clearer label"
        validate_graph(graph)

    def test_build_receipt_must_include_node_source(self):
        graph = to_graph(self.report, self.root, self.build)
        graph["evidence"][1]["source_ids"] = ["environment"]
        with self.assertRaisesRegex(ContractError, "source-bound Lean build"):
            validate_graph(graph)

    def test_passed_evidence_cannot_disagree_with_receipt_status(self):
        graph = to_graph(self.report, self.root, self.build)
        graph["evidence"][1]["receipt"]["status"] = "failed"
        with self.assertRaisesRegex(ContractError, "status differs"):
            validate_graph(graph)

    def test_receipt_hashes_must_match_graph_source(self):
        graph = to_graph(self.report, self.root, self.build)
        graph["evidence"][1]["receipt"]["source_hashes"]["Minimal.lean"] = "0" * 64
        with self.assertRaisesRegex(ContractError, "does not bind"):
            validate_graph(graph)


class ArtifactBoundaryTests(unittest.TestCase):
    def test_platform_closure_does_not_absorb_assumptions_or_support_edges(self):
        graph = synthetic_graph()
        graph["edges"].append({"from": "prerequisite", "to": "goal", "kind": "platform_decomposition", "evidence_ids": []})
        self.assertEqual(closure(graph), {"goal", "prerequisite", "assumption"})
        self.assertEqual(closure(graph, edge_kinds={"platform_decomposition"}), {"goal"})
        self.assertEqual(closure(graph, ["prerequisite"], {"platform_decomposition"}), {"goal", "prerequisite"})

    def test_formal_result_label_cannot_promote_conditional_claim(self):
        graph = synthetic_graph()
        artifact, content = synthetic_artifact(graph)
        artifact["passages"][0]["evidence_class"] = "formal_result"
        with self.assertRaisesRegex(ContractError, "kernel-checked declarations"):
            validate_artifact(artifact, graph, digest(encoded(graph)), content)

    def test_selected_goal_requires_authored_passage(self):
        graph = synthetic_graph()
        artifact, content = synthetic_artifact(graph)
        artifact["claim_ids"] = ["prerequisite"]
        artifact["passages"][0]["claim_ids"] = ["prerequisite"]
        with self.assertRaisesRegex(ContractError, "every selected goal"):
            validate_artifact(artifact, graph, digest(encoded(graph)), content)

    def test_duplicate_anchors_are_not_distinct_correspondence(self):
        graph = synthetic_graph()
        artifact, content = synthetic_artifact(graph)
        extra = copy.deepcopy(artifact["passages"][0])
        extra["rationale"] = "A different rationale cannot reuse one anchor."
        artifact["passages"].append(extra)
        with self.assertRaisesRegex(ContractError, "duplicate passage anchor"):
            validate_artifact(artifact, graph, digest(encoded(graph)), content)

    def test_unmapped_passage_marker_is_rejected(self):
        graph = synthetic_graph()
        artifact, content = synthetic_artifact(graph)
        content += b"<!-- passage:extra -->extra<!-- /passage:extra -->\n"
        artifact["content_sha256"] = digest(content)
        with self.assertRaisesRegex(ContractError, "unmapped passage"):
            validate_artifact(artifact, graph, digest(encoded(graph)), content)


class BundleCaptureTests(unittest.TestCase):
    def test_check_uses_hashed_capture_not_later_file_reads(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "bundle"
            bundle.scaffold(synthetic_graph(), root)
            original = bundle.validate_graph

            def mutate_after_capture(graph):
                (root / "papers/long.json").write_bytes(b"not JSON anymore\n")
                return original(graph)

            with patch.object(bundle, "validate_graph", side_effect=mutate_after_capture):
                self.assertTrue(bundle.check_bundle(root)["valid"])
            with self.assertRaisesRegex(ContractError, "hash mismatch"):
                bundle.check_bundle(root)

    def test_unknown_bundle_version_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "bundle"
            bundle.scaffold(synthetic_graph(), root)
            manifest = read_json(root / "manifest.json")
            manifest["bundle_version"] = "99.0.0"
            write_json(root / "manifest.json", manifest)
            with self.assertRaises(ContractError):
                bundle.check_bundle(root)

    def test_json_rejects_duplicate_keys_and_nonfinite_values(self):
        for data in (b'{"a":1,"a":2}', b'{"a":NaN}', b'{"a":Infinity}'):
            with self.subTest(data=data), self.assertRaises(ContractError):
                decode_json(data)

    def test_paths_reject_aliases_and_symlink_ancestry(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            for name in ("a//b", "./a", "a/../b", "a\x00b", "a/"):
                with self.subTest(name=name), self.assertRaises(ContractError):
                    local_path(root, name)
            (root / "real").mkdir()
            (root / "alias").symlink_to(root / "real", target_is_directory=True)
            with self.assertRaisesRegex(ContractError, "symlink"):
                local_path(root, "alias/output.json")

    def test_lock_cannot_substitute_a_different_repository_at_same_revision(self):
        revision = "1" * 40
        lock = {"schema_version": "1.0", "revision": revision, "license": "MIT",
                "repository": "https://github.com/example/expected",
                "files": [{"path": "source.txt", "url": f"https://raw.githubusercontent.com/example/other/{revision}/source.txt",
                           "bytes": 0, "sha256": digest(b"")}]}
        with self.assertRaisesRegex(ContractError, "locked repository"):
            validate_lock(lock)


if __name__ == "__main__":
    unittest.main()
