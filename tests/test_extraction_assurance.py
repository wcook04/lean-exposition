"""Snapshot/protocol regressions and an opt-in real Lean inspection fixture.

The first class uses synthetic receipts and establishes Python behaviour only.
The second class runs the pinned Lean toolchain when explicitly enabled.
"""
from __future__ import annotations

import copy
import json
import os
from pathlib import Path
import tempfile
import unittest

from lean_exposition.contracts import ContractError, digest, encoded, validate_graph, validate_process_receipt
from lean_exposition.extraction import to_graph
from lean_exposition.verification import check_build, extract_dependencies, extractor_source
from test_core_review import extraction_fixture, rebind


class ExtractionAssuranceTests(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.project = Path(directory.name)
        self.report, self.build = extraction_fixture(self.project)

    def test_added_project_source_invalidates_historical_snapshot(self):
        (self.project / "Added.lean").write_text("axiom added : False\n")
        with self.assertRaisesRegex(ContractError, "snapshot differs.*Added.lean"):
            to_graph(self.report, self.project, self.build)

    def test_matching_receipts_cannot_both_omit_an_existing_source(self):
        (self.project / "Support.lean").write_text("theorem support : True := True.intro\n")
        self.assertEqual(self.report["receipt"]["source_hashes"], self.build["source_hashes"])
        with self.assertRaisesRegex(ContractError, "snapshot differs.*Support.lean"):
            to_graph(self.report, self.project, self.build)

    def test_snapshot_boundary_still_excludes_cached_dependency_sources(self):
        cache = self.project / ".lake/packages/dep"
        cache.mkdir(parents=True)
        (cache / "Imported.lean").write_text("axiom imported : False\n")
        graph = to_graph(self.report, self.project, self.build)
        self.assertEqual(graph["nodes"][0]["status"], "kernel_checked")
        self.assertIn("outside that snapshot", " ".join(graph["notes"]))

    def test_repeated_requested_roots_produce_unique_goals_without_rebinding_report(self):
        self.report["roots"].append("result")
        rebind(self.report)
        original = copy.deepcopy(self.report)
        graph = to_graph(self.report, self.project, self.build)
        self.assertEqual(graph["selected_goals"], ["result"])
        self.assertEqual(self.report, original)
        self.assertEqual(graph["evidence"][0]["receipt"]["report_sha256"],
                         original["receipt"]["report_sha256"])
        validate_graph(graph)

    def test_recorded_extraction_request_survives_projection(self):
        request = {"module": "Minimal", "roots": ["result"],
                   "module_prefixes": ["Minimal"], "max_declarations": 1}
        self.report["receipt"]["extraction_request"] = request
        self.report["receipt"]["extractor_template_sha256"] = "a" * 64
        graph = to_graph(self.report, self.project)
        receipt = graph["evidence"][0]["receipt"]
        self.assertEqual(receipt["extraction_request"], request)
        self.assertEqual(receipt["extractor_template_sha256"], "a" * 64)

    def test_inconsistent_extraction_request_is_rejected(self):
        request = {"module": "Minimal", "roots": ["result"],
                   "module_prefixes": ["Minimal"], "max_declarations": 1}
        cases = {"module": "Different", "roots": ["different"],
                 "module_prefixes": ["Different"], "max_declarations": True}
        for field, value in cases.items():
            with self.subTest(field=field):
                report = copy.deepcopy(self.report)
                report["receipt"]["extraction_request"] = dict(request, **{field: value})
                with self.assertRaisesRegex(ContractError, "extraction request"):
                    to_graph(report, self.project)

    def test_request_cap_cannot_be_smaller_than_emitted_inventory(self):
        second = copy.deepcopy(self.report["declarations"][0])
        second["name"] = "other"
        self.report["declarations"].append(second)
        self.report["receipt"]["extraction_request"] = {
            "module": "Minimal", "roots": ["result"],
            "module_prefixes": ["Minimal"], "max_declarations": 1,
        }
        rebind(self.report)
        with self.assertRaisesRegex(ContractError, "declaration limit"):
            to_graph(self.report, self.project)

    def test_malformed_receipt_is_a_contract_failure(self):
        self.report["receipt"] = []
        with self.assertRaisesRegex(ContractError, "receipt must be an object"):
            to_graph(self.report, self.project)

    def test_malformed_receipt_command_is_a_contract_failure(self):
        for command in (None, [], [1], "lake"):
            with self.subTest(command=command):
                report = copy.deepcopy(self.report)
                report["receipt"]["command"] = command
                with self.assertRaisesRegex(ContractError, "command must be"):
                    to_graph(report, self.project)

    def test_public_receipt_retains_raw_and_display_stream_identities(self):
        receipt = self.report["receipt"]
        receipt.update(stderr="\ufffd", stderr_bytes_sha256=digest(b"\xff"),
                       stderr_utf8_valid=False, output_decoding="utf-8-with-replacement",
                       process_status="passed")
        graph = to_graph(self.report, self.project)
        public = graph["evidence"][0]["receipt"]
        self.assertEqual(public["stderr_sha256"], digest("\ufffd".encode("utf-8")))
        self.assertEqual(public["stderr_bytes_sha256"], digest(b"\xff"))
        self.assertFalse(public["stderr_utf8_valid"])
        self.assertEqual(public["process_status"], "passed")
        self.assertNotIn("stderr", public)

    def test_public_receipt_rejects_malformed_raw_stream_metadata(self):
        for field, value in (("stderr_bytes_sha256", "bad"),
                             ("stderr_utf8_valid", 0), ("process_status", "accepted")):
            with self.subTest(field=field):
                report = copy.deepcopy(self.report)
                report["receipt"][field] = value
                with self.assertRaisesRegex(ContractError, "invalid receipt"):
                    to_graph(report, self.project)

    def test_passed_receipts_cannot_record_a_failed_process(self):
        for evidence_id in ("extract", "build"):
            for process_status in ("failed", "unavailable", "timed_out", "not_run"):
                with self.subTest(evidence=evidence_id, process_status=process_status):
                    report, build = copy.deepcopy((self.report, self.build))
                    receipt = report["receipt"] if evidence_id == "extract" else build
                    receipt["process_status"] = process_status
                    with self.assertRaisesRegex(ContractError, "passed recorded process"):
                        to_graph(report, self.project, build)

                    # Direct graph ingestion must enforce the same rule;
                    # otherwise redaction/projection offers a bypass.
                    graph = to_graph(self.report, self.project, self.build)
                    item = next(e for e in graph["evidence"] if e["id"] == evidence_id)
                    item["receipt"]["process_status"] = process_status
                    with self.assertRaisesRegex(ContractError, "passed recorded process"):
                        validate_graph(graph)

    def test_successful_extraction_cannot_record_invalid_stdout(self):
        self.report["receipt"]["stdout_utf8_valid"] = False
        with self.assertRaisesRegex(ContractError, "valid UTF-8 stdout"):
            to_graph(self.report, self.project, self.build)
        del self.report["receipt"]["stdout_utf8_valid"]
        graph = to_graph(self.report, self.project, self.build)
        graph["evidence"][0]["receipt"]["stdout_utf8_valid"] = False
        with self.assertRaisesRegex(ContractError, "valid UTF-8 stdout"):
            validate_graph(graph)

    def test_utf8_valid_raw_digest_must_match_retained_text_before_projection(self):
        for evidence_id in ("extract", "build"):
            for stream in ("stdout", "stderr"):
                with self.subTest(evidence=evidence_id, stream=stream):
                    report, build = copy.deepcopy((self.report, self.build))
                    receipt = report["receipt"] if evidence_id == "extract" else build
                    receipt[stream + "_utf8_valid"] = True
                    receipt[stream + "_bytes_sha256"] = digest(b"different bytes")
                    # A stale legacy text hash agreeing with the incorrect raw
                    # hash cannot override the retained diagnostic text.
                    receipt[stream + "_sha256"] = receipt[stream + "_bytes_sha256"]
                    with self.assertRaisesRegex(ContractError, "byte and text digests disagree"):
                        to_graph(report, self.project, build)

    def test_redacted_utf8_valid_raw_digest_must_match_recorded_text_digest(self):
        for evidence_id in ("extract", "build"):
            for stream in ("stdout", "stderr"):
                with self.subTest(evidence=evidence_id, stream=stream):
                    graph = to_graph(self.report, self.project, self.build)
                    receipt = next(e["receipt"] for e in graph["evidence"] if e["id"] == evidence_id)
                    self.assertNotIn(stream, receipt)
                    receipt[stream + "_utf8_valid"] = True
                    receipt[stream + "_bytes_sha256"] = receipt[stream + "_sha256"]
                    validate_graph(graph)
                    receipt[stream + "_bytes_sha256"] = digest(b"different bytes")
                    with self.assertRaisesRegex(ContractError, "byte and text digests disagree"):
                        validate_graph(graph)

    def test_projection_raw_text_canonicalizes_legacy_digest_without_mutation(self):
        for evidence_id in ("extract", "build"):
            for stream in ("stdout", "stderr"):
                with self.subTest(evidence=evidence_id, stream=stream):
                    report, build = copy.deepcopy((self.report, self.build))
                    receipt = report["receipt"] if evidence_id == "extract" else build
                    observed = digest(receipt[stream].encode("utf-8"))
                    receipt[stream + "_sha256"] = digest(b"stale legacy text")
                    receipt[stream + "_utf8_valid"] = True
                    receipt[stream + "_bytes_sha256"] = observed
                    original = copy.deepcopy((report, build))
                    graph = to_graph(report, self.project, build)
                    public = next(e["receipt"] for e in graph["evidence"]
                                  if e["id"] == evidence_id)
                    self.assertEqual(public[stream + "_sha256"], observed)
                    self.assertEqual(public[stream + "_bytes_sha256"], observed)
                    self.assertEqual((report, build), original)

    def test_direct_graph_ingestion_rejects_text_digest_disagreement(self):
        for evidence_id in ("extract", "build"):
            for stream in ("stdout", "stderr"):
                with self.subTest(evidence=evidence_id, stream=stream):
                    graph = to_graph(self.report, self.project, self.build)
                    receipt = next(e["receipt"] for e in graph["evidence"]
                                   if e["id"] == evidence_id)
                    receipt[stream] = "text contradicting the recorded digest"
                    with self.assertRaisesRegex(ContractError, "text differs from its digest"):
                        validate_graph(graph)

    def test_failed_source_binding_can_retain_a_passed_process(self):
        receipt = copy.deepcopy(self.build)
        receipt.update(status="failed", process_status="passed", source_changed=True,
                       failure_reason="source_changed_during_run")
        validate_process_receipt(receipt)
        graph = to_graph(self.report, self.project, self.build)
        build = next(e for e in graph["evidence"] if e["id"] == "build")
        build["status"] = "failed"
        build["receipt"].update(status="failed", process_status="passed", source_changed=True,
                                failure_reason="source_changed_during_run")
        for node in graph["nodes"]:
            if node["status"] == "kernel_checked":
                node["status"] = "unverified"
        validate_graph(graph)

    def test_optional_legacy_process_metadata_is_not_invented(self):
        graph = to_graph(self.report, self.project, self.build)
        for item in graph["evidence"]:
            self.assertNotIn("process_status", item["receipt"])
            self.assertNotIn("stdout_utf8_valid", item["receipt"])
            self.assertNotIn("stdout_bytes_sha256", item["receipt"])
        validate_graph(graph)

    def test_utf8_valid_redacted_bytes_require_a_text_digest(self):
        graph = to_graph(self.report, self.project, self.build)
        receipt = graph["evidence"][0]["receipt"]
        receipt["stdout_utf8_valid"] = True
        receipt["stdout_bytes_sha256"] = receipt.pop("stdout_sha256")
        with self.assertRaisesRegex(ContractError, "require a text digest"):
            validate_graph(graph)


@unittest.skipUnless(os.environ.get("LEAN_EXPOSITION_RUN_LEAN") == "1",
                     "set LEAN_EXPOSITION_RUN_LEAN=1 for the pinned Lean integration fixture")
class LeanInspectionIntegrationTests(unittest.TestCase):
    def test_private_proof_axioms_structural_edges_and_truncation(self):
        with tempfile.TemporaryDirectory(prefix="lean-exposition-inspection-") as directory:
            project = Path(directory)
            archive = os.environ.get("LEAN_EXPOSITION_VALIDATION_DIR")
            destination = Path(archive) / "private-structure" if archive else None
            if destination:
                destination.mkdir(parents=True, exist_ok=True)

            def retain(name, value):
                if destination:
                    (destination / name).write_bytes(encoded(value))

            sources = {
                "lean-toolchain": "leanprover/lean4:v4.35.0-rc2\n",
                "lakefile.toml": ('name = "inspection_fixture"\nversion = "0.1.0"\n'
                                  'defaultTargets = ["Inspection"]\n\n'
                                  '[[lean_lib]]\nname = "Inspection"\n'),
                "lake-manifest.json": json.dumps({
                    "version": "1.2.0", "packagesDir": ".lake/packages", "packages": [],
                    "name": "inspection_fixture", "lakeDir": ".lake", "fixedToolchain": False,
                }) + "\n",
                "Inspection.lean": (
                    "namespace Inspection\n"
                    "axiom trusted : True\n"
                    "private theorem hidden : True := trusted\n"
                    "theorem visible : True := hidden\n"
                    "theorem withHole : True := by sorry\n"
                    "inductive Token where\n"
                    "  | empty\n"
                    "  | push (tail : Token)\n"
                    "partial def looping (n : Nat) : Nat := looping n\n"
                    "def loopAlias (n : Nat) : Nat := looping n\n"
                    "theorem alias_eq (n : Nat) : loopAlias n = looping n := rfl\n"
                    "end Inspection\n"
                ),
            }
            for name, contents in sources.items():
                (project / name).write_text(contents, encoding="utf-8")
                if destination:
                    (destination / name).write_text(contents, encoding="utf-8")
            build = check_build(project, "Inspection", timeout=600)
            retain("build-receipt.json", build)
            self.assertEqual(build["status"], "passed", build)
            roots = ["Inspection.visible", "Inspection.withHole", "Inspection.Token.rec",
                     "Inspection.alias_eq"]
            report = extract_dependencies(project, "Inspection", roots, timeout=600)
            retain("raw-report.json", report)
            if destination:
                (destination / "generated-driver.lean").write_text(
                    extractor_source("Inspection", roots, ["Inspection"]), encoding="utf-8")
            rows = {row["name"]: row for row in report["declarations"]}
            hidden = [name for name in rows if name.endswith(".Inspection.hidden")]
            self.assertEqual(len(hidden), 1, rows)
            self.assertTrue(rows[hidden[0]]["body_available"])
            self.assertIn(hidden[0], rows["Inspection.visible"]["value_dependencies"])
            self.assertIn("Inspection.trusted", rows["Inspection.visible"]["axioms"])
            self.assertTrue(rows["Inspection.withHole"]["has_sorry"])
            structural = rows["Inspection.Token.rec"]["structural_dependencies"]
            self.assertIn("Inspection.Token.empty", structural)
            self.assertIn("Inspection.Token.push", structural)
            graph = to_graph(report, project, build)
            retain("graph.json", graph)
            nodes = {node["id"]: node for node in graph["nodes"]}
            self.assertEqual(nodes["Inspection.withHole"]["status"], "unverified")
            self.assertEqual(nodes["sorryAx"]["status"], "open")
            self.assertEqual(nodes["Inspection.trusted"]["status"], "axiom")
            self.assertIn("Inspection.trusted", nodes["Inspection.visible"]["assumption_ids"])
            # A checked theorem about an opaque symbol proves its displayed
            # proposition. It does not certify termination of executable code
            # or safety classification of the complete dependency closure.
            self.assertEqual(nodes["Inspection.alias_eq"]["status"], "kernel_checked")
            self.assertEqual(nodes["Inspection.loopAlias"]["status"], "kernel_checked")
            self.assertEqual(nodes["Inspection.looping"]["status"], "unverified")
            self.assertIsNone(nodes["Inspection.looping"]["is_partial"])
            self.assertIn({"from": "Inspection.loopAlias", "to": "Inspection.looping",
                           "kind": "lean_value_dependency", "evidence_ids": ["extract"]},
                          graph["edges"])
            self.assertFalse(validate_graph(graph)["semantic_certification"])

            capped = extract_dependencies(project, "Inspection", roots,
                                          max_declarations=1, timeout=600)
            retain("capped-raw-report.json", capped)
            self.assertEqual(len(capped["declarations"]), 1)
            self.assertFalse(capped["scope_complete"])
            self.assertTrue(capped["unexpanded_declarations"])
            capped_graph = to_graph(capped, project, build)
            retain("capped-graph.json", capped_graph)
            self.assertEqual(capped_graph["extraction_status"], "partial")
            self.assertTrue(validate_graph(capped_graph)["unresolved"])


if __name__ == "__main__":
    unittest.main()
