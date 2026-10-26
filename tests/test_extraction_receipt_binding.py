"""Focused extraction receipt regressions using synthetic process output only."""
from __future__ import annotations

import copy
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

from lean_exposition.contracts import (ContractError, digest, formal_result_assurance,
                                     validate_graph)
from lean_exposition.extraction import to_graph
from lean_exposition.verification import _stream_fields, extract_dependencies
from test_core_review import extraction_fixture, rebind


class ExtractionReceiptBindingTests(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.project = Path(directory.name)
        self.report, self.build = extraction_fixture(self.project)

    def make_current_receipt(self):
        receipt = self.report["receipt"]
        receipt.update(
            extraction_request={"module": "Minimal", "roots": ["result"],
                                "module_prefixes": ["Minimal"], "max_declarations": 1},
            extractor_template_sha256="a" * 64,
            process_status="passed",
        )

    def retain_stdout(self, *, raw=None, prefix="", suffix=""):
        if raw is None:
            raw = {key: value for key, value in self.report.items() if key != "receipt"}
        self.report["receipt"]["stdout"] = (
            prefix + "LEAN_EXPOSITION_JSON:" + json.dumps(raw, ensure_ascii=True) + "\n" + suffix
        )

    def test_matching_report_and_custom_command_with_surrounding_logs(self):
        self.make_current_receipt()
        self.report["receipt"]["command"] = ["custom-lean-wrapper", "--driver"]
        self.report["declarations"][0]["type"] = "∀ α, α → α"
        rebind(self.report)
        self.retain_stdout(prefix="log LEAN_EXPOSITION_JSON:not a report line\n",
                           suffix="later diagnostic\n")
        before = copy.deepcopy(self.report)
        graph = to_graph(self.report, self.project, self.build)
        receipt = graph["evidence"][0]["receipt"]
        self.assertEqual(self.report, before)
        self.assertEqual(receipt["stdout_sha256"], digest(before["receipt"]["stdout"].encode()))
        self.assertNotIn("stdout", receipt)
        self.assertEqual(receipt["command"], ["custom-lean-wrapper", "--driver"])
        self.assertEqual(receipt["report_stdout_binding"], "lean-report-stdout-v1")

    def test_rehashed_structured_report_cannot_disagree_with_retained_raw_output(self):
        self.make_current_receipt()
        self.retain_stdout()
        self.report["declarations"][0]["type"] = "False"
        rebind(self.report)
        with self.assertRaisesRegex(ContractError, "retained.*output"):
            to_graph(self.report, self.project, self.build)

    def test_legacy_marker_bearing_output_is_also_checked(self):
        self.retain_stdout()
        self.report["declarations"][0]["type"] = "False"
        rebind(self.report)
        with self.assertRaisesRegex(ContractError, "retained.*output"):
            to_graph(self.report, self.project)

    def test_raw_unicode_separators_and_crlf_are_not_split_inside_json(self):
        self.make_current_receipt()
        self.report["declarations"][0]["type"] = "α\u2028β\u2029γ"
        rebind(self.report)
        raw = {key: value for key, value in self.report.items() if key != "receipt"}
        self.report["receipt"]["stdout"] = (
            "before\r\nLEAN_EXPOSITION_JSON:" + json.dumps(raw, ensure_ascii=False) + "\r\nafter\r\n"
        )
        graph = to_graph(self.report, self.project)
        self.assertEqual(graph["evidence"][0]["receipt"]["report_stdout_binding"],
                         "lean-report-stdout-v1")

    def test_unicode_separator_does_not_start_a_physical_marker_line(self):
        self.report["receipt"]["stdout"] = "legacy diagnostic\u2028LEAN_EXPOSITION_JSON:not a line"
        graph = to_graph(self.report, self.project)
        self.assertNotIn("report_stdout_binding", graph["evidence"][0]["receipt"])

    def test_producer_report_with_trailing_log_translates(self):
        raw = {key: value for key, value in self.report.items() if key != "receipt"}
        stdout = "LEAN_EXPOSITION_JSON:" + json.dumps(raw) + "\ntrailing log\n"
        process = {
            "status": "passed", "process_status": "passed", "returncode": 0,
            "command": ["custom-lean-wrapper", "driver.lean"],
            "source_hashes": self.report["receipt"]["source_hashes"],
            "source_changed": False,
            **_stream_fields(stdout.encode(), b""),
        }
        with patch("lean_exposition.verification._run_bound", return_value=process):
            report = extract_dependencies(self.project, "Minimal", ["result"],
                                          lean_command=["custom-lean-wrapper"])
        self.build["process_status"] = "passed"
        graph = to_graph(report, self.project, self.build)
        self.assertEqual(graph["nodes"][0]["status"], "kernel_checked")
        self.assertEqual(graph["evidence"][0]["receipt"]["report_stdout_binding"],
                         "lean-report-stdout-v1")
        self.assertTrue(formal_result_assurance(graph, "result")["formal_result_eligible"])

        # The graph is still historically readable if observations are absent,
        # but losing any required observation cannot create current eligibility.
        for field in ("extraction_request", "extractor_sha256", "extractor_template_sha256",
                      "process_status", "stdout_utf8_valid", "stdout_bytes_sha256"):
            with self.subTest(stripped=field):
                altered = copy.deepcopy(report)
                altered["receipt"].pop(field)
                historical = to_graph(altered, self.project, self.build)
                self.assertFalse(formal_result_assurance(historical, "result")["formal_result_eligible"])

        altered = copy.deepcopy(report)
        stdout = altered["receipt"].pop("stdout")
        altered["receipt"]["stdout_sha256"] = digest(stdout.encode())
        altered["receipt"]["report_stdout_binding"] = "lean-report-stdout-v1"
        historical = to_graph(altered, self.project, self.build)
        self.assertNotIn("report_stdout_binding", historical["evidence"][0]["receipt"])
        self.assertFalse(formal_result_assurance(historical, "result")["formal_result_eligible"])

        # A stripped marker plus stripped modern fields can take the legacy
        # readable path, but must not regain current eligibility.
        altered = copy.deepcopy(report)
        altered["receipt"]["stdout"] = "old diagnostic without report\n"
        altered["receipt"].pop("process_status")
        altered["receipt"].pop("stdout_utf8_valid")
        historical = to_graph(altered, self.project, self.build)
        self.assertNotIn("report_stdout_binding", historical["evidence"][0]["receipt"])
        self.assertFalse(formal_result_assurance(historical, "result")["formal_result_eligible"])

        altered_graph = copy.deepcopy(graph)
        altered_graph["evidence"][0]["receipt"].pop("report_stdout_binding")
        validate_graph(altered_graph)
        self.assertFalse(formal_result_assurance(altered_graph, "result")["formal_result_eligible"])

        for evidence in ("extract", "build"):
            with self.subTest(normalized_after_stripping=evidence):
                altered_report, altered_build = copy.deepcopy((report, self.build))
                receipt = altered_report["receipt"] if evidence == "extract" else altered_build
                receipt["stdout_sha256"] = "0" * 64
                receipt.pop("process_status")
                historical = to_graph(altered_report, self.project, altered_build)
                self.assertFalse(formal_result_assurance(historical, "result")["formal_result_eligible"])

    def test_current_receipts_reject_contradictory_text_hashes(self):
        self.make_current_receipt()
        self.retain_stdout()
        receipt = self.report["receipt"]
        receipt["extractor_sha256"] = "b" * 64
        receipt.update(_stream_fields(receipt["stdout"].encode(), b""))
        self.build["process_status"] = "passed"
        for evidence in ("extract", "build"):
            for stream in ("stdout", "stderr"):
                with self.subTest(evidence=evidence, stream=stream):
                    report, build = copy.deepcopy((self.report, self.build))
                    receipt = report["receipt"] if evidence == "extract" else build
                    receipt[stream + "_sha256"] = "0" * 64
                    with self.assertRaisesRegex(ContractError, "text differs from its digest"):
                        to_graph(report, self.project, build)

    def test_historical_v1_build_with_additive_process_status_keeps_legacy_normalization(self):
        self.report["schema_version"] = 1
        self.report["receipt"].pop("report_schema_version")
        for row in self.report["declarations"]:
            row.pop("is_unsafe")
            row.pop("is_partial")
        rebind(self.report)
        self.build.update(process_status="passed", stdout_sha256="0" * 64)
        graph = to_graph(self.report, self.project, self.build)
        build = next(item for item in graph["evidence"] if item["id"] == "build")
        self.assertEqual(build["receipt"]["stdout_sha256"], digest(self.build["stdout"].encode()))
        graph["nodes"][0]["status"] = "kernel_checked"
        validate_graph(graph)
        self.assertFalse(formal_result_assurance(graph, "result")["formal_result_eligible"])

    def test_excessive_canonical_nesting_is_a_contract_error(self):
        deep = current = []
        for _ in range(sys.getrecursionlimit() + 100):
            child = []
            current.append(child)
            current = child
        self.report["optional_metadata"] = deep
        with self.assertRaisesRegex(ContractError, "canonical UTF-8 JSON"):
            to_graph(self.report, self.project)

    def test_excessive_retained_output_nesting_is_a_contract_error(self):
        self.make_current_receipt()
        self.retain_stdout()
        deep = current = []
        for _ in range(sys.getrecursionlimit() + 100):
            child = []
            current.append(child)
            current = child
        raw = {key: value for key, value in self.report.items() if key != "receipt"}
        raw["optional_metadata"] = deep
        with patch("lean_exposition.extraction._decode_extraction_stdout", return_value=raw):
            with self.assertRaisesRegex(ContractError, "retained process output"):
                to_graph(self.report, self.project)

    def test_json_type_difference_is_not_hidden_by_python_equality(self):
        self.make_current_receipt()
        raw = copy.deepcopy({key: value for key, value in self.report.items() if key != "receipt"})
        raw["scope_complete"] = 1  # Python considers 1 == True, JSON does not.
        self.retain_stdout(raw=raw)
        with self.assertRaisesRegex(ContractError, "retained.*output"):
            to_graph(self.report, self.project)

    def test_multiple_markers_and_invalid_json_are_rejected(self):
        self.make_current_receipt()
        self.retain_stdout()
        marker_line = self.report["receipt"]["stdout"]
        for text in (marker_line + marker_line, "LEAN_EXPOSITION_JSON:{\"broken\":\n",
                     "LEAN_EXPOSITION_JSON:[]\n",
                     'LEAN_EXPOSITION_JSON:{"x": 1, "x": 2}\n'):
            with self.subTest(text=text):
                self.report["receipt"]["stdout"] = text
                with self.assertRaises(ContractError):
                    to_graph(self.report, self.project)

    def test_current_retained_output_requires_marker(self):
        self.make_current_receipt()
        self.report["receipt"]["stdout"] = "diagnostic without a report\n"
        with self.assertRaisesRegex(ContractError, "extraction report"):
            to_graph(self.report, self.project)

    def test_missing_stdout_or_legacy_diagnostic_remains_readable(self):
        self.make_current_receipt()
        del self.report["receipt"]["stdout"]
        self.report["receipt"]["report_stdout_binding"] = "lean-report-stdout-v1"
        graph = to_graph(self.report, self.project)
        self.assertNotIn("report_stdout_binding", graph["evidence"][0]["receipt"])

        self.report["schema_version"] = 1
        self.report["receipt"].pop("report_schema_version")
        self.report["receipt"].pop("extraction_request")
        self.report["receipt"].pop("extractor_template_sha256")
        self.report["receipt"].pop("process_status")
        self.report["receipt"]["stdout"] = "legacy redacted diagnostic\n"
        for row in self.report["declarations"]:
            row.pop("is_unsafe")
            row.pop("is_partial")
        rebind(self.report)
        graph = to_graph(self.report, self.project, self.build)
        self.assertEqual(graph["schema_version"], "1.0")
        self.assertEqual(graph["nodes"][0]["status"], "unverified")
        self.assertNotIn("report_stdout_binding", graph["evidence"][0]["receipt"])
        graph["nodes"][0]["status"] = "kernel_checked"
        validate_graph(graph)
        self.assertFalse(formal_result_assurance(graph, "result")["formal_result_eligible"])

    def test_request_contradictions_rejected_at_translation(self):
        self.make_current_receipt()
        self.retain_stdout()
        original = copy.deepcopy(self.report)
        for field, value in (("module", "Other"), ("max_declarations", 0),
                             ("roots", ["other"]), ("module_prefixes", ["Other"])):
            with self.subTest(field=field):
                report = copy.deepcopy(original)
                report["receipt"]["extraction_request"][field] = value
                with self.assertRaisesRegex(ContractError, "extraction request"):
                    to_graph(report, self.project)


if __name__ == "__main__":
    unittest.main()
