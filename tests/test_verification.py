import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

from lean_exposition.verification import (
    VerificationError, check_build, extract_dependencies, extractor_source,
    verify_comparator,
)


class VerificationTests(unittest.TestCase):
    def test_generated_syntax_rejects_code_injection(self):
        with self.assertRaises(ValueError):
            extractor_source("Minimal\nrun_cmd unsafeCode", ["Minimal.result"], ["Minimal"])
        with self.assertRaises(ValueError):
            extractor_source("Minimal", ["Minimal.result; unsafeCode"], ["Minimal"])

    def test_packaged_template_uses_elaborated_constants(self):
        source = extractor_source("Minimal", ["Minimal.result"], ["Minimal"])
        self.assertIn("ci.type.getUsedConstants", source)
        self.assertIn("ci.value? (allowOpaque := true)", source)
        self.assertIn("structuralDependencies ci", source)
        self.assertIn("collectAxioms n", source)
        self.assertNotIn("__LEAN_EXPOSITION_", source)

    def test_missing_executable_is_unavailable(self):
        with tempfile.TemporaryDirectory() as tmp:
            receipt = verify_comparator(tmp, "config.json", command=[str(Path(tmp) / "missing")])
        self.assertEqual(receipt["status"], "unavailable")
        self.assertIsNone(receipt["returncode"])

    @patch("lean_exposition.verification._execute")
    def test_rejected_comparator_stays_rejected(self, run):
        run.return_value = subprocess.CompletedProcess([], 1, "", "Illegal axiom: sorryAx")
        receipt = verify_comparator(".", "config.json")
        self.assertEqual(receipt["status"], "failed")
        self.assertEqual(receipt["returncode"], 1)
        self.assertFalse(receipt["sandbox_disabled_explicitly"])
        self.assertEqual(run.call_args.args[0], ["lake", "comparator", "--config", "config.json"])

    @patch("lean_exposition.verification._execute")
    def test_unstartable_comparator_is_not_rejection(self, run):
        run.return_value = subprocess.CompletedProcess([], 2, "", "bubblewrap missing")
        receipt = verify_comparator(".", "config.json")
        self.assertEqual(receipt["status"], "unavailable")

    @patch("lean_exposition.verification._execute")
    def test_export_output_cannot_replace_missing_report(self, run):
        run.return_value = subprocess.CompletedProcess([], 0, "some other output\n", "")
        with self.assertRaises(VerificationError) as raised:
            extract_dependencies(".", "Minimal", ["Minimal.result"])
        self.assertEqual(raised.exception.receipt["returncode"], 0)
        self.assertEqual(raised.exception.receipt["status"], "failed")
        self.assertEqual(raised.exception.receipt["failure_reason"], "invalid_extraction_report")

    @patch("lean_exposition.verification._execute")
    def test_report_retains_explicit_boundary(self, run):
        report = {"schema_version": 1, "module": "Minimal", "scope_complete": False,
                  "roots": ["Minimal.result"], "module_prefixes": ["Minimal"],
                  "declarations": [{"name": "Minimal.result"}],
                  "unexpanded_declarations": ["Minimal.swap"]}
        run.return_value = subprocess.CompletedProcess(
            [], 0, "LEAN_EXPOSITION_JSON:" + json.dumps(report) + "\n", "")
        result = extract_dependencies(".", "Minimal", ["Minimal.result"])
        self.assertFalse(result["scope_complete"])
        self.assertEqual(result["receipt"]["evidence_kind"], "elaboration_process")
        self.assertNotIn("kernel_checked", result)

    @patch("lean_exposition.verification._execute")
    def test_different_returned_roots_are_rejected(self, run):
        report = {"schema_version": 1, "module": "Minimal", "scope_complete": True,
                  "roots": ["Minimal.swap"], "module_prefixes": ["Minimal"],
                  "declarations": [{"name": "Minimal.swap"}]}
        run.return_value = subprocess.CompletedProcess(
            [], 0, "LEAN_EXPOSITION_JSON:" + json.dumps(report) + "\n", "")
        with self.assertRaisesRegex(VerificationError, "roots or module prefixes"):
            extract_dependencies(".", "Minimal", ["Minimal.result"])

    @patch("lean_exposition.verification._execute")
    def test_complete_report_cannot_omit_root(self, run):
        report = {"schema_version": 1, "module": "Minimal", "scope_complete": True,
                  "roots": ["Minimal.result"], "module_prefixes": ["Minimal"],
                  "declarations": [], "unexpanded_declarations": []}
        run.return_value = subprocess.CompletedProcess(
            [], 0, "LEAN_EXPOSITION_JSON:" + json.dumps(report) + "\n", "")
        with self.assertRaisesRegex(VerificationError, "omits a requested root"):
            extract_dependencies(".", "Minimal", ["Minimal.result"])

    @patch("lean_exposition.verification._execute")
    def test_complete_report_cannot_have_unexpanded_declarations(self, run):
        report = {"schema_version": 1, "module": "Minimal", "scope_complete": True,
                  "roots": ["Minimal.result"], "module_prefixes": ["Minimal"],
                  "declarations": [{"name": "Minimal.result"}],
                  "unexpanded_declarations": ["Minimal.swap"]}
        run.return_value = subprocess.CompletedProcess(
            [], 0, "LEAN_EXPOSITION_JSON:" + json.dumps(report) + "\n", "")
        with self.assertRaisesRegex(VerificationError, "claims complete scope"):
            extract_dependencies(".", "Minimal", ["Minimal.result"])

    @patch("lean_exposition.verification._execute")
    def test_custom_legacy_exit_two_stays_failed(self, run):
        run.return_value = subprocess.CompletedProcess([], 2, "", "legacy error")
        receipt = verify_comparator(".", "config.json", command=["comparator"])
        self.assertEqual(receipt["status"], "failed")

    @patch("lean_exposition.verification._execute")
    def test_timeout_preserves_partial_output(self, run):
        run.side_effect = subprocess.TimeoutExpired("lake", 1, output=b"partial", stderr=b"waiting")
        receipt = check_build(".", "Minimal", timeout=1)
        self.assertEqual(receipt["status"], "timed_out")
        self.assertEqual(receipt["stdout"], "partial")

    def test_real_timed_out_process_is_collected(self):
        with tempfile.TemporaryDirectory() as tmp:
            receipt = check_build(
                tmp, "Minimal", timeout=0.2,
                lake_command=[sys.executable, "-c",
                              "import time; print('started', flush=True); time.sleep(30)"],
            )
        self.assertEqual(receipt["status"], "timed_out")
        self.assertIn("started", receipt["stdout"])

    @patch("lean_exposition.verification._execute")
    def test_changed_source_invalidates_passing_process(self, run):
        with tempfile.TemporaryDirectory() as tmp:
            source = Path(tmp) / "Minimal.lean"
            source.write_text("theorem result : True := True.intro\n")
            def mutate(*args):
                source.write_text("theorem result : False := sorry\n")
                return subprocess.CompletedProcess([], 0, "Build completed", "")
            run.side_effect = mutate
            receipt = check_build(tmp, "Minimal")
        self.assertEqual(receipt["status"], "failed")
        self.assertTrue(receipt["source_changed"])
        self.assertEqual(receipt["changed_paths"], ["Minimal.lean"])
        self.assertEqual(receipt["module"], "Minimal")


if __name__ == "__main__":
    unittest.main()
