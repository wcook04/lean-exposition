"""Process-receipt checks using controlled Python processes, never Lean."""
from __future__ import annotations

import contextlib
import copy
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

from lean_exposition.cli import main
from lean_exposition.verification import (
    VerificationError, check_build, extract_dependencies, verify_comparator,
)
from test_verification import extraction_report_fixture


class VerificationReceiptConsistencyTests(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory(prefix="verification-receipt-")
        self.addCleanup(directory.cleanup)
        self.project = Path(directory.name)
        (self.project / "Main.lean").write_text("theorem result : True := True.intro\n")
        (self.project / "lean-toolchain").write_text("leanprover/lean4:v4.35.0\n")
        (self.project / "config.json").write_text(json.dumps({
            "challenge_module": "Challenge", "solution_module": "Main",
            "theorem_names": ["Main.result"], "permitted_axioms": [],
        }))

    def run_python(self, program):
        return verify_comparator(
            self.project, "config.json", command=[sys.executable, "-c", program],
        )

    def test_configuration_drift_does_not_invent_source_drift(self):
        original_source = (self.project / "Main.lean").read_bytes()
        receipt = self.run_python("from pathlib import Path; Path('config.json').write_text('{}')")
        self.assertEqual((self.project / "Main.lean").read_bytes(), original_source)
        self.assertEqual(receipt["status"], "failed")
        self.assertEqual(receipt["process_status"], "passed")
        self.assertEqual(receipt["failure_reason"], "config_changed_during_run")
        self.assertTrue(receipt["config_changed"])
        self.assertIs(receipt["source_changed"], False)

    def test_configuration_and_source_drift_remain_distinct(self):
        receipt = self.run_python(
            "from pathlib import Path; "
            "Path('Main.lean').write_text('changed'); "
            "Path('config.json').write_text('{}')"
        )
        self.assertTrue(receipt["config_changed"])
        self.assertIs(receipt["source_changed"], True)
        self.assertEqual(receipt["changed_paths"], ["Main.lean"])
        self.assertNotEqual(receipt["source_hashes"]["Main.lean"],
                            receipt["source_hashes_after"]["Main.lean"])

    def test_configuration_drift_preserves_failure_or_timeout_process_outcome(self):
        config = self.project / "config.json"
        original = config.read_bytes()
        for process_status in ("failed", "timed_out"):
            with self.subTest(process_status=process_status):
                config.write_bytes(original)

                def finish(*args):
                    config.write_text("{}")
                    if process_status == "timed_out":
                        raise subprocess.TimeoutExpired(args[0], 0.1, output=b"partial", stderr=b"waiting")
                    return subprocess.CompletedProcess(args[0], 3, b"partial", b"failure")

                with patch("lean_exposition.verification._execute", side_effect=finish):
                    receipt = verify_comparator(self.project, "config.json", command=[sys.executable])
                self.assertEqual(receipt["status"], "failed")
                self.assertEqual(receipt["process_status"], process_status)
                self.assertEqual(receipt["stdout"], "partial")
                self.assertIs(receipt["source_changed"], False)
                self.assertTrue(receipt["config_changed"])

    @unittest.skipUnless(os.name == "posix", "uses a broken source symlink")
    def test_configuration_drift_does_not_hide_unknown_source_snapshot(self):
        receipt = self.run_python(
            "from pathlib import Path; p=Path('Main.lean'); "
            "p.unlink(); p.symlink_to('missing.lean'); "
            "Path('config.json').write_text('{}')"
        )
        self.assertEqual(receipt["status"], "failed")
        self.assertTrue(receipt["config_changed"])
        self.assertIsNone(receipt["source_changed"])
        self.assertEqual(receipt["source_snapshot_error"]["error_type"], "FileNotFoundError")

    def test_nonfinite_timeout_prevents_each_process_launch(self):
        for timeout in (float("nan"), float("inf"), float("-inf")):
            for operation in ("build", "extract", "comparator"):
                with self.subTest(timeout=timeout, operation=operation), patch(
                    "lean_exposition.verification._execute"
                ) as execute:
                    if operation == "build":
                        receipt = check_build(self.project, "Main", timeout=timeout)
                    elif operation == "extract":
                        with self.assertRaises(VerificationError) as raised:
                            extract_dependencies(self.project, "Main", ["Main.result"], timeout=timeout)
                        receipt = raised.exception.receipt
                    else:
                        receipt = verify_comparator(
                            self.project, "config.json", command=[sys.executable], timeout=timeout,
                        )
                    execute.assert_not_called()
                    self.assertEqual(receipt["status"], "failed")
                    self.assertEqual(receipt["process_status"], "not_run")
                    self.assertIsNone(receipt["returncode"])
                    self.assertEqual(receipt["failure_stage"], "input_validation")
                    self.assertEqual(receipt["failure_reason"], "invalid_timeout")
                    self.assertNotIn("stdout_bytes_sha256", receipt)
                    self.assertNotIn("stderr_bytes_sha256", receipt)

    def test_cli_nonfinite_timeout_saves_structured_failure(self):
        out = self.project / "receipt.json"
        with patch("lean_exposition.verification._execute") as execute, contextlib.redirect_stderr(io.StringIO()):
            result = main(["comparator", str(self.project), "--config", "config.json",
                           "--timeout", "nan", "--out", str(out)])
        execute.assert_not_called()
        self.assertEqual(result, 2)
        receipt = json.loads(out.read_bytes())
        self.assertEqual(receipt["status"], "failed")
        self.assertEqual(receipt["process_status"], "not_run")
        self.assertEqual(receipt["failure_reason"], "invalid_timeout")

    def test_producer_enforces_declaration_limit_without_discarding_output(self):
        report = extraction_report_fixture()
        other = copy.deepcopy(report["declarations"][0])
        other["name"] = "Minimal.second"
        report["declarations"].append(other)
        output = "before\nLEAN_EXPOSITION_JSON:" + json.dumps(report) + "\nafter\n"
        completed = subprocess.CompletedProcess([], 0, output, "")
        with patch("lean_exposition.verification._execute", return_value=completed):
            with self.assertRaisesRegex(VerificationError, "declaration limit") as raised:
                extract_dependencies(self.project, "Minimal", ["Minimal.result"], max_declarations=1)
            self.assertEqual(raised.exception.receipt["process_status"], "passed")
            self.assertEqual(raised.exception.receipt["status"], "failed")
            self.assertEqual(raised.exception.receipt["stdout"], output)
            at_limit = extract_dependencies(self.project, "Minimal", ["Minimal.result"], max_declarations=2)
        self.assertEqual(len(at_limit["declarations"]), 2)
        self.assertEqual(at_limit["receipt"]["status"], "passed")

    def test_non_object_wire_report_keeps_failed_receipt(self):
        output = "before\nLEAN_EXPOSITION_JSON:[]\nafter\n"
        with patch("lean_exposition.verification._execute", return_value=subprocess.CompletedProcess(
            [], 0, output, ""
        )):
            with self.assertRaisesRegex(VerificationError, "must be an object") as raised:
                extract_dependencies(self.project, "Minimal", ["Minimal.result"])
        self.assertEqual(raised.exception.receipt["status"], "failed")
        self.assertEqual(raised.exception.receipt["process_status"], "passed")
        self.assertEqual(raised.exception.receipt["stdout"], output)

    def test_reserved_wire_receipt_field_preserves_real_process_output(self):
        report = extraction_report_fixture()
        report["receipt"] = {"status": "passed"}
        output = "LEAN_EXPOSITION_JSON:" + json.dumps(report) + "\n"
        program = ("import sys; sys.stdout.write(" + repr(output) + "); "
                   "sys.stderr.write('controlled diagnostic')")
        with self.assertRaisesRegex(VerificationError, "reserved receipt field") as raised:
            extract_dependencies(
                self.project, "Minimal", ["Minimal.result"],
                lean_command=[sys.executable, "-c", program],
            )
        receipt = raised.exception.receipt
        self.assertEqual(receipt["status"], "failed")
        self.assertEqual(receipt["process_status"], "passed")
        self.assertEqual(receipt["returncode"], 0)
        self.assertEqual(receipt["failure_reason"], "invalid_extraction_report")
        self.assertEqual(receipt["stdout"], output)
        self.assertEqual(receipt["stderr"], "controlled diagnostic")
        self.assertNotIn("report_sha256", receipt)

    def test_wire_json_accepts_unicode_separators_and_crlf_diagnostics(self):
        for separator in ("\u2028", "\u2029"):
            with self.subTest(separator=repr(separator)):
                report = extraction_report_fixture()
                statement = "before" + separator + "LEAN_EXPOSITION_JSON:not another report"
                report["declarations"][0]["type"] = statement
                output = ("before\r\nLEAN_EXPOSITION_JSON:"
                          + json.dumps(report, ensure_ascii=False) + "\r\nafter\r\n")
                with patch("lean_exposition.verification._execute", return_value=subprocess.CompletedProcess(
                    [], 0, output, ""
                )):
                    observed = extract_dependencies(self.project, "Minimal", ["Minimal.result"])
                self.assertEqual(observed["declarations"][0]["type"], statement)
                self.assertEqual(observed["receipt"]["stdout"], output)

    def assert_unhandleable_wire_report_retains_process(self, body):
        output = "LEAN_EXPOSITION_JSON:" + body + "\n"
        with patch("lean_exposition.verification._execute", return_value=subprocess.CompletedProcess(
            [], 0, output, "original diagnostic"
        )):
            with self.assertRaises(VerificationError) as raised:
                extract_dependencies(self.project, "Minimal", ["Minimal.result"])
        receipt = raised.exception.receipt
        self.assertEqual(receipt["status"], "failed")
        self.assertEqual(receipt["process_status"], "passed")
        self.assertEqual(receipt["returncode"], 0)
        self.assertEqual(receipt["failure_reason"], "invalid_extraction_report")
        self.assertEqual(receipt["stdout"], output)
        self.assertEqual(receipt["stderr"], "original diagnostic")

    def test_json_nesting_limit_keeps_process_receipt(self):
        report = json.dumps(extraction_report_fixture())
        self.assert_unhandleable_wire_report_retains_process(
            report[:-1] + ',"metadata":' + '[' * 1100 + '0' + ']' * 1100 + '}'
        )

    @unittest.skipUnless(hasattr(sys, "set_int_max_str_digits"), "integer conversion limit unavailable")
    def test_json_integer_conversion_limit_keeps_process_receipt(self):
        original_limit = sys.get_int_max_str_digits()
        try:
            sys.set_int_max_str_digits(sys.int_info.str_digits_check_threshold)
            digits = "1" * (sys.int_info.str_digits_check_threshold + 1)
            self.assert_unhandleable_wire_report_retains_process('{"number":' + digits + '}')
        finally:
            sys.set_int_max_str_digits(original_limit)


if __name__ == "__main__":
    unittest.main()
