"""Controlled wrapper probes, not Lean or Comparator acceptance fixtures.

The subprocesses are tiny, reviewable Python programs created by these tests.
They never execute the pinned third-party attack fixtures without a sandbox.
"""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

from lean_exposition.verification import (
    VerificationError, check_build, extract_dependencies, verify_comparator,
)


def config_bytes(**changes):
    config = {"challenge_module": "Challenge", "solution_module": "Main",
              "theorem_names": ["Main.result"], "permitted_axioms": []}
    config.update(changes)
    return json.dumps(config).encode("utf-8")


class ComparatorAssuranceTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory(prefix="comparator-assurance-")
        self.addCleanup(self.directory.cleanup)
        self.project = Path(self.directory.name)
        (self.project / "Main.lean").write_text("theorem result : True := True.intro\n")
        (self.project / "lean-toolchain").write_text("leanprover/lean4:v4.35.0-rc2\n")
        (self.project / "config.json").write_bytes(config_bytes())

    def run_python(self, code="pass", **options):
        return verify_comparator(self.project, "config.json",
                                 command=[sys.executable, "-c", code], **options)

    def test_zero_exit_has_bounded_input_and_process_observations(self):
        receipt = self.run_python("print('controlled process')")
        self.assertEqual(receipt["status"], "passed")
        self.assertEqual(receipt["process_status"], "passed")
        self.assertEqual(receipt["receipt_profile"], "comparator-process-v2")
        self.assertEqual(receipt["config_sha256"], hashlib.sha256(config_bytes()).hexdigest())
        self.assertEqual(receipt["config_sha256_after"], receipt["config_sha256"])
        self.assertEqual(receipt["config_observation"]["scope"]["theorem_names"], ["Main.result"])
        self.assertEqual(receipt["config_observation"]["claim_association"], "not_checked")
        self.assertEqual(receipt["launch_executable_before"]["sha256"],
                         hashlib.sha256(Path(sys.executable).read_bytes()).hexdigest())
        self.assertFalse(receipt["launch_executable_changed"])
        self.assertEqual(receipt["assurance"]["inner_stage_outcome"], "not_established")
        self.assertEqual(receipt["assurance"]["effective_checker_identity"], "not_established")
        self.assertEqual(receipt["assurance"]["sandbox_controls"], "not_established")

    def test_missing_config_cannot_support_zero_exit(self):
        (self.project / "config.json").unlink()
        receipt = self.run_python()
        self.assertEqual(receipt["status"], "failed")
        self.assertEqual(receipt["process_status"], "passed")
        self.assertEqual(receipt["failure_stage"], "receipt_binding")
        self.assertIsNone(receipt["config_sha256"])

    def test_ambiguous_or_targetless_configs_cannot_support_zero_exit(self):
        duplicate = config_bytes()[:-1] + b', "theorem_names": ["Other.result"]}'
        non_utf8 = b'\xff'
        unencodable_name = config_bytes().replace(b'Main.result', b'\\ud800')
        for label, data in [
            ("no targets", config_bytes(theorem_names=[])),
            ("duplicate key", duplicate),
            ("not an object", b'[]'),
            ("missing fields", b'{}'),
            ("invalid UTF8", non_utf8),
            ("escaped surrogate", unencodable_name),
            ("numeric axiom", config_bytes(permitted_axioms=[1])),
            ("bad external command", config_bytes(external_kernels={"k": []})),
            ("conflicting external commands", config_bytes(enable_nanoda=True, external_kernels={"k":["k"]})),
        ]:
            with self.subTest(label=label):
                (self.project / "config.json").write_bytes(data)
                receipt = self.run_python("print('Your solution is okay!')")
                self.assertEqual(receipt["status"], "failed")
                self.assertEqual(receipt["process_status"], "passed")
                self.assertEqual(receipt["config_observation"]["status"], "invalid")
                self.assertEqual(receipt["failure_reason"], "configuration_scope_unavailable")

    def test_definition_only_config_is_observed_without_inventing_theorems(self):
        (self.project / "config.json").write_bytes(config_bytes(theorem_names=[], definition_names=["candidate"]))
        receipt = self.run_python()
        self.assertEqual(receipt["status"], "passed")
        self.assertEqual(receipt["config_observation"]["scope"]["theorem_names"], [])
        self.assertEqual(receipt["config_observation"]["scope"]["definition_names"], ["candidate"])

    def test_legacy_optional_null_fields_keep_their_default_meaning(self):
        (self.project / "config.json").write_bytes(config_bytes(
            definition_names=None, external_kernels=None, enable_nanoda=None))
        receipt = self.run_python()
        self.assertEqual(receipt["status"], "passed")
        self.assertEqual(receipt["config_observation"]["scope"]["definition_names"], [])
        self.assertEqual(receipt["config_observation"]["scope"]["external_kernels"], {})
        self.assertFalse(receipt["config_observation"]["scope"]["enable_nanoda"])

    def test_unknown_config_fields_are_visible_not_silently_interpreted(self):
        (self.project / "config.json").write_bytes(config_bytes(future_option=True))
        receipt = self.run_python()
        self.assertEqual(receipt["config_observation"]["unknown_fields"], ["future_option"])
        self.assertEqual(receipt["assurance"]["paper_claim_correspondence"], "not_checked")

    def test_spoofed_success_diagnostic_does_not_override_failed_exit(self):
        receipt = self.run_python("print('Your solution is okay!'); raise SystemExit(1)")
        self.assertEqual(receipt["status"], "failed")
        self.assertEqual(receipt["failure_stage"], "unknown")
        self.assertEqual(receipt["assurance"]["inner_stage_outcome"], "not_established")

    def test_config_drift_keeps_before_and_after_hashes_and_process_exit(self):
        receipt = self.run_python("from pathlib import Path; Path('config.json').write_text('{}')")
        self.assertEqual(receipt["status"], "failed")
        self.assertEqual(receipt["process_status"], "passed")
        self.assertEqual(receipt["failure_reason"], "config_changed_during_run")
        self.assertNotEqual(receipt["config_sha256"], receipt["config_sha256_after"])
        self.assertTrue(receipt["config_changed"])

    def test_invalid_utf8_diagnostic_retains_raw_digest_and_failure(self):
        receipt = self.run_python("import os; os.write(2, b'\\xff'); raise SystemExit(1)")
        self.assertEqual(receipt["status"], "failed")
        self.assertFalse(receipt["stderr_utf8_valid"])
        self.assertEqual(receipt["stderr"], "\ufffd")
        self.assertEqual(receipt["stderr_bytes_sha256"], hashlib.sha256(b'\xff').hexdigest())

    def test_newlines_have_exact_raw_stream_identity(self):
        receipt = self.run_python("import os; os.write(1, b'line\\r\\n')")
        self.assertEqual(receipt["stdout"], "line\r\n")
        self.assertEqual(receipt["stdout_bytes_sha256"], hashlib.sha256(b'line\r\n').hexdigest())

    @unittest.skipUnless(os.name == "posix", "uses POSIX symlinks")
    def test_unreadable_source_after_run_retains_failed_receipt(self):
        receipt = self.run_python("from pathlib import Path; p=Path('Main.lean'); p.unlink(); p.symlink_to('missing.lean')")
        self.assertEqual(receipt["status"], "failed")
        self.assertEqual(receipt["process_status"], "passed")
        self.assertEqual(receipt["failure_reason"], "source_snapshot_unavailable")
        self.assertIsNone(receipt["source_changed"])
        self.assertIn("Main.lean", receipt["source_hashes"])

    @unittest.skipUnless(os.name == "posix", "uses POSIX symlinks")
    def test_unreadable_initial_snapshot_retains_no_run_receipt(self):
        (self.project / "broken.lean").symlink_to("missing.lean")
        receipt = self.run_python("from pathlib import Path; Path('must-not-run').touch()")
        self.assertEqual(receipt["status"], "failed")
        self.assertEqual(receipt["process_status"], "not_run")
        self.assertEqual(receipt["failure_stage"], "input_snapshot")
        self.assertFalse((self.project / "must-not-run").exists())

    @unittest.skipUnless(os.name == "posix", "uses executable scripts")
    def test_launch_script_mutation_is_not_a_stable_tool_observation(self):
        tool = self.project / "launcher"
        tool.write_text(f'#!{sys.executable}\nfrom pathlib import Path\nPath(__file__).write_text("# changed\\n")\n')
        tool.chmod(0o700)
        receipt = verify_comparator(self.project, "config.json", command=["./launcher"])
        self.assertEqual(receipt["process_status"], "passed")
        self.assertEqual(receipt["status"], "failed")
        self.assertTrue(receipt["launch_executable_changed"])
        self.assertEqual(receipt["failure_reason"], "launch_executable_changed_during_run")

    @unittest.skipUnless(os.name == "posix", "POSIX signal result")
    def test_signal_exit_stays_an_operational_failure(self):
        receipt = self.run_python("import os,signal; os.kill(os.getpid(), signal.SIGTERM)")
        self.assertEqual(receipt["returncode"], -signal.SIGTERM)
        self.assertEqual(receipt["status"], "failed")
        self.assertEqual(receipt["failure_stage"], "unknown")

    def test_invalid_utf8_stdout_is_not_repaired_into_extraction_evidence(self):
        with self.assertRaises(VerificationError) as raised:
            extract_dependencies(self.project, "Main", ["Main.result"],
                                 lean_command=[sys.executable, "-c", "import os; os.write(1, b'\\xff')"])
        receipt = raised.exception.receipt
        self.assertEqual(receipt["failure_reason"], "invalid_extraction_report")
        self.assertEqual(receipt["process_status"], "passed")
        self.assertFalse(receipt["stdout_utf8_valid"])

    def test_timeout_retains_observation_and_does_not_claim_rejection(self):
        receipt = self.run_python("import time; print('started',flush=True); time.sleep(30)", timeout=0.2)
        self.assertEqual(receipt["status"], "timed_out")
        self.assertEqual(receipt["process_status"], "timed_out")
        self.assertEqual(receipt["failure_stage"], "process_timeout")
        self.assertTrue(receipt["cleanup"]["parent_reaped"])
        self.assertEqual(receipt["assurance"]["inner_stage_outcome"], "not_established")

    @unittest.skipUnless(os.name == "posix", "POSIX signal permission")
    def test_denied_cleanup_signal_retains_timeout_and_reports_cleanup_limit(self):
        with patch("lean_exposition.verification.os.killpg", side_effect=PermissionError(1, "denied")):
            receipt = self.run_python("import time; time.sleep(0.2)", timeout=0.02)
        self.assertEqual(receipt["status"], "timed_out")
        self.assertTrue(receipt["cleanup"]["parent_reaped"])
        self.assertEqual(receipt["cleanup"]["signal_errors"][0]["error_type"], "PermissionError")
        self.assertEqual(receipt["assurance"]["inner_stage_outcome"], "not_established")

    @unittest.skipUnless(os.name == "posix", "POSIX process-group race")
    def test_exited_launcher_with_detached_pipe_does_not_lose_timeout_receipt(self):
        code = ("import subprocess,sys; "
                "subprocess.Popen([sys.executable,'-c','import time; time.sleep(0.5)'], start_new_session=True)")
        receipt = self.run_python(code, timeout=0.15)
        self.assertEqual(receipt["status"], "timed_out")
        self.assertEqual(receipt["cleanup"]["scope"], "invocation_process_group")
        self.assertTrue(receipt["cleanup"]["parent_reaped"])


if __name__ == "__main__":
    unittest.main()
