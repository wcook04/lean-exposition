"""Regression checks for failed process launch; no Lean tools are invoked."""
from __future__ import annotations

import contextlib
import io
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from lean_exposition.cli import main
from lean_exposition.verification import verify_comparator


@unittest.skipUnless(os.name == "posix", "POSIX executable permission and format checks")
class ProcessLaunchReceiptTests(unittest.TestCase):
    def test_non_executable_tool_returns_unavailable_receipt(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            tool = root / "not-executable"
            tool.write_text("#!/bin/sh\nexit 0\n")
            tool.chmod(0o644)
            (root / "config.json").write_text("{}\n")
            receipt = verify_comparator(root, "config.json", command=[str(tool)])
        self.assertEqual(receipt["status"], "unavailable")
        self.assertIsNone(receipt["returncode"])
        self.assertEqual(receipt["failure_stage"], "process_launch")
        self.assertEqual(receipt["error_type"], "PermissionError")
        self.assertFalse(receipt["source_changed"])
        self.assertIsNotNone(receipt["config_sha256"])

    def test_invalid_executable_format_returns_unavailable_receipt(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            tool = root / "bad-format"
            tool.write_text("not an executable image\n")
            tool.chmod(0o755)
            (root / "config.json").write_text("{}\n")
            receipt = verify_comparator(root, "config.json", command=[str(tool)])
        self.assertEqual(receipt["status"], "unavailable")
        self.assertIsNone(receipt["returncode"])
        self.assertEqual(receipt["failure_stage"], "process_launch")
        self.assertEqual(receipt["error_type"], "OSError")

    def test_cli_persists_launch_failure_receipt(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            tool = root / "lake"
            tool.write_text("#!/bin/sh\nexit 0\n")
            tool.chmod(0o644)
            (root / "config.json").write_text("{}\n")
            output = root / "receipt.json"
            with patch.dict(os.environ, {"PATH": str(root)}):
                with contextlib.redirect_stderr(io.StringIO()):
                    result = main(["comparator", str(root), "--config", "config.json", "--out", str(output)])
            self.assertEqual(result, 2)
            self.assertTrue(output.is_file())
            receipt = json.loads(output.read_text())
        self.assertEqual(receipt["status"], "unavailable")
        self.assertEqual(receipt["failure_stage"], "process_launch")
        self.assertEqual(receipt["error_type"], "PermissionError")


if __name__ == "__main__":
    unittest.main()
