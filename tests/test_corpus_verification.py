"""Input/prerequisite regressions, never a substitute for Lean replay."""
from __future__ import annotations

import importlib.util
import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest
from unittest.mock import patch


ROOT = Path(__file__).resolve().parents[1]
EXAMPLE = ROOT / "examples/qaoa-sk"
SPEC = importlib.util.spec_from_file_location(
    "corpus_preflight", EXAMPLE / "verification/preflight.py"
)
preflight = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(preflight)


class CorpusVerificationTests(unittest.TestCase):
    def test_consumed_inputs_cannot_be_omitted_from_lock(self):
        original = json.loads((EXAMPLE / "source-lock.json").read_text())
        for collection, path in (
            ("files", "upstream/lean/lean-toolchain"),
            ("files", "upstream/provenance/mathlib-lake-manifest.json"),
            ("files", "upstream/lean/ComparatorChallenges/SKFullSupport.json"),
            ("derived_files", "upstream/lean/lakefile.lean"),
            ("derived_files", "upstream/lean/lake-manifest.json"),
        ):
            with self.subTest(path=path):
                lock = dict(original)
                lock[collection] = [row for row in original[collection] if row["path"] != path]
                with self.assertRaisesRegex(ValueError, "absent from the source lock"):
                    preflight.require_locked_inputs(lock)

    def test_selected_comparator_policy_is_the_reviewed_policy(self):
        lock = json.loads((EXAMPLE / "source-lock.json").read_text())
        expected = {
            "OAI.ZeroTemperatureSK.full_support": ("SKFullSupport", "SKSupport"),
            "OAI.SKValue.value_consequences": ("SKValue", "SKValue"),
        }
        self.assertEqual({target["declaration"] for target in lock["targets"]}, set(expected))
        for target in lock["targets"]:
            challenge, solution = expected[target["declaration"]]
            config = json.loads((EXAMPLE / target["comparator_config"]).read_text())
            self.assertEqual(config["challenge_module"], f"ComparatorChallenges.{challenge}")
            self.assertEqual(config["solution_module"], f"OAI.Probability.{solution}.Main")
            self.assertEqual(config["solution_module"], target["module"])
            self.assertEqual(config["theorem_names"], [target["declaration"]])
            self.assertEqual(config["definition_names"], [])
            self.assertEqual(set(config["permitted_axioms"]), {"propext", "Quot.sound", "Classical.choice"})
            self.assertIs(config["enable_nanoda"], False)

    @patch.object(preflight.subprocess, "run")
    def test_invalid_lock_is_a_failed_receipt(self, run):
        for payload in (None, "{", "[]", "{}", '{"schema_version":"1.0","files":[null]}'):
            with self.subTest(payload=payload), tempfile.TemporaryDirectory() as temporary:
                root = Path(temporary)
                if payload is not None:
                    (root / "source-lock.json").write_text(payload)
                result = preflight.preflight(root)
                self.assertEqual(result["status"], "failed")
                self.assertEqual(result["reason"], "locked_input_check_failed")
                self.assertNotIn(temporary, json.dumps(result))
                self.assertEqual(result["lean_build"], "not_run")
        run.assert_not_called()

    def test_selected_pins_match_both_upstream_locks(self):
        result = preflight.dependency_pins(EXAMPLE)
        self.assertEqual(result["status"], "passed")
        self.assertEqual(len(result["packages"]), 9)
        self.assertFalse(result["checkout_bytes_checked"])

    def test_dependency_drift_is_rejected(self):
        mutations = {
            "revision": lambda rows: rows[0].update(rev="0" * 40),
            "repository": lambda rows: rows[0].update(url="https://example.org/other"),
            "configuration": lambda rows: rows[0].update(configFile="different.lean"),
            "unpinned": lambda rows: rows[0].update(rev="main"),
            "missing": lambda rows: rows.pop(),
            "duplicate": lambda rows: rows.append(rows[0].copy()),
        }
        for name, mutate in mutations.items():
            with self.subTest(name=name), tempfile.TemporaryDirectory() as temporary:
                root = Path(temporary)
                for relative in ("upstream/lean/lake-manifest.json",
                                 "upstream/provenance/lake-manifest.json",
                                 "upstream/provenance/mathlib-lake-manifest.json"):
                    target = root / relative
                    target.parent.mkdir(parents=True, exist_ok=True)
                    shutil.copyfile(EXAMPLE / relative, target)
                active = root / "upstream/lean/lake-manifest.json"
                data = json.loads(active.read_text())
                mutate(data["packages"])
                active.write_text(json.dumps(data))
                with self.assertRaises(ValueError):
                    preflight.dependency_pins(root)

    @patch.object(preflight.shutil, "which", return_value="elan")
    @patch.object(preflight.subprocess, "run")
    def test_nearby_toolchain_does_not_satisfy_pin(self, run, which):
        run.return_value = subprocess.CompletedProcess([], 0, "leanprover/lean4:v4.35.0-rc2\n", "")
        result = preflight.toolchain_availability("leanprover/lean4:v4.34.1")
        self.assertEqual(result["status"], "unavailable")
        self.assertEqual(run.call_args.args[0], ["elan", "toolchain", "list"])

    @patch.object(preflight.shutil, "which", return_value="elan")
    @patch.object(preflight.subprocess, "run")
    def test_default_marker_does_not_hide_exact_installed_pin(self, run, which):
        run.return_value = subprocess.CompletedProcess([], 0, "leanprover/lean4:v4.34.1 (default)\n", "")
        self.assertEqual(preflight.toolchain_availability("leanprover/lean4:v4.34.1")["status"], "passed")

    @patch.object(preflight.shutil, "which", return_value=None)
    @patch.object(preflight.subprocess, "run")
    def test_missing_tools_leave_proof_checks_unrun(self, run, which):
        result = preflight.preflight(EXAMPLE)
        self.assertEqual(result["status"], "unavailable")
        self.assertEqual(result["lean_build"], "not_run")
        self.assertEqual(result["comparator"], "not_run")
        self.assertEqual(result["source_audit"]["status"], "passed")
        run.assert_not_called()

    @patch.object(preflight.shutil, "which", return_value="tool")
    @patch.object(preflight.subprocess, "run")
    @patch.object(preflight.platform, "system", return_value="Linux")
    def test_ready_prerequisites_do_not_claim_verification(self, system, run, which):
        run.return_value = subprocess.CompletedProcess([], 0, "leanprover/lean4:v4.34.1\n", "")
        result = preflight.preflight(EXAMPLE)
        self.assertEqual(result["status"], "ready")
        self.assertEqual(result["comparator"], "not_run")
        self.assertEqual(result["lean_build"], "not_run")
        for check in ("axiom_audit", "extraction", "statement_comparison"):
            self.assertEqual(result[check], "not_run")
        self.assertEqual(result["tool_compatibility"], "not_checked")
        self.assertEqual(result["dependency_checkouts"], "not_checked")
        self.assertEqual(result["sandbox"]["functional_check"], "not_run")
        self.assertEqual([call.args[0] for call in run.call_args_list], [["elan", "toolchain", "list"]])


if __name__ == "__main__":
    unittest.main()
