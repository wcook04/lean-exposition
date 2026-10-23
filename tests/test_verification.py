import json
import os
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
from lean_exposition.extraction import to_graph
from lean_exposition.contracts import encoded


def extraction_report_fixture(**updates):
    """A complete synthetic wire report; this fixture never claims a Lean run."""
    report = {
        "schema_version": 2, "module": "Minimal", "roots": ["Minimal.result"],
        "module_prefixes": ["Minimal"], "scope_complete": True,
        "declarations": [{
            "name": "Minimal.result", "kind": "theorem", "type": "True",
            "type_dependencies": [], "value_dependencies": [], "structural_dependencies": [],
            "axioms": [], "has_sorry": False, "body_available": True,
            "is_unsafe": False, "is_partial": False,
            "source": {"module": "Minimal", "line": 1},
        }],
        "external_dependencies": [], "missing_declarations": [],
        "unexpanded_declarations": [], "unavailable_bodies": [],
        "evidence_kind": "elaborated_expression_dependencies",
    }
    report.update(updates)
    return report


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
        self.assertEqual(receipt["failure_stage"], "checker_start")

    @patch("lean_exposition.verification._execute")
    def test_export_output_cannot_replace_missing_report(self, run):
        run.return_value = subprocess.CompletedProcess([], 0, "some other output\n", "")
        with self.assertRaises(VerificationError) as raised:
            extract_dependencies(".", "Minimal", ["Minimal.result"])
        self.assertEqual(raised.exception.receipt["returncode"], 0)
        self.assertEqual(raised.exception.receipt["status"], "failed")
        self.assertEqual(raised.exception.receipt["failure_reason"], "invalid_extraction_report")

    @patch("lean_exposition.verification._execute")
    def test_nonencodable_report_line_retains_failed_receipt(self, run):
        output = "LEAN_EXPOSITION_JSON:\ud800\n"
        run.return_value = subprocess.CompletedProcess([], 0, output, "original diagnostic")
        with self.assertRaisesRegex(VerificationError, "invalid extraction JSON") as raised:
            extract_dependencies(".", "Minimal", ["Minimal.result"])
        receipt = raised.exception.receipt
        self.assertEqual(receipt["status"], "failed")
        self.assertEqual(receipt["failure_reason"], "invalid_extraction_report")
        self.assertEqual(receipt["stdout"], output)
        self.assertEqual(receipt["stderr"], "original diagnostic")

    @patch("lean_exposition.verification._execute")
    def test_report_retains_explicit_boundary(self, run):
        report = extraction_report_fixture(scope_complete=False,
                                           unexpanded_declarations=["Minimal.swap"])
        run.return_value = subprocess.CompletedProcess(
            [], 0, "LEAN_EXPOSITION_JSON:" + json.dumps(report) + "\n", "")
        result = extract_dependencies(".", "Minimal", ["Minimal.result"])
        self.assertFalse(result["scope_complete"])
        self.assertEqual(result["receipt"]["evidence_kind"], "elaboration_process")
        self.assertNotIn("kernel_checked", result)

    @patch("lean_exposition.verification._execute")
    def test_different_returned_roots_are_rejected(self, run):
        report = extraction_report_fixture(roots=["Minimal.swap"])
        report["declarations"][0]["name"] = "Minimal.swap"
        run.return_value = subprocess.CompletedProcess(
            [], 0, "LEAN_EXPOSITION_JSON:" + json.dumps(report) + "\n", "")
        with self.assertRaisesRegex(VerificationError, "roots or module prefixes"):
            extract_dependencies(".", "Minimal", ["Minimal.result"])

    @patch("lean_exposition.verification._execute")
    def test_complete_report_cannot_omit_root(self, run):
        report = extraction_report_fixture(declarations=[])
        run.return_value = subprocess.CompletedProcess(
            [], 0, "LEAN_EXPOSITION_JSON:" + json.dumps(report) + "\n", "")
        with self.assertRaisesRegex(VerificationError, "omits a requested root"):
            extract_dependencies(".", "Minimal", ["Minimal.result"])

    @patch("lean_exposition.verification._execute")
    def test_complete_report_cannot_have_unexpanded_declarations(self, run):
        report = extraction_report_fixture(unexpanded_declarations=["Minimal.swap"])
        run.return_value = subprocess.CompletedProcess(
            [], 0, "LEAN_EXPOSITION_JSON:" + json.dumps(report) + "\n", "")
        with self.assertRaisesRegex(VerificationError, "claims complete scope"):
            extract_dependencies(".", "Minimal", ["Minimal.result"])

    @patch("lean_exposition.verification._execute")
    def test_malformed_wire_reports_retain_failed_receipts(self, run):
        changes = {
            "string scope flag": lambda r: r.update(scope_complete="false"),
            "boolean schema version": lambda r: r.update(schema_version=True),
            "wrong evidence kind": lambda r: r.update(evidence_kind="lean_build"),
            "missing collection": lambda r: r.pop("missing_declarations"),
            "wrong collection type": lambda r: r.update(declarations=None),
            "missing declaration fields": lambda r: r.update(declarations=[{"name": "Minimal.result", "kind": "theorem"}]),
            "unhashable name": lambda r: r["declarations"][0].update(name=[]),
            "unknown kind": lambda r: r["declarations"][0].update(kind="future_kind"),
            "numeric body flag": lambda r: r["declarations"][0].update(body_available=0),
            "numeric sorry flag": lambda r: r["declarations"][0].update(has_sorry=0),
            "missing safety flag": lambda r: r["declarations"][0].pop("is_unsafe"),
            "numeric safety flag": lambda r: r["declarations"][0].update(is_partial=0),
            "string dependencies": lambda r: r["declarations"][0].update(value_dependencies="Minimal.support"),
            "boolean source line": lambda r: r["declarations"][0]["source"].update(line=True),
            "reversed source range": lambda r: r["declarations"][0]["source"].update(line=5, end_line=4),
            "nonfinite source line": lambda r: r["declarations"][0]["source"].update(line=float("nan")),
            "nonencodable statement": lambda r: r["declarations"][0].update(type="\ud800"),
            "nonencodable optional metadata": lambda r: r.update(note="\ud800"),
            "unknown unavailable body": lambda r: r.update(scope_complete=False, unavailable_bodies=["missing"]),
            "available body in unavailable summary": lambda r: r.update(scope_complete=False, unavailable_bodies=["Minimal.result"]),
            "complete despite body flag": lambda r: r["declarations"][0].update(body_available=False),
            "overlapping classifications": lambda r: r.update(external_dependencies=[{"name": "Minimal.result", "kind": "theorem", "module": "Init"}]),
            "unclassified complete dependency": lambda r: r["declarations"][0].update(value_dependencies=["unclassified"]),
        }
        for label, change in changes.items():
            with self.subTest(label=label):
                report = extraction_report_fixture()
                change(report)
                output = "LEAN_EXPOSITION_JSON:" + json.dumps(report) + "\n"
                run.return_value = subprocess.CompletedProcess([], 0, output, "")
                with self.assertRaises(VerificationError) as raised:
                    extract_dependencies(".", "Minimal", ["Minimal.result"])
                receipt = raised.exception.receipt
                self.assertEqual(receipt["status"], "failed")
                self.assertEqual(receipt["failure_reason"], "invalid_extraction_report")
                self.assertEqual(receipt["returncode"], 0)
                self.assertEqual(receipt["stdout"], output)

    @patch("lean_exposition.verification._execute")
    def test_duplicate_report_keys_are_rejected(self, run):
        report = json.dumps(extraction_report_fixture())[:-1] + ', "scope_complete": true}'
        run.return_value = subprocess.CompletedProcess([], 0, "LEAN_EXPOSITION_JSON:" + report + "\n", "")
        with self.assertRaises(VerificationError) as raised:
            extract_dependencies(".", "Minimal", ["Minimal.result"])
        self.assertEqual(raised.exception.receipt["failure_reason"], "invalid_extraction_report")

    @patch("lean_exposition.verification._execute")
    def test_nullable_ranges_repeated_edges_and_requests_remain_supported(self, run):
        report = extraction_report_fixture(roots=["Minimal.result", "Minimal.result"],
                                           module_prefixes=["Minimal", "Minimal"])
        report["declarations"][0]["source"].update(line=None, column=None, end_line=None)
        report["declarations"][0]["structural_dependencies"] = ["Minimal.result", "Minimal.result"]
        run.return_value = subprocess.CompletedProcess([], 0, "LEAN_EXPOSITION_JSON:" + json.dumps(report) + "\n", "")
        result = extract_dependencies(".", "Minimal", report["roots"], module_prefixes=report["module_prefixes"])
        self.assertEqual(result["receipt"]["status"], "passed")
        self.assertIsNone(result["declarations"][0]["source"]["line"])

    @patch("lean_exposition.verification._execute")
    def test_custom_legacy_exit_two_stays_failed(self, run):
        run.return_value = subprocess.CompletedProcess([], 2, "", "legacy error")
        receipt = verify_comparator(".", "config.json", command=["comparator"])
        self.assertEqual(receipt["status"], "failed")
        self.assertEqual(receipt["failure_stage"], "unknown")

    @patch("lean_exposition.verification._execute")
    def test_timeout_preserves_partial_output(self, run):
        run.side_effect = subprocess.TimeoutExpired("lake", 1, output=b"partial", stderr=b"waiting")
        receipt = check_build(".", "Minimal", timeout=1)
        self.assertEqual(receipt["status"], "timed_out")
        self.assertEqual(receipt["stdout"], "partial")

    def test_real_timed_out_process_is_collected(self):
        processes = []
        real_popen = subprocess.Popen

        def start_process(*args, **kwargs):
            process = real_popen(*args, **kwargs)
            processes.append(process)
            return process

        with tempfile.TemporaryDirectory() as tmp, patch(
            "lean_exposition.verification.subprocess.Popen", side_effect=start_process,
        ):
            receipt = check_build(
                tmp, "Minimal", timeout=0.2,
                lake_command=[sys.executable, "-c",
                              "import time; print('started', flush=True); time.sleep(30)"],
            )
        self.assertEqual(receipt["status"], "timed_out")
        # A cold interpreter may not print before the deadline. The process
        # must still be reaped; partial-output preservation is tested above.
        self.assertEqual(len(processes), 1)
        self.assertIsNotNone(processes[0].returncode)

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


@unittest.skipUnless(os.environ.get("LEAN_EXPOSITION_RUN_LEAN") == "1",
                     "set LEAN_EXPOSITION_RUN_LEAN=1 for the pinned Lean integration fixture")
class LeanSafetyIntegrationTests(unittest.TestCase):
    def test_safe_unsafe_and_partial_statuses_from_pinned_lean(self):
        with tempfile.TemporaryDirectory(prefix="lean-exposition-safety-") as tmp:
            project = Path(tmp)
            archive = os.environ.get("LEAN_EXPOSITION_VALIDATION_DIR")
            archive_path = Path(archive) if archive else None
            if archive_path:
                archive_path.mkdir(parents=True, exist_ok=True)
            def retain(name, value):
                if archive_path:
                    (archive_path / name).write_bytes(encoded(value))
            (project / "lean-toolchain").write_text("leanprover/lean4:v4.35.0-rc2\n")
            (project / "lakefile.toml").write_text(
                'name = "safety_fixture"\nversion = "0.1.0"\n'
                'defaultTargets = ["Safety"]\n\n[[lean_lib]]\nname = "Safety"\n'
            )
            (project / "lake-manifest.json").write_text(json.dumps({
                "version": "1.2.0", "packagesDir": ".lake/packages", "packages": [],
                "name": "safety_fixture", "lakeDir": ".lake", "fixedToolchain": False,
            }) + "\n")
            (project / "Safety.lean").write_text(
                "namespace Safety\n"
                "theorem safeTheorem : True := True.intro\n"
                "unsafe def unsafeProgram (n : Nat) : Nat := n + 1\n"
                "partial def partialProgram (n : Nat) : Nat :=\n"
                "  if n == 0 then 0 else partialProgram (n - 1)\n"
                "end Safety\n"
            )
            if archive_path:
                for name in ("lean-toolchain", "lakefile.toml", "lake-manifest.json", "Safety.lean"):
                    (archive_path / name).write_bytes((project / name).read_bytes())
                version = subprocess.run(["lean", "--version"], cwd=project,
                                         capture_output=True, text=True, check=False)
                retain("tool-version.json", {"returncode": version.returncode,
                                              "stdout": version.stdout, "stderr": version.stderr})
            build = check_build(project, "Safety", timeout=600)
            retain("build-receipt.json", build)
            self.assertEqual(build["status"], "passed", build)
            roots = ["Safety.safeTheorem", "Safety.unsafeProgram", "Safety.partialProgram"]
            report = extract_dependencies(project, "Safety", roots, timeout=600)
            retain("raw-report.json", report)
            if archive_path:
                (archive_path / "generated-driver.lean").write_text(
                    extractor_source("Safety", roots, ["Safety"])
                )
            by_name = {row["name"]: row for row in report["declarations"]}
            self.assertEqual((by_name[roots[0]]["is_unsafe"], by_name[roots[0]]["is_partial"]),
                             (False, False))
            self.assertTrue(by_name[roots[1]]["is_unsafe"])
            self.assertEqual(by_name[roots[2]]["kind"], "opaque")
            self.assertIsNone(by_name[roots[2]]["is_partial"])
            graph = to_graph(report, project, build)
            retain("graph.json", graph)
            statuses = {node["id"]: node["status"] for node in graph["nodes"]}
            self.assertEqual(statuses[roots[0]], "kernel_checked")
            self.assertEqual(statuses[roots[1]], "unverified")
            self.assertEqual(statuses[roots[2]], "unverified")


if __name__ == "__main__":
    unittest.main()
