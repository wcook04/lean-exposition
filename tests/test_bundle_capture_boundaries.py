"""Adversarial directory swaps must not redirect bundle reads or writes."""
from __future__ import annotations

import copy
import json
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from lean_exposition import bundle
from lean_exposition.contracts import ContractError, digest, encoded
from lean_exposition.extraction import to_graph
from test_adversarial import synthetic_artifact, synthetic_graph
from test_application_obligations import authored_mapping
from test_core_review import extraction_fixture, rebind
from test_scoped_applications import application_graph


class BundleDirectoryBoundaryTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="lean-exposition-boundary-")
        self.addCleanup(temporary.cleanup)
        self.base = Path(temporary.name)
        self.source = self.base / "source"
        bundle.scaffold(synthetic_graph(), self.source)
        self.pairs = {
            stage: (self.source / f"papers/{stage}.md", self.source / f"papers/{stage}.json")
            for stage in bundle.STAGES
        }

    @unittest.skipUnless(bundle._DIRECTORY_HANDLES, "requires no-follow directory handles")
    def test_capture_does_not_follow_a_swapped_paper_directory(self):
        original = (self.source / "papers/long.md").read_bytes()
        outside = self.base / "outside"
        outside.mkdir()
        (outside / "long.md").write_bytes(b"outside bytes must never be read\n")
        saved = self.source / "papers.saved"
        open_file = os.open
        swaps = []

        def swap_on_open(path, flags, *args, **kwargs):
            name = os.fspath(path)
            is_paper = name == "long.md" or name.endswith("/papers/long.md")
            if is_paper and not (flags & os.O_CREAT):
                (self.source / "papers").rename(saved)
                (self.source / "papers").symlink_to(outside, target_is_directory=True)
                try:
                    fd = open_file(path, flags, *args, **kwargs)
                finally:
                    (self.source / "papers").unlink()
                    saved.rename(self.source / "papers")
                swaps.append(name)
                return fd
            return open_file(path, flags, *args, **kwargs)

        with patch.object(os, "open", swap_on_open):
            capture = bundle.BundleCapture(self.source)
        self.assertEqual(len(swaps), 1)
        self.assertEqual(capture.files["papers/long.md"], original)
        self.assertTrue(bundle.check_bundle(capture)["valid"])

    @unittest.skipUnless(bundle._DIRECTORY_HANDLES, "requires no-follow directory handles")
    def test_assembly_does_not_write_through_a_swapped_paper_directory(self):
        out = self.base / "assembled"
        outside = self.base / "outside"
        outside.mkdir()
        saved = out / "papers.saved"
        open_file = os.open
        path_open = Path.open
        swaps = []

        def open_during_swap(open_fn):
            (out / "papers").rename(saved)
            (out / "papers").symlink_to(outside, target_is_directory=True)
            try:
                return open_fn()
            finally:
                (out / "papers").unlink()
                saved.rename(out / "papers")
                swaps.append(True)

        def swap_descriptor(path, flags, *args, **kwargs):
            if os.fspath(path) == "long.md" and flags & os.O_CREAT:
                return open_during_swap(lambda: open_file(path, flags, *args, **kwargs))
            return open_file(path, flags, *args, **kwargs)

        def swap_path(path, *args, **kwargs):
            if path == out / "papers/long.md" and args and args[0] == "xb":
                return open_during_swap(lambda: path_open(path, *args, **kwargs))
            return path_open(path, *args, **kwargs)

        with patch.object(os, "open", swap_descriptor), patch.object(Path, "open", swap_path):
            bundle.assemble_bundle(self.source / "graph.json", self.pairs, out)
        self.assertEqual(len(swaps), 1)
        self.assertFalse((outside / "long.md").exists())
        self.assertTrue(bundle.check_bundle(out)["valid"])
        self.assertEqual((out / "papers/long.md").read_bytes(), self.pairs["long"][0].read_bytes())

    @unittest.skipUnless(bundle._DIRECTORY_HANDLES, "requires no-follow directory handles")
    def test_assembly_reports_a_directory_left_replaced(self):
        out = self.base / "assembled"
        outside = self.base / "outside"
        outside.mkdir()
        saved = out / "papers.saved"
        open_file = os.open
        swaps = []

        def leave_swapped(path, flags, *args, **kwargs):
            if os.fspath(path) == "long.md" and flags & os.O_CREAT:
                (out / "papers").rename(saved)
                (out / "papers").symlink_to(outside, target_is_directory=True)
                swaps.append(True)
            return open_file(path, flags, *args, **kwargs)

        try:
            with patch.object(os, "open", leave_swapped):
                with self.assertRaisesRegex(ContractError, "directory changed"):
                    bundle.assemble_bundle(self.source / "graph.json", self.pairs, out)
        finally:
            if (out / "papers").is_symlink():
                (out / "papers").unlink()
                saved.rename(out / "papers")
        self.assertEqual(len(swaps), 1)
        self.assertFalse((outside / "long.md").exists())

    @unittest.skipUnless(bundle._DIRECTORY_HANDLES, "requires no-follow directory handles")
    def test_scaffold_does_not_write_through_a_swapped_paper_directory(self):
        out = self.base / "new-scaffold"
        outside = self.base / "outside"
        outside.mkdir()
        saved = out / "papers.saved"
        open_file = os.open
        write_bytes = Path.write_bytes
        swaps = []

        def during_swap(open_fn):
            (out / "papers").rename(saved)
            (out / "papers").symlink_to(outside, target_is_directory=True)
            try:
                return open_fn()
            finally:
                (out / "papers").unlink()
                saved.rename(out / "papers")
                swaps.append(True)

        def swap_descriptor(path, flags, *args, **kwargs):
            if os.fspath(path) == "long.md" and flags & os.O_CREAT:
                return during_swap(lambda: open_file(path, flags, *args, **kwargs))
            return open_file(path, flags, *args, **kwargs)

        def swap_path(path, content):
            if path == out / "papers/long.md":
                return during_swap(lambda: write_bytes(path, content))
            return write_bytes(path, content)

        with patch.object(os, "open", swap_descriptor), patch.object(Path, "write_bytes", swap_path):
            manifest = bundle.scaffold(synthetic_graph(), out)
        self.assertEqual(len(swaps), 1)
        self.assertFalse((outside / "long.md").exists())
        self.assertEqual(manifest["status"], "scaffold")
        self.assertEqual(bundle.check_bundle(out)["paper_states"], ["scaffold"] * 3)
        self.assertIn(b"EMPTY SCAFFOLD", (out / "papers/long.md").read_bytes())

    def test_scaffold_validates_generated_bytes_before_creating_output(self):
        out = self.base / "new-scaffold"
        with patch.object(bundle, "_validate_payload", side_effect=ContractError("invalid generated bytes")):
            with self.assertRaisesRegex(ContractError, "invalid generated bytes"):
                bundle.scaffold(synthetic_graph(), out)
        self.assertFalse(out.exists())

    def test_scaffold_applies_size_limits_before_creating_output(self):
        for limit in ("MAX_MEMBER_BYTES", "MAX_BUNDLE_BYTES"):
            with self.subTest(limit=limit), patch.object(bundle, limit, 1):
                out = self.base / limit
                with self.assertRaisesRegex(ContractError, "size limit"):
                    bundle.scaffold(synthetic_graph(), out)
                self.assertFalse(out.exists())

    @unittest.skipUnless(hasattr(os, "mkfifo"), "requires FIFO support")
    def test_capture_rejects_a_fifo_without_waiting_for_a_writer(self):
        fifo = self.source / "papers/long.md"
        fifo.unlink()
        os.mkfifo(fifo)
        environment = os.environ.copy()
        module_root = str(Path(bundle.__file__).resolve().parents[1])
        environment["PYTHONPATH"] = os.pathsep.join((module_root, environment.get("PYTHONPATH", "")))
        for mode in ("default", "portable_fallback", "nonblock_missing_before_import"):
            with self.subTest(mode=mode):
                before_import = "import os; os.O_NONBLOCK = 0; " if mode == "nonblock_missing_before_import" else ""
                setup = ("b._DIRECTORY_HANDLES = False; b.os.O_NOFOLLOW = 0; b.os.O_NONBLOCK = 0; "
                         if mode == "portable_fallback" else
                         "assert not b._DIRECTORY_HANDLES; " if mode == "nonblock_missing_before_import" else "")
                code = ("import sys; from pathlib import Path; " + before_import
                        + "from lean_exposition import bundle as b; " + setup + "b.BundleCapture(Path(sys.argv[1]))")
                process = subprocess.run([sys.executable, "-c", code, str(self.source)],
                                         capture_output=True, text=True, timeout=10, check=False, env=environment)
                self.assertNotEqual(process.returncode, 0)
                self.assertIn("not a regular artifact", process.stderr)

    def test_raw_descriptor_is_closed_if_fdopen_fails(self):
        opened = []
        open_file = os.open

        def track_open(path, flags, *args, **kwargs):
            fd = open_file(path, flags, *args, **kwargs)
            opened.append(fd)
            return fd

        with patch.object(os, "open", track_open), patch.object(os, "fdopen", side_effect=OSError("fdopen failed")):
            with self.assertRaisesRegex(ContractError, "cannot read artifact"):
                bundle._read_regular(self.source / "graph.json", "graph.json", bundle.MAX_MEMBER_BYTES)
        try:
            self.assertEqual(len(opened), 1)
            with self.assertRaises(OSError):
                os.fstat(opened[0])
        finally:
            for fd in opened:
                try:
                    os.close(fd)
                except OSError:
                    pass

    def test_ordinary_capture_and_assembly_still_work(self):
        capture = bundle.BundleCapture(self.source)
        out = self.base / "assembled"
        bundle.assemble_bundle(self.source / "graph.json", self.pairs, out)
        self.assertEqual(bundle.load_bundle(capture), bundle.load_bundle(out))

    def test_pathname_fallback_preserves_ordinary_capture_and_assembly(self):
        with patch.object(bundle, "_DIRECTORY_HANDLES", False), \
             patch.object(os, "O_NOFOLLOW", 0, create=True), \
             patch.object(os, "O_NONBLOCK", 0, create=True):
            scaffold_out = self.base / "fallback-scaffold"
            bundle.scaffold(synthetic_graph(), scaffold_out)
            self.assertEqual(bundle.check_bundle(scaffold_out)["paper_states"], ["scaffold"] * 3)
            capture = bundle.BundleCapture(self.source)
            out = self.base / "fallback"
            bundle.assemble_bundle(self.source / "graph.json", self.pairs, out)
            self.assertEqual(bundle.load_bundle(capture), bundle.load_bundle(out))

    @unittest.skipUnless(os.name == "posix", "requires symlink support")
    def test_pathname_fallback_rejects_a_static_symlink_without_nofollow(self):
        graph = self.source / "graph.json"
        actual = self.base / "actual.json"
        graph.rename(actual)
        graph.symlink_to(actual)
        with patch.object(bundle, "_DIRECTORY_HANDLES", False), patch.object(os, "O_NOFOLLOW", 0, create=True):
            with self.assertRaises(ContractError):
                bundle.BundleCapture(self.source)


class CurrentAssemblyBoundaryTests(unittest.TestCase):
    """New assembly is stricter than inspection of retained historical bytes."""

    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="lean-exposition-authoring-boundary-")
        self.addCleanup(temporary.cleanup)
        self.base = Path(temporary.name)

    def historical_bundle(self, graph, artifact, content, name):
        root = self.base / name
        bundle.scaffold(graph, root)
        (root / "papers/long.md").write_bytes(content)
        (root / "papers/long.json").write_bytes(encoded(artifact))
        manifest_path = root / "manifest.json"
        manifest = json.loads(manifest_path.read_bytes())
        manifest["status"] = "authored"
        for row in manifest["files"]:
            row["sha256"] = digest((root / row["path"]).read_bytes())
        manifest_path.write_bytes(encoded(manifest))
        return root

    @staticmethod
    def pairs(root):
        return {s: (root / f"papers/{s}.md", root / f"papers/{s}.json") for s in bundle.STAGES}

    def test_historical_premise_credit_is_readable_but_required_for_new_assembly(self):
        graph = application_graph()
        graph["citations"].append({"id": "premise-credit", "title": "premise-credit",
                                   "url": "https://example.org/credit", "source_id": "public",
                                   "locator": "premise"})
        next(row for row in graph["nodes"] if row["id"] == "assumption")["citation_ids"] = ["premise-credit"]
        artifact, content = synthetic_artifact(graph)
        artifact["assumption_ids"] = []
        artifact["passages"][0]["assumption_ids"] = []
        artifact["unresolved_ids"].append("supplier")
        root = self.historical_bundle(graph, artifact, content, "historical")
        self.assertTrue(bundle.check_bundle(root)["valid"])
        self.assertEqual(len(bundle.load_bundle(root)), 8)

        out = self.base / "assembled"
        with self.assertRaisesRegex(ContractError, "dropped a claim citation"):
            bundle.assemble_bundle(root / "graph.json", self.pairs(root), out)
        self.assertFalse(out.exists())

        artifact["citation_ids"].append("premise-credit")
        (root / "papers/long.json").write_bytes(encoded(artifact))
        with self.assertRaisesRegex(ContractError, "passage omits an applicable citation"):
            bundle.assemble_bundle(root / "graph.json", self.pairs(root), out)
        self.assertFalse(out.exists())

        artifact["passages"][0]["citation_ids"].append("premise-credit")
        (root / "papers/long.json").write_bytes(encoded(artifact))
        bundle.assemble_bundle(root / "graph.json", self.pairs(root), out)
        self.assertTrue(bundle.check_bundle(out)["valid"])

    def test_historical_formal_label_is_readable_but_not_newly_assembled(self):
        project = self.base / "project"
        project.mkdir()
        report, build = extraction_fixture(project)
        legacy = copy.deepcopy(report)
        legacy["schema_version"] = 1
        legacy["receipt"].pop("report_schema_version")
        for declaration in legacy["declarations"]:
            declaration.pop("is_unsafe")
            declaration.pop("is_partial")
        rebind(legacy)
        graph = to_graph(legacy, project, build)
        graph["nodes"][0]["status"] = "kernel_checked"
        artifact, content = authored_mapping(graph, "result")
        artifact["passages"][0]["evidence_class"] = "formal_result"
        root = self.historical_bundle(graph, artifact, content, "legacy-formal")
        self.assertTrue(bundle.check_bundle(root)["valid"])
        out = self.base / "legacy-assembled"
        with self.assertRaisesRegex(ContractError, "current bound extraction and build observations"):
            bundle.assemble_bundle(root / "graph.json", self.pairs(root), out)
        self.assertFalse(out.exists())

        # These are synthetic observations, used only to exercise the gate.
        graph = to_graph(report, project, build)
        extract = next(item for item in graph["evidence"] if item["kind"] == "extraction")
        extract["receipt"].update(
            extraction_request={"module": "Minimal", "roots": ["result"],
                                "module_prefixes": ["Minimal"], "max_declarations": 1},
            report_stdout_binding="lean-report-stdout-v1", process_status="passed",
            extractor_sha256="a" * 64, extractor_template_sha256="b" * 64,
            stdout_utf8_valid=True, stdout_sha256="c" * 64, stdout_bytes_sha256="c" * 64)
        next(item for item in graph["evidence"] if item["kind"] == "lean_build")["receipt"]["process_status"] = "passed"
        artifact, content = authored_mapping(graph, "result")
        artifact["passages"][0]["evidence_class"] = "formal_result"
        current = self.historical_bundle(graph, artifact, content, "current-formal")
        current_out = self.base / "current-assembled"
        bundle.assemble_bundle(current / "graph.json", self.pairs(current), current_out)
        self.assertTrue(bundle.check_bundle(current_out)["valid"])


if __name__ == "__main__":
    unittest.main()
