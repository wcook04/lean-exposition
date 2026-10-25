"""Immutable editions reuse validated bundle bytes across read-only consumers."""
from __future__ import annotations

import json
import shutil
import tempfile
import unittest
from dataclasses import FrozenInstanceError
from pathlib import Path
from unittest.mock import patch

from lean_exposition import bundle, consumer
from lean_exposition.contracts import ContractError, digest
from test_paper_views import authored_bundle


class BundleCaptureTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="lean-exposition-capture-")
        self.addCleanup(temporary.cleanup)
        self.parent = Path(temporary.name)
        self.root = authored_bundle(self.parent, formalization=True)
        self.archive = self.parent / "original.zip"
        bundle.export_bundle(self.root, self.archive)
        self.payload = bundle.load_bundle(self.root)
        self.manifest = digest(self.payload["manifest.json"])

    def test_directory_and_zip_capture_same_exact_edition_and_export(self):
        expected_summary = bundle.check_bundle(self.root)
        for index, path in enumerate((self.root, self.archive)):
            with self.subTest(input=path.name):
                capture = bundle.BundleCapture(path)
                self.assertEqual(dict(capture.files), self.payload)
                self.assertEqual(set(capture.files), set(bundle.BUNDLE_FILES))
                self.assertTrue(all(type(value) is bytes for value in capture.files.values()))
                self.assertEqual(bundle.check_bundle(capture), expected_summary)
                exported = self.parent / f"capture-{index}.zip"
                bundle.export_bundle(capture, exported)
                self.assertEqual(exported.read_bytes(), self.archive.read_bytes())

    def test_invalid_filesystem_input_rejects_during_construction(self):
        (self.root / "papers/short.md").write_bytes(b"changed after binding")
        self.archive.write_bytes(b"not a ZIP archive")
        link = self.parent / "alias"
        link.symlink_to(self.root, target_is_directory=True)
        for path in (self.root, self.archive, link, self.parent / "missing"):
            with self.subTest(input=path.name), self.assertRaises(ContractError):
                bundle.BundleCapture(path)
        for value in (self.payload, list(self.payload.items()), bytearray(b"bundle")):
            with self.subTest(input_type=type(value).__name__), self.assertRaises(TypeError):
                bundle.BundleCapture(value)

    def test_capture_and_returned_mappings_cannot_be_mutated_by_callers(self):
        capture = bundle.BundleCapture(self.root)
        with self.assertRaises(TypeError):
            capture.files["graph.json"] = b"changed"
        with self.assertRaises(FrozenInstanceError):
            capture.files = self.payload
        with self.assertRaises(FrozenInstanceError):
            del capture.files
        with self.assertRaises(AttributeError):
            capture.__init__(self.archive)

        returned = bundle.load_bundle(capture)
        returned["graph.json"] = b"changed"
        returned.clear()
        decoded = json.loads(capture.files["graph.json"])
        decoded["title"] = "Caller-local edit"
        summary = bundle.check_bundle(capture)
        summary["graph"].clear()
        self.assertEqual(bundle.load_bundle(capture), self.payload)
        self.assertIsNot(bundle.load_bundle(capture), bundle.load_bundle(capture))
        self.assertEqual(bundle.check_bundle(capture), bundle.check_bundle(self.root))

    def test_capture_survives_source_changes_and_deletion_without_reads_or_validation(self):
        captures = [bundle.BundleCapture(path) for path in (self.root, self.archive)]
        expected_summary = bundle.check_bundle(self.root)
        (self.root / "papers/short.md").write_bytes(b"later document")
        self.archive.write_bytes(b"later archive")
        for capture in captures:
            self.assertEqual(bundle.load_bundle(capture), self.payload)
        shutil.rmtree(self.root)
        self.archive.unlink()
        with patch.object(bundle, "_capture_directory", side_effect=AssertionError("must not reopen")), \
             patch.object(bundle, "_capture_archive", side_effect=AssertionError("must not reopen")), \
             patch.object(bundle, "_validate_payload", side_effect=AssertionError("already validated")):
            for capture in captures:
                self.assertEqual(bundle.load_bundle(capture), self.payload)
                self.assertEqual(bundle.check_bundle(capture), expected_summary)

    def test_all_consumer_operations_match_filesystem_outputs_after_removal(self):
        view = consumer.project_paper(self.root, "short")
        span = next(p for p in view["paper"]["passages"] if p["anchor"] == "result")["content_span"]
        operations = {
            "bundle": lambda source: consumer.inspect_bundle(source),
            "paper": lambda source: consumer.project_paper(source, "short", ["result"]),
            "corpus": lambda source: consumer.project_corpus(source, expected_manifest_sha256=self.manifest),
            "corpus query": lambda source: consumer.query_corpus(
                source, records=[("sources", "public")], families=["provenance"],
                direction="incoming", max_depth=2, expected_manifest_sha256=self.manifest),
            "paper query": lambda source: consumer.query_papers(
                source, node_ids=["prerequisite"], relation="prerequisites",
                expected_manifest_sha256=self.manifest),
            "range query": lambda source: consumer.query_papers(
                source, stage="short", byte_ranges=[(span["start_byte"], span["end_byte"])],
                expected_manifest_sha256=self.manifest),
            "reconstruction": lambda source: consumer.reconstruct_paper(
                source, "short", view["paper"]["document_parts"],
                expected_manifest_sha256=self.manifest),
            "graph inspection": lambda source: consumer.inspect_graph(
                json.loads(bundle.load_bundle(source)["graph.json"])),
            "typed graph": lambda source: consumer.project_graph(
                bundle.load_bundle(source)["graph.json"], "arguments", ["goal"],
                include_assumptions=True),
        }
        expected = {name: operation(self.root) for name, operation in operations.items()}
        captures = [bundle.BundleCapture(path) for path in (self.root, self.archive)]
        shutil.rmtree(self.root)
        self.archive.unlink()
        for capture in captures:
            for name, operation in operations.items():
                with self.subTest(operation=name):
                    self.assertEqual(operation(capture), expected[name])

    def test_expected_manifest_still_enforces_exact_captured_edition(self):
        capture = bundle.BundleCapture(self.root)
        view = consumer.project_paper(capture, "short")
        operations = (
            lambda expected: consumer.project_corpus(capture, expected_manifest_sha256=expected),
            lambda expected: consumer.query_corpus(capture, records=[("nodes", "goal")],
                                                   expected_manifest_sha256=expected),
            lambda expected: consumer.query_papers(capture, stage="short", passages=["result"],
                                                   expected_manifest_sha256=expected),
            lambda expected: consumer.reconstruct_paper(capture, "short", view["paper"]["document_parts"],
                                                        expected_manifest_sha256=expected),
        )
        for operation in operations:
            operation(self.manifest)
            with self.assertRaisesRegex(ContractError, "differs from the requested edition"):
                operation("0" * 64)
            with self.assertRaisesRegex(ContractError, "64 lowercase hexadecimal"):
                operation("stale")


if __name__ == "__main__":
    unittest.main()
