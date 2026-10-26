"""Input-path boundaries of the independent, standard-library ZIP reader."""
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest import mock
import zipfile

from lean_exposition import bundle


ROOT = Path(__file__).resolve().parents[1]
READER = ROOT / "examples/consumer/read_bundle.py"


class PortableReaderPathTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.scratch = tempfile.TemporaryDirectory(prefix="portable-reader-")
        cls.root = Path(cls.scratch.name)
        graph = json.loads((ROOT / "examples/minimal/evidence-graph.json").read_text())
        bundle.scaffold(graph, cls.root / "bundle")
        cls.archive = cls.root / "bundle.zip"
        bundle.export_bundle(cls.root / "bundle", cls.archive)

    @classmethod
    def tearDownClass(cls):
        cls.scratch.cleanup()

    def read(self, path):
        return subprocess.run(
            [sys.executable, "-I", "-S", str(READER), str(path)],
            cwd=self.root, capture_output=True, text=True, timeout=3,
        )

    @staticmethod
    def load_reader():
        spec = importlib.util.spec_from_file_location("independent_reader", READER)
        reader = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(reader)
        return reader

    def test_regular_archive_keeps_independent_success_and_hash(self):
        result = self.read(self.archive)
        self.assertEqual(result.returncode, 0, result.stderr)
        summary = json.loads(result.stdout)
        self.assertEqual(summary["archive_sha256"], hashlib.sha256(self.archive.read_bytes()).hexdigest())
        self.assertTrue(summary["transport_integrity"])
        self.assertFalse(summary["full_contract_validation"])
        self.assertFalse(summary["semantic_certification"])

    def archive_with_graph_id(self, name, graph_id):
        with zipfile.ZipFile(self.archive) as archive:
            payload = {member: archive.read(member) for member in archive.namelist()}
        graph = json.loads(payload["graph.json"])
        graph["id"] = graph_id
        payload["graph.json"] = json.dumps(graph, ensure_ascii=True).encode()
        for stage in ("long", "short", "expository"):
            name_in_zip = f"papers/{stage}.json"
            mapping = json.loads(payload[name_in_zip])
            mapping["graph_sha256"] = hashlib.sha256(payload["graph.json"]).hexdigest()
            payload[name_in_zip] = json.dumps(mapping, ensure_ascii=True).encode()
        manifest = json.loads(payload["manifest.json"])
        manifest["bundle_id"] = graph_id
        for row in manifest["files"]:
            row["sha256"] = hashlib.sha256(payload[row["path"]]).hexdigest()
        payload["manifest.json"] = json.dumps(manifest, ensure_ascii=True).encode()
        target = self.root / name
        with zipfile.ZipFile(target, "w") as archive:
            for member, content in payload.items():
                archive.writestr(member, content)
        return target

    def test_json_rejects_unpaired_surrogates_in_keys_and_values(self):
        reader = self.load_reader()
        for data in (br'{"schema_version":"1.0","nested":["\ud800"]}',
                     br'{"schema_version":"1.0","nested":{"key":"\udc00"}}',
                     br'{"schema_version":"1.0","nested":{"\ud800":"value"}}',
                     br'{"schema_version":"1.0","nested":{"\udc00":"value"}}',
                     br'{"schema_version":"1.0","nested":{"\ud800":1,"\ud800":2}}',
                     br'{"schema_version":"1.0","nested":["\udc00\ud800"]}',
                     br'{"schema_version":"1.0","nested":["\ud800x\udc00"]}'):
            with self.subTest(data=data), self.assertRaisesRegex(reader.BundleError, "unpaired Unicode surrogate"):
                reader.json_object(data, "graph.json")

    def test_scalar_check_preserves_duplicate_detection_and_valid_text(self):
        reader = self.load_reader()
        with self.assertRaisesRegex(reader.BundleError, "duplicate JSON key"):
            reader.json_object(br'{"schema_version":"1.0","x":1,"x":2}', "graph.json")
        result = reader.json_object(
            br'{"schema_version":"1.0","text":"caf\u00e9 \ud83d\ude00"}', "graph.json")
        self.assertEqual(result["text"], "caf\u00e9 \U0001f600")
        result = reader.json_object(
            br'{"schema_version":"1.0","\ud83d\ude00":"value"}', "graph.json")
        self.assertEqual(result["\U0001f600"], "value")
        with self.assertRaisesRegex(reader.BundleError, "duplicate JSON key"):
            reader.json_object(
                b'{"schema_version":"1.0","\\ud83d\\ude00":1,"\xf0\x9f\x98\x80":2}',
                "graph.json")

    def test_unpaired_surrogate_archive_returns_structured_error(self):
        archive = self.archive_with_graph_id("invalid-unicode.zip", "id-\ud800")
        result = self.read(archive)
        self.assertEqual(result.returncode, 1)
        self.assertIn("unpaired Unicode surrogate", json.loads(result.stderr)["error"])
        self.assertNotIn("Traceback", result.stderr)

    def test_escaped_surrogate_pair_remains_valid(self):
        archive = self.archive_with_graph_id("valid-unicode.zip", "id-\U0001f600")
        result = self.read(archive)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(json.loads(result.stdout)["bundle_id"], "id-\U0001f600")

    def test_symlink_to_valid_archive_is_rejected(self):
        link = self.root / "archive-link.zip"
        try:
            link.symlink_to(self.archive)
        except (OSError, NotImplementedError) as exc:
            self.skipTest(f"symlinks unavailable: {exc}")
        result = self.read(link)
        self.assertEqual(result.returncode, 1, result.stdout)
        self.assertIn("error", json.loads(result.stderr))

    @unittest.skipUnless(hasattr(os, "mkfifo"), "named FIFOs unavailable")
    def test_fifo_without_writer_is_rejected_without_waiting(self):
        fifo = self.root / "archive-fifo"
        os.mkfifo(fifo)
        result = self.read(fifo)
        self.assertEqual(result.returncode, 1, result.stdout)
        self.assertIn("error", json.loads(result.stderr))

    @unittest.skipUnless(hasattr(os, "mkfifo") and getattr(os, "O_NONBLOCK", 0),
                         "nonblocking FIFO opens unavailable")
    def test_replacement_with_fifo_at_open_does_not_wait(self):
        candidate = self.root / "replace-with-fifo.zip"
        candidate.write_bytes(b"ordinary file before open")
        probe = '''
import importlib.util, os, sys
from pathlib import Path
spec = importlib.util.spec_from_file_location("independent_reader", sys.argv[1])
reader = importlib.util.module_from_spec(spec)
spec.loader.exec_module(reader)
original_open = os.open
def replace_before_open(path, flags, *args, **kwargs):
    os.unlink(path)
    os.mkfifo(path)
    return original_open(path, flags, *args, **kwargs)
reader.os.open = replace_before_open
try:
    reader.capture(Path(sys.argv[2]))
except (reader.BundleError, OSError):
    pass
else:
    raise AssertionError("a FIFO was accepted")
'''
        result = subprocess.run([sys.executable, "-I", "-S", "-c", probe,
                                 str(READER), str(candidate)],
                                capture_output=True, text=True, timeout=3)
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_directory_is_rejected(self):
        result = self.read(self.root)
        self.assertEqual(result.returncode, 1, result.stdout)
        self.assertIn("error", json.loads(result.stderr))

    def test_regular_archive_remains_readable_without_posix_flags(self):
        reader = self.load_reader()
        with mock.patch.object(reader.os, "O_NOFOLLOW", 0, create=True), \
             mock.patch.object(reader.os, "O_NONBLOCK", 0, create=True):
            payload, archive_hash = reader.capture(self.archive)
        self.assertEqual(len(payload), 8)
        self.assertEqual(archive_hash, hashlib.sha256(self.archive.read_bytes()).hexdigest())

    def test_fallback_rejects_a_static_symlink(self):
        reader = self.load_reader()
        link = self.root / "fallback-link.zip"
        try:
            link.symlink_to(self.archive)
        except (OSError, NotImplementedError) as exc:
            self.skipTest(f"symlinks unavailable: {exc}")
        with mock.patch.object(reader.os, "O_NOFOLLOW", 0, create=True), \
             mock.patch.object(reader.os, "O_NONBLOCK", 0, create=True):
            with self.assertRaisesRegex(reader.BundleError, "not a regular file"):
                reader.capture(link)

    def test_fallback_rejects_changed_file_identity(self):
        reader = self.load_reader()
        candidate = self.root / "fallback-replacement.zip"
        replacement = self.root / "fallback-other.zip"
        shutil.copyfile(self.archive, candidate)
        shutil.copyfile(self.archive, replacement)
        original_open = os.open

        def replace_before_open(path, flags, *args, **kwargs):
            replacement.replace(candidate)
            return original_open(path, flags, *args, **kwargs)

        with mock.patch.object(reader.os, "O_NOFOLLOW", 0, create=True), \
             mock.patch.object(reader.os, "O_NONBLOCK", 0, create=True), \
             mock.patch.object(reader.os, "open", side_effect=replace_before_open):
            with self.assertRaisesRegex(reader.BundleError, "changed while opening"):
                reader.capture(candidate)

    @unittest.skipUnless(getattr(os, "O_NOFOLLOW", 0), "no-follow open unavailable")
    def test_replacement_with_symlink_at_open_is_rejected(self):
        reader = self.load_reader()
        candidate = self.root / "replace-at-open.zip"
        shutil.copyfile(self.archive, candidate)
        original_open = os.open

        def replace_before_open(path, flags, *args, **kwargs):
            candidate.unlink()
            candidate.symlink_to(self.archive)
            return original_open(path, flags, *args, **kwargs)

        with mock.patch.object(reader.os, "open", side_effect=replace_before_open):
            with self.assertRaises((reader.BundleError, OSError)):
                reader.capture(candidate)


if __name__ == "__main__":
    unittest.main()
