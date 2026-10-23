"""Offline intake regressions using the actual licensed QAOA/SK corpus.

Import and declaration-name checks below inspect source text only. They are not
Lean elaboration, a proof replay, or a manuscript-correspondence review.
"""
from __future__ import annotations

import copy
import io
import json
import re
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from lean_exposition.contracts import ContractError
from lean_exposition.intake import audit_sources, fetch, validate_lock


EXAMPLE = Path(__file__).resolve().parents[1] / "examples" / "qaoa-sk"


class MemoryResponse(io.BytesIO):
    def __init__(self, content: bytes, url: str):
        super().__init__(content)
        self.url = url


class IntakeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.lock = json.loads((EXAMPLE / "source-lock.json").read_text())
        cls.public_bytes = {
            row["url"]: (EXAMPLE / row["path"]).read_bytes()
            for row in cls.lock["files"]
        }

    def setUp(self):
        guard = patch(
            "lean_exposition.intake.urllib.request.urlopen",
            side_effect=AssertionError("intake tests must not access the network"),
        )
        self.urlopen = guard.start()
        self.addCleanup(guard.stop)

    def one_public_file(self):
        lock = copy.deepcopy(self.lock)
        lock["files"] = lock["files"][:1]
        lock["derived_files"] = []
        return lock

    def test_actual_locked_corpus_audits_offline(self):
        result = audit_sources(self.lock, EXAMPLE)
        rows = self.lock["files"] + self.lock["derived_files"]
        self.assertEqual(self.lock["id"], "qaoa-sk")
        self.assertEqual(result["status"], "passed")
        self.assertEqual(result["files"], len(self.lock["files"]))
        self.assertEqual(result["derived_files"], 2)
        self.assertEqual(result["bytes"], sum(row["bytes"] for row in rows))
        self.assertEqual(result["lean_replay"], "not_implied")
        self.urlopen.assert_not_called()

    def test_unicode_equivalent_destinations_fail_before_fetch(self):
        lock = self.one_public_file()
        row = lock['files'][0]
        lock['files'] = [dict(row, path='caf\u00e9.lean'),
                         dict(row, path='cafe\u0301.lean')]
        with tempfile.TemporaryDirectory() as tmp:
            destination = Path(tmp) / 'intake'
            with self.assertRaisesRegex(ContractError, 'collide'):
                fetch(lock, destination)
            self.assertFalse(destination.exists())
        self.urlopen.assert_not_called()

    def test_derived_content_or_metadata_mismatch_is_rejected(self):
        mutations = {
            "content": lambda row: row.update(content=row["content"] + "\n"),
            "hash": lambda row: row.update(sha256="0" * 64),
            "size": lambda row: row.update(bytes=row["bytes"] + 1),
        }
        for name, mutate in mutations.items():
            with self.subTest(name=name):
                lock = copy.deepcopy(self.lock)
                mutate(lock["derived_files"][0])
                with self.assertRaisesRegex(ContractError, "derived content differs"):
                    validate_lock(lock)

    def test_source_specific_revision_mismatch_is_rejected(self):
        lock = copy.deepcopy(self.lock)
        mathlib = next(s for s in lock["sources"] if s["id"] == "mathlib")
        self.assertNotEqual(mathlib["revision"], lock["revision"])
        row = next(r for r in lock["files"] if r["source"] == "mathlib")
        # A global-pin-only validator would wrongly accept this URL.
        row["url"] = row["url"].replace(mathlib["revision"], lock["revision"])
        with self.assertRaisesRegex(ContractError, "not pinned"):
            validate_lock(lock)

    def test_unknown_derivation_input_is_rejected(self):
        lock = copy.deepcopy(self.lock)
        lock["derived_files"][0]["derived_from"].append("unlocked-input.lean")
        with self.assertRaisesRegex(ContractError, "unknown derivation source"):
            validate_lock(lock)

    def test_missing_public_source_is_rejected(self):
        with tempfile.TemporaryDirectory() as temporary:
            with self.assertRaisesRegex(ContractError, "missing source"):
                audit_sources(self.lock, Path(temporary))
        self.urlopen.assert_not_called()

    def test_wrong_hash_for_existing_public_source_is_rejected(self):
        lock = copy.deepcopy(self.lock)
        lock["files"][0]["sha256"] = "0" * 64
        with self.assertRaisesRegex(ContractError, "source hash/size mismatch"):
            audit_sources(lock, EXAMPLE)

    def test_source_and_derived_destination_traversal_fail_before_fetch(self):
        for collection in ("files", "derived_files"):
            with self.subTest(collection=collection):
                lock = copy.deepcopy(self.lock)
                lock[collection][0]["path"] = "../escaped.lean"
                with tempfile.TemporaryDirectory() as temporary:
                    parent = Path(temporary)
                    destination = parent / "fetched"
                    with self.assertRaisesRegex(ContractError, "portable relative path"):
                        fetch(lock, destination)
                    self.assertFalse((parent / "escaped.lean").exists())
                    self.assertFalse(destination.exists())
        self.urlopen.assert_not_called()

    def test_mocked_fetch_materializes_exact_public_and_inline_bytes(self):
        def response(request, timeout):
            return MemoryResponse(self.public_bytes[request.full_url], request.full_url)

        self.urlopen.side_effect = response
        with tempfile.TemporaryDirectory() as temporary:
            destination = Path(temporary) / "fetched"
            result = fetch(self.lock, destination)
            self.assertEqual(result["status"], "passed")
            for row in self.lock["files"]:
                with self.subTest(path=row["path"]):
                    self.assertEqual(
                        (destination / row["path"]).read_bytes(),
                        self.public_bytes[row["url"]],
                    )
            for row in self.lock["derived_files"]:
                with self.subTest(path=row["path"]):
                    self.assertEqual(
                        (destination / row["path"]).read_bytes(),
                        row["content"].encode("utf-8"),
                    )
            expected_count = len(self.lock["files"]) + len(self.lock["derived_files"])
            self.assertEqual(sum(p.is_file() for p in destination.rglob("*")), expected_count)
        self.assertEqual(self.urlopen.call_count, len(self.lock["files"]))
        self.assertEqual(
            {call.args[0].full_url for call in self.urlopen.call_args_list},
            set(self.public_bytes),
        )

    def test_mocked_fetch_rejects_changed_truncated_and_extra_bytes(self):
        lock = self.one_public_file()
        row = lock["files"][0]
        original = self.public_bytes[row["url"]]
        variants = {
            "changed": bytes([original[0] ^ 1]) + original[1:],
            "truncated": original[:-1],
            "extra": original + b"\n",
        }
        for name, content in variants.items():
            with self.subTest(name=name):
                self.urlopen.side_effect = None
                self.urlopen.return_value = MemoryResponse(content, row["url"])
                with tempfile.TemporaryDirectory() as temporary:
                    destination = Path(temporary) / "fetched"
                    with self.assertRaisesRegex(ContractError, "download differs"):
                        fetch(lock, destination)
                    self.assertFalse((destination / row["path"]).exists())

    def test_every_retained_oai_import_resolves_and_targets_cover_corpus(self):
        lean = EXAMPLE / "upstream" / "lean"
        modules = {
            ".".join(path.relative_to(lean).with_suffix("").parts): path
            for path in (lean / "OAI").rglob("*.lean")
        }
        self.assertEqual(len(modules), 347)
        dependencies = {}
        external = set()
        for module, path in modules.items():
            dependencies[module] = set()
            for line in path.read_text().splitlines():
                match = re.match(r"^\s*(?:public\s+)?import\s+(.+)", line)
                if not match:
                    continue
                for name in match.group(1).split("--", 1)[0].split():
                    if name.startswith("OAI."):
                        self.assertIn(name, modules, f"{module} imports missing {name}")
                        dependencies[module].add(name)
                    else:
                        external.add(name)
        self.assertEqual(external, {"Mathlib"})
        reached = set()
        for target in self.lock["targets"]:
            pending = [target["module"]]
            closure = set()
            while pending:
                module = pending.pop()
                if module in closure:
                    continue
                closure.add(module)
                pending.extend(dependencies[module])
            self.assertEqual(len(closure), target["source_files"])
            self.assertEqual(
                sum(modules[name].stat().st_size for name in closure),
                target["source_bytes"],
            )
            reached.update(closure)
        self.assertEqual(reached, set(modules))

    def test_real_target_and_comparator_names_match_source_declarations(self):
        lean = EXAMPLE / "upstream" / "lean"
        locked_paths = {row["path"] for row in self.lock["files"]}
        self.assertEqual(len(self.lock["targets"]), 2)
        for target in self.lock["targets"]:
            with self.subTest(declaration=target["declaration"]):
                config_path = EXAMPLE / target["comparator_config"]
                config = json.loads(config_path.read_text())
                self.assertEqual(config["solution_module"], target["module"])
                self.assertEqual(config["theorem_names"], [target["declaration"]])
                self.assertEqual(config["permitted_axioms"], ["propext", "Quot.sound", "Classical.choice"])
                self.assertIs(config["enable_nanoda"], False)
                for module in (target["module"], config["challenge_module"]):
                    path = lean / (module.replace(".", "/") + ".lean")
                    self.assertIn(path.relative_to(EXAMPLE).as_posix(), locked_paths)
                    text = path.read_text()
                    namespaces = re.findall(r"^namespace\s+(\S+)", text, re.MULTILINE)
                    leaf = target["declaration"].rsplit(".", 1)[1]
                    self.assertEqual(".".join(namespaces + [leaf]), target["declaration"])
                    self.assertRegex(text, re.compile(r"^theorem\s+" + re.escape(leaf) + r"(?:\s|:|\()", re.MULTILINE))


if __name__ == "__main__":
    unittest.main()
