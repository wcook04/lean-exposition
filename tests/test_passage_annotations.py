"""Exercise the build's join against main, companion, adapted and RH tie responses."""
from __future__ import annotations

import json
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest

from scripts.apply_passage_annotations import apply_annotations


def write_json(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value), encoding="utf-8")


class PassageAnnotations(unittest.TestCase):
    def setUp(self):
        temp = TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.instance = Path(temp.name) / "instances/paper"
        self.edition = Path(temp.name) / "edition"
        self.annotations = self.instance / "annotations"
        write_json(self.instance / "instance.json", {"documents": [{"slot": "short"}, {"slug": "link"}]})

    def export(self, *, slot="short", companion=False, phrase="paragraph-1", filename=None):
        root = Path(f"docs/{slot}") if companion else Path()
        stage = "short" if companion else slot
        index = self.edition / root / "index.json"
        path = root / (filename or f"ties/{stage}.json")
        write_json(index, {"responses": {f"/ties/{stage}": path.as_posix()},
                           "snapshot": {"manifest_sha256": "bound-to-original-paper"}})
        ties = self.edition / path
        write_json(ties, {"paper": stage, "ties": [
            {"record": "one", "name": "Proof.result"},  # An old record-only tie.
            {"phrase": phrase, "rows": [
                {"name": "Proof.result", "plain": "A title", "note": "Earlier comparison"},
                {"name": "Proof.part", "fidelity": "weaker"},
            ]},
            {"phrase": "paragraph-2", "rows": [{"name": "Proof.result", "matters": "Earlier role"}]},
            {"phrase": "unmapped", "rows": []},
        ], "segments": [[1, 2, [1]]]})
        return ties

    def test_exact_pairs_only_with_legacy_rows_and_idempotent_writes(self):
        ties = self.export()
        source = self.annotations / "short.json"
        write_json(source, {"paragraph-1": {"Proof.result": "A new note with $x^2$."}})
        index = (self.edition / "index.json").read_bytes()
        before = ties.read_bytes()
        baseline = self.edition.parent / "baseline-ties.json"
        baseline.hardlink_to(ties)
        self.assertEqual(apply_annotations(self.instance, self.edition), {"short": 1})
        self.assertEqual(ties.read_bytes(), before)
        apply_annotations(self.instance, self.edition, write=True)
        expected = json.loads(before)
        expected["ties"][1]["rows"][0]["annotation"] = "A new note with $x^2$."
        self.assertEqual(json.loads(ties.read_bytes()), expected)
        self.assertEqual(baseline.read_bytes(), before)
        self.assertEqual((self.edition / "index.json").read_bytes(), index)
        written = ties.stat().st_ino
        apply_annotations(self.instance, self.edition, write=True)
        self.assertEqual(ties.stat().st_ino, written)
        write_json(source, {})
        apply_annotations(self.instance, self.edition, write=True)
        self.assertEqual(json.loads(ties.read_bytes()), json.loads(before))

    def test_nonstandard_rh_mark_keys_and_complete_coverage(self):
        (self.instance / "instance.json").unlink()
        write_json(self.instance / "reader.json", {"root": "Proof.result"})
        ties = self.export(phrase="offpath:5:1")
        with self.assertRaisesRegex(ValueError, r"3 exported pair\(s\) lack annotations"):
            apply_annotations(self.instance, self.edition, complete=True)
        write_json(self.annotations / "short.json", {
            "offpath:5:1": {"Proof.result": "Result", "Proof.part": "Part"}, "paragraph-2": {"Proof.result": "Reuse"},
        })
        self.assertEqual(apply_annotations(self.instance, self.edition, write=True, complete=True), {"short": 3})
        row = json.loads(ties.read_bytes())["ties"][1]["rows"][1]
        self.assertEqual(row, {"name": "Proof.part", "fidelity": "weaker", "annotation": "Part"})

    def test_companion_and_adapted_slots_target_their_own_short_routes(self):
        main = self.export()
        companion = self.export(slot="guide", companion=True)
        write_json(self.instance / "instance.json",
                   {"documents": [{"slot": "short"}, {"slot": "guide", "kind": "companion"}]})
        write_json(self.instance / "adapted/edition.json", {"document": {"slot": "adapted"}, "published": False})
        write_json(self.annotations / "guide.json", {"paragraph-1": {"Proof.result": "A guide note"}})
        write_json(self.annotations / "adapted.json", {"paragraph-1": {"Proof.result": "An adapted note"}})
        self.assertEqual(apply_annotations(self.instance, self.edition, write=True), {"guide": 1})
        adapted = self.export(slot="adapted", companion=True)  # A preview includes the draft's index.
        self.assertEqual(apply_annotations(self.instance, self.edition, write=True), {"adapted": 1, "guide": 1})
        for ties, note in [(main, None), (companion, "A guide note"), (adapted, "An adapted note")]:
            self.assertEqual(json.loads(ties.read_bytes())["ties"][1]["rows"][0].get("annotation"), note)

    def test_rejects_invalid_targets_before_writing_any_file(self):
        main = self.export()
        extra = self.export(slot="guide", companion=True)
        previous = extra.read_bytes()
        write_json(self.instance / "instance.json",
                   {"documents": [{"slot": "short"}, {"slot": "guide", "kind": "companion"}]})
        write_json(self.annotations / "guide.json", {"paragraph-1": {"Proof.result": "Good pair"}})
        source = self.annotations / "short.json"
        for value, error in [
            ('{"paragraph-1":{"Proof.result":"One","Proof.result":"Two"}}', "duplicate JSON key"),
            ('{"paragraph-1":{"Proof.part":" "}}', "nonempty annotation text"),
            ('{"paragraph-2":{"Proof.part":"Wrong passage"}}', "do not match exported ties"),
        ]:
            source.write_text(value, encoding="utf-8")
            with self.subTest(error=error), self.assertRaisesRegex(ValueError, error):
                apply_annotations(self.instance, self.edition, write=True)
            self.assertEqual(extra.read_bytes(), previous)
        source.unlink()
        write_json(self.annotations / "unpublished.json", {})
        with self.assertRaisesRegex(ValueError, "unknown document slot"):
            apply_annotations(self.instance, self.edition, write=True)
        self.assertNotIn(b"annotation", main.read_bytes())

    def test_original_only_capture_can_have_an_adapted_source(self):
        self.export()
        write_json(self.instance / "adapted/edition.json", {"document": {"slot": "adapted"}, "published": True})
        write_json(self.annotations / "short.json", {
            "paragraph-1": {"Proof.result": "Result", "Proof.part": "Part"}, "paragraph-2": {"Proof.result": "Reuse"},
        })
        write_json(self.annotations / "adapted.json", {"paragraph-1": {"Proof.result": "An adapted note"}})
        self.assertEqual(apply_annotations(self.instance, self.edition, complete=True), {"short": 3})
        (self.edition / "docs/adapted").mkdir(parents=True)
        with self.assertRaisesRegex(FileNotFoundError, "docs/adapted/index.json"):
            apply_annotations(self.instance, self.edition, complete=True)

    def test_refuses_to_overwrite_content_addressed_export(self):
        hashed = self.export(filename=f"{'a' * 64}.json")
        original = hashed.read_bytes()
        write_json(self.annotations / "short.json", {"paragraph-1": {"Proof.result": "Text"}})
        with self.assertRaisesRegex(ValueError, "must name the fixed-path response"):
            apply_annotations(self.instance, self.edition, write=True)
        self.assertEqual(hashed.read_bytes(), original)


if __name__ == "__main__":
    unittest.main()
