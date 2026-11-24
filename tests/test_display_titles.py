"""A title correction leaves the paper selection and its annotations intact."""
from __future__ import annotations

import json
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest

from scripts.apply_display_titles import graph_title_coverage, project


class DisplayTitles(unittest.TestCase):
    def setUp(self):
        temporary = TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name).resolve()
        self.edition = self.root / "reader/edition"
        self.name = "Proof.example"
        self.tie = {"phrase": "paragraph-1", "record": "arg.example", "at": "b1-2", "part": 0,
                    "name": self.name, "plain": "Previous title", "rows": [
                        {"name": self.name, "plain": "Previous title", "annotation": "Existing explanation"}
                    ]}
        self.write("index.json", {"responses": {"/lean/names": "lean/names.json", "/alignment": "alignment.json",
                                                "/ties/short": "ties/short.json"}})
        self.write("lean/names.json", {"names": [[self.name, "theorem", 0, 1, 2]]})
        self.write("alignment.json", {"names": {self.name: "Previous title"}, "records": {}})
        self.write("ties/short.json", {"ties": [self.tie], "segments": [[1, 2, [0]]]})
        self.write("docs/adapted/index.json", {"responses": {"/ties/short": "docs/adapted/ties/short.json",
                                                             "/phrases/short": "docs/adapted/phrases/short.json"}})
        self.write("docs/adapted/ties/short.json", {"ties": [self.tie], "segments": [[1, 2, [0]]]})
        self.write("docs/adapted/phrases/short.json", {"parts": [{"titles": {}, "notes": {}}]})

    def write(self, name, data):
        path = self.edition / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(data), encoding="utf-8")

    def test_projects_one_title_with_a_companion_variant(self):
        before = {p: p.read_bytes() for p in self.root.rglob("*.json")}
        names = {self.name: "Norm bound"}
        slots = {"adapted": [{self.name: "Uniform norm bound"}]}
        files, indexes = project(self.root, "reader", names, slots)
        outputs = {str(k): json.loads(data) for k, (data, _) in files.items()}
        prefix = "reader/edition/"
        self.assertEqual(outputs[prefix + "alignment.json"]["names"], names)
        for subpath, title in (("", "Norm bound"), ("docs/adapted/", "Uniform norm bound")):
            tie_index = outputs[prefix + subpath + "ties/short.json"]
            self.assertEqual(tie_index["segments"], [[1, 2, [0]]])
            row = {**self.tie["rows"][0], "plain": title}
            self.assertEqual(tie_index["ties"], [{**self.tie, "plain": title, "rows": [row]}])
        self.assertEqual(outputs[prefix + "docs/adapted/phrases/short.json"],
                         {"parts": [{"titles": {self.name: "Uniform norm bound"}, "notes": {}}]})
        self.assertEqual(set(indexes), {prefix + "index.json", prefix + "docs/adapted/index.json"})
        self.assertEqual({p: p.read_bytes() for p in self.root.rglob("*.json")}, before)

    def test_graph_title_audit_includes_unlinked_helpers_and_projected_names(self):
        helper = "Flow.Operators.average"
        law = "Flow.Support.average"
        rows = [[self.name, "theorem", 0, 1, 2], [helper, "def", 0, 7, 7],
                [law, "def", 1, 9, 9], [helper, "def", 2, 3, 3]]
        self.write("lean/names.json", {"names": rows})
        self.write("alignment.json", {"names": {self.name: "Previous title", law: "average"}, "records": {}})
        before = graph_title_coverage(self.root, "reader")
        self.assertEqual(before["without_explicit_title"], [helper])
        self.assertEqual(before["titles_repeating_identifier"], [law])
        self.assertEqual(before["names_in_multiple_modules"], [helper])
        changes, _ = project(self.root, "reader", {helper: "Phase average of a profile",
                                                  law: "Phase averaging preserves support"})
        after = graph_title_coverage(self.root, "reader", changes)
        self.assertEqual(after["compiled_declarations"], 4)
        self.assertEqual(after["unique_names"], 3)
        self.assertEqual(after["without_explicit_title"], [])
        self.assertEqual(after["titles_repeating_identifier"], [])

    def test_checks_names_and_their_edition_part(self):
        with self.assertRaisesRegex(ValueError, "absent from its Lean index"):
            project(self.root, "reader", {"Missing.example": "Norm bound"})
        with self.assertRaisesRegex(ValueError, "unknown short part and declaration"):
            project(self.root, "reader", {self.name: "Norm bound"},
                    {"adapted": [{}, {self.name: "Another norm bound"}]})
