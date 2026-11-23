"""Source review belongs to one placed passage and one Lean declaration."""

from pathlib import Path
import sys
import unittest
from unittest.mock import patch


ROOT = Path(__file__).resolve().parents[1]


class RHComparisons(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        with patch.object(sys, "path", [str(ROOT / "scripts"), *sys.path]):
            import build_rh_library

        cls.builder = build_rh_library
        cls.manifest = {source: cls.builder.read(cls.builder.INSTANCE / filename)
                        for source, filename in (("paper", "paper.json"), ("lean", "reader.json"))}
        cls.review_data = cls.builder.read(cls.builder.INSTANCE / "statement-comparisons.json")
        targets = {
            "st:rh": ["riemannHypothesis"],
            "offpath:5:1": ["riemannHypothesis"],
            "st:vwin": ["UpperTheory.Top.VVle", "UpperTheory.Top.VWin"],
        }
        all_reviews = cls.builder.statement_reviews(cls.review_data, cls.manifest)
        cls.reviews = {(mark, name): all_reviews[mark, name] for mark, names in targets.items() for name in names}
        cls.catalogue = {name: {"module": "Pinned", "line": 1, "end_line": 1, "signature_end_line": 1}
                         for names in targets.values() for name in names}
        cls.paper = b"RH mention window"
        marks = {mark: {"at": at} for mark, at in zip(targets, ("b0-2", "b3-10", "b11-17"))}
        links = {mark: {"role": "statement" if mark.startswith("st:") else "reference", "section": "", "topic": "",
                        "lean": [{"name": name, "module": "Pinned", "lines": [1, 1]} for name in names]}
                 for mark, names in targets.items()}
        cls.assets = {
            "pdf-marks.json": {"marks": marks, "pages": [{}]}, "passages.json": {"passages": links},
            "annotations.json": {"annotations": {}}, "topics.json": {"topics": [], "families": []},
            "lean-notes.json": {"sources": {}}, "lean-lines.json": {"modules": {}}, "sections.json": {"sections": []},
        }

    def project(self, reviews):
        return self.builder.reading_data(self.paper, self.assets, self.catalogue,
                                         {name: name for name in self.catalogue}, "riemannHypothesis", reviews)

    def test_fidelity_is_scoped_to_the_matching_passage_and_declaration(self):
        alignment, paper, _, _ = self.project(self.reviews)
        ties = {tie["phrase"]: tie for tie in paper["ties"]}
        main = ties["st:rh"]
        self.assertEqual((main["fidelity"], main["fidelity_source"]), ("same", "ai"))
        self.assertIn("0df444a360eaa60ab8c11dca51a86af692955474", main["explanation"]["citations"][0]["url"])
        result = alignment["records"][self.builder.GOAL]
        self.assertNotIn("fidelity", result["lean"][0])
        self.assertEqual(result["statements"][0]["lean"][0]["fidelity"], "same")

        mention = ties["offpath:5:1"]["rows"][0]
        self.assertIsNone(mention["relation"])
        self.assertIn("root declaration", mention["note"])
        self.assertNotIn("fidelity", mention)
        self.assertTrue(mention["source_review"])

        vvle, vwin = ties["st:vwin"]["rows"]
        self.assertEqual(vvle["fidelity"], "weaker")
        self.assertIn("prime pair", vwin["note"])
        self.assertNotIn("fidelity", vwin)
        self.assertTrue(vwin["source_review"])

    def test_rejects_other_revisions_and_wrong_passage_keys(self):
        with self.assertRaisesRegex(ValueError, "different lean revision"):
            self.builder.statement_reviews({**self.review_data, "lean_revision": "stale"}, self.manifest)
        with self.assertRaisesRegex(ValueError, "missing ties"):
            self.project({**self.reviews, ("st:rh", "LFunction_eq_zero_re"): {"note": "wrong declaration"}})
