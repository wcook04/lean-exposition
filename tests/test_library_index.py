import importlib.util
from pathlib import Path
import unittest

spec = importlib.util.spec_from_file_location(
    "build_library_index", Path(__file__).resolve().parents[1] / "scripts" / "build_library_index.py")
index = importlib.util.module_from_spec(spec)
spec.loader.exec_module(index)

ENTRY = {
    "id": "p", "title": "A paper", "authors": ["A. Author"], "href": "/library/p/", "sentence": "",
    "counts": {"phrases": 999, "statements": 256, "lean": 1012},
    "comparator": "Comparator accepted the main theorem.",
    "credit": "Paper and Lean by A. Author.", "where": "On its current site, Proof Reader.",
}


class LibraryIndexRow(unittest.TestCase):
    def test_counts_name_what_they_count(self):
        self.assertEqual(index.count_lines(ENTRY),
                         ["999 linked passages", "1,012 linked Lean declarations", "256 passages that state a result"])

    def test_paper_given_lines_win(self):
        lines = ["121 linked statements in OpenAI’s paper"]
        self.assertEqual(index.count_lines({**ENTRY, "count_lines": lines}), lines)

    def test_groups_in_order_without_strip_or_separators(self):
        row = index.entry_html(ENTRY)
        self.assertNotIn("strip", row)
        self.assertNotIn(" · ", row)
        self.assertNotIn("%", row)
        labels = ["Linked material", "Recorded checks", "Credit and source"]
        at = [row.index(f'<h4 class="paper__label">{label}</h4>') for label in labels]
        self.assertEqual(at, sorted(at))
        for text in (ENTRY["comparator"], ENTRY["credit"], ENTRY["where"]):
            self.assertIn(index.esc(text), row)

    def test_empty_groups_are_left_out(self):
        row = index.entry_html({**ENTRY, "counts": {}, "comparator": None})
        self.assertNotIn("Linked material", row)
        self.assertNotIn("Recorded checks", row)
        self.assertIn("Credit and source", row)


if __name__ == "__main__":
    unittest.main()
