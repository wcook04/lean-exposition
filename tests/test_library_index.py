"""scripts/build_library_index.py: the library search says what it covers, with its denominators."""
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
from build_library_index import search_scope  # noqa: E402


class SearchScope(unittest.TestCase):
    def test_names_the_indexed_papers_and_the_title_only_ones(self):
        papers = [{"id": "euler", "shard": "x"}] + [{"id": f"p{k}"} for k in range(9)]
        self.assertEqual(search_scope(papers), "Covers 1 paper’s contents indexed (statements and Lean names), "
                                               "9 by title, authors and summary only.")

    def test_every_paper_indexed(self):
        self.assertEqual(search_scope([{"id": "a", "shard": "x"}, {"id": "b", "shard": "y"}]),
                         "Covers 2 papers’ contents indexed (statements and Lean names).")


if __name__ == "__main__":
    unittest.main()
