"""scripts/build_library_index.py: each paper's row writes its counts as labelled lines, and the
library search says what it covers, with its denominators."""
import importlib.util
from pathlib import Path
import unittest

spec = importlib.util.spec_from_file_location(
    "build_library_index", Path(__file__).resolve().parents[1] / "scripts" / "build_library_index.py")
index = importlib.util.module_from_spec(spec)
spec.loader.exec_module(index)
search_scope = index.search_scope

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

    def test_entry_prints_its_labels_versions_and_credits_in_words(self):
        entry = {**ENTRY, "tier": "lead", "kind": "Authors’ paper · Adapted edition", "provenance": "anthropic",
                 "provenance_label": "Supported by Anthropic",
                 "credits": [["Paper and Lean", "A. Author"], ["Adapted edition", "W. Cook, with AI assistance"]],
                 "versions": [{"label": "Authors’ paper", "href": "/library/p/", "note": "their text"},
                              {"label": "Adapted edition", "href": "/library/p/adapted/"},
                              {"label": "Original PDF", "href": "https://example.org/p.pdf"}]}
        row = index.entry_html(entry)
        # The provenance is a word on the entry; the colour class only repeats it.
        self.assertIn("Supported by Anthropic", row)
        self.assertIn("prov-anthropic", row)
        self.assertIn(index.esc("Authors’ paper · Adapted edition"), row)
        listed = row[row.index('<ul class="versions"'):]
        at = [listed.index(index.esc(v["label"])) for v in entry["versions"]]
        self.assertEqual(at, sorted(at))
        self.assertIn('class="version version--main" href="/library/p/"', row)
        self.assertIn("<dt>Paper and Lean</dt><dd>A. Author</dd>", row)
        self.assertIn(index.esc(ENTRY["comparator"]), row)

    def test_without_versions_the_paper_and_its_pages_are_offered(self):
        row = index.entry_html({**ENTRY, "pages": [{"title": "Exposition", "href": "/library/p/exposition/"}]})
        self.assertIn('class="version version--main" href="/library/p/"', row)
        self.assertIn('href="/library/p/exposition/"', row)
        self.assertIn(index.esc(ENTRY["credit"]), row)

    def test_sections_follow_the_tiers_in_order(self):
        entries = [{**ENTRY, "id": i, "tier": t} for i, t in (("w", "own"), ("a", "lead"), ("b", "companion"), ("c", None))]
        page = index.sections_html(entries)
        at = [page.index(f'id="shelf-{t}"') for t in ("lead", "research", "companion", "own")]
        self.assertEqual(at, sorted(at))
        self.assertIn('id="key-title"', page)


class Catalogue(unittest.TestCase):
    def test_others_research_before_companions_before_own(self):
        import json
        papers = json.loads((Path(__file__).resolve().parents[1] / "scripts/build_library_index_assets/papers.json").read_text())["papers"]
        rank = {"lead": 0, "research": 1, "companion": 2, "own": 3}
        tiers = [rank[p["tier"]] for p in papers]
        self.assertEqual(tiers, sorted(tiers))
        self.assertEqual([p["id"] for p in papers[:3]], ["navier-stokes", "euler", "riemann-hypothesis"])
        for p in papers:
            self.assertTrue(p.get("provenance_label") and p.get("kind") and p.get("credits") and p.get("versions"), p["id"])


class SearchScope(unittest.TestCase):
    def test_names_the_indexed_papers_and_the_title_only_ones(self):
        papers = [{"id": "euler", "shard": "x"}] + [{"id": f"p{k}"} for k in range(9)]
        self.assertEqual(search_scope(papers), "Search statements and Lean names in 1 paper. "
                                               "For the other 9, search by title, author or summary.")

    def test_every_paper_indexed(self):
        self.assertEqual(search_scope([{"id": "a", "shard": "x"}, {"id": "b", "shard": "y"}]),
                         "Search statements and Lean names in 2 papers.")


if __name__ == "__main__":
    unittest.main()
