"""The adapted-edition converter (scripts/adapted_edition.py): every change is marked.

The first tests run on small made-up texts. The last ones run on a converted edition when one is
present (instances/*/adapted/, made locally from private inputs and not tracked until its
publication is agreed) and on its TeX when LX_ADAPTED_INPUTS names the folder that holds it.
"""
import json
import os
import re
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
sys.path.insert(0, str(ROOT / "src"))
import adapted_edition as ae  # noqa: E402


def tree(files: dict[str, str]) -> Path:
    root = Path(tempfile.mkdtemp(prefix="adapted-test-"))
    for rel, text in files.items():
        (root / rel).parent.mkdir(parents=True, exist_ok=True)
        (root / rel).write_text(text, encoding="utf-8")
    return root


AUTHORS = "\\section{One}\nFirst paragraph.\n\nSecond paragraph.\n\nThird paragraph.\n"


class TexMarks(unittest.TestCase):
    def test_a_marked_change_passes(self):
        a = tree({"main.tex": AUTHORS})
        e = tree({"main.tex": AUTHORS.replace("Second paragraph.", "% CHANGE X-1\nSecond paragraph, clarified.")})
        problems, covered = ae.unmarked_tex_changes(a, e)
        self.assertEqual(problems, [])
        self.assertEqual(covered, {"X-1": 1})

    def test_an_unmarked_change_fails(self):
        a = tree({"main.tex": AUTHORS})
        e = tree({"main.tex": AUTHORS.replace("Third paragraph.", "Third paragraph, quietly changed.")})
        problems, _ = ae.unmarked_tex_changes(a, e)
        self.assertEqual(len(problems), 1)
        self.assertIn("no CHANGE mark", problems[0])

    def test_a_change_after_an_unchanged_paragraph_needs_its_own_mark(self):
        a = tree({"main.tex": AUTHORS})
        e = tree({"main.tex": AUTHORS.replace("First paragraph.", "% CHANGE X-1\nFirst paragraph, new.")
                  .replace("Third paragraph.", "Third paragraph, new.")})
        problems, _ = ae.unmarked_tex_changes(a, e)
        self.assertTrue(any("no CHANGE mark" in p for p in problems))

    def test_a_mark_on_an_unchanged_paragraph_fails(self):
        a = tree({"main.tex": AUTHORS})
        e = tree({"main.tex": AUTHORS.replace("Second paragraph.", "% CHANGE X-1\nSecond paragraph.")})
        problems, _ = ae.unmarked_tex_changes(a, e)
        self.assertTrue(any("same as the authors'" in p for p in problems))

    def test_a_cut_paragraph_is_a_change(self):
        a = tree({"main.tex": AUTHORS})
        e = tree({"main.tex": AUTHORS.replace("Second paragraph.\n\n", "")})
        problems, _ = ae.unmarked_tex_changes(a, e)
        self.assertEqual(len(problems), 1)

    def test_an_added_file_must_be_marked(self):
        a = tree({"main.tex": AUTHORS})
        e = tree({"main.tex": AUTHORS, "extra.tex": "New words.\n"})
        problems, _ = ae.unmarked_tex_changes(a, e)
        self.assertTrue(problems)


def blocks(texts: list[str], heading: str = "1 One") -> list[dict]:
    out, line = [], 1
    for k, t in enumerate(texts, 1):
        out.append({"id": f"{heading}#{k}", "kind": "paragraph_open", "text": t, "lines": [line, line + 1], "bytes": [0, 0]})
        line += 2
    return out


class Assignment(unittest.TestCase):
    def change(self, cid, authors, kind="clarification"):
        return {"id": cid, "part": "X", "kind": kind, "authors": authors, "ours": "x.tex", "sources": [], "note": "", "status": "as returned"}

    def test_each_changed_paragraph_gets_its_change(self):
        a = blocks(["A", "B", "C", "D"])
        e = blocks(["A", "B2", "C2", "D"])
        changes = [self.change("c1", ["1 One#2"]), self.change("c2", ["1 One#3"])]
        rows, shown, problems = ae.assign(changes, a, e)
        self.assertEqual(problems, [])
        self.assertEqual(shown, [[1], [2]])
        self.assertEqual([r["change"] for r in rows], [None, "c1", "c2", None])

    def test_an_unclaimed_difference_is_reported(self):
        a = blocks(["A", "B", "C"])
        e = blocks(["A", "B", "C2"])
        _, _, problems = ae.assign([self.change("c1", ["1 One#1"])], a, e)
        self.assertTrue(any("differ with no change" in p for p in problems))

    def test_an_added_paragraph_belongs_to_the_change_beside_it(self):
        a = blocks(["A", "B", "C"])
        e = blocks(["A", "B", "New", "C"])
        rows, shown, problems = ae.assign([self.change("c1", ["1 One#2"])], a, e)
        self.assertEqual(problems, [])
        self.assertEqual(shown, [[2]])
        self.assertIn({"authors": None, "adapted": "1 One#3", "change": "c1"}, rows)


@unittest.skipUnless(any((ROOT / "instances").glob("*/adapted/changes.json")), "no adapted edition converted here")
class ConvertedEdition(unittest.TestCase):
    """On a converted edition: the change map shows every change, and every paragraph it calls
    unchanged is, word for word, the authors'."""

    def setUp(self):
        self.inst = next((ROOT / "instances").glob("*/adapted/changes.json")).parents[1]
        self.map = json.loads((self.inst / "adapted/changes.json").read_text())
        self.edition = json.loads((self.inst / "adapted/edition.json").read_text())
        main = next(d for d in json.loads((self.inst / "instance.json").read_text())["documents"] if d.get("main"))
        self.authors = (self.inst / "papers" / main["slot"] / "paper.md").read_text().split("\n")
        self.adapted = (self.inst / "adapted/paper.md").read_text().split("\n")

    def test_every_change_shows_in_a_paragraph(self):
        for c in self.map["changes"]:
            self.assertTrue(c["adapted_lines"], c["id"])

    def test_unchanged_paragraphs_are_the_authors_words(self):
        for row in self.map["paragraphs"]:
            if row["change"] is None:
                a, b = row["authors_lines"], row["adapted_lines"]
                self.assertEqual(self.authors[a[0] - 1:a[1] - 1], self.adapted[b[0] - 1:b[1] - 1], row)

    def test_every_differing_paragraph_has_its_change(self):
        for row in self.map["paragraphs"]:
            if row["authors"] is None or row["adapted"] is None:
                self.assertIsNotNone(row["change"], row)

    def test_the_credit_is_verbatim(self):
        credit = ("An adapted edition of Alpöge, Buckmaster and Coiculescu's paper, prepared by Will Cook with AI "
                  "assistance. The mathematics and the original text are the authors'. Every change is marked, and no "
                  "change has been reviewed by the authors.")
        if self.inst.name == "euler":
            self.assertEqual(self.edition["document"]["credit"], credit)

    def test_the_edition_is_off_until_published(self):
        if not self.edition["published"]:
            env = {k: v for k, v in os.environ.items() if k != "LX_PREVIEW_ADAPTED"}
            old, os.environ = os.environ, env
            try:
                self.assertFalse(ae.enabled(self.inst.name))
            finally:
                os.environ = old

    @unittest.skipUnless(os.environ.get("LX_ADAPTED_INPUTS"), "LX_ADAPTED_INPUTS does not name the edition's inputs")
    def test_every_tex_mark_is_a_visible_mark_and_no_change_is_unmarked(self):
        inputs = Path(os.environ["LX_ADAPTED_INPUTS"])
        edition, authors = inputs / "edition", Path(os.environ["LX_ADAPTED_AUTHORS"])
        marks = [m[2] for m in ae.marks_in(edition)]
        shown = {c["id"] for c in self.map["changes"] if c["adapted_lines"]}
        self.assertEqual(sorted(marks), sorted(shown))
        self.assertEqual(len(marks), len(set(marks)))
        problems, _ = ae.unmarked_tex_changes(authors, edition)
        self.assertEqual(problems, [])
        # The reading copy: a % CHANGE is a comment, so none reaches the text.
        self.assertFalse(re.search(r"% CHANGE", "\n".join(self.adapted)))


if __name__ == "__main__":
    unittest.main()
