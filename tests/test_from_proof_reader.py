"""scripts/from_proof_reader.py: a Proof Reader page becomes a library instance, and a re-import
keeps every old tie id as an address."""
import json
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CONVERTER = ROOT / "scripts/from_proof_reader.py"
LEAN_EXPOSITION = shutil.which("lean-exposition")

PAPER = """# A small paper

## 1 Introduction

**Theorem 1.1.** Every widget is round and every gadget is square.

The widgets are round because they roll. The gadgets are square because they stack.
"""
LEAN = """namespace Demo

/-- Widgets are round. -/
theorem widget_round : True := trivial

/-- Gadgets are square. -/
theorem gadget_square : True := trivial

end Demo
"""


def page(root: Path, passages: list[dict]) -> Path:
    folder = root / "papers/demo"
    (folder / "lean/Demo").mkdir(parents=True, exist_ok=True)
    (folder / "lean/Demo/Basic.lean").write_text(LEAN)
    (folder / "paper.md").write_text(PAPER)
    (folder / "paper.toml").write_text('[paper]\ntitle = "A small paper"\nauthors = ["A. Author", "B. Author"]\n'
                                       '[credit]\ntext = "Paper and Lean by A. Author and B. Author."\n'
                                       '[lean]\nproject = "lean"\nsource = "https://github.com/example/demo/tree/' + "0" * 40 + '/lean"\n')
    links = {
        "families": [{"id": "shapes", "name": "Shapes"}],
        "topics": [{"id": "round", "name": "Round things", "family": "shapes"}, {"id": "square", "name": "Square things", "family": "shapes"}],
        "claims": [{"id": "result-1.1", "title": "Theorem 1.1", "section": "1", "passage": "p.theorem", "lean": ["Demo.widget_round"]}],
        "passages": passages,
        "plain": {"Demo.widget_round": "Widgets are round", "Demo.gadget_square": "Gadgets are square"},
        "notes": {"Demo.widget_round": {"text": "Every widget is round.", "on": "lean"},
                  "Demo.gadget_square": {"text": "Every gadget is square.", "on": "lean"}},
    }
    (folder / "links.json").write_text(json.dumps(links))
    return folder


def passage(pid, quote, lean, topic):
    return {"id": pid, "section": "1", "role": "states", "quote": quote, "lean": [lean], "topic": topic,
            "anchor": {"heading": "1 Introduction", "block": 1}, "comparisons": [{"lean": lean, "fidelity": "same", "note": ""}]}


ALL = [passage("p.theorem", "Every widget is round", "Demo.widget_round", "round"),
       passage("p.roll", "The widgets are round because they roll", "Demo.widget_round", "round"),
       passage("p.stack", "The gadgets are square because they stack", "Demo.gadget_square", "square")]


sys.path.insert(0, str(ROOT / "scripts"))
from from_proof_reader import statement_block  # noqa: E402


class StatementBlock(unittest.TestCase):
    """A numbered result's canonical target is its statement block, never the introduction before it."""

    TEXT = ("<a id=\"1\"></a>\n\n# 1 Intro\n\nThe theorem below concerns widgets.\n\n"
            "**Theorem 1.1.** Every widget is round, $$\\begin{equation}\n a\n\n b\n\\end{equation}$$ and square.\n\n"
            "**Theorem 1.12.** Another.\n\n<a id=\"9\"></a>\n\n**Theorem 1.1.** A restatement in an appendix.\n")

    def test_the_label_paragraph_with_its_displays(self):
        intro = self.TEXT.index("The theorem below")
        begin, stop, found = statement_block(self.TEXT, "Theorem 1.1", self.TEXT.index('<a id="1">'), (intro, intro + 20))
        self.assertTrue(found)
        self.assertEqual(self.TEXT[begin:stop], "**Theorem 1.1.** Every widget is round, $$\\begin{equation}\n a\n\n b\n\\end{equation}$$ and square.")

    def test_a_longer_number_and_another_section_are_not_the_result(self):
        begin, _, _ = statement_block(self.TEXT, "Theorem 1.1", self.TEXT.index('<a id="9">'), None)
        self.assertTrue(self.TEXT[begin:].startswith("**Theorem 1.1.** A restatement"))
        begin, stop, _ = statement_block(self.TEXT, "Theorem 1.12", None, None)
        self.assertEqual(self.TEXT[begin:stop], "**Theorem 1.12.** Another.")

    def test_without_a_label_the_claims_phrase(self):
        self.assertEqual(statement_block(self.TEXT, "Lemma 4.4", None, (3, 9)), (3, 9, False))


@unittest.skipUnless(LEAN_EXPOSITION, "needs the lean-exposition command")
class FromProofReader(unittest.TestCase):
    def convert(self, root, folder, *extra):
        result = subprocess.run([sys.executable, str(CONVERTER), str(folder), "--paper", "demo", "--out", str(root / "instances/demo"),
                                 "--source-commit", "1" * 40, "--lean-exposition", LEAN_EXPOSITION, *extra],
                                capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        return root / "instances/demo"

    def check(self, out):
        return subprocess.run([LEAN_EXPOSITION, "check-alignment", str(out / "alignment"), "--lean-tree", str(out / "upstream/lean"),
                               "--graph", str(out / "evidence-graph.json"), "--paper", "short", str(out / "papers/short/paper.md"),
                               "--paper", "long", str(out / "papers/long/absent.md"), "--paper", "expository", str(out / "papers/expository/absent.md")],
                              capture_output=True, text=True)

    def test_converts_and_reimport_keeps_addresses(self):
        with tempfile.TemporaryDirectory() as scratch:
            root = Path(scratch)
            out = self.convert(root, page(root, ALL))
            instance = json.loads((out / "instance.json").read_text())
            self.assertEqual([t["family"] for t in instance["topics"]], ["shapes", "shapes"])
            phrases = json.loads((out / "alignment/phrases-short.json").read_text())
            self.assertEqual([t["id"] for t in phrases["ties"]], ["p.theorem", "p.roll", "p.stack"])
            self.assertIn("theorem-1.1", json.loads((out / "alignment/results.json").read_text())["results"])
            check = self.check(out)
            self.assertEqual(check.returncode, 0, check.stdout + check.stderr)
            # A return drops one tie and adds a comparison note. The dropped id is retired, with the date
            # and the nearest current phrase; it is never an alias that lands on that neighbour.
            revised = [ALL[0], dict(ALL[2], comparisons=[{"lean": "Demo.gadget_square", "fidelity": "weaker", "note": "Says less."}])]
            out = self.convert(root, page(root, revised), "--reimport", "--retired-on", "2026-11-21")
            phrases = json.loads((out / "alignment/phrases-short.json").read_text())
            self.assertEqual([t["id"] for t in phrases["ties"]], ["p.theorem", "p.stack"])
            self.assertEqual(phrases["ties"][1]["lean"][0]["fidelity"], "weaker")
            table = json.loads((out / "alignment/aliases.json").read_text())
            self.assertNotIn("p.roll", table["passages"])
            self.assertEqual(table["retired"]["p.roll"], {"retired": "2026-11-21", "nearest": "p.theorem"})
            # A later re-import keeps the retirement and its first date.
            out = self.convert(root, page(root, revised), "--reimport", "--retired-on", "2026-12-01")
            table = json.loads((out / "alignment/aliases.json").read_text())
            self.assertEqual(table["retired"]["p.roll"]["retired"], "2026-11-21")

    def test_pinned_source_root_reaches_the_index(self):
        from lean_exposition.lean_index import build_index

        revision = "0" * 40
        for suffix in ("", "/lean", "/formalization/lean/"):
            with self.subTest(suffix=suffix), tempfile.TemporaryDirectory() as scratch:
                root = Path(scratch)
                folder = page(root, ALL)
                toml = folder / "paper.toml"
                toml.write_text(toml.read_text().replace(revision + "/lean", revision + suffix))
                out = self.convert(root, folder)
                tree = out / "upstream/lean"
                index = build_index(tree)
                link = index["base_url"] + index["modules"][0]["path"]
                self.assertEqual(link, f"https://github.com/example/demo/blob/{revision}{suffix.rstrip('/')}/Demo/Basic.lean")

    def test_an_old_alias_no_merge_explains_is_retired(self):
        with tempfile.TemporaryDirectory() as scratch:
            root = Path(scratch)
            out = self.convert(root, page(root, ALL))
            # An earlier import sent a removed id to a neighbour; that is not a merge, so it is retired.
            table = json.loads((out / "alignment/aliases.json").read_text())
            table["passages"]["p.old"] = "p.stack"
            (out / "alignment/aliases.json").write_text(json.dumps(table))
            out = self.convert(root, page(root, ALL), "--reimport", "--retired-on", "2026-11-21")
            table = json.loads((out / "alignment/aliases.json").read_text())
            self.assertNotIn("p.old", table["passages"])
            self.assertEqual(table["retired"]["p.old"], {"retired": "2026-11-21", "nearest": "p.stack"})

    def test_a_missing_comparison_is_unassessed_never_same(self):
        with tempfile.TemporaryDirectory() as scratch:
            root = Path(scratch)
            folder = page(root, [dict(ALL[0], comparisons=[]), ALL[2]])
            out = self.convert(root, folder)
            ties = json.loads((out / "alignment/phrases-short.json").read_text())["ties"]
            self.assertEqual(ties[0]["lean"][0]["fidelity"], "unassessed")
            self.assertEqual(ties[1]["lean"][0]["fidelity"], "same")
            # The numbered result has no verdict in the page's `fidelity` table either.
            records = json.loads((out / "alignment/m1-results.json").read_text())["records"]
            self.assertEqual(records["demo.theorem-1.1"]["lean"][0]["fidelity"], "unassessed")
            report = json.loads((out / "generated/conversion-report.json").read_text())
            self.assertEqual(report["summary"]["unassessed"], 2)
            self.assertEqual(self.check(out).returncode, 0)

    def test_overlapping_phrases_keep_every_assessment(self):
        with tempfile.TemporaryDirectory() as scratch:
            root = Path(scratch)
            outer = dict(passage("p.outer", "Every widget is round and every gadget is square", "Demo.widget_round", "round"),
                         comparisons=[{"lean": "Demo.widget_round", "fidelity": "same", "note": "Only for round widgets."}])
            inner = dict(passage("p.inner", "every gadget is square", "Demo.widget_round", "square"),
                         lean=["Demo.widget_round", "Demo.gadget_square"],
                         comparisons=[{"lean": "Demo.widget_round", "fidelity": "stronger", "note": "Says more."},
                                      {"lean": "Demo.gadget_square", "fidelity": "weaker", "note": "Says less."}])
            folder = page(root, [outer, inner, ALL[2]])
            links = json.loads((folder / "links.json").read_text())
            links["claims"][0]["passage"] = "p.outer"
            (folder / "links.json").write_text(json.dumps(links))
            out = self.convert(root, folder)
            tie = json.loads((out / "alignment/phrases-short.json").read_text())["ties"][0]
            self.assertEqual(tie["id"], "p.outer")
            self.assertEqual([m["id"] for m in tie["merged"]], ["p.outer", "p.inner"])
            self.assertEqual(tie["merged"][1]["quote"], "every gadget is square")
            widget = next(r for r in tie["lean"] if r["name"] == "Demo.widget_round")
            # The inner phrase's "stronger" is kept beside the outer phrase's "same", not dropped.
            self.assertEqual([(a["phrase"], a["fidelity"]) for a in widget["assessments"]],
                             [("p.outer", "same"), ("p.inner", "stronger")])
            self.assertEqual(widget["assessments"][0]["fidelity_note"], "Only for round widgets.")
            gadget = next(r for r in tie["lean"] if r["name"] == "Demo.gadget_square")
            self.assertEqual(gadget["assessments"], [{"phrase": "p.inner", "fidelity": "weaker", "fidelity_note": "Says less."}])
            report = json.loads((out / "generated/conversion-report.json").read_text())
            self.assertEqual(report["merged_assessments_differ"][0][:2], ["p.outer", "Demo.widget_round"])
            self.assertEqual(self.check(out).returncode, 0, self.check(out).stdout)


    def test_held_comparisons_stay_hidden_and_others_show(self):
        with tempfile.TemporaryDirectory() as scratch:
            root = Path(scratch)
            folder = page(root, [dict(ALL[0], comparisons=[{"lean": "Demo.widget_round", "fidelity": "weaker", "note": "Says less."}]), ALL[2]])
            links = json.loads((folder / "links.json").read_text())
            links["fidelity_held"] = "The comparisons are held until the authors have seen them."
            (folder / "links.json").write_text(json.dumps(links))
            out = self.convert(root, folder)
            shown = json.loads((out / "alignment/phrases-short.json").read_text())
            self.assertEqual(shown["ties"][0]["lean"][0]["fidelity"], "weaker")
            self.assertNotIn("comparisons_hidden", json.loads((out / "instance.json").read_text()))
            out = self.convert(root, folder, "--hold-comparisons")
            held = json.loads((out / "alignment/phrases-short.json").read_text())
            self.assertEqual({row["fidelity"] for t in held["ties"] for row in t["lean"]}, {"held"})
            self.assertNotIn("Says less", json.dumps(held))
            # The numbered results are held too: a held paper never shows "same" for its results.
            records = json.loads((out / "alignment/m1-results.json").read_text())["records"]
            self.assertEqual({row["fidelity"] for r in records.values() for row in r["lean"]}, {"held"})
            instance = json.loads((out / "instance.json").read_text())
            self.assertTrue(instance["comparisons_hidden"])
            self.assertEqual(instance["comparisons_held_text"], links["fidelity_held"])


if __name__ == "__main__":
    unittest.main()
