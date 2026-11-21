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


@unittest.skipUnless(LEAN_EXPOSITION, "needs the lean-exposition command")
class FromProofReader(unittest.TestCase):
    def convert(self, root, folder, *extra):
        result = subprocess.run([sys.executable, str(CONVERTER), str(folder), "--paper", "demo", "--out", str(root / "instances/demo"),
                                 "--source-commit", "1" * 40, "--lean-exposition", LEAN_EXPOSITION, *extra],
                                capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        return root / "instances/demo"

    def test_converts_and_reimport_keeps_addresses(self):
        with tempfile.TemporaryDirectory() as scratch:
            root = Path(scratch)
            out = self.convert(root, page(root, ALL))
            instance = json.loads((out / "instance.json").read_text())
            self.assertEqual([t["family"] for t in instance["topics"]], ["shapes", "shapes"])
            phrases = json.loads((out / "alignment/phrases-short.json").read_text())
            self.assertEqual([t["id"] for t in phrases["ties"]], ["p.theorem", "p.roll", "p.stack"])
            self.assertIn("theorem-1.1", json.loads((out / "alignment/results.json").read_text())["results"])
            check = subprocess.run([LEAN_EXPOSITION, "check-alignment", str(out / "alignment"), "--lean-tree", str(out / "upstream/lean"),
                                    "--graph", str(out / "evidence-graph.json"), "--paper", "short", str(out / "papers/short/paper.md"),
                                    "--paper", "long", str(out / "papers/long/absent.md"), "--paper", "expository", str(out / "papers/expository/absent.md")],
                                   capture_output=True, text=True)
            self.assertEqual(check.returncode, 0, check.stdout + check.stderr)
            # A return drops one tie and adds a comparison note; the dropped id still lands on a neighbour.
            revised = [ALL[0], dict(ALL[2], comparisons=[{"lean": "Demo.gadget_square", "fidelity": "weaker", "note": "Says less."}])]
            out = self.convert(root, page(root, revised), "--reimport")
            phrases = json.loads((out / "alignment/phrases-short.json").read_text())
            self.assertEqual([t["id"] for t in phrases["ties"]], ["p.theorem", "p.stack"])
            self.assertEqual(phrases["ties"][1]["lean"][0]["fidelity"], "weaker")
            aliases = json.loads((out / "alignment/aliases.json").read_text())["passages"]
            self.assertEqual(aliases["p.roll"], "p.theorem")


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
            instance = json.loads((out / "instance.json").read_text())
            self.assertTrue(instance["comparisons_hidden"])
            self.assertEqual(instance["comparisons_held_text"], links["fidelity_held"])


if __name__ == "__main__":
    unittest.main()
