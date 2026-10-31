"""Record alignment: authored pointers against real and adversarial bytes."""
import json
import tempfile
import unittest
from pathlib import Path

from lean_exposition import alignment
from lean_exposition.cli import main
from lean_exposition.contracts import ContractError

ROOT = Path(__file__).resolve().parents[1]
INDEX = {"modules": [{"name": "OAI.M", "path": "OAI/M.lean", "declarations": [
    {"name": "N.thing", "written": "thing", "line": 3, "end_line": 5},
    {"name": "N.S.val", "written": "val", "line": 7, "end_line": 7},
    {"name": "N.T.val", "written": "val", "line": 8, "end_line": 8}]}]}
LONG = """# Title

## Café results

<!-- passage:first -->
Before. Théorème one states $x=1$.
<!-- /passage:first -->

### Part

Repeated words here. Repeated words here. Unique end $$y$$ tail.
""".encode()
PAPERS = {"long": LONG, "short": b"# Short\n\nA $ lone dollar.\n", "expository": b"# E\n"}
LEAN = {"file": "OAI/M.lean", "name": "thing", "relation": "states", "note": "Same claim."}
STATEMENT = {"paper": "long", "role": "statement", "from": "Théorème one", "to": "$x=1$."}


def resolve(records=None, terms=None, extra=None, strict=True):
    with tempfile.TemporaryDirectory() as directory:
        path = Path(directory)
        (path / "batch.json").write_text(json.dumps(
            {"schema_version": "1.0", **({"records": records} if records is not None else {}),
             **({"terms": terms} if terms is not None else {})}))
        for name, text in (extra or {}).items():
            (path / name).write_text(text)
        return alignment.resolve_alignment(path, INDEX, PAPERS, {"r", "s"}, strict=strict)


def row(lean=(LEAN,), statements=(STATEMENT,), short="A short title"):
    return {"short": short, "lean": list(lean), "statements": list(statements)}


class Resolve(unittest.TestCase):
    def fails(self, pattern, **options):
        with self.assertRaisesRegex(ContractError, pattern):
            resolve(**options)

    def test_resolves_names_bytes_passage_and_section(self):
        out = resolve({"r": row()})[0]["records"]["r"]
        self.assertEqual(out["lean"], [{"name": "N.thing", "module": "OAI.M", "line": 3, "end_line": 5,
                                        "relation": "states", "note": "Same claim."}])
        slice_ = out["statements"][0]
        self.assertEqual(LONG[slice_["start_byte"]:slice_["end_byte"]].decode(), slice_["markdown"])
        self.assertEqual(slice_["markdown"], "Théorème one states $x=1$.")
        self.assertEqual(slice_["anchor"], "first")
        self.assertEqual((slice_["section"], slice_["heading_id"]), ("Café results", "café-results"))

    def test_after_selects_a_repeated_quotation(self):
        statement = {**STATEMENT, "from": "Repeated words", "to": "here.", "after": "### Part\n\nRepeated words here. "}
        out = resolve({"r": row(statements=[statement])})[0]["records"]["r"]["statements"][0]
        self.assertEqual(out["section"], "Part")
        self.assertIsNone(out["anchor"])
        self.assertEqual(out["start_byte"], LONG.rindex(b"Repeated"))

    def test_a_partial_directory_resolves_and_companions_are_ignored(self):
        resolved, errors = resolve({"r": row()}, extra={"notes.json": '{"schema_version": "1.0", "pairs": []}'})
        self.assertEqual((list(resolved["records"]), resolved["dictionary"], errors), (["r"], [], []))

    def test_rejects_each_broken_pointer(self):
        self.fails("not a record", records={"absent": row()})
        self.fails("short has 7 words", records={"r": row(short="one two three four five six seven")})
        self.fails("no Lean file", records={"r": row(lean=[{**LEAN, "file": "OAI/X.lean"}])})
        self.fails("no declaration", records={"r": row(lean=[{**LEAN, "name": "absent"}])})
        self.fails("ambiguous", records={"r": row(lean=[{**LEAN, "name": "val"}])})
        self.fails("unknown relation", records={"r": row(lean=[{**LEAN, "relation": "proves"}])})
        self.fails("exceeds 25 words", records={"r": row(lean=[{**LEAN, "note": "word " * 26}])})
        self.fails("unknown role", records={"r": row(statements=[{**STATEMENT, "role": "aside"}])})
        self.fails("unknown paper", records={"r": row(statements=[{**STATEMENT, "paper": "other"}])})
        self.fails("from not found", records={"r": row(statements=[{**STATEMENT, "from": "Absent"}])})
        self.fails("to not found", records={"r": row(statements=[{**STATEMENT, "to": "Absent"}])})
        self.fails("from is ambiguous", records={"r": row(statements=[{**STATEMENT, "from": "Repeated", "to": "here."}])})
        self.fails("unbalanced", records={"r": row(statements=[{"paper": "short", "role": "mention",
                                                                 "from": "A $", "to": "lone"}])})
        self.fails("unknown", records={"r": {**row(), "extra": 1}})

    def test_rejects_an_oversized_slice_and_duplicate_records(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)
            body = {"schema_version": "1.0", "records": {"r": row()}}
            (path / "a.json").write_text(json.dumps(body))
            (path / "b.json").write_text(json.dumps(body))
            with self.assertRaisesRegex(ContractError, "already aligned"):
                alignment.resolve_alignment(path, INDEX, PAPERS, {"r"})
        long_paper = {**PAPERS, "short": b"# S\n\nstart " + b"x" * 1800 + b" stop\n"}
        with tempfile.TemporaryDirectory() as directory:
            (Path(directory) / "a.json").write_text(json.dumps({"schema_version": "1.0", "records": {"r": row(
                statements=[{"paper": "short", "role": "mention", "from": "start", "to": "stop"}])}}))
            with self.assertRaisesRegex(ContractError, "characters"):
                alignment.resolve_alignment(directory, INDEX, long_paper, {"r"})

    def test_lenient_mode_leaves_out_only_the_failing_row(self):
        records = {"r": row(lean=[LEAN, {**LEAN, "name": "absent"}]), "bad": row()}
        resolved, errors = resolve(records, strict=False)
        self.assertEqual(len(resolved["records"]["r"]["lean"]), 1)
        self.assertNotIn("bad", resolved["records"])
        self.assertEqual(len(errors), 2)

    def test_dictionary_resolves_fields_through_their_parent(self):
        terms = [{"file": "OAI/M.lean", "name": "val", "parent": "S", "tex": "\\gamma", "words": "A value.",
                  "paper": "long", "from": "Théorème one", "to": "$x=1$."},
                 {"file": "OAI/M.lean", "name": "thing", "words": "No quotation."}]
        rows = resolve(terms=terms)[0]["dictionary"]
        self.assertEqual((rows[0]["name"], rows[0]["line"], rows[0]["anchor"]), ("N.S.val", 7, "first"))
        self.assertIsNone(rows[1]["tex"])
        self.assertNotIn("paper", rows[1])

    def test_heading_ids_follow_the_reader(self):
        self.assertEqual(alignment._pandoc_identifier("2. What a *gap* means!"), "what-a-gap-means")
        self.assertEqual(alignment._pandoc_identifier("123"), "section")
        paper = alignment._Paper(b"# Same\n\n# Same\n")
        self.assertEqual([s["heading_id"] for s in paper.sections], ["same", "same-1"])


class RealFiles(unittest.TestCase):
    def test_authored_alignment_lands_in_the_real_tree_and_papers(self):
        directory = ROOT / "examples/qaoa-sk/alignment"
        if not directory.is_dir():
            self.skipTest("alignment not authored yet")
        report = alignment.check_alignment(directory)
        self.assertGreater(report["records"], 0)
        self.assertEqual(report["records"] + len(report["unaligned_records"]), report["graph_records"])

    def test_command_writes_the_resolved_structure_and_fails_on_a_bad_row(self):
        directory = ROOT / "examples/qaoa-sk/alignment"
        if not directory.is_dir():
            self.skipTest("alignment not authored yet")
        with tempfile.TemporaryDirectory() as scratch:
            out = Path(scratch) / "resolved.json"
            self.assertEqual(main(["check-alignment", str(directory), "--out", str(out)]), 0)
            self.assertIn("records", json.loads(out.read_text()))
            bad = Path(scratch) / "bad"
            bad.mkdir()
            (bad / "x.json").write_text(json.dumps({"schema_version": "1.0", "records": {"absent": row()}}))
            self.assertEqual(main(["check-alignment", str(bad), "--lean-tree", str(ROOT / "examples/qaoa-sk/upstream/lean"),
                                   "--graph", str(ROOT / "examples/qaoa-sk/evidence-graph.json"),
                                   *sum((["--paper", stage, str(path)] for stage, path
                                         in alignment.default_papers(directory).items()), [])]), 1)


if __name__ == "__main__":
    unittest.main()
