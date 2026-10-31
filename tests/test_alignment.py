"""Record alignment: authored pointers against real and adversarial bytes."""
import gzip
import json
import re
import shutil
import tempfile
import unittest
from pathlib import Path

from lean_exposition import alignment
from lean_exposition.cli import main
from lean_exposition.contracts import ContractError

ROOT = Path(__file__).resolve().parents[1]
SOURCE = """namespace N

theorem thing (a : Nat) :
    a = a ∧ a + 0 = a := by
  exact ⟨rfl, rfl⟩ -- a = a

def S.val : Nat := 1
def T.val : Nat := 2
structure Box where
  size : Nat
  deep : Nat
theorem short_proof : 1 = 1 := rfl
"""


def declaration(name, written, kind, line, signature_end, end):
    return {"name": name, "written": written, "kind": kind, "line": line, "signature_end_line": signature_end,
            "end_line": end}


INDEX = {"modules": [
    {"name": "OAI.M", "path": "OAI/M.lean", "source": SOURCE, "declarations": [
        declaration("N.thing", "thing", "theorem", 3, 4, 5),
        declaration("N.S.val", "val", "def", 7, 7, 7),
        declaration("N.T.val", "val", "def", 8, 8, 8),
        declaration("N.Box", "Box", "structure", 9, 9, 11),
        declaration("N.short_proof", "short_proof", "theorem", 12, 12, 12)]},
    {"name": "Challenge.M", "path": "Challenge/M.lean", "source": "theorem again : 2 = 2 := rfl\n", "declarations": [
        declaration("N.short_proof", "short_proof", "theorem", 1, 1, 1)]}]}
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
                                        "relation": "states", "note": "Same claim.", "lines": [3, 4],
                                        "proof_lines": [5, 5]}])
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


class LeanLines(unittest.TestCase):
    def lean(self, **item):
        return resolve({"r": row(lean=[{**LEAN, **item}])})[0]["records"]["r"]["lean"][0]

    def test_a_clause_gives_its_own_lines(self):
        self.assertEqual(self.lean(clause="a = a ∧ a + 0 = a")["lines"], [4, 4])
        self.assertEqual(self.lean(clause="(a : Nat) :\n    a = a")["lines"], [3, 4])

    def test_a_clause_found_in_statement_and_proof_means_the_statement(self):
        self.assertEqual(self.lean(clause="a = a")["lines"], [4, 4])

    def test_a_clause_in_a_definition_keeps_lines_inside_its_own_declaration(self):
        row_ = self.lean(clause="deep : Nat", clause_file="OAI/M.lean", clause_name="Box")
        self.assertEqual((row_["lines"], row_["clause_in"], row_["clause_module"], row_["clause_lines"]),
                         ([3, 4], "N.Box", "OAI.M", [11, 11]))

    def test_a_definition_is_all_statement_and_a_one_line_proof_adds_nothing(self):
        box = self.lean(name="Box")
        self.assertEqual(box["lines"], [9, 11])
        self.assertNotIn("proof_lines", box)
        short = self.lean(name="short_proof")
        self.assertEqual(short["lines"], [12, 12])
        self.assertNotIn("proof_lines", short)

    def test_rejects_a_clause_outside_its_declaration(self):
        with self.assertRaisesRegex(ContractError, "clause is not in N.thing"):
            self.lean(clause="def S.val")

    def test_a_row_without_source_keeps_its_statement_lines(self):
        index = {"modules": [{key: value for key, value in module.items() if key != "source"}
                             for module in INDEX["modules"]]}
        with tempfile.TemporaryDirectory() as directory:
            (Path(directory) / "a.json").write_text(json.dumps({"schema_version": "1.0", "records": {
                "r": row(lean=[{**LEAN, "clause": "not checked"}])}}))
            out = alignment.resolve_alignment(directory, index, PAPERS, {"r"})[0]
        self.assertEqual(out["records"]["r"]["lean"][0]["lines"], [3, 4])


class StatementLean(unittest.TestCase):
    def narrowed(self, *items):
        statement = {**STATEMENT, "lean": list(items)}
        return resolve({"r": row(statements=[statement])})[0]["records"]["r"]["statements"][0]

    def fails(self, pattern, *items):
        with self.assertRaisesRegex(ContractError, pattern):
            self.narrowed(*items)

    def test_a_statement_without_lean_shows_the_records_rows(self):
        out = resolve({"r": row()})[0]["records"]["r"]
        self.assertEqual(out["statements"][0]["lean"], out["lean"])
        self.assertEqual(out["statements"][0]["lean_source"], "record")

    def test_lines_narrow_a_declaration_on_the_record(self):
        out = self.narrowed({"name": "N.thing", "lines": [5, 5], "note": "The proof step."})
        self.assertEqual(out["lean_source"], "statement")
        self.assertEqual(out["lean"], [{"name": "N.thing", "module": "OAI.M", "line": 3, "end_line": 5,
                                        "relation": "states", "note": "The proof step.", "lines": [5, 5],
                                        "proof_lines": [5, 5]}])

    def test_a_clause_narrows_and_a_name_alone_keeps_the_records_row(self):
        self.assertEqual(self.narrowed({"name": "N.thing", "clause": "a + 0 = a"})["lean"][0]["lines"], [4, 4])
        out = self.narrowed({"name": "thing"})["lean"][0]
        self.assertEqual((out["lines"], out["relation"], out["note"]), ([3, 4], "states", "Same claim."))

    def test_a_declaration_off_the_record_has_no_relation_until_given_one(self):
        out = self.narrowed({"name": "N.Box"}, {"name": "N.S.val", "relation": "defines"})["lean"]
        self.assertEqual([(line["name"], line["relation"], line["lines"]) for line in out],
                         [("N.Box", None, [9, 11]), ("N.S.val", "defines", [7, 7])])

    def test_a_restated_name_needs_a_file_unless_the_record_holds_one(self):
        self.fails("short_proof is ambiguous, add file: Challenge/M.lean, OAI/M.lean", {"name": "N.short_proof"})
        out = self.narrowed({"name": "N.short_proof", "file": "Challenge/M.lean"})["lean"][0]
        self.assertEqual((out["module"], out["lines"]), ("Challenge.M", [1, 1]))
        held = {**LEAN, "name": "short_proof"}
        statement = {**STATEMENT, "lean": [{"name": "N.short_proof"}]}
        self.assertEqual(resolve({"r": row(lean=[held], statements=[statement])})[0]["records"]["r"]
                         ["statements"][0]["lean"][0]["module"], "OAI.M")

    def test_lines_settle_a_repeated_clause(self):
        self.assertEqual(self.narrowed({"name": "N.thing", "clause": "a = a", "lines": [5, 5]})["lean"][0]["lines"], [5, 5])

    def test_rejects_each_bad_row_with_a_precise_message(self):
        self.fails("no declaration N.absent in the Lean index", {"name": "N.absent"})
        self.fails(r"no declaration N.thing in the Lean index in Challenge/M.lean",
                   {"name": "N.thing", "file": "Challenge/M.lean"})
        self.fails(r"lines \[2, 4\] lie outside N.thing, which runs from line 3 to 5", {"name": "N.thing", "lines": [2, 4]})
        self.fails(r"lines \[5, 6\] lie outside N.thing", {"name": "N.thing", "lines": [5, 6]})
        self.fails(r"lines must be \[first, last\]", {"name": "N.thing", "lines": [5, 4]})
        self.fails(r"lines must be \[first, last\]", {"name": "N.thing", "lines": [5]})
        self.fails(r"lines must be \[first, last\]", {"name": "N.thing", "lines": [True, 4]})
        self.fails("clause does not land in N.thing: 'absent'", {"name": "N.thing", "clause": "absent"})
        self.fails(r"clause does not land in N.thing within lines \[3, 3\]",
                   {"name": "N.thing", "clause": "a + 0", "lines": [3, 3]})
        self.fails(r"clause is ambiguous in N.Box, on lines \[\[10, 10\], \[11, 11\]\]; add lines",
                   {"name": "N.Box", "clause": "Nat"})
        self.fails("clause must be nonempty text", {"name": "N.thing", "clause": ""})
        self.fails("note must be text", {"name": "N.thing", "note": "word " * 26})
        self.fails("unknown relation", {"name": "N.thing", "relation": "proves"})
        self.fails("unknown", {"name": "N.thing", "extra": 1})
        with self.assertRaisesRegex(ContractError, r"lean: must be a list; \[\] says"):
            resolve({"r": row(statements=[{**STATEMENT, "lean": "none"}])})

    def test_an_empty_list_says_there_is_no_lean_and_never_falls_back(self):
        out = self.narrowed()
        self.assertEqual((out["lean"], out["lean_source"]), ([], "statement"))
        record = {"statements": [out]}
        tie = alignment.tie_index(LONG, {"r": record}, "long")["ties"][0]
        self.assertEqual((tie["lean"], tie["from_record"], tie["name"], tie["lines"]), (False, False, None, None))

    def test_a_failed_list_is_not_a_claim_of_no_lean(self):
        out = resolve({"r": row(statements=[{**STATEMENT, "lean": [{"name": "N.absent"}]}])}, strict=False)
        self.assertEqual(out[0]["records"]["r"]["statements"][0]["lean_source"], "record")

    def test_a_clause_needs_source_to_land(self):
        index = {"modules": [{key: value for key, value in INDEX["modules"][0].items() if key != "source"}]}
        with tempfile.TemporaryDirectory() as directory:
            (Path(directory) / "a.json").write_text(json.dumps({"schema_version": "1.0", "records": {"r": row(
                statements=[{**STATEMENT, "lean": [{"name": "N.thing", "clause": "a"}]}])}}))
            with self.assertRaisesRegex(ContractError, "index has no source for OAI.M"):
                alignment.resolve_alignment(directory, index, PAPERS, {"r"})

    def test_lenient_mode_drops_only_the_failing_row(self):
        statement = {**STATEMENT, "lean": [{"name": "N.absent"}, {"name": "N.Box"}]}
        resolved, errors = resolve({"r": row(statements=[statement])}, strict=False)
        self.assertEqual([line["name"] for line in resolved["records"]["r"]["statements"][0]["lean"]], ["N.Box"])
        self.assertEqual(len(errors), 1)
        statement = {**STATEMENT, "lean": [{"name": "N.absent"}]}
        out = resolve({"r": row(statements=[statement])}, strict=False)[0]["records"]["r"]["statements"][0]
        self.assertEqual((out["lean_source"], out["lean"][0]["name"]), ("record", "N.thing"))


class TiesFiles(unittest.TestCase):
    TIE = {"record": "r", "paper": "long", "role": "explanation", "from": "Unique end", "to": "tail."}

    def tied(self, statements, name="ties-long.json", schema=1, strict=True, records=None):
        return resolve(records or {"r": row()}, extra={name: json.dumps({"schema": schema, "statements": statements})},
                       strict=strict)

    def fails(self, pattern, *arguments, **options):
        with self.assertRaisesRegex(ContractError, pattern):
            self.tied(*arguments, **options)

    def test_statements_join_the_record_after_its_batch_rows(self):
        lean = [{"name": "N.thing", "lines": [5, 5]}]
        rows = self.tied([{**self.TIE, "lean": lean, "note": "Close reading."}])[0]["records"]["r"]["statements"]
        self.assertEqual([slice_["role"] for slice_ in rows], ["statement", "explanation"])
        self.assertEqual((rows[1]["markdown"], rows[1]["note"]), ("Unique end $$y$$ tail.", "Close reading."))
        self.assertEqual(rows[1]["lean"][0]["lines"], [5, 5])
        self.assertEqual(rows[1]["section"], "Part")

    def test_a_tie_without_lean_uses_the_records_rows(self):
        rows = self.tied([self.TIE])[0]["records"]["r"]["statements"]
        self.assertEqual((rows[1]["lean_source"], rows[1]["lean"][0]["name"]), ("record", "N.thing"))

    def test_a_tie_can_say_it_has_no_lean_even_over_a_batch_row(self):
        tie = {**STATEMENT, "record": "r", "lean": []}
        rows = self.tied([tie])[0]["records"]["r"]["statements"]
        self.assertEqual((len(rows), rows[0]["lean"], rows[0]["lean_source"]), (1, [], "statement"))

    def test_the_same_slice_as_a_batch_row_narrows_it_in_place(self):
        tie = {**STATEMENT, "record": "r", "lean": [{"name": "N.thing", "lines": [5, 5]}]}
        rows = self.tied([tie])[0]["records"]["r"]["statements"]
        self.assertEqual(len(rows), 1)
        self.assertEqual(rows[0]["lean"][0]["lines"], [5, 5])

    def test_rejects_each_broken_tie(self):
        self.fails("absent is not an aligned record", [{**self.TIE, "record": "absent"}])
        self.fails(r"s is not an aligned record", [{**self.TIE, "record": "s"}])
        self.fails("from not found", [{**self.TIE, "from": "Absent"}])
        self.fails("to not found", [{**self.TIE, "to": "Absent"}])
        self.fails("unknown role", [{**self.TIE, "role": "aside"}])
        self.fails("paper short in a file for long", [{**self.TIE, "paper": "short"}])
        self.fails("other is not a paper", [self.TIE], name="ties-other.json")
        self.fails("expected schema 1", [self.TIE], schema=2)
        self.fails("already tied", [self.TIE, self.TIE])
        self.fails(r"statements\[0\]: missing \['record'\]", [{k: v for k, v in self.TIE.items() if k != "record"}])
        self.fails(r"statements\[0\].lean\[0\]: no declaration", [{**self.TIE, "lean": [{"name": "N.absent"}]}])

    def test_broken_json_is_an_error_and_lenient_mode_keeps_the_rest(self):
        with self.assertRaisesRegex(ContractError, "ties-long.json: not valid JSON"):
            resolve({"r": row()}, extra={"ties-long.json": "{"})
        resolved, errors = self.tied([self.TIE, {**self.TIE, "from": "Absent"}], strict=False)
        self.assertEqual((len(resolved["records"]["r"]["statements"]), len(errors)), (2, 1))

    def test_other_companions_stay_outside(self):
        resolved, errors = resolve({"r": row()}, extra={"main-theorem.json": '{"schema_version": "1.0", "pairs": []}'})
        self.assertEqual(errors, [])
        self.assertEqual(len(resolved["records"]["r"]["statements"]), 1)


def statement(markdown_bytes, start, end, *, role="statement", lean=True, anchor=None):
    return {"paper": "long", "role": role, "start_byte": start, "end_byte": end, "at": f"b{start}-{end}", "anchor": anchor,
            "lean": [{"name": "N.thing", "module": "OAI.M", "lines": [3, 4]}] if lean else [], "lean_source": "record"}


class TieIndex(unittest.TestCase):
    def ties(self, paper, *quotes, passages=()):
        """Each quote is `(record, text)` or `(record, text, options)`; returns segments as text."""
        content = paper.encode()
        records = {}
        for record, text, *options in quotes:
            start = content.index(text.encode())
            records.setdefault(record, {"statements": []})["statements"].append(
                statement(content, start, start + len(text.encode()), **(options[0] if options else {})))
        index = alignment.tie_index(content, records, "long", passages)
        return index, [(content[a:b].decode(), [index["ties"][n]["record"] for n in members])
                       for a, b, members in index["segments"]]

    def test_a_slice_is_cut_at_each_block_and_keeps_one_address(self):
        index, segments = self.ties("One.\n\nTwo words.\n", ("r", "One.\n\nTwo words."))
        self.assertEqual(segments, [("One.", ["r"]), ("Two words.", ["r"])])
        self.assertEqual({tie["at"] for tie in index["ties"]}, {"b0-16"})

    def test_passage_markers_and_headings_are_block_edges_and_are_not_marked(self):
        paper = "Alpha.\n<!-- passage:x -->\nBeta.\n## Head\nGamma.\n"
        self.assertEqual(self.ties(paper, ("r", paper.strip()))[1],
                         [("Alpha.", ["r"]), ("Beta.", ["r"]), ("## Head", ["r"]), ("Gamma.", ["r"])])

    def test_ends_inside_inline_math_move_out_to_its_edge(self):
        paper = "See $x+y$ and $z$ now.\n"
        self.assertEqual(self.ties(paper, ("r", "+y$ and $z"))[1], [("$x+y$ and $z$", ["r"])])

    def test_a_display_is_tied_whole_and_alone(self):
        paper = "Before\n$$\na=1\n\nb=2\n$$\nafter.\n"
        self.assertEqual(self.ties(paper, ("r", "a=1"))[1], [("$$\na=1\n\nb=2\n$$", ["r"])])
        self.assertEqual(self.ties(paper, ("r", "Before\n$$\na=1\n\nb=2\n$$\nafter."))[1],
                         [("Before", ["r"]), ("$$\na=1\n\nb=2\n$$", ["r"]), ("after.", ["r"])])

    def test_escaped_dollars_and_code_are_not_math(self):
        spans = alignment._math_spans("cost \\$5 and `$x$` then $y$ and 3$ and $ z$ and $w$2.\n")
        self.assertEqual(len(spans), 1)
        self.assertEqual(spans[0][1] - spans[0][0], 3)

    def test_math_is_found_as_the_reader_finds_it(self):
        text = "a $b$ c $$d$$ e\n\n```\n$no$\n```\n$open\n\nclose$\n"
        self.assertEqual([text[a:b] for a, b, _ in alignment._math_spans(text)], ["$b$", "$$d$$"])

    def test_two_records_share_the_text_they_both_cover(self):
        paper = "Alpha beta gamma.\n"
        _, segments = self.ties(paper, ("a", "Alpha beta"), ("b", "beta gamma."))
        self.assertEqual(segments, [("Alpha", ["a"]), ("beta", ["a", "b"]), ("gamma.", ["b"])])

    def test_a_segment_lists_lean_first_then_the_narrowest(self):
        paper = "Alpha beta gamma delta.\n"
        index, segments = self.ties(paper, ("wide", paper.strip()), ("narrow", "beta"),
                                    ("bare", "beta gamma", {"lean": False}))
        self.assertEqual(dict(segments)["beta"], ["narrow", "wide", "bare"])
        self.assertFalse(next(tie for tie in index["ties"] if tie["record"] == "bare")["lean"])

    def test_byte_offsets_survive_multibyte_text(self):
        paper = "Café $é$ thé.\n"
        index, segments = self.ties(paper, ("r", "thé."))
        self.assertEqual(segments, [("thé.", ["r"])])
        self.assertEqual(index["segments"][0][:2], [len("Café $é$ ".encode()), len(paper.strip().encode())])

    def test_a_tie_offers_the_first_row_or_the_clause_it_found_elsewhere(self):
        row_ = {**statement(b"", 0, 1), "lean": [{"name": "A", "module": "M", "lines": [1, 2], "clause": "c",
                                                  "clause_in": "B", "clause_module": "N", "clause_lines": [8, 9]}]}
        tie = alignment._tie("r", row_)
        self.assertEqual((tie["name"], tie["module"], tie["lines"]), ("B", "N", [8, 9]))
        tie = alignment._tie("r", {**statement(b"", 0, 1), "lean": []})
        self.assertEqual((tie["lean"], tie["name"], tie["module"], tie["lines"]), (False, None, None, None))

    def test_a_tie_without_lean_keeps_the_shape(self):
        index, _ = self.ties("Alpha.\n", ("r", "Alpha.", {"lean": False, "role": "mention", "anchor": "p"}))
        self.assertEqual(index["ties"], [{"record": "r", "role": "mention", "lean": False, "from_record": False,
                                          "name": None, "module": None, "lines": None, "anchor": "p", "at": "b0-6"}])

    def test_a_tie_says_when_its_lean_is_the_records(self):
        fallback = alignment._tie("r", statement(b"", 0, 1))
        own = alignment._tie("r", {**statement(b"", 0, 1), "lean_source": "statement"})
        self.assertEqual((fallback["from_record"], own["from_record"]), (True, False))

    def test_passages_fall_back_with_their_records_and_any_slice_inside(self):
        paper = "Alpha.\n\nBeta.\n"
        index, _ = self.ties(paper, ("slice", "Alpha.", {"anchor": "p"}),
                             passages=[(8, 13, [], "empty"), (0, 6, ["claim"], "p")])
        self.assertEqual(index["passages"], [[0, 6, ["claim", "slice"], "p"]])

    def test_a_paper_with_no_slices_is_empty_and_only_its_stage_is_read(self):
        self.assertEqual(alignment.tie_index(b"Alpha.\n", {}, "short")["segments"], [])
        records = {"r": {"statements": [statement(b"", 0, 6)]}}
        self.assertEqual(alignment.tie_index(b"Alpha.\n", records, "short")["ties"], [])


class RealFiles(unittest.TestCase):
    def test_the_documented_ties_file_lands_in_the_real_tree_and_papers(self):
        guide = (ROOT / "docs/record-alignment.md").read_text(encoding="utf-8")
        example = json.loads(re.search(r"`ties-short\.json`[^\n]*:\n\n```json\n(.*?)```", guide, re.S).group(1))
        with tempfile.TemporaryDirectory() as scratch:
            directory = Path(scratch) / "examples/qaoa-sk/alignment"
            shutil.copytree(ROOT / "examples/qaoa-sk/alignment", directory)
            (directory / "ties-short.json").write_text(json.dumps(example))
            out = Path(scratch) / "resolved.json"
            papers = alignment.default_papers(ROOT / "examples/qaoa-sk/alignment")
            alignment.check_alignment(directory, lean_tree=ROOT / "examples/qaoa-sk/upstream/lean",
                                      graph=ROOT / "examples/qaoa-sk/evidence-graph.json", papers=papers, out=out)
            resolved = json.loads(out.read_text())
        # The example replaces ties-short.json in this copy; other papers keep their own ties.
        rows = [row_ for row_ in resolved["records"][example["statements"][0]["record"]]["statements"]
                if row_["lean_source"] == "statement" and row_["paper"] == "short"]
        self.assertEqual(len(rows), len(example["statements"]))
        self.assertTrue(all(lean["lines"] for row_ in rows for lean in row_["lean"]))

    def test_tie_index_holds_its_promises_on_the_real_papers(self):
        directory = ROOT / "examples/qaoa-sk/alignment"
        if not directory.is_dir():
            self.skipTest("alignment not authored yet")
        out = Path(tempfile.mkdtemp()) / "resolved.json"
        self.addCleanup(shutil.rmtree, out.parent)
        alignment.check_alignment(directory, out=out)
        records = json.loads(out.read_text())["records"]
        for stage, path in alignment.default_papers(directory).items():
            with self.subTest(stage=stage):
                content = path.read_bytes()
                index = alignment.tie_index(content, records, stage)
                encoded = json.dumps(index, ensure_ascii=False, separators=(",", ":")).encode()
                self.assertLess(len(encoded), 250_000)
                self.assertLess(len(gzip.compress(encoded)), 40_000)
                math = [(len(content.decode()[:a].encode()), len(content.decode()[:b].encode()))
                        for a, b, _ in alignment._math_spans(content.decode())]
                covered, previous = bytearray(len(content)), 0
                for start, end, members in index["segments"]:
                    self.assertLessEqual(previous, start)
                    self.assertTrue(members)
                    previous = end
                    covered[start:end] = b"\1" * (end - start)
                    body = content[start:end].decode()
                    self.assertEqual(body, body.strip())
                    self.assertNotIn("<!--", body)
                    if not body.startswith("$$"):
                        self.assertIsNone(re.search(r"\n[ \t]*\n", body))
                    self.assertFalse([span for span in math if span[0] < start < span[1] or span[0] < end < span[1]])
                for tie in index["ties"]:
                    start, end = map(int, tie["at"][1:].split("-"))
                    left = bytes(c for c, hit in zip(content[start:end], covered[start:end]) if not hit).decode()
                    self.assertEqual("".join(re.sub(r"<!--.*?-->", "", left, flags=re.S).split()), "")
                    if tie["lean"]:
                        self.assertLessEqual(tie["lines"][0], tie["lines"][1])

    def test_every_real_lean_row_has_lines_inside_its_declaration(self):
        directory = ROOT / "examples/qaoa-sk/alignment"
        if not directory.is_dir():
            self.skipTest("alignment not authored yet")
        out = Path(tempfile.mkdtemp()) / "resolved.json"
        self.addCleanup(shutil.rmtree, out.parent)
        alignment.check_alignment(directory, out=out)
        for record in json.loads(out.read_text())["records"].values():
            for row_ in record["lean"]:
                self.assertLessEqual(row_["line"], row_["lines"][0])
                self.assertLessEqual(row_["lines"][1], row_["end_line"])
                self.assertEqual("proof_lines" in row_ and row_["proof_lines"][1], "proof_lines" in row_ and row_["end_line"])

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


class PlainNames(unittest.TestCase):
    NAMES = {"N.thing": "A plain title", "N.Box": "The box"}

    def named(self, names=None, schema=1, strict=True, statements=(STATEMENT,)):
        body = json.dumps({"schema": schema, "names": self.NAMES if names is None else names})
        return resolve({"r": row(statements=statements)}, extra={"names.json": body}, strict=strict)

    def test_titles_reach_the_map_the_rows_and_the_ties(self):
        statements = [STATEMENT, {**STATEMENT, "from": "Unique end", "to": "tail.", "lean": [{"name": "N.Box"}]}]
        resolved = self.named(statements=statements)[0]
        self.assertEqual(resolved["names"], {"N.Box": "The box", "N.thing": "A plain title"})
        record = resolved["records"]["r"]
        self.assertEqual(record["lean"][0]["plain"], "A plain title")
        self.assertEqual([item["lean"][0]["plain"] for item in record["statements"]], ["A plain title", "The box"])
        ties = alignment.tie_index(LONG, resolved["records"], "long", names=resolved["names"])["ties"]
        self.assertEqual([tie["plain"] for tie in ties], ["A plain title", "The box"])

    def test_a_title_is_left_off_where_none_exists_and_the_file_may_be_absent(self):
        resolved = self.named({"N.Box": "The box"})[0]
        self.assertNotIn("plain", resolved["records"]["r"]["lean"][0])
        self.assertNotIn("plain", alignment.tie_index(LONG, resolved["records"], "long", names=resolved["names"])["ties"][0])
        absent = resolve({"r": row()})[0]
        self.assertEqual(absent["names"], {})
        self.assertNotIn("plain", absent["records"]["r"]["lean"][0])

    def test_a_tie_takes_the_title_of_the_declaration_it_names(self):
        row_ = {**statement(b"", 0, 1), "lean": [{"name": "A", "module": "M", "lines": [1, 2], "clause_in": "B",
                                                  "clause_module": "N", "clause_lines": [8, 9], "plain": "Of A"}]}
        self.assertEqual(alignment._tie("r", row_, {"A": "Of A", "B": "Of B"})["plain"], "Of B")

    def test_rejects_what_cannot_be_a_title(self):
        for pattern, names, schema in (("N.absent: not a declaration in the Lean index", {"N.absent": "Two words"}, 1),
                                       ("thing: not a declaration", {"thing": "Two words"}, 1),
                                       ("title has 1 words", {"N.thing": "One"}, 1),
                                       ("title has 7 words", {"N.thing": "one two three four five six seven"}, 1),
                                       ("title has 0 words", {"N.thing": 3}, 1),
                                       ("expected schema 1", {}, 2)):
            with self.assertRaisesRegex(ContractError, pattern):
                self.named(names, schema)
        with self.assertRaisesRegex(ContractError, "names.json: not valid JSON"):
            resolve({"r": row()}, extra={"names.json": "{"})

    def test_lenient_mode_leaves_out_only_the_bad_title(self):
        resolved, errors = self.named({"N.absent": "Two words", "N.Box": "The box"}, strict=False)
        self.assertEqual((resolved["names"], len(errors)), ({"N.Box": "The box"}, 1))


class LeanStepTests(unittest.TestCase):
    INDEX = {"modules": [
        {"name": "OAI.A", "declarations": [
            {"name": "top", "uses": ["middle"]}, {"name": "middle", "uses": ["leaf"]}, {"name": "leaf", "uses": []},
            {"name": "alone", "uses": []}]},
        {"name": "Challenge", "declarations": [{"name": "top", "uses": []}]}]}
    ALIGNMENT = {"records": {
        "consumer": {"lean": [{"name": "top", "relation": "states"}]},
        "used": {"lean": [{"name": "leaf", "relation": "part"}]},
        "unreached": {"lean": [{"name": "alone", "relation": "states"}]},
        "only_defined": {"lean": [{"name": "top", "relation": "defines"}]},
        "no_lean": {"lean": []}}}

    def steps(self, *edges):
        rows = [{"from": a, "to": b, "kind": "supports"} for a, b in edges]
        return alignment.lean_steps(self.ALIGNMENT, self.INDEX, rows)

    def test_a_step_follows_names_through_the_source(self):
        step = self.steps(("consumer", "used"))["consumer→used→supports"]
        self.assertEqual(step["route"], ["top", "middle", "leaf"])

    def test_a_name_restated_elsewhere_keeps_its_proof_references(self):
        index = {"modules": list(reversed(self.INDEX["modules"]))}
        steps = alignment.lean_steps(self.ALIGNMENT, index, [{"from": "consumer", "to": "used", "kind": "supports"}])
        self.assertEqual(steps["consumer→used→supports"]["route"], ["top", "middle", "leaf"])

    def test_no_chain_is_reported_and_no_lean_is_left_out(self):
        steps = self.steps(("consumer", "unreached"), ("consumer", "no_lean"), ("only_defined", "used"))
        self.assertEqual(steps, {"consumer→unreached→supports": {"route": None}})

    def test_shared_declaration_is_a_route_of_one(self):
        alignment_ = {"records": {"a": {"lean": [{"name": "top", "relation": "contains"}]},
                                  "b": {"lean": [{"name": "top", "relation": "part"}]}}}
        steps = alignment.lean_steps(alignment_, self.INDEX, [{"from": "a", "to": "b", "kind": "supports"}])
        self.assertEqual(steps["a→b→supports"]["route"], ["top"])


if __name__ == "__main__":
    unittest.main()
