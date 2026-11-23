"""Regression checks for pointers into printed and compiled RH source."""

from importlib.util import find_spec
from pathlib import Path
import sqlite3
import sys
from types import SimpleNamespace
import unittest
from unittest.mock import patch


ROOT = Path(__file__).resolve().parents[1]
PDF_DEPENDENCIES = all(find_spec(module) is not None for module in ("numpy", "pyarrow", "pypdf", "scipy"))


@unittest.skipUnless(PDF_DEPENDENCIES, "RH paper build dependencies unavailable")
class RHPaperPointers(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        with patch.object(sys, "path", [str(ROOT / "scripts"), *sys.path]):
            import build_rh_paper

        cls.builder = build_rh_paper

    def test_reader_note_preserves_original_source(self):
        source = {"title": "Coefficient bound", "markdown": "**[L1]** Source wording.",
                  "reading_note": "The coefficient bound applies on each selected window."}
        projected = self.builder.reader_notes({"Deduction.bound": [source]})
        self.assertEqual(projected["Deduction.bound"]["text"], source["reading_note"])
        self.assertEqual(source["markdown"], "**[L1]** Source wording.")

    def test_tex_subscript_is_part_of_declaration_name(self):
        with patch.object(self.builder, "blob", side_effect=[
            r"\input{sections/lattices}".encode(),
            r"\section{Lattices} (\lean{SizeData}\textsubscript{\ttfamily 2})".encode(),
        ]):
            [ref] = self.builder.source_references(ROOT, "fixture")
        self.assertEqual(ref["name"], "SizeData₂")

    def test_numbered_subsections_keep_their_paper_titles(self):
        with patch.object(self.builder, "blob", side_effect=[
            br"\input{sections/intro}\input{sections/results}",
            b"\\section{Introduction}\n\\subsection{The argument}\\label{sec:arg}",
            b"\\section{Results}\n\\subsection*{Notation}\n\\subsection{The exponent $\\tfrac12$}",
        ]):
            titles = self.builder.subsection_titles(ROOT, "fixture")
        self.assertEqual(titles, {"1.1": "1.1 The argument", "2.1": "2.1 The exponent ½"})

    def test_pdf_pointer_covers_wrapped_name_only(self):
        tokens = ["Bessel", "models", "(rowMainEqP_of_", "siegelWeil)."]
        words = [{"text": token, "page": 21} for token in tokens]
        entry = {"tokens": tokens, "page": 21, "span": [2, 4]}
        self.assertEqual(self.builder.reviewed_pdf_location(words, entry, "rowMainEqP_of_siegelWeil"),
                         (2, 4))
        with self.assertRaises(ValueError):
            self.builder.reviewed_pdf_location(words, entry, "rowMainEqP_of")
        with self.assertRaises(ValueError):
            self.builder.reviewed_pdf_location(words + words, entry, "rowMainEqP_of_siegelWeil")

    def test_line_lookup_prefers_statement_and_keeps_proof_span(self):
        decl = {"name": "Foo.lemma", "module": "Foo", "lines": [2, 10], "statement_lines": [2, 4]}
        passages = {
            "proof": {"role": "derivation", "topic": "analytic", "lean": [{**decl, "focus_lines": [7, 9]}]},
            "claim": {"role": "statement", "topic": "analytic", "lean": [decl]},
        }
        marks = {"proof": {"at": "b1-3", "boxes": [[1]]}, "claim": {"at": "b4-8", "boxes": [[1]]}}
        bindings = {"Foo.lemma": {"source": decl, "passages": ["proof", "claim"], "references": []}}
        notes = {"Foo.lemma": [{"url": "external"}, {"lean_lines": [8, 8]}]}
        [row] = self.builder.reading_line_index(passages, {}, marks, bindings, notes)["Foo"]
        self.assertEqual(row["canonical"], "claim")
        self.assertEqual([link["lines"] for link in row["links"]], [[2, 4], [7, 9]])
        self.assertEqual(row["links"][1]["precision"], "reviewed_span")
        self.assertEqual(row["notes"], [{"index": 1, "lines": [8, 8]}])

    def test_archive_checks_join_successful_reports_by_name(self):
        config = {"repository": "https://example.test/paper", "revision": "pinned"}
        names = [f"theorem{n}" for n in range(5)]
        targets = {name: {"module": "Main", "kind": "theorem"} for name in names}
        printed = "\n".join(f"'{name}' depends on axioms: [{name}.axiom, propext]" for name in names)
        replayed = "\n".join(f"{name}: a theorem, checked by the kernel; it depends on 250 constants; "
                             f"axioms: [propext, {name}.axiom]" for name in reversed(names))
        with patch.object(self.builder, "repository_file",
                          side_effect=[f"{printed}\nCHECK-EXIT 0\n".encode(), replayed.encode(), b"exit code 0\n"]):
            rows = self.builder.archive_checks(ROOT, config, targets)
        self.assertEqual(rows[names[0]]["axioms"], [f"{names[0]}.axiom", "propext"])
        self.assertTrue(rows[names[0]]["print_href"].endswith("check.txt#L1"))
        self.assertTrue(rows[names[0]]["replay_href"].endswith("replay-targets.txt#L5"))
        with patch.object(self.builder, "repository_file",
                          side_effect=[f"{printed}\nCHECK-EXIT 0\n".encode(), replayed.encode(), b"exit code 1\n"]):
            with self.assertRaisesRegex(ValueError, "do not record successful runs"):
                self.builder.archive_checks(ROOT, config, targets)

    def test_graph_axioms_follow_dependencies_and_preserve_missing_names(self):
        import numpy as np

        db = sqlite3.connect(":memory:")
        self.addCleanup(db.close)
        db.execute("CREATE TABLE node (id, name, kind)")
        db.executemany("INSERT INTO node VALUES (?, ?, ?)", [
            (0, "choice", "axiom"), (1, "middle", "def"), (2, "uses_choice", "theorem"), (3, "plain", "theorem"),
        ])
        proof = SimpleNamespace(
            offsets={"in": np.array([0, 1, 2, 2, 2], dtype=np.int32)},
            edges={"in": np.array([(1 << 3) | 1, (2 << 3) | 4], dtype=np.uint32)},
            manifest={"dataset": "https://example.test/data"},
        )
        rows = self.builder.graph_axioms(proof, db, ["uses_choice", "plain", "unindexed"])
        self.assertEqual(rows["uses_choice"], {"axioms": ["choice"], "href": "https://example.test/data"})
        self.assertEqual(rows["plain"]["axioms"], [])
        self.assertNotIn("unindexed", rows)
