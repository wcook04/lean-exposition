from pathlib import Path
from tempfile import TemporaryDirectory
import json
import unittest
from unittest.mock import patch

from scripts.build_paper_references import (
    Point,
    Reference,
    aligned_points,
    build,
    choose_references,
    destination_blocks,
    destination_tone,
    locate_reference,
    pdf_references,
    reader_pdf,
    source_references,
    topic_ranges,
)


class PaperReferencesTest(unittest.TestCase):
    def test_source_targets_only_include_written_destinations(self):
        source = "\n".join([
            "# A title",
            "## 1. An introduction",
            "### 1.1 A subsection",
            "**Theorem 1.1.** The statement begins.",
            "We apply Theorem 9.1 in the analysis.",
            "**Lemma A.2 (bounds).** A second statement.",
            "Figure S11: The circuit.",
            "*Table 3.* A real caption.",
            "Table 8 of ref. 22 contains the value.",
            "## Appendix A. A continuation",
            "### A.1 An appendix subsection",
            r"`$$ x \tag{91} $$`",
            r"A command \tag{92} in prose.",
            "$$",
            r"x = \theta \tag{1.2}",
            "$$",
            "<!--",
            "**Theorem 7.** A commented label.",
            "-->",
            "```md",
            "<!--",
            "## 8. An example of syntax",
            r"$$ x \tag{8} $$",
            "```",
            "**Remark 2.** A visible label after the code.",
            "    **Theorem 8.** Indented code.",
        ])
        refs = choose_references(source_references(source), {}, False)
        self.assertEqual(
            {key: ref.line for key, ref in refs.items()},
            {"section:1": 2, "section:1.1": 3, "theorem:1.1": 4, "lemma:a.2": 6,
             "figure:s11": 7, "table:3": 8, "section:a": 10, "appendix:a": 10, "section:a.1": 11, "appendix:a.1": 11,
             "equation:1.2": 15, "remark:2": 25},
        )
        at = refs["equation:1.2"]
        self.assertEqual(source.encode()[at.start:at.end].decode(), r"\tag{1.2}")

    def test_duplicate_labels_require_a_unique_canonical_binding(self):
        source = "**Theorem 1.** First.\n\n## Auxiliary note. A second article\n\n**Theorem 1.** Second."
        refs = source_references(source)
        self.assertEqual(choose_references(refs, {}, True), {"theorem:m.1": refs["theorem:1"][0]})
        chosen = choose_references(refs, {"canonical": {"paper.theorem-1": [0, 0, 13]}}, True)
        self.assertEqual(chosen["theorem:1"].line, 1)
        self.assertEqual(chosen["theorem:m.1"].line, 1)

    def test_printed_sections_and_equations_require_destination_evidence(self):
        output = """<page width="612" height="792">
        <line yMin="42"><word xMin="55" xMax="75">1.</word>
          <word xMin="90" xMax="140">Introduction</word></line>
        <line yMin="133"><word xMin="250" xMax="260">1.</word>
          <word xMin="265" xMax="315">Introduction</word></line>
        <line yMin="187"><word xMin="72" xMax="84">See</word>
          <word xMin="88" xMax="113">(1.2)</word></line>
        <line yMin="320"><word xMin="510" xMax="540">(1.2)</word></line>
        <line yMin="343"><word xMin="510" xMax="540">(1.4)</word></line>
        <line yMin="390"><word xMin="510" xMax="540">(1.4)</word></line>
        </page>"""
        with patch("scripts.build_paper_references.subprocess.run") as poppler:
            poppler.return_value.stdout = output
            pages, printed = pdf_references(Path("paper.pdf"))
        self.assertEqual(pages, [(612, 792)])
        ref = Reference(1, 0, 15, ("introduction",))
        self.assertIsNone(locate_reference("section:1", ref, printed["section:1"], None))
        self.assertEqual(locate_reference("section:1", ref, printed["section:1"], Point(1, 134)), Point(1, 133))
        self.assertEqual(locate_reference("equation:1.2", ref, printed["equation:1.2"], None), Point(1, 320))
        self.assertIsNone(locate_reference("equation:1.4", ref, printed["equation:1.4"], None))

    def test_fallback_requires_edition_ties_and_matching_page_geometry(self):
        points = [[3, 1, 30], [15, 2, 100]]
        marks = {"pages": [[600, 800], [600, 800]], "marks": {"tie": {"at": "b0-26"}}, "positions": points}
        ties = {"ties": [{"phrase": "tie", "at": "b0-26"}]}
        sizes = [(600, 800), (600, 800)]
        self.assertEqual(aligned_points(marks, ties, sizes, 26), {3: Point(1, 30), 15: Point(2, 100)})
        self.assertEqual(aligned_points(marks, {}, sizes, 26), {})
        self.assertEqual(aligned_points(marks, ties, [(600, 810)] * 2, 26), {})
        self.assertEqual(aligned_points({**marks, "positions": [[15, 2, 100], [3, 1, 30]]}, ties, sizes, 26), {})

    def test_destination_topic_uses_exact_bytes_then_the_smallest_published_block(self):
        ties = {
            "topics": [
                {"id": "analysis", "tone": 0, "light": "#123", "dark": "#abc"},
                {"id": "model", "tone": 3, "light": "#456", "dark": "#def"},
            ],
            "ties": [
                {"topic": "analysis", "tone": 0, "at": "b10-20"},
                {"topic": "model", "tone": 3, "at": "b28-39"},
                {"topic": "analysis", "tone": 3, "at": "b60-65"},
            ],
        }
        structure = {"paper": {
            "byte_length": 90,
            "passages": [{"content_span": {"start_byte": 20, "end_byte": 40}}],
            "sections": [{"span": {"start_byte": 0, "end_byte": 55}}],
        }}
        topics = topic_ranges(ties, 90)
        blocks = destination_blocks(ties, structure, 90)
        self.assertEqual(destination_tone(Reference(1, 11, 15), topics, blocks), 0)
        self.assertEqual(destination_tone(Reference(2, 21, 25), topics, blocks), 3)
        self.assertIsNone(destination_tone(Reference(3, 15, 32), topics, blocks))
        self.assertIsNone(destination_tone(Reference(4, 44, 50), topics, blocks))
        self.assertIsNone(destination_tone(Reference(5, 61, 62), topics, blocks))
        self.assertIsNone(destination_tone(Reference(6, 70, 75), topics, blocks))
        self.assertEqual(destination_blocks(ties, structure, 89), [])

    def test_build_processes_the_exact_companion_and_reader_pdf(self):
        with TemporaryDirectory() as tmp:
            dist = Path(tmp)
            edition = dist / "edition"
            docs = edition / "docs" / "adapted"
            docs.mkdir(parents=True)
            (dist / "pdf").mkdir()
            (dist / "pdf/reading.pdf").touch()
            (dist / "pdf/marked.pdf").touch()
            (edition / "index.json").write_text(json.dumps({
                "documents": {"short": "main.md"}, "responses": {"/ties/short": "main-ties.json"},
            }))
            (edition / "main-ties.json").write_text(json.dumps({
                "topics": [{"id": "analysis", "tone": 0, "light": "#123", "dark": "#abc"}],
                "ties": [{"topic": "analysis", "tone": 0, "at": "b19-40"}],
            }))
            (edition / "main.md").write_text("## 1 Introduction\n\n**Theorem 1.** Original.\n")
            (docs / "index.json").write_text(json.dumps({
                "documents": {"short": "docs/adapted/document.md"}, "responses": {},
            }))
            (docs / "document.md").write_text("## 1 Introduction\n\nEdited.\n\n**Theorem 1.** Revised.\n")
            instance = {"documents": [{"slot": "adapted", "adapted": True,
                                       "reading_pdf": {"name": "reading.pdf"}, "pdf": {"name": "marked.pdf"}}]}
            with patch("scripts.build_paper_references.pdf_references", return_value=([], {})) as inspect_pdf:
                output = dist / "paper-references"
                build(dist, output, instance)
                inspect_pdf.assert_called_once_with(dist / "pdf/reading.pdf")
            self.assertEqual(reader_pdf(dist, "adapted", instance), dist / "pdf/reading.pdf")
            main = json.loads((output / "short.json").read_text())
            adapted = json.loads((output / "adapted.json").read_text())
            self.assertEqual(main["schema"], "paper-references/1")
            self.assertEqual(main["targets"]["theorem:1"], {"line": 3, "tone": 0})
            self.assertEqual(adapted["targets"]["theorem:1"], {"line": 5})


if __name__ == "__main__":
    unittest.main()
