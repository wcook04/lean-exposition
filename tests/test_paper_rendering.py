"""Optional Pandoc checks for bookmarks in the maintained reading copies."""
import re
import shutil
import subprocess
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
FILTER = ROOT / "scripts/paper_anchors.lua"


@unittest.skipUnless(shutil.which("pandoc"), "Pandoc is optional paper tooling")
class PaperRenderingTests(unittest.TestCase):
    def test_authored_html_bookmarks_survive_latex_conversion(self):
        paths = [ROOT / "papers/qaoa-sk/long/reasoning-record.md",
                 ROOT / "papers/qaoa-sk/short/paper.md"]
        for path in paths:
            with self.subTest(paper=path.name):
                source = path.read_text()
                anchors = re.findall(r'<a id="([^"]+)"></a>', source)
                self.assertTrue(anchors)
                result = subprocess.run(
                    ["pandoc", "-f", "markdown+raw_tex+tex_math_dollars", "-t", "latex",
                     "--lua-filter", str(FILTER)], input=source, text=True,
                    capture_output=True, check=True).stdout
                for anchor in anchors:
                    self.assertIn("\\phantomsection\\label{" + anchor + "}", result)
                    self.assertIn("\\hypertarget{" + anchor + "}{}", result)

    def test_local_pdf_named_destination_is_normalized_only_for_latex(self):
        source = '[Proof](../long/record.pdf#nameddest=proof-step).\n'
        command = ["pandoc", "-f", "markdown", "-t", "latex", "--lua-filter", str(FILTER)]
        result = subprocess.check_output(command, input=source, text=True)
        self.assertIn(r"\href{../long/record.pdf\#proof-step}", result)
        self.assertNotIn("nameddest=", result)
        html = ["pandoc", "-f", "markdown", "-t", "html"]
        self.assertEqual(subprocess.check_output(html, input=source, text=True),
                         subprocess.check_output(html + ["--lua-filter", str(FILTER)],
                                                 input=source, text=True))

    def test_companion_annotation_links_only_in_a_pdf_reading_edition(self):
        source = ('<span class="pdf-companion" data-pdf-target="../long/record.pdf" '
                  'data-pdf-anchor="proof-step">Long §4, the proof</span>.\n')
        command = ["pandoc", "-f", "markdown", "-t", "latex", "--lua-filter", str(FILTER)]
        result = subprocess.check_output(command, input=source, text=True)
        self.assertIn(r"\href{../long/record.pdf\#proof-step}{Long §4, the proof}", result)
        html = subprocess.check_output(
            ["pandoc", "-f", "markdown", "-t", "html", "--lua-filter", str(FILTER)],
            input=source, text=True)
        self.assertIn("Long §4, the proof", html)
        self.assertNotIn("href=", html)
        portable = "---\nportable-local-links: true\n---\n" + source
        result = subprocess.check_output(command, input=portable, text=True)
        self.assertIn("Long §4, the proof", result)
        self.assertNotIn("record.pdf", result)

    def test_html_output_retains_the_existing_anchor(self):
        source = '<a id="proof-step"></a>\n\n## Proof\n\nSee [proof](#proof-step).\n'
        command = ["pandoc", "-f", "markdown", "-t", "html"]
        plain = subprocess.check_output(command, input=source, text=True)
        filtered = subprocess.check_output(command + ["--lua-filter", str(FILTER)],
                                           input=source, text=True)
        self.assertEqual(filtered, plain)

    def test_portable_pdf_keeps_reference_text_without_local_launches(self):
        source = """---
portable-local-links: true
---
[Long record, curvature section](../long/record.md#curvature).
[Original proof](https://example.org/proof#lemma).
[This section](#local-section).
[Absolute file](/tmp/paper.pdf). [File URL](file:///tmp/paper.pdf).

## Local section
"""
        command = ["pandoc", "-f", "markdown", "-t", "latex", "--lua-filter", str(FILTER)]
        result = subprocess.check_output(command, input=source, text=True)
        self.assertIn("Long record, curvature section", result)
        for target in ("../long/record.md", "/tmp/paper.pdf", "file://"):
            self.assertNotIn(target, result)
        self.assertIn("https://example.org/proof", result)
        self.assertIn("\\hyperref[local-section]", result)

        # The policy is opt-in and must not alter the other papers or HTML.
        ordinary = source.replace("portable-local-links: true", "portable-local-links: false")
        result = subprocess.check_output(command, input=ordinary, text=True)
        self.assertIn("../long/record.md", result)
        html = ["pandoc", "-f", "markdown", "-t", "html"]
        self.assertEqual(subprocess.check_output(html, input=source, text=True),
                         subprocess.check_output(html + ["--lua-filter", str(FILTER)],
                                                 input=source, text=True))


if __name__ == "__main__":
    unittest.main()
