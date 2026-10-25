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

    def test_html_output_retains_the_existing_anchor(self):
        source = '<a id="proof-step"></a>\n\n## Proof\n\nSee [proof](#proof-step).\n'
        command = ["pandoc", "-f", "markdown", "-t", "html"]
        plain = subprocess.check_output(command, input=source, text=True)
        filtered = subprocess.check_output(command + ["--lua-filter", str(FILTER)],
                                           input=source, text=True)
        self.assertEqual(filtered, plain)


if __name__ == "__main__":
    unittest.main()
