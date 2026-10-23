import importlib.util
from pathlib import Path
import tempfile
import unittest

spec = importlib.util.spec_from_file_location(
    'check_links', Path(__file__).resolve().parents[1] / 'scripts/check_links.py')
links = importlib.util.module_from_spec(spec)
spec.loader.exec_module(links)


class ReferenceLinksTests(unittest.TestCase):
    def test_missing_explicit_reference_from_rendered_paper(self):
        _, missing = links.markdown_links('See [regularity section][support-regularity].')
        self.assertEqual(missing, ['support-regularity'])

    def test_resolves_case_whitespace_and_collapsed_labels(self):
        destinations, missing = links.markdown_links(
            '[section][Support  Regularity] and [Support regularity][]\n'
            '[support regularity]: source.md\n')
        self.assertEqual(missing, [])
        self.assertEqual(destinations, ['source.md'])

    def test_literal_code_math_and_shortcut_citations_are_not_links(self):
        _, missing = links.markdown_links(
            '```md\n[a][b]\n```\n`[c][d]` $[e][f]$ [Chen]\n'
            '$$[g][h]$$\n')
        self.assertEqual(missing, [])

    def test_defined_reference_still_requires_local_file(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary).resolve()
            document = root/'paper.md'
            document.write_text('[proof][p]\n[p]: absent.md\n')
            self.assertIn('missing or external local destination absent.md', links.check([document],root)[0])
            (root/'absent.md').write_text('Proof')
            self.assertEqual(links.check([document],root), [])
