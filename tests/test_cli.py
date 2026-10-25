"""Exercise the installed user journey with no network or Lean requirement."""
import contextlib
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import zipfile

from lean_exposition.cli import main

ROOT = Path(__file__).resolve().parents[1]
GRAPH = ROOT / 'examples/qaoa-sk/evidence-graph.json'


class CliTests(unittest.TestCase):
    def call(self, *args):
        output, errors = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(output), contextlib.redirect_stderr(errors):
            code = main([str(a) for a in args])
        return code, output.getvalue(), errors.getvalue()

    def test_serve_document_paths_require_a_complete_unambiguous_stage_map(self):
        paths = {"long": "proof/record.md", "short": "expert/paper.md", "expository": "reader/intro.md"}
        arguments = [value for stage, path in paths.items() for value in ("--document-path", stage, path)]
        with patch("lean_exposition.web.serve", return_value={"stopped": True}) as serve:
            code, _, errors = self.call("serve", "unused-bundle", *arguments)
            self.assertEqual(code, 0, errors)
            self.assertEqual(serve.call_args.kwargs["document_paths"], paths)
        for bad in (arguments[:3], [*arguments, *arguments[:3]],
                    ["--document-path", "unknown", "elsewhere.md", *arguments[3:]]):
            with self.subTest(arguments=bad), patch("lean_exposition.web.serve") as serve:
                code, output, errors = self.call("serve", "unused-bundle", *bad)
                self.assertEqual(code, 1)
                self.assertEqual(output, "")
                self.assertIn("exactly once", json.loads(errors)["error"])
                serve.assert_not_called()

    def test_offline_selection_scaffold_check_export(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            selected = root / 'selected.json'
            code, output, errors = self.call('select', GRAPH, '--goal', 'scalar_value', '--out', selected)
            self.assertEqual(code, 0, errors)
            self.assertEqual(json.loads(output)['selected_goals'], ['scalar_value'])
            bundle = root / 'bundle'
            code, _, errors = self.call('scaffold', selected, '--out', bundle)
            self.assertEqual(code, 0, errors)
            code, output, errors = self.call('check-bundle', bundle)
            self.assertEqual(code, 0, errors)
            self.assertEqual(json.loads(output)['paper_states'], ['scaffold'] * 3)
            assembled = root / 'assembled'
            arguments = ['assemble', bundle / 'graph.json']
            for stage in ('long', 'short', 'expository'):
                arguments.extend(['--' + stage, bundle / f'papers/{stage}.md',
                                  bundle / f'papers/{stage}.json'])
            code, _, errors = self.call(*arguments, '--out', assembled)
            self.assertEqual(code, 0, errors)
            archive = root / 'bundle.zip'
            code, _, errors = self.call('export', assembled, '--out', archive)
            self.assertEqual(code, 0, errors)
            with zipfile.ZipFile(archive) as z:
                self.assertEqual(len(z.namelist()), 8)
                self.assertIn(b'EMPTY SCAFFOLD', z.read('papers/expository.md'))
            code, output, errors = self.call('inspect-bundle', archive)
            self.assertEqual(code, 0, errors)
            self.assertTrue(json.loads(output)['contract_valid'])
            self.assertFalse(json.loads(output)['semantic_certification'])
            # No silent overwrite of a reviewed or existing export.
            code, _, _ = self.call('export', bundle, '--out', archive)
            self.assertEqual(code, 1)

    def test_unknown_goal_fails_without_output_file(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / 'bad.json'
            code, _, errors = self.call('select', GRAPH, '--goal', 'missing', '--out', path)
            self.assertEqual(code, 1)
            self.assertIn('unknown', errors)
            self.assertFalse(path.exists())

    def test_non_object_source_lock_has_structured_error(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / 'lock.json'
            destination = Path(tmp) / 'output'
            for value in (None, [], 'invalid'):
                with self.subTest(value=value):
                    path.write_text(json.dumps(value))
                    code, output, errors = self.call('fetch', path, '--out', destination)
                    self.assertEqual(code, 1)
                    self.assertEqual(output, '')
                    self.assertEqual(json.loads(errors)['error'], 'source lock must be an object')
                    self.assertFalse(destination.exists())

    def test_edit_without_rebinding_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / 'bundle'
            code, _, _ = self.call('scaffold', GRAPH, '--out', path)
            self.assertEqual(code, 0)
            (path / 'papers/short.md').write_text('Unbound new text\n')
            code, _, errors = self.call('check-bundle', path)
            self.assertEqual(code, 1)
            self.assertIn('hash mismatch', errors)

    def test_inspect_selection_preserves_evidence(self):
        code, output, errors = self.call('inspect', GRAPH, '--goal', 'scalar_value')
        self.assertEqual(code, 0, errors)
        result = json.loads(output)
        original = json.loads(GRAPH.read_text())
        self.assertEqual(result['selected_goals'], ['scalar_value'])
        self.assertEqual(len(result['nodes']), len(original['nodes']))
        self.assertEqual(len(result['evidence']), len(original['evidence']))
        self.assertTrue(any(n['selected'] for n in result['nodes'] if n['id'] == 'scalar_value'))

    def test_source_review_binds_current_graph_and_original_source_bytes(self):
        import hashlib
        review = json.loads((ROOT / 'papers/qaoa-sk/source-review/correspondence.json').read_text())
        self.assertEqual(review['graph_sha256'], hashlib.sha256(GRAPH.read_bytes()).hexdigest())
        for name, source in review['sources'].items():
            with self.subTest(source=name):
                self.assertEqual(source['sha256'], hashlib.sha256((ROOT / source['path']).read_bytes()).hexdigest())

    def test_public_graph_source_anchors_match_bytes(self):
        import hashlib
        graph = json.loads(GRAPH.read_text())
        sources = {s['id']: s for s in graph['sources']}
        for source in sources.values():
            if source['redistribution'] == 'vendored':
                path = GRAPH.parent / source['path']
                self.assertTrue(path.is_file(), source['id'])
                self.assertEqual(hashlib.sha256(path.read_bytes()).hexdigest(), source['sha256'])
        authored_sources = {
            'authored_long_comparisons_20261024':
                ROOT / 'papers/qaoa-sk/long/reasoning-record.md',
        }
        for citation in graph['citations']:
            with self.subTest(citation=citation['id']):
                self.assertIn(citation['source_id'], sources)
                self.assertTrue(citation['locator'])
                if citation['source_id'] in authored_sources:
                    source = sources[citation['source_id']]
                    self.assertEqual(source['kind'], 'file')
                    self.assertEqual(source['redistribution'], 'original')
                    self.assertRegex(source['sha256'], r'^[0-9a-f]{64}$')
                    expected_url = 'urn:sha256:' + source['sha256']
                    self.assertEqual(citation['url'], expected_url)
                    self.assertEqual(source['url'], expected_url)
                    self.assertEqual(source['revision'], 'sha256:' + source['sha256'])
                    path = authored_sources[citation['source_id']]
                    self.assertTrue(path.is_file())
                    self.assertEqual(hashlib.sha256(path.read_bytes()).hexdigest(),
                                     source['sha256'])
                else:
                    self.assertTrue(citation['url'].startswith('https://'))


if __name__ == '__main__':
    unittest.main()
