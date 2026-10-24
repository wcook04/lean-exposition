"""Decisive query tests: selectors, capture identity and recorded support boundaries."""
from __future__ import annotations

import contextlib
import io
import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from lean_exposition import bundle, consumer
from lean_exposition.cli import main
from lean_exposition.consumer import project_paper, query_papers
from lean_exposition.contracts import ContractError, closure, digest, required_citation_ids, write_json
from test_paper_views import authored_bundle


def rebind(root: Path, *, content: bytes | None = None, graph: dict | None = None,
           copy_short_to_long: bool = False) -> None:
    """Synthetic fixture edits with full structural rebinding; never review inheritance."""
    if graph is not None:
        write_json(root / 'graph.json', graph)
    else:
        graph = json.loads((root / 'graph.json').read_bytes())
    if content is not None:
        (root / 'papers/short.md').write_bytes(content)
    for stage in ('long', 'short', 'expository'):
        path = root / f'papers/{stage}.json'
        mapping = json.loads(path.read_bytes())
        raw = (root / f'papers/{stage}.md').read_bytes()
        mapping['graph_sha256'] = digest((root / 'graph.json').read_bytes())
        mapping['content_sha256'] = digest(raw)
        reachable = closure(graph, mapping['claim_ids'] + graph['selected_goals'])
        nodes = {n['id']: n for n in graph['nodes']}
        mapping['assumption_ids'] = sorted(n for n in reachable if nodes[n]['kind'] == 'assumption')
        mapping['unresolved_ids'] = sorted(n for n in reachable if nodes[n]['status'] in
                                           {'open', 'unverified', 'external', 'conditional'})
        mapping['citation_ids'] = sorted(required_citation_ids(graph, mapping['claim_ids'] + graph['selected_goals']))
        for p in mapping['passages']:
            marker = f'<!-- passage:{p["anchor"]} -->'.encode()
            start = raw.index(marker) + len(marker)
            stop = raw.index(f'<!-- /passage:{p["anchor"]} -->'.encode())
            p['text_sha256'] = digest(raw[start:stop])
            reach = closure(graph, p['claim_ids'])
            p['assumption_ids'] = sorted(n for n in reach if nodes[n]['kind'] == 'assumption')
            p['citation_ids'] = sorted(required_citation_ids(graph, p['claim_ids']))
        write_json(path, mapping)
    if copy_short_to_long:
        (root / 'papers/long.md').write_bytes((root / 'papers/short.md').read_bytes())
        mapping = json.loads((root / 'papers/short.json').read_bytes())
        mapping['stage'], mapping['path'] = 'long', 'papers/long.md'
        write_json(root / 'papers/long.json', mapping)
    manifest = json.loads((root / 'manifest.json').read_bytes())
    for row in manifest['files']:
        row['sha256'] = digest((root / row['path']).read_bytes())
    write_json(root / 'manifest.json', manifest)


class PaperQueryTests(unittest.TestCase):
    def fixture(self, temporary, **kwargs):
        return authored_bundle(Path(temporary), **kwargs)

    def test_line_endings_preserve_outline_navigation_and_exact_source_bytes(self):
        for style in ('lf', 'crlf', 'cr', 'mixed'):
            with self.subTest(style=style), tempfile.TemporaryDirectory() as temporary:
                root = self.fixture(temporary)
                original = (root / 'papers/short.md').read_bytes()
                endings = {'lf': [b'\n'], 'crlf': [b'\r\n'], 'cr': [b'\r'],
                           'mixed': [b'\r\n', b'\r', b'\n']}[style]
                content = b''.join(line + endings[index % len(endings)]
                                   for index, line in enumerate(original.splitlines()))
                rebind(root, content=content)
                view = project_paper(root, 'short')
                sections = view['paper']['sections']
                self.assertEqual([s['title'] for s in sections], ['Paper', 'Result', 'Result'])
                self.assertEqual([s['heading_span']['start_line'] for s in sections], [5, 9, 13])
                self.assertEqual([s['heading_span']['end_line'] for s in sections], [5, 9, 13])
                self.assertEqual(view['paper']['line_count'], 17)
                passages = view['paper']['passages']
                self.assertEqual([(p['content_span']['start_line'], p['content_span']['end_line'])
                                  for p in passages], [(10, 11), (14, 15)])
                for passage in passages:
                    span = passage['content_span']
                    self.assertEqual(content[span['start_byte']:span['end_byte']].decode(),
                                     passage['text'])
                self.assertEqual((root / 'papers/short.md').read_bytes(), content)
                self.assertEqual(view['bundle']['markdown_sha256'], digest(content))
                query = query_papers(root, stage='short', section_refs=[sections[-1]['ref']])
                self.assertEqual([m['anchor'] for m in query['papers'][0]['matches']], ['result'])

    def test_direct_and_prerequisite_matches_have_different_warrants(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = self.fixture(temporary)
            direct = query_papers(root, stage='short', node_ids=['prerequisite'])
            indirect = query_papers(root, stage='short', node_ids=['prerequisite'], relation='prerequisites')
            self.assertEqual([m['anchor'] for m in direct['papers'][0]['matches']], ['premise'])
            self.assertEqual([m['anchor'] for m in indirect['papers'][0]['matches']], ['premise', 'result'])
            witness = indirect['papers'][0]['matches'][1]['witnesses'][0]
            self.assertEqual(witness['root_node_id'], 'goal')
            self.assertEqual(witness['target_node_id'], 'prerequisite')
            self.assertEqual([link['kind'] for link in witness['links']], ['supports'])
            self.assertTrue(witness['links'][0]['from'].endswith('/nodes/goal'))
            self.assertTrue(witness['links'][0]['to'].endswith('/nodes/prerequisite'))
            self.assertFalse(witness['semantic_certification'])
            assumption = query_papers(root, stage='short', node_ids=['assumption'], relation='prerequisites')
            witness = assumption['papers'][0]['matches'][0]['witnesses'][0]
            self.assertEqual(witness['root_mapping_field'], 'assumption_ids')
            self.assertEqual(witness['links'], [])
            self.assertTrue(any(link['kind'] == 'assumption_ids' and link['derived']
                                for link in assumption['papers'][0]['view']['graph']['argument_links']))

    def test_selecting_one_passage_retains_external_prerequisites_and_failures(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = self.fixture(temporary, formalization=True)
            paper = query_papers(root, stage='short', passages=['result'])['papers'][0]
            boundary = paper['support_boundary']
            self.assertEqual(boundary['mapped_claim_ids'], ['goal'])
            self.assertEqual(boundary['mapped_assumption_ids'], ['assumption'])
            self.assertEqual(boundary['retained_node_ids'], ['assumption', 'decl', 'goal', 'prerequisite'])
            self.assertEqual(boundary['not_mapped_as_claim_ids'], ['assumption', 'decl', 'prerequisite'])
            self.assertEqual(boundary['required_assumption_ids'], ['assumption'])
            self.assertEqual(boundary['unresolved_node_ids'], ['decl', 'goal', 'prerequisite'])
            records = paper['view']['graph']['records']
            self.assertEqual(records['evidence'][0]['record']['status'], 'failed')
            self.assertEqual(next(n['record']['status'] for n in records['nodes']
                                  if n['record']['id'] == 'decl'), 'unverified')
            witnesses = {w['target_node_id']: w for w in boundary['witnesses']}
            self.assertEqual(witnesses['decl']['links'][0]['kind'], 'formalizes')
            self.assertEqual(witnesses['decl']['links'][0]['semantic_class'], 'formalization_correspondence')
            self.assertEqual(paper['view']['selection']['omitted_by_selector'], ['premise'])

    def test_section_identity_disambiguates_equal_titles(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = self.fixture(temporary)
            sections = [s for s in project_paper(root, 'short')['paper']['sections'] if s['title'] == 'Result']
            first = query_papers(root, stage='short', section_refs=[sections[0]['ref']])
            second = query_papers(root, stage='short', section_refs=[sections[1]['ref']])
            self.assertEqual([m['anchor'] for m in first['papers'][0]['matches']], ['premise'])
            self.assertEqual([m['anchor'] for m in second['papers'][0]['matches']], ['result'])
            self.assertFalse(second['papers'][0]['matches'][0]['whole_passage_extends_beyond_selected_sections'])
            self.assertNotEqual(first['cache_key'], second['cache_key'])
            with self.assertRaises(ContractError):
                query_papers(root, stage='short', section_refs=['Result'])

    def test_section_overlap_keeps_whole_passage_and_warns_when_it_extends(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = self.fixture(temporary)
            content = ('# Root\n<!-- passage:result -->\nμ-opening.\n## A\nA text.\n'
                       '## B\nB text.\n<!-- /passage:result -->\n'
                       '## C\n<!-- passage:premise -->\nC text.\n<!-- /passage:premise -->\n'
                       '## Unmapped\nUnbound mathematics is still text.\n').encode()
            rebind(root, content=content)
            sections = {s['title']: s for s in project_paper(root, 'short')['paper']['sections']}
            paper = query_papers(root, stage='short', section_refs=[sections['A']['ref']])['papers'][0]
            self.assertEqual([m['anchor'] for m in paper['matches']], ['result'])
            self.assertTrue(paper['matches'][0]['whole_passage_extends_beyond_selected_sections'])
            passage = next(p for p in paper['view']['paper']['passages'] if p['selected'])
            self.assertIn('μ-opening', passage['text'])
            overlap = paper['matches'][0]['section_overlaps'][0]['overlap_span']
            self.assertEqual(content[overlap['start_byte']:overlap['end_byte']], b'## A\nA text.\n')
            all_sections = query_papers(root, stage='short', section_refs=[sections['Root']['ref']])
            self.assertTrue(all(not m['whole_passage_extends_beyond_selected_sections']
                                for m in all_sections['papers'][0]['matches']))
            empty = query_papers(root, stage='short', section_refs=[sections['Unmapped']['ref']])
            self.assertEqual(empty['match_count'], 0)
            self.assertEqual(empty['papers'][0]['support_boundary']['retained_node_ids'], [])
            self.assertIn('unmapped section', empty['coverage']['empty_result_meaning'])
            self.assertIn('Unbound mathematics', empty['papers'][0]['view']['paper']['text'])

    def test_section_whitespace_before_a_heading_is_not_a_passage_match(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = self.fixture(temporary)
            content = ("# Root\n## Before\nUnmapped introduction.\n"
                       "<!-- passage:result -->\n\n## Actual\nThe result.\n"
                       "<!-- /passage:result -->\n## Premise\n"
                       "<!-- passage:premise -->\nThe premise.\n"
                       "<!-- /passage:premise -->\n").encode()
            rebind(root, content=content)
            sections = {s["title"]: s for s in project_paper(root, "short")["paper"]["sections"]}
            before = query_papers(root, stage="short", section_refs=[sections["Before"]["ref"]])
            actual = query_papers(root, stage="short", section_refs=[sections["Actual"]["ref"]])
            self.assertEqual(before["match_count"], 0)
            self.assertEqual([m["anchor"] for m in actual["papers"][0]["matches"]], ["result"])

    def test_selector_families_intersect_and_values_within_family_union(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = self.fixture(temporary)
            self.assertEqual(query_papers(root, stage='short', passages=['premise'], node_ids=['goal'])['match_count'], 0)
            self.assertEqual(query_papers(root, stage='short', node_ids=['goal', 'prerequisite'])['match_count'], 2)
            self.assertEqual(query_papers(root, stage='short', passages=[])['match_count'], 0)
            self.assertEqual(query_papers(root, stage='short', section_refs=[])['match_count'], 0)
            self.assertEqual(query_papers(root, node_ids=[])['match_count'], 0)

    def test_all_papers_use_one_capture_and_shared_graph_refs(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = self.fixture(temporary)
            rebind(root, copy_short_to_long=True)
            with patch.object(consumer, 'load_bundle', wraps=consumer.load_bundle) as load:
                result = query_papers(root, node_ids=['goal'])
                self.assertEqual(load.call_count, 1)
            self.assertEqual(result['match_count'], 2)
            self.assertEqual([p['stage'] for p in result['papers']], ['long', 'short', 'expository'])
            self.assertEqual({p['view']['bundle']['manifest_sha256'] for p in result['papers']},
                             {result['snapshot']['manifest_sha256']})
            self.assertEqual(result['papers'][0]['matches'][0]['witnesses'][0]['target_ref'],
                             result['papers'][1]['matches'][0]['witnesses'][0]['target_ref'])
            self.assertNotEqual(result['papers'][0]['matches'][0]['passage_ref'],
                                result['papers'][1]['matches'][0]['passage_ref'])

    def test_mapping_only_change_invalidates_cache_and_passage_but_not_graph_ref(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = self.fixture(temporary)
            before = query_papers(root, stage='short', passages=['result'])
            path = root / 'papers/short.json'
            mapping = json.loads(path.read_bytes())
            mapping['passages'][0]['rationale'] += ' Revised fixture rationale.'
            write_json(path, mapping)
            rebind(root)
            after = query_papers(root, stage='short', passages=['result'])
            self.assertNotEqual(before['cache_key'], after['cache_key'])
            self.assertNotEqual(before['papers'][0]['matches'][0]['passage_ref'], after['papers'][0]['matches'][0]['passage_ref'])
            self.assertEqual(before['snapshot']['graph_sha256'], after['snapshot']['graph_sha256'])
            self.assertEqual(before['papers'][0]['view']['bundle']['markdown_ref'], after['papers'][0]['view']['bundle']['markdown_ref'])
            self.assertFalse(after['semantic_certification'])

    def test_stale_section_and_stale_mapping_fail_closed(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = self.fixture(temporary)
            section = project_paper(root, 'short')['paper']['sections'][1]['ref']
            rebind(root, content=b'\n' + (root / 'papers/short.md').read_bytes())
            with self.assertRaises(ContractError):
                query_papers(root, stage='short', section_refs=[section])
            (root / 'papers/short.md').write_bytes(b'Unchecked edit\n')
            with self.assertRaises(ContractError):
                query_papers(root)

    def test_expected_manifest_pins_the_capture_and_rejects_valid_successor(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = self.fixture(temporary)
            expected = digest((root / 'manifest.json').read_bytes())
            before = query_papers(root)
            with patch.object(consumer, 'load_bundle', wraps=consumer.load_bundle) as load:
                guarded = query_papers(root, expected_manifest_sha256=expected)
                self.assertEqual(load.call_count, 1)
            self.assertEqual(before, guarded)
            output, errors = io.StringIO(), io.StringIO()
            with contextlib.redirect_stdout(output), contextlib.redirect_stderr(errors):
                status = main(['query-papers', str(root), '--expect-manifest', expected])
            self.assertEqual(status, 0, errors.getvalue())
            self.assertEqual(json.loads(output.getvalue()), before)
            path = root / 'papers/short.json'
            mapping = json.loads(path.read_bytes())
            mapping['passages'][0]['rationale'] += ' Valid successor rationale.'
            write_json(path, mapping)
            rebind(root)
            after = query_papers(root)
            self.assertNotEqual(before['snapshot']['manifest_sha256'], after['snapshot']['manifest_sha256'])
            with self.assertRaisesRegex(ContractError, 'requested edition'):
                query_papers(root, expected_manifest_sha256=expected)
            for malformed in (0, {}, 'A' * 64, 'f' * 63):
                with self.subTest(malformed=malformed), self.assertRaises(ContractError):
                    query_papers(root, expected_manifest_sha256=malformed)

    def test_cycles_terminate_and_citation_platform_relations_are_excluded(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = self.fixture(temporary)
            graph = json.loads((root / 'graph.json').read_bytes())
            graph['edges'].append({'from': 'prerequisite', 'to': 'goal', 'kind': 'supports', 'evidence_ids': []})
            for identity, kind in [('citation-only', 'cites'), ('platform-only', 'platform_decomposition')]:
                graph['nodes'].append({'id': identity, 'kind': 'claim', 'label': identity,
                                       'status': 'open', 'assumption_ids': [], 'citation_ids': [], 'evidence_ids': []})
                graph['edges'].append({'from': 'goal', 'to': identity, 'kind': kind, 'evidence_ids': []})
            for number, identity in enumerate(('goal', 'platform-only')):
                node = next(n for n in graph['nodes'] if n['id'] == identity)
                node['source_id'] = 'public'
                node['platform'] = {'provider': 'prove2me',
                                    'id': f'00000000-0000-0000-0000-{number:012d}',
                                    'entity': 'theorem', 'status': 'synthetic', 'visibility': 'public'}
            graph['evidence'].append({'id': 'synthetic-platform', 'kind': 'platform_observation',
                                      'status': 'passed', 'command': [], 'tool': 'synthetic fixture',
                                      'source_ids': ['public'], 'subject_ids': ['goal', 'platform-only'],
                                      'details': 'Synthetic navigation evidence only; no real platform queried.'})
            graph['edges'][-1]['evidence_ids'] = ['synthetic-platform']
            rebind(root, graph=graph)
            result = query_papers(root, stage='short', node_ids=['goal'], relation='prerequisites')
            self.assertEqual(result['match_count'], 2)
            self.assertTrue(any(c['cyclic'] for c in result['papers'][0]['view']['graph']['components']))
            for node in ('citation-only', 'platform-only'):
                self.assertEqual(query_papers(root, node_ids=[node], relation='prerequisites')['match_count'], 0)
            witness = result['papers'][0]['matches'][0]['witnesses'][0]
            self.assertEqual(len(witness['links']), 1)
            self.assertEqual(witness['links'][0]['kind'], 'supports')

    def test_directory_zip_cli_and_selector_order_have_identical_results(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = self.fixture(temporary)
            archive = Path(temporary) / 'bundle.zip'
            bundle.export_bundle(root, archive)
            expected = query_papers(root, stage='short', node_ids=['goal', 'prerequisite'], relation='prerequisites')
            self.assertEqual(expected, query_papers(archive, stage='short', node_ids=['prerequisite', 'goal'], relation='prerequisites'))
            output, errors = io.StringIO(), io.StringIO()
            with contextlib.redirect_stdout(output), contextlib.redirect_stderr(errors):
                status = main(['query-papers', str(archive), '--paper', 'short', '--node', 'prerequisite',
                               '--node', 'goal', '--relation', 'prerequisites'])
            self.assertEqual(status, 0, errors.getvalue())
            self.assertEqual(json.loads(output.getvalue()), expected)

    def test_unknown_and_malformed_selectors_fail(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = self.fixture(temporary)
            cases = [dict(stage='missing'), dict(stage=[]), dict(passages=['result']),
                     dict(section_refs=['any']), dict(node_ids=['missing']), dict(relation='proof'),
                     dict(stage='short', passages=['result', 'result']), dict(node_ids='goal'),
                     dict(node_ids=[{}]), dict(node_ids=[False]), dict(stage='short', section_refs=[None])]
            for kwargs in cases:
                with self.subTest(kwargs=kwargs), self.assertRaises(ContractError):
                    query_papers(root, **kwargs)
            output, errors = io.StringIO(), io.StringIO()
            with contextlib.redirect_stdout(output), contextlib.redirect_stderr(errors):
                status = main(['query-papers', str(root), '--passage', 'result'])
            self.assertEqual(status, 1)
            self.assertIn('require one paper stage', errors.getvalue())

    def test_text_summary_keeps_json_default_and_uses_one_validated_capture(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = self.fixture(temporary, formalization=True)
            args = ['query-papers', str(root), '--paper', 'short', '--passage', 'result']
            expected = query_papers(root, stage='short', passages=['result'])
            for format_args in ([], ['--format', 'json']):
                output = io.StringIO()
                with contextlib.redirect_stdout(output):
                    status = main(args + format_args)
                self.assertEqual(status, 0)
                self.assertEqual(output.getvalue(), json.dumps(expected, indent=2, ensure_ascii=False) + '\n')
            output = io.StringIO()
            with patch.object(consumer, 'load_bundle', wraps=consumer.load_bundle) as load, \
                    contextlib.redirect_stdout(output):
                status = main(args + ['--format', 'text'])
                self.assertEqual(load.call_count, 1)
            self.assertEqual(status, 0)
            summary = output.getvalue()
            self.assertIn(expected['snapshot']['manifest_sha256'], summary)
            self.assertIn('result (bytes [', summary)
            self.assertIn('paper state draft; review state not_reviewed', summary)
            self.assertIn('Mapped claims: goal', summary)
            self.assertIn('Mapped assumptions: assumption', summary)
            self.assertIn('Additional recorded prerequisites (2): decl, prerequisite', summary)
            self.assertIn('source_hash / failed: 1; historical-failure', summary)
            self.assertIn('completeness beyond recorded relations: unknown', summary)
            self.assertIn('external source/receipt bytes opened by this query: false', summary)
            self.assertIn('Other mapped passages outside this selection: premise', summary)

    def test_text_summary_shows_cross_paper_witnesses_and_example_rationale(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = self.fixture(temporary)
            mapping_path = root / 'papers/short.json'
            mapping = json.loads(mapping_path.read_bytes())
            mapping['passages'][0]['evidence_class'] = 'example'
            mapping['passages'][0]['rationale'] = 'Teaching illustration; not a proof premise.'
            write_json(mapping_path, mapping)
            rebind(root, copy_short_to_long=True)
            output = io.StringIO()
            with contextlib.redirect_stdout(output):
                status = main(['query-papers', str(root), '--node', 'prerequisite',
                               '--relation', 'prerequisites', '--format', 'text'])
            self.assertEqual(status, 0)
            summary = output.getvalue()
            self.assertIn('matched passages: 4', summary)
            self.assertIn('long: 2 matching passage(s)', summary)
            self.assertIn('short: 2 matching passage(s)', summary)
            self.assertIn('expository: 0 matching passage(s)', summary)
            self.assertIn('Mapping class: example', summary)
            self.assertIn('Mapping rationale: Teaching illustration; not a proof premise.', summary)
            self.assertIn('Recorded path from claim_ids: goal --supports--> prerequisite', summary)
            self.assertIn('prerequisite (direct mapping)', summary)

    def test_text_summary_does_not_collapse_failed_unavailable_and_not_run(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = self.fixture(temporary)
            graph = json.loads((root / 'graph.json').read_bytes())
            graph['nodes'].append({'id': 'outside-subject', 'kind': 'claim', 'label': 'Outside subject',
                                   'status': 'open', 'assumption_ids': [], 'citation_ids': [],
                                   'evidence_ids': []})
            for identity, status in [('failure', 'failed'), ('pending', 'not_run'), ('unavailable', 'unavailable')]:
                graph['evidence'].append({
                    'id': identity, 'kind': 'comparator', 'status': status,
                    'command': [], 'tool': 'synthetic fixture', 'source_ids': ['public'],
                    'subject_ids': ['goal', 'outside-subject'], 'details': f'Synthetic {status} observation only.',
                })
            graph['evidence'][-1]['receipt'] = {'status': 'timed_out', 'process_status': 'timed_out'}
            rebind(root, graph=graph)
            output = io.StringIO()
            with contextlib.redirect_stdout(output):
                status = main(['query-papers', str(root), '--paper', 'short',
                               '--passage', 'result', '--format', 'text'])
            self.assertEqual(status, 0)
            summary = output.getvalue()
            for identity, state in [('failure', 'failed'), ('pending', 'not_run'), ('unavailable', 'unavailable')]:
                self.assertIn(f'comparator / {state}: 1; {identity}', summary)
                self.assertIn(f'{identity}: Synthetic {state} observation only.', summary)
            self.assertIn('Recorded receipt: status=timed_out, process_status=timed_out', summary)
            self.assertIn('Semantic certification: false', summary)
            self.assertIn('those subjects are not added as prerequisites', ' '.join(summary.split()))
            self.assertIn('Graph nodes outside this closure: 1', summary)
            projected = query_papers(root, stage='short', passages=['result'])['papers'][0]
            self.assertNotIn('outside-subject', projected['support_boundary']['retained_node_ids'])
            self.assertIn('outside-subject', projected['support_boundary']['outside_closure_node_ids'])

    def test_text_summary_explains_empty_match_and_preserves_stale_error(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = self.fixture(temporary)
            output, errors = io.StringIO(), io.StringIO()
            with contextlib.redirect_stdout(output), contextlib.redirect_stderr(errors):
                status = main(['query-papers', str(root), '--paper', 'short', '--passage',
                               'premise', '--node', 'goal', '--format', 'text'])
            self.assertEqual(status, 0)
            self.assertEqual(errors.getvalue(), '')
            self.assertIn('matched passages: 0', output.getvalue())
            self.assertIn('zero matches do not establish independence', ' '.join(output.getvalue().split()))
            self.assertIn('no check is inferred to have run', output.getvalue())
            (root / 'papers/short.md').write_bytes(b'Unchecked text change.\n')
            errors_by_format = []
            for output_format in ('json', 'text'):
                output, errors = io.StringIO(), io.StringIO()
                with contextlib.redirect_stdout(output), contextlib.redirect_stderr(errors):
                    status = main(['query-papers', str(root), '--format', output_format])
                self.assertEqual(status, 1)
                self.assertEqual(output.getvalue(), '')
                errors_by_format.append(json.loads(errors.getvalue()))
            self.assertEqual(*errors_by_format)
            self.assertIn('hash mismatch', errors_by_format[0]['error'])

    def test_text_summary_escapes_source_control_characters(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = self.fixture(temporary)
            path = root / 'papers/short.json'
            mapping = json.loads(path.read_bytes())
            mapping['passages'][0]['rationale'] = 'Source text: \x1b[2J\n\u202eexample'
            write_json(path, mapping)
            rebind(root)
            output = io.StringIO()
            with contextlib.redirect_stdout(output):
                status = main(['query-papers', str(root), '--paper', 'short',
                               '--passage', 'result', '--format', 'text'])
            self.assertEqual(status, 0)
            self.assertNotIn('\x1b', output.getvalue())
            self.assertNotIn('\u202e', output.getvalue())
            self.assertIn(r'Source text: \u001b[2J\u000a\u202eexample', output.getvalue())


if __name__ == '__main__':
    unittest.main()
