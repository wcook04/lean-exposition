"""Application obligations and citations; extraction receipts are synthetic."""
from __future__ import annotations

import copy
import json
import sys
import tempfile
import unittest
from pathlib import Path

from lean_exposition import bundle
from lean_exposition.consumer import project_graph
from lean_exposition.contracts import (ContractError, closure, decode_json, digest, encoded, select,
    formal_result_assurance, required_citation_ids, validate_artifact, validate_graph)
from lean_exposition.extraction import to_graph
from lean_exposition.verification import verify_comparator
from test_adversarial import synthetic_artifact, synthetic_graph
from test_core_review import extraction_fixture, rebind
import test_graph_semantics
from test_scoped_applications import application_graph, node


def extracted_application(root: Path, axiom: str) -> dict:
    report, build = extraction_fixture(root)
    report['declarations'][0].update(body_available=False, axioms=[axiom],
                                     has_sorry=axiom == 'sorryAx')
    report.update(unavailable_bodies=['result'], scope_complete=False)
    rebind(report)
    graph = to_graph(report, root, build)
    graph['schema_version'] = '1.2'
    graph['nodes'].extend([node('consumer', 'claim', 'unverified'),
                           node('supplier', 'claim', 'unverified')])
    graph['selected_goals'] = ['consumer']
    graph['edges'].extend([
        {'from': 'consumer', 'to': 'result', 'kind': 'supports', 'evidence_ids': [],
         'application': {'status': 'authored', 'shared_bindings': {'x': 'a supplied witness'},
             'premise_bindings': [{'assumption_id': axiom, 'supplier_id': 'supplier',
                                   'binding_names': ['x'], 'rationale': 'Synthetic binding.'}],
             'remaining_assumption_ids': [],
             'source_span': {'source_id': graph['sources'][0]['id'], 'start_line': 1, 'end_line': 1},
             'rationale': 'Synthetic binding, not a Lean substitution.'}},
        {'from': 'consumer', 'to': 'supplier', 'kind': 'supports', 'evidence_ids': []},
    ])
    return graph


def authored_mapping(graph, goal, *, assumptions=(), unresolved=(), citations=()):
    artifact, content = synthetic_artifact(graph)
    artifact.update(selected_goal_ids=[goal], claim_ids=[goal], assumption_ids=list(assumptions),
                    unresolved_ids=list(unresolved), citation_ids=list(citations))
    artifact['passages'][0].update(claim_ids=[goal], assumption_ids=list(assumptions),
                                   citation_ids=list(citations))
    return artifact, content


class ApplicationObligationTests(unittest.TestCase):
    def test_extracted_axiom_survives_application_and_historical_binding(self):
        for axiom in ('Classical.choice', 'sorryAx'):
            with self.subTest(axiom=axiom), tempfile.TemporaryDirectory() as tmp:
                graph = extracted_application(Path(tmp), axiom)
                summary = validate_graph(graph)
                self.assertIn(axiom, summary['assumptions'])
                self.assertIn(axiom, closure(graph, ['consumer']))
                if axiom == 'sorryAx':
                    self.assertIn(axiom, summary['unresolved'])
                view = project_graph(encoded(graph), 'arguments', ['consumer'], include_assumptions=True)
                self.assertIn(axiom, {row['record']['id'] for row in view['records']['nodes']})
                graph['edges'][0]['application']['remaining_assumption_ids'] = [axiom]
                validate_graph(graph)

    def test_artifact_must_retain_extracted_hole(self):
        with tempfile.TemporaryDirectory() as tmp:
            graph = extracted_application(Path(tmp), 'sorryAx')
            artifact, content = authored_mapping(graph, 'consumer',
                unresolved=['consumer', 'result', 'supplier'])
            with self.assertRaisesRegex(ContractError, 'assumptions or unresolved'):
                validate_artifact(artifact, graph, digest(encoded(graph)), content)
            artifact['assumption_ids'].append('sorryAx')
            artifact['passages'][0]['assumption_ids'].append('sorryAx')
            artifact['unresolved_ids'].append('sorryAx')
            validate_artifact(artifact, graph, digest(encoded(graph)), content)

    def test_renamed_sorry_is_never_discharged(self):
        graph = application_graph()
        axiom = next(row for row in graph['nodes'] if row['id'] == 'assumption')
        axiom.update(id='renamed-sorry', declaration='sorryAx', status='open')
        graph['nodes'][1]['assumption_ids'] = ['renamed-sorry']
        graph['edges'][0]['application']['premise_bindings'][0]['assumption_id'] = 'renamed-sorry'
        summary = validate_graph(graph)
        self.assertIn('renamed-sorry', summary['unresolved'])

    def test_supplied_informal_premise_still_discharges(self):
        graph = application_graph()
        summary = validate_graph(graph)
        self.assertNotIn('assumption', summary['assumptions'])
        self.assertIn('assumption', closure(graph, ['prerequisite']))

    def test_same_id_in_disconnected_formal_axiom_does_not_block_informal_use(self):
        with tempfile.TemporaryDirectory() as tmp:
            graph = extracted_application(Path(tmp), 'Classical.choice')
            graph['nodes'].extend([node('ordinary-goal', 'claim', 'unverified'),
                                   node('ordinary-result', 'claim', 'unverified', ['Classical.choice'])])
            application = copy.deepcopy(graph['edges'][0]['application'])
            graph['edges'].extend([
                {'from': 'ordinary-goal', 'to': 'ordinary-result', 'kind': 'supports',
                 'evidence_ids': [], 'application': application},
                {'from': 'ordinary-goal', 'to': 'supplier', 'kind': 'supports', 'evidence_ids': []}])
            graph['selected_goals'] = ['ordinary-goal']
            validate_graph(graph)
            self.assertNotIn('Classical.choice', closure(graph))
            self.assertIn('Classical.choice', closure(graph, ['consumer']))

    def test_documentary_credit_from_supplied_premise_and_cites_edge(self):
        graph = application_graph()
        graph['citations'].extend([
            {'id': name, 'title': name, 'url': 'https://example.org/credit',
             'source_id': 'public', 'locator': name}
            for name in ('premise-credit', 'cited-credit')])
        premise = next(row for row in graph['nodes'] if row['id'] == 'assumption')
        premise['citation_ids'] = ['premise-credit']
        cited = node('cited-work', 'claim', 'unverified', ['cited-assumption'])
        cited['citation_ids'] = ['cited-credit']
        graph['nodes'].extend([cited, node('cited-assumption', 'assumption', 'axiom')])
        graph['edges'].append({'from': 'assumption', 'to': 'cited-work',
                               'kind': 'cites', 'evidence_ids': []})
        validate_graph(graph)
        self.assertEqual(required_citation_ids(graph),
                         {'goal-credit', 'prerequisite-credit', 'premise-credit', 'cited-credit'})
        self.assertNotIn('assumption', closure(graph))
        self.assertNotIn('cited-assumption', closure(graph))
        self.assertEqual(required_citation_ids(graph, ['supplier']), set())
        artifact, content = authored_mapping(graph, 'goal', unresolved=['goal', 'prerequisite', 'supplier'],
            citations=['goal-credit', 'prerequisite-credit'])
        validate_artifact(artifact, graph, digest(encoded(graph)), content)
        with self.assertRaisesRegex(ContractError, 'dropped a claim citation'):
            validate_artifact(artifact, graph, digest(encoded(graph)), content,
                              require_current_citations=True)
        artifact['citation_ids'].extend(['premise-credit', 'cited-credit'])
        validate_artifact(artifact, graph, digest(encoded(graph)), content)
        with self.assertRaisesRegex(ContractError, 'passage omits an applicable citation'):
            validate_artifact(artifact, graph, digest(encoded(graph)), content,
                              require_current_citations=True)
        artifact['passages'][0]['citation_ids'].extend(['premise-credit', 'cited-credit'])
        validate_artifact(artifact, graph, digest(encoded(graph)), content,
                          require_current_citations=True)

    def test_real_qaoa_application_retains_premise_citations(self):
        root = Path(__file__).resolve().parents[1]
        graph = json.loads((root / 'examples/qaoa-sk/evidence-graph.json').read_bytes())
        expected = {'scalar-r2-26-cite-paper-admissible', 'scalar-r2-26-cite-paper-minimizer'}
        for target in ('support.near_ground_pairs', 'scalar.separate_classical_algorithm',
                       'circuit.classical_primary'):
            with self.subTest(target=target):
                self.assertTrue(expected <= required_citation_ids(graph, [target]))
                self.assertNotIn('scalar.paper_minimizer', closure(graph, [target]))


class ExtractionGraphAssuranceTests(unittest.TestCase):
    def test_recorded_value_path_to_sorry_cannot_be_kernel_checked(self):
        with tempfile.TemporaryDirectory() as tmp:
            project = Path(tmp)
            report, build = extraction_fixture(project)
            result = report['declarations'][0]
            support = copy.deepcopy(result)
            result['value_dependencies'] = ['support']
            support.update(name='support', value_dependencies=['sorryAx'],
                           axioms=['sorryAx'], has_sorry=True)
            report['declarations'].append(support)
            report['external_dependencies'].append({
                'name': 'sorryAx', 'module': 'Init.Prelude', 'kind': 'axiom',
                'reason': 'outside_module_prefixes'})
            rebind(report)
            with self.assertRaisesRegex(ContractError, 'dependency path to sorryAx'):
                to_graph(report, project, build)
            graph = to_graph(report, project)
            validate_graph(graph)
            self.assertIn('sorryAx', closure(graph, ['result']))

    def test_structural_edge_does_not_imply_a_sorry_axiom_path(self):
        with tempfile.TemporaryDirectory() as tmp:
            project = Path(tmp)
            report, build = extraction_fixture(project)
            result = report['declarations'][0]
            support = copy.deepcopy(result)
            result['structural_dependencies'] = ['support']
            support.update(name='support', value_dependencies=['sorryAx'],
                           axioms=['sorryAx'], has_sorry=True)
            report['declarations'].append(support)
            report['external_dependencies'].append({
                'name': 'sorryAx', 'module': 'Init.Prelude', 'kind': 'axiom',
                'reason': 'outside_module_prefixes'})
            rebind(report)
            graph = to_graph(report, project, build)
            self.assertEqual(next(n for n in graph['nodes'] if n['id'] == 'result')['status'],
                             'kernel_checked')
            self.assertIn('sorryAx', validate_graph(graph)['unresolved'])

    def test_extraction_request_checked_without_rebinding_selection(self):
        with tempfile.TemporaryDirectory() as tmp:
            project = Path(tmp)
            report, build = extraction_fixture(project)
            validate_graph(to_graph(report, project, build))
            report['roots'] = ['result', 'result']
            report['receipt']['extraction_request'] = {
                'module': 'Minimal', 'roots': ['result', 'result'],
                'module_prefixes': ['Minimal'], 'max_declarations': 1}
            rebind(report)
            graph = to_graph(report, project, build)
            graph['nodes'].append(node('other', 'claim', 'unverified'))
            validate_graph(select(graph, ['other']))
            for field, value in (('module', 'Other'), ('max_declarations', 0),
                                 ('max_declarations', True), ('roots', [])):
                broken = copy.deepcopy(graph)
                extract = next(e for e in broken['evidence'] if e['kind'] == 'extraction')
                extract['receipt']['extraction_request'][field] = value
                with self.subTest(field=field, value=value), self.assertRaises(ContractError):
                    validate_graph(broken)

    def test_legacy_checked_status_is_readable_but_safety_is_unknown(self):
        with tempfile.TemporaryDirectory() as tmp:
            project = Path(tmp)
            report, build = extraction_fixture(project)
            legacy = copy.deepcopy(report)
            legacy['schema_version'] = 1
            legacy['receipt'].pop('report_schema_version')
            for declaration in legacy['declarations']:
                declaration.pop('is_unsafe')
                declaration.pop('is_partial')
            rebind(legacy)
            graph = to_graph(legacy, project, build)
            graph['nodes'][0]['status'] = 'kernel_checked'
            validate_graph(graph)
            assurance = formal_result_assurance(graph, 'result')
            self.assertFalse(assurance['formal_result_eligible'])
            self.assertEqual(assurance['safety_classification'], 'legacy_or_unknown_safety')
            artifact, content = authored_mapping(graph, 'result')
            artifact['passages'][0]['evidence_class'] = 'formal_result'
            validate_artifact(artifact, graph, digest(encoded(graph)), content)
            with self.assertRaisesRegex(ContractError, 'current bound extraction and build observations'):
                validate_artifact(artifact, graph, digest(encoded(graph)), content,
                                  require_current_formal_assurance=True)
            current = to_graph(report, project, build)
            self.assertFalse(formal_result_assurance(current, 'result')['formal_result_eligible'])
            self.assertEqual(formal_result_assurance(current, 'result')['safety_classification'],
                             'recorded_safe_v2')
            extract = next(item for item in current['evidence'] if item['kind'] == 'extraction')
            extract['receipt'].update(
                extraction_request={'module': 'Minimal', 'roots': ['result'],
                                    'module_prefixes': ['Minimal'], 'max_declarations': 1},
                report_stdout_binding='lean-report-stdout-v1', process_status='passed',
                extractor_sha256='a' * 64, extractor_template_sha256='b' * 64,
                stdout_utf8_valid=True, stdout_sha256='c' * 64, stdout_bytes_sha256='c' * 64)
            next(item for item in current['evidence'] if item['kind'] == 'lean_build')['receipt']['process_status'] = 'passed'
            validate_graph(current)
            self.assertTrue(formal_result_assurance(current, 'result')['formal_result_eligible'])
            for field in ('extraction_request', 'report_stdout_binding', 'process_status',
                          'extractor_sha256', 'extractor_template_sha256', 'stdout_utf8_valid',
                          'stdout_sha256', 'stdout_bytes_sha256'):
                weakened = copy.deepcopy(current)
                next(item for item in weakened['evidence'] if item['kind'] == 'extraction')['receipt'].pop(field)
                with self.subTest(missing=field):
                    self.assertFalse(formal_result_assurance(weakened, 'result')['formal_result_eligible'])
            weakened = copy.deepcopy(current)
            next(item for item in weakened['evidence'] if item['kind'] == 'lean_build')['receipt'].pop('process_status')
            self.assertFalse(formal_result_assurance(weakened, 'result')['formal_result_eligible'])
            artifact, content = authored_mapping(current, 'result')
            artifact['passages'][0]['evidence_class'] = 'formal_result'
            validate_artifact(artifact, current, digest(encoded(current)), content,
                              require_current_formal_assurance=True)


class ComparatorV2GraphTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.project = Path(temporary.name)
        (self.project / 'Main.lean').write_text('theorem result : True := True.intro\n')
        (self.project / 'lean-toolchain').write_text('synthetic-toolchain\n')
        self.config = self.project / 'config.json'
        self.config.write_text(json.dumps({'challenge_module': 'Challenge', 'solution_module': 'Main',
                                           'theorem_names': ['Main.result'], 'permitted_axioms': []}))

    def receipt(self):
        return verify_comparator(self.project, 'config.json', command=[sys.executable, '-c', 'pass'])

    def graph(self, receipt):
        graph = synthetic_graph()
        graph['sources'].append({'id': 'config', 'kind': 'synthetic', 'url': 'urn:synthetic:config',
            'revision': receipt['config_sha256'], 'sha256': receipt['config_sha256'],
            'path': 'config.json', 'license': 'CC0-1.0', 'redistribution': 'original'})
        graph['evidence'].append({'id': 'comparison', 'kind': 'comparator',
            'status': receipt['status'], 'command': receipt['command'], 'tool': 'synthetic fixture',
            'source_ids': ['config'], 'subject_ids': ['goal'], 'details': 'Controlled Python process.',
            'receipt': receipt})
        return graph

    def test_valid_v2_and_legacy_receipts_remain_readable(self):
        receipt = self.receipt()
        self.assertEqual(receipt['status'], 'passed')
        validate_graph(self.graph(receipt))
        validate_graph(test_graph_semantics.ComparatorEvidenceTests().graph())

    def test_invalid_scope_cannot_be_flipped_to_passed(self):
        self.config.write_text('{}')
        receipt = self.receipt()
        self.assertEqual((receipt['status'], receipt['process_status']), ('failed', 'passed'))
        validate_graph(self.graph(receipt))
        receipt['status'] = 'passed'
        with self.assertRaises(ContractError):
            validate_graph(self.graph(receipt))

    def test_contradictory_v2_observations_fail_closed(self):
        original = self.receipt()
        mutations = [
            lambda r: r['config_observation'].update(status='invalid'),
            lambda r: r['config_observation']['scope'].update(theorem_names=[]),
            lambda r: r.update(config_changed=True),
            lambda r: r.update(config_sha256_after='0' * 64),
            lambda r: r['launch_executable_after'].update(sha256='0' * 64),
            lambda r: r.update(launch_executable_changed=True),
            lambda r: r.update(process_status='failed'),
            lambda r: r.update(returncode=True),
            lambda r: r.update(failure_reason='config_changed_during_run'),
        ]
        for mutate in mutations:
            receipt = copy.deepcopy(original)
            mutate(receipt)
            with self.subTest(receipt=receipt), self.assertRaises(ContractError):
                validate_graph(self.graph(receipt))


class UnicodeScalarTests(unittest.TestCase):
    def test_unpaired_surrogates_are_rejected_in_keys_and_values(self):
        for content in (br'{"outer":{"\ud800":1}}', br'{"outer":["\udfff"]}',
                        br'"\ud800"', br'{"same":1,"same":2,"\udfff":3}'):
            with self.subTest(content=content), self.assertRaisesRegex(
                    ContractError, 'unpaired Unicode surrogate'):
                decode_json(content)

    def test_surrogate_pair_and_duplicate_key_contract(self):
        self.assertEqual(decode_json(br'{"face":"\ud83d\ude00"}')['face'], '\U0001f600')
        self.assertEqual(decode_json(br'{"\ud83d\ude00":1}')['\U0001f600'], 1)
        with self.assertRaisesRegex(ContractError, 'duplicate JSON key'):
            decode_json(br'{"a":1,"a":2}')
        with self.assertRaisesRegex(ContractError, 'duplicate JSON key'):
            decode_json(br'{"\ud83d\ude00":1,"\ud83d\ude00":2}')

    def test_native_graph_rejects_surrogates_before_scaffold_creates_output(self):
        for location, invalid in (('id', '\ud800'), ('label', '\udfff'),
                                  ('nested-key', '\ud800'), ('deep-value', '\udfff')):
            with self.subTest(location=location), tempfile.TemporaryDirectory() as tmp:
                graph = synthetic_graph()
                if location == 'id':
                    graph['id'] = invalid
                elif location == 'label':
                    graph['nodes'][0]['label'] = invalid
                else:
                    nested = {invalid: 'value'} if location == 'nested-key' else invalid
                    for _ in range(600):
                        nested = [nested]
                    graph['evidence'].append({
                        'id': 'unicode-probe', 'kind': 'source_hash', 'status': 'not_run',
                        'command': [], 'tool': 'fixture', 'source_ids': [], 'subject_ids': [],
                        'details': 'synthetic', 'receipt': {'nested': nested}})
                with self.assertRaisesRegex(ContractError, 'unpaired Unicode surrogate'):
                    validate_graph(graph)
                output = Path(tmp) / 'not-created' / 'bundle'
                with self.assertRaisesRegex(ContractError, 'unpaired Unicode surrogate'):
                    bundle.scaffold(graph, output)
                self.assertFalse(output.parent.exists())

    def test_native_encoding_wraps_unicode_errors_and_preserves_valid_scalars(self):
        with self.assertRaisesRegex(ContractError, 'unpaired Unicode surrogate'):
            encoded({'nested': ('\ud800',)})
        graph = synthetic_graph()
        graph['id'] = 'face-\U0001f600'
        self.assertEqual(validate_graph(graph)['id'], graph['id'])
        self.assertEqual(decode_json(encoded(graph))['id'], graph['id'])
        decomposed = {'text': 'e\u0301'}
        self.assertEqual(decode_json(encoded(decomposed)), decomposed)


if __name__ == '__main__':
    unittest.main()
