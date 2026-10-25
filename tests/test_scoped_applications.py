"""Authored theorem applications preserve witnesses without certifying their truth."""
from __future__ import annotations

import copy
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

from lean_exposition import bundle
from lean_exposition.consumer import project_graph, project_paper, query_papers, project_corpus
from lean_exposition.contracts import (
    ContractError, closure, digest, encoded, required_citation_ids, validate_graph, write_json,
)
from test_adversarial import synthetic_graph, synthetic_artifact


def node(identity, kind, status, assumptions=()):
    return {'id': identity, 'kind': kind, 'status': status, 'label': identity,
            'assumption_ids': list(assumptions), 'citation_ids': [], 'evidence_ids': []}


def application_graph():
    graph = synthetic_graph()
    graph['schema_version'] = '1.2'
    graph['nodes'][0]['assumption_ids'] = []
    graph['nodes'][1]['assumption_ids'] = ['assumption']
    graph['nodes'].append(node('supplier', 'claim', 'unverified'))
    graph['edges'].append({'from': 'goal', 'to': 'supplier', 'kind': 'supports', 'evidence_ids': []})
    graph['edges'][0]['application'] = {
        'status': 'authored', 'shared_bindings': {'x': 'the witness from supplier'},
        'premise_bindings': [{'assumption_id': 'assumption', 'supplier_id': 'supplier',
                              'binding_names': ['x'], 'rationale': 'Supplies A for this same x.'}],
        'remaining_assumption_ids': [],
        'source_span': {'source_id': 'public', 'start_line': 2, 'end_line': 5},
        'rationale': 'Apply the conditional theorem to the supplied common witness.',
    }
    return graph


def application_bundle(root):
    graph = application_graph()
    scaffold = root / 'scaffold'
    bundle.scaffold(graph, scaffold)
    mapping, content = synthetic_artifact(graph)
    mapping['assumption_ids'] = []
    mapping['passages'][0]['assumption_ids'] = []
    mapping['unresolved_ids'].append('supplier')
    paper, map_path = root / 'long.md', root / 'long.json'
    paper.write_bytes(content)
    write_json(map_path, mapping)
    result = root / 'bundle'
    bundle.assemble_bundle(scaffold / 'graph.json', {
        stage: (paper, map_path) if stage == 'long' else
        (scaffold / f'papers/{stage}.md', scaffold / f'papers/{stage}.json')
        for stage in bundle.STAGES
    }, result)
    return result


class ScopedApplicationTests(unittest.TestCase):
    def test_application_includes_theorem_and_supplier_without_free_supplied_premise(self):
        graph = application_graph()
        summary = validate_graph(graph)
        self.assertEqual(set(summary['argument_closure']), {'goal', 'prerequisite', 'supplier'})
        self.assertEqual(summary['assumptions'], [])
        self.assertIn('assumption', closure(graph, ['prerequisite']))
        self.assertEqual(required_citation_ids(graph), {'goal-credit', 'prerequisite-credit'})
        self.assertEqual(graph['nodes'][1]['status'], 'unverified')

    def test_independent_use_retains_free_assumption_and_correct_query_path(self):
        graph = application_graph()
        graph['nodes'].append(node('independent', 'claim', 'unverified', ['assumption']))
        graph['edges'].append({'from': 'goal', 'to': 'independent', 'kind': 'supports', 'evidence_ids': []})
        validate_graph(graph)
        self.assertIn('assumption', closure(graph))
        view = project_graph(encoded(graph), 'arguments', include_assumptions=True)
        free_links = [l for l in view['links'] if l.get('to_node_id') == 'assumption']
        self.assertEqual([l['from_node_id'] for l in free_links], ['independent'])

    def test_suppliers_keep_their_own_free_requirements(self):
        graph = application_graph()
        graph['nodes'][-1]['assumption_ids'] = ['assumption']
        with self.assertRaisesRegex(ContractError, 'remaining assumptions'):
            validate_graph(graph)
        graph['edges'][0]['application']['remaining_assumption_ids'] = ['assumption']
        validate_graph(graph)
        self.assertIn('assumption', closure(graph))

    def test_common_bindings_are_local_to_each_use_and_references_are_checked(self):
        graph = application_graph()
        other = copy.deepcopy(graph['edges'][0])
        other['from'] = 'other'
        other['application']['shared_bindings']['x'] = 'a distinct witness for other'
        graph['nodes'].append(node('other', 'claim', 'unverified'))
        graph['edges'].extend([other, {'from': 'other', 'to': 'supplier', 'kind': 'supports', 'evidence_ids': []}])
        validate_graph(graph)
        self.assertNotIn('assumption', closure(graph, ['goal', 'other']))
        self.assertIn('assumption', closure(graph, ['goal', 'prerequisite']))
        other['application']['premise_bindings'][0]['binding_names'] = ['different_x']
        with self.assertRaisesRegex(ContractError, 'shared application binding'):
            validate_graph(graph)

    def test_boundaries_reject_unbound_missing_duplicate_and_fabricated_status(self):
        for change in ('version', 'supplier', 'duplicate', 'premise', 'status', 'span', 'kind'):
            with self.subTest(change=change):
                graph = application_graph()
                app = graph['edges'][0]['application']
                if change == 'version': graph['schema_version'] = '1.1'
                if change == 'supplier': graph['edges'].pop()
                if change == 'duplicate': app['premise_bindings'] *= 2
                if change == 'premise': app['premise_bindings'][0]['assumption_id'] = 'goal'
                if change == 'status': app['status'] = 'kernel_checked'
                if change == 'span': app['source_span']['end_line'] = 1
                if change == 'kind': graph['edges'][0]['kind'] = 'cites'
                with self.assertRaises(ContractError): validate_graph(graph)

    def test_nested_and_cyclic_applications_fail_but_ordinary_cycles_terminate(self):
        graph = application_graph()
        graph['edges'].append({'from': 'prerequisite', 'to': 'goal', 'kind': 'supports', 'evidence_ids': []})
        with self.assertRaisesRegex(ContractError, 'cyclic scoped'):
            validate_graph(graph)
        graph = application_graph()
        graph['nodes'].extend([node('inner', 'claim', 'unverified', ['assumption']),
                               node('inner-supplier', 'claim', 'unverified')])
        graph['edges'].extend([{'from': 'prerequisite', 'to': 'inner', 'kind': 'supports', 'evidence_ids': [],
                               'application': copy.deepcopy(graph['edges'][0]['application'])},
                              {'from': 'prerequisite', 'to': 'supplier', 'kind': 'supports', 'evidence_ids': []}])
        with self.assertRaisesRegex(ContractError, 'nested scoped'):
            validate_graph(graph)
        for version in ('1.0', '1.1', '1.2'):
            legacy = synthetic_graph()
            legacy['schema_version'] = version
            legacy['edges'].append({'from': 'prerequisite', 'to': 'goal', 'kind': 'supports', 'evidence_ids': []})
            self.assertEqual(set(validate_graph(legacy)['argument_closure']), {'goal', 'prerequisite', 'assumption'})

    def test_graph_view_and_reverse_view_respect_scoped_assumptions(self):
        graph = application_graph()
        view = project_graph(encoded(graph), 'arguments', include_assumptions=True)
        self.assertEqual({row['record']['id'] for row in view['records']['nodes']}, {'goal', 'prerequisite', 'supplier'})
        self.assertTrue(any('application' in l for l in view['links']))
        self.assertTrue(any('application_scope' in l for l in view['links']))
        reverse = project_graph(encoded(graph), 'arguments', ['assumption'], direction='consumers', include_assumptions=True)
        self.assertEqual({row['record']['id'] for row in reverse['records']['nodes']}, {'prerequisite', 'assumption'})

    def test_paper_queries_include_theorem_and_exclude_discharged_premise(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = application_bundle(Path(temporary))
            view = project_paper(root, 'long')
            self.assertEqual({row['record']['id'] for row in view['graph']['records']['nodes']}, {'goal', 'prerequisite', 'supplier'})
            found = query_papers(root, node_ids=['prerequisite'], relation='prerequisites', stage='long')
            self.assertIn('application', str(found))
            missing = query_papers(root, node_ids=['assumption'], relation='prerequisites', stage='long')
            self.assertEqual(missing['papers'][0]['matches'], [])
            corpus = project_corpus(root)
            self.assertIn('flat record pool', corpus['coverage']['application_semantics'])
            self.assertTrue(any('application' in l for l in corpus['relations']['arguments']))

    def test_independent_reader_preserves_transport_only_boundary(self):
        with tempfile.TemporaryDirectory() as temporary:
            parent = Path(temporary)
            root = application_bundle(parent)
            archive = parent / 'bundle.zip'
            bundle.export_bundle(root, archive)
            reader = Path(__file__).resolve().parents[1] / 'examples/consumer/read_bundle.py'
            result = subprocess.run([sys.executable, '-I', str(reader), str(archive)],
                                    capture_output=True, text=True, check=True)
            observed = json.loads(result.stdout)
            self.assertTrue(observed['transport_integrity'])
            self.assertFalse(observed['full_contract_validation'])
            self.assertFalse(observed['semantic_certification'])

    def test_selected_specimen_applications_keep_proof_and_model_boundaries(self):
        root = Path(__file__).resolve().parents[1]
        graph = json.loads((root / 'examples/qaoa-sk/evidence-graph.json').read_text())
        validate_graph(graph)
        nodes = {node['id']: node for node in graph['nodes']}
        scalar = closure(graph, ['scalar.formal_parisi_clause'])
        self.assertIn('scalar.source_ground_state_identity_with_diffusion', scalar)
        self.assertIn('scalar.source_diffusion_exists', scalar)
        self.assertEqual({n for n in scalar if nodes[n]['kind'] == 'assumption'}, {'assumptions.value_minimizer'})
        circuit = closure(graph, ['circuit.classical_primary'])
        self.assertIn('support.full_relative_support', circuit)
        self.assertFalse({n for n in circuit if nodes[n]['kind'] == 'assumption'})
        self.assertIn('assumptions.full_support_minimizer', closure(graph, ['full_support']))
        self.assertIn('scalar.paper_minimizer', closure(graph, ['circuit.classical_fixed_minimizer']))


if __name__ == '__main__':
    unittest.main()
