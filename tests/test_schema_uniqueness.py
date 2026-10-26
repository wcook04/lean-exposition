"""The uniqueItems shortcut preserves JSON Schema and graph semantics."""
from __future__ import annotations

import copy
import unittest

from jsonschema import Draft202012Validator

from lean_exposition.contracts import ContractError, _SchemaValidator, validate_graph, validate_schema
from test_adversarial import synthetic_graph


class SchemaUniquenessTests(unittest.TestCase):
    def test_same_id_different_rows_is_schema_distinct_but_graph_invalid(self):
        graph = synthetic_graph()
        row = copy.deepcopy(graph['nodes'][0])
        row['label'] = 'a different row with the same identity'
        graph['nodes'].append(row)
        validate_schema(graph, 'graph')
        with self.assertRaisesRegex(ContractError, 'duplicate node'):
            validate_graph(graph)

    def test_duplicate_objects_and_nested_array_duplicates_fail_schema(self):
        graph = synthetic_graph()
        graph['nodes'].append(copy.deepcopy(graph['nodes'][0]))
        with self.assertRaises(ContractError):
            validate_schema(graph, 'graph')
        graph = synthetic_graph()
        graph['nodes'][0]['assumption_ids'] = ['assumption', 'assumption']
        with self.assertRaises(ContractError):
            validate_schema(graph, 'graph')

    def test_arbitrary_json_and_numeric_equality_match_upstream(self):
        schema = {'type': 'array', 'uniqueItems': True}
        values = [
            ([True, 1], True), ([False, 0], True), ([1, 1.0], False),
            ([{'a': [True, 1.0], 'b': 'x'}, {'b': 'x', 'a': [True, 1]}], False),
            ([{'a': [1, 2]}, {'a': [2, 1]}], True),
            ([{'id': 'same', 'x': 1}, {'id': 'same', 'x': 2}], True),
            ([{'from': 'a', 'to': 'b', 'kind': 'x'},
              {'from': 'a', 'to': 'c', 'kind': 'x'}], True),
            ([{'from': 'a', 'to': 'b', 'kind': 'x'},
              {'from': 'a', 'to': 'b', 'kind': 'x'}], False),
            ([{'from': 'a', 'to': 'b', 'kind': 'x', 'v': 1},
              {'from': 'a', 'to': 'b', 'kind': 'x', 'v': 2}], True),
        ]
        for value, expected in values:
            with self.subTest(value=value):
                self.assertEqual(Draft202012Validator(schema).is_valid(value), expected)
                self.assertEqual(_SchemaValidator(schema).is_valid(value), expected)

    def test_typed_edge_identity_remains_a_separate_graph_guard(self):
        graph = synthetic_graph()
        graph['evidence'].append({'id': 'ev', 'kind': 'source_hash', 'status': 'not_run',
                                  'command': [], 'tool': 'test', 'source_ids': [],
                                  'subject_ids': [], 'details': 'synthetic'})
        edge = copy.deepcopy(graph['edges'][0])
        edge['evidence_ids'] = ['ev']
        graph['edges'].append(edge)
        validate_schema(graph, 'graph')
        with self.assertRaisesRegex(ContractError, 'duplicate typed edge'):
            validate_graph(graph)

    def test_deep_receipt_and_large_valid_record_collection(self):
        graph = synthetic_graph()
        nested = 'leaf'
        for _ in range(600):
            nested = [nested]
        graph['evidence'].append({'id': 'deep', 'kind': 'source_hash', 'status': 'not_run',
                                  'command': [], 'tool': 'test', 'source_ids': [],
                                  'subject_ids': [], 'details': 'synthetic',
                                  'receipt': {'nested': nested}})
        template = graph['nodes'][0]
        for index in range(1200):
            graph['nodes'].append({**template, 'id': f'node-{index}', 'label': f'node-{index}'})
        validate_schema(graph, 'graph')
        self.assertEqual(validate_graph(graph)['selected_goals'], ['goal'])


if __name__ == '__main__':
    unittest.main()
