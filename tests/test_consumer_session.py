"""Prepared consumers preserve editions and semantics without rebuilding views."""
from __future__ import annotations

import json
import shutil
import tempfile
import unittest
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from unittest.mock import patch

from lean_exposition import bundle, consumer
from lean_exposition.contracts import ContractError
from test_corpus_views import bind, corpus_bundle
from test_scoped_applications import application_bundle


class ConsumerSessionTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="lean-exposition-session-")
        self.addCleanup(temporary.cleanup)
        self.parent = Path(temporary.name)
        self.root = corpus_bundle(self.parent)
        self.session = consumer.ConsumerSession(self.root)
        self.corpus = consumer.project_corpus(self.root)
        self.manifest = self.corpus["snapshot"]["manifest_sha256"]

    def ref(self, table, identity):
        return next(row["ref"] for row in self.corpus["records"][table]
                    if row["record"].get("id") == identity)

    def test_full_and_selected_paper_views_equal_existing_projections(self):
        self.assertEqual(self.session.project_corpus(), self.corpus)
        for stage in bundle.STAGES:
            for selection in (None, [], ["result"], ["result", "premise"]) if stage == "short" else (None, []):
                with self.subTest(stage=stage, passages=selection):
                    self.assertEqual(self.session.project_paper(stage, selection),
                                     consumer.project_paper(self.root, stage, selection))
        self.assertEqual(consumer.project_corpus(self.session), self.corpus)
        self.assertEqual(consumer.project_paper(self.session, "short"), self.session.project_paper("short"))

    def assert_graph_parity(self, session, raw):
        graph = json.loads(raw)
        for view in ("declarations", "arguments", "citations", "platform", "provenance"):
            valid = [node["id"] for node in graph["nodes"]
                     if view != "declarations" or node["kind"] in {"declaration", "assumption"}]
            choices = [None, valid[:1], valid[-1:], valid[:3], list(reversed(valid[:3])), valid]
            directions = ("prerequisites", "consumers") if view not in {"citations", "provenance"} else ("prerequisites",)
            for roots in choices:
                for direction in directions:
                    for assumptions in (False, True) if view in {"arguments", "declarations"} else (False,):
                        query = {"direction": direction, "include_assumptions": assumptions}
                        with self.subTest(view=view, roots=roots, **query):
                            try:
                                expected = consumer.project_graph(raw, view, roots, **query)
                            except ContractError as exc:
                                with self.assertRaises(ContractError) as actual:
                                    session.project_graph(view, roots, **query)
                                self.assertEqual(str(actual.exception), str(exc))
                            else:
                                self.assertEqual(session.project_graph(view, roots, **query), expected)
                                self.assertEqual(consumer.project_graph(session, view, roots, **query), expected)

    def test_graph_views_reuse_same_projection_for_cycles_and_retained_lean_graph(self):
        self.assert_graph_parity(self.session, (self.root / "graph.json").read_bytes())
        minimal = Path(__file__).resolve().parents[1] / "examples/minimal/evidence-graph.json"
        root = self.parent / "minimal"
        bundle.scaffold(json.loads(minimal.read_bytes()), root)
        self.assert_graph_parity(consumer.ConsumerSession(root), (root / "graph.json").read_bytes())
        self.assertTrue(any(row["cyclic"] for row in self.session.project_graph("arguments")["components"]))

    def test_graph_projection_reuses_validation_record_refs_and_relation_indexes(self):
        expected = {view: self.session.project_graph(view, ["assumption"] if view == "declarations" else ["goal"])
                    for view in ("declarations", "arguments", "citations", "platform", "provenance")}
        with patch.object(consumer, "validate_graph", side_effect=AssertionError("capture already validated")), \
             patch.object(consumer, "decode_json", side_effect=AssertionError("records already decoded")), \
             patch.object(consumer, "_view_ref", side_effect=AssertionError("record refs already indexed")), \
             patch.object(consumer, "_argument_adjacency", side_effect=AssertionError("argument links already indexed")):
            for view, result in expected.items():
                self.assertEqual(self.session.project_graph(view, ["assumption"] if view == "declarations" else ["goal"]), result)

    def test_corpus_query_parity_includes_families_cycles_budgets_and_paper_scope(self):
        edge_ref = self.corpus["records"]["edges"][0]["ref"]
        queries = [
            {"records": [("nodes", "goal")], "families": [family], "direction": direction,
             "max_depth": depth, "max_records": budget}
            for family in self.corpus["relations"] for direction in ("incoming", "outgoing", "both")
            for depth, budget in ((0, 1), (1, 2), (3, 100))
        ] + [
            {"record_refs": [edge_ref], "families": ["provenance"]},
            {"records": [("sources", "public")], "families": ["provenance"], "direction": "incoming"},
            {"records": [("nodes", "goal")], "stage": "short", "max_depth": 3},
            {"records": [("nodes", "isolated")]},
            {"records": [("nodes", "goal"), ("sources", "public")], "families": ["provenance", "arguments"]},
        ]
        for query in queries:
            with self.subTest(query=query):
                self.assertEqual(self.session.query_corpus(**query), consumer.query_corpus(self.root, **query))

    def test_paper_query_parity_for_ranges_sections_and_prerequisite_witnesses(self):
        view = consumer.project_paper(self.root, "short")
        section = next(p for p in view["paper"]["passages"] if p["anchor"] == "result")["section_ref"]
        content = view["paper"]["text"].encode()
        begin = content.index("μ-result".encode())
        queries = [
            {}, {"stage": "long"}, {"stage": "short", "passages": []},
            {"stage": "short", "passages": ["result"]},
            {"node_ids": ["prerequisite"], "relation": "direct"},
            {"node_ids": ["prerequisite"], "relation": "prerequisites"},
            {"stage": "short", "section_refs": [section], "node_ids": ["goal"]},
            {"stage": "short", "byte_ranges": [(begin, begin + len("μ-result".encode()))],
             "expected_manifest_sha256": self.manifest},
            {"stage": "short", "byte_ranges": [(0, 1)], "expected_manifest_sha256": self.manifest},
        ]
        for query in queries:
            with self.subTest(query=query):
                full = self.session.query_papers(**query)
                self.assertEqual(full, consumer.query_papers(self.root, **query))
                compact = self.session.query_papers(**query, include_views=False)
                self.assertEqual(compact, consumer.query_papers(self.root, **query, include_views=False))
                self.assert_compact(full, compact)

    def assert_compact(self, full, compact):
        self.assertNotIn("representation", full)
        self.assertEqual(compact["representation"], "selected_passages")
        self.assertEqual(compact["representation_version"], consumer.COMPACT_PAPER_QUERY_VERSION)
        self.assertNotEqual(full["cache_key"], compact["cache_key"])
        for field in ("query", "snapshot", "match_count", "coverage", "semantic_certification", "relation_semantics"):
            self.assertEqual(compact[field], full[field])
        for expected, actual in zip(full["papers"], compact["papers"], strict=True):
            self.assertNotIn("view", actual)
            for field in ("stage", "matches", "selected_section_refs", "support_boundary"):
                self.assertEqual(actual[field], expected[field])
            view = expected["view"]
            self.assertEqual(actual["passages"], [p for p in view["paper"]["passages"] if p["selected"]])
            self.assertEqual(actual["correspondence_links"], view["correspondence_links"])
            for field in ("bundle", "state", "review_state", "paper_scope", "coverage", "paper_view_version"):
                self.assertEqual(actual["document"][field], view[field])
            for field in ("path", "byte_length", "line_count"):
                self.assertEqual(actual["document"][field], view["paper"][field])
            content = view["paper"]["text"].encode()
            for passage in actual["passages"]:
                span = passage["content_span"]
                self.assertEqual(passage["text"].encode(), content[span["start_byte"]:span["end_byte"]])

    def test_prepared_queries_reuse_corpus_document_and_argument_indexes(self):
        expected = consumer.query_corpus(self.root, records=[("nodes", "goal")])
        with patch.object(consumer, "project_corpus", side_effect=AssertionError("must reuse corpus")), \
             patch.object(consumer, "_corpus_neighbors", side_effect=AssertionError("must reuse neighbors")), \
             patch.object(consumer, "_paper_sections", side_effect=AssertionError("must reuse document")), \
             patch.object(consumer, "_argument_adjacency", side_effect=AssertionError("must reuse adjacency")), \
             patch.object(consumer, "decode_json", side_effect=AssertionError("must reuse decoded records")), \
             patch.object(consumer, "_project_paper", wraps=consumer._project_paper) as project:
            for _ in range(3):
                self.assertEqual(self.session.query_corpus(records=[("nodes", "goal")]), expected)
                self.session.project_paper("short")
                self.session.query_papers(stage="short", passages=["result"], include_views=False)
            self.assertEqual(project.call_count, 0)
            self.session.query_papers(stage="short", passages=["result"])
            self.assertEqual(project.call_count, 1, "selected support is built once, not a second full paper")

    def test_results_are_detached_and_queries_do_not_grow_session_state(self):
        operations = (
            lambda: self.session.project_corpus(),
            lambda: self.session.project_graph("arguments", include_assumptions=True),
            lambda: self.session.project_graph("provenance"),
            lambda: self.session.project_paper("short"),
            lambda: self.session.project_paper("short", ["result"]),
            lambda: self.session.query_corpus(records=[("nodes", "goal")]),
            lambda: self.session.query_papers(stage="short", passages=["result"]),
            lambda: self.session.query_papers(stage="short", passages=["result"], include_views=False),
        )
        before = {key: id(value) for key, value in vars(self.session).items()}

        def poison(value):
            if isinstance(value, dict):
                for child in list(value.values()):
                    poison(child)
                value.clear()
            elif isinstance(value, list):
                for child in list(value):
                    poison(child)
                value.clear()

        for operation in operations:
            expected = operation()
            returned = operation()
            poison(returned)
            self.assertEqual(operation(), expected)
        self.assertEqual({key: id(value) for key, value in vars(self.session).items()}, before)

    def test_concurrent_queries_are_independent(self):
        operations = (
            lambda: self.session.query_corpus(records=[("nodes", "goal")], max_depth=2),
            lambda: self.session.query_papers(stage="short", passages=["result"], include_views=False),
            lambda: self.session.query_papers(node_ids=["prerequisite"], relation="prerequisites"),
            lambda: self.session.project_paper("short", ["premise"]),
            lambda: self.session.project_graph("provenance"),
        )
        expected = [operation() for operation in operations]

        def task(index):
            value = operations[index]()
            self.assertEqual(value, expected[index])
            value.clear()

        with ThreadPoolExecutor(max_workers=4) as executor:
            list(executor.map(task, list(range(len(operations))) * 4))
        for operation, result in zip(operations, expected):
            self.assertEqual(operation(), result)

    def test_capture_and_manifest_pins_survive_original_changes(self):
        archive = self.parent / "edition.zip"
        bundle.export_bundle(self.root, archive)
        other = consumer.ConsumerSession(bundle.BundleCapture(archive))
        expected = self.session.query_papers(stage="short", passages=["result"])
        graph_expected = self.session.project_graph("arguments", include_assumptions=True)
        mapping = json.loads((self.root / "papers/short.json").read_bytes())
        mapping["review_notes"].append("Later commentary, not acceptance.")
        bind(self.root, mapping=mapping)
        successor = consumer.ConsumerSession(self.root)
        with self.assertRaisesRegex(ContractError, "differs from the requested edition"):
            successor.project_corpus(expected_manifest_sha256=self.manifest)
        shutil.rmtree(self.root)
        archive.unlink()
        with patch.object(consumer, "load_bundle", side_effect=AssertionError("must not reopen")):
            for session in (self.session, other):
                self.assertEqual(session.project_corpus(expected_manifest_sha256=self.manifest), self.corpus)
                self.assertEqual(session.query_papers(stage="short", passages=["result"]), expected)
                self.assertEqual(session.project_graph("arguments", include_assumptions=True), graph_expected)
                for operation in (
                    lambda pin: session.project_corpus(expected_manifest_sha256=pin),
                    lambda pin: session.query_corpus(records=[("nodes", "goal")], expected_manifest_sha256=pin),
                    lambda pin: session.query_papers(stage="short", expected_manifest_sha256=pin),
                ):
                    with self.assertRaisesRegex(ContractError, "differs from the requested edition"):
                        operation("0" * 64)
                    with self.assertRaisesRegex(ContractError, "64 lowercase hexadecimal"):
                        operation("invalid")

    def test_invalid_selections_retain_existing_rejections(self):
        for method, kwargs in (
            ("project_graph", {"view": "missing"}),
            ("project_graph", {"view": "arguments", "roots": ["missing"]}),
            ("project_graph", {"view": "arguments", "roots": []}),
            ("project_graph", {"view": "arguments", "roots": ["goal", "goal"]}),
            ("project_graph", {"view": "provenance", "direction": "consumers"}),
            ("project_graph", {"view": "citations", "include_assumptions": True}),
            ("project_graph", {"view": "arguments", "include_assumptions": 1}),
            ("project_paper", {"stage": "missing"}),
            ("project_paper", {"stage": "short", "passages": ["missing"]}),
            ("project_paper", {"stage": "short", "passages": ["result", "result"]}),
            ("query_corpus", {"records": [("nodes", "outside")], "stage": "short"}),
            ("query_corpus", {"record_refs": ["old-edition"]}),
            ("query_papers", {"stage": "short", "section_refs": ["stale"]}),
            ("query_papers", {"stage": "short", "byte_ranges": [(0, 1)]}),
            ("query_papers", {"include_views": 1}),
        ):
            with self.subTest(method=method, kwargs=kwargs), self.assertRaises(ContractError):
                getattr(self.session, method)(**kwargs)

    def test_compact_and_full_queries_preserve_scoped_assumptions(self):
        parent = self.parent / "scoped"
        parent.mkdir()
        root = application_bundle(parent)
        session = consumer.ConsumerSession(root)
        self.assert_graph_parity(session, (root / "graph.json").read_bytes())
        expected = session.project_graph("arguments", ["assumption"], direction="consumers", include_assumptions=True)
        with patch.object(consumer, "validate_graph", side_effect=AssertionError("already validated")), \
             patch.object(consumer, "_argument_adjacency", side_effect=AssertionError("already indexed")):
            self.assertEqual(session.project_graph("arguments", ["assumption"], direction="consumers",
                                                   include_assumptions=True), expected)
        for target in ("goal", "supplier", "assumption"):
            params = {"stage": "long", "node_ids": [target], "relation": "prerequisites"}
            full = session.query_papers(**params)
            self.assertEqual(full, consumer.query_papers(root, **params))
            compact = session.query_papers(**params, include_views=False)
            self.assert_compact(full, compact)
            if target == "assumption":
                self.assertEqual(compact["match_count"], 0)
            else:
                self.assertEqual(compact["papers"][0]["support_boundary"]["required_assumption_ids"], [])


if __name__ == "__main__":
    unittest.main()
