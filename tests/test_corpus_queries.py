"""Record-first navigation: typed links, paper boundaries and bounded queries.

Synthetic records test navigation contracts; the QAOA fixture tests actual
source-to-paper correspondence. No test runs Lean, Comparator or source intake.
"""
from __future__ import annotations

import contextlib
import io
import json
import tempfile
import unittest
from collections import Counter
from pathlib import Path
from unittest.mock import patch

from lean_exposition import bundle, consumer
from lean_exposition.cli import main
from lean_exposition.contracts import ContractError
from test_adversarial import synthetic_graph
from test_corpus_views import bind, corpus_bundle

ROOT = Path(__file__).resolve().parents[1]


def pool(view, key="records"):
    return {row["ref"]: row["record"]
            for rows in view[key].values() for row in rows}


def ids(view, table="nodes"):
    return {row["record"]["id"] for row in view["records"][table]}


def record_ref(corpus, table, identifier):
    return next(row["ref"] for row in corpus["records"][table]
                if row["record"]["id"] == identifier)


class CorpusQueryTests(unittest.TestCase):
    def query(self, path, **kwargs):
        result = consumer.query_corpus(path, **kwargs)
        self.assertIsInstance(result, dict)
        return result

    def assert_resolves_without_reorienting(self, result, corpus):
        selected = set(result["selected_record_refs"])
        self.assertEqual(selected, set(pool(result)))
        available = pool(result) | pool(result, "supplementary_records")
        self.assertFalse(selected.intersection(pool(result, "supplementary_records")))
        original = pool(corpus)
        for ref, record in available.items():
            self.assertEqual(record, original[ref])
        original_links = {link["id"]: link
                          for links in corpus["relations"].values() for link in links}
        for links in result["relations"].values():
            for link in links:
                self.assertEqual(link, original_links[link["id"]])
                self.assertIn(link["from"], selected)
                self.assertIn(link["to"], selected)
                self.assertIn(link.get("owner_ref", link.get("record_ref")), available)
        for entry in result["frontier"]:
            link = entry["relation"]
            self.assertEqual(link, original_links[link["id"]])
            self.assertIn(link["from"], available)
            self.assertIn(link["to"], available)
            self.assertIn(link.get("owner_ref", link.get("record_ref")), available)
        witnesses = {row["record_ref"]: row for row in result["witnesses"]}
        self.assertEqual(set(witnesses), selected)
        for ref, row in witnesses.items():
            if row["parent"] is None:
                self.assertEqual(row["distance"], 0)
                self.assertEqual(row["root_ref"], ref)
                continue
            parent = row["parent"]
            self.assertIn(parent["record_ref"], witnesses)
            self.assertEqual(row["distance"], witnesses[parent["record_ref"]]["distance"] + 1)
            self.assertEqual(row["root_ref"], witnesses[parent["record_ref"]]["root_ref"])
            link = original_links[parent["relation_id"]]
            self.assertEqual({link["from"], link["to"]}, {ref, parent["record_ref"]})
            self.assertIn(link, corpus["relations"][parent["family"]])

    def test_actual_qaoa_source_reaches_records_and_exact_direct_passage_usage(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary) / "authored"
            papers = ROOT / "papers/qaoa-sk"
            bundle.assemble_bundle(ROOT / "examples/qaoa-sk/evidence-graph.json", {
                "long": (papers / "long/reasoning-record.md", papers / "long/reasoning-record.json"),
                "short": (papers / "short/paper.md", papers / "short/correspondence.json"),
                "expository": (papers / "expository/main.md", papers / "expository/correspondence.json"),
            }, root)
            result = self.query(root, records=[("sources", "support_tex_curvature")],
                                direction="incoming", families=["provenance"], max_depth=1)
            self.assertEqual(ids(result), {"support.positive_curvature", "scalar.constant_curvature"})
            self.assertEqual(ids(result, "citations"),
                             {"support_curvature_source", "scalar-r2-26-cite-constant-curvature"})
            self.assertEqual(len(ids(result, "evidence")), 8)
            self.assertEqual(ids(result, "sources"), {"support_tex_curvature"})
            self.assertEqual(len(result["selected_record_refs"]), 13)
            citation = record_ref(result, "citations", "support_curvature_source")
            usage = next(row for row in result["record_usage"] if row["record_ref"] == citation)
            self.assertEqual(Counter(row["stage"] for row in usage["direct_passages"]),
                             Counter(long=22, short=8, expository=10))
            self.assertFalse(result["coverage"]["source_bytes_opened"])
            self.assertFalse(result["coverage"]["receipt_bytes_opened"])
            corpus = consumer.project_corpus(root)
            self.assertEqual(corpus["graph"]["recorded_extraction_status"], "not_run")
            self.assert_resolves_without_reorienting(result, corpus)

    def test_reverse_and_parallel_relations_keep_stored_endpoints_and_witnesses(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = corpus_bundle(Path(temporary))
            graph = json.loads((root / "graph.json").read_bytes())
            graph["edges"].append({"from": "goal", "to": "decl", "kind": "supports", "evidence_ids": []})
            bind(root, graph=graph)
            corpus = consumer.project_corpus(root)
            result = self.query(root, records=[("nodes", "decl")], families=["arguments"],
                                direction="incoming", max_depth=10)
            self.assertEqual(ids(result), {"decl", "goal"})
            links = result["relations"]["arguments"]
            pair = [link for link in links if link["to"] == record_ref(corpus, "nodes", "decl")]
            self.assertEqual({link["kind"] for link in pair}, {"supports", "formalizes"})
            self.assertTrue(any(component["cyclic"] for component in result["components"]))
            self.assertFalse(result["coverage"]["query_truncated"])
            self.assertTrue(result["coverage"]["stored_traversal_exhausted"])
            self.assert_resolves_without_reorienting(result, corpus)

    def test_families_do_not_import_citation_platform_or_provenance_as_arguments(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = corpus_bundle(Path(temporary))
            result = self.query(root, records=[("nodes", "goal")], families=["arguments"],
                                direction="outgoing", max_depth=10)
            self.assertEqual(ids(result), {"goal", "prerequisite", "assumption", "decl"})
            self.assertFalse(ids(result, "sources"))
            kinds = {link["kind"] for links in result["relations"].values() for link in links}
            self.assertEqual(kinds, {"supports", "formalizes", "assumption_ids"})
            self.assertTrue(all(link["derived"] for link in result["relations"]["arguments"]
                                if link["kind"] == "assumption_ids"))

    def test_paper_scope_exposes_outside_subject_without_importing_it(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = corpus_bundle(Path(temporary))
            kwargs = dict(records=[("evidence", "historical-failure")],
                          families=["provenance"], direction="outgoing", max_depth=10)
            scoped = self.query(root, stage="short", **kwargs)
            global_view = self.query(root, **kwargs)
            self.assertIn("goal", ids(scoped))
            self.assertNotIn("outside", ids(scoped))
            self.assertIn("outside", ids(global_view))
            outside = record_ref(consumer.project_corpus(root), "nodes", "outside")
            boundaries = [row for row in scoped["frontier"] if row["traversed_to"] == outside]
            self.assertTrue(boundaries)
            self.assertEqual({row["reason"] for row in boundaries}, {"outside_paper"})
            self.assertTrue(scoped["coverage"]["paper_boundary_present"])
            self.assertFalse(scoped["coverage"]["query_truncated"])
            self.assertTrue(scoped["coverage"]["stored_traversal_exhausted"])
            self.assert_resolves_without_reorienting(scoped, consumer.project_corpus(root))
            for stage, identifier in (("short", "outside"), ("long", "goal")):
                with self.subTest(stage=stage), self.assertRaises(ContractError):
                    self.query(root, records=[("nodes", identifier)], stage=stage)

    def test_depth_and_record_caps_have_honest_frontiers_and_keep_roots(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = corpus_bundle(Path(temporary))
            kwargs = dict(records=[("nodes", "goal")], families=["arguments"], direction="outgoing")
            zero = self.query(root, max_depth=0, **kwargs)
            self.assertEqual(ids(zero), {"goal"})
            self.assertTrue(zero["frontier"])
            self.assertEqual({row["reason"] for row in zero["frontier"]}, {"depth_limit"})
            capped = self.query(root, max_depth=5, max_records=2, **kwargs)
            self.assertEqual(len(capped["selected_record_refs"]), 2)
            self.assertIn("goal", ids(capped))
            self.assertEqual({row["reason"] for row in capped["frontier"]}, {"record_limit"})
            for result in (zero, capped):
                self.assertTrue(result["coverage"]["query_truncated"])
                self.assertFalse(result["coverage"]["stored_traversal_exhausted"])
                self.assert_resolves_without_reorienting(result, consumer.project_corpus(root))
            with self.assertRaises(ContractError):
                self.query(root, records=[("nodes", "goal"), ("nodes", "prerequisite")], max_records=1)

    def test_disconnected_record_has_empty_neighbors_without_fabricated_membership(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = corpus_bundle(Path(temporary))
            result = self.query(root, records=[("nodes", "isolated")], max_depth=10)
            self.assertEqual(ids(result), {"isolated"})
            self.assertFalse(any(result["relations"].values()))
            self.assertEqual(result["frontier"], [])
            self.assertFalse(result["coverage"]["query_truncated"])
            self.assertTrue(result["coverage"]["stored_traversal_exhausted"])
            self.assertEqual(result["record_usage"][0]["paper_memberships"], [])
            self.assertEqual(result["record_usage"][0]["direct_passages"], [])

    def test_namespaces_encoded_ids_and_exact_edge_refs_are_unambiguous(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = corpus_bundle(Path(temporary))
            graph = json.loads((root / "graph.json").read_bytes())
            graph["sources"].append({**graph["sources"][0], "id": "goal"})
            graph["evidence"].append({**graph["evidence"][0], "id": "goal"})
            for identifier in ("x/y", "x%2Fy", "μ"):
                graph["nodes"].append({"id": identifier, "kind": "claim", "label": identifier,
                                       "status": "open", "assumption_ids": [],
                                       "citation_ids": [], "evidence_ids": []})
            bind(root, graph=graph)
            corpus = consumer.project_corpus(root)
            seeds = [(table, "goal") for table in ("nodes", "sources", "evidence")]
            seeds += [("nodes", identifier) for identifier in ("x/y", "x%2Fy", "μ")]
            result = self.query(root, records=seeds, max_depth=0)
            expected = {record_ref(corpus, table, identifier) for table, identifier in seeds}
            self.assertEqual(set(result["selected_record_refs"]), expected)
            self.assertEqual(len(expected), 6)
            edge = corpus["records"]["edges"][0]
            edge_result = self.query(root, record_refs=[edge["ref"]], max_depth=0)
            self.assertEqual(pool(edge_result), {edge["ref"]: edge["record"]})
            self.assert_resolves_without_reorienting(edge_result, corpus)

    def test_directory_zip_capture_and_selector_order_are_identical(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = corpus_bundle(Path(temporary))
            before = {name: (root / name).read_bytes() for name in bundle.BUNDLE_FILES}
            records = [("nodes", "goal"), ("evidence", "historical-failure")]
            families = ["arguments", "provenance"]
            with patch.object(consumer, "load_bundle", wraps=bundle.load_bundle) as capture:
                expected = self.query(root, records=records, families=families, max_depth=2)
                self.assertEqual(capture.call_count, 1)
            actual = self.query(root, records=list(reversed(records)),
                                families=list(reversed(families)), max_depth=2)
            self.assertEqual(actual, expected)
            archive = Path(temporary) / "bundle.zip"
            bundle.export_bundle(root, archive)
            self.assertEqual(self.query(archive, records=records, families=families, max_depth=2), expected)
            self.assertEqual(before, {name: (root / name).read_bytes() for name in bundle.BUNDLE_FILES})

    def test_witnesses_choose_shortest_routes_through_a_diamond_and_cycle(self):
        with tempfile.TemporaryDirectory() as temporary:
            graph = synthetic_graph()
            for identifier in ("left", "right", "join", "leaf"):
                graph["nodes"].append({"id": identifier, "kind": "claim", "label": identifier,
                                       "status": "open", "assumption_ids": [],
                                       "citation_ids": [], "evidence_ids": []})
            graph["edges"].extend({"from": source, "to": target, "kind": "supports", "evidence_ids": []}
                                  for source, target in (("goal", "left"), ("goal", "right"),
                                      ("left", "join"), ("right", "join"), ("join", "left"),
                                      ("join", "leaf"), ("goal", "leaf")))
            root = Path(temporary) / "bundle"
            bundle.scaffold(graph, root)
            corpus = consumer.project_corpus(root)
            for seeds, expected in ((["goal"], {"goal": 0, "left": 1, "right": 1, "join": 2, "leaf": 1}),
                                    (["goal", "join"], {"goal": 0, "left": 1, "right": 1, "join": 0, "leaf": 1})):
                with self.subTest(seeds=seeds):
                    result = self.query(root, records=[("nodes", seed) for seed in seeds],
                                        families=["arguments"], direction="outgoing", max_depth=10)
                    rows = pool(result)
                    distances = {rows[row["record_ref"]]["id"]: row["distance"]
                                 for row in result["witnesses"]}
                    for identifier, expected_distance in expected.items():
                        self.assertEqual(distances[identifier], expected_distance)
                    cycle = {record_ref(corpus, "nodes", identifier) for identifier in ("left", "join")}
                    self.assertTrue(any(set(row["members"]) == cycle and row["cyclic"]
                                        for row in result["components"]))
                    self.assert_resolves_without_reorienting(result, corpus)

    def test_cli_json_text_and_controls_use_the_same_validated_records(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = corpus_bundle(Path(temporary))
            argv = ["query-corpus", str(root), "--record", "sources", "public",
                    "--family", "provenance", "--direction", "incoming", "--max-depth", "1"]
            expected = self.query(root, records=[("sources", "public")], families=["provenance"],
                                  direction="incoming", max_depth=1)
            for output_format in ("json", "text"):
                output = io.StringIO()
                with patch.object(consumer, "load_bundle", wraps=bundle.load_bundle) as capture:
                    with contextlib.redirect_stdout(output):
                        status = main(argv + ["--format", output_format])
                    self.assertEqual(capture.call_count, 1)
                self.assertEqual(status, 0)
                if output_format == "json":
                    self.assertEqual(json.loads(output.getvalue()), expected)
                else:
                    self.assertIn(expected["snapshot"]["manifest_sha256"], output.getvalue())
                    self.assertIn("sources/public", output.getvalue())
                    self.assertIn("status=failed", output.getvalue())
                    self.assertIn("short / premise, result", output.getvalue())
            graph = json.loads((root / "graph.json").read_bytes())
            identifier = "line\nbreak\x1b[31m\u202e"
            graph["nodes"].append({"id": identifier, "kind": "claim", "label": identifier,
                                   "status": "open", "assumption_ids": [],
                                   "citation_ids": [], "evidence_ids": []})
            bind(root, graph=graph)
            output = io.StringIO()
            with contextlib.redirect_stdout(output):
                status = main(["query-corpus", str(root), "--record", "nodes", identifier, "--format", "text"])
            self.assertEqual(status, 0)
            self.assertNotIn("\x1b", output.getvalue())
            self.assertNotIn("\u202e", output.getvalue())
            self.assertIn(r"line\u000abreak\u001b[31m\u202e", output.getvalue())

    def test_manifest_pin_covers_mapping_only_change_and_stale_graph_refs_fail(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = corpus_bundle(Path(temporary))
            before = self.query(root, records=[("nodes", "goal")])
            mapping = json.loads((root / "papers/short.json").read_bytes())
            mapping["review_notes"].append("Synthetic metadata change, no review performed.")
            bind(root, mapping=mapping)
            after = self.query(root, records=[("nodes", "goal")])
            self.assertEqual(before["snapshot"]["graph_sha256"], after["snapshot"]["graph_sha256"])
            self.assertNotEqual(before["cache_key"], after["cache_key"])
            with self.assertRaises(ContractError):
                self.query(root, records=[("nodes", "goal")],
                           expected_manifest_sha256=before["snapshot"]["manifest_sha256"])
            stale = before["selected_record_refs"][0]
            graph = json.loads((root / "graph.json").read_bytes())
            graph["notes"].append("Synthetic graph edition change.")
            bind(root, graph=graph)
            with self.assertRaises(ContractError):
                self.query(root, record_refs=[stale])

    def test_statuses_and_record_bytes_are_not_upgraded_by_navigation(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = corpus_bundle(Path(temporary))
            graph = json.loads((root / "graph.json").read_bytes())
            for status in ("unavailable", "not_run", "passed"):
                graph["evidence"].append({**graph["evidence"][0], "id": "check-" + status,
                                          "status": status, "subject_ids": ["goal"]})
            bind(root, graph=graph)
            result = self.query(root, records=[("nodes", "goal")], families=["provenance"],
                                direction="incoming", max_depth=1)
            evidence = {row["record"]["id"]: row["record"] for row in result["records"]["evidence"]}
            for status in ("unavailable", "not_run", "passed"):
                self.assertEqual(evidence["check-" + status]["status"], status)
            self.assertEqual(evidence["historical-failure"]["status"], "failed")
            self.assert_resolves_without_reorienting(result, consumer.project_corpus(root))

    def test_invalid_selectors_and_limits_fail_without_guessing(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = corpus_bundle(Path(temporary))
            cases = [
                {}, {"records": []}, {"record_refs": []},
                {"records": [("nodes", "absent")]},
                {"records": [("papers", "short")]},
                {"records": [("nodes",)]}, {"records": ["goal"]},
                {"record_refs": ["goal"]}, {"record_refs": ["sha256:bad/nodes/goal"]},
            ]
            for options in cases:
                with self.subTest(options=options), self.assertRaises(ContractError):
                    self.query(root, **options)
            bad_options = [
                {"max_depth": -1}, {"max_depth": True}, {"max_depth": 1.5},
                {"max_records": 0}, {"max_records": False}, {"max_records": 1.5},
                {"direction": "consumers"}, {"direction": []},
                {"families": []}, {"families": ["unknown"]},
                {"stage": "unknown"}, {"expected_manifest_sha256": "BAD"},
            ]
            for options in bad_options:
                with self.subTest(options=options), self.assertRaises(ContractError):
                    self.query(root, records=[("nodes", "goal")], **options)


if __name__ == "__main__":
    unittest.main()
