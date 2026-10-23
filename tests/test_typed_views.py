"""Typed consumer projections using synthetic fixtures and retained graph bytes.

No test invokes Lean, Comparator, platform intake, or a mathematical review.
"""
from __future__ import annotations

import contextlib
import io
import json
from pathlib import Path
import unittest

from lean_exposition.cli import main
from lean_exposition.consumer import inspect_graph, project_graph
from lean_exposition.contracts import ContractError, digest, encoded
from test_adversarial import synthetic_graph
from test_graph_adversarial import graph_with_cited_claim, synthetic_node

ROOT = Path(__file__).resolve().parents[1]
MINIMAL = ROOT / "examples/minimal/evidence-graph.json"
QAOA = ROOT / "examples/qaoa-sk/evidence-graph.json"
PLATFORM = ROOT / "examples/prove2me/full-support/graph.json"


def ids(view, table="nodes"):
    return {row["record"]["id"] for row in view["records"][table]}


def observation(identity, subject, status="failed"):
    return {"id": identity, "kind": "source_hash", "status": status,
            "command": [], "tool": "synthetic fixture", "source_ids": ["public"],
            "subject_ids": [subject], "details": "Synthetic record; no check executed."}


class TypedViewTests(unittest.TestCase):
    def test_relation_orientations_and_reverse_queries_keep_recorded_endpoints(self):
        citations = graph_with_cited_claim()
        cases = [
            (MINIMAL.read_bytes(), "declarations", ["Minimal.result"], "lean_type_dependency"),
            (encoded(synthetic_graph()), "arguments", ["goal"], "supports"),
            (QAOA.read_bytes(), "arguments", ["full_support"], "formalizes"),
            (encoded(citations), "citations", ["goal"], "cites"),
            (PLATFORM.read_bytes(), "platform", None, "platform_decomposition"),
            (encoded(synthetic_graph()), "provenance", ["goal"], "assumption_ids"),
        ]
        for raw, view_name, roots, kind in cases:
            with self.subTest(view=view_name, kind=kind):
                view = project_graph(raw, view_name, roots)
                self.assertTrue(view["traversal"]["recorded_from_to"])
                self.assertNotIn("stored_edge_direction", view["traversal"])
                self.assertEqual(view["relation_scope"], "recorded_relation_reachability")
                semantics = view["relation_semantics"][kind]
                self.assertEqual(view["traversal"]["orientation_by_kind"][kind],
                                 semantics["orientation"])
                self.assertTrue(all(link["semantic_class"] == view["relation_semantics"][link["kind"]]["semantic_class"]
                                    for link in view["links"]))
        reverse_cases = [
            (MINIMAL.read_bytes(), "declarations", ["And"], "lean_type_dependency"),
            (encoded(synthetic_graph()), "arguments", ["prerequisite"], "supports"),
            (QAOA.read_bytes(), "arguments", ["lean.full_support"], "formalizes"),
        ]
        platform_graph = json.loads(PLATFORM.read_bytes())
        target = next(edge["to"] for edge in platform_graph["edges"]
                      if edge["kind"] == "platform_decomposition")
        reverse_cases.append((PLATFORM.read_bytes(), "platform", [target], "platform_decomposition"))
        for raw, view_name, roots, kind in reverse_cases:
            with self.subTest(reverse=view_name, kind=kind):
                view = project_graph(raw, view_name, roots, direction="consumers")
                graph = json.loads(raw)
                stored = {(edge["from"], edge["to"], edge["kind"]) for edge in graph["edges"]}
                links = [link for link in view["links"] if link["kind"] == kind]
                self.assertTrue(links)
                for link in links:
                    from_id = next(row["record"]["id"] for row in view["records"]["nodes"]
                                   if row["ref"] == link["from"])
                    to_id = next(row["record"]["id"] for row in view["records"]["nodes"]
                                 if row["ref"] == link["to"])
                    self.assertIn((from_id, to_id, kind), stored)
        for view_name in ("citations", "provenance"):
            with self.assertRaises(ContractError):
                project_graph(encoded(citations), view_name, ["goal"], direction="consumers")

    def test_condensation_preserves_parallel_kinds_and_provenance_cycles(self):
        graph = synthetic_graph()
        graph["nodes"].append({"id": "decl", "kind": "declaration", "label": "decl",
                               "status": "unverified", "declaration": "Synthetic.decl",
                               "statement": "True", "source_id": "public",
                               "assumption_ids": [], "citation_ids": [], "evidence_ids": []})
        graph["edges"].extend([
            {"from": "goal", "to": "decl", "kind": "supports", "evidence_ids": []},
            {"from": "goal", "to": "decl", "kind": "formalizes", "evidence_ids": []},
        ])
        argument = project_graph(encoded(graph), "arguments", ["goal"])
        self.assertTrue(any(set(link["link_kinds"]) == {"supports", "formalizes"}
                            for link in argument["condensation"]))
        self.assertEqual({link["kind"] for link in argument["links"]},
                         {"supports", "formalizes"})
        graph["evidence"].append(observation("review", "goal", "failed"))
        graph["nodes"][0]["evidence_ids"].append("review")
        provenance = project_graph(encoded(graph), "provenance", ["goal"])
        cycle = next(component for component in provenance["components"]
                     if {"evidence_ids", "subject_ids"} <= set(component["internal_link_kinds"]))
        self.assertTrue(cycle["cyclic"])
        self.assertEqual(provenance["relation_scope"], "recorded_relation_reachability")
        self.assertEqual(provenance["relation_semantics"]["subject_ids"]["semantic_class"],
                         "provenance_field_reference")

    def test_default_inspect_output_remains_the_existing_interface(self):
        output, errors = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(output), contextlib.redirect_stderr(errors):
            code = main(["inspect", str(QAOA), "--goal", "scalar_value"])
        self.assertEqual(code, 0, errors.getvalue())
        self.assertEqual(json.loads(output.getvalue()),
                         inspect_graph(json.loads(QAOA.read_bytes()), ["scalar_value"]))

    def test_query_roots_do_not_rebind_hash_or_selected_goals(self):
        raw = QAOA.read_bytes()
        original = json.loads(raw)
        view = project_graph(raw, "arguments", ["scalar_value"])
        self.assertEqual(view["graph_sha256"], digest(raw))
        self.assertEqual(view["selected_goals"], original["selected_goals"])
        self.assertEqual(view["requested_roots"], ["scalar_value"])
        self.assertEqual(QAOA.read_bytes(), raw)
        self.assertEqual(view["coverage"]["recorded_extraction_status"], "not_run")

    def test_declaration_view_preserves_parallel_edge_kinds(self):
        view = project_graph(MINIMAL.read_bytes(), "declarations")
        edges = [row["record"] for row in view["records"]["edges"]]
        pair = [e for e in edges if e["from"] == "Minimal.result" and e["to"] == "And"]
        self.assertEqual({e["kind"] for e in pair},
                         {"lean_type_dependency", "lean_value_dependency"})
        self.assertTrue(all(not link["derived"] for link in view["links"]))
        self.assertEqual(view["coverage"]["recorded_extraction_status"], "partial")

    def test_declaration_view_rejects_implicit_formalization_seed(self):
        with self.assertRaisesRegex(ContractError, "choose the formalized declaration"):
            project_graph(QAOA.read_bytes(), "declarations")
        view = project_graph(QAOA.read_bytes(), "declarations", ["lean.full_support"])
        self.assertEqual(ids(view), {"lean.full_support"})
        self.assertEqual(view["links"], [])
        self.assertIn("not a proof of independence", view["coverage"]["empty_result_meaning"])

    def test_assumptions_are_explicit_field_references(self):
        graph = synthetic_graph()
        without = project_graph(encoded(graph), "arguments")
        with_assumptions = project_graph(encoded(graph), "arguments", include_assumptions=True)
        self.assertEqual(ids(without), {"goal", "prerequisite"})
        self.assertEqual(ids(with_assumptions), {"goal", "prerequisite", "assumption"})
        extra = [link for link in with_assumptions["links"] if link["derived"]]
        self.assertEqual(len(extra), 1)
        self.assertEqual(extra[0]["kind"], "assumption_ids")
        self.assertEqual(graph, synthetic_graph())

    def test_citation_closure_keeps_credit_and_cited_evidence_without_assumptions(self):
        graph = graph_with_cited_claim()
        graph["evidence"].append(observation("cited-review", "cited-claim", "unavailable"))
        graph["nodes"][3]["evidence_ids"] = ["cited-review"]
        graph["edges"].append({"from": "cited-claim", "to": "goal",
                               "kind": "cites", "evidence_ids": []})
        view = project_graph(encoded(graph), "citations")
        self.assertIn("cited-claim", ids(view))
        self.assertNotIn("cited-assumption", ids(view))
        self.assertNotIn("cited-prerequisite", ids(view))
        self.assertIn("cited-credit", ids(view, "citations"))
        item = next(r for r in view["records"]["evidence"] if r["record"]["id"] == "cited-review")
        self.assertTrue(item["relevant"])
        self.assertEqual(item["record"]["status"], "unavailable")
        self.assertEqual(view["traversal"]["citation_seeds"], "argument_closure")
        self.assertEqual({link["kind"] for link in view["links"]}, {"cites"})

    def test_cycles_condense_without_losing_internal_links(self):
        graph = synthetic_graph()
        graph["edges"].extend([
            {"from": "prerequisite", "to": "goal", "kind": "supports", "evidence_ids": []},
            {"from": "goal", "to": "goal", "kind": "supports", "evidence_ids": []},
        ])
        view = project_graph(encoded(graph), "arguments")
        self.assertEqual(len(view["components"]), 1)
        self.assertTrue(view["components"][0]["cyclic"])
        self.assertEqual(len(view["components"][0]["internal_link_ids"]), 3)
        self.assertEqual(view["condensation"], [])
        self.assertEqual(view, project_graph(encoded(graph), "arguments"))

    def test_singleton_self_loop_is_cyclic(self):
        graph = synthetic_graph()
        graph["edges"] = [{"from": "goal", "to": "goal", "kind": "supports", "evidence_ids": []}]
        view = project_graph(encoded(graph), "arguments")
        self.assertEqual(len(view["components"][0]["members"]), 1)
        self.assertTrue(view["components"][0]["cyclic"])

    def test_deep_chain_uses_iterative_components_and_groups_every_link_once(self):
        graph = synthetic_graph()
        count = 1200
        graph["selected_goals"] = ["n0"]
        graph["nodes"] = [synthetic_node(f"n{i}") for i in range(count)]
        graph["edges"] = [{"from": f"n{i}", "to": f"n{i + 1}",
                           "kind": "supports", "evidence_ids": []}
                          for i in range(count - 1)]
        graph["edges"].append({"from": f"n{count - 1}", "to": f"n{count - 2}",
                               "kind": "supports", "evidence_ids": []})
        view = project_graph(encoded(graph), "arguments")
        self.assertEqual(len(view["components"]), count - 1)
        cyclic = [component for component in view["components"] if component["cyclic"]]
        self.assertEqual(len(cyclic), 1)
        self.assertEqual(len(cyclic[0]["members"]), 2)
        internal = [identity for component in view["components"]
                    for identity in component["internal_link_ids"]]
        external = [identity for link in view["condensation"] for identity in link["link_ids"]]
        self.assertEqual(len(internal), 2)
        self.assertEqual(len(external), count - 2)
        self.assertEqual(len(set(internal + external)), len(view["links"]))
        self.assertEqual(set(internal + external), {link["id"] for link in view["links"]})
        self.assertTrue(view["coverage"]["stored_traversal_exhausted"])
        self.assertFalse(view["coverage"]["query_truncated"])
        self.assertEqual(view["coverage"]["per_root_dependency_completeness"], "unknown")

    def test_reverse_impact_keeps_stored_direction(self):
        view = project_graph(encoded(synthetic_graph()), "arguments", ["prerequisite"], direction="consumers")
        self.assertEqual(ids(view), {"goal", "prerequisite"})
        edge = view["records"]["edges"][0]["record"]
        self.assertEqual((edge["from"], edge["to"]), ("goal", "prerequisite"))
        self.assertEqual(view["traversal"]["direction"], "consumers")

    def test_platform_coverage_and_local_statuses_stay_separate(self):
        raw = PLATFORM.read_bytes()
        view = project_graph(raw, "platform")
        receipt = view["coverage"]["platform_observations"][0]["recorded"]
        self.assertEqual(receipt["platform_closure_status"], "partial")
        self.assertEqual(receipt["local_verification"], "not_run")
        self.assertEqual(receipt["omissions"]["definition_dependencies_not_expanded"], 2)
        self.assertEqual({r["record"]["status"] for r in view["records"]["nodes"]}, {"unverified"})
        self.assertIn("union_for_navigation", view["coverage"]["platform_grouping"])
        self.assertFalse(view["coverage"]["source_bytes_opened"])
        self.assertFalse(view["semantic_certification"])

    def test_provenance_seeds_unlinked_failed_receipts_and_preserves_record_namespaces(self):
        graph = synthetic_graph()
        graph["evidence"].append(observation("goal", "goal"))
        graph["sources"].append({"id": "goal", "kind": "synthetic", "url": "urn:synthetic:goal",
                                  "revision": "fixture", "license": "CC0-1.0", "redistribution": "original"})
        graph["nodes"][0]["source_id"] = "goal"
        graph["evidence"][0]["subject_ids"].append("prerequisite")
        view = project_graph(encoded(graph), "provenance")
        refs = {table: next(r["ref"] for r in view["records"][table] if r["record"]["id"] == "goal")
                for table in ("nodes", "sources", "evidence")}
        self.assertEqual(len(set(refs.values())), 3)
        self.assertIn(refs["evidence"], view["seed_record_refs"])
        self.assertFalse(any(link["from"] == refs["nodes"] and link["to"] == refs["evidence"]
                             for link in view["links"]))
        self.assertIn("prerequisite", ids(view))
        self.assertEqual(view["records"]["evidence"][0]["record"]["status"], "failed")
        self.assertTrue(all(link["derived"] for link in view["links"]))

    def test_evidence_outside_selection_is_still_visible(self):
        graph = synthetic_graph()
        graph["nodes"].append(synthetic_node("adjacent-open", status="open"))
        graph["evidence"].append(observation("adjacent-failed", "adjacent-open"))
        view = project_graph(encoded(graph), "arguments")
        item = view["records"]["evidence"][0]
        self.assertEqual(item["record"]["status"], "failed")
        self.assertFalse(item["relevant"])
        self.assertNotIn("adjacent-open", ids(view))

    def test_exact_bytes_and_encoded_ids_define_snapshot_handles(self):
        graph = synthetic_graph()
        graph["nodes"].extend([synthetic_node("x/y"), synthetic_node("x%2Fy")])
        raw = encoded(graph)
        view = project_graph(raw, "arguments", ["x/y", "x%2Fy"])
        refs = [r["ref"] for r in view["records"]["nodes"]]
        self.assertEqual(len(set(refs)), 2)
        self.assertTrue(any("x%2Fy" in r for r in refs))
        self.assertTrue(any("x%252Fy" in r for r in refs))
        changed = project_graph(raw + b"\n", "arguments", ["x/y", "x%2Fy"])
        self.assertNotEqual(view["graph_sha256"], changed["graph_sha256"])

    def test_unsupported_queries_fail_instead_of_guessing(self):
        raw = encoded(synthetic_graph())
        cases = [
            {"view": "unknown"}, {"view": "arguments", "direction": "sideways"},
            {"view": []}, {"view": "arguments", "direction": []},
            {"view": "citations", "direction": "consumers"},
            {"view": "provenance", "direction": "consumers"},
            {"view": "platform", "include_assumptions": True},
            {"view": "arguments", "include_assumptions": 1},
            {"view": "arguments", "roots": []}, {"view": "arguments", "roots": ["missing"]},
            {"view": "arguments", "roots": ["goal", "goal"]},
        ]
        for kwargs in cases:
            with self.subTest(kwargs=kwargs), self.assertRaises(ContractError):
                project_graph(raw, **kwargs)
        with self.assertRaises(ContractError):
            project_graph(raw.decode(), "arguments")

    def test_cli_opt_in_and_options_without_view(self):
        output, errors = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(output), contextlib.redirect_stderr(errors):
            code = main(["inspect", str(MINIMAL), "--view", "declarations"])
        self.assertEqual(code, 0, errors.getvalue())
        self.assertEqual(json.loads(output.getvalue())["view"], "declarations")
        with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(errors):
            code = main(["inspect", str(QAOA), "--include-assumptions"])
        self.assertEqual(code, 1)
        self.assertIn("require --view", errors.getvalue())


if __name__ == "__main__":
    unittest.main()
