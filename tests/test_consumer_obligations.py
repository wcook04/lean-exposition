"""Consumer regressions for scoped premises, documentary credit and pagination.

Extraction receipts in these fixtures are synthetic; no Lean process is run.
"""
from __future__ import annotations

import copy
import json
import tempfile
import unittest
from pathlib import Path

from lean_exposition import bundle, consumer
from lean_exposition.contracts import (digest, encoded, extraction_projection_digest,
                                       formal_result_assurances, write_json)
from lean_exposition.extraction import to_graph
from test_adversarial import synthetic_artifact
from test_application_obligations import extracted_application
from test_core_review import extraction_fixture, rebind
from test_reading_views import reading_bundle
from test_scoped_applications import application_bundle, application_graph, node
from test_typed_views import PLATFORM


class ConsumerObligationTests(unittest.TestCase):
    def test_witness_tree_retains_formal_obligations_in_the_application_scope(self):
        for obligation in ("Classical.choice", "sorryAx"):
            with self.subTest(obligation=obligation), tempfile.TemporaryDirectory() as tmp:
                graph = extracted_application(Path(tmp), obligation)
                adjacency = consumer._argument_adjacency(graph, digest(encoded(graph)))
                paths = consumer._witness_tree(graph, adjacency, {"consumer"})
                self.assertIn(obligation, paths)
                root, links = paths[obligation]
                self.assertEqual(root, "consumer")
                self.assertEqual([(link["from_node_id"], link["to_node_id"]) for link in links],
                                 [("consumer", "result"), ("result", obligation)])
                self.assertEqual(links[0]["application_scope"]["to_discharged"], [obligation])
                self.assertEqual(links[1]["application_scope"]["from_discharged"], [obligation])
                self.assertEqual(links[1]["application_scope"]["to_discharged"], [])
                self.assertIn("historical metadata", links[0]["application_metadata_scope"])
                view = consumer.project_graph(encoded(graph), "arguments", ["consumer"],
                                              include_assumptions=True)
                self.assertIn(obligation, {row["record"]["id"] for row in view["records"]["nodes"]})
                self.assertIn(obligation, view["coverage"]["effective_retained_assumption_ids"])

    def test_witness_tree_still_discharges_informal_use_but_keeps_independent_use(self):
        graph = application_graph()
        adjacency = consumer._argument_adjacency(graph, digest(encoded(graph)))
        paths = consumer._witness_tree(graph, adjacency, {"goal"})
        self.assertNotIn("assumption", paths)
        graph["nodes"].append(node("independent", "claim", "unverified", ["assumption"]))
        graph["edges"].append({"from": "goal", "to": "independent", "kind": "supports",
                               "evidence_ids": []})
        adjacency = consumer._argument_adjacency(graph, digest(encoded(graph)))
        paths = consumer._witness_tree(graph, adjacency, {"goal"})
        self.assertEqual([link["from_node_id"] for link in paths["assumption"][1]],
                         ["goal", "independent"])

    def test_argument_view_audits_formal_obligations_beyond_its_edge_filter(self):
        with tempfile.TemporaryDirectory() as tmp:
            parent = Path(tmp)
            report, _ = extraction_fixture(parent)
            result = report["declarations"][0]
            helper = copy.deepcopy(result)
            result["value_dependencies"] = ["helper"]
            helper.update(name="helper", value_dependencies=["sorryAx"],
                          axioms=["sorryAx"], has_sorry=True)
            report["declarations"].append(helper)
            report["external_dependencies"].append({"name": "sorryAx", "module": "Init.Prelude",
                                                       "kind": "axiom", "reason": "outside_module_prefixes"})
            rebind(report)
            graph = to_graph(report, parent)
            graph["schema_version"] = "1.2"
            graph["selected_goals"] = ["consumer"]
            graph["nodes"].extend([node("consumer", "claim", "unverified"),
                                   node("supplier", "claim", "unverified")])
            graph["edges"].extend([
                {"from": "consumer", "to": "result", "kind": "supports", "evidence_ids": [],
                 "application": {"status": "authored", "shared_bindings": {"x": "synthetic"},
                    "premise_bindings": [{"assumption_id": "sorryAx", "supplier_id": "supplier",
                                          "binding_names": ["x"], "rationale": "Synthetic use."}],
                    "remaining_assumption_ids": [],
                    "source_span": {"source_id": graph["sources"][0]["id"], "start_line": 1, "end_line": 1},
                    "rationale": "Synthetic use, not a Lean substitution."}},
                {"from": "consumer", "to": "supplier", "kind": "supports", "evidence_ids": []},
            ])
            premise = next(n for n in graph["nodes"] if n["id"] == "sorryAx")
            premise.update(id="aliased-hole", declaration="sorryAx", label="aliased-hole")
            for item in graph["nodes"]:
                item["assumption_ids"] = ["aliased-hole" if n == "sorryAx" else n for n in item["assumption_ids"]]
            for edge in graph["edges"]:
                if edge["to"] == "sorryAx":
                    edge["to"] = "aliased-hole"
                if "application" in edge:
                    edge["application"]["premise_bindings"][0]["assumption_id"] = "aliased-hole"
            evidence = next(e for e in graph["evidence"] if e["kind"] == "extraction")
            evidence["receipt"]["projection_sha256"] = extraction_projection_digest(
                graph, evidence["subject_ids"], profile="lean-extraction-v2")
            view = consumer.project_graph(encoded(graph), "arguments", ["consumer"], include_assumptions=True)
            self.assertNotIn("helper", {row["record"]["id"] for row in view["records"]["nodes"]})
            self.assertEqual(view["coverage"]["effective_retained_assumption_ids"], ["aliased-hole"])
            self.assertIn("Lean dependency edges", view["coverage"]["effective_assumptions_scope"])

    def test_citation_view_keeps_bound_premise_credit_without_freeing_its_assumption(self):
        graph = application_graph()
        for name in ("premise-credit", "cited-credit"):
            graph["citations"].append({"id": name, "title": name, "source_id": "public",
                                       "url": "https://example.org/credit", "locator": name})
        next(n for n in graph["nodes"] if n["id"] == "assumption")["citation_ids"] = ["premise-credit"]
        cited = node("cited-work", "claim", "unverified", ["cited-assumption"])
        cited["citation_ids"] = ["cited-credit"]
        graph["nodes"].extend([cited, node("cited-assumption", "assumption", "axiom")])
        graph["edges"].append({"from": "assumption", "to": "cited-work", "kind": "cites",
                               "evidence_ids": []})
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "bundle"
            bundle.scaffold(graph, root)
            session = consumer.ConsumerSession(root)
            for source in (encoded(graph), session):
                with self.subTest(source=type(source).__name__):
                    citations = consumer.project_graph(source, "citations", ["goal"])
                    ids = {row["record"]["id"] for row in citations["records"]["citations"]}
                    self.assertTrue({"premise-credit", "cited-credit"} <= ids)
                    self.assertTrue(any(link["kind"] == "cites" and
                                        link["from"].endswith("/nodes/assumption") and
                                        link["to"].endswith("/nodes/cited-work")
                                        for link in citations["links"]))
                    arguments = consumer.project_graph(source, "arguments", ["goal"],
                                                       include_assumptions=True)
                    nodes = {row["record"]["id"] for row in arguments["records"]["nodes"]}
                    self.assertNotIn("assumption", nodes)
                    self.assertNotIn("cited-assumption", nodes)
                    self.assertEqual(arguments["coverage"]["effective_retained_assumption_ids"], [])

    def test_historical_passage_exposes_missing_effective_documentary_credit(self):
        graph = application_graph()
        graph["citations"].append({"id": "premise-credit", "title": "premise-credit",
                                   "source_id": "public", "url": "https://example.org/credit",
                                   "locator": "premise-credit"})
        next(n for n in graph["nodes"] if n["id"] == "assumption")["citation_ids"] = ["premise-credit"]
        with tempfile.TemporaryDirectory() as tmp:
            parent = Path(tmp)
            scaffold = parent / "scaffold"
            bundle.scaffold(graph, scaffold)
            mapping, content = synthetic_artifact(graph)
            mapping["assumption_ids"] = []
            mapping["passages"][0]["assumption_ids"] = []
            mapping["unresolved_ids"].append("supplier")
            mapping["citation_ids"].append("premise-credit")
            mapping["passages"][0]["citation_ids"].append("premise-credit")
            paper, map_path = parent / "long.md", parent / "long.json"
            paper.write_bytes(content)
            write_json(map_path, mapping)
            root = parent / "bundle"
            bundle.assemble_bundle(scaffold / "graph.json", {
                stage: (paper, map_path) if stage == "long" else
                (scaffold / f"papers/{stage}.md", scaffold / f"papers/{stage}.json")
                for stage in bundle.STAGES
            }, root)
            # A previously captured mapping may satisfy historical validation
            # while omitting a supplied premise's documentary credit.
            mapping_path = root / "papers/long.json"
            historical = json.loads(mapping_path.read_bytes())
            historical["citation_ids"].remove("premise-credit")
            historical["passages"][0]["citation_ids"].remove("premise-credit")
            write_json(mapping_path, historical)
            manifest_path = root / "manifest.json"
            manifest = json.loads(manifest_path.read_bytes())
            for entry in manifest["files"]:
                if entry["path"] == "papers/long.json":
                    entry["sha256"] = digest(mapping_path.read_bytes())
            write_json(manifest_path, manifest)
            projected = consumer.project_paper(root, "long")
            audit = projected["coverage"]["passage_citation_audits"][0]
            self.assertEqual(audit["missing_effective_citation_ids"], ["premise-credit"])
            self.assertEqual(projected["coverage"]["document_citation_audit"]["missing_effective_citation_ids"],
                             ["premise-credit"])
            self.assertIn("premise-credit", {r["record"]["id"] for r in projected["graph"]["records"]["citations"]})
            self.assertNotIn("assumption", {r["record"]["id"] for r in projected["graph"]["records"]["nodes"]})
            result = consumer.query_papers(root, stage="long", passages=["result"], include_views=False)
            self.assertEqual(result["papers"][0]["matches"][0]["missing_effective_citation_ids"],
                             ["premise-credit"])
            self.assertEqual(result["papers"][0]["document_citation_audit"]["missing_effective_citation_ids"],
                             ["premise-credit"])
            full = consumer.query_papers(root, stage="long", passages=["result"])
            self.assertEqual(result["papers"][0]["document"]["coverage"],
                             full["papers"][0]["view"]["coverage"])
            self.assertFalse(result["semantic_certification"])

    def test_formal_assurance_is_returned_without_upgrading_legacy_status(self):
        with tempfile.TemporaryDirectory() as tmp:
            parent = Path(tmp)
            report, build = extraction_fixture(parent)
            legacy = copy.deepcopy(report)
            legacy["schema_version"] = 1
            legacy["receipt"].pop("report_schema_version")
            for declaration in legacy["declarations"]:
                declaration.pop("is_unsafe")
                declaration.pop("is_partial")
            rebind(legacy)
            graph = to_graph(legacy, parent, build)
            next(n for n in graph["nodes"] if n["id"] == "result")["status"] = "kernel_checked"
            view = consumer.project_graph(encoded(graph), "arguments", ["result"])
            actual = view["coverage"]["formal_result_assurances"]
            self.assertEqual(actual, formal_result_assurances(graph, ["result"]))
            self.assertFalse(actual["result"]["formal_result_eligible"])
            self.assertEqual(actual["result"]["safety_classification"], "legacy_or_unknown_safety")
            self.assertIn("no execution authentication", actual["result"]["scope"])
            inspection = consumer.inspect_graph(graph)
            self.assertEqual(inspection["formal_result_assurances"]["result"], actual["result"])
            root = parent / "bundle"
            bundle.scaffold(graph, root)
            for source in (root, consumer.ConsumerSession(root)):
                record = consumer.query_corpus(source, records=[("nodes", "result")], max_depth=0)
                self.assertEqual(record["records"]["nodes"][0]["formal_result_assurance"], actual["result"])
            current = to_graph(report, parent, build)
            view = consumer.project_graph(encoded(current), "arguments", ["result"])
            checked = view["coverage"]["formal_result_assurances"]["result"]
            self.assertEqual(checked["safety_classification"], "recorded_safe_v2")
            self.assertFalse(checked["formal_result_eligible"])
            extracted = next(item for item in current["evidence"] if item["kind"] == "extraction")
            extracted["receipt"].update(
                extraction_request={"module": "Minimal", "roots": ["result"],
                                    "module_prefixes": ["Minimal"], "max_declarations": 1},
                report_stdout_binding="lean-report-stdout-v1", process_status="passed",
                extractor_sha256="a" * 64, extractor_template_sha256="b" * 64,
                stdout_utf8_valid=True, stdout_sha256="c" * 64, stdout_bytes_sha256="c" * 64)
            next(item for item in current["evidence"] if item["kind"] == "lean_build")["receipt"]["process_status"] = "passed"
            eligible = consumer.project_graph(encoded(current), "arguments", ["result"])
            assurance = eligible["coverage"]["formal_result_assurances"]["result"]
            self.assertTrue(assurance["formal_result_eligible"])
            self.assertEqual(assurance["assurance_state"], "current_observations")
            self.assertIn("no execution authentication", assurance["scope"])

    def test_platform_group_metadata_is_optional_and_preserved(self):
        graph = json.loads(PLATFORM.read_bytes())
        legacy = consumer.project_graph(encoded(graph), "platform")
        self.assertNotIn("platform_deprecation", legacy["coverage"]["platform_observations"][0]["recorded"])
        observation = next(e for e in graph["evidence"] if e["kind"] == "platform_observation")
        metadata = {"entities": [], "groups": []}
        observation["receipt"]["platform_deprecation"] = metadata
        view = consumer.project_graph(encoded(graph), "platform")
        self.assertEqual(view["coverage"]["platform_observations"][0]["recorded"]["platform_deprecation"],
                         metadata)
        self.assertIn("older receipts", view["coverage"]["platform_grouping"])

    def test_paper_boundary_distinguishes_explicit_mapping_from_scoped_discharge(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = application_bundle(Path(tmp))
            mapping_path = root / "papers/long.json"
            mapping = json.loads(mapping_path.read_bytes())
            mapping["assumption_ids"].append("assumption")
            mapping["passages"][0]["assumption_ids"].append("assumption")
            write_json(mapping_path, mapping)
            manifest_path = root / "manifest.json"
            manifest = json.loads(manifest_path.read_bytes())
            for entry in manifest["files"]:
                if entry["path"] == "papers/long.json":
                    entry["sha256"] = digest(mapping_path.read_bytes())
            write_json(manifest_path, manifest)
            result = consumer.query_papers(root, stage="long", passages=["result"])
            boundary = result["papers"][0]["support_boundary"]
            self.assertIn("assumption", boundary["mapped_assumption_ids"])
            self.assertIn("assumption", boundary["required_assumption_ids"])
            self.assertIn("whole-passage", boundary["meaning"])
            self.assertIn("not a list of undischarged premises", boundary["meaning"])
            view = consumer.project_graph((root / "graph.json").read_bytes(), "arguments", ["goal"],
                                          include_assumptions=True)
            self.assertNotIn("assumption", {row["record"]["id"] for row in view["records"]["nodes"]})

    def test_reading_truncation_depends_on_actual_omitted_links(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = reading_bundle(Path(tmp))
            empty = consumer.query_reading(root, stage="short", target_stage="short", offset=1, limit=1)
            self.assertEqual(empty["pagination"]["total"], 0)
            self.assertEqual(empty["links"], [])
            self.assertFalse(empty["coverage"]["query_truncated"])
            first = consumer.query_reading(root, stage="short", target_stage="long", offset=0, limit=1)
            self.assertGreater(first["pagination"]["total"], 1)
            self.assertTrue(first["coverage"]["query_truncated"])
            full = consumer.query_reading(root, stage="short", target_stage="long", offset=0, limit=1000)
            self.assertFalse(full["coverage"]["query_truncated"])
            after = consumer.query_reading(root, stage="short", target_stage="long", offset=1000, limit=1)
            self.assertEqual(after["links"], [])
            self.assertTrue(after["coverage"]["query_truncated"])


if __name__ == "__main__":
    unittest.main()
