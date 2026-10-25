"""Corpus integration and independent paper-focus contract regressions."""
from __future__ import annotations

import contextlib
import copy
import importlib.util
import io
import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from lean_exposition import bundle
from lean_exposition.cli import main
from lean_exposition.consumer import project_corpus, project_paper, query_papers
from lean_exposition.contracts import ContractError, digest, encoded, validate_artifact
from test_adversarial import synthetic_artifact, synthetic_graph
from test_paper_views import authored_bundle

ROOT = Path(__file__).resolve().parents[1]


def bind(root, *, graph=None, mapping=None, stage="short"):
    """Rebind transport bytes without repairing or broadening claimed scope."""
    if graph is not None:
        (root / "graph.json").write_bytes(encoded(graph))
    for name in bundle.STAGES:
        path = root / f"papers/{name}.json"
        value = mapping if name == stage and mapping is not None else json.loads(path.read_bytes())
        value = copy.deepcopy(value)
        value["graph_sha256"] = digest((root / "graph.json").read_bytes())
        path.write_bytes(encoded(value))
    manifest_path = root / "manifest.json"
    manifest = json.loads(manifest_path.read_bytes())
    for row in manifest["files"]:
        row["sha256"] = digest((root / row["path"]).read_bytes())
    manifest_path.write_bytes(encoded(manifest))


def corpus_bundle(parent):
    root = authored_bundle(parent, cycle=True, formalization=True)
    graph = json.loads((root / "graph.json").read_bytes())
    for name, kind, assumptions in (("outside", "claim", ["outside-premise"]),
                                     ("outside-premise", "assumption", []),
                                     ("isolated", "claim", [])):
        graph["nodes"].append({"id": name, "kind": kind, "label": name, "status": "open",
                               "assumption_ids": assumptions, "citation_ids": [], "evidence_ids": []})
    graph["edges"].extend({"from": "goal", "to": "outside", "kind": kind, "evidence_ids": []}
                           for kind in ("cites", "platform_decomposition"))
    for index, name in enumerate(("goal", "outside"), 1):
        node = next(n for n in graph["nodes"] if n["id"] == name)
        node.update(source_id="public", platform={"provider": "prove2me",
                    "id": f"00000000-0000-0000-0000-{index:012d}", "entity": "theorem",
                    "status": "Unproved", "visibility": "public"})
    graph["evidence"].append({"id": "platform-observation", "kind": "platform_observation",
        "status": "passed", "command": [], "tool": "synthetic fixture", "source_ids": ["public"],
        "subject_ids": ["goal", "outside"], "details": "Synthetic observed labels, not formal proof."})
    graph["edges"][-1]["evidence_ids"] = ["platform-observation"]
    graph["evidence"][0]["subject_ids"].append("outside")
    graph["sources"].append({**graph["sources"][0], "id": "unused-source"})
    graph["citations"].append({**graph["citations"][0], "id": "unused-citation", "source_id": "unused-source"})
    bind(root, graph=graph)
    return root


class PaperFocusTests(unittest.TestCase):
    def focused(self):
        graph = synthetic_graph()
        mapping, content = synthetic_artifact(graph)
        mapping.update(schema_version="1.1", selected_goal_ids=["prerequisite"],
                       claim_ids=["prerequisite"], assumption_ids=[],
                       unresolved_ids=["prerequisite"], citation_ids=["prerequisite-credit"])
        mapping["passages"][0].update(claim_ids=["prerequisite"], assumption_ids=[],
                                      citation_ids=["prerequisite-credit"])
        return graph, mapping, content

    def test_own_goal_can_be_outside_global_focus_legacy_stays_strict(self):
        graph, mapping, content = self.focused()
        validate_artifact(mapping, graph, digest(encoded(graph)), content)
        mapping["schema_version"] = "1.0"
        with self.assertRaisesRegex(ContractError, "changed selected goals"):
            validate_artifact(mapping, graph, digest(encoded(graph)), content)

    def test_scope_and_required_obligations_cannot_be_dropped(self):
        graph, mapping, content = self.focused()
        for field, value in (("selected_goal_ids", []), ("selected_goal_ids", ["absent"]),
                              ("selected_goal_ids", ["goal"]), ("citation_ids", []),
                              ("unresolved_ids", [])):
            with self.subTest(field=field, value=value):
                broken = copy.deepcopy(mapping)
                broken[field] = value
                with self.assertRaises(ContractError):
                    validate_artifact(broken, graph, digest(encoded(graph)), content)

    def test_explicit_assumptions_seed_document_and_passage_requirements(self):
        graph, mapping, content = self.focused()
        graph["nodes"].extend([
            {"id": "extra", "kind": "assumption", "label": "extra", "status": "axiom",
             "assumption_ids": ["hidden"], "citation_ids": [], "evidence_ids": []},
            {"id": "hidden", "kind": "assumption", "label": "hidden", "status": "open",
             "assumption_ids": [], "citation_ids": ["goal-credit"], "evidence_ids": []},
        ])
        mapping["graph_sha256"] = digest(encoded(graph))
        mapping["assumption_ids"] = ["extra"]
        mapping["passages"][0]["assumption_ids"] = ["extra"]
        with self.assertRaisesRegex(ContractError, "assumptions or unresolved"):
            validate_artifact(mapping, graph, mapping["graph_sha256"], content)
        mapping["assumption_ids"].append("hidden")
        mapping["unresolved_ids"].append("hidden")
        with self.assertRaisesRegex(ContractError, "citation"):
            validate_artifact(mapping, graph, mapping["graph_sha256"], content)
        mapping["citation_ids"].append("goal-credit")
        with self.assertRaisesRegex(ContractError, "applicable assumption"):
            validate_artifact(mapping, graph, mapping["graph_sha256"], content)
        mapping["passages"][0]["assumption_ids"].append("hidden")
        with self.assertRaisesRegex(ContractError, "applicable citation"):
            validate_artifact(mapping, graph, mapping["graph_sha256"], content)
        mapping["passages"][0]["citation_ids"].append("goal-credit")
        validate_artifact(mapping, graph, mapping["graph_sha256"], content)

    def test_blank_passage_cannot_count_as_authored(self):
        graph, mapping, _ = self.focused()
        for blank in (b"", b" \n\t"):
            content = b"<!-- passage:result -->" + blank + b"<!-- /passage:result -->"
            mapping["content_sha256"] = digest(content)
            mapping["passages"][0]["text_sha256"] = digest(blank)
            with self.assertRaisesRegex(ContractError, "no text"):
                validate_artifact(mapping, graph, mapping["graph_sha256"], content)


class CorpusViewTests(unittest.TestCase):
    def test_complete_pool_closed_references_separate_relations_and_membership(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = corpus_bundle(Path(temporary))
            graph = json.loads((root / "graph.json").read_bytes())
            view = project_corpus(root)
            pool = {row["ref"]: row["record"] for rows in view["records"].values() for row in rows}
            for table, rows in view["records"].items():
                self.assertEqual(len(rows), len(graph[table]))
                self.assertCountEqual([r["record"] for r in rows], graph[table])
            for family, links in view["relations"].items():
                for link in links:
                    self.assertIn(link["from"], pool)
                    self.assertIn(link["to"], pool)
                    self.assertIn(link["kind"], view["relation_semantics"])
                    self.assertIn(link.get("record_ref", link.get("owner_ref")), pool)
                    if family == "arguments":
                        self.assertNotIn(link["kind"], ("cites", "platform_decomposition", "next_in_text"))
            short = view["papers"][1]
            self.assertEqual(short["storage_profile"], "corpus_shared_records")
            retained = {pool[r]["id"] for r in short["graph"]["record_refs"]["nodes"]}
            self.assertEqual(retained, {"goal", "prerequisite", "assumption", "decl"})
            self.assertTrue(any(c["cyclic"] for c in short["graph"]["components"]))
            usages = {row["record_ref"]: row for row in view["record_usage"]}
            outside_ref = next(r for r, item in pool.items() if item.get("id") == "outside")
            self.assertEqual(usages[outside_ref]["paper_memberships"], [])
            self.assertEqual(usages[outside_ref]["direct_passages"], [])
            self.assertTrue(any(link["kind"] == "subject_ids" and link["to"] == outside_ref
                                for link in view["relations"]["provenance"]))
            for paper in view["papers"]:
                standalone = project_paper(root, paper["stage"])
                expected = copy.deepcopy(standalone)
                expected["storage_profile"] = "corpus_shared_records"
                expected["graph"]["record_refs"] = {table: [r["ref"] for r in rows]
                                                      for table, rows in expected["graph"].pop("records").items()}
                self.assertEqual(paper, expected)
                passage_refs = {p["ref"] for p in paper["paper"]["passages"]}
                for link in paper["correspondence_links"]:
                    self.assertIn(link["from"], passage_refs)
                    self.assertIn(link["to"], pool)
                    self.assertTrue(any(use["passage_ref"] == link["from"] and
                                        use["mapping_field"] == link["source_field"]
                                        for use in usages[link["to"]]["direct_passages"]))
            goal_ref = next(r for r, item in pool.items() if item.get("id") == "goal")
            self.assertEqual([p["stage"] for p in usages[goal_ref]["paper_focus"]], list(bundle.STAGES))
            self.assertEqual([p["stage"] for p in usages[goal_ref]["paper_memberships"]], ["short"])
            self.assertFalse(view["semantic_certification"])
            self.assertEqual(view["graph"]["recorded_extraction_status"], "fixture")

    def test_zip_same_capture_and_cli(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = corpus_bundle(Path(temporary))
            with patch('lean_exposition.consumer.load_bundle', wraps=bundle.load_bundle) as capture:
                expected = project_corpus(root)
                self.assertEqual(capture.call_count, 1)
            archive = Path(temporary) / "corpus.zip"
            bundle.export_bundle(root, archive)
            self.assertEqual(project_corpus(archive), expected)
            output = io.StringIO()
            with contextlib.redirect_stdout(output):
                result = main(["inspect-corpus", str(archive), "--expect-manifest",
                               expected["snapshot"]["manifest_sha256"]])
            self.assertEqual(result, 0)
            self.assertEqual(json.loads(output.getvalue()), expected)

    def test_mapping_only_revision_changes_subgraph_and_cache_not_graph_refs(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = authored_bundle(Path(temporary))
            before = project_corpus(root)
            mapping = json.loads((root / "papers/short.json").read_bytes())
            mapping.update(schema_version="1.1", selected_goal_ids=["prerequisite"])
            bind(root, mapping=mapping)
            after = project_corpus(root)
            self.assertEqual(before["records"], after["records"])
            self.assertEqual(before["papers"][1]["paper"]["text"], after["papers"][1]["paper"]["text"])
            self.assertNotEqual(before["snapshot"]["cache_key"], after["snapshot"]["cache_key"])
            self.assertNotEqual(before["papers"][1]["graph"]["ref"], after["papers"][1]["graph"]["ref"])
            self.assertNotEqual(before["papers"][1]["paper"]["passages"][0]["ref"],
                                after["papers"][1]["paper"]["passages"][0]["ref"])
            self.assertEqual(before["papers"][0]["graph"]["ref"], after["papers"][0]["graph"]["ref"])
            for reader in (project_corpus, query_papers):
                with self.assertRaisesRegex(ContractError, "requested edition"):
                    reader(root, expected_manifest_sha256=before["snapshot"]["manifest_sha256"])
            archive = Path(temporary) / "scoped.zip"
            bundle.export_bundle(root, archive)
            spec = importlib.util.spec_from_file_location("independent", ROOT / "examples/consumer/read_bundle.py")
            independent = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(independent)
            receipt = independent.read_bundle(archive)
            self.assertEqual(receipt["papers"][1]["selected_goal_ids"], ["prerequisite"])
            self.assertFalse(receipt["full_contract_validation"])

    def test_empty_scaffold_and_selector_have_no_invented_support(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary) / "bundle"
            bundle.scaffold(synthetic_graph(), root)
            view = project_corpus(root)
            self.assertTrue(all(not p["graph"]["record_refs"]["nodes"] for p in view["papers"]))
            self.assertTrue(all(not row["paper_memberships"] and not row["direct_passages"]
                                for row in view["record_usage"]))
            self.assertTrue(any(row["paper_focus"] for row in view["record_usage"]))
        with tempfile.TemporaryDirectory() as temporary:
            root = authored_bundle(Path(temporary))
            selected = project_paper(root, "short", [])
            self.assertFalse(selected["graph"]["records"]["nodes"])
            self.assertNotEqual(selected["graph"]["ref"], project_paper(root, "short")["graph"]["ref"])

    def test_invalid_edition_and_transport_fail_before_projection(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = authored_bundle(Path(temporary))
            for value in ("bad", 42, "A" * 64, "0" * 64):
                with self.subTest(value=value), self.assertRaises(ContractError):
                    project_corpus(root, expected_manifest_sha256=value)
            path = root / "papers/short.md"
            path.write_bytes(path.read_bytes() + b"changed")
            with self.assertRaises(ContractError):
                project_corpus(root)


if __name__ == "__main__":
    unittest.main()
