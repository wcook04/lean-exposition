"""Read-only paper projections from validated synthetic bundles."""
from __future__ import annotations

import contextlib
import io
import json
import tempfile
import unittest
from pathlib import Path

from lean_exposition import bundle
from lean_exposition.cli import main
from lean_exposition.consumer import project_paper
from lean_exposition.contracts import (
    ContractError, digest, encoded, required_citation_ids, validate_graph, write_json,
)
from test_adversarial import synthetic_graph


def authored_bundle(root: Path, *, cycle: bool = False, formalization: bool = False) -> Path:
    graph = synthetic_graph()
    if cycle:
        graph["edges"].append({"from": "goal", "to": "goal", "kind": "supports", "evidence_ids": []})
    if formalization:
        graph["nodes"].append({"id": "decl", "kind": "declaration", "label": "Synthetic.decl",
                               "status": "unverified", "source_id": "public",
                               "declaration": "Synthetic.decl", "statement": "True",
                               "assumption_ids": [], "citation_ids": [], "evidence_ids": []})
        graph["edges"].append({"from": "goal", "to": "decl", "kind": "formalizes",
                               "evidence_ids": []})
    graph["evidence"].append({
        "id": "historical-failure", "kind": "source_hash", "status": "failed",
        "command": [], "tool": "synthetic fixture", "source_ids": ["public"],
        "subject_ids": ["goal"], "details": "Historical failure remains recorded.",
    })
    graph["nodes"][0]["evidence_ids"].append("historical-failure")
    scaffold = root / "scaffold"
    bundle.scaffold(graph, scaffold)
    p2 = "\nA prerequisite is recorded.\n"
    p1 = "\nThe μ-result depends on a premise.\n"
    content = ("---\ntitle: Synthetic\n# YAML pseudo-heading\n---\n"
               "# Paper\n```md\n# Fenced pseudo-heading\n```\n"
               "## Result\n<!-- passage:premise -->" + p2 + "<!-- /passage:premise -->\n"
               "## Result\n<!-- passage:result -->" + p1 + "<!-- /passage:result -->\n"
               "Outside the mapped passages.\n").encode("utf-8")
    mapping = {
        "schema_version": "1.0", "stage": "short", "state": "draft",
        "path": "papers/short.md", "content_sha256": digest(content),
        "graph_sha256": digest(encoded(graph)), "selected_goal_ids": ["goal"],
        "claim_ids": ["goal", "prerequisite"],
        "citation_ids": ["goal-credit", "prerequisite-credit"],
        "assumption_ids": ["assumption"],
        "unresolved_ids": ["goal", "prerequisite"] + (["decl"] if formalization else []),
        "passages": [
            {"anchor": "result", "text_sha256": digest(p1.encode()),
             "claim_ids": ["goal"], "citation_ids": ["goal-credit", "prerequisite-credit"],
             "assumption_ids": ["assumption"], "evidence_class": "source_argument",
             "rationale": "Synthetic source correspondence."},
            {"anchor": "premise", "text_sha256": digest(p2.encode()),
             "claim_ids": ["prerequisite"], "citation_ids": ["prerequisite-credit"],
             "assumption_ids": [], "evidence_class": "source_argument",
             "rationale": "Synthetic prerequisite correspondence."},
        ],
        "review_state": "not_reviewed", "review_notes": [],
    }
    paper = root / "short.md"
    mapping_path = root / "short.json"
    paper.write_bytes(content)
    write_json(mapping_path, mapping)
    result = root / "bundle"
    bundle.assemble_bundle(scaffold / "graph.json", {
        "long": (scaffold / "papers/long.md", scaffold / "papers/long.json"),
        "short": (paper, mapping_path),
        "expository": (scaffold / "papers/expository.md", scaffold / "papers/expository.json"),
    }, result)
    return result


class PaperViewTests(unittest.TestCase):
    def test_mixed_argument_kinds_keep_their_origins_and_document_links_separate(self):
        base = Path(__file__).resolve().parents[1]
        graph = json.loads((base / "examples/minimal/evidence-graph.json").read_bytes())
        graph["selected_goals"] = ["paper-goal"]
        graph["nodes"].extend([
            {"id": "paper-goal", "kind": "claim", "label": "paper goal",
             "status": "conditional", "assumption_ids": ["paper-premise"],
             "evidence_ids": [], "citation_ids": []},
            {"id": "paper-ingredient", "kind": "claim", "label": "ingredient",
             "status": "unverified", "assumption_ids": [],
             "evidence_ids": [], "citation_ids": []},
            {"id": "paper-premise", "kind": "assumption", "label": "premise",
             "status": "axiom", "assumption_ids": [],
             "evidence_ids": [], "citation_ids": []},
        ])
        graph["edges"].extend([
            {"from": "paper-goal", "to": "Minimal.result", "kind": "formalizes",
             "evidence_ids": []},
            {"from": "paper-goal", "to": "paper-ingredient", "kind": "supports",
             "evidence_ids": []},
        ])
        with tempfile.TemporaryDirectory() as temporary:
            parent = Path(temporary)
            scaffold = parent / "scaffold"
            bundle.scaffold(graph, scaffold)
            content = b"# Paper\n<!-- passage:result -->\nRecorded correspondence.\n<!-- /passage:result -->\n"
            citations = sorted(required_citation_ids(graph))
            summary = validate_graph(graph)
            mapping = {
                "schema_version": "1.0", "stage": "short", "state": "draft",
                "path": "papers/short.md", "content_sha256": digest(content),
                "graph_sha256": digest(encoded(graph)), "selected_goal_ids": ["paper-goal"],
                "claim_ids": ["paper-goal"], "citation_ids": citations,
                "assumption_ids": summary["assumptions"], "unresolved_ids": summary["unresolved"],
                "passages": [{"anchor": "result", "text_sha256": digest(b"\nRecorded correspondence.\n"),
                              "claim_ids": ["paper-goal"], "citation_ids": citations,
                              "assumption_ids": summary["assumptions"],
                              "evidence_class": "source_argument",
                              "rationale": "Synthetic mapping, not proof certification."}],
                "review_state": "not_reviewed", "review_notes": [],
            }
            (parent / "short.md").write_bytes(content)
            write_json(parent / "short.json", mapping)
            root = parent / "bundle"
            bundle.assemble_bundle(scaffold / "graph.json", {
                "long": (scaffold / "papers/long.md", scaffold / "papers/long.json"),
                "short": (parent / "short.md", parent / "short.json"),
                "expository": (scaffold / "papers/expository.md", scaffold / "papers/expository.json"),
            }, root)
            view = project_paper(root, "short")
            graph_view = view["graph"]
            self.assertNotIn("proof_links", graph_view)
            self.assertEqual(graph_view["relation_scope"],
                             "recorded_argument_relation_reachability")
            classes = {link["kind"]: link["semantic_class"]
                       for link in graph_view["argument_links"]}
            self.assertEqual(classes["formalizes"], "formalization_correspondence")
            self.assertEqual(classes["supports"], "curated_argument_support")
            self.assertEqual(classes["lean_type_dependency"], "lean_syntactic_dependency")
            self.assertEqual(classes["lean_value_dependency"], "lean_syntactic_dependency")
            self.assertEqual(classes["assumption_ids"], "explicit_assumption_reference")
            self.assertTrue(all(link["record_ref"] in {r["ref"] for r in graph_view["records"]["edges"]}
                                for link in graph_view["argument_links"] if not link["derived"]))
            self.assertTrue(all(link["source_field"] == "assumption_ids"
                                for link in graph_view["argument_links"] if link["derived"]))
            self.assertTrue(all(link["derived"] and link["source_ref"] == view["bundle"]["mapping_ref"]
                                and link["source_anchor"] == "result"
                                for link in view["correspondence_links"]))
            self.assertTrue(all(link["derived"] and link["source_ref"] == view["bundle"]["markdown_ref"]
                                for links in (view["paper"]["reading_order"],
                                              view["paper"]["outline_links"],
                                              view["paper"]["section_passage_links"])
                                for link in links))
            self.assertTrue(all(link["derived"] and link["owner_ref"] == link["from"]
                                for link in graph_view["provenance_links"]))
            argument_kinds = {link["kind"] for link in graph_view["argument_links"]}
            self.assertFalse(argument_kinds & {"next_in_text", "subsection", "text_overlap",
                                               "maps_claim", "maps_citation", "maps_assumption"})
            self.assertFalse(view["semantic_certification"])

    def test_section_overlaps_cover_headings_inside_and_across_passages(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = authored_bundle(Path(temporary))
            content = (b"---\r\n# YAML pseudo-heading\r\n---\r\n# Root\r\n"
                       b"<!-- passage:result -->\nOpening text.\n## Inner A\nA text.\n"
                       b"## Inner B\nB text.\n<!-- /passage:result -->\n"
                       b"## C\n<!-- passage:premise -->\nC text.\n"
                       b"## D\nD text.\n<!-- /passage:premise -->\n")
            markdown_path = root / "papers/short.md"
            mapping_path = root / "papers/short.json"
            mapping = json.loads(mapping_path.read_bytes())
            markdown_path.write_bytes(content)
            mapping["content_sha256"] = digest(content)
            for row in mapping["passages"]:
                anchor = row["anchor"].encode()
                opening = b"<!-- passage:" + anchor + b" -->"
                start = content.index(opening) + len(opening)
                end = content.index(b"<!-- /passage:" + anchor + b" -->")
                row["text_sha256"] = digest(content[start:end])
            write_json(mapping_path, mapping)
            manifest_path = root / "manifest.json"
            manifest = json.loads(manifest_path.read_bytes())
            for row in manifest["files"]:
                if row["path"] in {"papers/short.md", "papers/short.json"}:
                    row["sha256"] = digest((root / row["path"]).read_bytes())
            write_json(manifest_path, manifest)
            view = project_paper(root, "short")
            paper = view["paper"]
            sections = {row["title"]: row for row in paper["sections"]}
            passages = {row["anchor"]: row for row in paper["passages"]}
            self.assertEqual(set(sections), {"Root", "Inner A", "Inner B", "C", "D"})
            links = paper["section_passage_links"]
            refs = {row["ref"] for row in paper["sections"] + paper["passages"]}
            self.assertTrue(all(link["from"] in refs and link["to"] in refs for link in links))
            pairs = {(link["from"], link["to"]) for link in links}
            self.assertEqual(len(pairs), len(links))
            for section in paper["sections"]:
                for passage in paper["passages"]:
                    start = max(section["span"]["start_byte"], passage["content_span"]["start_byte"])
                    end = min(section["span"]["end_byte"], passage["content_span"]["end_byte"])
                    matches = [link for link in links if link["from"] == section["ref"]
                               and link["to"] == passage["ref"]]
                    self.assertEqual(len(matches), int(start < end))
                    if matches:
                        self.assertEqual(matches[0]["overlap_span"]["start_byte"], start)
                        self.assertEqual(matches[0]["overlap_span"]["end_byte"], end)
                        self.assertEqual(matches[0]["kind"], "text_overlap")
            self.assertIn((sections["Inner A"]["ref"], passages["result"]["ref"]), pairs)
            self.assertIn((sections["Inner B"]["ref"], passages["result"]["ref"]), pairs)
            self.assertIn((sections["C"]["ref"], passages["premise"]["ref"]), pairs)
            self.assertIn((sections["D"]["ref"], passages["premise"]["ref"]), pairs)
            self.assertEqual(passages["result"]["section_ref"], sections["Root"]["ref"])
            self.assertEqual(passages["premise"]["section_ref"], sections["Root"]["ref"])
            self.assertEqual({link["from"] for link in view["correspondence_links"]},
                             {passages["result"]["ref"], passages["premise"]["ref"]})

    def test_formalization_direction_and_status_are_preserved(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = authored_bundle(Path(temporary), formalization=True)
            view = project_paper(root, "short", ["result"])
            self.assertIn("decl", {r["record"]["id"] for r in view["graph"]["records"]["nodes"]})
            link = next(link for link in view["graph"]["argument_links"]
                        if link["kind"] == "formalizes")
            self.assertTrue(link["from"].endswith("/nodes/goal"))
            self.assertTrue(link["to"].endswith("/nodes/decl"))
            decl = next(r["record"] for r in view["graph"]["records"]["nodes"]
                        if r["record"]["id"] == "decl")
            self.assertEqual(decl["status"], "unverified")

    def test_text_order_spans_sections_and_selective_graph(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = authored_bundle(Path(temporary))
            view = project_paper(root, "short", ["premise"])
            paper = view["paper"]
            self.assertEqual(view["selection"]["available_anchors"], ["premise", "result"])
            self.assertEqual(view["selection"]["omitted_by_selector"], ["result"])
            self.assertEqual([s["title"] for s in paper["sections"]], ["Paper", "Result", "Result"])
            self.assertNotEqual(paper["sections"][1]["ref"], paper["sections"][2]["ref"])
            self.assertEqual(paper["sections"][1]["parent_ref"], paper["sections"][0]["ref"])
            raw = (root / "papers/short.md").read_bytes()
            for passage in paper["passages"]:
                span = passage["content_span"]
                self.assertEqual(raw[span["start_byte"]:span["end_byte"]].decode(), passage["text"])
            self.assertIn("μ-result", paper["passages"][1]["text"])
            self.assertEqual({r["record"]["id"] for r in view["graph"]["records"]["nodes"]},
                             {"prerequisite"})
            self.assertEqual(view["graph"]["argument_links"], [])
            self.assertEqual({r["record"]["id"] for r in view["graph"]["records"]["citations"]},
                             {"prerequisite-credit"})
            self.assertEqual(len(view["correspondence_links"]), 2)
            self.assertTrue(paper["unmapped_segments"])
            self.assertIn("Outside the mapped passages", paper["unmapped_segments"][-1]["text"])
            self.assertEqual(view["coverage"]["mapped_content_bytes"] +
                             view["coverage"]["marker_bytes"] + view["coverage"]["unmapped_bytes"], len(raw))
            self.assertFalse(view["semantic_certification"])

    def test_all_passages_keep_failed_evidence_and_separate_reading_from_proof(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = authored_bundle(Path(temporary), cycle=True)
            view = project_paper(root, "short")
            graph = view["graph"]
            self.assertEqual({r["record"]["id"] for r in graph["records"]["nodes"]},
                             {"goal", "prerequisite", "assumption"})
            self.assertEqual({r["record"]["status"] for r in graph["records"]["evidence"]},
                             {"failed"})
            self.assertEqual({link["kind"] for link in graph["argument_links"]},
                             {"supports", "assumption_ids"})
            self.assertTrue(any(c["cyclic"] for c in graph["components"]))
            self.assertTrue(all(link["kind"] == "next_in_text" for link in view["paper"]["reading_order"]))
            self.assertFalse(any(link["kind"] == "next_in_text" for link in graph["argument_links"]))
            all_refs = {row["ref"] for rows in graph["records"].values() for row in rows}
            all_refs |= {row["ref"] for key in ("sections", "passages") for row in view["paper"][key]}
            for links in (view["paper"]["reading_order"], view["paper"]["outline_links"],
                          view["correspondence_links"], graph["argument_links"], graph["provenance_links"]):
                self.assertTrue(all(link["from"] in all_refs and link["to"] in all_refs for link in links))

    def test_directory_zip_and_cli_are_identical(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = authored_bundle(Path(temporary))
            archive = Path(temporary) / "bundle.zip"
            bundle.export_bundle(root, archive)
            expected = project_paper(root, "short", ["result"])
            self.assertEqual(project_paper(archive, "short", ["result"]), expected)
            output, errors = io.StringIO(), io.StringIO()
            with contextlib.redirect_stdout(output), contextlib.redirect_stderr(errors):
                status = main(["inspect-bundle", str(archive), "--paper", "short",
                               "--passage", "result"])
            self.assertEqual(status, 0, errors.getvalue())
            self.assertEqual(json.loads(output.getvalue()), expected)

    def test_empty_scaffold_and_bad_queries(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = authored_bundle(Path(temporary))
            view = project_paper(root, "long")
            self.assertEqual(view["paper"]["passages"], [])
            self.assertEqual(view["graph"]["records"]["nodes"], [])
            self.assertEqual(view["coverage"]["unmapped_bytes"], view["paper"]["byte_length"])
            with self.assertRaises(ContractError):
                project_paper(root, "unknown")
            with self.assertRaises(ContractError):
                project_paper(root, "short", ["missing"])
            with self.assertRaises(ContractError):
                project_paper(root, "short", ["result", "result"])
            output, errors = io.StringIO(), io.StringIO()
            with contextlib.redirect_stdout(output), contextlib.redirect_stderr(errors):
                status = main(["inspect-bundle", str(root), "--passage", "result"])
            self.assertEqual(status, 1)
            self.assertIn("requires --paper", errors.getvalue())

    def test_stale_mapping_is_rejected_by_existing_bundle_validation(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = authored_bundle(Path(temporary))
            before = project_paper(root, "short")
            mapping_path = root / "papers/short.json"
            mapping = json.loads(mapping_path.read_bytes())
            mapping["passages"][0]["text_sha256"] = "0" * 64
            write_json(mapping_path, mapping)
            manifest_path = root / "manifest.json"
            manifest = json.loads(manifest_path.read_bytes())
            for row in manifest["files"]:
                if row["path"] == "papers/short.json":
                    row["sha256"] = digest(mapping_path.read_bytes())
            write_json(manifest_path, manifest)
            with self.assertRaisesRegex(ContractError, "passage content hash is stale"):
                project_paper(root, "short")
            self.assertEqual(before["stage"], "short")

    def test_platform_decomposition_does_not_enter_proof_closure(self):
        graph_path = Path(__file__).resolve().parents[1] / "examples/prove2me/full-support/graph.json"
        graph = json.loads(graph_path.read_bytes())
        goal = graph["selected_goals"][0]
        with tempfile.TemporaryDirectory() as temporary:
            parent = Path(temporary)
            scaffold = parent / "scaffold"
            bundle.scaffold(graph, scaffold)
            content = b"# Platform observation\n<!-- passage:observation -->\nRecorded only.\n<!-- /passage:observation -->\n"
            citations = sorted(required_citation_ids(graph))
            summary = validate_graph(graph)
            mapping = {
                "schema_version": "1.0", "stage": "short", "state": "draft",
                "path": "papers/short.md", "content_sha256": digest(content),
                "graph_sha256": digest(encoded(graph)), "selected_goal_ids": [goal],
                "claim_ids": [goal], "citation_ids": citations,
                "assumption_ids": summary["assumptions"], "unresolved_ids": summary["unresolved"],
                "passages": [{"anchor": "observation",
                              "text_sha256": digest(b"\nRecorded only.\n"),
                              "claim_ids": [goal], "citation_ids": citations,
                              "assumption_ids": summary["assumptions"],
                              "evidence_class": "source_argument",
                              "rationale": "Platform metadata correspondence only."}],
                "review_state": "not_reviewed", "review_notes": [],
            }
            (parent / "short.md").write_bytes(content)
            write_json(parent / "short.json", mapping)
            root = parent / "bundle"
            bundle.assemble_bundle(scaffold / "graph.json", {
                "long": (scaffold / "papers/long.md", scaffold / "papers/long.json"),
                "short": (parent / "short.md", parent / "short.json"),
                "expository": (scaffold / "papers/expository.md", scaffold / "papers/expository.json"),
            }, root)
            view = project_paper(root, "short")
            self.assertEqual(view["graph"]["argument_links"], [])
            self.assertEqual({r["record"]["id"] for r in view["graph"]["records"]["nodes"]},
                             {goal})
            self.assertEqual({r["record"]["kind"] for r in view["graph"]["records"]["evidence"]},
                             {"platform_observation"})
