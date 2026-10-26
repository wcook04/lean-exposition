"""HTTP retrieval preserves consumer semantics and one exact captured edition."""
from __future__ import annotations

import contextlib
import http.client
import json
import queue
import shutil
import subprocess
import sys
import tempfile
import threading
import unittest
from pathlib import Path
from urllib.parse import parse_qs, urlencode, urlsplit
from wsgiref.simple_server import WSGIRequestHandler, make_server
from wsgiref.util import setup_testing_defaults
from wsgiref.validate import validator

from lean_exposition import bundle, consumer, web
from lean_exposition.contracts import ContractError, digest
from lean_exposition.extraction import to_graph
from test_application_obligations import extracted_application
from test_core_review import extraction_fixture, rebind
from test_corpus_views import bind, corpus_bundle
from test_scoped_applications import application_bundle, application_graph

ROOT = Path(__file__).resolve().parents[1]


def request(app, path="/api/v1", query=None, *, method="GET", headers=None):
    parsed = urlsplit(path)
    environ = {}
    setup_testing_defaults(environ)
    environ.update(REQUEST_METHOD=method, PATH_INFO=parsed.path,
                   QUERY_STRING=urlencode(query, doseq=True) if query is not None else parsed.query)
    for name, value in (headers or {}).items():
        environ["HTTP_" + name.upper().replace("-", "_")] = value
    response = {}

    def start_response(status, response_headers, exc_info=None):
        response.update(status=int(status.split()[0]), headers=dict(response_headers))

    output = app(environ, start_response)
    try:
        response["body"] = b"".join(output)
    finally:
        if hasattr(output, "close"):
            output.close()
    return response


class QuietHandler(WSGIRequestHandler):
    def log_message(self, format, *args):
        pass


@contextlib.contextmanager
def local_server(app):
    server = make_server("127.0.0.1", 0, validator(app), handler_class=QuietHandler)
    thread = threading.Thread(target=server.serve_forever, kwargs={"poll_interval": 0.01}, daemon=True)
    thread.start()
    try:
        yield server.server_port
    finally:
        server.shutdown()
        server.server_close()
        thread.join(timeout=2)


class WebTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="lean-exposition-http-")
        self.addCleanup(temporary.cleanup)
        self.parent = Path(temporary.name)
        self.root = corpus_bundle(self.parent)
        self.payload = bundle.load_bundle(self.root)
        self.app = web.create_app(self.root)
        self.corpus = consumer.project_corpus(self.root)
        self.manifest = self.corpus["snapshot"]["manifest_sha256"]

    def data(self, route, query=None, *, app=None):
        response = request(app or self.app, route, query)
        self.assertEqual(response["status"], 200, response["body"].decode())
        self.assertEqual(response["headers"]["Content-Type"], "application/json; charset=utf-8")
        value = json.loads(response["body"])
        self.assertEqual(value["api_version"], web.API_VERSION)
        self.assertEqual(value["snapshot"]["manifest_sha256"], (app or self.app).manifest_sha256)
        return value["data"]

    def ref(self, table, identifier):
        return next(row["ref"] for row in self.corpus["records"][table]
                    if row["record"].get("id") == identifier)

    def error(self, route, query=None, *, status=400, app=None, code=None, **kwargs):
        response = request(app or self.app, route, query, **kwargs)
        self.assertEqual(response["status"], status, response["body"].decode())
        self.assertEqual(response["headers"]["Content-Type"], "application/json; charset=utf-8")
        self.assertEqual(response["headers"]["Cache-Control"], "no-store")
        value = json.loads(response["body"])
        self.assertNotIn("data", value)
        if code:
            self.assertEqual(value["error"]["code"], code)
        return response

    def all_pages(self, route, query):
        result, seen, total = [], set(), None
        while route:
            self.assertNotIn(route, seen, "pagination must advance")
            seen.add(route)
            page = self.data(route, query)
            total = page["total"] if total is None else total
            self.assertEqual(page["total"], total)
            self.assertLessEqual(len(page["items"]), page["limit"])
            result.extend(page["items"])
            route, query = page["next"], None
            if route:
                self.assertEqual(parse_qs(urlsplit(route).query)["manifest"], [self.manifest])
        self.assertEqual(len(result), total)
        return result

    def test_discovery_counts_papers_and_paged_document_structures(self):
        discovery = self.data("/api/v1")
        self.assertEqual({r["href"] for r in discovery["routes"]},
                         {"/api/v1" + route for route in web.ROUTES})
        self.assertEqual({r["name"] for r in discovery["documents"]}, set(bundle.BUNDLE_FILES))
        self.assertFalse(discovery["semantic_certification"])
        overview = self.data("/api/v1/overview")
        self.assertEqual(overview["record_counts"], self.corpus["coverage"]["record_counts"])
        self.assertEqual(sum(overview["node_status_counts"].values()), len(self.corpus["records"]["nodes"]))
        self.assertFalse(overview["reading_order_is_dependency_order"])
        self.assertEqual(self.data("/api/v1/corpus"), self.corpus)
        papers = self.data("/api/v1/papers")["items"]
        self.assertEqual([p["stage"] for p in papers], list(bundle.STAGES))
        for paper in papers:
            view = self.data(paper["href"])
            self.assertEqual(view, consumer.project_paper(self.root, paper["stage"]))
            self.assertEqual(view["review_state"], paper["review_state"])
            self.assertEqual(request(self.app, paper["document_href"])["body"],
                             self.payload[f"papers/{paper['stage']}.md"])
            for route, key in (("sections", "sections"), ("passages", "passages"), ("parts", "document_parts")):
                rows = self.all_pages(f"/api/v1/papers/{paper['stage']}/{route}", {"limit": 1})
                if key == "document_parts":
                    self.assertEqual("".join(row["text"] for row in rows).encode("utf-8"),
                                     self.payload[f"papers/{paper['stage']}.md"])
                    rows = [{k: v for k, v in row.items() if k != "text"} for row in rows]
                self.assertEqual(rows, view["paper"][key])

    def test_record_filters_pagination_and_reverse_passage_links(self):
        records = self.all_pages("/api/v1/records", {"table": "nodes", "limit": 2})
        self.assertEqual({r["ref"] for r in records}, {r["ref"] for r in self.corpus["records"]["nodes"]})
        filtered = self.data("/api/v1/records", {"table": "nodes", "kind": "claim", "status": "open",
                                                "q": "ISOLATED", "limit": 1, "offset": 0})
        self.assertEqual([r["record"]["id"] for r in filtered["items"]], ["isolated"])
        paper = next(p for p in self.corpus["papers"] if p["stage"] == "short")
        members = self.all_pages("/api/v1/records", {"table": "nodes", "paper": "short", "limit": 1})
        self.assertEqual({r["ref"] for r in members}, set(paper["graph"]["record_refs"]["nodes"]))
        self.assertEqual(self.data("/api/v1/records", {"offset": 999999999})["items"], [])
        detail = self.data("/api/v1/record", {"ref": self.ref("nodes", "goal")})
        self.assertEqual(detail["record"]["id"], "goal")
        self.assertEqual({p["anchor"] for p in detail["aligned_passages"]}, {"result"})
        for passage in detail["aligned_passages"]:
            self.assertIn(passage["text"], self.data(passage["paper_href"])["paper"]["text"])
        self.assertIn(detail["ref"], self.data(detail["neighborhood_href"])["selected_record_refs"])
        isolated = self.data("/api/v1/record", {"ref": self.ref("nodes", "isolated")})
        self.assertEqual(isolated["aligned_passages"], [])

    def test_relation_pages_preserve_typed_links_and_paper_boundaries(self):
        rows = self.all_pages("/api/v1/relations", {"family": ["arguments", "provenance"], "limit": 2})
        expected = {(family, link["id"]) for family in ("arguments", "provenance")
                    for link in self.corpus["relations"][family]}
        self.assertEqual({(r["family"], r["id"]) for r in rows}, expected)
        self.assertEqual(len(rows), len(expected))
        short = next(p for p in self.corpus["papers"] if p["stage"] == "short")
        members = {ref for refs in short["graph"]["record_refs"].values() for ref in refs}
        rows = self.all_pages("/api/v1/relations", {"paper": "short", "limit": 2})
        self.assertTrue(rows)
        self.assertTrue(all({r["from"], r["to"]} <= members for r in rows))
        self.assertNotIn(self.ref("nodes", "outside"), {end for r in rows for end in (r["from"], r["to"])})

    def test_neighborhood_and_graph_parity_including_cycles_and_whole_corpus(self):
        refs = [self.ref("nodes", "goal"), self.ref("sources", "public")]
        params = {"ref": refs, "family": ["arguments", "provenance"], "direction": "both",
                  "paper": "short", "depth": 2, "budget": 4}
        result = self.data("/api/v1/neighborhood", params)
        self.assertEqual(result, consumer.query_corpus(self.root, record_refs=refs,
            families=["arguments", "provenance"], direction="both", stage="short", max_depth=2, max_records=4))
        self.assertTrue(result["coverage"]["paper_boundary_present"])
        self.assertTrue(result["coverage"]["query_truncated"])
        for direction in ("incoming", "outgoing", "both"):
            query = {"ref": self.ref("sources", "public"), "family": "provenance", "direction": direction}
            self.assertEqual(self.data("/api/v1/neighborhood", query), consumer.query_corpus(
                self.root, record_refs=[query["ref"]], families=["provenance"], direction=direction))
        for view in web.FAMILIES:
            nodes = ["decl"] if view == "declarations" else ["goal"]
            for direction in (("prerequisites", "consumers") if view in {"arguments", "declarations", "platform"}
                              else ("prerequisites",)):
                assumptions = view in {"arguments", "declarations"}
                result = self.data("/api/v1/graph", {"view": view, "node": nodes, "direction": direction,
                                                    "assumptions": str(assumptions).lower(), "scope": "focus"})
                self.assertEqual(result, consumer.project_graph(self.payload["graph.json"], view, nodes,
                    direction=direction, include_assumptions=assumptions))
            roots = sorted(r["record"]["id"] for r in self.corpus["records"]["nodes"]
                           if view != "declarations" or r["record"]["kind"] in {"declaration", "assumption"})
            self.assertEqual(self.data("/api/v1/graph", {"view": view, "scope": "corpus"}),
                             consumer.project_graph(self.payload["graph.json"], view, roots))
        self.assertTrue(any(c["cyclic"] for c in self.data("/api/v1/graph")["components"]))

    def test_compact_map_retains_formal_obligation_identity_and_extraction_scope(self):
        for axiom in ("Classical.choice", "sorryAx"):
            with self.subTest(axiom=axiom):
                project = self.parent / axiom
                project.mkdir()
                graph = extracted_application(project, axiom)
                graph["evidence"].append({
                    "id": "unknown-extraction", "kind": "extraction", "status": "not_run",
                    "subject_ids": ["consumer"], "source_ids": [], "command": [],
                    "tool": "synthetic fixture", "details": "No extraction was run for this subject.",
                })
                root = project / "bundle"
                bundle.scaffold(graph, root)
                app = web.create_app(root)
                query = {"view": "arguments", "node": "consumer", "assumptions": "true"}
                full = self.data("/api/v1/graph", query, app=app)
                compact = self.data("/api/v1/graph", {**query, "representation": "map"}, app=app)
                self.assertEqual(compact["links"], full["links"])
                nodes = {row["id"]: row for row in compact["records"]["nodes"]}
                self.assertIn(axiom, nodes)
                for row in full["records"]["nodes"]:
                    record = row["record"]
                    self.assertEqual(nodes[record["id"]].get("declaration"), record.get("declaration"))
                    self.assertNotIn("statement", nodes[record["id"]])
                evidence = {row["id"]: row for row in compact["records"]["evidence"]}
                for row in full["records"]["evidence"]:
                    record = row["record"]
                    card = evidence[record["id"]]
                    self.assertEqual(card["status"], record["status"])
                    if record["kind"] == "extraction":
                        self.assertEqual(card["subject_ids"], record["subject_ids"])
                    else:
                        self.assertNotIn("subject_ids", card)
                    self.assertNotIn("receipt", card)
                self.assertEqual(evidence["extract"]["subject_ids"], ["result"])
                self.assertEqual(evidence["unknown-extraction"]["status"], "not_run")
                self.assertEqual(evidence["unknown-extraction"]["subject_ids"], ["consumer"])

    def test_compact_map_keeps_renamed_hole_identity_without_extraction(self):
        graph = application_graph()
        assumption = next(row for row in graph["nodes"] if row["id"] == "assumption")
        assumption.update(id="renamed-sorry", declaration="sorryAx", status="open")
        graph["nodes"][1]["assumption_ids"] = ["renamed-sorry"]
        graph["edges"][0]["application"]["premise_bindings"][0]["assumption_id"] = "renamed-sorry"
        root = self.parent / "renamed-hole"
        bundle.scaffold(graph, root)
        app = web.create_app(root)
        query = {"view": "arguments", "node": "goal", "assumptions": "true"}
        full = self.data("/api/v1/graph", query, app=app)
        compact = self.data("/api/v1/graph", {**query, "representation": "map"}, app=app)
        self.assertEqual(compact["links"], full["links"])
        hole = next(row for row in compact["records"]["nodes"] if row["id"] == "renamed-sorry")
        self.assertEqual(hole["declaration"], "sorryAx")
        self.assertEqual(hole["status"], "open")
        self.assertFalse(any(row["kind"] == "extraction" for row in compact["records"]["evidence"]))

    def test_compact_and_full_maps_preserve_exact_lean_dependency_kinds(self):
        project = self.parent / "typed-lean-dependencies"
        project.mkdir()
        report, build = extraction_fixture(project)
        for field in ("type_dependencies", "value_dependencies", "structural_dependencies"):
            report["declarations"][0][field] = ["Classical.choice"]
        report["declarations"][0]["axioms"] = ["Classical.choice"]
        report["external_dependencies"] = [{"name": "Classical.choice", "kind": "axiom", "module": "Init"}]
        rebind(report)
        graph = to_graph(report, project, build)
        root = project / "bundle"
        bundle.scaffold(graph, root)
        app = web.create_app(root)
        query = {"view": "declarations", "node": "result", "assumptions": "true"}
        full = self.data("/api/v1/graph", query, app=app)
        compact = self.data("/api/v1/graph", {**query, "representation": "map"}, app=app)
        self.assertEqual(compact["links"], full["links"])
        typed = [link for link in compact["links"] if link["kind"].startswith("lean_")]
        self.assertEqual({link["kind"] for link in typed},
                         {"lean_type_dependency", "lean_value_dependency", "lean_structural_dependency"})
        self.assertTrue(all(link["semantic_class"] == "lean_syntactic_dependency" for link in typed))
        arguments = self.data("/api/v1/graph", {**query, "view": "arguments", "representation": "map"}, app=app)
        self.assertFalse(any(link["kind"].startswith("lean_") for link in arguments["links"]))

    def test_connection_witness_uses_stored_direction_and_exposes_cutoffs(self):
        source, target = self.ref("sources", "public"), self.ref("nodes", "goal")
        params = {"from": source, "to": target, "family": "provenance", "direction": "incoming",
                  "depth": 1, "budget": 100, "paper": "short"}
        result = self.data("/api/v1/connection", params)
        self.assertEqual(result["outcome"], "reached")
        self.assertEqual([w["record_ref"] for w in result["witness_path"]], [source, target])
        expected = consumer.query_corpus(self.root, record_refs=[source], families=["provenance"],
                                        direction="incoming", stage="short")
        self.assertEqual(result["neighborhood"], expected)
        link_id = result["witness_path"][-1]["parent"]["relation_id"]
        link = next(l for l in expected["relations"]["provenance"] if l["id"] == link_id)
        self.assertEqual((link["from"], link["to"]), (target, source))
        bounded = self.data("/api/v1/connection", {**params, "depth": 0})
        self.assertEqual(bounded["outcome"], "not_reached_within_query")
        self.assertEqual(bounded["witness_path"], [])
        self.assertTrue(bounded["neighborhood"]["coverage"]["query_truncated"])
        self.assertEqual(self.data("/api/v1/connection", {**params, "to": source})["outcome"], "reached")

    def test_paper_queries_keep_selectors_witnesses_and_unicode_byte_coordinates(self):
        view = consumer.project_paper(self.root, "short")
        passage = next(p for p in view["paper"]["passages"] if p["anchor"] == "result")
        section = passage["section_ref"]
        text = self.payload["papers/short.md"]
        start, end = text.index("μ-result".encode()), text.index("μ-result".encode()) + len("μ-result".encode())
        params = {"paper": "short", "passage": "result", "section": section, "node": "prerequisite",
                  "relation": "prerequisites", "start": start, "end": end, "manifest": self.manifest}
        result = self.data("/api/v1/papers/query", params)
        self.assertEqual(result, consumer.query_papers(self.root, stage="short", passages=["result"],
            section_refs=[section], node_ids=["prerequisite"], relation="prerequisites",
            byte_ranges=[(start, end)], expected_manifest_sha256=self.manifest))
        self.assertEqual(result["match_count"], 1)
        self.assertTrue(result["papers"][0]["matches"][0]["whole_passage_extends_beyond_selected_ranges"])
        for relation in ("direct", "prerequisites"):
            self.assertEqual(self.data("/api/v1/papers/query", {"node": "goal", "relation": relation}),
                consumer.query_papers(self.root, node_ids=["goal"], relation=relation,
                                      expected_manifest_sha256=self.manifest))
        self.error("/api/v1/papers/query", {"paper": "short", "start": start, "end": end}, code="edition_required")
        self.error("/api/v1/papers/query", {**params, "start": start + 1}, code="invalid_selection")
        self.error("/api/v1/papers/query", {**params, "end": len(text) + 1}, code="invalid_selection")
        self.error("/api/v1/papers/query", {"paper": "short", "start": start}, code="invalid_range")

    def test_compare_and_literal_search_return_resolvable_paged_results(self):
        rows = self.all_pages("/api/v1/compare", {"left": "short", "right": "long", "table": "nodes", "limit": 2})
        self.assertEqual({r["membership"] for r in rows}, {"short"})
        self.assertEqual({r["ref"] for r in rows}, set(next(p for p in self.corpus["papers"]
            if p["stage"] == "short")["graph"]["record_refs"]["nodes"]))
        found = self.data("/api/v1/search", {"q": "Μ-RESULT premise", "table": "passages", "paper": "short", "limit": 1})
        self.assertEqual(found["total"], 1)
        self.assertEqual(found["matching"], "literal_casefolded_AND")
        self.assertEqual(self.data(found["items"][0]["href"])["match_count"], 1)
        headings = self.all_pages("/api/v1/search", {"q": "Result", "table": "sections", "paper": "short", "limit": 1})
        self.assertEqual(len(headings), 2)
        self.assertEqual(len({r["ref"] for r in headings}), 2)
        for row in headings:
            self.data(row["href"])
        records = self.data("/api/v1/search", {"q": "isolated", "table": "nodes"})
        self.assertEqual(self.data(records["items"][0]["href"])["record"]["id"], "isolated")
        self.assertEqual(self.data("/api/v1/search", {"q": "[.*]"})["total"], 0)

    def test_exact_allowlisted_documents_and_headers(self):
        for name, content in self.payload.items():
            with self.subTest(name=name):
                response = request(self.app, "/api/v1/documents/" + name)
                self.assertEqual(response["status"], 200)
                self.assertEqual(response["body"], content)
                self.assertEqual(response["headers"]["Content-Length"], str(len(content)))
                self.assertEqual(response["headers"]["ETag"], '"' + digest(content) + '"')
                self.assertEqual(response["headers"]["X-Content-Type-Options"], "nosniff")
                self.assertEqual(response["headers"]["X-Manifest-SHA256"], self.manifest)
        for path in ("/api/v1/documents/../graph.json", "/api/v1/documents/%2e%2e/graph.json",
                     "/api/v1/documents//etc/passwd", "/api/v1/documents/papers/../../graph.json",
                     "/api/v1/documents/external/missing-build-receipt.json", "/api/v1/documents/unknown.json",
                     "/api/v1/papers/short/document/extra", "/api/v1/papers/unknown", "/", "/api/v10"):
            with self.subTest(path=path):
                self.error(path, status=404)

    def test_head_and_conditional_get_follow_representation_etag(self):
        for path in ("/api/v1/overview", "/api/v1/papers/short/document"):
            get = request(self.app, path)
            head = request(self.app, path, method="HEAD")
            self.assertEqual(head["status"], 200)
            self.assertEqual(head["body"], b"")
            self.assertEqual(head["headers"], get["headers"])
            for etag in (get["headers"]["ETag"], "W/" + get["headers"]["ETag"],
                         '"other", ' + get["headers"]["ETag"], "*"):
                response = request(self.app, path, headers={"If-None-Match": etag})
                self.assertEqual(response["status"], 304)
                self.assertEqual(response["body"], b"")
                self.assertNotIn("Content-Length", response["headers"])
            self.assertEqual(request(self.app, path, headers={"If-None-Match": '"different"'})["status"], 200)
        response = request(self.app, "/missing", method="HEAD")
        self.assertEqual(response["status"], 404)
        self.assertEqual(response["body"], b"")

    def test_methods_and_exact_origin_cors(self):
        allowed = "https://reader.example"
        app = web.create_app(self.root, allow_origin=allowed)
        for method in ("POST", "PUT", "PATCH", "DELETE", "TRACE"):
            self.error("/api/v1", status=405, method=method, app=app, code="method_not_allowed")
        for origin, expected in ((allowed, True), ("https://other.example", False), ("null", False)):
            response = request(app, "/api/v1/overview", headers={"Origin": origin})
            self.assertEqual("Access-Control-Allow-Origin" in response["headers"], expected)
            self.assertEqual(response["headers"]["Vary"], "Origin")
            if expected:
                self.assertEqual(response["headers"]["Access-Control-Allow-Origin"], allowed)
        response = request(app, "/api/v1/overview", method="OPTIONS", headers={"Origin": allowed})
        self.assertEqual(response["status"], 204)
        self.assertEqual(response["body"], b"")
        self.assertEqual(response["headers"]["Allow"], "GET, HEAD, OPTIONS")
        self.assertNotIn("Access-Control-Allow-Origin", request(self.app, "/api/v1")["headers"])
        for origin in ("*", "null", "https://reader.example/", "https://user:pass@reader.example",
                       "https://reader.example?query", "https://reader.example#fragment", "http://:bad",
                       "http://reader.example:bad", "http://reader.example:65536", "http://[broken"):
            with self.subTest(origin=origin), self.assertRaises(ContractError):
                web.create_app(self.root, allow_origin=origin)

    def test_bad_queries_and_unsupported_selections_have_explicit_client_errors(self):
        for route, query in (
            ("/records", {"table": "bogus"}), ("/records", {"offset": -1}),
            ("/records", {"limit": 0}), ("/records", {"limit": 201}), ("/records", {"limit": "1.5"}),
            ("/records", {"paper": "missing"}), ("/record", {}), ("/record", {"ref": ["a", "b"]}),
            ("/relations", {"family": ["arguments", "arguments"]}), ("/neighborhood", {}),
            ("/neighborhood", {"ref": self.ref("nodes", "goal"), "depth": 9}),
            ("/neighborhood", {"ref": self.ref("nodes", "goal"), "budget": 501}),
            ("/neighborhood", {"ref": self.ref("nodes", "outside"), "paper": "short"}),
            ("/connection", {"from": self.ref("nodes", "goal")}),
            ("/graph", {"view": "missing"}), ("/graph", {"node": "missing"}),
            ("/graph", {"view": "citations", "direction": "consumers"}),
            ("/graph", {"view": "platform", "assumptions": "true"}), ("/graph", {"scope": "missing"}),
            ("/graph", {"scope": "corpus", "node": "goal"}), ("/graph", {"assumptions": "yes"}),
            ("/graph", {"node": [str(i) for i in range(33)]}), ("/papers/query", {"passage": "result"}),
            ("/papers/query", {"paper": "short", "section": "stale"}),
            ("/papers/query", {"paper": "short", "passage": "missing"}), ("/papers/query", {"relation": "proof"}),
            ("/compare", {"left": "short", "right": "short"}), ("/compare", {"left": "short"}),
            ("/search", {}), ("/search", {"q": " "}), ("/search", {"q": "x" * 257}),
            ("/search", {"q": " ".join(str(i) for i in range(17))}),
            ("/search", {"q": "claim", "table": "missing"}),
        ):
            with self.subTest(route=route, query=query):
                self.error("/api/v1" + route, query)
        for raw in ("unknown=1", "limit=", "limit=1&limit=2", "q=%ZZ", "q=%FF", "q", "=value"):
            with self.subTest(query=raw):
                self.error("/api/v1/records?" + raw)
        self.error("/api/v1/records?q=" + "a" * web.MAX_QUERY_BYTES, status=414, code="query_too_long")
        self.error("/api/v1/record", {"ref": "missing"}, status=404, code="record_not_found")
        self.error("/api/v1/connection", {"from": self.ref("nodes", "goal"), "to": "missing"}, status=404)

    def test_manifest_pinning_and_capture_stability_after_mutation_and_deletion(self):
        archive = self.parent / "bundle.zip"
        bundle.export_bundle(self.root, archive)
        zip_app = web.create_app(archive)
        capture_app = web.create_app(bundle.BundleCapture(self.root))
        target = "/api/v1/papers/query?" + urlencode({"paper": "short", "passage": "result", "manifest": self.manifest})
        expected = request(self.app, target)
        mapping = json.loads((self.root / "papers/short.json").read_bytes())
        mapping["review_notes"].append("A later edition; not an acceptance.")
        bind(self.root, mapping=mapping)
        successor = web.create_app(self.root)
        self.assertNotEqual(successor.manifest_sha256, self.manifest)
        self.error(target, app=successor, status=409, code="edition_mismatch")
        shutil.rmtree(self.root)
        archive.unlink()
        for app in (self.app, zip_app, capture_app):
            self.assertEqual(request(app, target), expected)
            self.assertEqual(request(app, "/api/v1/documents/graph.json")["body"], self.payload["graph.json"])
        self.error("/api/v1/corpus", {"manifest": "0" * 64}, status=409, code="edition_mismatch")
        self.error("/api/v1/corpus", {"manifest": "invalid"}, code="invalid_manifest")
        self.error("/api/v1/corpus", {"manifest": [self.manifest, self.manifest]}, code="invalid_parameter")

    def test_oversized_representations_fail_without_silent_truncation(self):
        app = web.create_app(self.root, max_response_bytes=1024)
        response = self.error("/api/v1/corpus", app=app, status=413, code="response_too_large")
        self.assertLessEqual(len(response["body"]), 1024)
        self.assertNotIn("ETag", response["headers"])
        paper = self.parent / "large"
        paper.mkdir()
        large_root = corpus_bundle(paper)
        content = (large_root / "papers/short.md").read_bytes() + b"\nUnmapped appendix.\n" * 100
        (large_root / "papers/short.md").write_bytes(content)
        mapping = json.loads((large_root / "papers/short.json").read_bytes())
        mapping["content_sha256"] = digest(content)
        bind(large_root, mapping=mapping)
        large_app = web.create_app(large_root, max_response_bytes=1024)
        response = self.error("/api/v1/papers/short/document", app=large_app, status=413, code="response_too_large")
        self.assertNotIn("Content-Disposition", response["headers"])
        for maximum in (0, 1023, True, 1.5):
            with self.subTest(maximum=maximum), self.assertRaises(ContractError):
                web.create_app(self.root, max_response_bytes=maximum)

    def test_url_encoded_namespace_identifiers_round_trip_without_path_interpretation(self):
        graph = json.loads(self.payload["graph.json"])
        identity = "source / % μ ? #"
        graph["sources"].append({**graph["sources"][0], "id": identity})
        bind(self.root, graph=graph)
        app = web.create_app(self.root)
        rows = self.data("/api/v1/records", {"table": "sources"}, app=app)["items"]
        row = next(r for r in rows if r["record"]["id"] == identity)
        self.assertEqual(self.data(row["href"], app=app)["record"]["id"], identity)
        result = self.data("/api/v1/neighborhood", {"ref": row["ref"], "depth": 0}, app=app)
        self.assertEqual(result["selected_record_refs"], [row["ref"]])

    def test_scoped_applications_do_not_reintroduce_discharged_assumptions(self):
        path = self.parent / "scoped"
        path.mkdir()
        root = application_bundle(path)
        app = web.create_app(root)
        result = self.data("/api/v1/graph", {"view": "arguments", "node": "goal", "assumptions": "true"}, app=app)
        self.assertEqual(result, consumer.project_graph((root / "graph.json").read_bytes(), "arguments", ["goal"], include_assumptions=True))
        self.assertNotIn("assumption", {r["record"]["id"] for r in result["records"]["nodes"]})
        query = self.data("/api/v1/papers/query", {"paper": "long", "node": "assumption", "relation": "prerequisites"}, app=app)
        self.assertEqual(query["match_count"], 0)

    def test_real_http_handles_headers_content_and_encoded_queries(self):
        with local_server(self.app) as port:
            connection = http.client.HTTPConnection("127.0.0.1", port, timeout=5)
            self.addCleanup(connection.close)
            target = "/api/v1/record?" + urlencode({"ref": self.ref("nodes", "goal"), "manifest": self.manifest})
            connection.request("GET", target)
            response = connection.getresponse()
            self.assertEqual(response.status, 200)
            body = response.read()
            self.assertEqual(json.loads(body)["data"]["record"]["id"], "goal")
            etag = response.getheader("ETag")
            connection.request("GET", target, headers={"If-None-Match": etag})
            response = connection.getresponse()
            self.assertEqual(response.status, 304)
            self.assertEqual(response.read(), b"")
            connection.request("HEAD", "/api/v1/papers/short/document")
            response = connection.getresponse()
            self.assertEqual(response.status, 200)
            self.assertEqual(response.getheader("Content-Length"), str(len(self.payload["papers/short.md"])))
            self.assertEqual(response.read(), b"")
            connection.request("GET", "/api/v1/documents/../graph.json")
            response = connection.getresponse()
            self.assertEqual(response.status, 404)
            self.assertEqual(json.loads(response.read())["error"]["code"], "not_found")

    def test_actual_qaoa_bundle_source_to_paper_journey(self):
        root = self.parent / "qaoa"
        papers = ROOT / "papers/qaoa-sk"
        bundle.assemble_bundle(ROOT / "examples/qaoa-sk/evidence-graph.json", {
            "long": (papers / "long/reasoning-record.md", papers / "long/reasoning-record.json"),
            "short": (papers / "short/paper.md", papers / "short/correspondence.json"),
            "expository": (papers / "expository/main.md", papers / "expository/correspondence.json"),
        }, root)
        app = web.create_app(root)
        sources = self.data("/api/v1/records", {"table": "sources", "q": "support_tex_curvature"}, app=app)
        self.assertEqual(sources["total"], 1)
        source_ref = sources["items"][0]["ref"]
        result = self.data("/api/v1/neighborhood", {"ref": source_ref, "family": "provenance",
                                                  "direction": "incoming", "depth": 1}, app=app)
        self.assertEqual(result, consumer.query_corpus(root, record_refs=[source_ref], families=["provenance"],
                                                      direction="incoming", max_depth=1))
        self.assertIn("support.positive_curvature", {r["record"]["id"] for r in result["records"]["nodes"]})
        self.assertFalse(result["coverage"]["source_bytes_opened"])
        self.assertFalse(result["semantic_certification"])
        passage = self.data("/api/v1/papers/query", {"paper": "short", "passage": "main-result"}, app=app)
        self.assertEqual(passage["match_count"], 1)
        self.assertEqual(passage["papers"][0]["view"]["bundle"]["publication"], "local_only")
        structure = self.data("/api/v1/papers/long/structure", app=app)
        full_paper = consumer.project_paper(root, "long")
        self.assertEqual(structure["paper"]["section_passage_links"], full_paper["paper"]["section_passage_links"])
        contact = next(row for row in structure["paper"]["passages"] if row["anchor"] == "contact")
        overlaps = [link for link in structure["paper"]["section_passage_links"] if link["to"] == contact["ref"]]
        self.assertGreater(len({link["from"] for link in overlaps}), 1)
        for link in overlaps:
            selected = self.data(structure["resources"]["query_href"] + "&" + urlencode({"section": link["from"]}), app=app)
            self.assertIn("contact", [match["anchor"] for match in selected["papers"][0]["matches"]])

    def test_serve_cli_starts_a_real_captured_edition(self):
        process = subprocess.Popen(
            [sys.executable, "-m", "lean_exposition.cli", "serve", str(self.root), "--port", "0",
             "--document-path", "long", "proof/record.md",
             "--document-path", "short", "expert/paper.md",
             "--document-path", "expository", "reader/intro.md"],
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
        )
        startup = queue.Queue()
        reader = threading.Thread(target=lambda: startup.put(process.stdout.readline()), daemon=True)
        reader.start()
        try:
            notice = json.loads(startup.get(timeout=10))
            self.assertEqual(notice["manifest_sha256"], self.manifest)
            location = urlsplit(notice["url"])
            self.assertEqual(location.hostname, "127.0.0.1")
            connection = http.client.HTTPConnection(location.hostname, location.port, timeout=5)
            try:
                connection.request("GET", location.path + "/overview")
                response = connection.getresponse()
                self.assertEqual(response.status, 200)
                result = json.loads(response.read())
                self.assertEqual(result["snapshot"]["manifest_sha256"], self.manifest)
                self.assertEqual(result["data"]["record_counts"], self.corpus["coverage"]["record_counts"])
                connection.request("GET", location.path + "/papers/resolve-link?" + urlencode({
                    "paper": "short", "href": "../proof/record.md#proof", "manifest": self.manifest}))
                response = connection.getresponse()
                self.assertEqual(response.status, 200)
                result = json.loads(response.read())["data"]
                self.assertEqual(result["status"], "resolved")
                self.assertEqual(result["target"]["stage"], "long")
                self.assertEqual(result["fragment"], "proof")
            finally:
                connection.close()
        finally:
            process.terminate()
            try:
                process.communicate(timeout=5)
            except subprocess.TimeoutExpired:
                process.kill()
                process.communicate(timeout=5)
            reader.join(timeout=2)


if __name__ == "__main__":
    unittest.main()
