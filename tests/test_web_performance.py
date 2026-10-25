"""Bounded work and compact transport contracts, without timing thresholds."""
from __future__ import annotations

import json
import tempfile
import threading
import unittest
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from unittest.mock import patch

from lean_exposition import web
from test_corpus_views import bind, corpus_bundle
from test_web import request


class WebPerformanceTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = corpus_bundle(Path(temporary.name))
        self.app = web.create_app(self.root)

    def data(self, path, query=None, app=None):
        result = request(app or self.app, path, query)
        self.assertEqual(result["status"], 200, result["body"])
        return json.loads(result["body"])["data"]

    def ref(self, identifier):
        return next(ref for ref, (table, row) in self.app._records.items()
                    if table == "nodes" and row["record"].get("id") == identifier)

    def test_get_head_and_revalidation_reuse_serialized_bytes(self):
        with patch.object(self.app, "_representation", wraps=self.app._representation) as build:
            get = request(self.app, "/api/v1/records", {"table": "nodes", "limit": 1})
            for method in ("GET", "HEAD"):
                result = request(self.app, "/api/v1/records", {"limit": 1, "table": "nodes"}, method=method)
                self.assertEqual(result["headers"], get["headers"])
                self.assertEqual(result["body"], get["body"] if method == "GET" else b"")
            conditional = request(self.app, "/api/v1/records", {"table": "nodes", "limit": 1},
                                  headers={"If-None-Match": get["headers"]["ETag"]})
            self.assertEqual(conditional["status"], 304)
            self.assertEqual(build.call_count, 1)
        self.assertNotIn(b'\n  "', get["body"])

    def test_lru_obeys_entry_and_byte_limits_and_can_be_disabled(self):
        app = web.create_app(self.root, cache_entries=1)
        with patch.object(app, "_representation", wraps=app._representation) as build:
            for path in ("/api/v1/overview", "/api/v1/papers", "/api/v1/overview"):
                self.data(path, app=app)
            self.assertEqual(build.call_count, 3)
            self.assertEqual(len(app._responses._entries), 1)
        size = len(request(self.app, "/api/v1/records", {"limit": 1})["body"])
        app = web.create_app(self.root, cache_bytes=size, cache_entries=20)
        for offset in range(10):
            self.data("/api/v1/records", {"limit": 1, "offset": offset}, app=app)
            self.assertLessEqual(app._responses._bytes, size)
            self.assertEqual(app._responses._bytes, sum(len(row[0]) for row in app._responses._entries.values()))
        app = web.create_app(self.root, cache_bytes=0)
        with patch.object(app, "_representation", wraps=app._representation) as build:
            self.data("/api/v1/overview", app=app)
            self.data("/api/v1/overview", app=app)
            self.assertEqual(build.call_count, 2)
            self.assertEqual(app._responses._bytes, 0)

    def test_concurrent_identical_cold_requests_build_once(self):
        entered, release = threading.Event(), threading.Event()
        original = self.app._representation

        def blocked(*args):
            entered.set()
            if not release.wait(5):
                raise RuntimeError("test builder release timed out")
            return original(*args)

        with patch.object(self.app, "_representation", side_effect=blocked) as build:
            with ThreadPoolExecutor(max_workers=6) as executor:
                jobs = [executor.submit(request, self.app, "/api/v1/overview") for _ in range(6)]
                try:
                    self.assertTrue(entered.wait(5))
                finally:
                    release.set()
                responses = [job.result(timeout=5) for job in jobs]
            self.assertEqual(build.call_count, 1)
            self.assertTrue(all(result == responses[0] for result in responses))

    def test_cache_preserves_manifest_requirement_and_ordered_selectors(self):
        span = self.app._papers["short"]["paper"]["passages"][0]["content_span"]
        query = {"paper": "short", "start": span["start_byte"], "end": span["end_byte"],
                 "manifest": self.app.manifest_sha256}
        self.data("/api/v1/papers/query", query)
        query.pop("manifest")
        self.assertEqual(request(self.app, "/api/v1/papers/query", query)["status"], 400)
        a = self.data("/api/v1/graph", {"node": ["goal", "prerequisite"]})
        b = self.data("/api/v1/graph", {"node": ["prerequisite", "goal"]})
        self.assertEqual(a["requested_roots"], list(reversed(b["requested_roots"])))
        with patch.object(self.app, "_representation", wraps=self.app._representation) as build:
            for _ in range(2):
                self.assertEqual(request(self.app, "/api/v1/records", {"limit": 0})["status"], 400)
            self.assertEqual(build.call_count, 2)

    def test_summary_batch_hydration_and_facets_keep_exact_record_scope(self):
        refs = [self.ref("goal"), self.ref("prerequisite")]
        full = self.data("/api/v1/records", {"ref": refs})
        summary = self.data("/api/v1/records", {"ref": refs, "representation": "summary"})
        self.assertEqual({row["ref"] for row in full["items"]}, set(refs))
        self.assertEqual([row["ref"] for row in full["items"]], [row["ref"] for row in summary["items"]])
        for row in summary["items"]:
            self.assertNotIn("record", row)
            detail = self.data(row["href"])
            self.assertEqual(detail["record"]["id"], row["id"])
            self.assertEqual(detail["record"]["status"], row["status"])
        for stage in (None, "short"):
            query = {"paper": stage} if stage else {}
            facets = self.data("/api/v1/facets", query)
            for table in facets["tables"]:
                records = self.data("/api/v1/records", {**query, "table": table["table"], "limit": 200})
                self.assertEqual(table["count"], records["total"])
        self.assertEqual(request(self.app, "/api/v1/records", {"ref": [refs[0], "missing"]})["status"], 404)

    def test_map_preserves_cycles_links_scope_and_application_semantics(self):
        full = self.data("/api/v1/graph", {"scope": "corpus"})
        mapped = self.data("/api/v1/graph", {"scope": "corpus", "representation": "map"})
        for key, value in full.items():
            if key != "records":
                self.assertEqual(mapped[key], value)
        for table, rows in full["records"].items():
            self.assertEqual([row["ref"] for row in rows], [row["ref"] for row in mapped["records"][table]])
            for card in mapped["records"][table]:
                self.assertNotIn("record", card)
                self.assertNotIn("papers", card)
                self.assertNotIn("href", card)
        self.assertIn("manifest=" + self.app.manifest_sha256, mapped["records_href"])
        self.assertTrue(any(component["cyclic"] for component in mapped["components"]))
        self.assertFalse(mapped["semantic_certification"])

    def test_matches_representation_preserves_support_and_selected_source_text(self):
        query = {"node": "prerequisite", "relation": "prerequisites"}
        full = self.data("/api/v1/papers/query", query)
        compact = self.data("/api/v1/papers/query", {**query, "representation": "matches"})
        self.assertEqual(compact["match_count"], full["match_count"])
        self.assertNotEqual(compact["cache_key"], full["cache_key"])
        for a, b in zip(full["papers"], compact["papers"]):
            self.assertNotIn("view", b)
            self.assertEqual(a["matches"], b["matches"])
            self.assertEqual(a["support_boundary"], b["support_boundary"])
            self.assertEqual(b["passages"], [p for p in a["view"]["paper"]["passages"] if p["selected"]])
            self.assertEqual(b["document"]["bundle"], a["view"]["bundle"])

    def test_search_excerpt_finds_late_unicode_casefold_matches(self):
        graph = json.loads((self.root / "graph.json").read_bytes())
        node = next(row for row in graph["nodes"] if row["id"] == "isolated")
        node["label"] = "prefix " * 100 + "Straße μ suffix"
        bind(self.root, graph=graph)
        app = web.create_app(self.root)
        data = self.data("/api/v1/search", {"q": "STRASSE μ", "table": "nodes"}, app=app)
        row = data["items"][0]
        self.assertIn("Straße", row["excerpt"])
        self.assertGreater(row["excerpt_start_character"], 0)
        source = next(item["text"] for item in app._search if item["ref"] == row["ref"])
        for match in row["matches"]:
            self.assertEqual(source[match["start_character"]:match["end_character"]].casefold(), match["term"])
        self.assertLessEqual(len(row["excerpt"]), 280)

    def test_paper_structure_keeps_complete_document_graph_without_prose_or_record_bodies(self):
        for summary in self.data("/api/v1/papers")["items"]:
            full = self.data(summary["href"])
            structure = self.data(summary["structure_href"])
            self.assertEqual(structure["representation"], "document_structure")
            self.assertNotIn("text", structure["paper"])
            self.assertNotIn("graph", structure)
            for key in ("bundle", "coverage", "paper_scope", "state", "review_state", "semantic_certification"):
                self.assertEqual(structure[key], full[key])
            for key, value in full["paper"].items():
                if key == "text":
                    continue
                expected = ([{k: v for k, v in row.items() if k not in {"text", "rationale"}} for row in value]
                            if key in {"passages", "unmapped_segments"} else value)
                self.assertEqual(structure["paper"][key], expected)
            self.assertEqual(structure["correspondence_links"], full["correspondence_links"])
            self.assertEqual(structure["support_record_refs"],
                             {table: [row["ref"] for row in rows] for table, rows in full["graph"]["records"].items()})
            relation_kinds = {link["kind"] for key in ("reading_order", "outline_links", "section_passage_links")
                              for link in structure["paper"][key]}
            relation_kinds.update(link["kind"] for link in structure["correspondence_links"])
            self.assertEqual(set(structure["relation_semantics"]), relation_kinds)
            document_refs = {row["ref"] for key in ("sections", "passages", "unmapped_segments")
                             for row in structure["paper"][key]}
            support_refs = {ref for refs in structure["support_record_refs"].values() for ref in refs}
            for key in ("reading_order", "outline_links", "section_passage_links"):
                for link in structure["paper"][key]:
                    self.assertIn(link["from"], document_refs)
                    self.assertIn(link["to"], document_refs)
            for link in structure["correspondence_links"]:
                self.assertIn(link["from"], document_refs)
                self.assertIn(link["to"], support_refs)
            source = request(self.app, structure["resources"]["document_href"])["body"]
            self.assertEqual(source.decode(), full["paper"]["text"])
        self.assertEqual(request(self.app, "/api/v1/papers/short/structure", {"limit": 1})["status"], 400)


if __name__ == "__main__":
    unittest.main()
