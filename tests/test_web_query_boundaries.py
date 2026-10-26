"""CORS and generated links respect the web transport's stated bounds."""
from __future__ import annotations

import copy
import http.client
import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch
from urllib.parse import urlsplit

from lean_exposition import bundle, web
from lean_exposition.extraction import to_graph
from lean_exposition.verification import _stream_fields, extract_dependencies
from test_core_review import extraction_fixture
from test_corpus_views import bind, corpus_bundle
from test_web import local_server, request


class WebQueryBoundaryTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temporary = tempfile.TemporaryDirectory(prefix="web-query-boundary-")
        cls.addClassCleanup(cls.temporary.cleanup)
        cls.root = corpus_bundle(Path(cls.temporary.name))
        cls.origin = "http://localhost:5173"
        cls.app = web.create_app(cls.root, allow_origin=cls.origin)

    def test_conditional_preflight_is_limited_to_the_configured_origin(self):
        headers = {"Origin": self.origin, "Access-Control-Request-Method": "GET",
                   "Access-Control-Request-Headers": "if-none-match"}
        response = request(self.app, "/api/v1/overview", method="OPTIONS", headers=headers)
        self.assertEqual(response["status"], 204)
        self.assertEqual(response["headers"]["Access-Control-Allow-Origin"], self.origin)
        self.assertEqual(response["headers"]["Access-Control-Allow-Headers"].lower(), "if-none-match")

        get = request(self.app, "/api/v1/overview", headers={"Origin": self.origin})
        conditional = request(self.app, "/api/v1/overview", headers={
            "Origin": self.origin, "If-None-Match": get["headers"]["ETag"]})
        self.assertEqual(conditional["status"], 304)
        self.assertEqual(conditional["headers"]["Access-Control-Allow-Origin"], self.origin)
        refused = request(self.app, "/api/v1/overview", method="OPTIONS", headers={
            **headers, "Origin": "http://untrusted.example"})
        self.assertNotIn("Access-Control-Allow-Origin", refused["headers"])
        self.assertNotIn("Access-Control-Allow-Headers", refused["headers"])

    def test_real_http_conditional_preflight_and_pagination(self):
        with local_server(self.app) as port:
            connection = http.client.HTTPConnection("127.0.0.1", port, timeout=5)
            try:
                route = "/api/v1/records?limit=1"
                connection.request("GET", route, headers={"Origin": self.origin})
                response = connection.getresponse()
                self.assertEqual(response.status, 200)
                etag = response.getheader("ETag")
                page = json.loads(response.read())["data"]
                self.assertEqual(response.getheader("Access-Control-Allow-Origin"), self.origin)
                connection.request("OPTIONS", route, headers={
                    "Origin": self.origin, "Access-Control-Request-Method": "GET",
                    "Access-Control-Request-Headers": "if-none-match"})
                response = connection.getresponse()
                self.assertEqual(response.status, 204)
                self.assertEqual(response.getheader("Access-Control-Allow-Headers"), "If-None-Match")
                self.assertEqual(response.read(), b"")
                connection.request("GET", route, headers={"Origin": self.origin, "If-None-Match": etag})
                response = connection.getresponse()
                self.assertEqual(response.status, 304)
                self.assertEqual(response.read(), b"")
                connection.request("GET", page["next"], headers={"Origin": self.origin})
                response = connection.getresponse()
                self.assertEqual(response.status, 200)
                next_page = json.loads(response.read())["data"]
                self.assertEqual(next_page["total"], page["total"])
                self.assertEqual(next_page["offset"], 1)
                self.assertNotEqual(next_page["items"][0]["ref"], page["items"][0]["ref"])
            finally:
                connection.close()

    def test_rejects_first_page_when_a_later_continuation_would_exceed_limit(self):
        # For this 19-row fixture, offset=1 fits but offset=10 would not.
        raw = "limit=1&q=id" + "+" * 8097
        self.assertLess(len(raw), web.MAX_QUERY_BYTES)
        response = request(self.app, "/api/v1/records?" + raw)
        self.assertEqual(response["status"], 414)
        error = json.loads(response["body"])["error"]
        self.assertEqual(error["code"], "generated_query_too_long")
        self.assertNotIn("data", json.loads(response["body"]))

    def test_all_pages_at_the_generated_query_limit_are_followable(self):
        raw = "limit=1&q=id" + "+" * 8096
        route = "/api/v1/records?" + raw
        pages, total, longest = 0, None, 0
        while route:
            response = request(self.app, route)
            self.assertEqual(response["status"], 200, response["body"][:300])
            page = json.loads(response["body"])["data"]
            total = page["total"]
            self.assertEqual(len(page["items"]), 1)
            route = page["next"]
            if route:
                length = len(urlsplit(route).query.encode("ascii"))
                longest = max(longest, length)
                self.assertLessEqual(length, web.MAX_QUERY_BYTES)
            pages += 1
            self.assertLessEqual(pages, total)
        self.assertEqual(pages, total)
        self.assertEqual(longest, web.MAX_QUERY_BYTES)

    def test_near_limit_query_with_no_continuation_still_succeeds(self):
        raw = "limit=1&q=missing-token" + "+" * 8100
        response = request(self.app, "/api/v1/records?" + raw)
        self.assertEqual(response["status"], 200)
        page = json.loads(response["body"])["data"]
        self.assertEqual((page["total"], page["next"]), (0, None))

    def test_unpageable_total_is_rejected_before_a_broken_offset_is_emitted(self):
        synthetic = {"pagination": {"total": web.MAX_OFFSET + 2},
                     "links": [], "passage_cards": []}
        with patch.object(self.app._reader, "query_reading", return_value=synthetic):
            response = request(self.app, "/api/v1/papers/reading", {"paper": "short", "limit": 1})
        self.assertEqual(response["status"], 400)
        self.assertEqual(json.loads(response["body"])["error"]["code"], "pagination_out_of_range")

    def test_long_detail_link_is_explicitly_unavailable_without_rejecting_bundle(self):
        with tempfile.TemporaryDirectory(prefix="web-long-id-") as temporary:
            root = corpus_bundle(Path(temporary))
            graph = json.loads((root / "graph.json").read_bytes())
            identity = "μ" * 802 + "x" * 8
            graph["sources"].append({**graph["sources"][0], "id": identity})
            bind(root, graph=graph)
            app = web.create_app(root)
            listed = request(app, "/api/v1/records?table=sources&limit=200")
            self.assertEqual(listed["status"], 200)
            rows = json.loads(listed["body"])["data"]["items"]
            row = next(row for row in rows if row["record"]["id"] == identity)
            self.assertEqual(len(urlsplit(row["href"]).query.encode("ascii")), web.MAX_QUERY_BYTES)
            self.assertEqual(request(app, row["href"])["status"], 200)

            graph["sources"][-1]["id"] += "x"
            bind(root, graph=graph)
            app = web.create_app(root)
            for representation in ("full", "summary"):
                listed = request(app, "/api/v1/records", {
                    "table": "sources", "limit": 200, "representation": representation})
                self.assertEqual(listed["status"], 200)
                rows = json.loads(listed["body"])["data"]["items"]
                row = next(row for row in rows if
                           (row["record"]["id"] if representation == "full" else row["id"]) == identity + "x")
                self.assertIsNone(row["href"])
                self.assertEqual(row["href_unavailable_reason"], "generated_query_too_long")
            search = request(app, "/api/v1/search", {"table": "sources", "q": "μ", "limit": 200})
            self.assertEqual(search["status"], 200)
            item = json.loads(search["body"])["data"]["items"][0]
            self.assertIsNone(item["href"])
            self.assertEqual(item["href_unavailable_reason"], "generated_query_too_long")

    def test_summary_and_map_preserve_current_and_historical_formal_assurance(self):
        with tempfile.TemporaryDirectory(prefix="web-assurance-") as temporary:
            parent = Path(temporary)
            report, build = extraction_fixture(parent)
            raw = {key: value for key, value in report.items() if key != "receipt"}
            stdout = ("LEAN_EXPOSITION_JSON:" + json.dumps(raw) + "\ntrailing log\n").encode()
            process = {"status": "passed", "process_status": "passed", "returncode": 0,
                       "command": ["custom-wrapper", "driver.lean"],
                       "source_hashes": report["receipt"]["source_hashes"], "source_changed": False,
                       **_stream_fields(stdout, b"")}
            with patch("lean_exposition.verification._run_bound", return_value=process):
                current = extract_dependencies(parent, "Minimal", ["result"], lean_command=["custom-wrapper"])
            build["process_status"] = "passed"
            graph = to_graph(current, parent, build)
            root = parent / "bundle"
            bundle.scaffold(graph, root)
            for eligible in (True, False):
                with self.subTest(eligible=eligible):
                    if not eligible:
                        graph = copy.deepcopy(graph)
                        next(row for row in graph["evidence"] if row["kind"] == "extraction")["receipt"].pop("report_stdout_binding")
                        bind(root, graph=graph)
                    app = web.create_app(root)
                    full = request(app, "/api/v1/records", {"table": "nodes", "representation": "full"})
                    summary = request(app, "/api/v1/records", {"table": "nodes", "representation": "summary"})
                    compact = request(app, "/api/v1/graph", {"view": "arguments", "node": "result", "representation": "map"})
                    self.assertEqual([full["status"], summary["status"], compact["status"]], [200, 200, 200])
                    full_row = json.loads(full["body"])["data"]["items"][0]
                    summary_row = json.loads(summary["body"])["data"]["items"][0]
                    compact_data = json.loads(compact["body"])["data"]
                    compact_row = compact_data["records"]["nodes"][0]
                    assurance = full_row["formal_result_assurance"]
                    self.assertEqual(full_row["record"]["status"], "kernel_checked")
                    self.assertIs(assurance["formal_result_eligible"], eligible)
                    self.assertEqual(summary_row["formal_result_assurance"], assurance)
                    self.assertEqual(compact_row["formal_result_assurance"], assurance)
                    self.assertEqual(compact_data["coverage"]["formal_result_assurances"]["result"], assurance)


if __name__ == "__main__":
    unittest.main()
