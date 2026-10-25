"""Real manuscript journeys through authored and derived reading relationships."""
from __future__ import annotations

import http.client
import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch
from urllib.parse import parse_qs, urlsplit

from lean_exposition import bundle, consumer, web
from test_web import local_server, request
from test_reading_views import reading_bundle

ROOT = Path(__file__).resolve().parents[1]


class WebReadingPaginationTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="reading-page-http-")
        self.addCleanup(temporary.cleanup)
        self.app = web.create_app(reading_bundle(Path(temporary.name)), cache_bytes=0)

    def test_invalid_paging_rejects_before_consumer_work(self):
        with patch.object(self.app._reader, "query_reading", side_effect=AssertionError("must not query")):
            for key, value in (("limit", "0"), ("limit", "201"), ("limit", "many"),
                               ("offset", "-1"), ("offset", "1000000000")):
                with self.subTest(key=key, value=value):
                    self.assertEqual(request(self.app, "/api/v1/papers/reading",
                                             {"paper": "long", key: value})["status"], 400)

    def test_transport_pages_in_consumer_and_returns_exact_total(self):
        expected = self.app._reader.query_reading(stage="long")
        with patch.object(self.app._reader, "query_reading", wraps=self.app._reader.query_reading) as query:
            response = request(self.app, "/api/v1/papers/reading", {"paper": "long", "offset": 1, "limit": 1})
        self.assertEqual(response["status"], 200, response["body"])
        self.assertEqual(query.call_args.kwargs["offset"], 1)
        self.assertEqual(query.call_args.kwargs["limit"], 1)
        data = json.loads(response["body"])["data"]
        self.assertEqual(data["items"], expected["links"][1:2])
        self.assertEqual(data["total"], len(expected["links"]))
        self.assertNotIn("pagination", data)
        self.assertNotIn("links", data)
        self.assertEqual(parse_qs(urlsplit(data["next"]).query)["offset"], ["2"])
        refs = set(expected["source_passage_refs"])
        refs.update(ref for row in data["items"] for ref in (row["from"], row["to"]))
        self.assertEqual({card["ref"] for card in data["passage_cards"]}, refs)


class WebReadingTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temporary = tempfile.TemporaryDirectory(prefix="reading-http-")
        cls.addClassCleanup(cls.temporary.cleanup)
        cls.root = Path(cls.temporary.name) / "bundle"
        papers = ROOT / "papers/qaoa-sk"
        bundle.assemble_bundle(ROOT / "examples/qaoa-sk/evidence-graph.json", {
            "long": (papers / "long/reasoning-record.md", papers / "long/reasoning-record.json"),
            "short": (papers / "short/paper.md", papers / "short/correspondence.json"),
            "expository": (papers / "expository/main.md", papers / "expository/correspondence.json"),
        }, cls.root)
        cls.app = web.create_app(cls.root)
        cls.reader = consumer.ConsumerSession(cls.root)

    def data(self, route, query=None):
        result = request(self.app, route, query)
        self.assertEqual(result["status"], 200, result["body"])
        return json.loads(result["body"])["data"]

    def test_reference_and_derivation_are_different_accounts_of_same_claim(self):
        result = self.data("/api/v1/papers/reading", {
            "paper": "expository", "passage": "density-and-approximation", "target": "short"})
        cards = {row["ref"]: row for row in result["passage_cards"]}
        source = cards[result["source_passage_refs"][0]]
        self.assertEqual(source["treatments"][0]["kinds"], ["reference"])
        expansions = [link for link in result["items"] if link["kind"] == "expands"]
        self.assertEqual(len(expansions), 1)
        self.assertEqual(expansions[0]["to"], source["ref"])
        self.assertEqual(cards[expansions[0]["from"]]["anchor"], "density-consequence")
        shared = next(link for link in result["items"] if link["kind"] == "shared_claim"
                      and cards[link["to"]]["anchor"] == "density-consequence")
        self.assertIn("derivation", shared["target_treatments"][0]["kinds"])
        self.assertTrue(shared["derived"])
        self.assertFalse(expansions[0]["derived"])
        self.assertNotEqual(shared["annotation_basis"], expansions[0]["annotation_basis"])
        self.assertFalse(result["semantic_certification"])
        target = cards[shared["to"]]
        selected = self.data(target["query_href"])
        self.assertEqual(selected["papers"][0]["passages"][0]["anchor"], "density-consequence")
        self.assertIn("treatments", selected["papers"][0]["passages"][0])

    def test_exercise_and_illustration_do_not_acquire_research_claims(self):
        for anchor, kind, counterpart in (("changed-cases", "answers", "changed-case-answer"),
                                           ("correction-example", "illustrates", "curvature-mechanism")):
            result = self.data("/api/v1/papers/reading", {"paper": "expository", "passage": anchor})
            cards = {row["ref"]: row for row in result["passage_cards"]}
            selected = cards[result["source_passage_refs"][0]]
            self.assertEqual(selected["claim_refs"], [])
            self.assertEqual(selected["treatments"], [])
            self.assertEqual({link["kind"] for link in result["items"]}, {kind})
            self.assertTrue(any(row["anchor"] == counterpart for row in cards.values()))

    def test_pagination_keeps_page_endpoints_and_exact_selection(self):
        query = {"paper": "expository", "passage": "curvature-transfer", "target": "long", "limit": 1}
        route, rows, seen = "/api/v1/papers/reading", [], set()
        while route:
            self.assertNotIn(route, seen)
            seen.add(route)
            data = self.data(route, query)
            query = None
            rows.extend(data["items"])
            needed = set(data["source_passage_refs"])
            needed.update(ref for link in data["items"] for ref in (link["from"], link["to"]))
            self.assertEqual({card["ref"] for card in data["passage_cards"]}, needed)
            for card in data["passage_cards"]:
                self.assertNotIn("text", card)
                self.assertEqual(parse_qs(urlsplit(card["reading_href"]).query)["manifest"], [self.app.manifest_sha256])
            route = data["next"]
        expected = self.reader.query_reading(stage="expository", passages=["curvature-transfer"], target_stage="long")
        self.assertEqual(rows, expected["links"])
        self.assertEqual(len(rows), data["total"])
        self.assertEqual(len(rows), len({row["id"] for row in rows}))

    def test_reading_ranges_pins_and_conditional_http(self):
        source = next(p for p in self.reader.project_paper("expository")["paper"]["passages"]
                      if p["anchor"] == "changed-cases")
        query = {"paper": "expository", "start": source["content_span"]["start_byte"],
                 "end": source["content_span"]["end_byte"], "manifest": self.app.manifest_sha256}
        full = request(self.app, "/api/v1/papers/reading", query)
        self.assertEqual(full["status"], 200)
        head = request(self.app, "/api/v1/papers/reading", query, method="HEAD")
        self.assertEqual(head["body"], b"")
        self.assertEqual(head["headers"], full["headers"])
        conditional = request(self.app, "/api/v1/papers/reading", query,
                              headers={"If-None-Match": full["headers"]["ETag"]})
        self.assertEqual(conditional["status"], 304)
        query.pop("manifest")
        self.assertEqual(request(self.app, "/api/v1/papers/reading", query)["status"], 400)
        query["manifest"] = "0" * 64
        self.assertEqual(request(self.app, "/api/v1/papers/reading", query)["status"], 409)
        self.assertEqual(request(self.app, "/api/v1/papers/reading")["status"], 400)
        self.assertEqual(request(self.app, "/api/v1/papers/reading", {"paper": "short", "node": "full_support"})["status"], 400)
        with local_server(self.app) as port:
            connection = http.client.HTTPConnection("127.0.0.1", port, timeout=5)
            try:
                connection.request("GET", "/api/v1/papers/reading?paper=expository&passage=changed-cases")
                response = connection.getresponse()
                self.assertEqual(response.status, 200)
                self.assertEqual(json.loads(response.read())["data"]["items"][0]["kind"], "answers")
            finally:
                connection.close()

    def test_structure_and_record_passages_link_to_reading_context(self):
        structure = self.data("/api/v1/papers/expository/structure")
        self.assertEqual(structure["reading_view_version"], consumer.READING_VIEW_VERSION)
        self.assertIn("answers", {link["kind"] for link in structure["reading_links"]})
        self.assertIn("reading_href", structure["resources"])
        record = self.data("/api/v1/records", {"table": "nodes", "q": "scalar.smooth_positive_density"})
        selected = next(row for row in record["items"] if row["record"]["id"] == "scalar.smooth_positive_density")
        detail = self.data(selected["href"])
        for aligned in detail["aligned_passages"]:
            self.assertEqual(len(self.data(aligned["reading_href"])["source_passage_refs"]), 1)


if __name__ == "__main__":
    unittest.main()
