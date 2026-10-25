"""Reading guidance stays authored, edition-bound and separate from proof relations."""
from __future__ import annotations

import copy
import json
import shutil
import tempfile
import unittest
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from unittest.mock import patch

from lean_exposition import bundle, consumer
from lean_exposition.contracts import ContractError, digest, encoded
from test_corpus_views import bind
from test_paper_views import authored_bundle


def reading_bundle(parent):
    root = authored_bundle(parent, cycle=True, formalization=True)
    original = json.loads((root / "papers/short.json").read_bytes())
    mappings = {}
    for stage in bundle.STAGES:
        mapping = copy.deepcopy(original)
        mapping.update(schema_version="1.2", stage=stage, path=f"papers/{stage}.md")
        rows = mapping["passages"]
        if stage == "short":
            rows[0]["treatments"] = [{"claim_id": "goal", "kinds": ["statement"],
                                      "rationale": "States the conditional result."}]
            rows.append({"anchor": "question", "claim_ids": [], "citation_ids": [],
                         "assumption_ids": [], "evidence_class": "open_question", "rationale": "A reading question."})
        elif stage == "long":
            detail = copy.deepcopy(rows[0])
            detail.update(anchor="detail", claim_ids=["goal", "prerequisite"], treatments=[
                {"claim_id": "goal", "kinds": ["derivation", "explanation"], "rationale": "Detailed argument."},
                {"claim_id": "prerequisite", "kinds": ["application"], "rationale": "Uses the conditional premise."},
            ])
            rows.append(detail)
            rows.append({"anchor": "answer", "claim_ids": [], "citation_ids": [],
                         "assumption_ids": [], "evidence_class": "context", "rationale": "An explicit reading answer."})
        else:
            # Being an example does not authorize a per-claim illustration treatment.
            rows[0]["evidence_class"] = "example"
        pieces = [f"# {stage.title()} paper\n"]
        for row in rows:
            text = f"\n{stage} μ-{row['anchor']} text.\n"
            row["text_sha256"] = digest(text.encode())
            pieces.append(f"## {row['anchor'].title()}\n<!-- passage:{row['anchor']} -->"
                          + text + f"<!-- /passage:{row['anchor']} -->\n")
        raw = "".join(pieces).encode()
        (root / f"papers/{stage}.md").write_bytes(raw)
        mapping["content_sha256"] = digest(raw)
        mappings[stage] = mapping

    def link(stage, source, target_stage, target, kind):
        source_row = next(p for p in mappings[stage]["passages"] if p["anchor"] == source)
        target_row = next(p for p in mappings[target_stage]["passages"] if p["anchor"] == target)
        return {"from_anchor": source, "from_text_sha256": source_row["text_sha256"],
                "to_stage": target_stage, "to_anchor": target,
                "to_text_sha256": target_row["text_sha256"], "kind": kind,
                "rationale": "Authored reading guidance only."}

    mappings["long"]["reading_links"] = [
        link("long", "detail", "short", "result", "expands"),
        link("long", "answer", "short", "question", "answers"),
        link("long", "detail", "long", "result", "expands"),
    ]
    mappings["expository"]["reading_links"] = [link("expository", "result", "long", "detail", "illustrates")]
    for stage, mapping in mappings.items():
        (root / f"papers/{stage}.json").write_bytes(encoded(mapping))
    bind(root)
    return root


def many_shared_passages(parent, count):
    """Small valid input with quadratically many shared-claim correspondences."""
    root = authored_bundle(parent)
    base = json.loads((root / "papers/short.json").read_bytes())
    for stage in bundle.STAGES:
        mapping = copy.deepcopy(base)
        mapping.update(stage=stage, path=f"papers/{stage}.md")
        mapping["passages"] = []
        parts = ["# Paper\n"]
        for position in range(count + 1):
            passage = copy.deepcopy(base["passages"][0 if position < count else 1])
            passage["anchor"] = f"p{position:04}" if position < count else "premise"
            text = f"\n{stage} paragraph {position}.\n"
            passage["text_sha256"] = digest(text.encode())
            mapping["passages"].append(passage)
            parts.append(f"<!-- passage:{passage['anchor']} -->" + text
                         + f"<!-- /passage:{passage['anchor']} -->\n")
        raw = "".join(parts).encode()
        mapping["content_sha256"] = digest(raw)
        (root / f"papers/{stage}.md").write_bytes(raw)
        (root / f"papers/{stage}.json").write_bytes(encoded(mapping))
    bind(root)
    return root


class ReadingViewTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="lean-exposition-reading-")
        self.addCleanup(temporary.cleanup)
        self.parent = Path(temporary.name)
        self.root = reading_bundle(self.parent)
        self.session = consumer.ConsumerSession(self.root)
        self.manifest = self.session.project_corpus()["snapshot"]["manifest_sha256"]

    def passage(self, stage, anchor):
        return next(p for p in self.session.project_paper(stage)["paper"]["passages"] if p["anchor"] == anchor)

    def test_exact_cards_and_mapping_provenance_retain_original_directions(self):
        result = self.session.query_reading(stage="short", passages=["result"])
        self.assertEqual(result["reading_view_version"], consumer.READING_VIEW_VERSION)
        self.assertFalse(result["semantic_certification"])
        selected = self.passage("short", "result")
        self.assertEqual(result["source_passage_refs"], [selected["ref"]])
        cards = {row["ref"]: row for row in result["passage_cards"]}
        for ref, card in cards.items():
            original = self.passage(card["stage"], card["anchor"])
            self.assertEqual(card["content_span"], original["content_span"])
            self.assertEqual(card["section_ref"], original["section_ref"])
            self.assertEqual(card["section_title"], card["anchor"].title())
            self.assertNotIn("text", card)
            self.assertNotIn("rationale", card)
            self.assertNotIn("status", card)
            self.assertTrue(ref.startswith("sha256:"))
        authored = [link for link in result["links"] if not link["derived"]]
        self.assertEqual(len(authored), 1)
        link = authored[0]
        self.assertEqual(link["from"], self.passage("long", "detail")["ref"])
        self.assertEqual(link["to"], selected["ref"])
        self.assertEqual(link["annotation_basis"], "authored_reading_link")
        self.assertEqual(link["kind"], "expands")
        self.assertEqual(link["selection_relation"], "incoming")
        mapping = json.loads((self.root / "papers/long.json").read_bytes())
        self.assertEqual({key: link[key] for key in mapping["reading_links"][0]}, mapping["reading_links"][0])
        self.assertEqual(link["source_ref"], self.session.project_paper("long")["bundle"]["mapping_ref"])
        self.assertEqual(link["source_field"], "reading_links")
        self.assertEqual(link["source_index"], 0)
        self.assertEqual(set(cards), {selected["ref"]} | {link[key] for link in result["links"] for key in ("from", "to")})

    def test_shared_claims_are_exact_and_treatments_stay_explicit_and_relevant(self):
        result = self.session.query_reading(stage="short", passages=["result"])
        shared = [link for link in result["links"] if link["derived"]]
        self.assertEqual({link["to"] for link in shared}, {
            self.passage("long", "result")["ref"], self.passage("long", "detail")["ref"],
            self.passage("expository", "result")["ref"],
        })
        for link in shared:
            self.assertEqual(link["annotation_basis"], "shared_claim_ids")
            self.assertEqual(link["kind"], "shared_claim")
            self.assertEqual(link["selection_relation"], "outgoing")
            self.assertEqual(len(link["shared_claim_refs"]), 1)
            self.assertTrue(link["shared_claim_refs"][0].endswith("/nodes/goal"))
            self.assertEqual(link["source_treatments"][0]["kinds"], ["statement"])
            self.assertNotIn("score", link)
            self.assertNotIn("rationale", link)
        detail = next(link for link in shared if link["to"] == self.passage("long", "detail")["ref"])
        self.assertEqual([row["claim_id"] for row in detail["target_treatments"]], ["goal"])
        self.assertEqual(detail["target_treatments"][0]["kinds"], ["derivation", "explanation"])
        example = next(link for link in shared if link["to"] == self.passage("expository", "result")["ref"])
        self.assertEqual(example["target_treatments"], [])
        # Shared references do not pull in the prerequisite's passages, formalization,
        # citations or assumptions, even though those graph relations are present.
        self.assertFalse(any(card["anchor"] == "premise" for card in result["passage_cards"]))
        self.assertIn("unspecified", result["coverage"]["treatment_policy"])
        self.assertIn("Further consequences", result["coverage"]["scope"])

    def test_zero_claim_routes_survive_both_directions(self):
        for stage, anchor, target in (("short", "question", "long"), ("long", "answer", "short")):
            result = self.session.query_reading(stage=stage, passages=[anchor], target_stage=target)
            self.assertEqual(len(result["links"]), 1)
            link = result["links"][0]
            self.assertFalse(link["derived"])
            self.assertEqual(link["kind"], "answers")
            self.assertEqual(link["selection_relation"], "incoming" if stage == "short" else "outgoing")
            self.assertEqual(link["from"], self.passage("long", "answer")["ref"])
            self.assertEqual(link["to"], self.passage("short", "question")["ref"])
            self.assertTrue(all(card["claim_refs"] == [] and card["treatments"] == [] for card in result["passage_cards"]))
        self.assertEqual(self.session.query_reading(stage="short", passages=["question"], target_stage="expository")["links"], [])

    def test_target_stage_filters_other_endpoint_and_explicit_same_stage(self):
        default = self.session.query_reading(stage="long", passages=["detail", "result"])
        same = self.session.query_reading(stage="long", passages=["result", "detail"], target_stage="long")
        same_links = same["links"]
        self.assertEqual(len([link for link in same_links if not link["derived"]]), 1)
        self.assertEqual(next(link for link in same_links if not link["derived"])["selection_relation"], "internal")
        self.assertEqual(len({link["id"] for link in same_links}), len(same_links))
        self.assertEqual(len([link for link in same_links if link["derived"]]), 3)  # detail↔result and detail→premise
        self.assertEqual([link["selection_relation"] for link in same_links if link["derived"]].count("internal"), 2)
        self.assertFalse(any(link["derived"] and link["to"] in same["source_passage_refs"] for link in default["links"]))
        expository = self.session.query_reading(stage="long", passages=["detail"], target_stage="expository")
        incoming = next(link for link in expository["links"] if not link["derived"])
        self.assertEqual(incoming["from"], self.passage("expository", "result")["ref"])
        self.assertEqual(incoming["to"], self.passage("long", "detail")["ref"])
        self.assertNotEqual(default["cache_key"], same["cache_key"])
        self.assertEqual(same, self.session.query_reading(stage="long", passages=["detail", "result"], target_stage="long"))

    def test_range_and_section_selection_reuse_exact_paper_query_contract(self):
        selected = self.passage("short", "result")
        raw = (self.root / "papers/short.md").read_bytes()
        start = raw.index("μ-result".encode())
        queries = [
            {"passages": []}, {"passages": ["result"]}, {"section_refs": [selected["section_ref"]]},
            {"byte_ranges": [(start, start + len("μ-result".encode()))]},
            {"byte_ranges": [(0, 1)]},
            {"passages": ["premise"], "section_refs": [selected["section_ref"]]},
        ]
        for query in queries:
            with self.subTest(query=query):
                paper = self.session.query_papers(stage="short", expected_manifest_sha256=self.manifest,
                                                   include_views=False, **query)
                actual = self.session.query_reading(stage="short", expected_manifest_sha256=self.manifest, **query)
                self.assertEqual(actual["source_passage_refs"], [row["passage_ref"] for row in paper["papers"][0]["matches"]])
                if not actual["source_passage_refs"]:
                    self.assertEqual(actual["links"], [])
                    self.assertEqual(actual["passage_cards"], [])
        invalid = [
            {"byte_ranges": [(start + 1, start + 2)], "expected_manifest_sha256": self.manifest},
            {"byte_ranges": [(start, start + 2)]},
            {"expected_manifest_sha256": "0" * 64}, {"passages": ["unknown"]},
            {"passages": ["result", "result"]}, {"section_refs": ["missing"]},
            {"target_stage": "absent"}, {"target_stage": []},
        ]
        for query in invalid:
            with self.subTest(query=query), self.assertRaises(ContractError):
                self.session.query_reading(stage="short", **query)
        for stage in (None, [], "absent"):
            with self.subTest(stage=stage), self.assertRaises(ContractError):
                self.session.query_reading(stage=stage)

    def test_capture_zip_and_session_are_equivalent_after_original_disappears(self):
        archive = self.parent / "reading.zip"
        bundle.export_bundle(self.root, archive)
        capture = bundle.BundleCapture(self.root)
        query = {"stage": "short", "passages": ["result"], "expected_manifest_sha256": self.manifest}
        expected = self.session.query_reading(**query)
        self.assertEqual(consumer.query_reading(self.root, **query), expected)
        self.assertEqual(consumer.query_reading(archive, **query), expected)
        (self.root / "papers/long.md").write_text("changed original")
        shutil.rmtree(self.root)
        self.assertEqual(consumer.query_reading(capture, **query), expected)
        self.assertEqual(consumer.query_reading(self.session, **query), expected)

    def test_reader_rejects_stale_link_bindings_before_building_navigation(self):
        original = json.loads((self.root / "papers/long.json").read_bytes())
        expected = self.session.query_reading(stage="long", passages=["detail"])
        for field in ("from_text_sha256", "to_text_sha256"):
            broken = copy.deepcopy(original)
            broken["reading_links"][0][field] = "0" * 64
            bind(self.root, mapping=broken, stage="long")
            with self.subTest(field=field), self.assertRaises(ContractError):
                consumer.query_reading(self.root, stage="long", passages=["detail"])
            self.assertEqual(self.session.query_reading(stage="long", passages=["detail"]), expected)
        bind(self.root, mapping=original, stage="long")

    def test_pages_equal_full_order_and_keep_only_selected_sources_and_page_endpoints(self):
        for stage in bundle.STAGES:
            for target in (None, *bundle.STAGES):
                query = {"stage": stage, "target_stage": target}
                full = self.session.query_reading(**query)
                self.assertNotIn("pagination", full)
                self.assertEqual(full, self.session.query_reading(**query, offset=0, limit=None))
                self.assertEqual(full["links"], sorted(full["links"], key=lambda row: (
                    row["annotation_basis"], row["from"], row["to"], row["kind"], row["id"])))
                count = len(full["links"])
                for offset in {0, 1, max(0, count - 1), count, count + 4}:
                    for limit in (1, 2, 100):
                        with self.subTest(stage=stage, target=target, offset=offset, limit=limit):
                            page = self.session.query_reading(**query, offset=offset, limit=limit)
                            self.assertEqual(page["links"], full["links"][offset:offset + limit])
                            self.assertEqual(page["pagination"], {"offset": offset, "limit": limit, "total": count})
                            self.assertEqual(page["source_passage_refs"], full["source_passage_refs"])
                            needed = set(page["source_passage_refs"]) | {
                                link[key] for link in page["links"] for key in ("from", "to")}
                            self.assertEqual(page["passage_cards"], [card for card in full["passage_cards"] if card["ref"] in needed])
                            self.assertNotEqual(page["cache_key"], full["cache_key"])
                            self.assertEqual(page["query"], full["query"] | {"offset": offset, "limit": limit})
                self.assertEqual([link for offset in range(0, count, 2)
                                  for link in self.session.query_reading(**query, offset=offset, limit=2)["links"]],
                                 full["links"])
        expected = self.session.query_reading(stage="short", passages=["question"], limit=1)
        self.assertEqual(consumer.query_reading(self.root, stage="short", passages=["question"], limit=1), expected)

    def test_bad_pagination_is_rejected_before_selection_or_capture(self):
        invalid = [{"offset": value, "limit": 1} for value in (-1, True, None, 0.5, "0")] + [
            {"limit": value} for value in (0, -1, True, 0.5, "1")] + [{"offset": 1}]
        with patch.object(consumer, "query_papers", side_effect=AssertionError("selection must not run")):
            for query in invalid:
                with self.subTest(query=query), self.assertRaises(ContractError):
                    self.session.query_reading(stage="short", **query)
                with self.subTest(query=query, source="missing"), self.assertRaisesRegex(ContractError, "reading (offset|limit)"):
                    consumer.query_reading(self.parent / "missing", stage="short", **query)

    def test_large_shared_index_constructs_and_hashes_only_retained_page_pairs(self):
        parent = self.parent / "many"
        parent.mkdir()
        session = consumer.ConsumerSession(many_shared_passages(parent, 200))
        original_digest = consumer.digest
        pair_hashes = []

        def counted_digest(content):
            if content.startswith(b"{"):
                value = json.loads(content)
                if set(value) == {"from", "to", "claims"}:
                    pair_hashes.append(value)
            return original_digest(content)

        with patch.object(consumer, "_shared_reading_link", wraps=consumer._shared_reading_link) as build, \
             patch.object(consumer, "digest", side_effect=counted_digest):
            first = session.query_reading(stage="short", limit=1)
            self.assertEqual(first["pagination"]["total"], 80002)
            self.assertEqual(build.call_count, 1)
            self.assertEqual(len(pair_hashes), 1)
            self.assertEqual(len(first["links"]), 1)
            self.assertEqual(len(first["source_passage_refs"]), 201)
            self.assertEqual(len(first["passage_cards"]), 202)
            tail = session.query_reading(stage="short", offset=80000, limit=4)
            self.assertEqual(tail["pagination"]["total"], 80002)
            self.assertEqual(len(tail["links"]), 2)
            self.assertEqual(build.call_count, 3)
            self.assertEqual(len(pair_hashes), 3)
            empty = session.query_reading(stage="short", offset=80002, limit=4)
            self.assertEqual(empty["links"], [])
            self.assertEqual(len(empty["passage_cards"]), 201)
            self.assertEqual(build.call_count, 3)
        stable = copy.deepcopy(first)
        first["links"][0]["shared_claim_refs"].append("invented")
        first["passage_cards"][0]["claim_refs"].append("invented")
        self.assertEqual(session.query_reading(stage="short", limit=1), stable)

    def test_prepared_index_is_reused_and_results_are_detached_under_concurrency(self):
        with patch.object(consumer, "_prepare_reading_index", wraps=consumer._prepare_reading_index) as prepare:
            session = consumer.ConsumerSession(self.root)
            self.assertEqual(prepare.call_count, 1)
            queries = [{"stage": stage, "target_stage": target} for stage in bundle.STAGES for target in (None, *bundle.STAGES)]
            expected = [session.query_reading(**query) for query in queries]
            with patch.object(consumer, "_project_paper", side_effect=AssertionError("prepared document reused")), \
                 patch.object(consumer, "decode_json", side_effect=AssertionError("prepared mappings reused")):
                with ThreadPoolExecutor(max_workers=4) as executor:
                    actual = list(executor.map(lambda query: session.query_reading(**query), queries))
            self.assertEqual(actual, expected)
            self.assertEqual(prepare.call_count, 1)
        changed = session.query_reading(stage="short", passages=["result"])
        stable = copy.deepcopy(changed)
        changed["passage_cards"][0]["content_span"]["start_byte"] = -1
        changed["links"][0]["kind"] = "invented"
        next(card for card in changed["passage_cards"] if card["treatments"])["treatments"][0]["kinds"].append("invented")
        self.assertEqual(session.query_reading(stage="short", passages=["result"]), stable)

    def test_optional_metadata_projection_does_not_change_legacy_views_or_graph_authority(self):
        new = self.session.project_paper("long")
        self.assertEqual(new["reading_view_version"], consumer.READING_VIEW_VERSION)
        mapping = json.loads((self.root / "papers/long.json").read_bytes())
        self.assertEqual(new["reading_links"], mapping["reading_links"])
        self.assertIn("treatments", self.passage("long", "detail"))
        self.assertNotIn("treatments", self.passage("long", "result"))
        before = self.session.project_graph("arguments")
        self.session.query_reading(stage="long")
        self.assertEqual(self.session.project_graph("arguments"), before)
        legacy_parent = self.parent / "legacy"
        legacy_parent.mkdir()
        legacy_root = authored_bundle(legacy_parent)
        for version in ("1.0", "1.1"):
            legacy_mapping = json.loads((legacy_root / "papers/short.json").read_bytes())
            legacy_mapping["schema_version"] = version
            bind(legacy_root, mapping=legacy_mapping)
            original = consumer.project_paper(legacy_root, "short")
            session = consumer.ConsumerSession(legacy_root)
            self.assertNotIn("reading_view_version", original)
            self.assertNotIn("reading_links", original)
            self.assertTrue(all("treatments" not in row for row in original["paper"]["passages"]))
            self.assertEqual(session.project_paper("short"), original)
            result = session.query_reading(stage="short")
            self.assertEqual(result["links"], [])
            self.assertTrue(all(row["treatments"] == [] for row in result["passage_cards"]))
            self.assertEqual(session.project_paper("short"), original)


if __name__ == "__main__":
    unittest.main()
