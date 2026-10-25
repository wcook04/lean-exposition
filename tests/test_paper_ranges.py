"""Exact source selections retain authored correspondence and edition identity."""
from __future__ import annotations

import contextlib
import io
import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from lean_exposition import bundle, consumer
from lean_exposition.cli import main
from lean_exposition.consumer import project_paper, query_papers
from lean_exposition.contracts import ContractError, digest
from test_paper_queries import rebind
from test_paper_views import authored_bundle


CONTENT = (
    "# Paper\nUnmapped introduction.\n"
    "## Premise\n<!-- passage:premise -->\nα🙂 premise.\n<!-- /passage:premise -->\n"
    "## Result\n<!-- passage:result -->\n\t\u2003\nThe μ-result follows.\nTail explanation.\n"
    "<!-- /passage:result -->\n"
    "## Unmapped\nAn unmapped claim is still prose.\n"
).encode("utf-8")


def fixture(parent: Path) -> tuple[Path, str]:
    root = authored_bundle(parent, formalization=True)
    rebind(root, content=CONTENT)
    return root, digest((root / "manifest.json").read_bytes())


def occurrence(text: str) -> tuple[int, int]:
    raw = text.encode("utf-8")
    start = CONTENT.index(raw)
    return start, start + len(raw)


def content_range(anchor: str) -> tuple[int, int]:
    opening = f"<!-- passage:{anchor} -->".encode()
    return (CONTENT.index(opening) + len(opening),
            CONTENT.index(f"<!-- /passage:{anchor} -->".encode()))


class PaperRangeTests(unittest.TestCase):
    def query(self, root, manifest, ranges, **selectors):
        return query_papers(root, stage="short", byte_ranges=ranges,
                            expected_manifest_sha256=manifest, **selectors)

    def test_unicode_fragment_keeps_whole_passage_and_recorded_support(self):
        with tempfile.TemporaryDirectory() as temporary:
            root, manifest = fixture(Path(temporary))
            start, end = occurrence("μ-result")
            result = self.query(root, manifest, [(start, end)])
            self.assertEqual(result["paper_query_version"], "0.4.1")
            self.assertEqual(result["query"]["byte_ranges"], [[start, end]])
            self.assertTrue(result["query"]["range_policy"])
            self.assertEqual(result["match_count"], 1)
            paper = result["papers"][0]
            match = paper["matches"][0]
            self.assertEqual(match["anchor"], "result")
            self.assertEqual(match["byte_overlaps"], [{
                "requested_range": {"start_byte": start, "end_byte": end},
                "overlap_span": {"start_byte": start, "end_byte": end},
            }])
            self.assertTrue(match["whole_passage_extends_beyond_selected_ranges"])
            selected = [p for p in paper["view"]["paper"]["passages"] if p["selected"]]
            self.assertEqual(len(selected), 1)
            self.assertIn("Tail explanation.", selected[0]["text"])
            self.assertEqual(paper["support_boundary"]["retained_node_ids"],
                             ["assumption", "decl", "goal", "prerequisite"])
            self.assertEqual(paper["view"]["graph"]["records"]["evidence"][0]["record"]["status"], "failed")
            self.assertFalse(result["semantic_certification"])
            self.assertEqual((root / "papers/short.md").read_bytes(), CONTENT)

    def test_marker_unmapped_and_unicode_whitespace_do_not_create_correspondence(self):
        with tempfile.TemporaryDirectory() as temporary:
            root, manifest = fixture(Path(temporary))
            for text in ("<!-- passage:result -->", "<!-- /passage:result -->",
                         "An unmapped claim is still prose.", "\n\t\u2003\n"):
                with self.subTest(text=text):
                    result = self.query(root, manifest, [occurrence(text)])
                    self.assertEqual(result["match_count"], 0)
                    self.assertEqual(result["papers"][0]["matches"], [])
                    self.assertEqual(result["papers"][0]["support_boundary"]["retained_node_ids"], [])
                    self.assertIn("An unmapped claim", result["papers"][0]["view"]["paper"]["text"])

    def test_half_open_endpoint_excludes_next_passage(self):
        with tempfile.TemporaryDirectory() as temporary:
            root, manifest = fixture(Path(temporary))
            premise_start, premise_end = content_range("premise")
            result_start, result_end = content_range("result")
            before = self.query(root, manifest, [(premise_start, result_start)])
            self.assertEqual([m["anchor"] for m in before["papers"][0]["matches"]], ["premise"])
            self.assertEqual(before["papers"][0]["matches"][0]["byte_overlaps"], [{
                "requested_range": {"start_byte": premise_start, "end_byte": result_start},
                "overlap_span": {"start_byte": premise_start, "end_byte": premise_end},
            }])
            self.assertFalse(before["papers"][0]["matches"][0]["whole_passage_extends_beyond_selected_ranges"])
            self.assertEqual(self.query(root, manifest, [(result_end, len(CONTENT))])["match_count"], 0)

    def test_ranges_union_and_intersect_other_selector_families(self):
        with tempfile.TemporaryDirectory() as temporary:
            root, manifest = fixture(Path(temporary))
            ranges = [occurrence("α🙂"), occurrence("μ-result")]
            both = self.query(root, manifest, ranges)
            self.assertEqual([m["anchor"] for m in both["papers"][0]["matches"]], ["premise", "result"])
            self.assertEqual(self.query(root, manifest, ranges, passages=["result"])["match_count"], 1)
            self.assertEqual(self.query(root, manifest, [ranges[0]], passages=["result"])["match_count"], 0)
            self.assertEqual(self.query(root, manifest, [ranges[1]], node_ids=["prerequisite"])["match_count"], 0)
            indirect = self.query(root, manifest, [ranges[1]], node_ids=["prerequisite"], relation="prerequisites")
            self.assertEqual(indirect["match_count"], 1)
            witness = indirect["papers"][0]["matches"][0]["witnesses"][0]
            self.assertEqual([link["kind"] for link in witness["links"]], ["supports"])
            sections = {s["title"]: s["ref"] for s in project_paper(root, "short")["paper"]["sections"]}
            self.assertEqual(self.query(root, manifest, ranges, section_refs=[sections["Result"]])["match_count"], 1)
            self.assertEqual(self.query(root, manifest, [ranges[0]], section_refs=[sections["Result"]])["match_count"], 0)

    def test_adjacent_overlapping_and_whitespace_ranges_have_exact_union_coverage(self):
        with tempfile.TemporaryDirectory() as temporary:
            root, manifest = fixture(Path(temporary))
            start, end = content_range("result")
            split, _ = occurrence("Tail explanation.")
            body, _ = occurrence("The μ-result")
            for ranges in ([(start, split), (split, end)],
                           [(start, split + 4), (split, end)],
                           [(start, body), (body, end)]):
                with self.subTest(ranges=ranges):
                    result = self.query(root, manifest, ranges)
                    self.assertEqual(result["match_count"], 1)
                    match = result["papers"][0]["matches"][0]
                    self.assertEqual(len(match["byte_overlaps"]), 2)
                    self.assertFalse(match["whole_passage_extends_beyond_selected_ranges"])
            gap = self.query(root, manifest, [(start, split), (split + 4, end)])
            self.assertTrue(gap["papers"][0]["matches"][0]["whole_passage_extends_beyond_selected_ranges"])

    def test_one_range_selects_two_passages_with_separate_content_intersections(self):
        with tempfile.TemporaryDirectory() as temporary:
            root, manifest = fixture(Path(temporary))
            begin, _ = occurrence("α🙂")
            _, end = occurrence("μ-result")
            matches = self.query(root, manifest, [(begin, end)])["papers"][0]["matches"]
            self.assertEqual([m["anchor"] for m in matches], ["premise", "result"])
            self.assertEqual(matches[0]["byte_overlaps"][0]["overlap_span"],
                             {"start_byte": begin, "end_byte": content_range("premise")[1]})
            self.assertEqual(matches[1]["byte_overlaps"][0]["overlap_span"],
                             {"start_byte": content_range("result")[0], "end_byte": end})
            self.assertTrue(all(m["whole_passage_extends_beyond_selected_ranges"] for m in matches))

    def test_ranges_require_stage_and_manifest_and_reject_valid_successor(self):
        with tempfile.TemporaryDirectory() as temporary:
            root, manifest = fixture(Path(temporary))
            ranges = [occurrence("μ-result")]
            with self.assertRaises(ContractError):
                query_papers(root, byte_ranges=ranges, expected_manifest_sha256=manifest)
            for expected in (None, "", "0" * 64):
                with self.subTest(expected=expected), self.assertRaises(ContractError):
                    query_papers(root, stage="short", byte_ranges=ranges, expected_manifest_sha256=expected)
            rebind(root, content=b"New introduction.\n" + CONTENT)
            with self.assertRaises(ContractError):
                self.query(root, manifest, ranges)

    def test_malformed_or_non_boundary_offsets_fail_closed(self):
        with tempfile.TemporaryDirectory() as temporary:
            root, manifest = fixture(Path(temporary))
            alpha, _ = occurrence("α")
            emoji, emoji_end = occurrence("🙂")
            candidates = [
                [], "0:1", (0, 1), [None], [(0,)], [(0, 1, 2)],
                [(False, 1)], [(0, True)], [(0.0, 1)], [(0, "1")],
                [(-1, 1)], [(1, 1)], [(2, 1)], [(0, len(CONTENT) + 1)],
                [(alpha + 1, alpha + 2)], [(alpha, alpha + 1)],
                [(emoji + 1, emoji_end)], [(emoji, emoji_end - 1)],
                [(alpha, alpha + 2), [alpha, alpha + 2]],
            ]
            for ranges in candidates:
                with self.subTest(ranges=ranges), self.assertRaises(ContractError):
                    self.query(root, manifest, ranges)
            self.assertEqual(self.query(root, manifest, [(emoji, emoji_end)])["match_count"], 1)
            self.assertEqual(self.query(root, manifest, [(0, len(CONTENT))])["match_count"], 2)

    def test_directory_zip_cli_and_range_order_share_pinned_capture(self):
        with tempfile.TemporaryDirectory() as temporary:
            parent = Path(temporary)
            root, manifest = fixture(parent)
            archive = parent / "bundle.zip"
            bundle.export_bundle(root, archive)
            ranges = [occurrence("α🙂"), occurrence("μ-result")]
            with patch.object(consumer, "load_bundle", wraps=consumer.load_bundle) as load:
                expected = self.query(root, manifest, ranges)
            self.assertEqual(load.call_count, 1)
            self.assertEqual(expected["query"]["byte_ranges"], [list(r) for r in ranges])
            self.assertEqual(expected, self.query(archive, manifest, [list(ranges[1]), ranges[0]]))
            args = ["query-papers", str(archive), "--paper", "short", "--expect-manifest", manifest]
            for start, end in reversed(ranges):
                args.extend(["--byte-range", str(start), str(end)])
            output, errors = io.StringIO(), io.StringIO()
            with contextlib.redirect_stdout(output), contextlib.redirect_stderr(errors):
                status = main(args)
            self.assertEqual(status, 0, errors.getvalue())
            self.assertEqual(json.loads(output.getvalue()), expected)
            self.assertNotEqual(expected["cache_key"], self.query(root, manifest, [ranges[0]])["cache_key"])

    def test_cli_rejects_unpinned_or_bad_ranges_without_query_output(self):
        with tempfile.TemporaryDirectory() as temporary:
            root, manifest = fixture(Path(temporary))
            start, end = occurrence("μ-result")
            cases = [
                ["--paper", "short", "--byte-range", str(start), str(end)],
                ["--expect-manifest", manifest, "--byte-range", str(start), str(end)],
                ["--paper", "short", "--expect-manifest", manifest, "--byte-range", str(end), str(start)],
                ["--paper", "short", "--expect-manifest", "0" * 64, "--byte-range", str(start), str(end)],
            ]
            for flags in cases:
                with self.subTest(flags=flags):
                    output, errors = io.StringIO(), io.StringIO()
                    with contextlib.redirect_stdout(output), contextlib.redirect_stderr(errors):
                        status = main(["query-papers", str(root)] + flags)
                    self.assertEqual(status, 1)
                    self.assertEqual(output.getvalue(), "")
                    self.assertTrue(errors.getvalue())


if __name__ == "__main__":
    unittest.main()
