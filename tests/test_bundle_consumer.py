"""Consumer-facing ZIP acceptance using synthetic, explicitly unverified evidence."""
from __future__ import annotations

import copy
import json
import os
from pathlib import Path
import posixpath
import re
import shutil
import stat
import struct
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch
from urllib.parse import unquote, urlsplit
import warnings
import zipfile

from lean_exposition import bundle
from lean_exposition.consumer import inspect_bundle, inspect_graph
from lean_exposition.contracts import ContractError, digest, encoded
from test_adversarial import synthetic_artifact, synthetic_graph


EXPECTED_MEMBERS = {"manifest.json", "graph.json"} | {
    f"papers/{stage}.{extension}"
    for stage in ("long", "short", "expository")
    for extension in ("md", "json")
}
ROOT = Path(__file__).resolve().parents[1]


def graph_with_recorded_failures():
    """Synthetic records for selection tests; no tool success is asserted."""
    graph = synthetic_graph()
    for name in ("outside", "platform-only"):
        graph["nodes"].append({
            "id": name, "kind": "claim", "label": name, "status": "open",
            "assumption_ids": [], "evidence_ids": [], "citation_ids": [],
        })
    graph["edges"].append({
        "from": "goal", "to": "platform-only", "kind": "platform_decomposition",
        "evidence_ids": ["platform-observation"],
    })
    for index, identity in enumerate(("goal", "platform-only"), 1):
        node = next(row for row in graph["nodes"] if row["id"] == identity)
        node.update({"source_id": "public", "platform": {
            "provider": "prove2me", "id": f"00000000-0000-0000-0000-{index:012d}",
            "entity": "theorem", "status": "Unproved", "visibility": "public",
        }})
    graph["sources"][0].update({
        "path": "external/synthetic.lean", "sha256": digest(b"-- Uncompiled synthetic source.\n"),
    })
    for identity, kind, status, subject in (
        ("build-failure", "lean_build", "failed", "goal"),
        ("comparator-unavailable", "comparator", "unavailable", "goal"),
        ("extraction-pending", "extraction", "not_run", "prerequisite"),
        ("outside-review", "semantic_review", "failed", "outside"),
        ("platform-pending", "platform_observation", "not_run", "platform-only"),
    ):
        graph["evidence"].append({
            "id": identity, "kind": kind, "status": status, "command": [],
            "tool": "synthetic fixture", "source_ids": ["public"], "subject_ids": [subject],
            "details": "Synthetic regression record only; no tool was executed.",
        })
    graph["evidence"].append({
        "id": "platform-observation", "kind": "platform_observation", "status": "passed",
        "command": [], "tool": "synthetic fixture", "source_ids": ["public"],
        "subject_ids": ["goal", "platform-only"],
        "details": "Synthetic platform observation of Unproved labels; not formal evidence.",
    })
    graph["evidence"][0].update({
        "receipt_path": "external/missing-build-receipt.json",
        "receipt_sha256": digest(b"Synthetic receipt placeholder; never a passed check.\n"),
        "receipt": {"status": "failed", "diagnostic": {"synthetic": True}},
    })
    graph["notes"] = ["No formal check ran; missing dependencies do not establish independence."]
    return graph


class BundleConsumerTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="lean-exposition-consumer-")
        self.addCleanup(temporary.cleanup)
        self.tmp = Path(temporary.name)
        self.root = self.tmp / "bundle"
        self.graph = synthetic_graph()
        bundle.scaffold(self.graph, self.root)
        self.payload = {name: (self.root / name).read_bytes() for name in EXPECTED_MEMBERS}
        self.serial = 0

    def archive(self, payload=None, *, entries=None, modes=None, compression=zipfile.ZIP_STORED):
        """Build independent ZIP inputs, including files the exporter never emits."""
        self.serial += 1
        path = self.tmp / f"input-{self.serial}.zip"
        if entries is None:
            entries = list((self.payload if payload is None else payload).items())
        with zipfile.ZipFile(path, "x") as output, warnings.catch_warnings():
            warnings.simplefilter("ignore", UserWarning)  # Deliberately duplicated names.
            for name, content in entries:
                info = zipfile.ZipInfo(name)
                info.create_system = 3
                info.external_attr = (modes or {}).get(name, stat.S_IFREG | 0o644) << 16
                info.compress_type = compression
                output.writestr(info, content)
        return path

    def rebind(self, payload, name, content):
        """Update the outer file hash, leaving inner semantic bindings to the checker."""
        payload[name] = content
        if name != "manifest.json":
            manifest = json.loads(payload["manifest.json"])
            for row in manifest["files"]:
                if row["path"] == name:
                    row["sha256"] = digest(content)
            payload["manifest.json"] = encoded(manifest)

    def assert_rejected(self, path):
        for reader in (bundle.load_bundle, bundle.check_bundle):
            with self.subTest(reader=reader.__name__), self.assertRaises(ContractError):
                reader(path)

    def test_export_roundtrip_exposes_validated_exact_bytes_without_extraction(self):
        destination = self.tmp / "export.zip"
        receipt = bundle.export_bundle(self.root, destination)
        directory_summary = bundle.check_bundle(self.root)
        shutil.rmtree(self.root)
        with patch.object(zipfile.ZipFile, "extract", side_effect=AssertionError("must not extract")), \
             patch.object(zipfile.ZipFile, "extractall", side_effect=AssertionError("must not extract")):
            captured = bundle.load_bundle(destination)
            archive_summary = bundle.check_bundle(destination)
        self.assertEqual(captured, self.payload)
        self.assertEqual(set(captured), EXPECTED_MEMBERS)
        self.assertEqual(archive_summary, directory_summary)
        self.assertEqual(archive_summary["paper_states"], ["scaffold"] * 3)
        self.assertEqual(receipt["sha256"], digest(destination.read_bytes()))
        self.assertEqual(receipt["files"], 8)
        self.assertEqual(set(self.tmp.iterdir()), {destination})
        manifest = json.loads(captured["manifest.json"])
        for row in manifest["files"]:
            self.assertEqual(row["sha256"], digest(captured[row["path"]]))
        for stage in ("long", "short", "expository"):
            mapping = json.loads(captured[f"papers/{stage}.json"])
            self.assertEqual(mapping["graph_sha256"], digest(captured["graph.json"]))
            self.assertEqual(mapping["content_sha256"], digest(captured[f"papers/{stage}.md"]))
            self.assertEqual(mapping["review_state"], "not_reviewed")

    def test_directory_load_returns_the_same_fixed_payload(self):
        (self.root / "not-exported.txt").write_text("Unlisted notes are not a bundle member.\n")
        self.assertEqual(bundle.load_bundle(self.root), self.payload)
        destination = self.tmp / "export.zip"
        bundle.export_bundle(self.root, destination)
        with zipfile.ZipFile(destination) as archive:
            self.assertEqual(set(archive.namelist()), EXPECTED_MEMBERS)

    def test_repeated_exports_are_identical_despite_source_metadata(self):
        first, second = self.tmp / "first.zip", self.tmp / "second.zip"
        first_receipt = bundle.export_bundle(self.root, first)
        for name in EXPECTED_MEMBERS:
            os.utime(self.root / name, (1_000_000_000, 1_000_000_000))
            (self.root / name).chmod(0o600)
        second_receipt = bundle.export_bundle(self.root, second)
        self.assertEqual(first.read_bytes(), second.read_bytes())
        self.assertEqual(first_receipt, second_receipt)
        with zipfile.ZipFile(first) as archive:
            self.assertEqual(archive.namelist(), sorted(EXPECTED_MEMBERS))
            dates = {member.date_time for member in archive.infolist()}
            self.assertEqual(len(dates), 1)
            for member in archive.infolist():
                self.assertEqual(member.compress_type, zipfile.ZIP_STORED)
                self.assertEqual(member.create_system, 3)
                self.assertEqual(member.external_attr >> 16, stat.S_IFREG | 0o644)

    def test_deflated_previous_format_exports_remain_readable(self):
        archive = self.archive(compression=zipfile.ZIP_DEFLATED)
        self.assertEqual(bundle.load_bundle(archive), self.payload)

    def test_unsupported_contract_versions_are_rejected(self):
        for name, field in (
            ("manifest.json", "schema_version"),
            ("manifest.json", "bundle_version"),
            ("graph.json", "schema_version"),
            ("papers/long.json", "schema_version"),
        ):
            with self.subTest(name=name, field=field):
                payload = self.payload.copy()
                record = json.loads(payload[name])
                record[field] = "99.0.0"
                self.rebind(payload, name, encoded(record))
                self.assert_rejected(self.archive(payload))

    def test_modified_payload_fails_its_manifest_hash(self):
        for name in ("graph.json", "papers/short.md", "papers/expository.json"):
            with self.subTest(name=name):
                payload = self.payload.copy()
                payload[name] += b"\n"
                self.assert_rejected(self.archive(payload))

    def test_rehashing_a_paper_does_not_bypass_its_mapping(self):
        payload = self.payload.copy()
        self.rebind(payload, "papers/short.md", payload["papers/short.md"] + b"Unbound extra sentence.\n")
        self.assert_rejected(self.archive(payload))

    def test_missing_mapping_fields_report_contract_errors(self):
        for field in ("stage", "path", "state"):
            with self.subTest(field=field):
                payload = self.payload.copy()
                mapping = json.loads(payload["papers/long.json"])
                del mapping[field]
                self.rebind(payload, "papers/long.json", encoded(mapping))
                self.assert_rejected(self.archive(payload))

    def test_malformed_json_reports_contract_errors(self):
        invalid_json = (
            b"not JSON\n", b"\xff", b"[]", b"null",
            b'{"bundle_version":"0.1.0","bundle_version":"99.0.0"}',
            b'{"value":NaN}',
        )
        for content in invalid_json:
            with self.subTest(content=content):
                payload = self.payload.copy()
                payload["manifest.json"] = content
                self.assert_rejected(self.archive(payload))

    def test_member_set_rejects_missing_extra_and_duplicate_entries(self):
        rows = list(self.payload.items())
        for entries in (
            rows[:-1], rows + [("extra.txt", b"extra")],
            rows + [("graph.json", self.payload["graph.json"])],
        ):
            with self.subTest(names=[name for name, _ in entries]):
                self.assert_rejected(self.archive(entries=entries))

    def test_unsafe_member_names_are_rejected_without_writing_files(self):
        for name in ("../escape.json", "/absolute.json", "papers/../graph.json", "./graph.json",
                     "papers//long.md", "papers\\long.md", "C:/graph.json", "papers/", "graph.json\n"):
            with self.subTest(name=name):
                payload = self.payload.copy()
                payload[name] = payload.pop("graph.json")
                archive = self.archive(payload)
                before = set(self.tmp.iterdir())
                self.assert_rejected(archive)
                self.assertEqual(set(self.tmp.iterdir()), before)

    def test_symlink_and_nonregular_members_are_rejected(self):
        for mode in (stat.S_IFLNK | 0o777, stat.S_IFIFO | 0o644, stat.S_IFDIR | 0o755):
            with self.subTest(mode=oct(mode)):
                self.assert_rejected(self.archive(modes={"graph.json": mode}))

    def test_directory_symlink_artifact_is_rejected(self):
        real = self.tmp / "actual-graph.json"
        (self.root / "graph.json").rename(real)
        (self.root / "graph.json").symlink_to(real)
        self.assert_rejected(self.root)

    def test_corrupt_zip_and_crc_fail_as_contract_errors(self):
        valid = self.archive()
        raw = valid.read_bytes()
        invalid = self.tmp / "invalid.zip"
        for content in (b"not a ZIP archive\n", raw[:20], raw[:-22]):
            with self.subTest(length=len(content)):
                invalid.write_bytes(content)
                self.assert_rejected(invalid)
        with zipfile.ZipFile(valid) as archive:
            member = archive.getinfo("graph.json")
        # Change a stored byte without changing either recorded CRC.
        changed = bytearray(raw)
        filename_length, extra_length = struct.unpack_from("<HH", raw, member.header_offset + 26)
        offset = member.header_offset + 30 + filename_length + extra_length
        changed[offset] ^= 1
        invalid.write_bytes(changed)
        self.assert_rejected(invalid)

    def test_invalid_deflate_block_reports_contract_error(self):
        archive_path = self.archive(compression=zipfile.ZIP_DEFLATED)
        raw = bytearray(archive_path.read_bytes())
        with zipfile.ZipFile(archive_path) as archive:
            member = archive.getinfo("graph.json")
        filename_length, extra_length = struct.unpack_from("<HH", raw, member.header_offset + 26)
        offset = member.header_offset + 30 + filename_length + extra_length
        raw[offset] = 0xff  # Reserved DEFLATE block type, independent of payload CRC.
        archive_path.write_bytes(raw)
        self.assert_rejected(archive_path)
        result = self.standalone(archive_path)
        self.assertEqual(result.returncode, 1)
        self.assertEqual(result.stdout, "")
        self.assertIsInstance(json.loads(result.stderr)["error"], str)

    def test_unsupported_compression_and_encrypted_members_are_rejected(self):
        self.assert_rejected(self.archive(compression=zipfile.ZIP_BZIP2))
        archive_path = self.archive()
        raw = bytearray(archive_path.read_bytes())
        central = raw.index(b"PK\x01\x02")
        for offset in (6, central + 8):
            flags = struct.unpack_from("<H", raw, offset)[0]
            struct.pack_into("<H", raw, offset, flags | 1)
        archive_path.write_bytes(raw)
        self.assert_rejected(archive_path)

    def test_archive_member_and_total_byte_limits_are_enforced(self):
        archive = self.archive()
        limits = (
            ("MAX_ARCHIVE_BYTES", archive.stat().st_size - 1),
            ("MAX_MEMBER_BYTES", max(map(len, self.payload.values())) - 1),
            ("MAX_BUNDLE_BYTES", sum(map(len, self.payload.values())) - 1),
        )
        for constant, threshold in limits:
            with self.subTest(limit=constant), patch.object(bundle, constant, threshold):
                self.assert_rejected(archive)

    def test_assemble_preserves_supplied_graph_and_paper_bytes(self):
        # Deliberately choose valid JSON serialization different from scaffold's.
        graph_bytes = (json.dumps(self.graph, separators=(",", ":")) + "\n").encode()
        (self.root / "graph.json").write_bytes(graph_bytes)
        pairs = {}
        expected = {"graph.json": graph_bytes}
        for stage in ("long", "short", "expository"):
            document = self.root / f"papers/{stage}.md"
            mapping_path = self.root / f"papers/{stage}.json"
            mapping = json.loads(mapping_path.read_bytes())
            mapping["graph_sha256"] = digest(graph_bytes)
            mapping_bytes = (json.dumps(mapping, separators=(",", ":")) + "\n").encode()
            mapping_path.write_bytes(mapping_bytes)
            pairs[stage] = (document, mapping_path)
            expected[f"papers/{stage}.md"] = document.read_bytes()
            expected[f"papers/{stage}.json"] = mapping_bytes
        destination = self.tmp / "assembled"
        manifest = bundle.assemble_bundle(self.root / "graph.json", pairs, destination)
        captured = bundle.load_bundle(destination)
        self.assertEqual({name: captured[name] for name in expected}, expected)
        self.assertEqual(json.loads(captured["manifest.json"]), manifest)
        self.assertEqual(manifest["status"], "scaffold")

    def test_assemble_rejects_stale_mapping_without_publishing_output(self):
        pairs = {
            stage: (self.root / f"papers/{stage}.md", self.root / f"papers/{stage}.json")
            for stage in ("long", "short", "expository")
        }
        document = self.root / "papers/short.md"
        document.write_bytes(document.read_bytes() + b"This sentence has no updated mapping.\n")
        destination = self.tmp / "assembled"
        with self.assertRaises(ContractError):
            bundle.assemble_bundle(self.root / "graph.json", pairs, destination)
        self.assertFalse(destination.exists())

    def test_assemble_authored_pairs_preserves_draft_and_review_boundaries(self):
        pairs = {}
        for stage in bundle.STAGES:
            mapping, content = synthetic_artifact(self.graph)
            mapping.update({"stage": stage, "path": f"papers/{stage}.md"})
            document = self.tmp / f"{stage}.md"
            record = self.tmp / f"{stage}.json"
            document.write_bytes(content)
            record.write_bytes(encoded(mapping))
            pairs[stage] = (document, record)
        destination = self.tmp / "authored"
        manifest = bundle.assemble_bundle(self.root / "graph.json", pairs, destination)
        self.assertEqual(manifest["status"], "authored")
        report = inspect_bundle(destination)
        self.assertEqual([paper["state"] for paper in report["papers"]], ["draft"] * 3)
        self.assertEqual([paper["review_state"] for paper in report["papers"]], ["not_reviewed"] * 3)
        self.assertFalse(report["semantic_certification"])
        for stage in bundle.STAGES:
            self.assertEqual((destination / f"papers/{stage}.md").read_bytes(), pairs[stage][0].read_bytes())
            self.assertEqual((destination / f"papers/{stage}.json").read_bytes(), pairs[stage][1].read_bytes())

    def test_inspection_retains_evidence_outside_both_closures(self):
        graph = graph_with_recorded_failures()
        report = inspect_graph(graph)
        self.assertFalse(report["semantic_certification"])
        self.assertEqual(report["notes"], graph["notes"])
        self.assertEqual(report["assumptions"], ["assumption"])
        self.assertEqual(report["unresolved"], ["goal", "prerequisite"])
        self.assertEqual(report["argument_closure"], ["assumption", "goal", "prerequisite"])
        self.assertEqual(report["platform_closure"], ["goal", "platform-only"])
        evidence = {row["id"]: row for row in report["evidence"]}
        self.assertEqual(set(evidence), {row["id"] for row in graph["evidence"]})
        for original in graph["evidence"]:
            self.assertEqual({key: evidence[original["id"]][key] for key in original}, original)
        self.assertFalse(evidence["outside-review"]["relevant_to_argument"])
        self.assertFalse(evidence["outside-review"]["relevant_to_platform"])
        self.assertFalse(evidence["platform-pending"]["relevant_to_argument"])
        self.assertTrue(evidence["platform-pending"]["relevant_to_platform"])
        self.assertEqual(report["failed_evidence"], ["build-failure", "outside-review"])

    def test_inspection_selection_and_returned_records_do_not_mutate_input(self):
        graph = graph_with_recorded_failures()
        before = copy.deepcopy(graph)
        report = inspect_graph(graph, goals=["outside"])
        self.assertEqual(report["selected_goals"], ["outside"])
        self.assertEqual(report["argument_closure"], ["outside"])
        self.assertEqual(report["unresolved"], ["outside"])
        evidence = {row["id"]: row for row in report["evidence"]}
        self.assertTrue(evidence["outside-review"]["relevant_to_argument"])
        self.assertFalse(evidence["build-failure"]["relevant_to_argument"])
        self.assertEqual(len(report["nodes"]), len(graph["nodes"]))
        self.assertEqual(len(report["evidence"]), len(graph["evidence"]))
        report["selected_goals"].append("goal")
        report["notes"].append("A report-local annotation must not rewrite the source graph.")
        evidence["build-failure"]["receipt"]["diagnostic"]["synthetic"] = False
        self.assertEqual(graph, before)
        with self.assertRaises(ContractError):
            inspect_graph(graph, goals=["missing"])

    def test_bundle_inspection_exposes_mapping_and_external_resource_boundaries(self):
        source = self.tmp / "evidence-bundle"
        graph = graph_with_recorded_failures()
        bundle.scaffold(graph, source)
        archive = self.tmp / "evidence.zip"
        bundle.export_bundle(source, archive)
        captured = bundle.load_bundle(archive)
        shutil.rmtree(source)
        report = inspect_bundle(archive)
        self.assertTrue(report["contract_valid"])
        self.assertFalse(report["semantic_certification"])
        self.assertEqual(report["status"], "scaffold")
        self.assertEqual(report["publication"], "local_only")
        self.assertEqual(report["manifest_sha256"], digest(captured["manifest.json"]))
        self.assertEqual(report["graph"], inspect_graph(graph))
        for row in report["papers"]:
            mapping = json.loads(captured[row["mapping_path"]])
            self.assertEqual({key: row[key] for key in mapping}, mapping)
        self.assertEqual(report["external_resources"]["sources"], [
            {**graph["sources"][0], "included": False},
        ])
        self.assertEqual(report["external_resources"]["receipts"], [{
            "evidence_id": "build-failure", "path": graph["evidence"][0]["receipt_path"],
            "sha256": graph["evidence"][0]["receipt_sha256"], "included": False,
        }])

    def standalone(self, archive):
        script = self.tmp / "read_bundle.py"
        shutil.copyfile(ROOT / "examples/consumer/read_bundle.py", script)
        return subprocess.run(
            [sys.executable, "-I", "-S", str(script), str(archive)], cwd=self.tmp,
            capture_output=True, text=True, timeout=15, check=False,
        )

    def test_standalone_consumer_runs_without_installed_package_or_site_dependencies(self):
        source = self.tmp / "evidence-bundle"
        graph = graph_with_recorded_failures()
        bundle.scaffold(graph, source)
        archive = self.tmp / "evidence.zip"
        bundle.export_bundle(source, archive)
        shutil.rmtree(source)
        result = self.standalone(archive)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stderr, "")
        report = json.loads(result.stdout)
        self.assertTrue(report["transport_integrity"])
        self.assertFalse(report["full_contract_validation"])
        self.assertFalse(report["semantic_certification"])
        self.assertEqual(report["archive_sha256"], digest(archive.read_bytes()))
        self.assertEqual(report["selected_goals"], [{"id": "goal", "label": "goal"}])
        self.assertEqual(report["scope"], graph["scope"])
        self.assertEqual(report["notes"], graph["notes"])
        expected = {row["id"]: (row["kind"], row["status"], row["details"]) for row in graph["evidence"]}
        actual = {row["id"]: (row["kind"], row["status"], row["details"]) for row in report["evidence"]}
        self.assertEqual(actual, expected)
        self.assertEqual([row["state"] for row in report["papers"]], ["scaffold"] * 3)
        self.assertEqual([row["review_state"] for row in report["papers"]], ["not_reviewed"] * 3)

    def test_standalone_consumer_rejects_unsupported_tampered_and_malformed_inputs(self):
        unsupported = self.payload.copy()
        manifest = json.loads(unsupported["manifest.json"])
        manifest["bundle_version"] = "99.0.0"
        unsupported["manifest.json"] = encoded(manifest)
        tampered = self.payload.copy()
        tampered["papers/short.md"] += b"Unbound bytes.\n"
        invalid_zip = self.tmp / "invalid.zip"
        invalid_zip.write_bytes(b"not a ZIP")
        for archive in (self.archive(unsupported), self.archive(tampered), invalid_zip):
            with self.subTest(archive=archive.name):
                result = self.standalone(archive)
                self.assertEqual(result.returncode, 1)
                self.assertEqual(result.stdout, "")
                self.assertIsInstance(json.loads(result.stderr)["error"], str)
                self.assertNotIn("Traceback", result.stderr)


class QaoaPaperConsumerTests(unittest.TestCase):
    """Replay the authored public example, without claiming a new formal check."""

    def assert_paper_links_resolve(self, payload):
        # Match the authored link syntax checked by scripts/check_links.py.
        # In particular, mathematical ](...) expressions are not Markdown links.
        for name, content in payload.items():
            if not name.endswith(".md"):
                continue
            text = content.decode("utf-8")
            text = re.sub(r"(?ms)^(`{3,}|~{3,}).*?^\1[^\n]*$", "", text)
            text = re.sub(r"(?s)\$\$.*?\$\$|\\\[.*?\\\]|\\\(.*?\\\)", "", text)
            text = re.sub(r"`[^`\n]+`|(?<!\\)\$(?:\\.|[^$\n])*\$", "", text)
            links = re.findall(r"(?<!!)\[[^\]]+\]\(([^)]+)\)", text)
            links += re.findall(r"(?m)^\[[^\]]+\]:\s*(\S+)", text)
            for link in links:
                url = urlsplit(link.strip("<>"))
                if url.scheme or url.netloc:
                    continue
                destination = posixpath.normpath(posixpath.join(
                    posixpath.dirname(name), unquote(url.path)
                )) if url.path else name
                self.assertIn(destination, payload, f"{name}: missing bundled destination {link}")
                if url.fragment:
                    pattern = r"(?:id|name)=[\"']" + re.escape(unquote(url.fragment)) + r"[\"']"
                    self.assertRegex(payload[destination].decode("utf-8"), pattern,
                                     f"{name}: missing explicit bundled anchor {link}")

    def test_actual_papers_assemble_export_and_read_without_checkout_dependencies(self):
        graph = ROOT / "examples/qaoa-sk/evidence-graph.json"
        papers = ROOT / "papers/qaoa-sk"
        pairs = {
            "long": (papers / "long/reasoning-record.md", papers / "long/reasoning-record.json"),
            "short": (papers / "short/paper.md", papers / "short/correspondence.json"),
            "expository": (papers / "expository/main.md", papers / "expository/correspondence.json"),
        }
        original = {"graph.json": graph.read_bytes()}
        for stage, pair in pairs.items():
            original[f"papers/{stage}.md"] = pair[0].read_bytes()
            original[f"papers/{stage}.json"] = pair[1].read_bytes()
        with tempfile.TemporaryDirectory(prefix="qaoa-paper-consumer-") as temporary:
            root = Path(temporary)
            manifest = bundle.assemble_bundle(graph, pairs, root / "bundle")
            self.assertEqual(manifest["status"], "authored")
            archive = root / "qaoa-sk.zip"
            receipt = bundle.export_bundle(root / "bundle", archive)
            shutil.rmtree(root / "bundle")
            payload = bundle.load_bundle(archive)
            self.assertEqual({name: payload[name] for name in original}, original)
            self.assert_paper_links_resolve(payload)
            reader = root / "read_bundle.py"
            shutil.copyfile(ROOT / "examples/consumer/read_bundle.py", reader)
            process = subprocess.run(
                [sys.executable, "-I", "-S", str(reader), str(archive)],
                cwd=root, capture_output=True, text=True, timeout=15, check=False,
            )
            self.assertEqual(process.returncode, 0, process.stderr)
            report = json.loads(process.stdout)
            self.assertEqual(report["archive_sha256"], receipt["sha256"])
            self.assertFalse(report["semantic_certification"])
            self.assertFalse(report["full_contract_validation"])
            source_graph = json.loads(original["graph.json"])
            self.assertEqual(report["notes"], source_graph["notes"])
            self.assertEqual(
                {row["id"]: (row["kind"], row["status"], row["details"]) for row in report["evidence"]},
                {row["id"]: (row["kind"], row["status"], row["details"]) for row in source_graph["evidence"]},
            )
            for paper in report["papers"]:
                mapping = json.loads(original[f"papers/{paper['stage']}.json"])
                self.assertNotEqual(mapping["state"], "scaffold")
                for key in ("state", "review_state", "review_notes"):
                    self.assertEqual(paper[key], mapping[key])

    def test_export_link_check_detects_old_layout_without_misreading_mathematics(self):
        payload = {
            "papers/long.md": b'<a id="gap-elimination"></a>\n',
            "papers/short.md": b"$[a](t,X_t)$\n[Proof](long.md#gap-elimination)\n",
        }
        self.assert_paper_links_resolve(payload)
        payload["papers/short.md"] = b"[Proof](../long/reasoning-record.md#gap-elimination)\n"
        with self.assertRaisesRegex(AssertionError, "missing bundled destination"):
            self.assert_paper_links_resolve(payload)


if __name__ == "__main__":
    unittest.main()
