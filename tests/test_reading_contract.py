"""Authored reading metadata stays local to the captured paper mappings."""
from __future__ import annotations

import copy
import tempfile
import unittest
from pathlib import Path

from lean_exposition import bundle
from lean_exposition.contracts import ContractError, decode_json, digest, encoded, validate_artifact, write_json
from test_adversarial import synthetic_artifact, synthetic_graph


def reading_artifact(graph, stage="long"):
    artifact, content = synthetic_artifact(graph)
    artifact.update(schema_version="1.2", stage=stage, path=f"papers/{stage}.md")
    detail = "\nAn authored derivation with more detail than the later statement.\n"
    content = ("<!-- passage:detail -->" + detail + "<!-- /passage:detail -->\n").encode() + content
    artifact["content_sha256"] = digest(content)
    artifact["passages"].insert(0, {**copy.deepcopy(artifact["passages"][0]),
                                    "anchor": "detail", "text_sha256": digest(detail.encode())})
    return artifact, content


def treatment(**changes):
    return {"claim_id": "goal", "kinds": ["derivation", "explanation"],
            "rationale": "Explains the argument and its recorded assumptions.", **changes}


def reading_link(artifact, **changes):
    passages = {row["anchor"]: row for row in artifact["passages"]}
    return {"from_anchor": "detail", "to_stage": artifact["stage"], "to_anchor": "result",
            "from_text_sha256": passages["detail"]["text_sha256"],
            "to_text_sha256": passages["result"]["text_sha256"],
            "kind": "expands", "rationale": "The detailed argument expands the short statement.",
            **changes}


class ReadingContractTests(unittest.TestCase):
    def setUp(self):
        self.graph = synthetic_graph()
        self.artifact, self.content = reading_artifact(self.graph)

    def validate(self, artifact=None, content=None):
        validate_artifact(self.artifact if artifact is None else artifact, self.graph,
                          digest(encoded(self.graph)), self.content if content is None else content)

    def test_optional_metadata_preserves_all_versions_without_defaults(self):
        for version in ("1.0", "1.1", "1.2"):
            with self.subTest(version=version):
                artifact = copy.deepcopy(self.artifact)
                artifact["schema_version"] = version
                before = copy.deepcopy(artifact)
                self.validate(artifact)
                self.assertEqual(artifact, before)
                self.assertNotIn("reading_links", artifact)
                self.assertNotIn("treatments", artifact["passages"][0])

    def test_new_version_keeps_independent_paper_goal_selection(self):
        self.artifact["selected_goal_ids"] = ["prerequisite"]
        self.artifact["claim_ids"].append("prerequisite")
        self.artifact["passages"][0]["claim_ids"].append("prerequisite")
        for version in ("1.1", "1.2"):
            self.artifact["schema_version"] = version
            self.validate()
        self.artifact["schema_version"] = "1.0"
        with self.assertRaisesRegex(ContractError, "changed selected goals"):
            self.validate()

    def test_all_treatments_and_forward_local_links_remain_authored_data(self):
        self.artifact["passages"][0]["treatments"] = [treatment(kinds=[
            "statement", "derivation", "explanation", "illustration", "reference", "application"])]
        self.artifact["reading_links"] = [reading_link(self.artifact, kind=kind)
                                          for kind in ("expands", "illustrates", "answers")]
        before = copy.deepcopy((self.artifact, self.graph))
        self.validate()
        self.assertEqual((self.artifact, self.graph), before)
        self.assertEqual(self.artifact["review_state"], "not_reviewed")
        self.assertEqual(self.graph["nodes"][0]["status"], "conditional")

    def test_treatment_requires_this_passages_claim_even_if_graph_claim_exists(self):
        for claim in ("prerequisite", "missing"):
            with self.subTest(claim=claim):
                self.artifact["passages"][0]["treatments"] = [treatment(claim_id=claim)]
                with self.assertRaisesRegex(ContractError, "passage treatment claim"):
                    self.validate()

    def test_duplicate_treatment_claim_rejected_even_with_different_kinds(self):
        self.artifact["passages"][0]["treatments"] = [
            treatment(), treatment(kinds=["reference"], rationale="Different treatment text.")]
        with self.assertRaisesRegex(ContractError, "duplicate treatment claim"):
            self.validate()

    def test_treatment_shape_is_strict(self):
        cases = [treatment(kinds=[]), treatment(kinds=["proof"]),
                 treatment(kinds=["statement", "statement"]), treatment(kinds="statement"),
                 treatment(rationale=""), treatment(status="accepted")]
        for field in ("claim_id", "kinds", "rationale"):
            row = treatment()
            del row[field]
            cases.append(row)
        for row in cases:
            with self.subTest(row=row):
                self.artifact["passages"][0]["treatments"] = [row]
                with self.assertRaises(ContractError):
                    self.validate()

    def test_older_versions_reject_present_metadata_including_empty_lists(self):
        for version in ("1.0", "1.1"):
            for field, value in (("treatments", []), ("treatments", [treatment()]),
                                 ("reading_links", []), ("reading_links", [reading_link(self.artifact)])):
                with self.subTest(version=version, field=field, empty=not value):
                    artifact = copy.deepcopy(self.artifact)
                    artifact["schema_version"] = version
                    owner = artifact["passages"][0] if field == "treatments" else artifact
                    owner[field] = value
                    with self.assertRaises(ContractError):
                        self.validate(artifact)

    def test_reading_link_references_and_shape_are_strict(self):
        changes = [{"from_anchor": "absent"}, {"to_anchor": "absent"}, {"to_stage": "unknown"},
                   {"kind": "supports"}, {"kind": "derivation"}, {"rationale": ""},
                   {"semantic_certification": True}, {"from_anchor": ""}, {"to_anchor": "../result"},
                   {"from_text_sha256": "bad"}, {"to_text_sha256": "F" * 64}]
        cases = [reading_link(self.artifact, **change) for change in changes]
        for field in ("from_anchor", "to_stage", "to_anchor", "from_text_sha256", "to_text_sha256", "kind", "rationale"):
            row = reading_link(self.artifact)
            del row[field]
            cases.append(row)
        for row in cases:
            with self.subTest(row=row):
                self.artifact["reading_links"] = [row]
                with self.assertRaises(ContractError):
                    self.validate()

    def test_duplicate_reading_tuple_rejected_despite_different_rationale(self):
        self.artifact["reading_links"] = [reading_link(self.artifact),
                                          reading_link(self.artifact, rationale="Another reason.")]
        with self.assertRaisesRegex(ContractError, "duplicate reading link"):
            self.validate()

    def test_changed_passage_text_requires_deliberate_link_rebinding(self):
        for anchor, binding in (("detail", "from_text_sha256"), ("result", "to_text_sha256")):
            with self.subTest(anchor=anchor):
                artifact = copy.deepcopy(self.artifact)
                artifact["reading_links"] = [reading_link(artifact)]
                opening, closing = f"<!-- passage:{anchor} -->".encode(), f"<!-- /passage:{anchor} -->".encode()
                start = self.content.index(opening) + len(opening)
                end = self.content.index(closing)
                changed = self.content[start:end] + b"Revised explanation.\n"
                content = self.content[:start] + changed + self.content[end:]
                artifact["content_sha256"] = digest(content)
                next(p for p in artifact["passages"] if p["anchor"] == anchor)["text_sha256"] = digest(changed)
                with self.assertRaisesRegex(ContractError, "passage hash is stale"):
                    self.validate(artifact, content)
                artifact["reading_links"][0][binding] = digest(changed)
                self.validate(artifact, content)

    def test_reading_metadata_cannot_bypass_mathematical_or_review_requirements(self):
        self.artifact["passages"][0]["treatments"] = [treatment(kinds=["derivation"])]
        self.artifact["reading_links"] = [reading_link(self.artifact, kind="answers")]
        for change in ("formal_result", "assumption", "review"):
            with self.subTest(change=change):
                artifact = copy.deepcopy(self.artifact)
                if change == "formal_result":
                    artifact["passages"][0]["evidence_class"] = "formal_result"
                elif change == "assumption":
                    artifact["passages"][0]["assumption_ids"] = []
                else:
                    artifact["state"] = "reviewed"
                with self.assertRaises(ContractError):
                    self.validate(artifact)

    def assemble(self, parent, **link_changes):
        graph_path = parent / "graph.json"
        write_json(graph_path, self.graph)
        pairs = {}
        for stage, version in zip(bundle.STAGES, ("1.2", "1.1", "1.0")):
            artifact, content = reading_artifact(self.graph, stage)
            artifact["schema_version"] = version
            if stage == "long":
                artifact["passages"][0]["treatments"] = [treatment()]
                artifact["reading_links"] = [reading_link(artifact, to_stage="expository", **link_changes)]
            paper, mapping = parent / f"{stage}.md", parent / f"{stage}.json"
            paper.write_bytes(content)
            write_json(mapping, artifact)
            pairs[stage] = (paper, mapping)
        output = parent / "bundle"
        return output, bundle.assemble_bundle(graph_path, pairs, output)

    def test_cross_stage_forward_target_resolves_in_mixed_version_directory_and_zip(self):
        with tempfile.TemporaryDirectory() as temporary:
            parent = Path(temporary)
            output, manifest = self.assemble(parent)
            self.assertEqual(manifest["schema_version"], "1.0")
            self.assertEqual(manifest["bundle_version"], "0.1.0")
            capture = bundle.BundleCapture(output)
            self.assertEqual(set(bundle.load_bundle(capture)), set(bundle.BUNDLE_FILES))
            self.assertEqual(len(capture.files), 8)
            self.assertFalse(bundle.check_bundle(capture)["graph"]["semantic_certification"])
            archive = parent / "bundle.zip"
            bundle.export_bundle(capture, archive)
            self.assertEqual(bundle.load_bundle(archive), bundle.load_bundle(capture))

    def test_missing_or_stale_cross_stage_target_rejected_before_output_creation(self):
        for changes, reason in (({"to_anchor": "absent"}, "unknown reading link target in expository"),
                                ({"to_text_sha256": "0" * 64}, "target passage hash is stale in expository")):
            with self.subTest(changes=changes), tempfile.TemporaryDirectory() as temporary:
                # Standalone validation cannot resolve another captured mapping.
                self.artifact["reading_links"] = [reading_link(self.artifact, to_stage="expository", **changes)]
                self.validate()
                parent = Path(temporary)
                with self.assertRaisesRegex(ContractError, "papers/long.json: .*" + reason):
                    self.assemble(parent, **changes)
                self.assertFalse((parent / "bundle").exists())

    def test_cross_stage_target_edit_requires_rebinding_even_with_current_bundle_hashes(self):
        with tempfile.TemporaryDirectory() as temporary:
            output, manifest = self.assemble(Path(temporary))
            original = bundle.BundleCapture(output)
            mapping_path, content_path = output / "papers/expository.json", output / "papers/expository.md"
            mapping, content = decode_json(mapping_path.read_bytes()), content_path.read_bytes()
            start = content.index(b"<!-- passage:result -->") + len(b"<!-- passage:result -->")
            end = content.index(b"<!-- /passage:result -->")
            revised = content[start:end] + b"A revised statement explanation.\n"
            content = content[:start] + revised + content[end:]
            mapping["content_sha256"] = digest(content)
            next(p for p in mapping["passages"] if p["anchor"] == "result")["text_sha256"] = digest(revised)
            content_path.write_bytes(content)
            write_json(mapping_path, mapping)

            def bind_manifest():
                for row in manifest["files"]:
                    row["sha256"] = digest((output / row["path"]).read_bytes())
                write_json(output / "manifest.json", manifest)

            bind_manifest()
            with self.assertRaisesRegex(ContractError, "target passage hash is stale in expository"):
                bundle.check_bundle(output)
            self.assertTrue(bundle.check_bundle(original)["valid"])
            source_path = output / "papers/long.json"
            source = decode_json(source_path.read_bytes())
            source["reading_links"][0]["to_text_sha256"] = digest(revised)
            write_json(source_path, source)
            bind_manifest()
            self.assertTrue(bundle.check_bundle(output)["valid"])


if __name__ == "__main__":
    unittest.main()
