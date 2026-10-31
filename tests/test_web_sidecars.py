"""The Lean index and alignment routes sit beside an edition and never alter it."""
import json
import shutil
import tempfile
import unittest
from pathlib import Path

from lean_exposition import bundle, lean_index, web
from lean_exposition.contracts import ContractError, digest
from test_web import request

ROOT = Path(__file__).resolve().parents[1]
PAPERS = ROOT / "papers/qaoa-sk"
TREE = ROOT / "examples/qaoa-sk/upstream/lean"


def body(response):
    return json.loads(response["body"])


class Sidecars(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.parent = Path(tempfile.mkdtemp())
        cls.root = cls.parent / "bundle"
        bundle.assemble_bundle(ROOT / "examples/qaoa-sk/evidence-graph.json", {
            "long": (PAPERS / "long/reasoning-record.md", PAPERS / "long/reasoning-record.json"),
            "short": (PAPERS / "short/paper.md", PAPERS / "short/correspondence.json"),
            "expository": (PAPERS / "expository/main.md", PAPERS / "expository/correspondence.json"),
        }, cls.root)
        cls.alignment = cls.parent / "alignment"
        cls.alignment.mkdir()
        (cls.alignment / "one.json").write_text(json.dumps({"schema_version": "1.0", "records": {
            "support.moment_saturation": {"short": "Both moments", "lean": [
                {"file": "OAI/Probability/SKSupport/Main.lean", "name": "full_support", "relation": "contains"}],
                "statements": []}}}), encoding="utf-8")
        cls.bare = web.create_app(cls.root)
        cls.app = web.create_app(cls.root, lean_index=TREE, alignment=cls.alignment)

    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(cls.parent)

    def data(self, path, app=None):
        response = request(app or self.app, path)
        self.assertEqual(response["status"], 200)
        return body(response)["data"]

    def test_routes_are_absent_without_sidecars(self):
        for path, code in (("/api/v1/lean/modules", "lean_index_unavailable"),
                           ("/api/v1/lean/names", "lean_index_unavailable"),
                           ("/api/v1/lean/module?name=OAI.X", "lean_index_unavailable"),
                           ("/api/v1/alignment", "alignment_unavailable"),
                           ("/api/v1/ties/short", "alignment_unavailable")):
            response = request(self.bare, path)
            self.assertEqual((response["status"], body(response)["error"]["code"]), (404, code))
        self.assertEqual(self.data("/api/v1", self.bare)["sidecars"]["lean_index"], {"available": False})

    def test_sidecars_change_no_bundle_hash(self):
        self.assertEqual(self.app.manifest_sha256, self.bare.manifest_sha256)
        self.assertEqual(digest((self.root / "manifest.json").read_bytes()), self.app.manifest_sha256)
        before = body(request(self.bare, "/api/v1/overview"))
        self.assertEqual(body(request(self.app, "/api/v1/overview")), before)

    def test_discovery_records_each_sidecar_hash(self):
        sidecars = self.data("/api/v1")["sidecars"]
        index = lean_index.build_index(TREE)
        self.assertEqual(sidecars["lean_index"]["sha256"], digest(lean_index.canonical(index)))
        self.assertEqual(len(sidecars["alignment"]["sha256"]), 64)
        self.assertEqual(len(sidecars["ties"]["sha256"]), 64)
        self.assertEqual(self.data("/api/v1", self.bare)["sidecars"]["ties"], {"available": False})

    def test_modules_names_and_module_match_the_client_contract(self):
        modules = self.data("/api/v1/lean/modules")
        self.assertEqual({"revision", "base_url", "toolchain", "dependency_source", "counts", "folders"}
                         - modules.keys(), set())
        row = modules["folders"][0]["modules"][0]
        self.assertEqual(row.keys(), {"module", "path", "lines", "declarations", "sha256"})
        self.assertNotIn('"source"', json.dumps(modules))
        names = self.data("/api/v1/lean/names")
        self.assertEqual(names.keys(), {"modules", "names"})
        field = next(r for r in names["names"] if r[0].endswith("OrderParameter.monotone"))
        self.assertEqual(field[1], "def")
        one = self.data("/api/v1/lean/module?name=OAI.Probability.SKSupport.Main")
        self.assertEqual(one["module"], "OAI.Probability.SKSupport.Main")
        declaration = next(r for r in one["declarations"] if r["short"] == "full_support")
        self.assertEqual({"name", "short", "kind", "namespace", "line", "signature_end_line", "end_line",
                          "doc", "private", "uses", "used_by"} - declaration.keys(), set())
        response = request(self.app, "/api/v1/lean/module?name=OAI.Absent")
        self.assertEqual(response["status"], 404)
        self.assertEqual(request(self.app, "/api/v1/lean/module")["status"], 400)
        self.assertEqual(request(self.app, "/api/v1/lean/modules?extra=1")["status"], 400)

    def test_alignment_keyed_by_node_id(self):
        result = self.data("/api/v1/alignment")
        row = result["records"]["support.moment_saturation"]
        self.assertEqual(row["lean"][0]["name"], "OAI.ZeroTemperatureSK.full_support")
        self.assertEqual(result["dictionary"], [])
        self.assertIn("steps", result)

    def test_alignment_rows_carry_exact_lines_and_statements_their_lean(self):
        row = self.data("/api/v1/alignment")["records"]["support.moment_saturation"]
        self.assertEqual((row["lean"][0]["lines"], row["lean"][0]["proof_lines"]), ([35, 36], [37, 59]))

    def test_ties_route_serves_a_small_index_for_each_paper(self):
        for stage in ("long", "short", "expository"):
            result = self.data(f"/api/v1/ties/{stage}")
            self.assertEqual(result.keys(), {"segments", "ties", "passages", "meaning"})
            self.assertTrue(result["passages"])
            start, end, records, anchor = result["passages"][0]
            self.assertLess(start, end)
            self.assertTrue(records)
            self.assertIsInstance(anchor, str)
        self.assertEqual(request(self.app, "/api/v1/ties/other")["status"], 404)
        self.assertEqual(request(self.app, "/api/v1/ties/short?extra=1")["status"], 400)
        self.assertEqual(request(self.app, "/api/v1/ties")["status"], 404)

    def test_ties_follow_authored_slices_and_their_lean(self):
        directory = self.parent / "tied"
        directory.mkdir()
        (directory / "one.json").write_text(json.dumps({"schema_version": "1.0", "records": {
            "support.moment_saturation": {"short": "Both moments", "lean": [
                {"file": "OAI/Probability/SKSupport/Main.lean", "name": "minimizer_full_support_actual",
                 "relation": "contains"}],
                "statements": [{"paper": "short", "role": "statement", "from": "For the solution of the displayed SDE",
                                "to": "=1.\n$$"}]}}}), encoding="utf-8")
        (directory / "ties-short.json").write_text(json.dumps({"schema": 1, "statements": [{
            "record": "support.moment_saturation", "paper": "short", "role": "derivation",
            "from": "These cases exhaust the complement of the relatively closed set $S$.",
            "to": "These cases exhaust the complement of the relatively closed set $S$.",
            "lean": [{"name": "OAI.ZeroTemperatureSK.minimizer_full_support_actual", "lines": [30, 33]}]}]}),
            encoding="utf-8")
        app = web.create_app(self.root, lean_index=lean_index.build_index(TREE), alignment=directory)
        self.assertEqual(app.alignment_errors, [])
        ties = self.data("/api/v1/ties/short", app)
        self.assertEqual([tie["lines"] for tie in ties["ties"]], [[19, 22], [30, 33]])
        self.assertEqual(ties["ties"][0]["name"], "OAI.ZeroTemperatureSK.minimizer_full_support_actual")
        self.assertEqual(ties["ties"][0]["module"], "OAI.Probability.SKSupport.Main")
        self.assertEqual(self.data("/api/v1/ties/long", app)["ties"], [])

    def test_a_failing_alignment_row_is_reported_and_left_out(self):
        bad = self.parent / "bad"
        bad.mkdir()
        (bad / "one.json").write_text(json.dumps({"schema_version": "1.0", "records": {
            "absent": {"short": "No record", "lean": [], "statements": []}}}))
        app = web.create_app(self.root, lean_index=lean_index.build_index(TREE), alignment=bad)
        self.assertEqual(self.data("/api/v1/alignment", app)["records"], {})
        self.assertEqual(len(app.alignment_errors), 1)

    def test_alignment_requires_an_index(self):
        with self.assertRaises(ContractError):
            web.create_app(self.root, alignment=self.alignment)


if __name__ == "__main__":
    unittest.main()
