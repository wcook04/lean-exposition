"""Synthetic read-only API tests; no real credentials or live network access."""
import io
import json
import tempfile
import time
import unittest
from pathlib import Path
from unittest.mock import patch
from urllib.error import HTTPError

from lean_exposition.contracts import digest, validate_graph
from lean_exposition.prove2me import (
    API_BASE, REVIEWED_VERSION, Prove2MeClient, Prove2MeError,
    _NoRedirect, collect_prove2me, intake_prove2me, theorem_id,
)

ROOT = "11111111-1111-4111-8111-111111111111"
CHILD = "22222222-2222-4222-8222-222222222222"
DEF = "33333333-3333-4333-8333-333333333333"
PRIVATE = "44444444-4444-4444-8444-444444444444"
SUBMISSION = "55555555-5555-4555-8555-555555555555"
REV = "a" * 40
URL = "https://prove2.me/theorems/" + ROOT


class Response(io.BytesIO):
    status = 200

    def __init__(self, data, url):
        super().__init__(data)
        self.url = url

    def geturl(self):
        return self.url


def entity(kind, identity, name, **extra):
    return {kind + "_id": identity, kind + "_name": name, "visibility": "public",
            "status": "Proved", "mathlib_rev": REV, **extra}


def fixture():
    return {
        "/theorems/" + ROOT: entity("theorem", ROOT, "Synthetic.result",
            source="https://example.org/source/" + REV,
            formal_statement="DO_NOT_RETAIN_PROOF_TEXT", audits=[{"comment": "DO_NOT_RETAIN_AUDIT"}]),
        "/theorems/" + CHILD: entity("theorem", CHILD, "Synthetic.lemma", status="Open"),
        "/definitions/" + DEF: entity("definition", DEF, "Synthetic.definition"),
        "/theorems/" + PRIVATE: entity("theorem", PRIVATE, "DO_NOT_RETAIN_PRIVATE", visibility="private"),
        "/theorems/" + ROOT + "/decompositions": {"decompositions": [
            {"submission_id": SUBMISSION, "created_by": "DO_NOT_RETAIN_PERSON",
             "children": [{"theorem_id": CHILD}, {"definition_id": DEF}, {"theorem_id": PRIVATE}]}]},
        # The cycle tests visited-set handling; this is synthetic, not a claim about platform admissibility.
        "/theorems/" + CHILD + "/decompositions": {"decompositions": [
            {"submission_id": None, "children": [{"theorem_id": ROOT}]}]},
        "/environments": {"environments": [{"mathlib_rev": REV, "toolchain": "leanprover/lean4:v4.33.1"},
            {"mathlib_rev": "b" * 40, "toolchain": "DO_NOT_RETAIN_UNRELATED"}]},
    }


class FakeAPI:
    def __init__(self, routes=None):
        self.routes = fixture() if routes is None else routes
        self.calls = []
        self.version = REVIEWED_VERSION

    def __call__(self, request, timeout):
        self.calls.append(request)
        self.assert_origin(request.full_url)
        route = request.full_url.removeprefix(API_BASE)
        if request.method == "POST":
            if route != "/agent/refresh":
                raise AssertionError("attempted platform mutation")
            value = {"access_token": "synthetic-token", "expires_at": time.time() + 3600,
                     "version": self.version}
        else:
            if request.method != "GET":
                raise AssertionError("unexpected request method")
            value = self.routes[route]
            if isinstance(value, Exception):
                raise value
        return Response(json.dumps(value).encode(), request.full_url)

    @staticmethod
    def assert_origin(url):
        if not url.startswith(API_BASE + "/"):
            raise AssertionError("wrong API origin")


class Prove2MeTests(unittest.TestCase):
    def setUp(self):
        env = patch.dict("os.environ", {"PROVE2ME_API_KEY": "p2m_synthetic_test"})
        env.start()
        self.addCleanup(env.stop)
        network = patch("lean_exposition.prove2me._open", side_effect=AssertionError("live network forbidden"))
        network.start()
        self.addCleanup(network.stop)

    def collect(self, api=None, **kwargs):
        api = api or FakeAPI()
        return collect_prove2me(URL, Prove2MeClient(opener=api), **kwargs)

    def test_public_only_direction_and_separate_status(self):
        api = FakeAPI()
        graph, files = self.collect(api)
        report = validate_graph(graph)
        self.assertEqual(len(graph["nodes"]), 3)
        self.assertTrue(all(n["status"] == "unverified" for n in graph["nodes"]))
        root = next(n for n in graph["nodes"] if n["platform"]["id"] == ROOT)
        self.assertEqual(root["platform"]["status"], "Proved")
        self.assertEqual(len(root["citation_ids"]), 2)
        self.assertEqual(report["argument_closure"], ["prove2me:theorem:" + ROOT])
        self.assertEqual(len(report["platform_closure"]), 3)
        self.assertIn({"from": root["id"], "to": "prove2me:theorem:" + CHILD,
                       "kind": "platform_decomposition", "evidence_ids": ["platform-intake"]}, graph["edges"])
        retained = b"".join(files.values())
        self.assertNotIn(b"DO_NOT_RETAIN", retained)
        self.assertNotIn(PRIVATE.encode(), retained)
        self.assertNotIn(b"synthetic-token", retained)
        self.assertNotIn(b"p2m_synthetic_test", retained)
        self.assertIn(("https://example.org/source/" + REV).encode(), retained)
        self.assertEqual(sum(r.method == "POST" for r in api.calls), 1)
        for source in graph["sources"]:
            self.assertEqual(digest(files[source["path"]]), source["sha256"])
        provenance = graph["evidence"][0]["receipt"]["provenance"]
        self.assertTrue(any(p["response_sha256"] != p["retained_sha256"] for p in provenance))

    def test_root_visibility_fails_closed(self):
        for visibility in ("private", None):
            api = FakeAPI()
            api.routes["/theorems/" + ROOT]["visibility"] = visibility
            with self.subTest(visibility=visibility), self.assertRaisesRegex(Prove2MeError, "explicitly public"):
                self.collect(api)

    def test_missing_child_and_caps_remain_partial(self):
        api = FakeAPI()
        api.routes["/theorems/" + CHILD] = HTTPError("redacted", 404, "sensitive body", {}, None)
        graph, files = self.collect(api)
        self.assertNotIn(CHILD.encode(), b"".join(files.values()))
        self.assertEqual(graph["evidence"][0]["receipt"]["omissions"]["non_public_or_unavailable"], 2)
        for options, expected in [({"max_nodes": 1}, "node_limit"), ({"max_depth": 0}, "depth_limit")]:
            with self.subTest(options=options):
                graph, _ = self.collect(**options)
                receipt = graph["evidence"][0]["receipt"]
                self.assertEqual(receipt["platform_closure_status"], "partial")
                self.assertGreater(receipt["omissions"][expected], 0)

    def test_unreviewed_version_stops_after_auth(self):
        api = FakeAPI()
        api.version = "99.0.0"
        with self.assertRaisesRegex(Prove2MeError, "version changed"):
            self.collect(api)
        self.assertEqual(len(api.calls), 1)

    def test_url_and_route_allowlists(self):
        for url in ["http://prove2.me/theorems/" + ROOT, URL + "?token=secret",
                    URL.replace("prove2.me", "evil.example"), "https://prove2.me/missions/" + ROOT,
                    "https://user:secret@prove2.me/theorems/" + ROOT]:
            with self.subTest(url=url), self.assertRaises(Prove2MeError):
                theorem_id(url)
        for route in ["/verify", "/agent/api-key", "//evil.example", "/theorems/" + ROOT + "?x=y"]:
            with self.assertRaisesRegex(Prove2MeError, "unsupported"):
                Prove2MeClient(opener=FakeAPI()).get(route)

    def test_redirects_and_transport_errors_do_not_disclose_bodies(self):
        self.assertIsNone(_NoRedirect().redirect_request(None, None, 302, "", {}, "https://elsewhere.example"))
        for opener in [lambda req, timeout: Response(b"{}", "https://elsewhere.example"),
                       lambda req, timeout: (_ for _ in ()).throw(HTTPError("secret", 302, "sensitive", {}, None))]:
            with self.assertRaises(Prove2MeError) as caught:
                self.collect_client(opener)
            self.assertNotIn("sensitive", str(caught.exception))
            self.assertNotIn("secret", str(caught.exception))

    def collect_client(self, opener):
        return collect_prove2me(URL, Prove2MeClient(opener=opener))

    def test_response_and_request_budgets(self):
        with patch("lean_exposition.prove2me.MAX_RESPONSE_BYTES", 10):
            with self.assertRaisesRegex(Prove2MeError, "byte budget"):
                self.collect()
        with self.assertRaisesRegex(Prove2MeError, "request budget"):
            collect_prove2me(URL, Prove2MeClient(opener=FakeAPI(), max_requests=1))
        api = FakeAPI()
        with patch("lean_exposition.prove2me.MAX_TOTAL_BYTES", 500):
            with self.assertRaisesRegex(Prove2MeError, "byte budget"):
                self.collect(api)

    def test_malformed_and_duplicate_json_are_rejected_without_echo(self):
        for raw in [b'{"private-secret":', b'{"private-secret":1,"private-secret":2}', b'[]']:
            with self.subTest(raw=raw), self.assertRaises(Prove2MeError) as caught:
                self.collect_client(lambda req, timeout: Response(raw, req.full_url))
            self.assertNotIn("private-secret", str(caught.exception))

    def test_write_occurs_only_after_complete_validation(self):
        with tempfile.TemporaryDirectory() as tmp:
            output = Path(tmp) / "output"
            api = FakeAPI()
            api.routes["/theorems/" + ROOT]["visibility"] = "private"
            with patch("lean_exposition.prove2me._open", api), self.assertRaises(Prove2MeError):
                intake_prove2me(URL, output)
            self.assertFalse(output.exists())
            with patch("lean_exposition.prove2me._open", FakeAPI()):
                result = intake_prove2me(URL, output)
            self.assertTrue((output / "graph.json").is_file())
            self.assertEqual(result["local_verification"], "not_run")
            with self.assertRaisesRegex(Prove2MeError, "empty directory"):
                intake_prove2me(URL, output)

    def test_credential_file_external_private_and_unchanged(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            credentials = root / "key.json"
            raw = b'{"api_key":"p2m_synthetic.file"}'
            credentials.write_bytes(raw)
            credentials.chmod(0o600)
            with patch("lean_exposition.prove2me._open", FakeAPI()):
                intake_prove2me(URL, root / "output", credentials=credentials)
            self.assertEqual(credentials.read_bytes(), raw)
            credentials.chmod(0o644)
            with self.assertRaises(Prove2MeError):
                Prove2MeClient(credentials, opener=FakeAPI()).get("/environments")

    def test_credentials_inside_repository_are_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / ".git").mkdir()
            credentials = root / "key.json"
            credentials.write_text('{"api_key":"p2m_synthetic"}')
            credentials.chmod(0o600)
            with self.assertRaises(Prove2MeError):
                Prove2MeClient(credentials, opener=FakeAPI()).get("/environments")

    def test_checked_in_live_example_hashes_and_public_boundaries(self):
        root = Path(__file__).resolve().parents[1] / "examples/prove2me/full-support"
        graph = json.loads((root / "graph.json").read_text())
        validate_graph(graph)
        self.assertEqual(graph["extraction_status"], "not_run")
        for node in graph["nodes"]:
            self.assertEqual(node["platform"]["visibility"], "public")
            self.assertEqual(node["status"], "unverified")
        for source in graph["sources"]:
            self.assertEqual(digest((root / source["path"]).read_bytes()), source["sha256"])


if __name__ == "__main__":
    unittest.main()
