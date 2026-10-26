"""Offline regressions for source redirects and platform provenance."""
from __future__ import annotations

import io
import json
import tempfile
import time
import unittest
from email.message import Message
from pathlib import Path
from unittest.mock import patch
from urllib.error import HTTPError
from urllib.request import BaseHandler, ProxyHandler, build_opener
from urllib.response import addinfourl

from lean_exposition.consumer import inspect_graph, project_graph
from lean_exposition.contracts import ContractError, digest, validate_graph
from lean_exposition.intake import _PublicRedirect, fetch, validate_lock
from lean_exposition.prove2me import (
    API_BASE, REVIEWED_VERSION, Prove2MeClient, Prove2MeError, collect_prove2me, theorem_id,
)

REV = "a" * 40
ROOT = "11111111-1111-4111-8111-111111111111"
CHILD = "22222222-2222-4222-8222-222222222222"
PRIVATE = "33333333-3333-4333-8333-333333333333"
THEOREM_URL = "https://prove2.me/theorems/" + ROOT
BODY = b"synthetic locked source\n"


def source_lock(url):
    return {
        "schema_version": "1.0", "revision": REV, "license": "MIT",
        "sources": [{"id": "fixture", "revision": REV, "license": "MIT",
                     "repository": "https://github.com/example/repo"}],
        "files": [{"path": "source.txt", "source": "fixture", "url": url,
                   "upstream_path": "source.txt", "bytes": len(BODY),
                   "sha256": digest(BODY)}],
    }


class StubTransport(BaseHandler):
    """Let urllib process responses without any DNS, proxy, or network I/O."""
    handler_order = 100

    def __init__(self, redirect, body=BODY):
        self.redirect = redirect
        self.body = body
        self.visits = []

    def _response(self, request):
        self.visits.append(request.full_url)
        headers = Message()
        if len(self.visits) == 1:
            headers["Location"] = self.redirect
            response = addinfourl(io.BytesIO(b""), headers, request.full_url, 302)
            response.msg = "Found"
        else:
            response = addinfourl(io.BytesIO(self.body), headers, request.full_url, 200)
            response.msg = "OK"
        return response

    def https_open(self, request):
        return self._response(request)

    def http_open(self, request):
        return self._response(request)


class RedirectBoundaryTests(unittest.TestCase):
    def setUp(self):
        self.url = "https://raw.githubusercontent.com/example/repo/" + REV + "/source.txt"

    def test_disallowed_redirect_never_reaches_transport(self):
        for destination in ("http://127.0.0.1/private", "https://127.0.0.1/private",
                            "https://[::1]/private", "https://localhost/private",
                            "https://169.254.169.254/private", "https://public.example/a?secret=x",
                            "https://user@public.example/a", "https://@public.example/a",
                            "https://127.1/private", "https://0x7f000001/private",
                            "https://2130706433/private", "https://0177.0.0.1/private",
                            "https://[::ffff:127.0.0.1]/private"):
            with self.subTest(destination=destination), tempfile.TemporaryDirectory() as temporary:
                transport = StubTransport(destination)
                opener = build_opener(ProxyHandler({}), transport, _PublicRedirect())
                with patch("lean_exposition.intake.urllib.request.build_opener", return_value=opener):
                    with self.assertRaises(ContractError):
                        fetch(source_lock(self.url), Path(temporary) / "out")
                self.assertEqual(transport.visits, [self.url])
                self.assertFalse((Path(temporary) / "out/source.txt").exists())

    def test_public_https_redirects_keep_byte_integrity(self):
        for destination in ("https://cdn.example/elsewhere", "/other/path",
                            "https://[2001:4860:4860::8888]/source"):
            with self.subTest(destination=destination), tempfile.TemporaryDirectory() as temporary:
                transport = StubTransport(destination)
                opener = build_opener(ProxyHandler({}), transport, _PublicRedirect())
                with patch("lean_exposition.intake.urllib.request.build_opener", return_value=opener):
                    result = fetch(source_lock(self.url), Path(temporary) / "out")
                self.assertEqual(result["status"], "passed")
                self.assertEqual(result["lean_replay"], "not_implied")
                self.assertEqual((Path(temporary) / "out/source.txt").read_bytes(), BODY)
                self.assertEqual(len(transport.visits), 2)
                self.assertTrue(transport.visits[1].startswith("https://"))

    def test_redirect_does_not_bypass_locked_hash(self):
        with tempfile.TemporaryDirectory() as temporary:
            transport = StubTransport("https://cdn.example/source", body=b"altered source\n")
            opener = build_opener(ProxyHandler({}), transport, _PublicRedirect())
            with patch("lean_exposition.intake.urllib.request.build_opener", return_value=opener):
                with self.assertRaisesRegex(ContractError, "download differs"):
                    fetch(source_lock(self.url), Path(temporary) / "out")
            self.assertEqual(len(transport.visits), 2)
            self.assertFalse((Path(temporary) / "out/source.txt").exists())

    def test_direct_non_public_ip_and_localhost_are_rejected_offline(self):
        for host in ("127.0.0.1", "[::1]", "10.0.0.1", "169.254.169.254", "localhost",
                     "localhost.", "127.1", "0x7f000001", "0177.0.0.1", "2130706433",
                     "[::ffff:127.0.0.1]", "127%2e0%2e0%2e1", "localhost\u3002",
                     "127\u30020\u30020\u30021"):
            with self.subTest(host=host):
                lock = source_lock("https://" + host + "/" + REV + "/source.txt")
                lock["sources"][0].pop("repository")
                with self.assertRaises(ContractError):
                    validate_lock(lock)

    def test_stdlib_proxy_configuration_is_preserved(self):
        with patch("urllib.request.getproxies", return_value={"https": "http://proxy.example:8080"}):
            opener = build_opener(_PublicRedirect())
        proxy = next(handler for handler in opener.handlers if isinstance(handler, ProxyHandler))
        self.assertEqual(proxy.proxies["https"], "http://proxy.example:8080")

    def test_github_repository_aliases_keep_owner_and_host_binding(self):
        for repository in ("https://github.com/example/repo", "https://GITHUB.COM./example/repo",
                           "https://github\u3002com/example/repo"):
            for host in ("raw.githubusercontent.com", "raw.githubusercontent.com.",
                         "raw\u3002githubusercontent\u3002com"):
                with self.subTest(repository=repository, host=host):
                    lock = source_lock("https://" + host + "/example/repo/" + REV + "/source.txt")
                    lock["sources"][0]["repository"] = repository
                    validate_lock(lock)
            for host in ("evil.example", "raw.githubusercontent.com.evil.example"):
                with self.subTest(repository=repository, host=host):
                    lock = source_lock("https://" + host + "/example/repo/" + REV + "/source.txt")
                    lock["sources"][0]["repository"] = repository
                    with self.assertRaisesRegex(ContractError, "differs from the locked repository"):
                        validate_lock(lock)


class WireResponse(io.BytesIO):
    status = 200

    def __init__(self, data, url):
        super().__init__(data)
        self.url = url

    def geturl(self):
        return self.url


def platform_routes():
    root = {"theorem_id": ROOT, "theorem_name": "Synthetic.root", "visibility": "public",
            "status": "Proved", "mathlib_rev": REV, "deprecated_at": "2026-01-01T00:00:00Z"}
    child = {"theorem_id": CHILD, "theorem_name": "Synthetic.child", "visibility": "public",
             "status": "Open", "mathlib_rev": REV, "deprecated_at": None}
    return {
        "/theorems/" + ROOT: root,
        "/theorems/" + CHILD: child,
        "/theorems/" + ROOT + "/decompositions": {"decompositions": [
            {"submission_id": None, "deprecated_at": "2026-01-01T00:00:00Z",
             "children": [{"theorem_id": CHILD}, {"theorem_id": PRIVATE}]},
            {"submission_id": None, "deprecated_at": None, "children": [{"theorem_id": CHILD}]},
            {"submission_id": None, "children": []},
        ]},
        "/theorems/" + CHILD + "/decompositions": {"decompositions": []},
        "/environments": {"environments": [{"mathlib_rev": REV, "toolchain": "leanprover/lean4:v4.33.1"}]},
    }


class WireAPI:
    def __init__(self, routes=None, auth=None):
        self.routes = platform_routes() if routes is None else routes
        self.auth = auth or {}

    def __call__(self, request, timeout):
        route = request.full_url.removeprefix(API_BASE)
        if request.method == "POST":
            value = {"version": REVIEWED_VERSION, "access_token": "synthetic-token",
                     "expires_at": time.time() + 3600}
            value.update(self.auth)
        elif route == "/theorems/" + PRIVATE:
            raise HTTPError(request.full_url, 404, "unavailable", {}, None)
        else:
            value = self.routes[route]
        raw = value if isinstance(value, bytes) else json.dumps(value, ensure_ascii=True).encode()
        return WireResponse(raw, request.full_url)


class PlatformBoundaryTests(unittest.TestCase):
    def setUp(self):
        environment = patch.dict("os.environ", {"PROVE2ME_API_KEY": "p2m_synthetic"})
        environment.start()
        self.addCleanup(environment.stop)
        network = patch("lean_exposition.prove2me._open", side_effect=AssertionError("network forbidden"))
        network.start()
        self.addCleanup(network.stop)

    def collect(self, routes=None):
        return collect_prove2me(THEOREM_URL, Prove2MeClient(opener=WireAPI(routes)))

    def test_malformed_theorem_url_raises_documented_error(self):
        for url in ("https://[invalid", None):
            with self.subTest(url=url), self.assertRaisesRegex(Prove2MeError, "expected https://prove2.me"):
                theorem_id(url)
        self.assertEqual(theorem_id(THEOREM_URL), ROOT)

    def test_graph_receipt_retains_mixed_groups_without_promoting_status(self):
        graph, files = self.collect()
        observation = graph["evidence"][0]
        receipt = observation["receipt"]
        metadata = receipt["platform_deprecation"]
        root_id, child_id = "prove2me:theorem:" + ROOT, "prove2me:theorem:" + CHILD
        flags = {row["node_id"]: row["deprecated"] for row in metadata["entities"]}
        self.assertIs(flags[root_id], True)
        self.assertIs(flags[child_id], False)
        groups = metadata["groups"]
        self.assertEqual([g["deprecated"] for g in groups], [True, False, None])
        self.assertEqual([g["children"] for g in groups], [[child_id], [child_id], []])
        self.assertEqual(groups[0]["omitted_children"], 1)
        self.assertNotIn(PRIVATE.encode(), b"".join(files.values()))
        self.assertEqual({g["source_id"] for g in groups}, {"decompositions-" + ROOT})
        self.assertEqual(receipt["platform_closure_status"], "partial")
        self.assertEqual(receipt["local_verification"], "not_run")
        self.assertEqual(receipt["assumption_audit"], "not_run")
        self.assertEqual({n["status"] for n in graph["nodes"]}, {"unverified"})
        self.assertEqual(validate_graph(graph)["argument_closure"], [root_id])
        inspected = inspect_graph(graph)
        self.assertEqual(inspected["evidence"][0]["receipt"]["platform_deprecation"], metadata)
        projected = project_graph(files["graph.json"], "platform")
        self.assertEqual(projected["coverage"]["platform_observations"][0]["recorded"]["platform_deprecation"], metadata)
        self.assertFalse(projected["semantic_certification"])
        self.assertTrue(all(digest(files[s["path"]]) == s["sha256"] for s in graph["sources"]))

    def test_omitted_deprecation_is_unknown_not_false(self):
        routes = platform_routes()
        del routes["/theorems/" + ROOT]["deprecated_at"]
        graph, files = self.collect(routes)
        record = json.loads(files["snapshots/theorem-" + ROOT + ".json"])
        self.assertIsNone(record["deprecated"])
        row = next(r for r in graph["evidence"][0]["receipt"]["platform_deprecation"]["entities"]
                   if r["node_id"].endswith(ROOT))
        self.assertIsNone(row["deprecated"])

    def test_malformed_json_fields_raise_safe_documented_error(self):
        variants = [
            ("status", []), ("status", {}), ("theorem_name", "synthetic\ud800"),
            ("deprecated_at", False), ("deprecated_at", {}), ("deprecated_at", "not-a-date"),
        ]
        for field, value in variants:
            with self.subTest(field=field, value=repr(value)):
                routes = platform_routes()
                routes["/theorems/" + ROOT][field] = value
                with self.assertRaises(Prove2MeError) as caught:
                    self.collect(routes)
                self.assertNotIn("synthetic-token", str(caught.exception))
        routes = platform_routes()
        routes["/theorems/" + ROOT + "/decompositions"]["decompositions"][0]["deprecated_at"] = False
        with self.assertRaisesRegex(Prove2MeError, "deprecation"):
            self.collect(routes)

    def test_excessive_json_nesting_is_a_safe_error(self):
        routes = platform_routes()
        routes["/theorems/" + ROOT] = b'{"x":' + b'[' * 10000 + b'0' + b']' * 10000 + b'}'
        with self.assertRaisesRegex(Prove2MeError, "malformed JSON"):
            self.collect(routes)

    def test_unusable_source_references_are_not_persisted(self):
        for value in ("https://@example.org/", "https://user@example.org/",
                      "https://example.org:bad/source"):
            with self.subTest(value=repr(value)):
                routes = platform_routes()
                routes["/theorems/" + ROOT]["source"] = value
                graph, files = self.collect(routes)
                root = json.loads(files["snapshots/theorem-" + ROOT + ".json"])
                self.assertNotIn("source_reference", root)
                self.assertFalse(any(c["id"].startswith("source-reference:") for c in graph["citations"]))
        routes = platform_routes()
        routes["/theorems/" + ROOT]["source"] = "https://example.org/a\ud800"
        with self.assertRaisesRegex(Prove2MeError, "malformed JSON"):
            self.collect(routes)

    def test_malformed_auth_metadata_raises_safe_error(self):
        for auth in ({"access_token": "synthetic\ud800"}, {"expires_at": True}):
            with self.subTest(auth=repr(auth)):
                client = Prove2MeClient(opener=WireAPI(auth=auth))
                with self.assertRaises(Prove2MeError):
                    collect_prove2me(THEOREM_URL, client)


if __name__ == "__main__":
    unittest.main()
