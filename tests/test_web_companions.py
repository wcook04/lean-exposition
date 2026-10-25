"""Companion paths are explicit transport configuration, never captured source edits."""
from __future__ import annotations

import http.client
import json
import shutil
import tempfile
import unittest
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from unittest.mock import patch
from urllib.parse import parse_qs, urlencode, urlsplit

from lean_exposition import bundle, web
from lean_exposition.contracts import ContractError, digest
from test_corpus_views import corpus_bundle
from test_web import local_server, request


class WebCompanionTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="lean-exposition-companions-")
        self.addCleanup(temporary.cleanup)
        self.root = corpus_bundle(Path(temporary.name))
        self.capture = bundle.BundleCapture(self.root)
        self.paths = {"long": "accounts/details/record.md", "short": "accounts/brief/paper.md",
                      "expository": "introductions/main.md"}
        self.app = web.create_app(self.capture, document_paths=self.paths)

    def data(self, route="/api/v1", query=None, *, app=None):
        response = request(app or self.app, route, query)
        self.assertEqual(response["status"], 200, response["body"].decode())
        result = json.loads(response["body"])
        self.assertEqual(result["snapshot"]["manifest_sha256"], self.app.manifest_sha256)
        return result["data"]

    def resolve(self, href, *, paper="short", app=None):
        result = self.data("/api/v1/papers/resolve-link", {"paper": paper, "href": href}, app=app)
        self.assertEqual(result["href"], href)
        self.assertEqual(result["paper"], paper)
        self.assertEqual(result["resolver_version"], "0.1.0")
        self.assertEqual(result["resolution_scope"], "document_identity_only")
        self.assertFalse(result["fragment_verified"])
        return result

    def test_declared_relative_paths_resolve_to_pinned_captured_documents(self):
        for paper, href, target, fragment in (
                ("short", "../details/record.md#unverified-anchor", "long", "unverified-anchor"),
                ("short", "paper.md", "short", None),
                ("long", "../../introductions/main.md#π", "expository", "π"),
                ("expository", "../accounts/brief/paper.md#section%20one", "short", "section one"),
                ("short", "../details/../details/./record.md", "long", None)):
            with self.subTest(paper=paper, href=href):
                result = self.resolve(href, paper=paper)
                self.assertEqual((result["status"], result["reason"]),
                                 ("resolved", "declared_document_path"))
                self.assertEqual(result["fragment"], fragment)
                destination = result["target"]
                self.assertEqual(destination["stage"], target)
                self.assertEqual(destination["path"], f"papers/{target}.md")
                self.assertEqual(destination["markdown_ref"],
                                 self.app._papers[target]["bundle"]["markdown_ref"])
                for key in ("paper_href", "document_href", "structure_href"):
                    self.assertEqual(parse_qs(urlsplit(destination[key]).query)["manifest"],
                                     [self.app.manifest_sha256])
                    self.assertNotIn("#", destination[key])
                self.assertEqual(request(self.app, destination["document_href"])["body"],
                                 self.capture.files[destination["path"]])

    def test_fragment_only_needs_no_path_config_and_does_not_verify_anchor(self):
        unconfigured = web.create_app(self.capture)
        for app in (self.app, unconfigured):
            for href, fragment in (("#does-not-exist", "does-not-exist"), ("#", ""),
                                   ("#question?with-query-spelling", "question?with-query-spelling")):
                result = self.resolve(href, paper="expository", app=app)
                self.assertEqual(result["status"], "resolved")
                self.assertEqual(result["reason"], "same_document_fragment")
                self.assertEqual(result["target"]["stage"], "expository")
                self.assertEqual(result["fragment"], fragment)
        for href in ("long.md#anchor", "papers/long.md", "../details/record.md", "paper.md"):
            result = self.resolve(href, app=unconfigured)
            self.assertEqual((result["status"], result["reason"]),
                             ("unresolved", "document_paths_not_configured"))
            self.assertNotIn("target", result)

    def test_unknown_companions_and_encoded_traversal_use_exact_declared_names(self):
        for href, status, reason in (
                ("record.md", "unresolved", "undeclared_document"),
                ("../details/record.pdf", "unresolved", "undeclared_document"),
                ("../details/record.md/", "unresolved", "undeclared_document"),
                ("../details/record.md/.", "unresolved", "undeclared_document"),
                ("../../papers/long.md", "unresolved", "undeclared_document"),
                ("../../../accounts/details/record.md", "unresolved", "path_outside_declared_namespace"),
                ("%2e%2e/%2e%2e/%2e%2e/accounts/details/record.md", "unresolved", "path_outside_declared_namespace"),
                ("%252e%252e/details/record.md", "unresolved", "undeclared_document"),
                ("/accounts/details/record.md", "unsupported", "absolute_path_not_supported"),
                ("%2faccounts/details/record.md", "unsupported", "absolute_path_not_supported"),
                ("%2f%2fexample.org/path", "unsupported", "absolute_path_not_supported"),
                ("..%5cdetails%5crecord.md", "unsupported", "unsafe_path"),
                ("../details/%00record.md", "unsupported", "unsafe_path"),
                ("../details/%C2%85record.md", "unsupported", "unsafe_path"),
                ("javascript%3Aalert(1)", "unsupported", "unsafe_path"),
                ("../details/record.md%3Fdownload", "unsupported", "unsafe_path"),
                ("../details/record.md%23anchor", "unsupported", "unsafe_path"),
                ("../details/%FFrecord.md", "unsupported", "invalid_href"),
                ("../details/record.md%", "unsupported", "invalid_href")):
            with self.subTest(href=href):
                result = self.resolve(href)
                self.assertEqual((result["status"], result["reason"]), (status, reason))
                self.assertNotIn("target", result)
        self.assertEqual(self.resolve("%2e%2e%2fdetails%2frecord.md")["target"]["stage"], "long")

    def test_logical_unicode_and_percent_names_decode_once_without_basename_guessing(self):
        paths = {"long": "α/one/shared name.md", "short": "α/two/shared name.md",
                 "expository": "α/three/100%.md"}
        app = web.create_app(self.capture, document_paths=paths)
        self.assertEqual(self.resolve("../one/shared%20name.md", app=app)["target"]["stage"], "long")
        self.assertEqual(self.resolve("shared%20name.md", app=app)["target"]["stage"], "short")
        self.assertEqual(self.resolve("../three/100%25.md", app=app)["target"]["stage"], "expository")
        self.assertEqual(self.resolve("../one/shared%2520name.md", app=app)["status"], "unresolved")

    def test_external_and_unsupported_urls_never_produce_navigation_targets(self):
        for href in ("https://example.org/paper?download=1#section", "HTTP://example.org/paper",
                     "mailto:reader@example.org?subject=Paper", "//example.org/long.md"):
            with self.subTest(href=href):
                result = self.resolve(href)
                self.assertEqual((result["status"], result["reason"]), ("external", "external_url"))
                self.assertNotIn("target", result)
                self.assertFalse(any(key.endswith("_href") for key in result))
        for href, reason in (("file:///tmp/record.md", "unsupported_scheme"),
                             ("javascript:alert(1)", "unsupported_scheme"),
                             ("data:text/html,hello", "unsupported_scheme"),
                             ("ftp://example.org/paper.md", "unsupported_scheme"),
                             ("https:relative", "invalid_external_url"),
                             ("mailto:", "invalid_external_url"),
                             ("//", "invalid_external_url"),
                             ("https://[invalid", "invalid_href"),
                             (" javascript:alert(1)", "invalid_href"),
                             ("java\nscript:alert(1)", "invalid_href"),
                             ("#bad%0Afragment", "invalid_fragment")):
            with self.subTest(href=href):
                result = self.resolve(href)
                self.assertEqual((result["status"], result["reason"]), ("unsupported", reason))
                self.assertNotIn("target", result)

    def test_local_queries_are_explicitly_unsupported_including_empty_query(self):
        for href in ("paper.md?download=1", "paper.md?", "?mode=reader#anchor", "?#anchor"):
            result = self.resolve(href)
            self.assertEqual((result["status"], result["reason"]),
                             ("unsupported", "local_query_not_supported"))
            self.assertNotIn("target", result)

    def test_config_validation_happens_before_capture_and_rejects_ambiguous_paths(self):
        invalid = [[], "paths", {}, {"long": "record.md"},
                   self.paths | {"other": "other.md"}, self.paths | {"short": self.paths["long"]}]
        for path in (None, 1, True, Path("record.md"), b"record.md", [], "", "/record.md",
                     "//host/record.md", "a/./record.md", "../record.md", "a/../record.md",
                     "a//record.md", "a/", "a\\record.md", "a?query", "a#fragment",
                     "a\nrecord.md", "a\x00record.md", "a\x7frecord.md", "a\x85record.md",
                     "a\ud800record.md", "C:/record.md", "file:record.md"):
            invalid.append(self.paths | {"long": path})
        with patch.object(web, "BundleCapture", side_effect=AssertionError("must not read invalid config")):
            for paths in invalid:
                with self.subTest(paths=repr(paths)), self.assertRaises(ContractError):
                    web.create_app(Path("does-not-exist"), document_paths=paths)

    def test_config_is_detached_and_has_its_own_stable_identity(self):
        original = dict(self.paths)
        config = self.data()["companion_resolution"]
        self.assertEqual(config["document_paths"], original)
        self.assertTrue(config["configured"])
        self.assertEqual(config["fragment_verification"], "not_performed")
        self.assertEqual(config["config_sha256"], digest(web._json_bytes({
            "resolver_version": "0.1.0", "document_paths": original})))
        self.paths["long"] = "changed.md"
        config["document_paths"]["long"] = "mutated-response.md"
        direct = self.app._companion_configuration()
        direct["document_paths"]["short"] = "mutated-return.md"
        self.assertEqual(self.data()["companion_resolution"]["document_paths"], original)
        with self.assertRaises(TypeError):
            self.app._document_paths["long"] = "mutated-private-map.md"
        same = web.create_app(self.capture, document_paths=dict(reversed(list(original.items()))))
        changed = web.create_app(self.capture, document_paths=original | {"long": "different/record.md"})
        unconfigured = web.create_app(self.capture)
        self.assertEqual(self.data(app=same)["companion_resolution"], self.data()["companion_resolution"])
        for other in (changed, unconfigured):
            self.assertEqual(other.manifest_sha256, self.app.manifest_sha256)
            self.assertNotEqual(self.data(app=other)["companion_resolution"]["config_sha256"],
                                config["config_sha256"])
        self.assertIsNone(self.data(app=unconfigured)["companion_resolution"]["document_paths"])
        with ThreadPoolExecutor(max_workers=4) as executor:
            results = list(executor.map(lambda _: self.resolve("../details/record.md"), range(8)))
        results[0]["target"]["stage"] = "changed"
        self.assertTrue(all(row["target"]["stage"] == "long" for row in results[1:]))

    def test_capture_bytes_survive_source_mutation_deletion_and_zip_resolution(self):
        archive = self.root.parent / "edition.zip"
        bundle.export_bundle(self.capture, archive)
        zipped = web.create_app(archive, document_paths=self.paths)
        before = self.resolve("../details/record.md#anchor")
        (self.root / "papers/long.md").write_bytes(b"replacement source")
        shutil.rmtree(self.root)
        archive.unlink()
        with patch.object(bundle, "_read_regular", side_effect=AssertionError("unexpected filesystem read")):
            for app in (self.app, zipped):
                self.assertEqual(self.resolve("../details/record.md#anchor", app=app), before)
                self.assertEqual(self.resolve("../details/./record.md", app=app)["target"]["stage"], "long")
                for name, content in self.capture.files.items():
                    self.assertEqual(request(app, "/api/v1/documents/" + name)["body"], content)

    def test_etag_head_and_manifest_checks_apply_even_to_cached_resolution(self):
        route = "/api/v1/papers/resolve-link"
        query = {"paper": "short", "href": "../details/record.md", "manifest": self.app.manifest_sha256}
        first = request(self.app, route, query)
        self.assertEqual(first["status"], 200)
        head = request(self.app, route, query, method="HEAD")
        self.assertEqual(head["status"], 200)
        self.assertEqual(head["body"], b"")
        self.assertEqual(head["headers"]["ETag"], first["headers"]["ETag"])
        self.assertEqual(head["headers"]["Content-Length"], str(len(first["body"])))
        conditional = request(self.app, route, query, headers={"If-None-Match": first["headers"]["ETag"]})
        self.assertEqual((conditional["status"], conditional["body"]), (304, b""))
        mismatch = request(self.app, route, query | {"manifest": "0" * 64},
                           headers={"If-None-Match": first["headers"]["ETag"]})
        self.assertEqual(mismatch["status"], 409)
        self.assertEqual(json.loads(mismatch["body"])["error"]["code"], "edition_mismatch")
        other = web.create_app(self.capture, document_paths=self.paths | {"long": "different/record.md"})
        self.assertNotEqual(request(other, route, query)["headers"]["ETag"], first["headers"]["ETag"])

    def test_route_parameters_are_bounded_and_discovered(self):
        routes = self.data()["routes"]
        route = next(row for row in routes if row["href"].endswith("/papers/resolve-link"))
        self.assertEqual(route["parameters"], ["manifest", "paper", "href"])
        for query in ({}, {"paper": "short"}, {"href": "#a"}, {"paper": "other", "href": "#a"},
                      {"paper": "short", "href": ""}, {"paper": "short", "href": ["#a", "#b"]},
                      {"paper": "short", "href": "#a", "path": "extra"}):
            self.assertEqual(request(self.app, route["href"], query)["status"], 400)
        self.assertEqual(request(self.app, route["href"], {"paper": "short", "href": "a" * 9000})["status"], 414)

    def test_actual_http_resolution_does_not_redirect_or_modify_document(self):
        with local_server(self.app) as port:
            connection = http.client.HTTPConnection("127.0.0.1", port, timeout=5)
            self.addCleanup(connection.close)
            query = urlencode({"paper": "short", "href": "../details/record.md#never-verified"})
            connection.request("GET", "/api/v1/papers/resolve-link?" + query)
            response = connection.getresponse()
            self.assertEqual(response.status, 200)
            self.assertIsNone(response.getheader("Location"))
            result = json.loads(response.read())["data"]
            connection.request("GET", result["target"]["document_href"])
            response = connection.getresponse()
            self.assertEqual(response.status, 200)
            self.assertEqual(response.read(), self.capture.files["papers/long.md"])


if __name__ == "__main__":
    unittest.main()
