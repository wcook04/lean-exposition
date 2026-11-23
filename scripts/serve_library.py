#!/usr/bin/env python3
"""Serve a folder as GitHub Pages does, for local checks of the library.

A folder serves its index.html; a missing path is answered with status 404 and the site's one
404.html (ROOT/<site>/404.html), as Pages does: the library's 404.html loads the paper's own
shell for phrase and Lean addresses. Usage: serve_library.py ROOT [PORT]
"""
import argparse
import http.server
import json
from pathlib import Path
from urllib.parse import parse_qs, urlsplit

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("root", type=Path)
parser.add_argument("port", nargs="?", type=int, default=47311)
parser.add_argument("--proof-index", type=Path, help="serve a compiled proof index at /api/proof")
parser.add_argument("--proof-origin", help="allow this frontend origin to read the proof API")
parser.add_argument("--lean-source", type=Path, help="local Git checkout with the pinned RH Lean modules")
args = parser.parse_args()
ROOT = args.root.resolve()
PROOF = None
SOURCES = None
if args.lean_source and not args.proof_index:
    parser.error("--lean-source requires --proof-index")
if args.proof_index:
    from lean_exposition.proof_index import ProofIndex

    PROOF = ProofIndex(args.proof_index)
if args.lean_source:
    from lean_exposition.proof_sources import ProofSources

    try:
        reader = Path(__file__).resolve().parents[1] / "instances/riemann-hypothesis/reader.json"
        SOURCES = ProofSources(args.lean_source, ROOT / "paper", PROOF, reader_config=reader)
    except (OSError, ValueError, KeyError) as error:
        parser.error(str(error))


class Pages(http.server.SimpleHTTPRequestHandler):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, directory=str(ROOT), **kwargs)

    def do_GET(self):
        url = urlsplit(self.path)
        if PROOF is None or not url.path.startswith("/api/proof/"):
            return super().do_GET()
        params = parse_qs(url.query)
        def param(key, fallback=""):
            return params.get(key, [fallback])[0]

        route = url.path.removeprefix("/api/proof/")
        lean_route = route.startswith("lean/")
        if SOURCES and lean_route:
            pin = SOURCES.paper_manifest_sha256
            if param("manifest", pin) != pin:
                self.json_response(409, {"error": {"code": "edition_changed", "message": "The RH paper edition has changed."}})
                return
        try:
            limit = int(param("limit", "20"))
            offset = int(param("offset", "0"))
            if not 1 <= limit <= 50 or not 0 <= offset <= 5_000_000:
                raise ValueError("Invalid page bounds")
            if route == "manifest":
                value = {**PROOF.manifest, **({"lean_sources": SOURCES.metadata} if SOURCES else {})}
            elif route == "search":
                query = param("q").strip()
                if not 1 <= len(query) <= 256:
                    raise ValueError("Search needs 1 to 256 characters")
                value = PROOF.search(query, limit)
            elif route == "neighbourhood":
                name = param("name")
                if not 1 <= len(name) <= 1024:
                    raise ValueError("Invalid declaration name")
                value = PROOF.neighbourhood(name, offset, limit)
            elif route == "lean/modules" and SOURCES:
                value = SOURCES.modules()
            elif route == "lean/names" and SOURCES:
                value = SOURCES.names()
            elif route == "lean/module" and SOURCES:
                name = param("name")
                if not 1 <= len(name) <= 1024:
                    raise ValueError("Invalid Lean module name")
                value = SOURCES.module(name)
            else:
                raise KeyError(route)
            status = 200
        except ValueError as error:
            detail = {"code": "invalid_query", "message": str(error)} if lean_route else str(error)
            status, value = 400, {"error": detail}
        except KeyError:
            if lean_route and not SOURCES:
                detail = {"code": "lean_source_unavailable", "message": "This proof server has no Lean source catalogue."}
            elif route == "lean/module":
                detail = {"code": "lean_module_not_found", "message": "The module is outside the paper-linked catalogue."}
            else:
                detail = "Declaration or resource not found"
            status, value = 404, {"error": detail}
        self.json_response(status, value)

    def json_response(self, status, value):
        body = json.dumps(value, ensure_ascii=False).encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-cache")
        if args.proof_origin:
            self.send_header("Vary", "Origin")
            if self.headers.get("Origin") == args.proof_origin:
                self.send_header("Access-Control-Allow-Origin", args.proof_origin)
        self.end_headers()
        self.wfile.write(body)

    def send_head(self):
        path = Path(self.translate_path(self.path))
        if path.exists():
            return super().send_head()
        # As GitHub Pages serves a project site: one 404.html, at the site's root (ROOT/<site>/404.html).
        rel = path.relative_to(ROOT).parts if ROOT in path.parents else ()
        page = ROOT / rel[0] / "404.html" if rel else ROOT / "404.html"
        if page.is_file():
            body = page.read_bytes()
            self.send_response(404)
            self.send_header("Content-Type", "text/html; charset=utf-8")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            import io
            return io.BytesIO(body)
        return super().send_head()

    def log_message(self, *args):
        pass


http.server.ThreadingHTTPServer(("127.0.0.1", args.port), Pages).serve_forever()
