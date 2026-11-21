#!/usr/bin/env python3
"""Serve a folder as GitHub Pages does, for local checks of the library.

A folder serves its index.html; a missing path is answered with status 404 and the site's one
404.html (ROOT/<site>/404.html), as Pages does: the library's 404.html loads the paper's own
shell for phrase and Lean addresses. Usage: serve_library.py ROOT [PORT]
"""
import http.server
import sys
from pathlib import Path

ROOT = Path(sys.argv[1]).resolve()
PORT = int(sys.argv[2]) if len(sys.argv) > 2 else 47311


class Pages(http.server.SimpleHTTPRequestHandler):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, directory=str(ROOT), **kwargs)

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


http.server.ThreadingHTTPServer(("127.0.0.1", PORT), Pages).serve_forever()
