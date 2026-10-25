"""Read-only HTTP transport over one captured explanation edition.

Consumer owns mathematical navigation; this module owns transport and discovery.
It never fetches or opens referenced source files or receipts.
"""
from __future__ import annotations

import json
import re
from collections import Counter
from http import HTTPStatus
from pathlib import Path
from urllib.parse import parse_qs, urlencode, urlsplit
from wsgiref.simple_server import make_server

from .bundle import BUNDLE_FILES, STAGES, BundleCapture, load_bundle
from .consumer import project_corpus, project_graph, project_paper, query_corpus, query_papers
from .contracts import ContractError, digest, encoded

API_VERSION = "1.0"
API_ROOT = "/api/v1"
TABLES = ("nodes", "edges", "sources", "citations", "evidence")
FAMILIES = ("declarations", "arguments", "citations", "platform", "provenance")
MAX_QUERY_BYTES = 8192
MAX_RESPONSE_BYTES = 16 * 1024 * 1024
MAX_PAGE_SIZE = 200

# Discovery and the query-parameter allowlist share one owner.
ROUTES = {
    "": ("API capabilities and limits", ()),
    "/overview": ("Corpus, reading stages and typed relation counts", ()),
    "/corpus": ("Complete existing corpus projection", ()),
    "/records": ("Paged recorded entities", ("table", "kind", "status", "paper", "q", "offset", "limit")),
    "/record": ("Record, typed links and aligned paper passages", ("ref",)),
    "/relations": ("Paged links for a global or paper graph", ("family", "paper", "offset", "limit")),
    "/neighborhood": ("Typed traversal with explicit frontier", ("ref", "family", "paper", "direction", "depth", "budget")),
    "/connection": ("Explain one recorded connection within a bounded traversal", ("from", "to", "family", "paper", "direction", "depth", "budget")),
    "/graph": ("Scoped dependency view, components and condensation", ("view", "node", "scope", "direction", "assumptions")),
    "/papers": ("Independently authored reading accounts", ()),
    "/papers/query": ("Passage, section, text selection or node correspondence", ("paper", "passage", "section", "start", "end", "node", "relation")),
    "/compare": ("Shared and exclusive paper support", ("left", "right", "table", "offset", "limit")),
    "/search": ("Literal search of records, headings and passages", ("q", "table", "paper", "offset", "limit")),
}


class APIError(Exception):
    def __init__(self, status, code, message):
        self.status, self.code, self.message = status, code, message


class Parameters:
    def __init__(self, query, allowed):
        if len(query.encode("utf-8")) > MAX_QUERY_BYTES:
            raise APIError(414, "query_too_long", "Query exceeds the HTTP query-byte limit.")
        try:
            if re.search(r"%(?![0-9a-fA-F]{2})", query):
                raise ValueError("invalid escape")
            self.values = parse_qs(query, keep_blank_values=True, strict_parsing=True,
                                   encoding="utf-8", errors="strict", max_num_fields=128)
        except (ValueError, UnicodeError):
            raise APIError(400, "invalid_query", "Use a valid UTF-8 URL query.") from None
        if set(self.values) - set(allowed) - {"manifest"}:
            raise APIError(400, "unknown_parameter", "Query contains unsupported parameters.")
        if any(not value for values in self.values.values() for value in values):
            raise APIError(400, "empty_parameter", "Query values must be nonempty.")

    def one(self, name, default=None, *, required=False, choices=None):
        values = self.values.get(name, [])
        if len(values) > 1 or (required and not values):
            raise APIError(400, "invalid_parameter", f"Supply {name} exactly once.")
        value = values[0] if values else default
        if value is not None and choices is not None and value not in choices:
            raise APIError(400, "invalid_parameter", f"Unknown {name} value.")
        return value

    def many(self, name, *, choices=None):
        values = self.values.get(name)
        if values is not None and (len(values) != len(set(values)) or len(values) > 32
                                   or (choices is not None and not set(values) <= set(choices))):
            raise APIError(400, "invalid_parameter", f"Invalid {name} selections.")
        return values

    def integer(self, name, default, low, high):
        value = self.one(name)
        if value is None:
            return default
        if not re.fullmatch(r"[0-9]{1,9}", value) or not low <= int(value) <= high:
            raise APIError(400, "invalid_parameter", f"{name} must be an integer in {low}..{high}.")
        return int(value)


class WebApplication:
    """WSGI callable. Construct a new application to publish a new edition."""

    def __init__(self, bundle: Path | BundleCapture, *, allow_origin=None,
                 max_response_bytes=MAX_RESPONSE_BYTES):
        if allow_origin is not None:
            try:
                origin = urlsplit(allow_origin)
                valid_host = origin.hostname is not None and origin.port != 0
            except (ValueError, TypeError):
                raise ContractError("allow_origin must be one valid HTTP(S) origin") from None
            if (origin.scheme not in {"http", "https"} or not origin.netloc or origin.path
                    or origin.query or origin.fragment or origin.username or origin.password
                    or not valid_host
                    or any(ord(c) < 33 or ord(c) > 126 for c in allow_origin)):
                raise ContractError("allow_origin must be one exact HTTP(S) origin without a path")
        if type(max_response_bytes) is not int or max_response_bytes < 1024:
            raise ContractError("max_response_bytes must be an integer of at least 1024")
        self._capture = bundle if isinstance(bundle, BundleCapture) else BundleCapture(bundle)
        self._files = load_bundle(self._capture)
        self._corpus = project_corpus(self._capture)
        self._snapshot = self._corpus["snapshot"]
        self.manifest_sha256 = self._snapshot["manifest_sha256"]
        self.allow_origin, self.max_response_bytes = allow_origin, max_response_bytes
        self._records = {row["ref"]: (table, row) for table, rows in self._corpus["records"].items()
                         for row in rows}
        self._usage = {row["record_ref"]: row for row in self._corpus["record_usage"]}
        self._papers = {p["stage"]: p for p in self._corpus["papers"]}
        self._passages = {p["ref"]: (stage, p) for stage, view in self._papers.items()
                          for p in view["paper"]["passages"]}
        self._links = sorted(({"family": family, **link}
                              for family, links in self._corpus["relations"].items() for link in links),
                             key=lambda row: (row["family"], row["id"]))
        self._search = self._search_index()

    def _href(self, route, **query):
        return API_ROOT + route + "?" + urlencode({"manifest": self.manifest_sha256, **query}, doseq=True)

    def _paper_summary(self, stage):
        view = self._papers[stage]
        return {key: view[key] for key in ("stage", "state", "review_state", "paper_scope", "coverage")} | {
            "markdown_ref": view["bundle"]["markdown_ref"], "mapping_ref": view["bundle"]["mapping_ref"],
            "sections": len(view["paper"]["sections"]), "passages": len(view["paper"]["passages"]),
            "href": self._href(f"/papers/{stage}"),
            "document_href": self._href(f"/papers/{stage}/document"),
            "sections_href": self._href(f"/papers/{stage}/sections"),
            "passages_href": self._href(f"/papers/{stage}/passages"),
            "parts_href": self._href(f"/papers/{stage}/parts")}

    def _page(self, rows, params, route):
        offset = params.integer("offset", 0, 0, 999999999)
        limit = params.integer("limit", 50, 1, MAX_PAGE_SIZE)
        query = {key: values for key, values in params.values.items()
                 if key not in {"manifest", "offset", "limit"}}
        next_href = (self._href(route, **query, offset=offset + limit, limit=limit)
                     if offset + limit < len(rows) else None)
        return {"items": rows[offset:offset + limit], "total": len(rows),
                "offset": offset, "limit": limit, "next": next_href}

    def _paper_refs(self, stage):
        return {ref for refs in self._papers[stage]["graph"]["record_refs"].values() for ref in refs}

    def _aligned_passages(self, ref):
        rows = []
        for link in self._usage[ref]["direct_passages"]:
            stage, passage = self._passages[link["passage_ref"]]
            rows.append({**link, "text": passage["text"], "span": passage["content_span"],
                         "paper_href": self._href(f"/papers/{stage}"),
                         "query_href": self._href("/papers/query", paper=stage, passage=passage["anchor"])})
        return rows

    def _search_index(self):
        rows = []
        for ref, (table, row) in sorted(self._records.items()):
            record = row["record"]
            rows.append({"ref": ref, "table": table, "label": record.get("label", record.get("id", ref)),
                         "text": json.dumps(record, ensure_ascii=False, sort_keys=True),
                         "papers": sorted({p["stage"] for p in self._usage[ref]["paper_memberships"]}),
                         "href": self._href("/record", ref=ref)})
        for stage, view in self._papers.items():
            content = view["paper"]["text"].encode("utf-8")
            for table, items in (("passages", view["paper"]["passages"]),
                                 ("sections", view["paper"]["sections"])):
                for item in items:
                    span = item.get("content_span", item.get("span"))
                    text = (item.get("title", "") if table == "sections" else
                            content[span["start_byte"]:span["end_byte"]].decode("utf-8"))
                    rows.append({"ref": item["ref"], "table": table,
                                 "label": item.get("title", item.get("anchor", item["ref"])),
                                 "text": text, "papers": [stage], "span": span,
                                 "href": self._href("/papers/query", paper=stage,
                                                    **{"section" if table == "sections" else "passage":
                                                       item["ref"] if table == "sections" else item["anchor"]})})
        return sorted(rows, key=lambda row: (row["table"], row["ref"]))

    def _dispatch(self, route, p):
        if route == "":
            return {"routes": [{"href": API_ROOT + key, "description": value[0],
                                "parameters": ["manifest", *value[1]]} for key, value in ROUTES.items()],
                    "paper_routes": [self._paper_summary(s) for s in STAGES],
                    "documents": [{"name": name, "sha256": digest(self._files[name]),
                                   "href": self._href("/documents/" + name)} for name in BUNDLE_FILES],
                    "limits": {"query_bytes": MAX_QUERY_BYTES, "response_bytes": self.max_response_bytes,
                               "page_size": MAX_PAGE_SIZE, "depth": 8, "budget": 500},
                    "relation_semantics": self._corpus["relation_semantics"],
                    "semantic_certification": False}
        if route == "/overview":
            return {"graph": self._corpus["graph"], "coverage": self._corpus["coverage"],
                    "record_counts": self._corpus["coverage"]["record_counts"],
                    "node_status_counts": dict(sorted(Counter(row["record"]["status"]
                                                for row in self._corpus["records"]["nodes"]).items())),
                    "relation_counts": {family: len(rows) for family, rows in self._corpus["relations"].items()},
                    "papers": [self._paper_summary(s) for s in STAGES],
                    "reading_order_is_dependency_order": False}
        if route == "/corpus":
            return self._corpus
        if route == "/papers":
            return {"items": [self._paper_summary(s) for s in STAGES]}
        if route.startswith("/papers/") and route != "/papers/query":
            parts = route.split("/")
            if len(parts) == 4:
                key = {"sections": "sections", "passages": "passages", "parts": "document_parts"}[parts[3]]
                result = self._page(self._papers[parts[2]]["paper"][key], p, route)
                if key == "document_parts":
                    content = self._files[f"papers/{parts[2]}.md"]
                    result["items"] = [{**row, "text": content[row["span"]["start_byte"]:
                                                               row["span"]["end_byte"]].decode("utf-8")}
                                       for row in result["items"]]
                return result
            return project_paper(self._capture, parts[2])
        if route == "/records":
            table = p.one("table", choices=TABLES)
            kind, status = p.one("kind"), p.one("status")
            stage = p.one("paper", choices=STAGES)
            members = self._paper_refs(stage) if stage else None
            tokens = p.one("q", "").casefold().split()
            rows = [{"table": t, **row, "usage": self._usage[ref], "href": self._href("/record", ref=ref)}
                    for ref, (t, row) in sorted(self._records.items())
                    if (table is None or t == table) and (members is None or ref in members)
                    and (kind is None or row["record"].get("kind") == kind)
                    and (status is None or row["record"].get("status") == status)
                    and all(token in json.dumps(row["record"], ensure_ascii=False).casefold() for token in tokens)]
            return self._page(rows, p, route)
        if route == "/record":
            ref = p.one("ref", required=True)
            if ref not in self._records:
                raise APIError(404, "record_not_found", "Record reference is absent from this graph edition.")
            table, row = self._records[ref]
            lenses = ({
                "prerequisites": self._href("/graph", view="arguments", node=row["record"]["id"], assumptions="true"),
                "consumers": self._href("/graph", view="arguments", node=row["record"]["id"], direction="consumers", assumptions="true"),
                "direct_passages": self._href("/papers/query", node=row["record"]["id"], relation="direct"),
                "prerequisite_uses": self._href("/papers/query", node=row["record"]["id"], relation="prerequisites"),
            } if table == "nodes" else {})
            return {"table": table, **row, "usage": self._usage[ref],
                    "aligned_passages": self._aligned_passages(ref),
                    "lenses": lenses,
                    "relations": [link for link in self._links if ref in {link["from"], link["to"]}],
                    "neighborhood_href": self._href("/neighborhood", ref=ref)}
        if route == "/relations":
            families = p.many("family", choices=FAMILIES) or list(FAMILIES)
            stage = p.one("paper", choices=STAGES)
            members = self._paper_refs(stage) if stage else None
            rows = [link for link in self._links if link["family"] in families
                    and (members is None or {link["from"], link["to"]} <= members)]
            return self._page(rows, p, route)
        if route in {"/neighborhood", "/connection"}:
            source = p.one("from", required=True) if route == "/connection" else None
            target = p.one("to", required=True) if route == "/connection" else None
            if target is not None and target not in self._records:
                raise APIError(404, "record_not_found", "Target record is absent from this graph edition.")
            result = query_corpus(self._capture, record_refs=[source] if source else p.many("ref"),
                                families=p.many("family", choices=FAMILIES),
                                direction=p.one("direction", "both", choices=("both", "incoming", "outgoing")),
                                max_depth=p.integer("depth", 1, 0, 8), max_records=p.integer("budget", 100, 1, 500),
                                stage=p.one("paper", choices=STAGES))
            if route == "/neighborhood":
                return result
            witnesses = {row["record_ref"]: row for row in result["witnesses"]}
            path, cursor = [], target
            while cursor in witnesses:
                row = witnesses[cursor]
                path.append(row)
                if row["parent"] is None:
                    break
                cursor = row["parent"]["record_ref"]
            return {"from": source, "to": target,
                    "outcome": "reached" if path else "not_reached_within_query",
                    "witness_path": list(reversed(path)), "neighborhood": result,
                    "meaning": "One deterministic recorded traversal witness; no claim of logical entailment. A cutoff or paper restriction can hide a connection."}
        if route == "/graph":
            view = p.one("view", "arguments", choices=FAMILIES)
            roots = p.many("node")
            scope = p.one("scope", "focus", choices=("focus", "corpus"))
            if scope == "corpus":
                if roots is not None:
                    raise APIError(400, "invalid_scope", "Corpus scope cannot also select node roots.")
                roots = sorted(row["record"]["id"] for row in self._corpus["records"]["nodes"]
                               if view != "declarations" or row["record"]["kind"] in {"declaration", "assumption"})
                if not roots:
                    raise APIError(400, "empty_scope", "No recorded declarations or assumptions in this corpus.")
            return project_graph(self._files["graph.json"], view,
                                 roots, direction=p.one("direction", "prerequisites",
                                                                   choices=("prerequisites", "consumers")),
                                 include_assumptions=p.one("assumptions", "false", choices=("true", "false")) == "true")
        if route == "/papers/query":
            start = p.integer("start", None, 0, 999999999)
            end = p.integer("end", None, 1, 999999999)
            if (start is None) != (end is None):
                raise APIError(400, "invalid_range", "Supply both start and end UTF-8 byte offsets.")
            if start is not None and p.one("manifest") is None:
                raise APIError(400, "edition_required", "Text selections require an explicit manifest pin.")
            return query_papers(self._capture, stage=p.one("paper", choices=STAGES),
                                passages=p.many("passage"), section_refs=p.many("section"),
                                byte_ranges=[(start, end)] if start is not None else None,
                                node_ids=p.many("node"), relation=p.one("relation", "direct",
                                                                    choices=("direct", "prerequisites")),
                                expected_manifest_sha256=self.manifest_sha256)
        if route == "/compare":
            left, right = (p.one(side, required=True, choices=STAGES) for side in ("left", "right"))
            if left == right:
                raise APIError(400, "invalid_comparison", "Choose two different paper stages.")
            table = p.one("table", choices=TABLES)
            a, b = self._paper_refs(left), self._paper_refs(right)
            rows = [{"table": t, **row, "membership": "shared" if ref in a & b else left if ref in a else right,
                     "direct_passages": [link for link in self._usage[ref]["direct_passages"]
                                         if link["stage"] in {left, right}]}
                    for ref, (t, row) in sorted(self._records.items())
                    if ref in a | b and (table is None or t == table)]
            return self._page(rows, p, route) | {"left": left, "right": right,
                "meaning": "Recorded support membership and explicit mappings; an exclusive record is not asserted absent from the other prose, and shared membership is not a proof edge."}
        if route == "/search":
            query = p.one("q", required=True)
            tokens = query.casefold().split()
            if not tokens or len(tokens) > 16 or len(query) > 256:
                raise APIError(400, "invalid_search", "Use 1..16 literal tokens and at most 256 characters.")
            table = p.one("table", choices=(*TABLES, "sections", "passages"))
            stage = p.one("paper", choices=STAGES)
            rows = []
            for row in self._search:
                if ((table is None or row["table"] == table) and (stage is None or stage in row["papers"])
                        and all(token in row["text"].casefold() for token in tokens)):
                    rows.append({key: value for key, value in row.items() if key != "text"} |
                                {"excerpt": row["text"][:280], "excerpt_truncated": len(row["text"]) > 280})
            return self._page(rows, p, route) | {"matching": "literal_casefolded_AND", "ranking": "table_then_exact_ref"}
        raise APIError(404, "not_found", "Unknown API resource.")

    def __call__(self, environ, start_response):
        method = environ.get("REQUEST_METHOD", "GET")
        headers = [("X-Content-Type-Options", "nosniff"), ("X-Manifest-SHA256", self.manifest_sha256)]
        if self.allow_origin and environ.get("HTTP_ORIGIN") == self.allow_origin:
            headers += [("Access-Control-Allow-Origin", self.allow_origin),
                        ("Access-Control-Expose-Headers", "ETag, X-Manifest-SHA256")]
        if self.allow_origin:
            headers.append(("Vary", "Origin"))
        status, content_type = 200, "application/json; charset=utf-8"
        try:
            if method not in {"GET", "HEAD", "OPTIONS"}:
                raise APIError(405, "method_not_allowed", "Use GET or HEAD; this API is read-only.")
            path = environ.get("PATH_INFO", "")
            route = path[len(API_ROOT):] if path == API_ROOT or path.startswith(API_ROOT + "/") else None
            allowed = ROUTES.get(route, (None, None))[1]
            document = None
            if route is not None and route.startswith("/documents/"):
                document = route[len("/documents/"):]
                if document in BUNDLE_FILES:
                    allowed = ()
            elif route is not None and route.startswith("/papers/"):
                parts = route.split("/")
                if len(parts) in {3, 4} and parts[2] in STAGES:
                    if len(parts) == 3:
                        allowed = ()
                    elif parts[3] == "document":
                        document, allowed = f"papers/{parts[2]}.md", ()
                    elif parts[3] in {"sections", "passages", "parts"}:
                        allowed = ("offset", "limit")
            if allowed is None:
                raise APIError(404, "not_found", "Unknown API resource.")
            p = Parameters(environ.get("QUERY_STRING", ""), allowed)
            pin = p.one("manifest")
            if pin is not None and not re.fullmatch(r"[0-9a-f]{64}", pin):
                raise APIError(400, "invalid_manifest", "Manifest must be a lowercase SHA-256.")
            if pin is not None and pin != self.manifest_sha256:
                raise APIError(409, "edition_mismatch", "Requested edition is not the edition served by this application.")
            if method == "OPTIONS":
                start_response("204 No Content", headers + [("Allow", "GET, HEAD, OPTIONS"),
                                                            ("Access-Control-Allow-Methods", "GET, HEAD, OPTIONS")])
                return []
            if document is not None:
                body = self._files[document]
                content_type = "text/markdown; charset=utf-8" if document.endswith(".md") else content_type
                headers.append(("Content-Disposition", f'inline; filename="{document.rsplit("/", 1)[-1]}"'))
            else:
                body = encoded({"api_version": API_VERSION, "snapshot": self._snapshot,
                                "data": self._dispatch(route, p)})
            if len(body) > self.max_response_bytes:
                raise APIError(413, "response_too_large", "Response exceeds the configured limit; use paged records/relations or a narrower selection.")
            etag = '"' + digest(body) + '"'
            headers += [("ETag", etag), ("Cache-Control", "private, max-age=0, must-revalidate")]
            candidates = [value.strip().removeprefix("W/")
                          for value in environ.get("HTTP_IF_NONE_MATCH", "").split(",")]
            if etag in candidates or "*" in candidates:
                start_response("304 Not Modified", headers)
                return []
        except (APIError, ContractError) as exc:
            if isinstance(exc, ContractError):
                exc = APIError(400, "invalid_selection", str(exc))
            status = exc.status
            content_type = "application/json; charset=utf-8"
            headers = [(k, v) for k, v in headers if k != "Content-Disposition"]
            body = encoded({"api_version": API_VERSION, "snapshot": self._snapshot,
                            "error": {"code": exc.code, "message": exc.message}})
            headers.append(("Cache-Control", "no-store"))
            if status == 405:
                headers.append(("Allow", "GET, HEAD, OPTIONS"))
        except Exception:
            status = 500
            content_type = "application/json; charset=utf-8"
            headers = [(k, v) for k, v in headers if k != "Content-Disposition"]
            body = encoded({"api_version": API_VERSION, "snapshot": self._snapshot,
                            "error": {"code": "internal_error", "message": "Unable to complete this request."}})
            headers.append(("Cache-Control", "no-store"))
        start_response(f"{status} {HTTPStatus(status).phrase}",
                       headers + [("Content-Type", content_type), ("Content-Length", str(len(body)))])
        return [] if method == "HEAD" else [body]


def create_app(bundle: Path | BundleCapture, **options) -> WebApplication:
    """Create a WSGI callable for an assembled directory or ZIP bundle."""
    return WebApplication(bundle, **options)


def serve(bundle: Path, *, host="127.0.0.1", port=8000, allow_origin=None):
    """Local reference server; deploy the WSGI callable with a hosting server."""
    if not isinstance(host, str) or not host or type(port) is not int or not 0 <= port <= 65535:
        raise ContractError("host must be nonempty and port must be in 0..65535")
    app = create_app(bundle, allow_origin=allow_origin)
    with make_server(host, port, app) as server:
        print(json.dumps({"url": f"http://{host}:{server.server_port}{API_ROOT}",
                          "manifest_sha256": app.manifest_sha256}), flush=True)
        try:
            server.serve_forever()
        except KeyboardInterrupt:
            pass
    return {"stopped": True, "manifest_sha256": app.manifest_sha256}
