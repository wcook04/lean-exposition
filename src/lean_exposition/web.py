"""Read-only HTTP transport over one captured explanation edition.

Consumer owns mathematical navigation; this module owns transport and discovery.
It never fetches or opens referenced source files or receipts.
"""
from __future__ import annotations

import json
import re
from bisect import bisect_left, bisect_right
from collections import Counter, OrderedDict
from http import HTTPStatus
from pathlib import Path
from threading import Lock
from urllib.parse import parse_qs, urlencode, urlsplit
from wsgiref.simple_server import make_server

from .bundle import BUNDLE_FILES, STAGES, BundleCapture, load_bundle
from .consumer import ConsumerSession
from .contracts import ContractError, digest

API_VERSION = "1.2"
API_ROOT = "/api/v1"
TABLES = ("nodes", "edges", "sources", "citations", "evidence")
FAMILIES = ("declarations", "arguments", "citations", "platform", "provenance")
MAX_QUERY_BYTES = 8192
MAX_RESPONSE_BYTES = 16 * 1024 * 1024
MAX_PAGE_SIZE = 200
DEFAULT_CACHE_BYTES = 32 * 1024 * 1024


def _json_bytes(value):
    """Transport encoding; bundle/source encoding and hashes remain untouched."""
    return json.dumps(value, ensure_ascii=False, sort_keys=True,
                      separators=(",", ":"), allow_nan=False).encode("utf-8")


class _ResponseCache:
    """Bounded LRU of immutable bytes; fixed lock stripes collapse duplicate builds."""

    def __init__(self, max_bytes, max_entries):
        self.max_bytes, self.max_entries = max_bytes, max_entries
        self._entries, self._bytes = OrderedDict(), 0
        self._lock = Lock()
        self._builders = tuple(Lock() for _ in range(16))

    def _get(self, key):
        with self._lock:
            value = self._entries.get(key)
            if value is not None:
                self._entries.move_to_end(key)
            return value

    def get_or_build(self, key, build):
        if not self.max_bytes or not self.max_entries:
            return build()
        cached = self._get(key)
        if cached is not None:
            return cached
        with self._builders[hash(key) % len(self._builders)]:
            cached = self._get(key)
            if cached is not None:
                return cached
            value = build()
            size = len(value[0])
            if size <= self.max_bytes:
                with self._lock:
                    while self._entries and (self._bytes + size > self.max_bytes
                                             or len(self._entries) >= self.max_entries):
                        _, evicted = self._entries.popitem(last=False)
                        self._bytes -= len(evicted[0])
                    self._entries[key] = value
                    self._bytes += size
            return value

# Discovery and the query-parameter allowlist share one owner.
ROUTES = {
    "": ("API capabilities and limits", ()),
    "/overview": ("Corpus, reading stages and typed relation counts", ()),
    "/corpus": ("Complete existing corpus projection", ()),
    "/records": ("Paged recorded entities", ("table", "kind", "status", "paper", "q", "ref", "representation", "offset", "limit")),
    "/facets": ("Available record filters and counts in the chosen paper scope", ("paper",)),
    "/record": ("Record, typed links and aligned paper passages", ("ref",)),
    "/relations": ("Paged links for a global or paper graph", ("family", "paper", "offset", "limit")),
    "/neighborhood": ("Typed traversal with explicit frontier", ("ref", "family", "paper", "direction", "depth", "budget")),
    "/connection": ("Explain one recorded connection within a bounded traversal", ("from", "to", "family", "paper", "direction", "depth", "budget")),
    "/graph": ("Scoped dependency view, components and condensation", ("view", "node", "scope", "direction", "assumptions", "representation")),
    "/papers": ("Independently authored reading accounts", ()),
    "/papers/query": ("Passage, section, text selection or node correspondence", ("paper", "passage", "section", "start", "end", "node", "relation", "representation")),
    "/papers/reading": ("Authored reading routes and shared-claim alternatives for a passage or section", ("paper", "passage", "section", "start", "end", "target", "offset", "limit")),
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
                 max_response_bytes=MAX_RESPONSE_BYTES, cache_bytes=DEFAULT_CACHE_BYTES,
                 cache_entries=128):
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
        if any(type(value) is not int or value < 0 for value in (cache_bytes, cache_entries)):
            raise ContractError("cache_bytes and cache_entries must be nonnegative integers")
        self._responses = _ResponseCache(cache_bytes, cache_entries)
        self._capture = bundle if isinstance(bundle, BundleCapture) else BundleCapture(bundle)
        self._files = load_bundle(self._capture)
        self._reader = ConsumerSession(self._capture)
        self._corpus = self._reader.project_corpus()
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
        self._memberships = {stage: frozenset(ref for refs in view["graph"]["record_refs"].values()
                                             for ref in refs) for stage, view in self._papers.items()}
        self._adjacent = {ref: [] for ref in self._records}
        for link in self._links:
            self._adjacent[link["from"]].append(link)
            if link["to"] != link["from"]:
                self._adjacent[link["to"]].append(link)
        self._search = self._search_index()
        self._folded = {row["ref"]: row["text"].casefold() for row in self._search}
        self._summaries = {ref: self._record_summary(ref) for ref in self._records}

    def _href(self, route, **query):
        return API_ROOT + route + "?" + urlencode({"manifest": self.manifest_sha256, **query}, doseq=True)

    def _paper_summary(self, stage):
        view = self._papers[stage]
        return {key: view[key] for key in ("stage", "state", "review_state", "paper_scope", "coverage")} | {
            "markdown_ref": view["bundle"]["markdown_ref"], "mapping_ref": view["bundle"]["mapping_ref"],
            "sections": len(view["paper"]["sections"]), "passages": len(view["paper"]["passages"]),
            "href": self._href(f"/papers/{stage}"),
            "structure_href": self._href(f"/papers/{stage}/structure"),
            "reading_href": self._href("/papers/reading", paper=stage),
            "document_href": self._href(f"/papers/{stage}/document"),
            "sections_href": self._href(f"/papers/{stage}/sections"),
            "passages_href": self._href(f"/papers/{stage}/passages"),
            "parts_href": self._href(f"/papers/{stage}/parts")}

    def _paper_structure(self, stage):
        view = self._papers[stage]
        paper = view["paper"]
        links = {key: paper[key] for key in ("reading_order", "outline_links", "section_passage_links")}
        kinds = {link["kind"] for rows in links.values() for link in rows}
        kinds.update(link["kind"] for link in view["correspondence_links"])
        return {"representation": "document_structure", "representation_version": "0.1.0",
                **{key: view[key] for key in ("paper_view_version", "stage", "state", "review_state",
                                            "paper_scope", "bundle", "coverage", "semantic_certification")},
                "paper": {**{key: paper[key] for key in ("path", "byte_length", "line_count", "sections", "document_parts")},
                          "passages": [{key: value for key, value in row.items() if key not in {"text", "rationale"}}
                                       for row in paper["passages"]],
                          "unmapped_segments": [{key: value for key, value in row.items() if key != "text"}
                                                for row in paper["unmapped_segments"]], **links},
                "correspondence_links": view["correspondence_links"],
                **{key: view[key] for key in ("reading_view_version", "reading_links") if key in view},
                "support_record_refs": view["graph"]["record_refs"],
                "relation_semantics": {kind: view["relation_semantics"][kind] for kind in sorted(kinds)},
                "resources": {**{key: value for key, value in self._paper_summary(stage).items()
                                  if key.endswith("_href") or key == "href"},
                              "query_href": self._href("/papers/query", paper=stage, representation="matches"),
                              "records_href": self._href("/records"),
                              "record_href": self._href("/record")},
                "meaning": "Document structure and authored passage correspondences. Reading order, containment and text overlap do not assert mathematical dependencies. Source text and support record bodies are fetched separately."}

    def _page(self, rows, params, route):
        offset = params.integer("offset", 0, 0, 999999999)
        limit = params.integer("limit", 50, 1, MAX_PAGE_SIZE)
        return self._page_result(rows[offset:offset + limit], len(rows), offset, limit, params, route)

    def _page_result(self, items, total, offset, limit, params, route):
        query = {key: values for key, values in params.values.items()
                 if key not in {"manifest", "offset", "limit"}}
        next_href = (self._href(route, **query, offset=offset + limit, limit=limit)
                     if offset + limit < total else None)
        return {"items": items, "total": total,
                "offset": offset, "limit": limit, "next": next_href}

    def _paper_refs(self, stage):
        return self._memberships[stage]

    def _paper_selectors(self, params, *, require_stage=False):
        start = params.integer("start", None, 0, 999999999)
        end = params.integer("end", None, 1, 999999999)
        if (start is None) != (end is None):
            raise APIError(400, "invalid_range", "Supply both start and end UTF-8 byte offsets.")
        if start is not None and params.one("manifest") is None:
            raise APIError(400, "edition_required", "Text selections require an explicit manifest pin.")
        return {"stage": params.one("paper", required=require_stage, choices=STAGES),
                "passages": params.many("passage"), "section_refs": params.many("section"),
                "byte_ranges": [(start, end)] if start is not None else None,
                "expected_manifest_sha256": self.manifest_sha256}

    def _record_summary(self, ref):
        table, row = self._records[ref]
        record, usage = row["record"], self._usage[ref]
        papers = [{"stage": member["stage"], "roles": member["roles"],
                   "direct_passage_count": len({p["passage_ref"] for p in usage["direct_passages"]
                                                if p["stage"] == member["stage"]})}
                  for member in usage["paper_memberships"]]
        return {"ref": ref, "table": table,
                **{key: record[key] for key in ("id", "kind", "status") if key in record},
                "label": record.get("label", record.get("title", record.get("id", ref))),
                "papers": papers, "href": self._href("/record", ref=ref)}

    def _map_view(self, view):
        # Preserve selected records, typed links, application bindings and scope;
        # replace only record bodies. Scope and detail URLs are shared rather
        # than repeated for every record in a graph with hundreds of records.
        return {**view, "representation": "map", "records": {
            table: [{**{key: value for key, value in self._summaries[row["ref"]].items()
                        if key in {"ref", "id", "label", "kind", "status"}},
                     **({"relevant": row["relevant"]} if "relevant" in row else {})} for row in rows]
            for table, rows in view["records"].items()},
            "records_href": self._href("/records"),
            "record_detail": "Map records omit bodies and paper memberships; append repeated ref parameters to records_href for a batch of exact records, or use /record for evidence and passage mappings."}

    def _search_result(self, row, tokens):
        text, folded = row["text"], self._folded[row["ref"]]
        boundaries = [0]
        for character in text:
            boundaries.append(boundaries[-1] + len(character.casefold()))
        matches = []
        for token in tokens:
            start = folded.index(token)
            matches.append({"term": token, "start_character": bisect_right(boundaries, start) - 1,
                            "end_character": bisect_left(boundaries, start + len(token))})
        start = max(0, min(m["start_character"] for m in matches) - 80)
        start = min(start, max(0, len(text) - 280))
        return {key: value for key, value in row.items() if key != "text"} | {
            "excerpt": text[start:start + 280], "excerpt_truncated": len(text) > 280,
            "excerpt_start_character": start, "matches": matches,
            "match_coordinates": "Unicode code-point offsets in indexed text, not UTF-8 manuscript bytes"}

    def _aligned_passages(self, ref):
        rows = []
        for link in self._usage[ref]["direct_passages"]:
            stage, passage = self._passages[link["passage_ref"]]
            rows.append({**link, "text": passage["text"], "span": passage["content_span"],
                         "paper_href": self._href(f"/papers/{stage}"),
                         "reading_href": self._href("/papers/reading", paper=stage, passage=passage["anchor"]),
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
                               "page_size": MAX_PAGE_SIZE, "depth": 8, "budget": 500,
                               "response_cache_bytes": self._responses.max_bytes,
                               "response_cache_entries": self._responses.max_entries},
                    "representations": {"records": ["full", "summary"], "graph": ["full", "map"],
                                        "paper_query": ["full", "matches"]},
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
        if route.startswith("/papers/") and route not in {"/papers/query", "/papers/reading"}:
            parts = route.split("/")
            if len(parts) == 4:
                if parts[3] == "structure":
                    return self._paper_structure(parts[2])
                key = {"sections": "sections", "passages": "passages", "parts": "document_parts"}[parts[3]]
                result = self._page(self._papers[parts[2]]["paper"][key], p, route)
                if key == "document_parts":
                    content = self._files[f"papers/{parts[2]}.md"]
                    result["items"] = [{**row, "text": content[row["span"]["start_byte"]:
                                                               row["span"]["end_byte"]].decode("utf-8")}
                                       for row in result["items"]]
                return result
            return self._reader.project_paper(parts[2])
        if route == "/records":
            table = p.one("table", choices=TABLES)
            kind, status = p.one("kind"), p.one("status")
            stage = p.one("paper", choices=STAGES)
            members = self._paper_refs(stage) if stage else None
            tokens = p.one("q", "").casefold().split()
            representation = p.one("representation", "full", choices=("full", "summary"))
            requested = p.many("ref")
            if requested is not None and not set(requested) <= self._records.keys():
                raise APIError(404, "record_not_found", "A record reference is absent from this graph edition.")
            selected = set(requested) if requested is not None else None
            refs = [ref
                    for ref, (t, row) in sorted(self._records.items())
                    if (table is None or t == table) and (members is None or ref in members)
                    and (selected is None or ref in selected)
                    and (kind is None or row["record"].get("kind") == kind)
                    and (status is None or row["record"].get("status") == status)
                    and all(token in self._folded[ref] for token in tokens)]
            page = self._page(refs, p, route)
            if representation == "summary":
                page["items"] = [self._summaries[ref] for ref in page["items"]]
                page["representation"] = "summary"
            else:
                page["items"] = [{"table": self._records[ref][0], **self._records[ref][1],
                                  "usage": self._usage[ref], "href": self._href("/record", ref=ref)}
                                 for ref in page["items"]]
            return page
        if route == "/facets":
            stage = p.one("paper", choices=STAGES)
            members = self._paper_refs(stage) if stage else self._records.keys()
            tables = []
            for table in TABLES:
                records = [row["record"] for ref, (t, row) in self._records.items()
                           if t == table and ref in members]
                tables.append({"table": table, "count": len(records),
                               **{key: dict(sorted(Counter(r[key] for r in records if key in r).items()))
                                  for key in ("kind", "status")}})
            return {"paper": stage, "tables": tables,
                    "meaning": "Counts of recorded entities in the corpus or selected paper support, not mathematical importance or complete explanation coverage."}
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
                    "relations": self._adjacent[ref],
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
            result = self._reader.query_corpus(record_refs=[source] if source else p.many("ref"),
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
            representation = p.one("representation", "full", choices=("full", "map"))
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
            result = self._reader.project_graph(view,
                                 roots, direction=p.one("direction", "prerequisites",
                                                                   choices=("prerequisites", "consumers")),
                                 include_assumptions=p.one("assumptions", "false", choices=("true", "false")) == "true")
            return self._map_view(result) if representation == "map" else result
        if route == "/papers/query":
            representation = p.one("representation", "full", choices=("full", "matches"))
            return self._reader.query_papers(**self._paper_selectors(p),
                                node_ids=p.many("node"), relation=p.one("relation", "direct",
                                                                    choices=("direct", "prerequisites")),
                                include_views=representation == "full")
        if route == "/papers/reading":
            offset = p.integer("offset", 0, 0, 999999999)
            limit = p.integer("limit", 50, 1, MAX_PAGE_SIZE)
            result = self._reader.query_reading(**self._paper_selectors(p, require_stage=True),
                                               target_stage=p.one("target", choices=STAGES),
                                               offset=offset, limit=limit)
            pagination = result.pop("pagination")
            page = self._page_result(result.pop("links"), pagination["total"], offset, limit, p, route)
            result["passage_cards"] = [card | {
                "query_href": self._href("/papers/query", paper=card["stage"], passage=card["anchor"], representation="matches"),
                "reading_href": self._href("/papers/reading", paper=card["stage"], passage=card["anchor"])}
                for card in result["passage_cards"]]
            return result | page
        if route == "/compare":
            left, right = (p.one(side, required=True, choices=STAGES) for side in ("left", "right"))
            if left == right:
                raise APIError(400, "invalid_comparison", "Choose two different paper stages.")
            table = p.one("table", choices=TABLES)
            a, b = self._paper_refs(left), self._paper_refs(right)
            shared, combined = a & b, a | b
            refs = [ref for ref, (t, _) in sorted(self._records.items())
                    if ref in combined and (table is None or t == table)]
            page = self._page(refs, p, route)
            page["items"] = [{"table": self._records[ref][0], **self._records[ref][1],
                              "membership": "shared" if ref in shared else left if ref in a else right,
                              "direct_passages": [link for link in self._usage[ref]["direct_passages"]
                                                  if link["stage"] in {left, right}]}
                             for ref in page["items"]]
            return page | {"left": left, "right": right,
                "meaning": "Recorded support membership and explicit mappings; an exclusive record is not asserted absent from the other prose, and shared membership is not a proof edge."}
        if route == "/search":
            query = p.one("q", required=True)
            tokens = query.casefold().split()
            if not tokens or len(tokens) > 16 or len(query) > 256:
                raise APIError(400, "invalid_search", "Use 1..16 literal tokens and at most 256 characters.")
            table = p.one("table", choices=(*TABLES, "sections", "passages"))
            stage = p.one("paper", choices=STAGES)
            rows = [row for row in self._search
                    if (table is None or row["table"] == table) and (stage is None or stage in row["papers"])
                    and all(token in self._folded[row["ref"]] for token in tokens)]
            page = self._page(rows, p, route)
            page["items"] = [self._search_result(row, tokens) for row in page["items"]]
            return page | {"matching": "literal_casefolded_AND", "ranking": "table_then_exact_ref"}
        raise APIError(404, "not_found", "Unknown API resource.")

    def _representation(self, route, params, document):
        content_type, disposition = "application/json; charset=utf-8", None
        if document is not None:
            body = self._files[document]
            if document.endswith(".md"):
                content_type = "text/markdown; charset=utf-8"
            disposition = f'inline; filename="{document.rsplit("/", 1)[-1]}"'
        else:
            body = _json_bytes({"api_version": API_VERSION, "snapshot": self._snapshot,
                                "data": self._dispatch(route, params)})
        if len(body) > self.max_response_bytes:
            raise APIError(413, "response_too_large", "Response exceeds the configured limit; use paged records/relations or a narrower selection.")
        return body, content_type, disposition, '"' + digest(body) + '"'

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
                    elif parts[3] == "structure":
                        allowed = ()
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
            # Parameter order is immaterial; repeated selector order can be
            # meaningful in consumer output and stays in the key. The manifest
            # parameter is retained: a byte selection requires its presence.
            key = (route, tuple((name, tuple(values)) for name, values in sorted(p.values.items())))
            body, content_type, disposition, etag = self._responses.get_or_build(
                key, lambda: self._representation(route, p, document))
            if disposition:
                headers.append(("Content-Disposition", disposition))
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
            body = _json_bytes({"api_version": API_VERSION, "snapshot": self._snapshot,
                            "error": {"code": exc.code, "message": exc.message}})
            headers.append(("Cache-Control", "no-store"))
            if status == 405:
                headers.append(("Allow", "GET, HEAD, OPTIONS"))
        except Exception:
            status = 500
            content_type = "application/json; charset=utf-8"
            headers = [(k, v) for k, v in headers if k != "Content-Disposition"]
            body = _json_bytes({"api_version": API_VERSION, "snapshot": self._snapshot,
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
