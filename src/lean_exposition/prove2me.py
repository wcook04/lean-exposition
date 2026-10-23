"""Read-only, public-metadata intake from the documented Prove2Me API.

This adapter never downloads proof bodies, submits content, or treats a platform
label as local Lean verification. Raw API/authentication responses stay in memory.
"""
from __future__ import annotations

import os
import re
import time
from collections import Counter, deque
from datetime import datetime, timezone
from pathlib import Path
from urllib.error import HTTPError, URLError
from urllib.parse import urlsplit
from urllib.request import HTTPRedirectHandler, Request, build_opener
from uuid import UUID

from .contracts import ContractError, decode_json, digest, encoded, validate_graph

API_BASE = "https://prove2.me/api/v1"
REVIEWED_VERSION = "0.13.2"
MAX_RESPONSE_BYTES = 2_000_000
MAX_TOTAL_BYTES = 20_000_000


class Prove2MeError(ContractError):
    """A safe-to-display intake failure, without response bodies or credentials."""


class _Unavailable(Prove2MeError):
    pass


class _NoRedirect(HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        return None


def _open(request, timeout):
    return build_opener(_NoRedirect()).open(request, timeout=timeout)


def _uuid(value):
    if not isinstance(value, str):
        raise Prove2MeError("expected a canonical platform UUID")
    try:
        canonical = str(UUID(value))
    except ValueError:
        raise Prove2MeError("expected a canonical platform UUID") from None
    if canonical != value:
        raise Prove2MeError("expected a canonical platform UUID")
    return value


def theorem_id(url: str) -> str:
    """Accept only a canonical public theorem page, never an arbitrary API URL."""
    parsed = urlsplit(url)
    parts = parsed.path.strip("/").split("/")
    if (parsed.scheme != "https" or parsed.netloc != "prove2.me" or parsed.query
            or parsed.fragment or len(parts) != 2 or parts[0] != "theorems"
            or any(c.isspace() for c in url)):
        raise Prove2MeError("expected https://prove2.me/theorems/UUID")
    return _uuid(parts[1])


def _reference(value):
    """A public record's source link is a reference, never a download instruction."""
    if not isinstance(value, str) or len(value) > 2000 or any(c.isspace() for c in value):
        return None
    try:
        url = urlsplit(value)
        if (url.scheme == "https" and url.hostname and not url.username
                and not url.password and not url.query and not url.fragment):
            return value
    except ValueError:
        pass
    return None


class Prove2MeClient:
    """Fixed origin, bounded GETs, and the sole POST: existing-key authentication."""

    def __init__(self, credentials: Path | None = None, *, timeout=30.0,
                 max_requests=404, opener=None):
        if not 0 < timeout <= 60:
            raise Prove2MeError("timeout must be between 0 and 60 seconds")
        self.timeout = timeout
        self.max_requests = max_requests
        self.opener = opener or _open
        self.requests = self.total_bytes = 0
        self.credentials = credentials
        self.token = None
        self.expires_at = 0.0

    def _read(self, request):
        if self.requests >= self.max_requests:
            raise Prove2MeError("API request budget exceeded")
        self.requests += 1
        try:
            with self.opener(request, self.timeout) as response:
                if response.status != 200 or response.geturl() != request.full_url:
                    raise Prove2MeError("unexpected API status or redirect")
                raw = response.read(MAX_RESPONSE_BYTES + 1)
        except HTTPError as exc:
            if exc.code in {403, 404}:
                raise _Unavailable("platform record is not publicly available") from None
            raise Prove2MeError(f"Prove2Me returned HTTP {exc.code}") from None
        except (URLError, OSError, ValueError):
            raise Prove2MeError("Prove2Me transport failed") from None
        self.total_bytes += len(raw)
        if len(raw) > MAX_RESPONSE_BYTES or self.total_bytes > MAX_TOTAL_BYTES:
            raise Prove2MeError("API response byte budget exceeded")
        try:
            value = decode_json(raw)
        except (ValueError, UnicodeError):
            raise Prove2MeError("Prove2Me returned malformed JSON") from None
        if not isinstance(value, dict):
            raise Prove2MeError("Prove2Me returned a non-object response")
        return value, {"response_sha256": digest(raw), "observed_at":
                       datetime.now(timezone.utc).isoformat().replace("+00:00", "Z")}

    def _authenticate(self):
        if self.token is not None and self.expires_at > time.time() + 60:
            return
        key = os.environ.get("PROVE2ME_API_KEY")
        if self.credentials is not None:
            try:
                path = Path(self.credentials)
                if path.is_symlink() or not path.is_file() or path.stat().st_mode & 0o077:
                    raise Prove2MeError("credential file must be a private regular file")
                if any((parent / ".git").exists() for parent in path.resolve().parents):
                    raise Prove2MeError("credential file must stay outside Git repositories")
                with path.open("rb") as stream:
                    raw = stream.read(16_385)
                if len(raw) > 16_384:
                    raise Prove2MeError("credential file exceeds size limit")
                credentials = decode_json(raw)
                key = credentials.get("api_key") if isinstance(credentials, dict) else None
            except (OSError, ValueError, UnicodeError):
                raise Prove2MeError("could not read an API key from credential file") from None
        if not isinstance(key, str) or not re.fullmatch(r"p2m_[A-Za-z0-9_.-]{1,1024}", key):
            raise Prove2MeError("provide an existing API key in PROVE2ME_API_KEY or --credentials")
        request = Request(API_BASE + "/agent/refresh", data=encoded({"api_key": key}),
                          headers={"Content-Type": "application/json", "Accept": "application/json"},
                          method="POST")
        auth, _ = self._read(request)
        if auth.get("version") != REVIEWED_VERSION:
            raise Prove2MeError("platform version changed; review current API documentation before intake")
        token, expiry = auth.get("access_token"), auth.get("expires_at")
        if (not isinstance(token, str) or not token or len(token) > 8192
                or any(c.isspace() for c in token) or not isinstance(expiry, (int, float))
                or expiry <= time.time() + 60):
            raise Prove2MeError("authentication returned unusable token metadata")
        self.token, self.expires_at = token, expiry

    def get(self, route):
        # The allowlist is deliberately small: no generic arbitrary-URL fetcher.
        pattern = r"/(?:theorems|definitions)/[0-9a-f-]{36}(?:/decompositions)?"
        if route != "/environments" and re.fullmatch(pattern, route) is None:
            raise Prove2MeError("unsupported read-only API route")
        self._authenticate()
        return self._read(Request(API_BASE + route, method="GET", headers={
            "Accept": "application/json", "Authorization": "Bearer " + self.token}))


def _public_entity(value, entity, identity):
    if value.get("visibility") != "public":
        raise _Unavailable("record does not explicitly declare public visibility")
    if value.get(entity + "_id") != identity:
        raise Prove2MeError("platform entity identity mismatch")
    name = value.get(entity + "_name")
    if not isinstance(name, str) or not 0 < len(name) <= 1000 or any(ord(c) < 32 for c in name):
        raise Prove2MeError("invalid platform declaration name")
    status = value.get("status") if entity == "theorem" else "not_reported"
    if entity == "theorem" and status not in {"Open", "Proved", "Disproved"}:
        raise Prove2MeError("unrecognized platform theorem status")
    rev = value.get("mathlib_rev")
    if not isinstance(rev, str) or re.fullmatch(r"[0-9a-f]{40}", rev) is None:
        raise Prove2MeError("platform record has no full Mathlib revision")
    result = {"id": identity, "entity": entity, "name": name, "status": status,
              "visibility": "public", "mathlib_rev": rev,
              "deprecated": value.get("deprecated_at") is not None}
    reference = _reference(value.get("source"))
    if reference:
        result["source_reference"] = reference
    return result


def collect_prove2me(url: str, client: Prove2MeClient, *, max_nodes=100, max_depth=10):
    """Collect in memory before writing; return a graph and filtered public bytes.

    The union of alternative decomposition groups is navigation evidence, not a
    conjunction of obligations. Unconfirmed children are counted but never named.
    """
    root = theorem_id(url)
    if type(max_nodes) is not int or not 1 <= max_nodes <= 200:
        raise Prove2MeError("max_nodes must be between 1 and 200")
    if type(max_depth) is not int or not 0 <= max_depth <= 10:
        raise Prove2MeError("max_depth must be between 0 and 10")
    entities, decompositions, omitted = {}, {}, Counter()
    pending, attempted = deque([("theorem", root, 0)]), set()
    while pending:
        entity, identity, depth = pending.popleft()
        key = (entity, identity)
        if key in attempted:
            continue
        attempted.add(key)
        if len(attempted) > max_nodes:
            omitted["node_limit"] += 1
            continue
        route = f"/{entity}s/{identity}"
        try:
            value, provenance = client.get(route)
            record = _public_entity(value, entity, identity)
        except _Unavailable:
            if identity == root:
                raise Prove2MeError("selected theorem must be explicitly public and available") from None
            omitted["non_public_or_unavailable"] += 1
            continue
        entities[key] = (record, provenance)
        if entity == "definition":
            omitted["definition_dependencies_not_expanded"] += 1
            continue
        if depth >= max_depth:
            omitted["depth_limit"] += 1
            continue
        try:
            value, provenance = client.get(route + "/decompositions")
        except _Unavailable:
            omitted["decomposition_unavailable"] += 1
            continue
        rows = value.get("decompositions")
        if not isinstance(rows, list) or len(rows) > 1000:
            raise Prove2MeError("invalid or excessive decomposition groups")
        groups = []
        for row in rows:
            if not isinstance(row, dict) or not isinstance(row.get("children"), list):
                raise Prove2MeError("invalid decomposition group")
            if len(row["children"]) > 1000:
                raise Prove2MeError("excessive decomposition children")
            submission = row.get("submission_id")
            if submission is not None:
                _uuid(submission)
            children = []
            for child in row["children"]:
                if not isinstance(child, dict):
                    raise Prove2MeError("invalid decomposition child")
                kinds = [kind for kind in ("theorem", "definition") if child.get(kind + "_id") is not None]
                if len(kinds) != 1:
                    raise Prove2MeError("ambiguous decomposition child")
                kind = kinds[0]
                child_id = _uuid(child[kind + "_id"])
                children.append((kind, child_id))
                pending.append((kind, child_id, depth + 1))
            groups.append({"submission_id": submission, "children": children,
                           "deprecated": row.get("deprecated_at") is not None})
        decompositions[key] = (groups, provenance)

    # Only the matching environment facts survive; no unrelated listing is saved.
    env_value, env_provenance = client.get("/environments")
    env_rows = env_value.get("environments")
    if not isinstance(env_rows, list):
        raise Prove2MeError("invalid environment listing")
    revisions = {item[0]["mathlib_rev"] for item in entities.values()}
    environments = []
    for rev in sorted(revisions):
        matches = [r for r in env_rows if isinstance(r, dict) and r.get("mathlib_rev") == rev]
        if len(matches) != 1 or not isinstance(matches[0].get("toolchain"), str):
            raise Prove2MeError("platform environment missing or ambiguous")
        toolchain = matches[0]["toolchain"]
        if re.fullmatch(r"leanprover/lean4:v[0-9.]+(?:-[A-Za-z0-9.]+)?", toolchain) is None:
            raise Prove2MeError("unrecognized platform toolchain")
        environments.append({"mathlib_rev": rev, "toolchain": toolchain})

    graph = {"schema_version": "1.0", "id": "prove2me:" + root,
             "title": entities[("theorem", root)][0]["name"],
             "selected_goals": ["prove2me:theorem:" + root], "sources": [],
             "citations": [], "nodes": [], "edges": [], "evidence": [],
             "extraction_status": "not_run",
             "scope": "Partial public platform metadata; no Lean extraction, proof bodies, or local replay.",
             "notes": ["Platform status is an observation, not local verification.",
                       "Decomposition edges unite alternative groups; they are not a conjunctive proof obligation.",
                       "Definition dependencies, hidden platform relations and proof-body dependencies are not audited."]}
    files, provenance_rows = {}, []

    def snapshot(source_id, route, payload, provenance):
        path = "snapshots/" + source_id + ".json"
        data = encoded(payload)
        files[path] = data
        graph["sources"].append({"id": source_id, "kind": "api_snapshot", "url": API_BASE + route,
            "revision": "sha256:" + digest(data), "sha256": digest(data), "path": path,
            "observed_at": provenance["observed_at"], "license": "NOASSERTION",
            "redistribution": "reference_only"})
        provenance_rows.append({"source_id": source_id, **provenance,
                                "retained_sha256": digest(data), "filtered": True})

    for (kind, identity), (record, provenance) in sorted(entities.items()):
        node_id = f"prove2me:{kind}:{identity}"
        source_id = f"{kind}-{identity}"
        snapshot(source_id, f"/{kind}s/{identity}", record, provenance)
        citation_id = "cite:" + node_id
        graph["citations"].append({"id": citation_id, "title": record["name"],
            "url": f"https://prove2.me/{kind}s/{identity}", "source_id": source_id,
            "locator": "public platform record; proof source remains reference-only"})
        citation_ids = [citation_id]
        if "source_reference" in record:
            reference_id = "source-reference:" + node_id
            graph["citations"].append({"id": reference_id, "title": "Platform-provided source reference",
                "url": record["source_reference"], "source_id": source_id,
                "locator": "source field in public platform record; linked bytes not retrieved or verified"})
            citation_ids.append(reference_id)
        graph["nodes"].append({"id": node_id, "kind": "goal" if kind == "theorem" else "claim",
            "label": record["name"], "status": "unverified", "source_id": source_id,
            "assumption_ids": [], "evidence_ids": ["platform-intake"], "citation_ids": citation_ids,
            "boundary": "No local proof body, Lean extraction, assumption audit, or replay.",
            "platform": {"provider": "prove2me", "id": identity, "entity": kind,
                         "status": record["status"], "visibility": "public", "mathlib_rev": record["mathlib_rev"]}})
    for (kind, identity), (groups, provenance) in sorted(decompositions.items()):
        public_groups, destinations = [], set()
        for group in groups:
            children = [{"entity": kind, "id": child_id} for kind, child_id in group["children"]
                        if (kind, child_id) in entities]
            public_groups.append({"submission_id": group["submission_id"], "children": children,
                                  "deprecated": group["deprecated"],
                                  "omitted_children": len(group["children"]) - len(children)})
            destinations.update((c["entity"], c["id"]) for c in children)
        snapshot("decompositions-" + identity, f"/theorems/{identity}/decompositions",
                 {"theorem_id": identity, "decompositions": public_groups}, provenance)
        for child_kind, child_id in sorted(destinations):
            graph["edges"].append({"from": "prove2me:theorem:" + identity,
                "to": f"prove2me:{child_kind}:{child_id}", "kind": "platform_decomposition",
                "evidence_ids": ["platform-intake"]})
    snapshot("environments", "/environments", {"environments": environments}, env_provenance)
    graph["evidence"].append({"id": "platform-intake", "kind": "platform_observation", "status": "passed",
        "command": ["lean-exposition", "prove2me", url], "tool": "Prove2Me API " + REVIEWED_VERSION,
        "source_ids": [s["id"] for s in graph["sources"]], "subject_ids": [n["id"] for n in graph["nodes"]],
        "details": "Public metadata observed and filtered. No proof, assumption, or mathematical correctness check performed.",
        "receipt": {"platform": "prove2me", "platform_version": REVIEWED_VERSION,
                    "platform_closure_status": "partial", "local_verification": "not_run",
                    "assumption_audit": "not_run", "limits": {"max_nodes": max_nodes, "max_depth": max_depth},
                    "omissions": dict(sorted(omitted.items())), "hidden_relations": "unknown",
                    "environments": environments, "provenance": provenance_rows}})
    validate_graph(graph)
    files["graph.json"] = encoded(graph)
    return graph, files


def intake_prove2me(url: str, out: Path, *, credentials: Path | None = None,
                    max_nodes=100, max_depth=10, timeout=30.0) -> dict:
    """Write a filtered public snapshot into an empty directory after validation."""
    theorem_id(url)
    out = Path(out)
    if out.is_symlink():
        raise Prove2MeError("output directory must not be a symlink")
    # Canonicalize the chosen parent (e.g. macOS /tmp), then create only our fixed
    # filenames beneath a new/empty directory; no server-provided path is used.
    out = out.parent.resolve() / out.name
    if out.exists() and (not out.is_dir() or any(out.iterdir())):
        raise Prove2MeError("intake destination must be an empty directory")
    if credentials is not None and Path(credentials).resolve().is_relative_to(out.resolve()):
        raise Prove2MeError("credentials must stay outside the intake directory")
    client = Prove2MeClient(credentials, timeout=timeout, max_requests=2 * max_nodes + 4)
    graph, files = collect_prove2me(url, client, max_nodes=max_nodes, max_depth=max_depth)
    out.mkdir(parents=True, exist_ok=True)
    for name, data in files.items():
        path = out / name
        path.parent.mkdir(parents=True, exist_ok=True)
        with path.open("xb") as stream:
            stream.write(data)
    return {"graph_path": str(out / "graph.json"), "root_id": graph["selected_goals"][0],
            "nodes": len(graph["nodes"]), "edges": len(graph["edges"]),
            "platform_closure_status": "partial", "local_verification": "not_run"}
