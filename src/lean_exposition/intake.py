"""Retrieve explicitly licensed, pinned public bytes, without executing them."""
from __future__ import annotations

import re
import unicodedata
import urllib.parse
import urllib.request
from pathlib import Path

from .contracts import ContractError, digest, local_path, portable_path


def _public_url(value: str):
    if not isinstance(value, str) or any(c.isspace() for c in value):
        raise ContractError("source URL must be public HTTPS without credentials/query")
    parsed = urllib.parse.urlsplit(value)
    if parsed.scheme != "https" or not parsed.hostname or parsed.username or parsed.password or parsed.query or parsed.fragment:
        raise ContractError("source URL must be public HTTPS without credentials/query")
    return parsed


def validate_lock(lock: dict) -> None:
    if not isinstance(lock, dict):
        raise ContractError("source lock must be an object")
    if lock.get("schema_version") != "1.0" or not isinstance(lock.get("files"), list) or not lock["files"]:
        raise ContractError("invalid source lock")
    revision = lock.get("revision", "")
    if not re.fullmatch(r"[0-9a-f]{40}", revision):
        raise ContractError("source revision must be a full Git commit")
    if lock.get("license") not in {"Apache-2.0", "MIT", "BSD-3-Clause", "CC0-1.0"}:
        raise ContractError("retrieval requires an explicitly supported redistribution license")
    seen = set()
    sources = {s["id"]: s for s in lock.get("sources", [])}
    if len(sources) != len(lock.get("sources", [])):
        raise ContractError("duplicate locked source")
    for row in lock["files"]:
        portable_path(row["path"])
        if row["path"] in seen:
            raise ContractError("duplicate source path")
        seen.add(row["path"])
        parsed = _public_url(row["url"])
        source = sources.get(row.get("source"), lock)
        if sources and row.get("source") not in sources:
            raise ContractError("unknown locked source")
        if source["license"] not in {"Apache-2.0", "MIT", "BSD-3-Clause", "CC0-1.0"}:
            raise ContractError("source license does not allow this retrieval policy")
        if not re.fullmatch(r"[0-9a-f]{40}", source["revision"]) or source["revision"] not in parsed.path.split("/"):
            raise ContractError("source URL is not pinned to the locked revision")
        if "repository" in source:
            repository = _public_url(source["repository"])
            if repository.hostname == "github.com":
                owner_repo = repository.path.strip("/").removesuffix(".git")
                prefix = f"/{owner_repo}/{source['revision']}/"
                if parsed.hostname != "raw.githubusercontent.com" or not parsed.path.startswith(prefix):
                    raise ContractError("source URL differs from the locked repository")
                if "upstream_path" in row and parsed.path != prefix + row["upstream_path"]:
                    raise ContractError("source URL differs from the locked upstream path")
        if not re.fullmatch(r"[0-9a-f]{64}", row["sha256"]) or type(row["bytes"]) is not int or not 0 <= row["bytes"] <= 10_000_000:
            raise ContractError("invalid source size/hash")
    for row in lock.get("derived_files", []):
        portable_path(row["path"])
        if row["path"] in seen:
            raise ContractError("duplicate derived source path")
        seen.add(row["path"])
        if not row["derived_from"] or not set(row["derived_from"]) <= {f["path"] for f in lock["files"]}:
            raise ContractError("unknown derivation source")
        data = row["content"].encode("utf-8")
        if type(row["bytes"]) is not int or not 0 <= row["bytes"] <= 10_000_000 or len(data) != row["bytes"] or digest(data) != row["sha256"]:
            raise ContractError("derived content differs from its locked hash")
    portable = {unicodedata.normalize("NFC", path).casefold() for path in seen}
    if len(portable) != len(seen) or any("/".join(path.split("/")[:i]) in portable for path in portable for i in range(1, len(path.split("/")))):
        raise ContractError("source destinations collide on a portable filesystem")


def audit_sources(lock: dict, root: Path) -> dict:
    validate_lock(lock)
    total = 0
    rows = lock["files"] + lock.get("derived_files", [])
    for row in rows:
        path = local_path(root, row["path"])
        if not path.is_file():
            raise ContractError(f"missing source: {row['path']}")
        data = path.read_bytes()
        if len(data) != row["bytes"] or digest(data) != row["sha256"]:
            raise ContractError(f"source hash/size mismatch: {row['path']}")
        total += len(data)
    return {"status": "passed", "revision": lock["revision"], "files": len(lock["files"]), "derived_files": len(lock.get("derived_files", [])), "bytes": total, "lean_replay": "not_implied"}


def fetch(lock: dict, root: Path) -> dict:
    validate_lock(lock)
    if root.exists() and any(root.iterdir()):
        raise ContractError("fetch destination must be empty")
    root.mkdir(parents=True, exist_ok=True)
    for row in lock["files"]:
        request = urllib.request.Request(row["url"], headers={"User-Agent": "lean-exposition/0.1"})
        with urllib.request.urlopen(request, timeout=45) as response:
            _public_url(response.url)
            data = response.read(row["bytes"] + 1)
        if digest(data) != row["sha256"] or len(data) != row["bytes"]:
            raise ContractError(f"download differs from source lock: {row['path']}")
        path = local_path(root, row["path"])
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)
    for row in lock.get("derived_files", []):
        path = local_path(root, row["path"])
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(row["content"].encode("utf-8"))
    return audit_sources(lock, root)
