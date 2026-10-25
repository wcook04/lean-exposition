"""Structural checks and cross-record invariants; never a semantic proof checker."""
from __future__ import annotations

import copy
import hashlib
import json
import math
import re
from datetime import datetime
from importlib.resources import files
from pathlib import Path, PurePosixPath
from urllib.parse import urlsplit

from jsonschema import Draft202012Validator


class ContractError(ValueError):
    """An artifact violates a declared contract."""


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def encoded(value: dict) -> bytes:
    return (json.dumps(value, indent=2, ensure_ascii=False, sort_keys=True, allow_nan=False) + "\n").encode()


def decode_json(data: bytes) -> dict:
    """Decode exactly the bytes checked or captured, without ambiguous JSON."""
    def pairs(items):
        result = {}
        for key, value in items:
            if key in result:
                raise ContractError(f"duplicate JSON key: {key}")
            result[key] = value
        return result
    def invalid_constant(value):
        raise ContractError(f"non-finite JSON number: {value}")
    def finite_float(value):
        result = float(value)
        if not math.isfinite(result):
            raise ContractError(f"non-finite JSON number: {value}")
        return result
    return json.loads(data.decode("utf-8"), object_pairs_hook=pairs,
                      parse_constant=invalid_constant, parse_float=finite_float)


def read_json(path: Path) -> dict:
    return decode_json(path.read_bytes())


def write_json(path: Path, value: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(encoded(value))


def portable_path(relative: str) -> PurePosixPath:
    """Check a reference's syntax without resolving it against the caller's CWD."""
    if not isinstance(relative, str) or not relative:
        raise ContractError(f"not a portable relative path: {relative}")
    name = PurePosixPath(relative)
    if name.is_absolute() or any(p in ("", "..", ".") for p in relative.split("/")) or "\\" in relative or ":" in relative or any(ord(c) < 32 for c in relative):
        raise ContractError(f"not a portable relative path: {relative}")
    devices = {"CON", "PRN", "AUX", "NUL"} | {f"{prefix}{n}" for prefix in ("COM", "LPT") for n in "123456789¹²³"}
    if any(part.endswith((".", " ")) or part.split(".", 1)[0].upper() in devices
           or any(c in '<>"|?*' for c in part) for part in name.parts):
        raise ContractError(f"not a portable relative path: {relative}")
    return name


def local_path(root: Path, relative: str) -> Path:
    """Resolve an artifact for I/O without traversal or symlink ancestry."""
    name = portable_path(relative)
    root = root.resolve()
    current = root
    for part in name.parts:
        current /= part
        if current.is_symlink():
            raise ContractError(f"symlink is not a bundle artifact: {relative}")
    if not current.resolve().is_relative_to(root):
        raise ContractError(f"path escapes artifact root: {relative}")
    return current


def validate_schema(value: dict, name: str) -> None:
    schema = json.loads(files("lean_exposition").joinpath(f"resources/schemas/{name}.schema.json").read_text())
    errors = sorted(Draft202012Validator(schema).iter_errors(value), key=lambda e: str(e.path))
    if errors:
        e = errors[0]
        raise ContractError(f"{name}:{'/'.join(map(str, e.path))}: {e.message}")


def indexed(rows: list[dict], label: str) -> dict[str, dict]:
    result = {r["id"]: r for r in rows}
    if len(result) != len(rows):
        raise ContractError(f"duplicate {label} id")
    return result


def require_refs(values, universe, label):
    missing = set(values) - set(universe)
    if missing:
        raise ContractError(f"unknown {label}: {', '.join(sorted(missing))}")


LEAN_EDGES = {"lean_type_dependency", "lean_value_dependency", "lean_structural_dependency"}
ARGUMENT_EDGES = LEAN_EDGES | {"formalizes", "supports"}
EDGE_KINDS = ARGUMENT_EDGES | {"platform_decomposition", "cites"}


def validate_process_receipt(receipt: dict, *, evidence_kind: str | None = None) -> None:
    """Check optional process/stream observations without inventing legacy data.

    Wrapper failure can follow a successful process, for example when source
    binding fails. The converse cannot support passing evidence. Raw-byte and
    display-text hashes agree only when the recorded UTF-8 decoding was valid.
    This checks internal consistency; it does not authenticate the receipt.
    """
    if not isinstance(receipt, dict):
        raise ContractError("receipt must be an object")
    if "process_status" in receipt:
        process_status = receipt["process_status"]
        if (not isinstance(process_status, str) or process_status not in {
            "passed", "failed", "unavailable", "timed_out", "not_run"
        }):
            raise ContractError("invalid receipt process_status")
        if receipt.get("status") == "passed" and process_status != "passed":
            raise ContractError("successful receipt requires a passed recorded process")
    if "output_decoding" in receipt and receipt["output_decoding"] != "utf-8-with-replacement":
        raise ContractError("invalid receipt output_decoding")
    for stream in ("stdout", "stderr"):
        text_key, raw_key = stream + "_sha256", stream + "_bytes_sha256"
        validity_key = stream + "_utf8_valid"
        for key in (text_key, raw_key):
            if key in receipt and (
                not isinstance(receipt[key], str)
                or re.fullmatch(r"[0-9a-f]{64}", receipt[key]) is None
            ):
                raise ContractError(f"invalid receipt {key}")
        if validity_key in receipt and type(receipt[validity_key]) is not bool:
            raise ContractError(f"invalid receipt {validity_key}")
        text_hash = receipt.get(text_key)
        if stream in receipt:
            if not isinstance(receipt[stream], str):
                raise ContractError(f"receipt {stream} must be text")
            try:
                observed = digest(receipt[stream].encode("utf-8"))
            except UnicodeEncodeError as exc:
                raise ContractError(f"receipt {stream} is not encodable UTF-8 text") from exc
            if text_hash is not None and text_hash != observed:
                raise ContractError(f"receipt {stream} text differs from its digest")
            text_hash = observed
        if receipt.get(validity_key) is True and raw_key in receipt:
            if text_hash is None:
                raise ContractError(f"UTF-8-valid {stream} bytes require a text digest")
            if receipt[raw_key] != text_hash:
                raise ContractError(f"UTF-8-valid {stream} byte and text digests disagree")
    kind = evidence_kind if evidence_kind is not None else receipt.get("evidence_kind")
    if (kind in ("extraction", "elaboration_process")
            and receipt.get("status") == "passed"
            and receipt.get("stdout_utf8_valid") is False):
        raise ContractError("successful extraction requires valid UTF-8 stdout")


def validate_extraction_report(report: dict) -> None:
    """Check the raw report protocol before hashing or translating it.

    This checks shape and classification consistency, not Lean semantics.
    Dependency arrays may repeat structural references. Optional metadata
    remains extensible; required evidence fields must have exact JSON types.
    """
    kinds = {"axiom", "definition", "theorem", "opaque", "quotient_primitive",
             "inductive", "constructor", "recursor"}
    body_kinds = {"definition", "theorem", "opaque"}

    def fields(value, required, label):
        if not isinstance(value, dict) or not required <= value.keys():
            raise ContractError(f"extraction report {label} lacks required fields")

    def text(value, label):
        if not isinstance(value, str) or not value:
            raise ContractError(f"extraction report {label} must be nonempty text")

    def names(value, label):
        if not isinstance(value, list):
            raise ContractError(f"extraction report {label} must be a name array")
        for name in value:
            text(name, label)
        return set(value)

    fields(report, {"schema_version", "module", "roots", "module_prefixes",
                   "declarations", "external_dependencies", "missing_declarations",
                   "unexpanded_declarations", "unavailable_bodies", "scope_complete",
                   "evidence_kind"}, "object")
    if type(report["schema_version"]) is not int or report["schema_version"] not in {1, 2}:
        raise ContractError("unsupported extraction report version")
    text(report["module"], "module")
    roots = names(report["roots"], "roots")
    if not roots:
        raise ContractError("extraction report requires at least one root")
    names(report["module_prefixes"], "module_prefixes")
    if type(report["scope_complete"]) is not bool:
        raise ContractError("extraction report scope_complete must be boolean")
    if report["evidence_kind"] != "elaborated_expression_dependencies":
        raise ContractError("unexpected extraction report evidence_kind")
    if "type_rendering" in report:
        text(report["type_rendering"], "type_rendering")

    records = {}
    for field in ("declarations", "external_dependencies"):
        if not isinstance(report[field], list):
            raise ContractError(f"extraction report {field} must be an array")
        records[field] = {}
        for row in report[field]:
            fields(row, {"name", "kind"}, field)
            text(row["name"], f"{field} name")
            if not isinstance(row["kind"], str) or row["kind"] not in kinds:
                raise ContractError("unsupported extracted declaration kind")
            if row["name"] in records[field]:
                raise ContractError(f"duplicate extracted declaration in {field}")
            records[field][row["name"]] = row

    references = set()
    declarations = records["declarations"]
    for row in declarations.values():
        fields(row, {"type", "type_dependencies", "value_dependencies", "structural_dependencies",
                     "axioms", "has_sorry", "body_available", "source"}, "declaration")
        text(row["type"], "declaration type")
        for flag in ("has_sorry", "body_available"):
            if type(row[flag]) is not bool:
                raise ContractError(f"extraction report {flag} must be boolean")
        if report["schema_version"] == 2:
            fields(row, {"is_unsafe", "is_partial"}, "declaration safety")
            if type(row["is_unsafe"]) is not bool:
                raise ContractError("extraction report is_unsafe must be boolean")
            if ((row["kind"] == "opaque" and row["is_partial"] is not None)
                    or (row["kind"] != "opaque" and type(row["is_partial"]) is not bool)):
                raise ContractError("extraction report is_partial must be boolean, or null for opaque")
        for field in ("type_dependencies", "value_dependencies", "structural_dependencies"):
            references.update(names(row[field], field))
        axioms = names(row["axioms"], "axioms")
        if row["has_sorry"] != ("sorryAx" in axioms):
            raise ContractError("inconsistent extracted sorry inventory")
        fields(row["source"], {"module", "line"}, "source")
        text(row["source"]["module"], "source module")
        for field in ("line", "column", "end_line"):
            value = row["source"].get(field)
            minimum = 0 if field == "column" else 1
            if value is not None and (type(value) is not int or value < minimum):
                raise ContractError(f"extraction report source {field} must be an integer or null")
        start, end = row["source"]["line"], row["source"].get("end_line")
        if start is not None and end is not None and end < start:
            raise ContractError("extraction report source range ends before it starts")
    for row in records["external_dependencies"].values():
        fields(row, {"module"}, "external dependency")
        text(row["module"], "external module")
        if "reason" in row and row["reason"] != "outside_module_prefixes":
            raise ContractError("unexpected external dependency reason")

    classifications = [set(declarations), set(records["external_dependencies"])]
    classifications.extend(names(report[field], field) for field in
                           ("missing_declarations", "unexpanded_declarations"))
    classified = set()
    for group in classifications:
        if classified & group:
            raise ContractError("extraction report declaration classifications overlap")
        classified.update(group)
    if not roots <= set(declarations) | set(report["unexpanded_declarations"]):
        raise ContractError("Lean report omits a requested root declaration")
    unavailable = names(report["unavailable_bodies"], "unavailable_bodies")
    if not unavailable <= set(declarations) or any(
        declarations[name]["kind"] not in body_kinds or declarations[name]["body_available"]
        for name in unavailable
    ):
        raise ContractError("extraction report unavailable_bodies contradicts declarations")
    unavailable_by_flag = {name for name, row in declarations.items()
                           if row["kind"] in body_kinds and not row["body_available"]}
    if report["scope_complete"] and (
        report["missing_declarations"] or report["unexpanded_declarations"]
        or unavailable or unavailable_by_flag or references - classified
    ):
        raise ContractError("Lean report claims complete scope with unresolved declarations")


def extraction_projection_digest(graph: dict, subject_ids: list[str], *,
                                 profile: str = "lean-extraction-v1") -> str:
    """Bind translated formal data while leaving prose and goal selection editable."""
    if profile not in {"lean-extraction-v1", "lean-extraction-v2"}:
        raise ContractError("unsupported extraction projection profile")
    subjects = set(subject_ids)
    edges = sorted(
        ({k: e[k] for k in ("from", "to", "kind")}
         for e in graph["edges"] if e["from"] in subjects and e["kind"] in LEAN_EDGES),
        key=lambda e: (e["from"], e["to"], e["kind"]),
    )
    identifiers = subjects | {e["to"] for e in edges}
    identifiers |= {a for n in graph["nodes"] if n["id"] in subjects for a in n["assumption_ids"]}
    fields = ("id", "kind", "declaration", "statement", "source_id", "assumption_ids", "boundary")
    if profile == "lean-extraction-v2":
        fields += ("locator", "lean_kind", "is_unsafe", "is_partial")
    nodes = sorted(({k: n[k] for k in fields if k in n} for n in graph["nodes"] if n["id"] in identifiers), key=lambda n: n["id"])
    return digest(encoded({"nodes": nodes, "edges": edges, "extraction_status": graph["extraction_status"]}))


def closure(graph: dict, roots=None, edge_kinds=None) -> set[str]:
    """Consumer -> prerequisite; only argument closure adds explicit assumptions."""
    nodes = indexed(graph["nodes"], "node")
    pending = list(graph["selected_goals"] if roots is None else roots)
    require_refs(pending, nodes, "closure root")
    kinds = ARGUMENT_EDGES if edge_kinds is None else set(edge_kinds)
    require_refs(kinds, EDGE_KINDS, "closure edge kind")
    neighbors: dict[str, set[str]] = {}
    for e in graph["edges"]:
        if e["kind"] in kinds:
            require_refs([e["from"], e["to"]], nodes, "closure edge endpoint")
            neighbors.setdefault(e["from"], set()).add(e["to"])
    result = set()
    while pending:
        node = pending.pop()
        if node in result:
            continue
        result.add(node)
        pending.extend(neighbors.get(node, ()))
        if kinds & ARGUMENT_EDGES:
            require_refs(nodes[node]["assumption_ids"], nodes, "closure assumption")
            pending.extend(nodes[node]["assumption_ids"])
    return result


def required_citation_ids(graph: dict, roots=None) -> set[str]:
    """Preserve reference credit without treating cited claims as prerequisites."""
    argument = closure(graph, roots)
    cited = closure(graph, argument, {"cites"})
    return {c for n in graph["nodes"] if n["id"] in cited for c in n["citation_ids"]}


def validate_graph(graph: dict) -> dict:
    validate_schema(graph, "graph")
    if graph["schema_version"] == "1.0" and any(
        "lean_kind" in node or "is_unsafe" in node or "is_partial" in node
        for node in graph["nodes"]
    ):
        raise ContractError("graph version 1.0 cannot contain declaration classification fields")
    nodes = indexed(graph["nodes"], "node")
    sources = indexed(graph["sources"], "source")
    cites = indexed(graph["citations"], "citation")
    evidence = indexed(graph["evidence"], "evidence")
    if not graph["selected_goals"]:
        raise ContractError("at least one selected goal is required")
    require_refs(graph["selected_goals"], nodes, "selected goal")
    for source in sources.values():
        if source["redistribution"] == "vendored" and not {"path", "sha256"} <= source.keys():
            raise ContractError("vendored source needs path and content hash")
        if "path" in source:
            portable_path(source["path"])
            if "sha256" not in source:
                raise ContractError("a source path requires a content hash")
        url = urlsplit(source["url"])
        if url.username or url.password:
            raise ContractError("source URLs must not contain credentials")
        if source["url"].startswith("urn:lean-source:sha256:") and (
            source.get("sha256") != source["url"].rsplit(":", 1)[-1]
            or source["revision"] != source.get("sha256")
        ):
            raise ContractError("Lean source identity differs from its content hash")
        if source["kind"] == "api_snapshot":
            if not {"sha256", "observed_at"} <= source.keys():
                raise ContractError("API snapshot requires content hash and observation time")
            if source["revision"] != "sha256:" + source["sha256"]:
                raise ContractError("API snapshot revision differs from its content hash")
            try:
                datetime.fromisoformat(source["observed_at"].replace("Z", "+00:00"))
            except ValueError as exc:
                raise ContractError("invalid API snapshot observation time") from exc
    for cite in cites.values():
        require_refs([cite["source_id"]], sources, "citation source")
        url = urlsplit(cite["url"])
        if url.username or url.password:
            raise ContractError("citation URLs must not contain credentials")
    for item in evidence.values():
        require_refs(item["source_ids"], sources, "evidence source")
        require_refs(item["subject_ids"], nodes, "evidence subject")
        if ("receipt_path" in item) != ("receipt_sha256" in item):
            raise ContractError("receipt path and hash must appear together")
        if "receipt_path" in item:
            portable_path(item["receipt_path"])
        receipt = item.get("receipt")
        if receipt is not None and "status" in receipt:
            recorded = "unavailable" if receipt["status"] == "timed_out" else receipt["status"]
            if recorded != item["status"]:
                raise ContractError("evidence status differs from its receipt")
        if receipt is not None and item["kind"] in {"lean_build", "extraction", "comparator"}:
            validate_process_receipt(receipt, evidence_kind=item["kind"])
        if item["kind"] in {"lean_build", "extraction", "comparator"} and item["status"] == "passed":
            if not item["source_ids"] or not item["command"] or not item["subject_ids"]:
                raise ContractError("successful Lean evidence requires sources, subjects and command")
            if receipt is None or type(receipt.get("returncode")) is not int or receipt["returncode"] != 0 or receipt.get("source_changed") is not False:
                raise ContractError("successful Lean evidence requires an unchanged source snapshot")
            expected_kind = "elaboration_process" if item["kind"] == "extraction" else item["kind"]
            if receipt.get("evidence_kind") != expected_kind:
                raise ContractError("Lean receipt purpose differs from its evidence kind")
            if receipt.get("status") != "passed" or receipt.get("command") != item["command"]:
                raise ContractError("successful Lean evidence must match its receipt status and command")
            if item["kind"] != "comparator" and (not isinstance(receipt.get("module"), str) or not receipt["module"]):
                raise ContractError("successful Lean evidence requires its module")
            if item["kind"] == "comparator":
                config_hash = receipt.get("config_sha256")
                if not isinstance(config_hash, str) or re.fullmatch(r"[0-9a-f]{64}", config_hash) is None:
                    raise ContractError("successful Comparator evidence requires its configuration hash")
                if not any(sources[s].get("sha256") == config_hash for s in item["source_ids"]):
                    raise ContractError("Comparator configuration must match an identified source")
            hashes = receipt.get("source_hashes", {})
            if not isinstance(hashes, dict) or "lean-toolchain" not in hashes:
                raise ContractError("successful Lean evidence requires pinned environment hashes")
            for path, sha in hashes.items():
                portable_path(path)
                if not isinstance(sha, str) or re.fullmatch(r"[0-9a-f]{64}", sha) is None:
                    raise ContractError("invalid receipt source hash")
            for sid in item["source_ids"]:
                source = sources[sid]
                is_comparator_config = item["kind"] == "comparator" and source.get("sha256") == receipt["config_sha256"]
                if "path" in source and not is_comparator_config and hashes.get(source["path"]) != source.get("sha256"):
                    raise ContractError("Lean receipt does not bind its source bytes")
                if source["url"].startswith("urn:lean-environment:sha256:"):
                    environment = {p: sha for p, sha in hashes.items() if p in {"lean-toolchain", "lake-manifest.json", "lakefile.lean", "lakefile.toml"}}
                    if source.get("sha256") != digest(encoded(environment)) or source["url"] != "urn:lean-environment:sha256:" + source["sha256"]:
                        raise ContractError("Lean environment identity differs from receipt hashes")
            if item["kind"] == "extraction":
                if not isinstance(receipt.get("report_sha256"), str) or re.fullmatch(r"[0-9a-f]{64}", receipt["report_sha256"]) is None:
                    raise ContractError("successful extraction requires its report content hash")
                profile = receipt.get("projection_profile", "lean-extraction-v1")
                if profile == "lean-extraction-v2" and graph["schema_version"] != "1.1":
                    raise ContractError("version 2 extraction requires graph version 1.1")
                if profile == "lean-extraction-v1" and graph["schema_version"] != "1.0":
                    raise ContractError("legacy extraction cannot be reclassified as graph version 1.1")
                if (type(receipt.get("report_schema_version", 1)) is not int
                        or receipt.get("report_schema_version", 1) != (2 if profile == "lean-extraction-v2" else 1)):
                    raise ContractError("extraction report and projection versions disagree")
                if receipt.get("projection_sha256") != extraction_projection_digest(graph, item["subject_ids"], profile=profile):
                    raise ContractError("formal graph projection differs from extraction receipt")
                for subject in item["subject_ids"]:
                    node = nodes[subject]
                    if node["kind"] not in {"declaration", "assumption"} or not {"source_id", "declaration", "statement"} <= node.keys():
                        raise ContractError("extraction subjects must identify formal declarations")
                    if node["source_id"] not in item["source_ids"]:
                        raise ContractError("extraction receipt must include each subject's source")
                    if profile == "lean-extraction-v2" and (
                        node.get("lean_kind") not in {"axiom", "definition", "theorem", "opaque",
                                                       "quotient_primitive", "inductive", "constructor", "recursor"}
                        or type(node.get("is_unsafe")) is not bool
                        or not (type(node.get("is_partial")) is bool or node.get("is_partial") is None)
                        or "is_partial" not in node
                        or not isinstance(node.get("locator"), str) or not node["locator"]
                    ):
                        raise ContractError("version 2 extraction requires bound safety and locator fields")
                    if profile == "lean-extraction-v2" and (
                        (node["lean_kind"] == "opaque" and node["is_partial"] is not None)
                        or (node["lean_kind"] != "opaque" and type(node["is_partial"]) is not bool)
                    ):
                        raise ContractError("opaque partiality must remain unknown in version 2")
    safety_subjects = {subject for item in evidence.values()
                       if item["kind"] == "extraction" and item["status"] == "passed"
                       and item.get("receipt", {}).get("projection_profile") == "lean-extraction-v2"
                       for subject in item["subject_ids"]}
    for node in nodes.values():
        if ("lean_kind" in node or "is_unsafe" in node or "is_partial" in node) and node["id"] not in safety_subjects:
            raise ContractError("declaration safety requires version 2 extraction evidence")
        require_refs(node["assumption_ids"], nodes, "assumption")
        if any(nodes[a]["kind"] != "assumption" for a in node["assumption_ids"]):
            raise ContractError("assumption_ids must reference assumption nodes")
        require_refs(node["evidence_ids"], evidence, "node evidence")
        require_refs(node["citation_ids"], cites, "node citation")
        if "source_id" in node:
            require_refs([node["source_id"]], sources, "node source")
        if node["status"] == "axiom" and node["kind"] != "assumption":
            raise ContractError("axiom status is reserved for assumption nodes")
        if node["kind"] == "assumption" and (node["id"] == "sorryAx" or node.get("declaration") == "sorryAx") and node["status"] != "open":
            raise ContractError("sorryAx must remain an open obligation")
        if node["status"] == "kernel_checked":
            if node.get("is_unsafe") is True or node.get("is_partial") is True:
                raise ContractError("unsafe or partial declaration cannot be kernel_checked")
            if any(evidence[e]["kind"] == "extraction" and evidence[e]["status"] == "passed"
                   and evidence[e].get("receipt", {}).get("projection_profile") == "lean-extraction-v2"
                   for e in node["evidence_ids"]) and (
                node.get("is_unsafe") is not False or node.get("is_partial") is not False
            ):
                raise ContractError("kernel_checked requires safe declaration classification")
            if node["kind"] != "declaration" or not {"source_id", "declaration", "statement"} <= node.keys():
                raise ContractError("kernel_checked is reserved for identified formal declarations")
            relevant = [evidence[e] for e in node["evidence_ids"] if evidence[e]["kind"] == "lean_build" and node["id"] in evidence[e]["subject_ids"]]
            if not relevant or not any(e["status"] == "passed" and node["source_id"] in e["source_ids"] for e in relevant):
                raise ContractError("kernel_checked needs a passed, source-bound Lean build receipt for that node")
            if "sha256" not in sources[node["source_id"]] or "path" not in sources[node["source_id"]]:
                raise ContractError("kernel_checked requires identified source file bytes")
            if any(a == "sorryAx" or nodes[a].get("declaration") == "sorryAx" for a in node["assumption_ids"]):
                raise ContractError("kernel_checked cannot depend on sorryAx")
            extractions = [evidence[e] for e in node["evidence_ids"] if evidence[e]["kind"] == "extraction" and evidence[e]["status"] == "passed" and node["id"] in evidence[e]["subject_ids"]]
            if not extractions:
                raise ContractError("kernel_checked requires an extracted declaration binding")
            if not any(build["receipt"]["module"] == extract["receipt"]["module"] and build["receipt"]["source_hashes"] == extract["receipt"]["source_hashes"]
                       for build in relevant if build["status"] == "passed" and node["source_id"] in build["source_ids"] for extract in extractions):
                raise ContractError("kernel_checked requires matching build and extraction source snapshots")
            if any(e["kind"] == "lean_build" and e["status"] == "failed"
                   and node["id"] in e["subject_ids"] and node["source_id"] in e["source_ids"]
                   for e in evidence.values()):
                raise ContractError("conflicting Lean build receipts require explicit resolution before kernel_checked")
    seen_edges = set()
    for edge in graph["edges"]:
        require_refs([edge["from"], edge["to"]], nodes, "edge endpoint")
        require_refs(edge["evidence_ids"], evidence, "edge evidence")
        identity = (edge["from"], edge["to"], edge["kind"])
        if identity in seen_edges:
            raise ContractError("duplicate typed edge")
        seen_edges.add(identity)
        if edge["kind"] == "formalizes" and (
            nodes[edge["from"]]["kind"] not in {"goal", "claim"}
            or nodes[edge["to"]]["kind"] != "declaration"
        ):
            raise ContractError("formalizes must point from an informal claim to a declaration")
        if edge["kind"] in LEAN_EDGES:
            if any(nodes[x]["kind"] not in {"declaration", "assumption"} for x in (edge["from"], edge["to"])):
                raise ContractError("Lean dependencies must join declarations or assumptions")
            if not any(evidence[e]["kind"] == "extraction" and evidence[e]["status"] == "passed" and edge["from"] in evidence[e]["subject_ids"] and nodes[edge["from"]].get("source_id") in evidence[e]["source_ids"] for e in edge["evidence_ids"]):
                raise ContractError("Lean dependency needs successful extraction evidence")
        if edge["kind"] == "platform_decomposition":
            endpoints = [nodes[edge[key]] for key in ("from", "to")]
            if any("platform" not in node or "source_id" not in node for node in endpoints) or endpoints[0]["platform"]["provider"] != endpoints[1]["platform"]["provider"]:
                raise ContractError("platform decomposition needs compatible platform endpoints")
            if not any(evidence[e]["kind"] == "platform_observation" and evidence[e]["status"] == "passed"
                       and all(node["id"] in evidence[e]["subject_ids"] and node["source_id"] in evidence[e]["source_ids"] for node in endpoints)
                       for e in edge["evidence_ids"]):
                raise ContractError("platform decomposition needs source-bound platform observation evidence")
    selected = closure(graph)
    if graph["extraction_status"] in {"partial", "complete"} and not any(e["kind"] == "extraction" and e["status"] == "passed" for e in evidence.values()):
        raise ContractError("extraction status requires successful extraction evidence")
    return {
        "id": graph["id"], "selected_goals": graph["selected_goals"],
        "argument_closure": sorted(selected),
        "platform_closure": sorted(closure(graph, edge_kinds={"platform_decomposition"})),
        "assumptions": sorted(n for n in selected if nodes[n]["kind"] == "assumption"),
        "unresolved": sorted(n for n in selected if nodes[n]["status"] in {"open", "unverified", "external", "conditional"}),
        "failed_evidence": sorted(e["id"] for e in evidence.values() if e["status"] == "failed"),
        "extraction_status": graph["extraction_status"],
        "semantic_certification": False,
    }


def select(graph: dict, goals: list[str]) -> dict:
    result = copy.deepcopy(graph)
    result["selected_goals"] = list(goals)
    validate_graph(result)
    return result


def validate_artifact(artifact: dict, graph: dict, graph_hash: str, content: bytes) -> None:
    validate_schema(artifact, "artifact")
    validate_graph(graph)
    nodes = indexed(graph["nodes"], "node")
    cites = indexed(graph["citations"], "citation")
    if artifact["graph_sha256"] != graph_hash or artifact["content_sha256"] != digest(content):
        raise ContractError("artifact content or graph hash is stale")
    goals = artifact["selected_goal_ids"]
    if artifact["schema_version"] == "1.0" and goals != graph["selected_goals"]:
        raise ContractError("artifact changed selected goals")
    if not goals:
        raise ContractError("artifact must select at least one goal")
    require_refs(goals, nodes, "artifact selected goal")
    for field in ("claim_ids", "assumption_ids", "unresolved_ids"):
        require_refs(artifact[field], nodes, field)
    if any(nodes[n]["kind"] != "assumption" for n in artifact["assumption_ids"]):
        raise ContractError("artifact assumption_ids must identify assumptions")
    require_refs(artifact["citation_ids"], cites, "artifact citation")
    roots = artifact["claim_ids"] + goals + artifact["assumption_ids"]
    required = closure(graph, roots)
    assumptions = {n for n in required if nodes[n]["kind"] == "assumption"}
    unresolved = {n for n in required if nodes[n]["status"] in {"open", "unverified", "external", "conditional"}}
    if not assumptions <= set(artifact["assumption_ids"]) or not unresolved <= set(artifact["unresolved_ids"]):
        raise ContractError("artifact omits assumptions or unresolved obligations")
    required_cites = required_citation_ids(graph, roots)
    if not required_cites <= set(artifact["citation_ids"]):
        raise ContractError("artifact dropped a claim citation")
    if artifact["state"] == "scaffold":
        if artifact["passages"] or artifact["review_state"] != "not_reviewed":
            raise ContractError("empty scaffold cannot carry authored passages or review")
        if "EMPTY SCAFFOLD" not in content.decode():
            raise ContractError("scaffold must visibly identify itself")
    else:
        if not artifact["passages"] or not artifact["claim_ids"]:
            raise ContractError("authored artifact requires claim and passage correspondence")
        if "EMPTY SCAFFOLD" in content.decode():
            raise ContractError("authored state still contains scaffold marker")
        if not set(goals) <= set(artifact["claim_ids"]):
            raise ContractError("authored artifact must cover every selected goal")
        anchors = [p["anchor"] for p in artifact["passages"]]
        if len(set(anchors)) != len(anchors):
            raise ContractError("duplicate passage anchor")
        intervals = []
        text = content.decode("utf-8")
        if set(re.findall(r"<!-- /?passage:([^>]+) -->", text)) != set(anchors):
            raise ContractError("unmapped passage marker")
        for passage in artifact["passages"]:
            require_refs(passage["claim_ids"], artifact["claim_ids"], "passage claim")
            require_refs(passage["citation_ids"], artifact["citation_ids"], "passage citation")
            require_refs(passage["assumption_ids"], artifact["assumption_ids"], "passage assumption")
            if passage["evidence_class"] == "formal_result" and (
                not passage["claim_ids"] or any(nodes[n]["kind"] != "declaration" or nodes[n]["status"] != "kernel_checked" for n in passage["claim_ids"])
            ):
                raise ContractError("formal_result passage requires kernel-checked declarations")
            passage_roots = passage["claim_ids"] + passage["assumption_ids"]
            passage_closure = closure(graph, passage_roots)
            if not {n for n in passage_closure if nodes[n]["kind"] == "assumption"} <= set(passage["assumption_ids"]):
                raise ContractError("passage omits an applicable assumption")
            if not required_citation_ids(graph, passage_roots) <= set(passage["citation_ids"]):
                raise ContractError("passage omits an applicable citation")
            # A stable explicit marker binds the exact passage bytes, not a fuzzy heading.
            marker = f"<!-- passage:{passage['anchor']} -->"
            end = f"<!-- /passage:{passage['anchor']} -->"
            if text.count(marker) != 1 or text.count(end) != 1:
                raise ContractError("passage markers missing or duplicated")
            start = text.index(marker) + len(marker)
            stop = text.index(end)
            if stop < start or digest(text[start:stop].encode()) != passage["text_sha256"]:
                raise ContractError("passage content hash is stale")
            if not text[start:stop].strip():
                raise ContractError("authored passage has no text")
            intervals.append((start - len(marker), stop + len(end)))
        intervals.sort()
        if any(a[1] > b[0] for a, b in zip(intervals, intervals[1:])):
            raise ContractError("passage markers overlap")
        covered = {c for p in artifact["passages"] for c in p["claim_ids"]}
        if not set(artifact["claim_ids"]) <= covered:
            raise ContractError("claimed coverage has no passage correspondence")
    if artifact["state"] == "reviewed" and (artifact["review_state"] != "accepted" or not artifact["review_notes"]):
        raise ContractError("reviewed artifact requires an explicit acceptance record")
