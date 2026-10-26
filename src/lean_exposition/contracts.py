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
from jsonschema.validators import extend


class ContractError(ValueError):
    """An artifact violates a declared contract."""


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def encoded(value: dict) -> bytes:
    try:
        return (json.dumps(value, indent=2, ensure_ascii=False, sort_keys=True, allow_nan=False) + "\n").encode()
    except UnicodeEncodeError as exc:
        raise ContractError("JSON contains an unpaired Unicode surrogate") from exc


def _check_unicode_scalars(value) -> None:
    """Check native JSON-like keys and values without recursion or normalization."""
    pending, seen = [value], set()
    while pending:
        item = pending.pop()
        if isinstance(item, str):
            if any(0xD800 <= ord(character) <= 0xDFFF for character in item):
                raise ContractError("JSON contains an unpaired Unicode surrogate")
        elif isinstance(item, (list, tuple, dict)):
            identity = id(item)
            if identity in seen:
                continue
            seen.add(identity)
            if isinstance(item, dict):
                pending.extend(item.keys())
                pending.extend(item.values())
            else:
                pending.extend(item)


def decode_json(data: bytes) -> dict:
    """Decode exactly the bytes checked or captured, without ambiguous JSON."""
    def pairs(items):
        result = {}
        for key, _ in items:
            _check_unicode_scalars(key)
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
    value = json.loads(data.decode("utf-8"), object_pairs_hook=pairs,
                       parse_constant=invalid_constant, parse_float=finite_float)
    _check_unicode_scalars(value)
    return value


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


_UPSTREAM_UNIQUE_ITEMS = Draft202012Validator.VALIDATORS["uniqueItems"]


def _unique_items(validator, enabled, instance, schema):
    # These keys distinguish whole JSON objects. When they do not distinguish
    # every record, defer to jsonschema's full JSON equality, not ID equality.
    if enabled and type(instance) is list and all(type(row) is dict for row in instance):
        if all(type(row.get("id")) is str for row in instance):
            ids = [row["id"] for row in instance]
            if len(ids) == len(set(ids)):
                return
        elif all(all(type(row.get(key)) is str for key in ("from", "to", "kind"))
               for row in instance):
            triples = [(row["from"], row["to"], row["kind"]) for row in instance]
            if len(triples) == len(set(triples)):
                return
    yield from _UPSTREAM_UNIQUE_ITEMS(validator, enabled, instance, schema)


_SchemaValidator = extend(Draft202012Validator, {"uniqueItems": _unique_items})


def validate_schema(value: dict, name: str) -> None:
    _check_unicode_scalars(value)
    schema = json.loads(files("lean_exposition").joinpath(f"resources/schemas/{name}.schema.json").read_text())
    errors = sorted(_SchemaValidator(schema).iter_errors(value), key=lambda e: str(e.path))
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
    if receipt.get("receipt_profile") == "comparator-process-v2":
        if kind != "comparator":
            raise ContractError("Comparator process profile requires Comparator evidence")
        _validate_comparator_v2(receipt)


def _validate_comparator_v2(receipt: dict) -> None:
    """Check recorded v2 observations, not their authenticity or theorem scope."""
    def observation(name):
        value = receipt.get(name)
        if (not isinstance(value, dict) or not isinstance(value.get("status"), str) or
                value["status"] not in {"read", "unavailable"}):
            raise ContractError(f"invalid Comparator {name}")
        sha = value.get("sha256")
        if value["status"] == "read":
            if not isinstance(sha, str) or re.fullmatch(r"[0-9a-f]{64}", sha) is None:
                raise ContractError(f"invalid Comparator {name} hash")
        elif sha is not None:
            raise ContractError(f"unavailable Comparator {name} cannot carry a hash")
        if name.startswith("launch_"):
            if not isinstance(value.get("requested"), str) or not value["requested"]:
                raise ContractError(f"invalid Comparator {name} request")
            if value["status"] == "read" and any(
                not isinstance(value.get(field), str) or not value[field]
                for field in ("path", "resolved_path")
            ):
                raise ContractError(f"invalid Comparator {name} path")
        return value

    before, after = observation("config_read_before"), observation("config_read_after")
    launch_before = observation("launch_executable_before")
    launch_after = observation("launch_executable_after")
    if (receipt.get("config_sha256") != before.get("sha256") or
            receipt.get("config_sha256_after") != after.get("sha256")):
        raise ContractError("Comparator configuration hashes differ from observations")
    for field, changed in (("config_changed", before.get("sha256") != after.get("sha256")),
                           ("launch_executable_changed", launch_before != launch_after)):
        if type(receipt.get(field)) is not bool or receipt[field] != changed:
            raise ContractError(f"Comparator {field} differs from observations")
    scope = receipt.get("config_observation")
    if (not isinstance(scope, dict) or not isinstance(scope.get("status"), str) or
            scope["status"] not in {"observed", "invalid", "unavailable"}):
        raise ContractError("invalid Comparator configuration observation")
    if scope["status"] == "observed":
        if before["status"] != "read":
            raise ContractError("observed Comparator scope requires readable configuration")
        value = scope.get("scope")
        if (not isinstance(value, dict) or
                any(not isinstance(value.get(key), str) or not value[key].strip()
                    for key in ("challenge_module", "solution_module")) or
                any(not isinstance(value.get(key), list) or
                    any(not isinstance(item, str) or not item for item in value[key])
                    for key in ("theorem_names", "definition_names", "permitted_axioms")) or
                not (value["theorem_names"] or value["definition_names"]) or
                type(value.get("enable_nanoda")) is not bool):
            raise ContractError("invalid observed Comparator scope")
        kernels = value.get("external_kernels")
        if (not isinstance(kernels, dict) or
                any(not isinstance(name, str) or not name or not isinstance(cmd, list) or
                    not cmd or any(not isinstance(token, str) for token in cmd) or not cmd[0]
                    for name, cmd in kernels.items()) or
                (value["enable_nanoda"] and kernels) or
                not isinstance(scope.get("unknown_fields"), list) or
                any(not isinstance(field, str) for field in scope["unknown_fields"]) or
                scope.get("claim_association") != "not_checked"):
            raise ContractError("invalid observed Comparator scope")
    if receipt.get("status") == "passed":
        command = receipt.get("command")
        if (receipt.get("process_status") != "passed" or
                type(receipt.get("returncode")) is not int or receipt["returncode"] != 0 or
                receipt.get("source_changed") is not False or scope["status"] != "observed" or
                before["status"] != "read" or after["status"] != "read" or
                launch_before["status"] != "read" or launch_after["status"] != "read" or
                not isinstance(command, list) or not command or
                not isinstance(command[0], str) or launch_before["requested"] != command[0] or
                receipt["config_changed"] or receipt["launch_executable_changed"] or
                any(field in receipt for field in ("failure_reason", "failure_stage", "source_snapshot_error"))):
            raise ContractError("passed Comparator v2 receipt has contradictory observations")


def validate_extraction_request(receipt: dict, declaration_count: int) -> None:
    """Validate a present request; graph selection may differ from its roots."""
    if "extraction_request" not in receipt:
        return
    request = receipt["extraction_request"]
    if (not isinstance(request, dict) or
            set(request) != {"module", "roots", "module_prefixes", "max_declarations"} or
            not isinstance(request.get("module"), str) or not request["module"] or
            request["module"] != receipt.get("module") or
            not isinstance(request.get("roots"), list) or not request["roots"] or
            any(not isinstance(value, str) or not value for value in request["roots"]) or
            not isinstance(request.get("module_prefixes"), list) or
            any(not isinstance(value, str) or not value for value in request["module_prefixes"]) or
            type(request.get("max_declarations")) is not int or
            request["max_declarations"] < max(1, declaration_count)):
        raise ContractError("extraction request differs from receipt module or declaration limit")


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


def argument_contexts(graph: dict, roots=None, edge_kinds=None, *, include_assumptions=True):
    """Walk recorded dependencies in local premise scopes, never infer a proof.

    A state is (node ID, discharged premise IDs). Keeping states, rather than
    globally deleting premises, preserves an independently reached free use.
    Suppliers are ordinary support edges outside the annotated theorem branch.
    A retained formal axiom or proof hole can restore that ID on its own path.
    """
    return _argument_contexts(graph, roots, edge_kinds,
                              include_assumptions=include_assumptions,
                              retain_formal_dependencies=True)


def _argument_contexts(graph: dict, roots=None, edge_kinds=None, *, include_assumptions=True,
                       retain_formal_dependencies=True):
    nodes = indexed(graph["nodes"], "node")
    seeds = list(graph["selected_goals"] if roots is None else roots)
    require_refs(seeds, nodes, "closure root")
    kinds = ARGUMENT_EDGES if edge_kinds is None else set(edge_kinds)
    require_refs(kinds, EDGE_KINDS, "closure edge kind")
    extracted_subjects = {subject for evidence in graph.get("evidence", [])
                          if evidence["kind"] == "extraction" and evidence["status"] == "passed"
                          for subject in evidence["subject_ids"]}
    neighbors: dict[str, list[dict]] = {}
    for e in graph["edges"]:
        if e["kind"] in kinds:
            require_refs([e["from"], e["to"]], nodes, "closure edge endpoint")
            neighbors.setdefault(e["from"], []).append(e)
    pending = [(node, frozenset()) for node in seeds]
    states, transitions = set(), []
    while pending:
        state = pending.pop()
        node, discharged = state
        if state in states or node in discharged:
            continue
        states.add(state)
        steps = []
        for edge in neighbors.get(node, ()):
            supplied = {p["assumption_id"] for p in edge.get("application", {}).get("premise_bindings", [])}
            steps.append((edge["to"], discharged | supplied, edge))
        if include_assumptions and kinds & ARGUMENT_EDGES:
            require_refs(nodes[node]["assumption_ids"], nodes, "closure assumption")
            steps.extend((target, discharged, None) for target in nodes[node]["assumption_ids"])
        for target, scope, edge in steps:
            if target in scope:
                # A supplied premise cannot alter a retained Lean proof's axiom
                # inventory or fill a hole. Classification is occurrence-specific.
                assumption = nodes[target]
                is_hole = target == "sorryAx" or assumption.get("declaration") == "sorryAx"
                is_lean_dependency = (assumption["kind"] == "assumption" and
                    ((edge is None and node in extracted_subjects) or
                     (edge is not None and edge["kind"] in LEAN_EDGES)))
                if not retain_formal_dependencies or not (is_hole or is_lean_dependency):
                    continue
                scope = scope - {target}
            successor = (target, frozenset(scope))
            transitions.append((state, successor, edge))
            pending.append(successor)
    return states, transitions


def closure(graph: dict, roots=None, edge_kinds=None) -> set[str]:
    """Consumer -> prerequisite, respecting only explicitly authored applications."""
    states, _ = argument_contexts(graph, roots, edge_kinds)
    return {node for node, _ in states}


def _validate_applications(graph: dict, nodes: dict, sources: dict) -> None:
    applications = [edge for edge in graph["edges"] if "application" in edge]
    if applications and graph["schema_version"] != "1.2":
        raise ContractError("scoped applications require graph version 1.2")
    # One application layer only. Ordinary dependency cycles remain supported.
    plain = {**graph, "edges": [{k: v for k, v in edge.items() if k != "application"}
                               for edge in graph["edges"]]}
    for edge in applications:
        app = edge["application"]
        if edge["kind"] != "supports":
            raise ContractError("scoped application must annotate a supports edge")
        if nodes[edge["from"]]["kind"] not in {"goal", "claim"} or nodes[edge["to"]]["kind"] == "assumption":
            raise ContractError("scoped application must connect a claim to a conditional result")
        span = app["source_span"]
        require_refs([span["source_id"]], sources, "application source")
        if span["end_line"] < span["start_line"]:
            raise ContractError("application source span is reversed")
        premises = [p["assumption_id"] for p in app["premise_bindings"]]
        if len(set(premises)) != len(premises):
            raise ContractError("application premise may be supplied only once")
        theorem_scope = closure(plain, [edge["to"]])
        theorem_assumptions = {n for n in theorem_scope if nodes[n]["kind"] == "assumption"}
        require_refs(premises, theorem_assumptions, "application theorem premise")
        supplied_scope = set()
        for premise in app["premise_bindings"]:
            supplier = premise["supplier_id"]
            require_refs([supplier], nodes, "application supplier")
            if nodes[supplier]["kind"] == "assumption":
                raise ContractError("application supplier must record an argument, not another assumption")
            require_refs(premise["binding_names"], app["shared_bindings"], "shared application binding")
            if not any(e["from"] == edge["from"] and e["to"] == supplier
                       and e["kind"] == "supports" and "application" not in e
                       for e in graph["edges"]):
                raise ContractError("application supplier needs an ordinary support edge from its consumer")
            supplied_scope |= closure(plain, [supplier])
        inputs = theorem_scope | supplied_scope
        if edge["from"] in inputs:
            raise ContractError("cyclic scoped application is unsupported")
        if any(other["from"] in inputs for other in applications):
            raise ContractError("nested scoped applications are unsupported")
        # Measure only this use, including supplier premises. The actual consumer
        # may also have independent inputs, which retain their own assumptions.
        local = copy.deepcopy(graph)
        root = "__application_scope__"
        while root in nodes:
            root += "_"
        local["nodes"].append({"id": root, "assumption_ids": []})
        local["edges"].append({**edge, "from": root})
        local["edges"].extend({"from": root, "to": p["supplier_id"], "kind": "supports"}
                              for p in app["premise_bindings"])
        required = {n for n in closure(local, [root]) if n in nodes and nodes[n]["kind"] == "assumption"}
        old_states, _ = _argument_contexts(local, [root], retain_formal_dependencies=False)
        historical = {n for n, _ in old_states if n in nodes and nodes[n]["kind"] == "assumption"}
        if set(app["remaining_assumption_ids"]) not in (required, historical):
            raise ContractError("application remaining assumptions differ from scoped inputs")


def documentary_citation_seeds(graph: dict, roots=None) -> set[str]:
    """Record proof-use and supplied-premise references without making them assumptions."""
    states, transitions = argument_contexts(graph, roots)
    seeds = {node for node, _ in states}
    seeds.update(p["assumption_id"] for _, _, edge in transitions if edge
                 for p in edge.get("application", {}).get("premise_bindings", []))
    return seeds


def required_citation_ids(graph: dict, roots=None) -> set[str]:
    """Preserve reference credit without treating cited claims as prerequisites."""
    cited = closure(graph, documentary_citation_seeds(graph, roots), {"cites"})
    return {c for n in graph["nodes"] if n["id"] in cited for c in n["citation_ids"]}


def _historical_required_citation_ids(graph: dict, roots=None) -> set[str]:
    """Retain the original validation policy for captured historical mappings."""
    cited = closure(graph, closure(graph, roots), {"cites"})
    return {c for n in graph["nodes"] if n["id"] in cited for c in n["citation_ids"]}


def formal_result_assurances(graph: dict, node_ids=None) -> dict[str, dict]:
    """Describe recorded eligibility on a validated graph, not execution truth."""
    nodes = indexed(graph["nodes"], "node")
    selected = list(nodes) if node_ids is None else list(node_ids)
    require_refs(selected, nodes, "formal result node")
    evidence = indexed(graph["evidence"], "evidence")
    result = {}
    for node_id in selected:
        node = nodes[node_id]
        associated = [evidence[e] for e in node["evidence_ids"] if e in evidence]
        extracted = [item for item in associated
                     if item["kind"] == "extraction" and item["status"] == "passed"
                     and node_id in item["subject_ids"]
                     and item.get("receipt", {}).get("projection_profile") == "lean-extraction-v2"]
        builds = [item for item in associated if item["kind"] == "lean_build"
                  and item["status"] == "passed" and node_id in item["subject_ids"]
                  and node.get("source_id") in item["source_ids"]
                  and item.get("receipt", {}).get("process_status") == "passed"]
        current = []
        for item in extracted:
            receipt = item["receipt"]
            hashes = (receipt.get("extractor_sha256"), receipt.get("extractor_template_sha256"),
                      receipt.get("stdout_sha256"), receipt.get("stdout_bytes_sha256"))
            complete = (isinstance(receipt.get("extraction_request"), dict) and
                        receipt.get("report_stdout_binding") == "lean-report-stdout-v1" and
                        receipt.get("process_status") == "passed" and receipt.get("stdout_utf8_valid") is True and
                        all(isinstance(sha, str) and re.fullmatch(r"[0-9a-f]{64}", sha) for sha in hashes) and
                        hashes[2] == hashes[3])
            if complete and any(build["receipt"].get("module") == receipt.get("module") and
                                build["receipt"].get("source_hashes") == receipt.get("source_hashes")
                                for build in builds):
                current.append(item["id"])
        safe = (node["kind"] == "declaration" and node["status"] == "kernel_checked" and
                node.get("is_unsafe") is False and node.get("is_partial") is False and bool(extracted))
        eligible = bool(safe and current)
        safety = ("recorded_safe_v2" if safe else
                  "legacy_or_unknown_safety" if node["status"] == "kernel_checked" else
                  "not_kernel_checked")
        result[node_id] = {"node_id": node_id, "recorded_status": node["status"],
                           "formal_result_eligible": eligible, "safety_classification": safety,
                           "assurance_state": ("current_observations" if eligible else
                                               "historical_or_incomplete" if node["status"] == "kernel_checked"
                                               else "not_kernel_checked"),
                           "v2_extraction_evidence_ids": sorted(item["id"] for item in extracted),
                           "current_extraction_evidence_ids": sorted(current),
                           "scope": "Recorded classification and bound evidence only; no execution authentication or mathematical acceptance."}
    return result


def formal_result_assurance(graph: dict, node_id: str) -> dict:
    return formal_result_assurances(graph, [node_id])[node_id]


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
        if receipt is not None and item["kind"] == "extraction":
            validate_extraction_request(receipt, len(item["subject_ids"]))
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
                if profile == "lean-extraction-v2" and graph["schema_version"] not in {"1.1", "1.2"}:
                    raise ContractError("version 2 extraction requires graph version 1.1 or 1.2")
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
    # Do not infer missing axioms or follow structural edges. Reject only a
    # positively recorded type/value path or extracted inventory leading to a
    # known hole, even if one declaration's own inventory omitted it.
    extracted = {subject for item in evidence.values()
                 if item["kind"] == "extraction" and item["status"] == "passed"
                 for subject in item["subject_ids"]}
    incoming: dict[str, set[str]] = {}
    for edge in graph["edges"]:
        if edge["kind"] in {"lean_type_dependency", "lean_value_dependency"}:
            incoming.setdefault(edge["to"], set()).add(edge["from"])
    for subject in extracted:
        for assumption in nodes[subject]["assumption_ids"]:
            incoming.setdefault(assumption, set()).add(subject)
    holes = {identity for identity, node in nodes.items()
             if identity == "sorryAx" or node.get("declaration") == "sorryAx"}
    affected, pending = set(holes), list(holes)
    while pending:
        for predecessor in incoming.get(pending.pop(), ()):
            if predecessor not in affected:
                affected.add(predecessor)
                pending.append(predecessor)
    if any(nodes[identity]["status"] == "kernel_checked" for identity in affected):
        raise ContractError("kernel_checked cannot have a recorded type/value dependency path to sorryAx")
    _validate_applications(graph, nodes, sources)
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


def validate_artifact(artifact: dict, graph: dict, graph_hash: str, content: bytes, *,
                      require_current_formal_assurance: bool = False,
                      require_current_citations: bool = False) -> None:
    if type(require_current_formal_assurance) is not bool or type(require_current_citations) is not bool:
        raise ContractError("current authoring validation flags must be boolean")
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
    # Read historical captures under their original citation rule. New authoring
    # enforces effective documentary credit both globally and in each passage.
    citation_requirements = (required_citation_ids if require_current_citations
                             else _historical_required_citation_ids)
    required_cites = citation_requirements(graph, roots)
    if not required_cites <= set(artifact["citation_ids"]):
        raise ContractError("artifact dropped a claim citation")
    # Reading metadata describes authored treatment and navigation only. It does
    # not enter mathematical closure or change evidence and review requirements.
    reading_passages = {passage["anchor"]: passage for passage in artifact["passages"]}
    reading_keys = set()
    for link in artifact.get("reading_links", []):
        require_refs([link["from_anchor"]], reading_passages, "reading link source anchor")
        if link["from_text_sha256"] != reading_passages[link["from_anchor"]]["text_sha256"]:
            raise ContractError("reading link source passage hash is stale")
        if link["to_stage"] == artifact["stage"]:
            require_refs([link["to_anchor"]], reading_passages, "reading link target anchor")
            if link["to_text_sha256"] != reading_passages[link["to_anchor"]]["text_sha256"]:
                raise ContractError("reading link target passage hash is stale")
        key = (link["from_anchor"], link["to_stage"], link["to_anchor"], link["kind"])
        if key in reading_keys:
            raise ContractError("duplicate reading link")
        reading_keys.add(key)
    for passage in artifact["passages"]:
        treatment_claims = [row["claim_id"] for row in passage.get("treatments", [])]
        if len(treatment_claims) != len(set(treatment_claims)):
            raise ContractError("duplicate treatment claim in passage")
        require_refs(treatment_claims, passage["claim_ids"], "passage treatment claim")
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
        formal_assurance = (formal_result_assurances(graph)
                            if require_current_formal_assurance and
                            any(p["evidence_class"] == "formal_result" for p in artifact["passages"])
                            else {})
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
            if (passage["evidence_class"] == "formal_result" and require_current_formal_assurance and
                    any(not formal_assurance[n]["formal_result_eligible"]
                        for n in passage["claim_ids"])):
                raise ContractError("new formal_result requires current bound extraction and build observations")
            passage_roots = passage["claim_ids"] + passage["assumption_ids"]
            passage_closure = closure(graph, passage_roots)
            if not {n for n in passage_closure if nodes[n]["kind"] == "assumption"} <= set(passage["assumption_ids"]):
                raise ContractError("passage omits an applicable assumption")
            if not citation_requirements(graph, passage_roots) <= set(passage["citation_ids"]):
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
