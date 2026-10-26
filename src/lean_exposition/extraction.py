"""Translate an actual Lean expression report to the common evidence graph."""
import re
from pathlib import Path

from .contracts import (ContractError, digest, encoded, extraction_projection_digest,
                        local_path, validate_extraction_report,
                        validate_extraction_request, validate_graph,
                        validate_process_receipt)
from .verification import _decode_extraction_stdout, _source_hashes


def _bound_receipt(receipt: dict, project: Path, module: str, *, evidence_kind: str) -> None:
    if not isinstance(receipt, dict):
        raise ContractError("receipt must be an object")
    if receipt.get("evidence_kind") != evidence_kind:
        raise ContractError(f"receipt must record {evidence_kind} evidence")
    if receipt.get("module") != module:
        raise ContractError("receipt belongs to a different Lean module")
    hashes = receipt.get("source_hashes")
    if not isinstance(hashes, dict) or "lean-toolchain" not in hashes:
        raise ContractError("receipt lacks a pinned source snapshot")
    if receipt.get("source_changed") is not False:
        raise ContractError("source changed during the recorded command")
    for path, sha in hashes.items():
        target = local_path(project, path)
        if not target.is_file() or digest(target.read_bytes()) != sha:
            raise ContractError(f"source differs from command receipt: {path}")
    # Checking only recorded paths misses newly added sources (or a receipt
    # that omitted an existing source). Use the producer's snapshot boundary,
    # including its explicit exclusions for caches and imported packages.
    try:
        current = _source_hashes(project)
    except OSError as exc:
        raise ContractError("current project source snapshot is unavailable") from exc
    if current != hashes:
        changed = sorted(path for path in current.keys() | hashes.keys()
                         if current.get(path) != hashes.get(path))
        raise ContractError("project source snapshot differs from command receipt: "
                            + ", ".join(changed))


def _current_extraction_receipt(receipt: dict) -> bool:
    return (receipt.get("evidence_kind") == "elaboration_process" and
            all(field in receipt for field in (
                "extraction_request", "extractor_template_sha256", "process_status")))


def _public_receipt(receipt: dict, *, strict_text_hash: bool = False) -> dict:
    """Keep evidence metadata, excluding machine-specific diagnostic output."""
    # Current process observations must agree before projection. Historical
    # receipts retain the earlier rule that raw diagnostic text is authoritative
    # for its display-text hash; a missing current field also precludes current
    # assurance in the derived graph classification.
    if _current_extraction_receipt(receipt) or strict_text_hash:
        validate_process_receipt(receipt)
    # Canonicalize a copy without rewriting the caller's receipt or raw-byte hash.
    receipt = receipt.copy()
    for stream in ("stdout", "stderr"):
        if stream in receipt:
            if not isinstance(receipt[stream], str):
                raise ContractError(f"receipt {stream} must be text")
            try:
                receipt[stream + "_sha256"] = digest(receipt[stream].encode("utf-8"))
            except UnicodeEncodeError as exc:
                raise ContractError(f"receipt {stream} is not encodable UTF-8 text") from exc
    validate_process_receipt(receipt)
    fields = {"status", "returncode", "module", "source_hashes", "source_changed",
              "evidence_kind", "extractor_sha256", "report_sha256", "failure_reason",
              "changed_paths", "command_sha256", "command_paths_redacted",
              "report_schema_version", "projection_profile", "failure_stage",
              "error_type", "errno", "extraction_request", "extractor_template_sha256",
              "process_status", "stdout_bytes_sha256", "stderr_bytes_sha256",
              "stdout_utf8_valid", "stderr_utf8_valid", "output_decoding"}
    result = {k: v for k, v in receipt.items() if k in fields}
    for key in ("failure_stage", "error_type"):
        if key in result and (
            not isinstance(result[key], str)
            or re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", result[key]) is None
        ):
            raise ContractError(f"invalid receipt {key}")
    if "errno" in result and result["errno"] is not None and (
        type(result["errno"]) is not int or result["errno"] < 0
    ):
        raise ContractError("invalid receipt errno")
    if "command_sha256" in result and (
        not isinstance(result["command_sha256"], str)
        or re.fullmatch(r"[0-9a-f]{64}", result["command_sha256"]) is None
    ):
        raise ContractError("invalid receipt command_sha256")
    for stream in ("stdout", "stderr"):
        key = stream + "_sha256"
        if key in receipt:
            result[key] = receipt[key]
    command = receipt.get("command")
    if (not isinstance(command, list) or not command
            or any(not isinstance(token, str) or not token for token in command)):
        raise ContractError("receipt command must be a nonempty text array")
    result["command"] = [Path(token).name if Path(token).is_absolute() else token for token in command]
    if result["command"] != receipt["command"]:
        result.setdefault("command_sha256", digest(encoded({"command": receipt["command"]})))
        result["command_paths_redacted"] = True
    return result


def _check_retained_output(receipt: dict, report_hash: str) -> bool:
    """Compare a retained raw report when present; old redacted receipts remain readable."""
    if "stdout" not in receipt:
        return False
    stdout = receipt["stdout"]
    if not isinstance(stdout, str):
        raise ContractError("receipt stdout must be text")
    marker_present = any(line.startswith("LEAN_EXPOSITION_JSON:")
                         for line in stdout.split("\n"))
    # A current producer always records these fields alongside its stdout. Old
    # receipts may retain diagnostics without the original report, so absence
    # of the marker alone does not establish a contradiction for those records.
    current_receipt = _current_extraction_receipt(receipt)
    if not marker_present and not current_receipt:
        return False
    try:
        raw_report = _decode_extraction_stdout(stdout)
        raw_hash = digest(encoded(raw_report))
    except (RecursionError, TypeError, ValueError) as exc:
        raise ContractError("invalid extraction report in retained process output") from exc
    if raw_hash != report_hash:
        raise ContractError("extraction report differs from retained process output")
    return True


def to_graph(report: dict, project: Path, build_receipt: dict | None = None) -> dict:
    """Source and environment bytes bind results; unresolved boundary nodes remain."""
    project = project.resolve()
    validate_extraction_report(report)
    profile = "lean-extraction-v2" if report["schema_version"] == 2 else "lean-extraction-v1"
    receipt = report.get("receipt", {})
    if not isinstance(receipt, dict):
        raise ContractError("extraction receipt must be an object")
    validate_extraction_request(receipt, len(report["declarations"]))
    if "extraction_request" in receipt and any(
        receipt["extraction_request"][field] != report[field]
        for field in ("module", "roots", "module_prefixes")
    ):
        raise ContractError("extraction request differs from report")
    if "extractor_template_sha256" in receipt and (
        not isinstance(receipt["extractor_template_sha256"], str)
        or re.fullmatch(r"[0-9a-f]{64}", receipt["extractor_template_sha256"]) is None
    ):
        raise ContractError("invalid extractor template hash")
    if (report["schema_version"] == 2 and
            (type(receipt.get("report_schema_version")) is not int
             or receipt["report_schema_version"] != 2)):
        raise ContractError("version 2 extraction requires its report version receipt")
    if "report_schema_version" in receipt and (
        type(receipt["report_schema_version"]) is not int
        or receipt["report_schema_version"] != report["schema_version"]
    ):
        raise ContractError("extraction report version differs from its receipt")
    if receipt.get("status") != "passed" or receipt.get("returncode") != 0:
        raise ContractError("extraction report requires a successful process receipt")
    try:
        report_hash = digest(encoded({k: v for k, v in report.items() if k != "receipt"}))
    except (RecursionError, TypeError, ValueError) as exc:
        raise ContractError("extraction report is not canonical UTF-8 JSON") from exc
    if receipt.get("report_sha256") != report_hash:
        raise ContractError("extraction report differs from its receipt")
    retained_report_bound = _check_retained_output(receipt, report_hash)
    _bound_receipt(receipt, project, report["module"], evidence_kind="elaboration_process")
    if build_receipt is not None:
        _bound_receipt(build_receipt, project, report["module"], evidence_kind="lean_build")
        if build_receipt["source_hashes"] != receipt["source_hashes"]:
            raise ContractError("build and extraction used different source snapshots")
    sources = []
    module_sources = {}
    modules = sorted({d["source"]["module"] for d in report["declarations"]})
    for module in modules:
        path = Path(*module.split(".")).with_suffix(".lean")
        local = local_path(project, path.as_posix())
        if not local.is_file():
            raise ContractError(f"selected module source unavailable: {path}")
        sha = digest(local.read_bytes())
        if receipt["source_hashes"].get(path.as_posix()) != sha:
            raise ContractError(f"extraction receipt omits selected source: {path}")
        sid = "module:" + module
        sources.append({"id": sid, "kind": "file", "url": f"urn:lean-source:sha256:{sha}",
                        "revision": sha, "sha256": sha, "path": path.as_posix(),
                        "license": "NOASSERTION", "redistribution": "reference_only"})
        module_sources[module] = sid
    env_files = {}
    for name in ("lean-toolchain", "lake-manifest.json", "lakefile.toml", "lakefile.lean"):
        path = local_path(project, name)
        if path.is_file():
            env_files[name] = digest(path.read_bytes())
    if "lean-toolchain" not in env_files:
        raise ContractError("extraction requires a pinned lean-toolchain")
    if any(receipt["source_hashes"].get(name) != sha for name, sha in env_files.items()):
        raise ContractError("environment differs from extraction source snapshot")
    toolchain = (project / "lean-toolchain").read_text(encoding="utf-8").strip()
    if re.fullmatch(r"[\w.-]+/[\w.-]+:(?:v\d+\.\d+\.\d+(?:-rc\d+)?|nightly-\d{4}-\d{2}-\d{2}|[0-9a-f]{40})", toolchain) is None:
        raise ContractError("lean-toolchain must pin a release, dated nightly or commit")
    env_hash = digest(encoded(env_files))
    sources.append({"id": "environment", "kind": "repository", "url": f"urn:lean-environment:sha256:{env_hash}",
                    "revision": toolchain,
                    "sha256": env_hash, "license": "NOASSERTION", "redistribution": "reference_only"})
    declaration_ids = {d["name"] for d in report["declarations"]}
    if len(declaration_ids) != len(report["declarations"]):
        raise ContractError("duplicate extracted declaration")
    unavailable_bodies = set(report["unavailable_bodies"])
    consumers = {}
    for d in report["declarations"]:
        if d["kind"] in {"definition", "theorem", "opaque"} and d["body_available"] is False:
            unavailable_bodies.add(d["name"])
        for field in ("type_dependencies", "value_dependencies", "structural_dependencies"):
            for dependency in d[field]:
                consumers.setdefault(dependency, set()).add(d["name"])
    incomplete_inspections = set(unavailable_bodies)
    pending = list(unavailable_bodies)
    while pending:
        for consumer in consumers.get(pending.pop(), ()):
            if consumer not in incomplete_inspections:
                incomplete_inspections.add(consumer)
                pending.append(consumer)
    nodes = {}
    for d in report["declarations"]:
        if d["has_sorry"] != ("sorryAx" in d["axioms"]):
            raise ContractError("inconsistent extracted sorry inventory")
        nodes[d["name"]] = {"id": d["name"], "kind": "assumption" if d["kind"] == "axiom" else "declaration",
             "label": d["name"], "declaration": d["name"], "statement": d["type"],
             "status": "axiom" if d["kind"] == "axiom" else "unverified",
             "source_id": module_sources[d["source"]["module"]],
             "locator": (f"{d['source']['module']}:{d['source']['line']}"
                         if d["source"]["line"] is not None else d["source"]["module"]),
             "assumption_ids": sorted(d["axioms"]), "evidence_ids": ["extract"], "citation_ids": [],
             "boundary": "Elaborated type/proof references; theorem hypotheses remain in the displayed type."}
        if report["schema_version"] == 2:
            nodes[d["name"]]["lean_kind"] = d["kind"]
            nodes[d["name"]]["is_unsafe"] = d["is_unsafe"]
            nodes[d["name"]]["is_partial"] = d["is_partial"]
        if d["name"] in unavailable_bodies:
            nodes[d["name"]]["boundary"] = (
                "Declaration body unavailable: proof-value dependency traversal is incomplete. Axiom names are retained independently from Lean.collectAxioms; body availability alone does not establish axiom-inventory completeness. "
                "Theorem hypotheses remain in the displayed type. Build status is recorded separately."
            )
        elif d["name"] in incomplete_inspections:
            nodes[d["name"]]["boundary"] = (
                "A dependency body is unavailable: transitive proof-value dependency traversal is incomplete. Axiom names are retained independently from Lean.collectAxioms; body availability alone does not establish axiom-inventory completeness. "
                "Theorem hypotheses remain in the displayed type. Build status is recorded separately."
            )
    for d in report["external_dependencies"]:
        nodes.setdefault(d["name"], {"id": d["name"], "kind": "assumption" if d["kind"] == "axiom" else "declaration",
                "label": d["name"], "status": "axiom" if d["kind"] == "axiom" else "external", "source_id": "environment",
                "locator": d["module"], "assumption_ids": [], "evidence_ids": ["extract"], "citation_ids": [],
                "boundary": "Outside selected module prefixes; declaration body not traversed."})
    for d in report["declarations"]:
        for name in d["axioms"]:
            nodes.setdefault(name, {"id": name, "kind": "assumption", "label": name,
                         "status": "open" if name == "sorryAx" else "axiom", "source_id": "environment",
                         "assumption_ids": [], "evidence_ids": ["extract"], "citation_ids": [],
                         "boundary": "Transitive Lean axiom inventory; not an informal premise inventory."})
            nodes[name]["kind"] = "assumption"
            if name == "sorryAx":
                nodes[name]["status"] = "open"
    edges = []
    unknown = set(report["missing_declarations"]) | set(report["unexpanded_declarations"])
    for name in unknown | set(report["roots"]):
        if name not in nodes:
            nodes[name] = {"id": name, "kind": "declaration", "label": name, "status": "unverified",
                           "assumption_ids": [], "evidence_ids": [], "citation_ids": [],
                           "boundary": "Extraction limit or missing declaration; unresolved."}
    for d in report["declarations"]:
        for key, kind in (("type_dependencies", "lean_type_dependency"), ("value_dependencies", "lean_value_dependency"), ("structural_dependencies", "lean_structural_dependency")):
            for name in sorted(set(d[key])):
                if name not in nodes:
                    unknown.add(name)
                    nodes[name] = {"id": name, "kind": "declaration", "label": name, "status": "unverified",
                                   "assumption_ids": [], "evidence_ids": ["extract"], "citation_ids": [],
                                   "boundary": "Extraction limit or missing declaration; unresolved."}
                edges.append({"from": d["name"], "to": name, "kind": kind, "evidence_ids": ["extract"]})
    receipt = _public_receipt(receipt)
    if retained_report_bound:
        # This is an observation of internal consistency, not authentication
        # of the process or a proof of semantic correspondence.
        receipt["report_stdout_binding"] = "lean-report-stdout-v1"
    current_hashes = (receipt.get("extractor_sha256"), receipt.get("extractor_template_sha256"),
                      receipt.get("stdout_sha256"), receipt.get("stdout_bytes_sha256"))
    current_observations = (
        report["schema_version"] == 2 and retained_report_bound and
        _current_extraction_receipt(receipt) and receipt.get("process_status") == "passed" and
        receipt.get("stdout_utf8_valid") is True and
        all(isinstance(sha, str) and re.fullmatch(r"[0-9a-f]{64}", sha) for sha in current_hashes) and
        current_hashes[2] == current_hashes[3]
    )
    evidence = [{"id": "extract", "kind": "extraction", "status": "passed", "command": receipt["command"],
                 "tool": sources[-1]["revision"], "source_ids": [s["id"] for s in sources],
                 "subject_ids": sorted(declaration_ids), "details": "Expression extraction executed; not a fresh kernel replay, equivalence proof, or prose review.", "receipt": receipt}]
    if build_receipt is not None:
        public_build_receipt = _public_receipt(
            build_receipt, strict_text_hash=current_observations and
            build_receipt.get("process_status") == "passed")
        status = build_receipt["status"]
        if status == "timed_out":
            status = "unavailable"
        evidence.append({"id": "build", "kind": "lean_build", "status": status,
                         "command": public_build_receipt["command"], "tool": sources[-1]["revision"],
                         "source_ids": [s["id"] for s in sources], "subject_ids": sorted(declaration_ids),
                         "details": "Local Lake build of the selected module, using its pinned environment; cached dependencies may be reused.", "receipt": public_build_receipt})
        for d in report["declarations"]:
            nodes[d["name"]]["evidence_ids"].append("build")
            if (status == "passed" and not d["has_sorry"] and d["kind"] != "axiom"
                    and report["schema_version"] == 2
                    and d["is_unsafe"] is False and d["is_partial"] is False):
                nodes[d["name"]]["status"] = "kernel_checked"
    graph = {"schema_version": "1.1" if report["schema_version"] == 2 else "1.0",
             "id": "lean:" + report["module"], "title": "Selected Lean declaration closure",
             "selected_goals": list(dict.fromkeys(report["roots"])), "sources": sources, "citations": [],
             "nodes": sorted(nodes.values(), key=lambda n:n["id"]), "edges": edges, "evidence": evidence,
             "scope": "Elaborated expression references within selected module prefixes; external dependencies remain explicit.",
             "extraction_status": "complete" if report["scope_complete"] and not report["external_dependencies"] and not unknown and not unavailable_bodies else "partial",
             "notes": ["Type, proof-value and structural edges point from consumer to prerequisite.",
                       "No tactic execution, macro dependency, informal argument or pedagogical order is inferred.",
                       "Source licensing must be established before redistributing a new corpus.",
                       "Receipts bind project source and environment bytes; imported package sources and cached compiled artifacts are outside that snapshot.",
                       "Diagnostic output is retained by hash only; absolute executable paths are reduced to their final component.",
                       "Environment file hashes: " + str(env_files)]}
    evidence[0]["receipt"]["report_schema_version"] = report["schema_version"]
    evidence[0]["receipt"]["projection_profile"] = profile
    evidence[0]["receipt"]["projection_sha256"] = extraction_projection_digest(
        graph, evidence[0]["subject_ids"], profile=profile)
    validate_graph(graph)
    return graph
