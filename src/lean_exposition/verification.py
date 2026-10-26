"""Run local Lean tools and retain their distinct evidence boundaries.

Extraction loads trusted project code into Lean. Comparator's default command
uses the sandbox supplied by the selected Lean toolchain. Neither operation
establishes correspondence with an informal mathematical statement.
"""

from __future__ import annotations

import hashlib
from importlib import resources
import json
import math
import os
from pathlib import Path
import re
import signal
import shutil
import subprocess
import tempfile
from typing import Any, Sequence

from .contracts import ContractError, decode_json, validate_extraction_report


class VerificationError(RuntimeError):
    """A tool failed or did not return a usable report; receipt retains why."""

    def __init__(self, message: str, receipt: dict[str, Any]):
        super().__init__(message)
        self.receipt = receipt


class _ProcessLaunchError(RuntimeError):
    """Popen could not launch a usable tool process."""

    def __init__(self, error: OSError):
        super().__init__(str(error))
        self.error = error


def _text(value: str | bytes | None) -> str:
    if isinstance(value, bytes):
        return value.decode("utf-8", errors="replace")
    return value or ""


def _execute(
    args: list[str], project: Path, input_text: str | None, timeout: float,
) -> subprocess.CompletedProcess[bytes]:
    # Collect this invocation and its process group after a deadline. This is
    # lifecycle cleanup, not containment of children that escape that group.
    try:
        process = subprocess.Popen(
            args, cwd=project, stdin=subprocess.PIPE if input_text is not None else None,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            start_new_session=os.name == "posix",
        )
    except OSError as exc:
        raise _ProcessLaunchError(exc) from exc
    cleanup_errors = []

    def signal_invocation(*, force: bool = False) -> None:
        try:
            if os.name == "posix":
                os.killpg(process.pid, signal.SIGKILL if force else signal.SIGTERM)
            elif not force:
                process.terminate()
            else:
                process.kill()
        except ProcessLookupError:
            # The launcher can exit before timeout cleanup; a surviving child
            # may still hold its pipes. This is not a new launch failure.
            pass
        except OSError as exc:
            cleanup_errors.append({"operation": "kill" if force else "terminate",
                                   "error_type": type(exc).__name__, "errno": exc.errno})

    try:
        stdout, stderr = process.communicate(
            input=input_text.encode("utf-8") if input_text is not None else None, timeout=timeout)
    except subprocess.TimeoutExpired:
        signal_invocation()
        pipes_drained = True
        try:
            stdout, stderr = process.communicate(timeout=2)
        except subprocess.TimeoutExpired:
            signal_invocation(force=True)
            try:
                stdout, stderr = process.communicate(timeout=2)
            except subprocess.TimeoutExpired as remainder:
                # Escaped/detached descendants can retain pipe descriptors.
                # Do not wait indefinitely or claim their containment.
                stdout, stderr = remainder.output, remainder.stderr
                pipes_drained = False
                for stream in (process.stdin, process.stdout, process.stderr):
                    if stream is not None:
                        stream.close()
                try:
                    process.wait(timeout=2)
                except subprocess.TimeoutExpired:
                    pass
        error = subprocess.TimeoutExpired(args, timeout, output=stdout, stderr=stderr)
        error.cleanup = {"parent_reaped": process.poll() is not None,
                         "pipes_drained": pipes_drained,
                         "scope": "invocation_process_group",
                         "signal_errors": cleanup_errors}
        raise error from None
    except BaseException:
        if process.poll() is None:
            signal_invocation(force=True)
        try:
            process.communicate(timeout=2)
        except subprocess.TimeoutExpired:
            for stream in (process.stdin, process.stdout, process.stderr):
                if stream is not None:
                    stream.close()
        raise
    return subprocess.CompletedProcess(args, process.returncode, stdout, stderr)


def _stream_fields(stdout: str | bytes | None, stderr: str | bytes | None) -> dict[str, Any]:
    """Retain byte identities even when diagnostics are not valid UTF-8."""
    result: dict[str, Any] = {"output_decoding": "utf-8-with-replacement"}
    for name, value in (("stdout", stdout), ("stderr", stderr)):
        result[name] = _text(value)
        if isinstance(value, bytes):
            raw = value
        else:
            try:
                raw = (value or "").encode("utf-8")
            except UnicodeEncodeError:
                # Only non-process providers (for example test doubles) can
                # return an unencodable Python string. Do not invent raw bytes.
                result[name + "_utf8_valid"] = False
                continue
        result[name + "_bytes_sha256"] = hashlib.sha256(raw).hexdigest()
        try:
            raw.decode("utf-8")
            result[name + "_utf8_valid"] = True
        except UnicodeDecodeError:
            result[name + "_utf8_valid"] = False
    return result


def _run(
    command: Sequence[str], project: Path, timeout: float,
    *, input_text: str | None = None,
) -> dict[str, Any]:
    args = [str(x) for x in command]
    if not args:
        raise ValueError("tool command must not be empty")
    try:
        result = _execute(args, project, input_text, timeout)
    except _ProcessLaunchError as exc:
        return {"status": "unavailable", "process_status": "unavailable", "command": args,
                "returncode": None, **_stream_fields("", str(exc)),
                "failure_stage": "process_launch", "failure_reason": "process_launch_failed",
                "error_type": type(exc.error).__name__, "errno": exc.error.errno}
    except FileNotFoundError as exc:
        return {"status": "unavailable", "process_status": "unavailable", "command": args,
                "returncode": None, **_stream_fields("", str(exc)),
                "failure_stage": "process_launch", "failure_reason": "process_launch_failed",
                "error_type": type(exc).__name__, "errno": exc.errno}
    except subprocess.TimeoutExpired as exc:
        return {"status": "timed_out", "process_status": "timed_out", "command": args,
                "returncode": None, **_stream_fields(exc.stdout, exc.stderr),
                "failure_stage": "process_timeout",
                "cleanup": getattr(exc, "cleanup", {"scope": "not_observed"})}
    status = "passed" if result.returncode == 0 else "failed"
    return {"status": status, "process_status": status, "command": args,
            "returncode": result.returncode, **_stream_fields(result.stdout, result.stderr)}


def _identifier(value: str) -> str:
    # Validate only generated Lean syntax, never infer dependencies from text.
    if not re.fullmatch(r"[^\W\d]\w*(?:'\w*)*(?:\.[^\W\d]\w*(?:'\w*)*)*", value):
        raise ValueError(f"expected a dotted Lean identifier: {value!r}")
    return value


def _source_hashes(project: Path) -> dict[str, str]:
    """Snapshot project Lean sources and its environment, excluding caches."""
    paths: set[Path] = set()
    def walk_error(error: OSError) -> None:
        raise error
    for base, dirs, files in os.walk(project, onerror=walk_error):
        dirs[:] = sorted(d for d in dirs if d not in {".lake", ".git", ".venv", "__pycache__"})
        paths.update(Path(base) / name for name in files if name.endswith(".lean"))
    for name in ("lean-toolchain", "lakefile.lean", "lakefile.toml", "lake-manifest.json"):
        path = project / name
        if path.is_file():
            paths.add(path)
    return {path.relative_to(project).as_posix(): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in sorted(paths)}


def _bind_sources(receipt: dict[str, Any], project: Path, before: dict[str, str]) -> None:
    receipt["source_hashes"] = before
    try:
        after = _source_hashes(project)
    except OSError as exc:
        receipt["source_changed"] = None
        receipt["source_snapshot_error"] = {"error_type": type(exc).__name__, "errno": exc.errno}
        if receipt["status"] == "passed":
            receipt["status"] = "failed"
            receipt["failure_stage"] = "receipt_binding"
            receipt["failure_reason"] = "source_snapshot_unavailable"
        return
    receipt["source_changed"] = before != after
    if before != after:
        receipt["status"] = "failed"
        receipt["failure_stage"] = "receipt_binding"
        receipt["failure_reason"] = "source_changed_during_run"
        receipt["changed_paths"] = sorted(
            path for path in before.keys() | after.keys() if before.get(path) != after.get(path)
        )
        receipt["source_hashes_after"] = after


def _run_bound(
    command: Sequence[str], project: Path, timeout: float,
) -> dict[str, Any]:
    """Retain a no-run or executed receipt even if a source snapshot fails."""
    try:
        finite_timeout = math.isfinite(timeout)
    except (TypeError, ValueError, OverflowError):
        finite_timeout = False
    if not finite_timeout:
        return {"status": "failed", "process_status": "not_run",
                "command": [str(token) for token in command], "returncode": None,
                "stdout": "", "stderr": "",
                "source_hashes": {}, "source_changed": None,
                "failure_stage": "input_validation", "failure_reason": "invalid_timeout"}
    try:
        before = _source_hashes(project)
    except OSError as exc:
        return {"status": "failed", "process_status": "not_run", "command": list(command),
                "returncode": None, "stdout": "", "stderr": "",
                "source_hashes": {}, "source_changed": None,
                "failure_stage": "input_snapshot", "failure_reason": "source_snapshot_unavailable",
                "source_snapshot_error": {"error_type": type(exc).__name__, "errno": exc.errno}}
    receipt = _run(command, project, timeout)
    _bind_sources(receipt, project, before)
    return receipt


def _lean_names(values: Sequence[str]) -> str:
    return "#[" + ", ".join("`" + _identifier(v) for v in values) + "]"


def _render_extractor_source(
    template: str, module: str, roots: Sequence[str], module_prefixes: Sequence[str],
    *, max_declarations: int = 1000,
) -> str:
    """Generate an import header and the packaged Lean extraction template."""
    _identifier(module)
    if not roots:
        raise ValueError("at least one root declaration is required")
    if type(max_declarations) is not int or max_declarations < 1:
        raise ValueError("max_declarations must be positive")
    source = template.replace("__LEAN_EXPOSITION_ROOTS__", _lean_names(roots))
    source = source.replace("__LEAN_EXPOSITION_PREFIXES__", _lean_names(module_prefixes))
    source = source.replace("__LEAN_EXPOSITION_LIMIT__", str(max_declarations))
    source = source.replace("__LEAN_EXPOSITION_MODULE__", json.dumps(module, ensure_ascii=False))
    source = source.replace("__LEAN_EXPOSITION_TARGET__", "`" + module)
    # Target data is imported by Lean's environment API with private bodies;
    # compiler implementation data need not be imported into this wrapper.
    imports = (
        "prelude\n"
        "import Lean.CoreM\n"
        "import Lean.Util.CollectAxioms\n"
        "import Lean.Util.FoldConsts\n"
        "import Lean.DeclarationRange\n"
    )
    return imports + "\n" + source


def _extractor_template() -> str:
    return resources.files("lean_exposition").joinpath(
        "resources/lean/Extract.lean"
    ).read_text(encoding="utf-8")


def _decode_extraction_stdout(stdout: str) -> dict[str, Any]:
    """Read one protocol report while allowing surrounding diagnostic lines."""
    marker = "LEAN_EXPOSITION_JSON:"
    # The wire protocol uses LF-delimited lines. Other Unicode line-separator
    # characters may occur unescaped inside a valid JSON string.
    lines = [line[len(marker):] for line in stdout.split("\n") if line.startswith(marker)]
    if len(lines) != 1:
        raise ContractError("Lean did not emit exactly one extraction report")
    try:
        report = decode_json(lines[0].encode("utf-8"))
    except (ValueError, RecursionError) as exc:
        raise ContractError("Lean emitted invalid extraction JSON") from exc
    if not isinstance(report, dict):
        raise ContractError("Lean extraction report must be an object")
    return report


def extractor_source(
    module: str, roots: Sequence[str], module_prefixes: Sequence[str],
    *, max_declarations: int = 1000,
) -> str:
    """Generate an import header and the packaged Lean extraction template."""
    return _render_extractor_source(_extractor_template(), module, roots, module_prefixes,
                                    max_declarations=max_declarations)


def extract_dependencies(
    project: Path | str, module: str, roots: Sequence[str], *,
    module_prefixes: Sequence[str] | None = None,
    lean_command: Sequence[str] | None = None,
    timeout: float = 120,
    max_declarations: int = 1000,
) -> dict[str, Any]:
    """Extract a bounded elaborated dependency graph from prebuilt modules.

    ``lean_command`` is the prefix before the generated driver's filename.
    The default is ``lake env lean --run`` and obeys the project's toolchain.
    No build or toolchain download is initiated explicitly by this function.
    ``lake``/``elan`` may themselves resolve a missing toolchain: inspect the
    pin before executing a project. This operation is for trusted source.
    """
    project = Path(project).resolve()
    prefixes = tuple(module_prefixes) if module_prefixes is not None else (module,)
    template = _extractor_template()
    source = _render_extractor_source(template, module, roots, prefixes, max_declarations=max_declarations)
    command = tuple(lean_command) if lean_command is not None else (
        "lake", "env", "lean", "--run",
    )
    with tempfile.TemporaryDirectory(prefix="lean-exposition-") as driver_dir:
        driver = Path(driver_dir) / "LeanExpositionDriver.lean"
        driver.write_text(source, encoding="utf-8")
        receipt = _run_bound([*command, str(driver)], project, timeout)
        receipt["command_sha256"] = hashlib.sha256(json.dumps(
            {"command": receipt["command"]}, indent=2, ensure_ascii=False,
            sort_keys=True).encode() + b"\n").hexdigest()
        receipt["command"][-1] = driver.name
        receipt["command_paths_redacted"] = True
    receipt["module"] = module
    receipt["evidence_kind"] = "elaboration_process"
    receipt["extraction_request"] = {"module": module, "roots": list(roots),
                                      "module_prefixes": list(prefixes),
                                      "max_declarations": max_declarations}
    receipt["extractor_template_sha256"] = hashlib.sha256(template.encode("utf-8")).hexdigest()
    receipt["extractor_sha256"] = hashlib.sha256(source.encode()).hexdigest()
    if receipt["status"] != "passed":
        raise VerificationError("Lean dependency extraction did not succeed", receipt)
    def invalid_report(message: str) -> VerificationError:
        receipt["status"] = "failed"
        receipt["failure_reason"] = "invalid_extraction_report"
        return VerificationError(message, receipt)

    if receipt.get("stdout_utf8_valid") is False:
        raise invalid_report("Lean emitted invalid extraction JSON: stdout is not UTF-8")
    try:
        report = _decode_extraction_stdout(receipt["stdout"])
    except ContractError as exc:
        raise invalid_report(str(exc)) from exc
    if "receipt" in report:
        raise invalid_report("Lean extraction report contains a reserved receipt field")
    try:
        validate_extraction_report(report)
    except ContractError as exc:
        raise invalid_report(str(exc)) from exc
    if report["schema_version"] != 2:
        raise invalid_report("current extractor requires version 2 safety metadata")
    if report["module"] != module:
        raise invalid_report("Lean emitted an unexpected extraction report")
    if report["roots"] != list(roots) or report["module_prefixes"] != list(prefixes):
        raise invalid_report("Lean report roots or module prefixes differ from the request")
    if len(report["declarations"]) > max_declarations:
        raise invalid_report("Lean report exceeds the requested declaration limit")
    try:
        canonical = json.dumps(report, indent=2, ensure_ascii=False, sort_keys=True) + "\n"
        receipt["report_sha256"] = hashlib.sha256(canonical.encode("utf-8")).hexdigest()
        receipt["report_schema_version"] = report["schema_version"]
    except (ValueError, RecursionError) as exc:
        raise invalid_report("Lean extraction report is not canonical UTF-8 JSON") from exc
    report["receipt"] = receipt
    return report


def check_build(
    project: Path | str, module: str, *,
    lake_command: Sequence[str] = ("lake",), timeout: float = 120,
) -> dict[str, Any]:
    """Build exactly the requested module; a build is its own evidence class."""
    _identifier(module)
    project = Path(project).resolve()
    receipt = _run_bound([*lake_command, "build", module], project, timeout)
    receipt["module"] = module
    receipt["evidence_kind"] = "lean_build"
    return receipt


def _file_observation(path: Path) -> tuple[dict[str, Any], bytes | None]:
    try:
        data = path.read_bytes()
    except OSError as exc:
        return {"status": "unavailable", "sha256": None,
                "error_type": type(exc).__name__, "errno": exc.errno}, None
    return {"status": "read", "sha256": hashlib.sha256(data).hexdigest()}, data


def _comparator_scope(data: bytes | None) -> dict[str, Any]:
    """Observe known configuration fields; this is not a target-to-paper map."""
    if data is None:
        return {"status": "unavailable"}
    try:
        config = decode_json(data)
        json.dumps(config, ensure_ascii=False).encode("utf-8")
        if not isinstance(config, dict):
            raise ValueError("configuration must be an object")
        for key in ("challenge_module", "solution_module"):
            if not isinstance(config.get(key), str) or not config[key].strip():
                raise ValueError(f"{key} must be a nonempty string")
        definitions = config.get("definition_names")
        definitions = [] if definitions is None else definitions
        for key in ("theorem_names", "permitted_axioms", "definition_names"):
            value = definitions if key == "definition_names" else config.get(key)
            if not isinstance(value, list) or any(not isinstance(x, str) or not x for x in value):
                raise ValueError(f"{key} must be an array of nonempty strings")
        if not config["theorem_names"] and not definitions:
            raise ValueError("configuration selects no theorem or definition targets")
        kernels = config.get("external_kernels")
        kernels = {} if kernels is None else kernels
        if not isinstance(kernels, dict) or any(
            not isinstance(name, str) or not name or not isinstance(cmd, list) or not cmd
            or any(not isinstance(arg, str) for arg in cmd) or not cmd[0]
            for name, cmd in kernels.items()
        ):
            raise ValueError("external_kernels must contain nonempty command arrays")
        nanoda = config.get("enable_nanoda")
        nanoda = False if nanoda is None else nanoda
        if type(nanoda) is not bool:
            raise ValueError("enable_nanoda must be a Boolean")
        if nanoda and kernels:
            raise ValueError("enable_nanoda cannot be combined with external_kernels")
        scope = {"challenge_module": config["challenge_module"],
                 "solution_module": config["solution_module"],
                 "theorem_names": config["theorem_names"],
                 "definition_names": definitions,
                 "permitted_axioms": config["permitted_axioms"],
                 "external_kernels": kernels, "enable_nanoda": nanoda}
        # The byte digest binds the whole JSON, including unknown fields. The
        # observation does not claim a complete parser for every checker version.
        return {"status": "observed", "scope": scope,
                "unknown_fields": sorted(set(config) - set(scope)),
                "claim_association": "not_checked"}
    except (ContractError, ValueError, UnicodeError) as exc:
        return {"status": "invalid", "reason": str(exc)}


def _launch_observation(program: str, project: Path) -> dict[str, Any]:
    """Observe only the first executable, never infer a nested checker identity."""
    try:
        if os.path.dirname(program):
            candidate = Path(program)
            candidate = candidate if candidate.is_absolute() else project / candidate
        else:
            # POSIX resolves relative PATH entries from the child's cwd.
            search_path = os.pathsep.join(
                str(Path(entry) if Path(entry).is_absolute() else project / entry)
                for entry in os.get_exec_path()
            )
            located = shutil.which(program, path=search_path)
            if located is None:
                return {"status": "unavailable", "requested": program, "sha256": None}
            candidate = Path(located)
        resolved = candidate.resolve()
        observation, _ = _file_observation(candidate)
        return {**observation, "requested": program, "path": str(candidate),
                "resolved_path": str(resolved)}
    except (OSError, RuntimeError) as exc:
        return {"status": "unavailable", "requested": program, "sha256": None,
                "error_type": type(exc).__name__}


def verify_comparator(
    project: Path | str, config: Path | str, *,
    command: Sequence[str] | None = None, timeout: float = 120,
) -> dict[str, Any]:
    """Run Comparator and retain process, input-binding and scope observations.

    Default prefix: ``lake comparator --config`` (Lean >= 4.35).
    Legacy prefix: ``["comparator"]``. ``config`` is always appended.
    The caller must select binaries compatible with the project's toolchain.
    No sandbox-disabling flag is added automatically. ``passed`` records zero
    process exit with usable, stable observed bindings; the caller must still
    establish effective checker identity, stages, caches and sandbox controls.
    """
    project = Path(project).resolve()
    config = Path(config)
    config_path = config if config.is_absolute() else project / config
    prefix = tuple(command) if command is not None else ("lake", "comparator", "--config")
    if not prefix:
        raise ValueError("Comparator command prefix must not be empty")
    config_before, config_bytes = _file_observation(config_path)
    scope = _comparator_scope(config_bytes)
    launch_before = _launch_observation(str(prefix[0]), project)
    receipt = _run_bound([*prefix, str(config)], project, timeout)
    config_after, _ = _file_observation(config_path)
    launch_after = _launch_observation(str(prefix[0]), project)
    receipt["receipt_profile"] = "comparator-process-v2"
    receipt["evidence_kind"] = "comparator"
    receipt["sandbox_disabled_explicitly"] = "--inadvisably-no-sandbox" in prefix
    receipt["config_sha256"] = config_before["sha256"]
    receipt["config_sha256_after"] = config_after["sha256"]
    receipt["config_observation"] = scope
    receipt["config_read_before"] = config_before
    receipt["config_read_after"] = config_after
    receipt["launch_executable_before"] = launch_before
    receipt["launch_executable_after"] = launch_after
    receipt["assurance"] = {
        "status_meaning": "process_exit_and_observed_bindings",
        "effective_checker_identity": "not_established",
        "inner_stage_outcome": "not_established",
        "sandbox_controls": "not_established",
        "compiled_import_identity": "not_established",
        "paper_claim_correspondence": "not_checked",
    }
    if command is None and receipt["returncode"] == 2 and receipt["source_changed"] is False:
        receipt["status"] = "unavailable"
        receipt["failure_stage"] = "checker_start"
    elif receipt["status"] == "failed" and "failure_stage" not in receipt:
        receipt["failure_stage"] = "unknown"
    config_changed = config_before["sha256"] != config_after["sha256"]
    receipt["config_changed"] = config_changed
    launch_changed = launch_before != launch_after
    receipt["launch_executable_changed"] = launch_changed
    if config_changed:
        receipt["status"] = "failed"
        receipt["failure_stage"] = "receipt_binding"
        receipt["failure_reason"] = "config_changed_during_run"
    elif receipt["status"] == "passed" and scope["status"] != "observed":
        receipt["status"] = "failed"
        receipt["failure_stage"] = "receipt_binding"
        receipt["failure_reason"] = "configuration_scope_unavailable"
    if launch_changed:
        receipt["status"] = "failed"
        receipt["failure_stage"] = "receipt_binding"
        receipt["failure_reason"] = "launch_executable_changed_during_run"
    elif receipt["status"] == "passed" and launch_before["status"] != "read":
        receipt["status"] = "failed"
        receipt["failure_stage"] = "receipt_binding"
        receipt["failure_reason"] = "launch_executable_identity_unavailable"
    return receipt
