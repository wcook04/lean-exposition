"""Run local Lean tools and retain their distinct evidence boundaries.

Extraction loads trusted project code into Lean. Comparator's default command
uses the sandbox supplied by the selected Lean toolchain. Neither operation
establishes correspondence with an informal mathematical statement.
"""

from __future__ import annotations

import hashlib
from importlib import resources
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import tempfile
from typing import Any, Sequence


class VerificationError(RuntimeError):
    """A tool failed or did not return a usable report; receipt retains why."""

    def __init__(self, message: str, receipt: dict[str, Any]):
        super().__init__(message)
        self.receipt = receipt


def _text(value: str | bytes | None) -> str:
    if isinstance(value, bytes):
        return value.decode("utf-8", errors="replace")
    return value or ""


def _execute(
    args: list[str], project: Path, input_text: str | None, timeout: float,
) -> subprocess.CompletedProcess[str]:
    # Kill this invocation's descendants too when a Lake child exceeds its
    # deadline; never leave a Lean build running after reporting a timeout.
    process = subprocess.Popen(
        args, cwd=project, stdin=subprocess.PIPE if input_text is not None else None,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
        start_new_session=os.name == "posix",
    )
    try:
        stdout, stderr = process.communicate(input=input_text, timeout=timeout)
    except subprocess.TimeoutExpired:
        if os.name == "posix":
            os.killpg(process.pid, signal.SIGTERM)
        else:
            process.terminate()
        try:
            stdout, stderr = process.communicate(timeout=2)
        except subprocess.TimeoutExpired:
            if os.name == "posix":
                os.killpg(process.pid, signal.SIGKILL)
            else:
                process.kill()
            stdout, stderr = process.communicate()
        raise subprocess.TimeoutExpired(args, timeout, output=stdout, stderr=stderr) from None
    except BaseException:
        if process.poll() is None:
            if os.name == "posix":
                os.killpg(process.pid, signal.SIGKILL)
            else:
                process.kill()
        process.communicate()
        raise
    return subprocess.CompletedProcess(args, process.returncode, stdout, stderr)


def _run(
    command: Sequence[str], project: Path, timeout: float,
    *, input_text: str | None = None,
) -> dict[str, Any]:
    args = [str(x) for x in command]
    if not args:
        raise ValueError("tool command must not be empty")
    try:
        result = _execute(args, project, input_text, timeout)
    except FileNotFoundError as exc:
        return {"status": "unavailable", "command": args, "returncode": None,
                "stdout": "", "stderr": str(exc)}
    except subprocess.TimeoutExpired as exc:
        return {"status": "timed_out", "command": args, "returncode": None,
                "stdout": _text(exc.stdout), "stderr": _text(exc.stderr)}
    return {"status": "passed" if result.returncode == 0 else "failed",
            "command": args, "returncode": result.returncode,
            "stdout": result.stdout, "stderr": result.stderr}


def _identifier(value: str) -> str:
    # Validate only generated Lean syntax, never infer dependencies from text.
    if not re.fullmatch(r"[^\W\d]\w*(?:'\w*)*(?:\.[^\W\d]\w*(?:'\w*)*)*", value):
        raise ValueError(f"expected a dotted Lean identifier: {value!r}")
    return value


def _source_hashes(project: Path) -> dict[str, str]:
    """Snapshot project Lean sources and its environment, excluding caches."""
    paths: set[Path] = set()
    for base, dirs, files in os.walk(project):
        dirs[:] = sorted(d for d in dirs if d not in {".lake", ".git", ".venv", "__pycache__"})
        paths.update(Path(base) / name for name in files if name.endswith(".lean"))
    for name in ("lean-toolchain", "lakefile.lean", "lakefile.toml", "lake-manifest.json"):
        path = project / name
        if path.is_file():
            paths.add(path)
    return {path.relative_to(project).as_posix(): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in sorted(paths)}


def _bind_sources(receipt: dict[str, Any], project: Path, before: dict[str, str]) -> None:
    after = _source_hashes(project)
    receipt["source_hashes"] = before
    receipt["source_changed"] = before != after
    if before != after:
        receipt["status"] = "failed"
        receipt["failure_reason"] = "source_changed_during_run"
        receipt["changed_paths"] = sorted(
            path for path in before.keys() | after.keys() if before.get(path) != after.get(path)
        )


def _lean_names(values: Sequence[str]) -> str:
    return "#[" + ", ".join("`" + _identifier(v) for v in values) + "]"


def extractor_source(
    module: str, roots: Sequence[str], module_prefixes: Sequence[str],
    *, max_declarations: int = 1000,
) -> str:
    """Generate an import header and the packaged Lean extraction template."""
    _identifier(module)
    if not roots:
        raise ValueError("at least one root declaration is required")
    if max_declarations < 1:
        raise ValueError("max_declarations must be positive")
    template = resources.files("lean_exposition").joinpath(
        "resources/lean/Extract.lean"
    ).read_text(encoding="utf-8")
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
    source = extractor_source(module, roots, prefixes, max_declarations=max_declarations)
    command = tuple(lean_command) if lean_command is not None else (
        "lake", "env", "lean", "--run",
    )
    before = _source_hashes(project)
    with tempfile.TemporaryDirectory(prefix="lean-exposition-") as driver_dir:
        driver = Path(driver_dir) / "LeanExpositionDriver.lean"
        driver.write_text(source, encoding="utf-8")
        receipt = _run([*command, str(driver)], project, timeout)
        receipt["command_sha256"] = hashlib.sha256(json.dumps(
            {"command": receipt["command"]}, indent=2, ensure_ascii=False,
            sort_keys=True).encode() + b"\n").hexdigest()
        receipt["command"][-1] = driver.name
        receipt["command_paths_redacted"] = True
    _bind_sources(receipt, project, before)
    receipt["module"] = module
    receipt["evidence_kind"] = "elaboration_process"
    receipt["extractor_sha256"] = hashlib.sha256(source.encode()).hexdigest()
    if receipt["status"] != "passed":
        raise VerificationError("Lean dependency extraction did not succeed", receipt)
    def invalid_report(message: str) -> VerificationError:
        receipt["status"] = "failed"
        receipt["failure_reason"] = "invalid_extraction_report"
        return VerificationError(message, receipt)

    marker = "LEAN_EXPOSITION_JSON:"
    lines = [line[len(marker):] for line in receipt["stdout"].splitlines()
             if line.startswith(marker)]
    if len(lines) != 1:
        raise invalid_report("Lean did not emit exactly one extraction report")
    try:
        report = json.loads(lines[0])
    except json.JSONDecodeError as exc:
        raise invalid_report("Lean emitted invalid extraction JSON") from exc
    if not isinstance(report, dict) or report.get("schema_version") != 1 or report.get("module") != module:
        raise invalid_report("Lean emitted an unexpected extraction report")
    if report.get("roots") != list(roots) or report.get("module_prefixes") != list(prefixes):
        raise invalid_report("Lean report roots or module prefixes differ from the request")
    names = {d.get("name") for d in report.get("declarations", []) if isinstance(d, dict)}
    pending = set(report.get("unexpanded_declarations", []))
    if any(root not in names | pending for root in roots):
        raise invalid_report("Lean report omits a requested root declaration")
    if report.get("scope_complete") is True and (
        report.get("missing_declarations") or pending or report.get("unavailable_bodies")
    ):
        raise invalid_report("Lean report claims complete scope with unresolved declarations")
    canonical = json.dumps(report, indent=2, ensure_ascii=False, sort_keys=True) + "\n"
    receipt["report_sha256"] = hashlib.sha256(canonical.encode("utf-8")).hexdigest()
    report["receipt"] = receipt
    return report


def check_build(
    project: Path | str, module: str, *,
    lake_command: Sequence[str] = ("lake",), timeout: float = 120,
) -> dict[str, Any]:
    """Build exactly the requested module; a build is its own evidence class."""
    _identifier(module)
    project = Path(project).resolve()
    before = _source_hashes(project)
    receipt = _run([*lake_command, "build", module], project, timeout)
    _bind_sources(receipt, project, before)
    receipt["module"] = module
    receipt["evidence_kind"] = "lean_build"
    return receipt


def verify_comparator(
    project: Path | str, config: Path | str, *,
    command: Sequence[str] | None = None, timeout: float = 120,
) -> dict[str, Any]:
    """Run a real Comparator command and retain its unmodified verdict.

    Default prefix: ``lake comparator --config`` (Lean >= 4.35).
    Legacy prefix: ``["comparator"]``. ``config`` is always appended.
    The caller must select binaries compatible with the project's toolchain.
    No sandbox-disabling flag is added automatically.
    """
    project = Path(project).resolve()
    config = Path(config)
    config_path = config if config.is_absolute() else project / config
    prefix = tuple(command) if command is not None else ("lake", "comparator", "--config")
    before = _source_hashes(project)
    config_before = hashlib.sha256(config_path.read_bytes()).hexdigest() if config_path.is_file() else None
    receipt = _run([*prefix, str(config)], project, timeout)
    _bind_sources(receipt, project, before)
    receipt["evidence_kind"] = "comparator"
    receipt["sandbox_disabled_explicitly"] = "--inadvisably-no-sandbox" in prefix
    if command is None and receipt["returncode"] == 2 and not receipt["source_changed"]:
        receipt["status"] = "unavailable"
    config_after = hashlib.sha256(config_path.read_bytes()).hexdigest() if config_path.is_file() else None
    receipt["config_sha256"] = config_before
    if config_before != config_after:
        receipt["status"] = "failed"
        receipt["source_changed"] = True
        receipt["failure_reason"] = "source_changed_during_run"
    return receipt
