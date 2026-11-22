#!/usr/bin/env python3
"""Check this corpus's locked inputs and local replay prerequisites.

This command never installs tools, downloads dependencies, builds Lean, or runs
Comparator. A ready preflight is not proof verification. Invoke after installing
lean-exposition, and keep transient output outside the source checkout.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import platform
import re
import shutil
import subprocess

from lean_exposition.contracts import ContractError
from lean_exposition.intake import audit_sources


def read_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def require_locked_inputs(lock: dict) -> None:
    paths = {row["path"] for row in lock["files"] + lock.get("derived_files", [])}
    required = {
        "upstream/lean/lean-toolchain", "upstream/lean/lakefile.lean",
        "upstream/lean/lake-manifest.json", "upstream/provenance/lake-manifest.json",
        "upstream/provenance/mathlib-lake-manifest.json",
        "upstream/lean/ComparatorChallenges/SKFullSupport.json",
        "upstream/lean/ComparatorChallenges/SKValue.json",
    }
    if not required <= paths:
        raise ValueError("a consumed input is absent from the source lock")


def package_index(manifest: dict) -> dict:
    packages = manifest["packages"]
    names = [row["name"] for row in packages]
    if len(set(names)) != len(names):
        raise ValueError("duplicate dependency name")
    for row in packages:
        if row.get("type") != "git" or not re.fullmatch(r"[0-9a-f]{40}", row.get("rev", "")):
            raise ValueError("dependency is not pinned to a full Git commit")
    return {row["name"]: row for row in packages}


def dependency_pins(example: Path) -> dict:
    """Compare selected immutable pins, not floating inputRev display labels."""
    active = package_index(read_json(example / "upstream/lean/lake-manifest.json"))
    original = package_index(read_json(example / "upstream/provenance/lake-manifest.json"))
    mathlib = package_index(read_json(example / "upstream/provenance/mathlib-lake-manifest.json"))
    if set(active) != set(mathlib) | {"mathlib"}:
        raise ValueError("selected dependency set differs from mathlib's locked closure")
    for name, row in active.items():
        if name not in original:
            raise ValueError(f"dependency absent from upstream lock: {name}")
        references = [original[name]] + ([mathlib[name]] if name in mathlib else [])
        for reference in references:
            for field in ("url", "rev", "subDir", "configFile", "manifestFile"):
                if row.get(field) != reference.get(field):
                    raise ValueError(f"dependency {field} differs from upstream lock: {name}")
    return {"status": "passed", "packages": {
        name: {"url": row["url"], "revision": row["rev"]}
        for name, row in sorted(active.items())
    }, "checkout_bytes_checked": False}


def toolchain_availability(pin: str) -> dict:
    """Query elan's installed list; never invoke an auto-installing Lean shim."""
    if not shutil.which("elan"):
        return {"status": "unavailable", "pin": pin, "reason": "elan_not_found"}
    try:
        result = subprocess.run(
            ["elan", "toolchain", "list"], capture_output=True, text=True,
            timeout=15, check=False,
        )
    except (OSError, subprocess.TimeoutExpired):
        return {"status": "unavailable", "pin": pin, "reason": "installed_list_unavailable"}
    if result.returncode:
        return {"status": "unavailable", "pin": pin, "reason": "installed_list_failed",
                "returncode": result.returncode}
    installed = {line.split()[0] for line in result.stdout.splitlines() if line.strip()}
    return {"status": "passed" if pin in installed else "unavailable", "pin": pin,
            "reason": "exact_pin_installed" if pin in installed else "exact_pin_not_installed"}


def preflight(example: Path) -> dict:
    example = example.resolve()
    result = {
        "schema_version": "1.0",
        "evidence_kind": "corpus_preflight",
        "observed_at": datetime.now(timezone.utc).isoformat(),
        "runner_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "host": {"system": platform.system(), "machine": platform.machine()},
        "lean_build": "not_run",
        "comparator": "not_run",
        "axiom_audit": "not_run",
        "extraction": "not_run",
        "statement_comparison": "not_run",
        "boundary": "Input integrity and prerequisite availability only; no proof was checked.",
    }
    try:
        lock_bytes = (example / "source-lock.json").read_bytes()
        lock = json.loads(lock_bytes)
        if not isinstance(lock, dict):
            raise ValueError("source lock must be an object")
        result["source_lock_sha256"] = hashlib.sha256(lock_bytes).hexdigest()
        result["source_audit"] = audit_sources(lock, example)
        require_locked_inputs(lock)
        result["source_revision"] = lock["revision"]
        result["dependency_pins"] = dependency_pins(example)
        pin = (example / "upstream/lean/lean-toolchain").read_text().strip()
    except (ContractError, ValueError, KeyError, TypeError, OSError) as exc:
        # Do not include local filesystem paths or diagnostic streams in a
        # portable receipt. The failure category is sufficient for preflight.
        result.update(status="failed", reason="locked_input_check_failed",
                      error_type=type(exc).__name__)
        return result
    result["toolchain"] = toolchain_availability(pin)
    result["tools"] = {name: {"available": bool(shutil.which(name))}
                       for name in ("lake", "comparator", "lean4export", "landrun", "systemd-run")}
    result["sandbox"] = {
        "status": "available" if platform.system() == "Linux" else "unavailable",
        "requirement": "Standalone Comparator's documented landrun/systemd sandbox requires Linux.",
        "functional_check": "not_run",
    }
    available = (result["toolchain"]["status"] == "passed"
                 and all(tool["available"] for tool in result["tools"].values())
                 and result["sandbox"]["status"] == "available")
    result["status"] = "ready" if available else "unavailable"
    result["tool_compatibility"] = "not_checked"
    result["dependency_checkouts"] = "not_checked"
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--out", type=Path)
    args = parser.parse_args()
    result = preflight(args.root)
    payload = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.out:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(payload, encoding="utf-8")
    print(payload, end="")
    return 0 if result["status"] == "ready" else 2 if result["status"] == "unavailable" else 1


if __name__ == "__main__":
    raise SystemExit(main())
