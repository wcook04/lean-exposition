#!/usr/bin/env python3
"""Check maintained Git candidates and the repository's entry and package routes.

The working check includes tracked and untracked nonignored files. --index checks
only the staged candidate tree and reads every inspected file from the index.
This is an independent, standard-library implementation.
"""
from __future__ import annotations

import argparse
import fnmatch
import json
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys
import tomllib
from urllib.parse import unquote, urlsplit

POLICY_PATH = "docs/repository_layout.json"


class LayoutError(ValueError):
    """The candidate tree or its policy cannot be inspected."""


def git(root: Path, *args: str) -> bytes:
    try:
        result = subprocess.run(
            ["git", "-C", str(root), *args], capture_output=True, check=False
        )
    except OSError as exc:
        raise LayoutError(f"Git is unavailable: {exc}") from exc
    if result.returncode:
        raise LayoutError("Git inspection failed: " + result.stderr.decode(errors="replace").strip())
    return result.stdout


def portable_path(value: str) -> bool:
    return bool(value) and not value.startswith("/") and "\\" not in value and ":" not in value and all(
        part not in {"", ".", ".."} for part in value.split("/")
    )


class CandidateTree:
    def __init__(self, root: Path, index: bool):
        self.root = root.resolve()
        self.index = index
        top = Path(git(self.root, "rev-parse", "--show-toplevel").decode().strip()).resolve()
        if top != self.root:
            raise LayoutError("--root must name the Git repository root")
        self.entries: dict[str, str] = {}
        for record in git(self.root, "ls-files", "--stage", "-z").split(b"\0"):
            if not record:
                continue
            metadata, name = record.split(b"\t", 1)
            mode, _oid, stage = metadata.decode().split()
            path = name.decode(errors="surrogateescape")
            if stage != "0":
                raise LayoutError(f"unmerged index entry: {path}")
            self.entries[path] = mode
        if not index:
            for name in git(self.root, "ls-files", "--others", "--exclude-standard", "-z").split(b"\0"):
                if name:
                    self.entries.setdefault(name.decode(errors="surrogateescape"), "working")

    def regular_working_file(self, path: str) -> bool:
        candidate = self.root
        for part in PurePosixPath(path).parts:
            candidate /= part
            if candidate.is_symlink():
                return False
        return candidate.is_file()

    def read(self, path: str) -> bytes:
        if path not in self.entries:
            raise LayoutError(f"missing candidate file: {path}")
        if self.index:
            return git(self.root, "show", f":{path}")
        candidate = self.root / path
        if not self.regular_working_file(path):
            raise LayoutError(f"not a regular candidate file: {path}")
        try:
            return candidate.read_bytes()
        except OSError as exc:
            raise LayoutError(f"cannot read candidate file {path}: {exc}") from exc


def read_policy(tree: CandidateTree) -> dict:
    try:
        policy = json.loads(tree.read(POLICY_PATH))
    except (ValueError, UnicodeError) as exc:
        raise LayoutError(f"invalid layout policy: {exc}") from exc
    if not isinstance(policy, dict) or policy.get("schema_version") != "1.0":
        raise LayoutError("layout policy must use schema_version 1.0")
    for field in ("root_files", "directory_roles"):
        value = policy.get(field)
        if not isinstance(value, dict) or not value or any(
            not isinstance(k, str) or "/" in k or not portable_path(k)
            or not isinstance(v, str) or not v.strip() for k, v in value.items()
        ):
            raise LayoutError(f"layout policy {field} must declare names and purposes")
    for field in ("required_paths", "readme_map", "entry_references"):
        value = policy.get(field)
        if not isinstance(value, list) or not value or any(
            not isinstance(p, str) or not portable_path(p.rstrip("/")) for p in value
        ) or len(set(value)) != len(value):
            raise LayoutError(f"layout policy {field} must contain unique relative paths")
    return policy


def readme_targets(text: str) -> set[str]:
    # The map uses ordinary inline Markdown links; hidden comments are not a map.
    text = re.sub(r"<!--.*?-->", "", text, flags=re.S)
    return {
        match[0] or match[1]
        for match in re.findall(r"\]\(\s*(?:<([^>]+)>|([^\s)]+))(?:\s+[^)]*)?\)", text)
    }


def check(root: Path, *, index: bool = False) -> dict:
    errors: list[str] = []
    report = {"ok": False, "mode": "index" if index else "working", "files": 0, "errors": errors}
    try:
        tree = CandidateTree(root, index)
        report["files"] = len(tree.entries)
        policy = read_policy(tree)
        existing = set(tree.entries)
        for path, mode in tree.entries.items():
            if not portable_path(path):
                errors.append(f"nonportable candidate path: {path}")
                continue
            first, slash, _rest = path.partition("/")
            if slash and first not in policy["directory_roles"]:
                errors.append(f"undeclared top-level directory: {first} ({path})")
            elif not slash and path not in policy["root_files"]:
                errors.append(f"unrecognized root file: {path}; place it under its owner or declare the interface")
            if mode not in {"100644", "100755", "working"}:
                errors.append(f"not a regular Git file: {path} (mode {mode})")
            if not index and not tree.regular_working_file(path):
                errors.append(f"missing or nonregular working file: {path}")
        for path in policy["required_paths"]:
            if path not in existing:
                errors.append(f"missing required path: {path}")

        def text(path: str) -> str:
            try:
                return tree.read(path).decode()
            except (LayoutError, UnicodeError) as exc:
                errors.append(str(exc))
                return ""

        targets = readme_targets(text("README.md"))
        local_targets = set()
        for target in sorted(targets):
            try:
                url = urlsplit(target)
            except ValueError:
                errors.append(f"malformed README link: {target}")
                continue
            if url.scheme or url.netloc or not url.path:
                continue
            path = unquote(url.path)
            while path.startswith("./"):
                path = path[2:]
            local_targets.add(path.rstrip("/"))
            if not portable_path(path.rstrip("/")):
                errors.append(f"README link leaves the portable tree: {target}")
            elif path.rstrip("/") not in existing and not any(p.startswith(path.rstrip("/") + "/") for p in existing):
                errors.append(f"README link has no candidate destination: {target}")
        for target in policy["readme_map"]:
            if target.rstrip("/") not in local_targets:
                errors.append(f"README map is missing a link to {target}")
        entry = text("AGENTS.md")
        for reference in policy["entry_references"]:
            if reference not in entry:
                errors.append(f"AGENTS.md is missing its entry reference: {reference}")
        try:
            project = tomllib.loads(text("pyproject.toml"))
            command = project.get("project", {}).get("scripts", {}).get("lean-exposition")
            if command != "lean_exposition.cli:main":
                errors.append("pyproject.toml must expose lean-exposition = lean_exposition.cli:main")
            patterns = project.get("tool", {}).get("setuptools", {}).get("package-data", {}).get("lean_exposition", [])
            if not isinstance(patterns, list) or not all(isinstance(p, str) for p in patterns):
                errors.append("pyproject.toml package-data must be a list of patterns")
            else:
                for path in sorted(existing):
                    if path.startswith("src/lean_exposition/resources/"):
                        relative = str(PurePosixPath(path).relative_to("src/lean_exposition"))
                        if not any(fnmatch.fnmatchcase(relative, pattern) for pattern in patterns):
                            errors.append(f"packaged resource has no package-data pattern: {path}")
        except (tomllib.TOMLDecodeError, TypeError, AttributeError) as exc:
            errors.append(f"invalid package interface: {exc}")
    except (LayoutError, OSError) as exc:
        errors.append(str(exc))
    errors[:] = sorted(set(errors))
    report["ok"] = not errors
    return report


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--index", action="store_true", help="inspect staged candidate names and bytes")
    parser.add_argument("--json", action="store_true", help="emit a machine-readable report")
    args = parser.parse_args(argv)
    report = check(args.root, index=args.index)
    if args.json:
        print(json.dumps(report, indent=2, ensure_ascii=True))
    elif report["ok"]:
        print(f"Layout OK ({report['mode']}; {report['files']} maintained files)")
    else:
        for error in report["errors"]:
            print(f"Layout error: {error}", file=sys.stderr)
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
