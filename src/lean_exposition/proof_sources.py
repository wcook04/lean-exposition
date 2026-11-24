"""Pinned Lean module data for the paper-linked part of a compiled proof."""
from __future__ import annotations

from collections import defaultdict
from hashlib import sha256
import json
from pathlib import Path, PurePosixPath
import re
import subprocess
from urllib.parse import quote

from .lean_index import module_view, modules_view, names_view, parse_module


NEIGHBOURHOOD_LIMIT = 12


def _git(checkout: Path, *args: str) -> bytes:
    result = subprocess.run(
        ["git", "--no-replace-objects", "-C", str(checkout), *args],
        capture_output=True, check=False,
    )
    if result.returncode:
        raise ValueError(f"Cannot read the pinned Lean checkout ({' '.join(args)})")
    return result.stdout


def _checked_asset(directory, manifest, filename):
    raw = (directory / filename).read_bytes()
    if sha256(raw).hexdigest() != manifest["files"].get(filename):
        raise ValueError(f"{filename} does not match the RH paper manifest")
    return json.loads(raw)


def _source_declarations(items, parsed, references, consumers, last_line):
    by_name = {row["name"]: row for row in parsed["declarations"]}
    declarations = []
    for item in sorted(items, key=lambda row: (*row["lines"], row["name"])):
        name = item["name"]
        first, last = item["lines"]
        if not 1 <= first <= last <= last_line:
            raise ValueError(f"{name} is outside its pinned Lean module")
        authored = item.get("statement_lines")
        syntax = by_name.get(name)
        syntax = syntax if syntax and first <= syntax["line"] <= last else None
        if authored:
            signature, boundary = authored[1], "paper_alignment"
        elif syntax and first <= syntax["signature_end_line"] <= last:
            signature, boundary = syntax["signature_end_line"], "source_syntax"
        else:
            signature, boundary = last, "whole_declaration"
        if not first <= signature <= last:
            raise ValueError(f"{name} has an invalid statement boundary")
        namespace, _, short = name.rpartition(".")
        declarations.append({
            "name": name, "short": short, "namespace": namespace, "kind": item["kind"],
            "line": first, "end_line": last, "signature_end_line": signature,
            "signature_source": boundary, "doc": syntax["doc"] if syntax else None,
            "private": syntax["private"] if syntax else name.startswith("_private."),
            "uses": references.get(name, []), "used_by": consumers.get(name, []),
            **({"dependency_source": "elaborated"} if name in references else {}),
            "in_proof": item["in_proof"],
        })
    return declarations


class ProofSources:
    """Capture the edition's linked modules once and serve them without reading Git per request."""

    def __init__(self, checkout: Path, paper: Path, proof, *, reader_config: Path | None = None):
        revision = proof.manifest["revision"]
        if not re.fullmatch(r"[0-9a-f]{40}", revision):
            raise ValueError("The proof index must pin a full Git revision")
        if _git(checkout, "rev-parse", "--verify", f"{revision}^{{commit}}").decode().strip() != revision:
            raise ValueError("The Lean checkout does not contain the pinned proof revision")
        raw = (paper / "manifest.json").read_bytes()
        manifest = json.loads(raw)
        self.paper_manifest_sha256 = sha256(raw).hexdigest()
        if manifest["lean"]["revision"] != revision:
            raise ValueError("The paper and proof index use different Lean revisions")
        paper_revision = manifest["paper"]["revision"]
        notes = _checked_asset(paper, manifest, "lean-notes.json")
        line_data = _checked_asset(paper, manifest, "lean-lines.json")
        for asset in (notes, line_data):
            if asset["lean_revision"] != revision or asset["paper_revision"] != paper_revision:
                raise ValueError("The paper links use a different edition")

        grouped = defaultdict(list)
        bindings = notes["bindings"]
        titles = {}
        self.graph_titles = {}
        if reader_config is not None:
            reader = json.loads(reader_config.read_bytes())
            if reader["revision"] != revision:
                raise ValueError("Reader titles and Lean source catalogue use different revisions")
            titles = {name: label[0] for name, label in reader["labels"].items()
                      if isinstance(label, list) and label and isinstance(label[0], str) and label[0].strip()}
            if missing := sorted(bindings.keys() - titles.keys()):
                raise ValueError(f"Missing display title for {missing[0]}")
            graph_titles = reader.get("graph_titles", {})
            if not isinstance(graph_titles, dict) or any(
                not name or not isinstance(title, str) or not title or title != title.strip()
                or any(ord(char) < 32 for char in title)
                for name, title in graph_titles.items()
            ):
                raise ValueError("Graph titles must map exact names to single-line titles")
            if repeated := sorted(graph_titles.keys() & titles.keys()):
                raise ValueError(f"Graph title repeats a reader label for {repeated[0]}")
            if graph_titles and (unknown := sorted(graph_titles.keys() - proof.known_names(graph_titles))):
                raise ValueError(f"No compiled graph declaration for {unknown[0]}")
            self.graph_titles = {name: title for name, title in titles.items() if name not in bindings} | graph_titles
        for name, entry in bindings.items():
            source = entry["source"]
            if source["name"] != name or source["revision"] != revision:
                raise ValueError(f"Invalid source binding for {name}")
            grouped[source["module"]].append(source)
        if grouped.keys() != line_data["modules"].keys():
            raise ValueError("The Lean source bindings and line index cover different modules")
        references = proof.references_among(sorted(bindings))
        if {name for name, binding in bindings.items() if binding["source"]["in_proof"]} != references.keys():
            raise ValueError("The source bindings and compiled proof disagree on declaration membership")
        archive_checks, graph_axioms = {}, {}
        if "lean-checks.json" in manifest["files"]:
            checks = _checked_asset(paper, manifest, "lean-checks.json")
            if (checks["schema"] != "rh-lean-checks/1" or checks["lean_revision"] != revision
                    or checks["paper_revision"] != paper_revision):
                raise ValueError("The Lean checks use a different edition or schema")
            archive_checks, graph_axioms = checks["archive"], checks["graph"]
            main_theorems = {name for name, binding in bindings.items()
                             if binding["source"]["module"] == "Main" and binding["source"]["kind"] == "theorem"}
            if archive_checks.keys() != main_theorems or graph_axioms.keys() != references.keys():
                raise ValueError("The Lean checks and source bindings cover different declarations")
        consumers = defaultdict(list)
        for name, uses in references.items():
            for target in uses:
                consumers[target].append(name)
        self._links = line_data["modules"]
        self._reference_kinds = {
            name: {target: proof.dependency_kinds(name, target) for target in targets}
            for name, targets in references.items()
        }
        modules = []
        for module, items in sorted(grouped.items()):
            paths = {row["file"] for row in items}
            if len(paths) != 1:
                raise ValueError(f"Conflicting files for Lean module {module}")
            path = paths.pop()
            local = PurePosixPath(path)
            if not path.startswith("src/") or local.suffix != ".lean" or ".." in local.parts:
                raise ValueError(f"Invalid archived path for Lean module {module}")
            line_rows = {row["name"]: row["lines"] for row in self._links[module]}
            if line_rows != {item["name"]: item["lines"] for item in items}:
                raise ValueError(f"Source ranges differ from the paper links for {module}")
            content = _git(checkout, "cat-file", "blob", f"{revision}:{path}")
            text = content.decode("utf-8")
            line_count = text.count("\n") + int(not text.endswith("\n") and bool(text))
            parsed = parse_module(text, module, path)
            declarations = _source_declarations(items, parsed, references, consumers, line_count)
            for declaration in declarations:
                name = declaration["name"]
                if name in titles:
                    declaration["display_title"] = titles[name]
                if name in archive_checks:
                    declaration["archive_check"] = archive_checks[name]
                if name in graph_axioms:
                    declaration["graph_axioms"] = graph_axioms[name]
                if name not in references:
                    continue
                kinds = self._reference_kinds[name]
                declaration["statement_uses"] = [target for target in references[name] if "type" in kinds[target]]
                declaration["proof_uses"] = [target for target in references[name] if "value" in kinds[target]]
                declaration["statement_used_by"] = [
                    user for user in consumers[name] if "type" in self._reference_kinds[user][name]
                ]
                declaration["proof_used_by"] = [
                    user for user in consumers[name] if "value" in self._reference_kinds[user][name]
                ]
            modules.append({
                "name": module, "path": path, "sha256": sha256(content).hexdigest(), "source": text,
                "lines": line_count, "imports": parsed["imports"],
                "declarations": declarations,
            })
        self._index = {
            "revision": revision, "base_url": f'{proof.manifest["upstream"]}/blob/{revision}/',
            "toolchain": _git(checkout, "cat-file", "blob", f"{revision}:lean-toolchain").decode().strip(),
            "dependency_source": "elaborated",
            "dependency_note": "Direct compiled references among paper-linked declarations in the RH proof.",
            "modules": modules,
        }
        self.metadata = {"revision": revision, "paper_revision": paper_revision,
                         "paper_manifest_sha256": self.paper_manifest_sha256, "scope": "paper_linked"}
        self._proof = proof
        self._titles = titles
        self._paper_names = bindings.keys()

    def modules(self):
        return {**modules_view(self._index), **self.metadata}

    def names(self):
        return {
            **names_view(self._index), **self.metadata,
            "declarations": [
                {**declaration, "module": module["name"], "path": module["path"],
                 "reference_kinds": self._reference_kinds.get(declaration["name"], {})}
                for module in self._index["modules"]
                for declaration in module["declarations"]
            ],
        }

    def module(self, name: str):
        item = module_view(self._index, name)
        if item is None:
            raise KeyError(name)
        declarations = []
        for declaration in item["declarations"]:
            graph = self._proof.direct_neighbourhood(declaration["name"])
            declarations.append({**declaration, "neighbourhood": self._reader_neighbourhood(graph)}
                                if graph is not None else declaration)
        return {**item, **self.metadata, "paper_links": self._links[name], "declarations": declarations}

    def _reader_neighbourhood(self, graph):
        def rank(node):
            name = node["name"]
            return (node["origin"] != "project", name not in self._paper_names, name not in self._titles,
                    node.get("declaration", name) != name, name)

        result = {
            "source": "compiled_lean", "scope": graph["scope"], "dataset": self._proof.manifest["dataset"],
            "limit": NEIGHBOURHOOD_LIMIT, "counts": {},
        }
        for direction in ("dependencies", "users"):
            result["counts"][direction] = len(graph[direction])
            result[direction] = []
            for node in sorted(graph[direction], key=rank)[:NEIGHBOURHOOD_LIMIT]:
                name = node["name"]
                item = {key: node[key] for key in ("name", "kind", "origin", "kinds")}
                item["display_title"] = self._titles.get(name) or self.graph_titles.get(name, name)
                if node["origin"] == "project" and node.get("file") and node.get("line"):
                    path = quote(node["file"], safe="/")
                    line = node["line"]
                    end = node.get("end_line") or line
                    item["href"] = f'{self._index["base_url"]}{path}#L{line}-L{end}'
                result[direction].append(item)
        return result
