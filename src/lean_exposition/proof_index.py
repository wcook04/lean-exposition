"""Read a pinned compiled proof graph without loading its edges into process memory."""
from __future__ import annotations

from contextlib import closing
import json
from pathlib import Path
import sqlite3
from urllib.parse import quote


REFERENCE_KINDS = ("type", "value")
STATEMENT_NEIGHBOURHOODS = "statement-neighbourhoods.json"


class ProofIndex:
    """Read-only views of the compiled closure and one shortest route to each node."""

    def __init__(self, directory: Path):
        import numpy as np

        self.manifest = json.loads((directory / "manifest.json").read_text(encoding="utf-8"))
        if self.manifest["schema"] != 1:
            raise ValueError("Unsupported compiled proof index schema")
        self.database = (directory / "nodes.sqlite").resolve().as_uri() + "?mode=ro&immutable=1"
        self.parents = np.load(directory / "parents.npy", mmap_mode="r", allow_pickle=False)
        self.offsets = {d: np.load(directory / f"{d}-offsets.npy", mmap_mode="r", allow_pickle=False) for d in ("out", "in")}
        self.edges = {d: np.load(directory / f"{d}-edges.npy", mmap_mode="r", allow_pickle=False) for d in ("out", "in")}
        supplement = directory / STATEMENT_NEIGHBOURHOODS
        self.statement_neighbourhoods = {}
        if supplement.is_file():
            data = json.loads(supplement.read_text(encoding="utf-8"))
            if (data["schema"] != 1 or data["revision"] != self.manifest["revision"]
                    or data["dataset"] != self.manifest["dataset"]
                    or any(data["sha256"].get(file) != digest for file, digest in self.manifest["sha256"].items())):
                raise ValueError("Statement neighbourhoods use a different compiled edition")
            self.statement_neighbourhoods = data["subjects"]

    def _db(self):
        db = sqlite3.connect(self.database, uri=True)
        db.row_factory = sqlite3.Row
        return db

    def _node(self, row):
        node = dict(row)
        if node["file"] and node["line"]:
            path = quote(node["file"], safe="/")
            lines = f'L{node["line"]}-L{node["end_line"] or node["line"]}'
            node["href"] = f'{self.manifest["upstream"]}/blob/{self.manifest["revision"]}/{path}#{lines}'
        return node

    def search(self, query: str, limit: int):
        with closing(self._db()) as db:
            exact = db.execute("SELECT * FROM node WHERE name = ?", (query,)).fetchone()
            if len(query) >= 3:
                phrase = '"' + query.replace('"', '""') + '"'
                rows = db.execute(
                    """SELECT node.* FROM lookup JOIN node ON node.id = lookup.rowid
                       WHERE lookup MATCH ? AND node.name != ?
                       ORDER BY node.origin != 'project', node.declaration IS NOT node.name,
                                length(node.name), node.name LIMIT ?""",
                    (phrase, query, limit - bool(exact)),
                ).fetchall()
            else:
                rows = db.execute(
                    "SELECT * FROM node WHERE name >= ? AND name < ? AND name != ? ORDER BY name LIMIT ?",
                    (query, query + "\U0010ffff", query, limit - bool(exact)),
                ).fetchall()
        return [self._node(row) for row in ([exact] if exact else []) + rows]

    def dependency_kinds(self, consumer: str, prerequisite: str) -> list[str]:
        """Kinds of direct compiled edges from a consumer to a prerequisite."""
        with closing(self._db()) as db:
            ids = dict(db.execute("SELECT name, id FROM node WHERE name IN (?, ?)", (consumer, prerequisite)))
        if consumer not in ids or prerequisite not in ids:
            return []
        start, end = map(int, self.offsets["out"][ids[consumer]:ids[consumer] + 2])
        edges = self.edges["out"][start:end]
        kinds = set(int(edge) & 7 for edge in edges[(edges >> 3) == ids[prerequisite]])
        return [self.manifest["kinds"][kind] for kind in sorted(kinds)]

    def references_among(self, names):
        """Direct type and value references within a selected set of declarations."""
        with closing(self._db()) as db:
            ids = {row["id"]: name for name in names
                   if (row := db.execute("SELECT id FROM node WHERE name = ?", (name,)).fetchone()) is not None}
        kinds = {n for n, kind in enumerate(self.manifest["kinds"]) if kind in REFERENCE_KINDS}
        references = {}
        for node, name in ids.items():
            start, end = map(int, self.offsets["out"][node:node + 2])
            targets = {ids[edge >> 3] for edge in map(int, self.edges["out"][start:end])
                       if (edge & 7) in kinds and (edge >> 3) in ids}
            references[name] = sorted(targets)
        return references

    def known_names(self, names):
        """Exact names from the compiled closure or its bound statement supplement."""
        requested = set(names)
        supplemental = set(self.statement_neighbourhoods) & requested
        for neighbourhood in self.statement_neighbourhoods.values():
            for direction in ("dependencies", "users"):
                supplemental.update(row["name"] for row in neighbourhood[direction] if row["name"] in requested)
        with closing(self._db()) as db:
            return supplemental | {
                name for name in requested - supplemental
                if db.execute("SELECT 1 FROM node WHERE name = ?", (name,)).fetchone() is not None
            }

    def direct_neighbourhood(self, name: str):
        """Immediate named type and value references, with their recorded scope."""
        supplement = self.statement_neighbourhoods.get(name)
        if supplement is not None:
            return supplement
        with closing(self._db()) as db:
            subject = db.execute("SELECT id FROM node WHERE name = ?", (name,)).fetchone()
            if subject is None:
                return None
            centre = subject["id"]
            kind_codes = {n: kind for n, kind in enumerate(self.manifest["kinds"]) if kind in REFERENCE_KINDS}
            adjacency = {}
            for direction, label in (("out", "dependencies"), ("in", "users")):
                start, end = map(int, self.offsets[direction][centre:centre + 2])
                neighbours = {}
                for edge in map(int, self.edges[direction][start:end]):
                    other, code = edge >> 3, edge & 7
                    if other != centre and code in kind_codes:
                        neighbours.setdefault(other, set()).add(kind_codes[code])
                adjacency[label] = neighbours

            ids = sorted(adjacency["dependencies"].keys() | adjacency["users"].keys())
            nodes = {}
            for start in range(0, len(ids), 500):
                batch = ids[start:start + 500]
                placeholders = ",".join("?" for _ in batch)
                nodes.update((row["id"], dict(row)) for row in
                             db.execute(f"SELECT * FROM node WHERE id IN ({placeholders})", batch))
        return {
            "scope": "riemann_hypothesis_closure",
            **{label: [{**nodes[other], "kinds": sorted(kinds)} for other, kinds in neighbours.items()]
               for label, neighbours in adjacency.items()},
        }

    def neighbourhood(self, name: str, offset: int, limit: int):
        with closing(self._db()) as db:
            subject = db.execute("SELECT * FROM node WHERE name = ?", (name,)).fetchone()
            if subject is None:
                raise KeyError(name)
            centre = subject["id"]
            pairs = []
            totals = {}
            for direction in ("out", "in"):
                start, end = map(int, self.offsets[direction][centre:centre + 2])
                totals[direction] = end - start
                for raw in self.edges[direction][min(start + offset, end):min(start + offset + limit, end)]:
                    edge = int(raw)
                    other, kind = edge >> 3, self.manifest["kinds"][edge & 7]
                    left, right = (centre, other) if direction == "out" else (other, centre)
                    pairs.append((left, right, kind))
            route = [centre]
            while route[-1] != self.manifest["root"]:
                route.append(int(self.parents[route[-1]]))
            ids = {i for pair in pairs for i in pair[:2]} | set(route)
            placeholders = ",".join("?" for _ in ids)
            rows = db.execute(f"SELECT * FROM node WHERE id IN ({placeholders})", tuple(ids)).fetchall()
        nodes = {row["id"]: self._node(row) for row in rows}
        return {
            "revision": self.manifest["revision"],
            "subject": subject["name"],
            "nodes": list(nodes.values()),
            "edges": [{"from": nodes[left]["name"], "to": nodes[right]["name"], "kind": kind} for left, right, kind in pairs],
            "route": [nodes[i]["name"] for i in route],
            "references": totals,
            "offset": offset,
            "limit": limit,
        }
