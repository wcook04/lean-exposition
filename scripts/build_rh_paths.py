#!/usr/bin/env python3
"""Project pinned, compiled Lean dependencies onto the RH reader's cards."""
from __future__ import annotations

import argparse
import collections
import hashlib
import json
from array import array
from pathlib import Path

import numpy as np
import pyarrow as pa
import pyarrow.compute as pc
import pyarrow.parquet as pq


INSTANCE = Path(__file__).resolve().parents[1] / "instances" / "riemann-hypothesis"
HASHES = {
    "decls.parquet": "29d3c4406f89d43b5ad5002ab85d64b3bf392946ebdb83bd0c352cb290302ac2",
    "decl_edges.parquet": "62a184a781184bc1f3953ed90f5b967a27a2a3517d7b1f7e169ca6cc7d1bbec3",
}


def check_inputs(dataset: Path) -> None:
    for file, expected in HASHES.items():
        with (dataset / file).open("rb") as data:
            actual = hashlib.file_digest(data, "sha256").hexdigest()
        if actual != expected:
            raise ValueError(f"{file} does not match the pinned v0.2.1 release")


def shortest_paths(table, root: str, targets: list[str]) -> dict[str, list[str]]:
    """Breadth-first search once, with edges oriented from use to prerequisite."""
    sources = table["src"].combine_chunks()
    destinations = table["dst"].combine_chunks()
    names = pc.unique(pa.concat_arrays([sources.dictionary, destinations.dictionary]))
    def node_ids(column):
        return pc.index_in(column.dictionary, value_set=names).to_numpy()[column.indices.to_numpy()]
    source_ids = node_ids(sources)
    order = np.argsort(source_ids, kind="stable")
    neighbours = node_ids(destinations)[order]
    offsets = np.concatenate(([0], np.cumsum(np.bincount(source_ids, minlength=len(names)))))
    wanted = pc.index_in(pa.array([root, *targets]), value_set=names).to_pylist()
    if None in wanted:
        raise ValueError("A reader endpoint is missing from the compiled graph")
    start, *ends = wanted
    parent = array("i", [-1]) * len(names)
    parent[start] = start
    remaining = set(ends) - {start}
    queue = collections.deque([start])
    while queue and remaining:
        node = queue.popleft()
        for neighbour in neighbours[offsets[node]:offsets[node + 1]]:
            if parent[neighbour] == -1:
                parent[neighbour] = node
                queue.append(neighbour)
                remaining.discard(neighbour)
    if remaining:
        raise ValueError(f"Endpoints outside the RH closure: {names.take(pa.array(sorted(remaining))).to_pylist()}")
    result = {}
    for target, end in zip(targets, ends, strict=True):
        path = [end]
        while path[-1] != start:
            path.append(parent[path[-1]])
        result[target] = names.take(pa.array(path[::-1])).to_pylist()
    return result


def write_json(path: Path, value) -> None:
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def build(dataset: Path, output: Path) -> None:
    manifest = json.loads((INSTANCE / "reader.json").read_text(encoding="utf-8"))
    check_inputs(dataset)
    edges_file = dataset / "decl_edges.parquet"
    columns = ["src", "dst"]
    table = pq.read_table(edges_file, columns=columns, read_dictionary=columns)
    paths = manifest["paths"]
    by_target = shortest_paths(table, manifest["root"], [row["target"] for row in paths])
    del table
    names = sorted({name for path in by_target.values() for name in path})
    decls = pq.read_table(dataset / "decls.parquet",
                          columns=["decl", "file", "start_line", "end_line", "in_cone"],
                          filters=[("decl", "in", names)]).to_pylist()
    by_name = {row["decl"]: row for row in decls}
    lookup = collections.defaultdict(set)
    for row in pq.read_table(edges_file, columns=["src", "dst", "via"],
                             filters=[("src", "in", names), ("dst", "in", names)]).to_pylist():
        lookup[row["src"], row["dst"]].add(row["via"])
    nodes = {}
    for name in names:
        row = by_name.get(name)
        if not row or not row["in_cone"]:
            raise ValueError(f"No compiled source span in the theorem export for {name}")
        title, topic = manifest["labels"].get(name, [name, ""])
        location = f'{row["file"]}#L{row["start_line"]}-L{row["end_line"]}'
        nodes[name] = {"id": name, "title": title, "topic": topic,
                       "href": f'{manifest["upstream"]}/blob/{manifest["revision"]}/{location}'}
    output.mkdir(parents=True, exist_ok=True)
    overview_edges = {}
    landmarks = set(manifest["landmarks"])
    for route in paths:
        path = by_target[route["target"]]
        direct = []
        for left, right in zip(path, path[1:]):
            kinds = sorted(lookup[left, right])
            if not kinds:
                raise ValueError(f"No compiled edge from {left} to {right}")
            direct.append({"from": left, "to": right, "kinds": kinds})
        write_json(output / f'{route["id"]}.json', {
            "revision": manifest["revision"], "path": path,
            "nodes": [nodes[name] for name in path], "edges": direct,
        })
        marked = [i for i, name in enumerate(path) if name in landmarks]
        for start, end in zip(marked, marked[1:]):
            left, right = path[start], path[end]
            overview_edges.setdefault((left, right), {
                "from": left, "to": right, "route": route["id"], "hops": end - start,
                "kinds": direct[start]["kinds"] if end == start + 1 else [],
            })
    write_json(output / "overview.json", {
        **{key: manifest[key] for key in ("root", "revision", "upstream", "dataset", "verification", "paths")},
        "nodes": [nodes[name] for name in manifest["landmarks"]],
        "edges": list(overview_edges.values()),
    })
    print(f"Published {len(overview_edges)} overview edges backed by {len(paths)} shortest paths")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("dataset", type=Path, help="folder containing the two v0.2.1 Parquet tables")
    parser.add_argument("--out", type=Path, default=INSTANCE / "edition")
    args = parser.parse_args()
    build(args.dataset, args.out)


if __name__ == "__main__":
    main()
