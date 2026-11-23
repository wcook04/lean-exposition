#!/usr/bin/env python3
"""Build the read-only index of the exact, published RH proof closure."""
from __future__ import annotations

import argparse
from collections import defaultdict
import hashlib
import json
import sqlite3
import tempfile
from pathlib import Path

import numpy as np
import pyarrow.parquet as pq
from scipy.sparse import csr_matrix
from scipy.sparse.csgraph import breadth_first_order

from build_rh_paths import HASHES as DECLARATION_HASHES, INSTANCE, write_json

HASHES = {
    "constants.parquet": "ba43068ff85ee20b3e8aa11f9437dc7976233a0bf56937d0553e4fe487aa132a",
    "edges.parquet": "423a8dfe2150b5a5937679a5822f1477b7d10f241702afc6abd254813203aaae",
}
KINDS = ["type", "value", "lit", "quot", "block"]
STATEMENT_NEIGHBOURHOODS = "statement-neighbourhoods.json"


def check_inputs(dataset: Path, hashes) -> None:
    for file, expected in hashes.items():
        with (dataset / file).open("rb") as stream:
            if hashlib.file_digest(stream, "sha256").hexdigest() != expected:
                raise ValueError(f"{file} does not match publication v0.2.1")


def adjacent_rows(path, left, right, subjects, columns, expression_only=False):
    """Read only published edges touching a named subject."""
    kinds = [("via", "in", ["type", "value"])] if expression_only else []
    return pq.read_table(path, columns=columns,
                         filters=[[(key, "in", subjects), *kinds] for key in (left, right)]).to_pylist()


def group_references(subjects, edges, nodes, left, right, scope):
    """Preserve edge direction and both expression kinds when a pair has both."""
    grouped = {subject: {"dependencies": defaultdict(set), "users": defaultdict(set)} for subject in subjects}
    for edge in edges:
        consumer, prerequisite = edge[left], edge[right]
        if consumer == prerequisite:
            continue
        if consumer in grouped:
            grouped[consumer]["dependencies"][prerequisite].add(edge["via"])
        if prerequisite in grouped:
            grouped[prerequisite]["users"][consumer].add(edge["via"])
    return {
        nodes[subject]["name"]: {
            "scope": scope,
            **{direction: [{**nodes[other], "kinds": sorted(kinds)}
                           for other, kinds in sorted(neighbours.items())]
               for direction, neighbours in adjacent.items()},
        }
        for subject, adjacent in grouped.items()
    }


def reference_node(row, name):
    return {
        "name": name,
        "kind": row["kind"], "origin": row["origin"],
        "file": row["file"], "line": row["start_line"], "end_line": row["end_line"],
    }


def write_statement_neighbourhoods(dataset: Path, out: Path, reader) -> None:
    """Retain bounded subjects outside the RH-only index from their compiled tables."""
    constants = dataset / "constants.parquet"
    declarations = dataset / "decls.parquet"
    columns = ["kind", "origin", "file", "start_line", "end_line"]
    named = pq.read_table(constants, columns=["id", "name", "thm_mask"],
                          filters=[("name", "in", list(reader["labels"]))]).to_pylist()
    masks = {row["name"]: row["thm_mask"] for row in named}
    rh_mask = masks[reader["root"]]
    exact = [row["id"] for row in named if row["thm_mask"] and not row["thm_mask"] & rh_mask]
    edges = adjacent_rows(dataset / "edges.parquet", "src_id", "dst_id", exact,
                          ["src_id", "dst_id", "via"], expression_only=True)
    ids = sorted(set(exact) | {edge[key] for edge in edges for key in ("src_id", "dst_id")})
    nodes = {row["id"]: reference_node(row, row["name"])
             for row in pq.read_table(constants, columns=["id", "name", *columns],
                                      filters=[("id", "in", ids)]).to_pylist()}
    subjects = group_references(exact, edges, nodes, "src_id", "dst_id", "published_theorem_export")

    remaining = sorted(reader["labels"].keys() - masks.keys())
    project = [row["decl"] for row in pq.read_table(
        declarations, columns=["decl"], filters=[("decl", "in", remaining), ("origin", "=", "project")]
    ).to_pylist()]
    edges = adjacent_rows(dataset / "decl_edges.parquet", "src", "dst", project,
                          ["src", "dst", "src_kind", "dst_kind", "via"])
    names = set(project)
    nodes = {}
    for edge in edges:
        for direction in ("src", "dst"):
            name = edge[direction]
            if edge[f"{direction}_kind"] == "decl":
                names.add(name)
            else:
                nodes[name] = {"name": name, "kind": "constant", "origin": "project"}
    nodes.update((row["decl"], reference_node(row, row["decl"])) for row in pq.read_table(
        declarations, columns=["decl", *columns], filters=[("decl", "in", sorted(names))]
    ).to_pylist())
    subjects.update(group_references(project, edges, nodes, "src", "dst", "compiled_project_declarations"))
    write_json(out / STATEMENT_NEIGHBOURHOODS, {
        "schema": 1, "revision": reader["revision"], "dataset": reader["dataset"],
        "sha256": {**HASHES, **DECLARATION_HASHES}, "subjects": subjects,
    })


def read_constants(dataset: Path, root: str):
    table = pq.read_table(dataset / "constants.parquet",
                          columns=["id", "name", "kind", "origin", "file", "start_line", "end_line", "decl", "block", "thm_mask"])
    ids, names, masks = [table[k].combine_chunks() for k in ("id", "name", "thm_mask")]
    root_id = names.index(root).as_py()
    if root_id < 0 or np.any(ids.to_numpy() != np.arange(len(ids))):
        raise ValueError("The compiled export's root or identifier order is invalid")
    bit = masks[root_id].as_py()
    if bit <= 0 or bit & (bit - 1):
        raise ValueError("The requested root is not a standalone export target")
    return table, root_id, (masks.to_numpy() & bit) != 0


def build_edges(dataset: Path, blocks: np.ndarray, member: np.ndarray):
    parquet = pq.ParquetFile(dataset / "edges.parquet")
    capacity = parquet.metadata.num_rows + 2 * len(member)
    source = np.empty(capacity, dtype=np.uint32)
    dest = np.empty(capacity, dtype=np.uint32)
    kind = np.empty(capacity, dtype=np.uint8)
    end = 0
    for batch in parquet.iter_batches(columns=["src_id", "dst_id", "via"], batch_size=1_000_000):
        left, right = (batch.column(i).to_numpy() for i in range(2))
        keep = member[left] & member[right]
        size = int(np.count_nonzero(keep))
        encoded = batch.column(2).dictionary_encode()
        mapping = np.array([KINDS.index(k) for k in encoded.dictionary.to_pylist()], dtype=np.uint8)
        source[end:end + size] = left[keep]
        dest[end:end + size] = right[keep]
        kind[end:end + size] = mapping[encoded.indices.to_numpy()[keep]]
        end += size

    # The exporter requires every member of an inductive/quotient block.
    # Connect its members to a representative explicitly as structural edges.
    _, first, group = np.unique(blocks, return_index=True, return_inverse=True)
    representative = first[group]
    children = np.flatnonzero(member & (blocks >= 0) & (representative != np.arange(len(member))))
    parents = representative[children]
    if not np.all(member[parents]):
        raise ValueError("The selected proof has a partially included kernel block")
    stop = end + len(children)
    source[end:stop], dest[end:stop], kind[end:stop] = parents, children, 4
    source[stop:stop + len(children)], dest[stop:stop + len(children)], kind[stop:stop + len(children)] = children, parents, 4
    end = stop + len(children)
    print(f"Selected {end:,} references, including {2 * len(children):,} structural edges", flush=True)
    return source[:end], dest[:end], kind[:end]


def write_adjacency(path: Path, direction: str, source, dest, kind, size):
    order = np.argsort(source, kind="stable")
    offsets = np.concatenate(([0], np.cumsum(np.bincount(source, minlength=size)))).astype(np.int32)
    np.save(path / f"{direction}-offsets.npy", offsets)
    packed = np.lib.format.open_memmap(path / f"{direction}-edges.npy", mode="w+", dtype=np.uint32, shape=(len(order),))
    for start in range(0, len(order), 1_000_000):
        chunk = order[start:start + 1_000_000]
        packed[start:start + len(chunk)] = (dest[chunk] << 3) | kind[chunk]
    return offsets, packed


def write_names(path: Path, table, member: np.ndarray) -> None:
    with sqlite3.connect(path) as db:
        db.executescript("""
          PRAGMA journal_mode=OFF;
          PRAGMA synchronous=OFF;
          CREATE TABLE node (id INTEGER PRIMARY KEY, name TEXT UNIQUE, kind TEXT, origin TEXT,
                             file TEXT, line INTEGER, end_line INTEGER, declaration TEXT);
          CREATE VIRTUAL TABLE lookup USING fts5(name, content='node', content_rowid='id', tokenize='trigram');
        """)
        for batch in table.filter(member).to_batches(max_chunksize=20_000):
            data = batch.to_pydict()
            columns = ("id", "name", "kind", "origin", "file", "start_line", "end_line", "decl")
            db.executemany("INSERT INTO node VALUES (?, ?, ?, ?, ?, ?, ?, ?)",
                           zip(*(data[key] for key in columns), strict=True))
        db.execute("INSERT INTO lookup(lookup) VALUES ('rebuild')")
        db.execute("PRAGMA optimize")


def build(dataset: Path, out: Path) -> None:
    check_inputs(dataset, HASHES)
    include_statements = all((dataset / file).is_file() for file in DECLARATION_HASHES)
    if include_statements:
        check_inputs(dataset, DECLARATION_HASHES)
    manifest = json.loads((INSTANCE / "reader.json").read_text(encoding="utf-8"))
    table, root, member = read_constants(dataset, manifest["root"])
    size = len(member)
    source, dest, kind = build_edges(dataset, table["block"].combine_chunks().fill_null(-1).to_numpy(), member)
    out.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(dir=out.parent) as temp:
        stage = Path(temp) / "index"
        stage.mkdir()
        offsets, packed = write_adjacency(stage, "out", source, dest, kind, size)
        print("Wrote forward adjacency", flush=True)
        write_adjacency(stage, "in", dest, source, kind, size)
        print("Wrote reverse adjacency", flush=True)
        del source, dest, kind

        indices = (packed >> 3).astype(np.int32, copy=False)
        values = np.ones(len(indices), dtype=np.float64)
        order, parent = breadth_first_order(csr_matrix((values, indices, offsets), shape=(size, size)), root)
        del indices, values
        if len(order) != int(np.count_nonzero(member)) or not np.all(member[order]):
            raise ValueError(f"Traversal found {len(order):,} constants, expected {np.count_nonzero(member):,}")
        np.save(stage / "parents.npy", parent)
        print(f"Replayed reachability to all {len(order):,} constants", flush=True)
        write_names(stage / "nodes.sqlite", table, member)
        metadata = {k: manifest[k] for k in ("revision", "upstream", "dataset", "verification")}
        (stage / "manifest.json").write_text(json.dumps({
            **metadata, "schema": 1, "root": root, "root_name": manifest["root"],
            "constants": len(order), "edges": len(packed), "kinds": KINDS, "sha256": HASHES,
        }, indent=2) + "\n", encoding="utf-8")
        if include_statements:
            write_statement_neighbourhoods(dataset, stage, manifest)
        stage.rename(out)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("dataset", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--statement-neighbourhoods-only", action="store_true",
                        help="update the supplemental statement graphs in a matching existing index")
    args = parser.parse_args()
    if args.statement_neighbourhoods_only:
        reader = json.loads((INSTANCE / "reader.json").read_text(encoding="utf-8"))
        manifest = json.loads((args.output / "manifest.json").read_text(encoding="utf-8"))
        if (manifest.get("schema") != 1 or manifest["sha256"] != HASHES or
                any(manifest[key] != reader[key] for key in ("revision", "dataset"))):
            parser.error("existing index does not match the pinned compiled edition")
        check_inputs(args.dataset, {**HASHES, **DECLARATION_HASHES})
        with tempfile.TemporaryDirectory(dir=args.output) as temp:
            write_statement_neighbourhoods(args.dataset, Path(temp), reader)
            (Path(temp) / STATEMENT_NEIGHBOURHOODS).replace(args.output / STATEMENT_NEIGHBOURHOODS)
    elif args.output.exists():
        parser.error("output already exists; choose a new edition folder")
    else:
        build(args.dataset, args.output)


if __name__ == "__main__":
    main()
