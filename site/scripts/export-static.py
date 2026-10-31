#!/usr/bin/env python3
"""Capture the reading site's requests from the existing Python web application.

Run from the repository root after assembling a bundle. Output is derived,
untracked website data; neither the bundle nor publication/review states change.
"""
import argparse
import hashlib
import json
import shutil
import sys
from pathlib import Path
from urllib.parse import urlencode

from lean_exposition.web import API_VERSION, ROUTES, STAGES, TABLES, Parameters, create_app


# What the reader takes from each compact response. Accounts.UsedBy reads anchors
# and the first witness root; the selection inspector reads coverage and the
# claims and assumptions of each whole passage. The tests hold these fields to the
# client's reads and to the server's own full responses.
QUERY_MATCH_FIELDS = ("stage", "anchor", "direct_claim_ids", "direct_assumption_ids")
ROUTE_MAPS = ("/papers/query", "/papers/reading", "/record", "/lean/module", "/alignment/record")
# What only a reader of that statement's paper needs. The rest of a statement says where it
# is and which Lean it names, which is enough to mark it and to link to it from elsewhere.
STATEMENT_DETAIL = ("markdown", "lean", "note")
# Every page starts from the map and the overview, and none reads these.
MAP_OMITTED = ("condensation", "requested_roots", "seed_node_ids", "seed_record_refs", "selected_record_refs")


def node_query(result):
    """The fields of a node query that the "used by" list reads."""
    return {"representation": "reader_node_matches", "papers": [
        {"stage": paper["stage"], "matches": [
            {"anchor": match["anchor"],
             "witnesses": [{"root_node_id": row["root_node_id"]} for row in match["witnesses"][:1]]}
            for match in paper["matches"]]} for paper in result["papers"]]}


def paper_query(result):
    """The fields a text selection reads, filtered in the browser by byte range."""
    return {"representation": "reader_paper_matches", "match_count": result["match_count"],
            "coverage": result["coverage"], "papers": [
                {"stage": paper["stage"], "matches": [
                    {key: match[key] for key in QUERY_MATCH_FIELDS} for match in paper["matches"]]}
                for paper in result["papers"]]}


def record_detail(result, documents):
    """Passage text repeats across records; the reader restores it from the paper's bytes."""
    rows = []
    for row in result["aligned_passages"]:
        span = row["span"]
        if documents[row["stage"]][span["start_byte"]:span["end_byte"]].decode("utf-8") != row["text"]:
            raise SystemExit(f"Passage text differs from its paper bytes: {row['passage_ref']}")
        rows.append({key: value for key, value in row.items() if key != "text"})
    return {**result, "aligned_passages": rows}


def alignment_core(alignment):
    """The alignment without the statements' own text, which every page's marks and links read."""
    def place(row):
        kept = {key: value for key, value in row.items() if key not in STATEMENT_DETAIL}
        return {**kept, "lean": [{"name": lean["name"]} for lean in row["lean"]]} if "lean" in row else kept
    return {**alignment, "representation": "alignment_core", "records": {
        record: {**body, "statements": [place(row) for row in body["statements"]]}
        for record, body in alignment["records"].items()}}


def alignment_paper(alignment, stage):
    """Each record's statements in one paper, in the core's order: only what the core left out."""
    return {"representation": "alignment_paper", "paper": stage, "records": {
        record: rows for record, body in alignment["records"].items()
        if (rows := [{key: row[key] for key in STATEMENT_DETAIL if key in row}
                     for row in body["statements"] if row["paper"] == stage])}}


def encoded(value):
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":")).encode()


def clear_output(out):
    """Remove a previous export so that output is a function of the input alone."""
    if out.exists():
        if (out / "index.json").is_file():
            shutil.rmtree(out)
        elif any(out.iterdir()):
            raise SystemExit(f"Refusing to replace {out}: it is not a previous export.")
    out.mkdir(parents=True, exist_ok=True)


def export(bundle, out, *, lean_tree=None, alignment=None, oracle=Path("build/edition-oracle")):
    clear_output(out)
    if oracle.exists():
        shutil.rmtree(oracle)
    oracle.mkdir(parents=True)
    app = create_app(bundle, document_paths={
        "long": "long/reasoning-record.md", "short": "short/paper.md",
        "expository": "expository/main.md"}, lean_index=lean_tree, alignment=alignment)
    for error in app.alignment_errors:
        print(f"alignment left out: {error}", file=sys.stderr)
    index = {"version": 2, "api_version": API_VERSION, "snapshot": dict(app._snapshot),
             "responses": {}, "documents": {}}
    routes = {}

    def write(value, suffix="json"):
        raw = value if isinstance(value, bytes) else encoded(value)
        name = hashlib.sha256(raw).hexdigest() + "." + suffix
        (out / name).write_bytes(raw)
        return name

    def named(path, value):
        """Sidecars keep fixed paths, so Lean never touches a paper's file names."""
        target = out / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(encoded(value))
        return path

    def data(route, **params):
        allowed = ROUTES.get(route, (None, ("offset", "limit")))[1]
        return app._dispatch(route, Parameters(urlencode(params, doseq=True), allowed))

    def key_of(route, **params):
        return route + ("?" + urlencode(sorted(params.items()), doseq=True) if params else "")

    def record(key, file):
        route = key.split("?")[0]
        (routes.setdefault(route, {}) if route in ROUTE_MAPS else index["responses"])[key] = file

    def capture(route, **params):
        record(key_of(route, **params), write(data(route, **params)))

    def complete(route, **params):
        result = data(route, **params, limit=200)
        items = list(result["items"])
        while len(items) < result["total"]:
            items.extend(data(route, **params, limit=200, offset=len(items))["items"])
        return {**result, "items": items, "next": None}

    for route in ("", "/overview"):
        capture(route)
    capture("/graph", view="arguments", representation="map", scope="corpus", assumptions="true")
    # What every page loads at startup, without what no page reads. The full responses stay
    # published and remain what the live API serves.
    overview = data("/overview")
    record(key_of("/overview", representation="reader"), write({
        **overview, "graph": {key: value for key, value in overview["graph"].items() if key != "notes"},
        "representation": "reader_overview", "omitted_fields": ["graph.notes"]}))
    map_params = dict(view="arguments", scope="corpus", assumptions="true")
    corpus_map = data("/graph", representation="map", **map_params)
    record(key_of("/graph", representation="reader_map", **map_params), write({
        **{key: value for key, value in corpus_map.items() if key not in MAP_OMITTED},
        "representation": "reader_map", "omitted_fields": list(MAP_OMITTED)}))
    records = {}
    for table in TABLES:
        records[table] = complete("/records", table=table)["items"]
    summaries = {t: [app._record_summary(r["ref"]) for r in rows]
                 for t, rows in records.items()}
    # The reader always names a table or exact refs; an unscoped request reads
    # these same files, so no whole-edition copy is published.
    index["records_by_table"] = {t: write(rows) for t, rows in records.items()}
    index["summaries_by_table"] = {t: write(rows) for t, rows in summaries.items()}
    documents = {stage: app._files[f"papers/{stage}.md"] for stage in STAGES}
    full_records = []
    for ref in sorted(app._records):
        full = data("/record", ref=ref)
        record(key_of("/record", ref=ref), write(record_detail(full, documents)))
        if full["aligned_passages"] and len(full_records) < 12:
            full_records.append({"key": key_of("/record", ref=ref), "full": full})
    (oracle / "record-samples.json").write_bytes(encoded(full_records))
    sampled = [row["record"]["id"] for row in records["nodes"][::40]]
    samples = []
    for stage in STAGES:
        # The reading components use the paper, coverage and authored reading
        # links, not the expanded correspondence graph. The full structure stays
        # available from the live API and in the test oracle.
        structure = data(f"/papers/{stage}/structure")
        omitted = ("correspondence_links", "support_record_refs")
        reader_structure = {k: v for k, v in structure.items() if k not in omitted}
        reader_structure.update(representation="reader_structure", representation_version="1.0",
                                omitted_fields=list(omitted))
        (oracle / f"structure-{stage}.json").write_bytes(encoded(structure))
        index["responses"][f"/papers/{stage}/structure?representation=reader"] = write(reader_structure)
        index["responses"][f"/papers/{stage}/sections"] = write(complete(f"/papers/{stage}/sections"))
        index["documents"][stage] = write(app._files[f"papers/{stage}.md"], "md")
        whole = data("/papers/query", paper=stage, representation="matches")
        record(key_of("/papers/query", paper=stage, representation="matches"), write(paper_query(whole)))
        samples.append({"key": key_of("/papers/query", paper=stage, representation="matches"),
                        "kind": "paper", "full": whole})
        index["responses"][f"/papers/reading?paper={stage}"] = write(complete("/papers/reading", paper=stage))
        for passage in app._papers[stage]["paper"]["passages"]:
            params = {"paper": stage, "passage": passage["anchor"]}
            key = "/papers/reading?" + urlencode(sorted(params.items()))
            record(key, write(complete("/papers/reading", **params)))
        for row in records["nodes"]:
            params = dict(paper=stage, node=row["record"]["id"], relation="prerequisites",
                          representation="matches")
            full = data("/papers/query", **params)
            record(key_of("/papers/query", **params), write(node_query(full)))
            if row["record"]["id"] in sampled:
                samples.append({"key": key_of("/papers/query", **params), "kind": "node", "full": full})
    (oracle / "query-samples.json").write_bytes(encoded(samples))
    if lean_tree is not None:
        index["responses"]["/lean/modules"] = named("lean/modules.json", data("/lean/modules"))
        index["responses"]["/lean/names"] = named("lean/names.json", data("/lean/names"))
        for module in app._lean["modules"]:
            name = module["name"]
            record(key_of("/lean/module", name=name), named(f"lean/module/{name}.json", data("/lean/module", name=name)))
    if alignment is not None:
        whole = data("/alignment")
        index["responses"]["/alignment"] = named("alignment.json", whole)
        # A reader needs one paper's statements, so a page loads the core and that paper.
        index["responses"]["/alignment/core"] = named("alignment/core.json", alignment_core(whole))
        for stage in STAGES:
            index["responses"][f"/alignment/{stage}"] = named(f"alignment/{stage}.json", alignment_paper(whole, stage))
            index["responses"][f"/ties/{stage}"] = named(f"ties/{stage}.json", data(f"/ties/{stage}"))
        # One record whole, for the panel that opens on it.
        for id_, row in whole["records"].items():
            record(key_of("/alignment/record", id=id_), write(row))
    index["route_maps"] = {route: write(routes[route]) for route in sorted(routes)}
    # Python owns the indexed fields, row order and Unicode folding rules.
    index["search"] = write({"rows": app._search,
        "casefold": {chr(i): chr(i).casefold() for i in range(sys.maxunicode + 1)
                     if chr(i).casefold() != chr(i)},
        "whitespace": "".join(chr(i) for i in range(sys.maxunicode + 1) if chr(i).isspace())})
    # Executable parity cases use the real server as their oracle.
    queries = ["support", "Parisi", "QAOA", "σ", "ß", "SUPPORT gap", "unfindablezzzz"]
    vectors = []
    for query in queries:
        for table in ("nodes", "sections", "passages", "citations", "sources", "evidence"):
            params = {"q": query, "table": table, "offset": 1, "limit": 3}
            vectors.append({"params": params, "expected": data("/search", **params)})
    (oracle / "parity.json").write_bytes(encoded(vectors))
    (out / "index.json").write_bytes(encoded(index))
    total = sum(path.stat().st_size for path in out.rglob("*") if path.is_file())
    print(f"Exported {len(index['responses']) + sum(map(len, routes.values()))} responses "
          f"({total / 1e6:.1f} MB) for {app.manifest_sha256} to {out}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("bundle", type=Path)
    parser.add_argument("--out", type=Path, default=Path("site/public/edition"))
    parser.add_argument("--lean-tree", type=Path, help="Lean tree or prebuilt index to publish beside the edition")
    parser.add_argument("--alignment", type=Path, help="Record-alignment directory to publish beside the edition")
    parser.add_argument("--oracle", type=Path, default=Path("build/edition-oracle"),
                        help="Parity data for the tests; keep it outside anything published")
    args = parser.parse_args()
    export(args.bundle, args.out, lean_tree=args.lean_tree, alignment=args.alignment, oracle=args.oracle)
