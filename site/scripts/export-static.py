#!/usr/bin/env python3
"""Capture the reading site's requests from the existing Python web application.

Run from the repository root after assembling a bundle. Output is derived,
untracked website data; neither the bundle nor publication/review states change.
"""
import argparse
import hashlib
import json
import sys
from pathlib import Path
from urllib.parse import urlencode

from lean_exposition.web import API_ROOT, ROUTES, STAGES, TABLES, Parameters, create_app


def export(bundle, out):
    out.mkdir(parents=True, exist_ok=True)
    app = create_app(bundle, document_paths={
        "long": "long/reasoning-record.md", "short": "short/paper.md",
        "expository": "expository/main.md"})
    index = {"version": 1, "api_version": "1.2", "snapshot": dict(app._snapshot),
             "responses": {}, "documents": {}}

    def write(value, suffix="json"):
        raw = value if isinstance(value, bytes) else json.dumps(
            value, ensure_ascii=False, separators=(",", ":")).encode()
        name = hashlib.sha256(raw).hexdigest() + "." + suffix
        (out / name).write_bytes(raw)
        return name

    def data(route, **params):
        allowed = ROUTES.get(route, (None, ("offset", "limit")))[1]
        return app._dispatch(route, Parameters(urlencode(params, doseq=True), allowed))

    def capture(route, **params):
        key = route + ("?" + urlencode(sorted(params.items()), doseq=True) if params else "")
        index["responses"][key] = write(data(route, **params))

    def complete(route, **params):
        result = data(route, **params, limit=200)
        items = list(result["items"])
        while len(items) < result["total"]:
            items.extend(data(route, **params, limit=200, offset=len(items))["items"])
        return {**result, "items": items, "next": None}

    for route in ("", "/overview"):
        capture(route)
    capture("/graph", view="arguments", representation="map", scope="corpus", assumptions="true")
    records = {}
    for table in TABLES:
        records[table] = complete("/records", table=table)["items"]
    index["records"] = write(records)
    summaries = {t: [app._record_summary(r["ref"]) for r in rows]
                 for t, rows in records.items()}
    index["summaries"] = write(summaries)
    # Keep the complete tables for unscoped requests and older clients. Readers
    # asking for one table need not download unrelated citation/check records.
    index["records_by_table"] = {t: write(rows) for t, rows in records.items()}
    index["summaries_by_table"] = {t: write(rows) for t, rows in summaries.items()}
    for ref in sorted(app._records):
        capture("/record", ref=ref)
    for stage in STAGES:
        capture(f"/papers/{stage}/structure")
        index["responses"][f"/papers/{stage}/sections"] = write(complete(f"/papers/{stage}/sections"))
        index["documents"][stage] = write(app._files[f"papers/{stage}.md"], "md")
        capture("/papers/query", paper=stage, representation="matches")
        index["responses"][f"/papers/reading?paper={stage}"] = write(complete("/papers/reading", paper=stage))
        for passage in app._papers[stage]["paper"]["passages"]:
            params = {"paper": stage, "passage": passage["anchor"]}
            key = "/papers/reading?" + urlencode(sorted(params.items()))
            index["responses"][key] = write(complete("/papers/reading", **params))
        for row in records["nodes"]:
            capture("/papers/query", paper=stage, node=row["record"]["id"],
                    relation="prerequisites", representation="matches")
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
    (out / "parity.json").write_text(json.dumps(vectors, ensure_ascii=False))
    (out / "index.json").write_text(json.dumps(index, ensure_ascii=False, separators=(",", ":")))
    print(f"Exported {len(index['responses'])} responses for {app.manifest_sha256} to {out}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("bundle", type=Path)
    parser.add_argument("--out", type=Path, default=Path("site/public/edition"))
    args = parser.parse_args()
    export(args.bundle, args.out)
