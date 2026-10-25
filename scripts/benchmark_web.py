#!/usr/bin/env python3
"""Measure cold/warm WSGI work and body sizes on an actual captured bundle.

Run with the installed package. Timing is diagnostic, never a test threshold;
this does not measure browser rendering, network or concurrent server load.
"""
import argparse
import json
import statistics
import time
from pathlib import Path
from urllib.parse import urlencode

from lean_exposition.web import API_VERSION, create_app


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("bundle", type=Path)
    parser.add_argument("--node", required=True, help="Recorded node ID for paper queries")
    parser.add_argument("--source", required=True, help="Recorded source ID for neighborhood queries")
    parser.add_argument("--repetitions", type=int, default=5)
    parser.add_argument("--out", type=Path)
    args = parser.parse_args()
    if not 1 <= args.repetitions <= 100:
        parser.error("repetitions must be in 1..100")
    start = time.perf_counter()
    app = create_app(args.bundle)
    startup = time.perf_counter() - start

    def get(route, query, etag=None):
        response = {}
        def start_response(status, headers):
            response.update(status=int(status.split()[0]), headers=dict(headers))
        env = {"REQUEST_METHOD": "GET", "PATH_INFO": "/api/v1" + route,
               "QUERY_STRING": urlencode(query, doseq=True)}
        if etag:
            env["HTTP_IF_NONE_MATCH"] = etag
        start = time.perf_counter()
        response["body"] = b"".join(app(env, start_response))
        response["elapsed_ms"] = (time.perf_counter() - start) * 1000
        return response

    source, offset = None, 0
    while source is None:
        response = get("/records", {"table": "sources", "q": args.source, "offset": offset, "limit": 200})
        if response["status"] != 200:
            raise RuntimeError(f"source lookup: HTTP {response['status']}: {response['body'].decode()}")
        page = json.loads(response["body"])["data"]
        source = next((r["ref"] for r in page["items"] if r["record"]["id"] == args.source), None)
        if source is not None or page["next"] is None:
            break
        offset += page["limit"]
    if source is None:
        parser.error("source ID absent from the recorded source search results")
    paper_query = {"node": args.node, "relation": "prerequisites"}
    cases = [
        ("overview", "/overview", {}),
        ("records", "/records", {"table": "nodes", "limit": 50}),
        ("records-summary", "/records", {"table": "nodes", "limit": 50, "representation": "summary"}),
        ("neighborhood", "/neighborhood", {"ref": source, "family": "provenance", "direction": "incoming", "depth": 1}),
        ("paper-query", "/papers/query", paper_query),
        ("paper-matches", "/papers/query", {**paper_query, "representation": "matches"}),
        ("paper", "/papers/long", {}),
        ("paper-structure", "/papers/long/structure", {}),
        ("global-graph", "/graph", {"scope": "corpus"}),
        ("graph-map", "/graph", {"scope": "corpus", "representation": "map"}),
        ("search", "/search", {"q": "curvature"}),
        ("compare", "/compare", {"left": "long", "right": "expository"}),
    ]
    rows = []
    for name, route, query in cases:
        first = get(route, query)
        if first["status"] != 200:
            raise RuntimeError(f"{name}: HTTP {first['status']}: {first['body'].decode()}")
        warm = [get(route, query)["elapsed_ms"] for _ in range(args.repetitions)]
        conditional = get(route, query, first["headers"]["ETag"])
        if conditional["status"] != 304 or conditional["body"]:
            raise RuntimeError(f"{name}: conditional retrieval did not revalidate")
        rows.append({"case": name, "response_bytes": len(first["body"]),
                     "cold_ms": round(first["elapsed_ms"], 3),
                     "warm_median_ms": round(statistics.median(warm), 3),
                     "conditional_ms": round(conditional["elapsed_ms"], 3)})
    result = {"api_version": API_VERSION, "manifest_sha256": app.manifest_sha256,
              "node_id": args.node, "source_ref": source, "repetitions": args.repetitions,
              "startup_ms": round(startup * 1000, 3), "rows": rows,
              "scope": "In-process WSGI work and body sizes; timing depends on machine and load."}
    output = json.dumps(result, indent=2) + "\n"
    if args.out:
        args.out.write_text(output)
    print(output, end="")


if __name__ == "__main__":
    main()
