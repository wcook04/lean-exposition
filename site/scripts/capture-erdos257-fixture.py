#!/usr/bin/env python3
"""Capture the parts of the #257 static edition the #257 tests read, from site/public/edition.

Run after `python site/scripts/export-static.py build/erdos257-edition ...` has written the
#257 edition into site/public/edition. Writes site/tests/fixtures/erdos257-edition/edition/:
index.json with only the captured routes, and their files under their own names. The tests
(tests/erdos257-edition.test.tsx) then run for either instance, whatever public/edition holds.

    python site/scripts/capture-erdos257-fixture.py
"""
from __future__ import annotations

import json
import shutil
import sys
from pathlib import Path

SITE = Path(__file__).resolve().parents[1]
EDITION = SITE / "public/edition"
OUT = SITE / "tests/fixtures/erdos257-edition/edition"
ROUTES = ["/overview", "/alignment", "/ties/short", "/ties/long", "/ties/expository"]
GRAPH_ID = "erdos257-lambert-subseries"


def main() -> int:
    index = json.loads((EDITION / "index.json").read_text())
    overview = json.loads((EDITION / index["responses"]["/overview"]).read_text())
    if (overview.get("data", overview).get("graph") or {}).get("id") != GRAPH_ID:
        print("site/public/edition is not the #257 edition; export it first", file=sys.stderr)
        return 1
    if OUT.exists():
        shutil.rmtree(OUT)
    OUT.mkdir(parents=True)
    kept = {"version": index["version"], "api_version": index["api_version"], "snapshot": index["snapshot"], "responses": {}}
    for route in ROUTES:
        name = index["responses"][route]
        (OUT / name).parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(EDITION / name, OUT / name)
        kept["responses"][route] = name
    nodes = index["summaries_by_table"]["nodes"]
    shutil.copyfile(EDITION / nodes, OUT / nodes)
    kept["summaries_by_table"] = {"nodes": nodes}
    (OUT / "index.json").write_text(json.dumps(kept, indent=1, sort_keys=True) + "\n")
    size = sum(p.stat().st_size for p in OUT.iterdir())
    print(f"captured {len(ROUTES)} routes and the node summaries, {size:,} bytes, to {OUT}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
