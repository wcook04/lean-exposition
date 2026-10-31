#!/usr/bin/env python3
"""Record the backend's scoped argument closure for every node, as a test oracle.

    .venv/bin/python site/scripts/capture-closures.py [build/qaoa-sk-authored/graph.json]

Run from the repository root with the project's own interpreter. For each node
taken as the only root it writes, from `lean_exposition.contracts`:

- `closure`: the backend's `closure(graph, [root])`, which keeps theorem
  application scopes, so a premise supplied by an application is not restored;
- `flat`: the same traversal with every application annotation removed, for
  comparison with what an unscoped client would draw;
- `states`: each reachable (node, discharged premises) context;
- `live`: every relation followed in at least one reachable context, keyed as
  the site keys its edges (`from→to→kind`, with node assumptions as `assumes`).

The site's `argumentContexts`, `argumentProjection` and `closure` are tested
against this file (site/tests/application-scope.test.ts). Recapture it with the
other fixtures whenever the edition changes; the test checks the graph digest.
"""

import argparse
import hashlib
import json
from pathlib import Path

from lean_exposition.contracts import argument_contexts, closure

repo = Path(__file__).resolve().parents[2]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("graph", type=Path, nargs="?", default=repo / "build" / "qaoa-sk-authored" / "graph.json")
parser.add_argument("--out", type=Path, default=repo / "site" / "tests" / "fixtures" / "closures.json",
                    help="Output oracle; use a scratch path to inspect a recapture first")
args = parser.parse_args()
graph_path, out = args.graph, args.out

raw = graph_path.read_bytes()
graph = json.loads(raw)
plain = {**graph, "edges": [{k: v for k, v in e.items() if k != "application"} for e in graph["edges"]]}

roots = {}
for node in sorted(n["id"] for n in graph["nodes"]):
    states, transitions = argument_contexts(graph, [node])
    live = set()
    for (source, _), (target, _), edge in transitions:
        live.add(f"{source}→{target}→{edge['kind'] if edge else 'assumes'}")
    roots[node] = {
        "closure": sorted(closure(graph, [node])),
        "flat": sorted(closure(plain, [node])),
        "states": sorted([n, sorted(d)] for n, d in states),
        "live": sorted(live),
    }

out.parent.mkdir(parents=True, exist_ok=True)
out.write_text(json.dumps({
    "graph_sha256": hashlib.sha256(raw).hexdigest(),
    "selected_goals": graph["selected_goals"],
    "roots": roots,
}, indent=1, ensure_ascii=False) + "\n")
print(f"Wrote closures for {len(roots)} roots to {out}")
