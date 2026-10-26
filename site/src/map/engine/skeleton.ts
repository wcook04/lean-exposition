// The drawn skeleton: the transitive reduction of the visible subgraph. An
// edge u -> w is left out when another visible path from u reaches w, because
// that longer path already says u rests on w. The graph is acyclic.

import type { EngineEdge } from "./types";

export interface Skeleton {
  edges: EngineEdge[];
  /** Keys of visible edges that a longer visible path implies. */
  implied: Set<string>;
}

export function transitiveReduction(nodes: Iterable<string>, edges: readonly EngineEdge[]): Skeleton {
  const ids = new Set(nodes);
  const out = new Map<string, EngineEdge[]>();
  for (const id of ids) out.set(id, []);
  const live = edges.filter((e) => e.from !== e.to && ids.has(e.from) && ids.has(e.to));
  for (const e of live) out.get(e.from)!.push(e);

  // Descendants of each node (excluding itself), memoised in post-order.
  const below = new Map<string, Set<string>>();
  const visit = (id: string): Set<string> => {
    const known = below.get(id);
    if (known) return known;
    const set = new Set<string>();
    below.set(id, set); // acyclic, so no re-entry
    for (const e of out.get(id)!) {
      set.add(e.to);
      for (const d of visit(e.to)) set.add(d);
    }
    return set;
  };
  for (const id of ids) visit(id);

  const implied = new Set<string>();
  const kept: EngineEdge[] = [];
  for (const e of live) {
    let longer = false;
    for (const other of out.get(e.from)!) {
      if (other.to !== e.to && below.get(other.to)!.has(e.to)) {
        longer = true;
        break;
      }
    }
    // Two kinds of edge between the same pair: keep each, they are distinct relations.
    if (longer) implied.add(e.key);
    else kept.push(e);
  }
  return { edges: kept, implied };
}
