// The argument for one main result with every branch open, drawn at the map's
// mark scale: each record a tile of its card's footprint in its source colour,
// with the real lines between them. The layout and the line routes come from
// the map's own engine (the same steps ArgumentTree takes for "Show all
// branches"); only the drawing is still. The tiles and lines use the map's
// classes and tokens, so the figure always matches the map.

import { useLayoutEffect, useMemo, useRef, useState } from "react";
import type { ArgGraph } from "../model/graph";
import { reach, scopedGraph, usesOf, visibleEdges, visibleSet } from "../map/treeModel";
import { transitiveReduction } from "../map/engine/skeleton";
import { layoutScope, recordOf, splitSharedLeaves } from "../map/engine/occurrences";
import { layoutBounds, layoutTree } from "../map/engine/layout";
import { roundedPath, route } from "../map/engine/router";
import { METRICS, type Size } from "../map/engine/types";

/** Card footprints as the map lays them out before it measures them (ArgumentTree's widths and first guesses). */
function footprint(graph: ArgGraph, lid: string, root: string): Size {
  const id = recordOf(lid);
  if (lid === root) return { w: 600, h: 260 };
  if (lid !== id) return { w: 176, h: 96 };
  return graph.nodes.get(id)?.kind === "declaration" ? { w: 196, h: 112 } : { w: 176, h: 124 };
}

/** `version` changes when the stored edges arrive: they are attached to the same graph object. */
export function useArgumentDrawing(fullGraph: ArgGraph, goal: string, version: string) {
  return useMemo(() => {
    const graph = scopedGraph(fullGraph, goal);
    const all = new Set([...reach(graph, goal)].filter((id) => id !== goal && usesOf(graph, id).length));
    const visible = visibleSet(graph, goal, all);
    const edges = visibleEdges(graph, goal, visible, all);
    const skel = transitiveReduction(visible, edges);
    const scope = layoutScope(goal, visible, skel.edges, (id) => graph.nodes.get(id)?.kind === "assumption");
    const split = splitSharedLeaves(goal, scope.nodes, scope.edges);
    const { layout, plan } = layoutTree({ root: goal, nodes: split.nodes, edges: split.edges, size: (lid) => footprint(graph, lid, goal), metrics: METRICS });
    const routed = route(plan, { boxes: layout.boxes, dummyX: (key) => layout.dummies.get(key)!.x });
    const r = METRICS.radius;
    const buses = new Map<string, string>();
    const lines: { key: string; kind: string; d: string }[] = [];
    for (const pe of plan.edges.values()) {
      const re = routed.edges.get(pe.key);
      if (!re) continue;
      const d = roundedPath(re.points, r);
      if (pe.bus) buses.set(pe.from, (buses.get(pe.from) ?? "") + d);
      else lines.push({ key: pe.key, kind: pe.kind, d });
    }
    for (const [parent, rb] of routed.buses) buses.set(parent, (buses.get(parent) ?? "") + roundedPath(rb.stem, r));
    const tiles = [...layout.boxes].map(([lid, box]) => {
      const id = recordOf(lid);
      const node = graph.nodes.get(id);
      return { lid, box, slot: node?.origin.slot ?? 0, root: lid === goal, clone: lid !== id, assumption: node?.kind === "assumption" };
    });
    const b = layoutBounds(layout);
    const pad = 24;
    return {
      tiles,
      lines,
      buses: [...buses.values()],
      view: { x: b.x0 - pad, y: b.y0 - pad, w: b.x1 - b.x0 + 2 * pad, h: b.y1 - b.y0 + 2 * pad },
      records: new Set(tiles.map((t) => recordOf(t.lid))).size,
    };
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [fullGraph, goal, version]);
}

/** The still drawing. Its strokes keep their screen width, as on the map: --k is the drawing's scale on screen. */
export function ArgumentFigure({ graph, goal, version }: { graph: ArgGraph; goal: string; version: string }) {
  const drawing = useArgumentDrawing(graph, goal, version);
  const ref = useRef<SVGSVGElement>(null);
  const [k, setK] = useState(0.4);
  useLayoutEffect(() => {
    const el = ref.current;
    if (!el) return;
    const measure = () => {
      // "meet" scales the drawing by the tighter of the two sides.
      const r = el.getBoundingClientRect();
      if (r.width > 0 && r.height > 0) setK(Math.min(r.width / drawing.view.w, r.height / drawing.view.h));
    };
    measure();
    const observer = new ResizeObserver(measure);
    observer.observe(el);
    return () => observer.disconnect();
  }, [drawing.view.w]);
  const { x, y, w, h } = drawing.view;
  return (
    <svg ref={ref} className="argfig" viewBox={`${x} ${y} ${w} ${h}`} preserveAspectRatio="xMidYMin meet" aria-hidden="true" style={{ ["--k" as string]: k }}>
      <g className="argfig__links">
        {drawing.buses.map((d, i) => (
          <g key={`bus${i}`}>
            <path className="casing" d={d} />
            <path className="link link--supports" d={d} />
          </g>
        ))}
        {drawing.lines.map((l) => (
          <g key={l.key}>
            <path className="casing" d={l.d} />
            <path className={`link link--${l.kind}`} d={l.d} />
          </g>
        ))}
      </g>
      {drawing.tiles.map((t) => (
        <g key={t.lid} data-slot={t.slot || undefined} className={`argfig__tile${t.root ? " argfig__tile--root" : ""}${t.assumption ? " argfig__tile--assumption" : ""}`}>
          <rect x={t.box.x} y={t.box.y} width={t.box.w} height={t.box.h} rx={METRICS.radius} />
          {t.clone && <rect className="argfig__band" x={t.box.x} y={t.box.y + t.box.h - 5 / k} width={t.box.w} height={5 / k} />}
        </g>
      ))}
    </svg>
  );
}
