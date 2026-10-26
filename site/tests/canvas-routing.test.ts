// Routing as a reader sees it: no needless sideways steps, no two lines on top
// of each other, and no crossing in a channel that a different lane order (or
// port order) would remove — the drawn crossings never exceed what the node
// order itself forces (the straight-line count the layout minimises).
import { describe, expect, it } from "vitest";
import { graphFixture } from "./fixtures";
import { closure } from "../src/model/graph";
import { expandTo, reach, usesOf, visibleEdges, visibleSet } from "../src/map/treeModel";
import { transitiveReduction } from "../src/map/engine/skeleton";
import { layoutTree } from "../src/map/engine/layout";
import { route } from "../src/map/engine/router";
import { collinearOverlaps, jogs, lineCrossings, segments } from "../src/map/engine/audit";
import { METRICS } from "../src/map/engine/types";
import { layoutScope, recordOf, splitSharedLeaves } from "../src/map/engine/occurrences";

const graph = graphFixture();

function draw(goal: string, expanded: Set<string>) {
  const visible = visibleSet(graph, goal, expanded);
  const sk = transitiveReduction(visible, visibleEdges(graph, goal, visible, expanded));
  const scope = layoutScope(goal, visible, sk.edges, (id) => graph.nodes.get(id)!.kind === "assumption");
  const split = splitSharedLeaves(goal, scope.nodes, scope.edges);
  const size = (lid: string) => (recordOf(lid) === goal ? { w: 800, h: 300 } : { w: graph.nodes.get(recordOf(lid))!.kind === "declaration" ? 196 : 176, h: 108 + (lid.length % 3) * 19 });
  const { layout, plan } = layoutTree({ root: goal, nodes: split.nodes, edges: split.edges, size, metrics: METRICS });
  const segs = segments(plan, route(plan, { boxes: layout.boxes, dummyX: (k) => layout.dummies.get(k)!.x }));
  return { layout, plan, segs };
}

const allOpen = (goal: string) => new Set([...reach(graph, goal)].filter((id) => id !== goal && usesOf(graph, id).length));
function litRoute(goal: string, selected: string) {
  const ex = new Set<string>();
  const traced = [...closure(graph, selected, "prerequisites")].filter((id) => reach(graph, goal).has(id));
  expandTo(graph, goal, [selected, ...traced], ex);
  for (const id of traced) if (usesOf(graph, id).length) ex.add(id);
  return ex;
}

const SCENES: [string, string, Set<string>][] = [
  ["landing", "full_support", new Set()],
  ["lit route rests from Exhausting the support complement", "full_support", litRoute("full_support", "support.full_relative_support")],
  ["full support unfolded", "full_support", allOpen("full_support")],
  ["value identities unfolded", "scalar_value", allOpen("scalar_value")],
  ["QAOA unfolded", "qaoa_thermodynamic_first", allOpen("qaoa_thermodynamic_first")],
];

describe.each(SCENES)("routing: %s", (name, goal, expanded) => {
  const { layout, plan, segs } = draw(goal, expanded);
  it("has no jogs, no overlapping runs, no broken lane orders, and no avoidable crossings", () => {
    const crossings = lineCrossings(segs);
    console.log(`[routing] ${name}: crossings ${crossings} (node order forces ${layout.crossings}), jogs ${jogs(segs).length}, overlaps ${collinearOverlaps(segs).length}, broken channels ${plan.brokenChannels.length}`);
    expect(jogs(segs).map((s) => s.line)).toEqual([]);
    expect(collinearOverlaps(segs)).toHaveLength(0);
    expect(plan.brokenChannels).toEqual([]);
    expect(crossings).toBeLessThanOrEqual(layout.crossings);
  });
});
