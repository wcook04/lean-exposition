import { describe, expect, it } from "vitest";
import { graphFixture } from "./fixtures";
import { reach, usesOf, visibleEdges, visibleSet } from "../src/map/treeModel";
import { transitiveReduction } from "../src/map/engine/skeleton";
import { layoutTree } from "../src/map/engine/layout";
import { route } from "../src/map/engine/router";
import { collinearOverlaps, lineCrossings, segments } from "../src/map/engine/audit";
import { METRICS } from "../src/map/engine/types";
import { layoutScope, recordOf, splitSharedLeaves } from "../src/map/engine/occurrences";

const graph = graphFixture();
const GOALS = ["full_support", "scalar_value", "qaoa_thermodynamic_first"];
const allOpen = (goal: string) => new Set([...reach(graph, goal)].filter((id) => id !== goal && usesOf(graph, id).length));

function drawn(goal: string) {
  const expanded = allOpen(goal);
  const visible = visibleSet(graph, goal, expanded);
  const edges = visibleEdges(graph, goal, visible, expanded);
  const sk = transitiveReduction(visible, edges);
  const scope = layoutScope(goal, visible, sk.edges, (id) => graph.nodes.get(id)!.kind === "assumption");
  const split = splitSharedLeaves(goal, scope.nodes, scope.edges);
  const size = (lid: string) => {
    const id = recordOf(lid);
    if (id === goal) return { w: 800, h: 250 };
    if (lid !== id) return { w: 176, h: 96 };
    return { w: graph.nodes.get(id)!.kind === "declaration" ? 196 : 176, h: 104 + (id.length % 3) * 22 };
  };
  const { layout, plan } = layoutTree({ root: goal, nodes: split.nodes, edges: split.edges, size, metrics: METRICS });
  const routed = route(plan, { boxes: layout.boxes, dummyX: (k) => layout.dummies.get(k)!.x });
  return { layout, plan, routed, sk, split };
}

describe.each(GOALS)("lines of %s, fully unfolded", (goal) => {
  const { plan, routed, sk, split, layout } = drawn(goal);
  const segs = segments(plan, routed);
  it("never runs two different lines on top of each other", () => {
    const overlaps = collinearOverlaps(segs);
    console.log(`[lines] ${goal}: ${sk.edges.length} drawn, ${sk.implied.size} not drawn, ${new Set([...layout.boxes.keys()].map(recordOf)).size} records in ${layout.boxes.size} cards (${split.shared.size} shared leaves split), crossings ${lineCrossings(segs)}, collinear overlaps ${overlaps.length}`);
    expect(overlaps.map((o) => `${o.a.line} [${o.a.a.x},${o.a.a.y}-${o.a.b.x},${o.a.b.y}] | ${o.b.line} [${o.b.a.x},${o.b.a.y}-${o.b.b.x},${o.b.b.y}]`)).toEqual([]);
  });
  it("brings each assumption and Lean correspondence into its consumer at its own port, left of the support bus", () => {
    for (const pe of plan.edges.values()) {
      if (pe.bus) continue;
      const others = [...plan.edges.values()].filter((o) => o.from === pe.from && o.key !== pe.key && !o.bus);
      for (const o of others) expect(Math.abs(o.parentPort - pe.parentPort) * layoutWidth(pe.from)).toBeGreaterThanOrEqual(METRICS.portSp - 0.01);
      const bus = plan.buses.get(pe.from);
      if (bus) expect(pe.parentPort).toBeLessThan(bus.stem);
    }
  });
  function layoutWidth(id: string) {
    return drawn(goal).layout.boxes.get(id)!.w;
  }
});
