import { describe, expect, it } from "vitest";
import { graphFixture } from "./fixtures";
import { reach, usesOf, visibleEdges, visibleSet } from "../src/map/treeModel";
import { transitiveReduction } from "../src/map/engine/skeleton";
import { layoutTree } from "../src/map/engine/layout";
import { consumerOf, layoutScope, occurrenceId, recordOf, splitSharedLeaves } from "../src/map/engine/occurrences";
import { METRICS, type EngineEdge } from "../src/map/engine/types";

const e = (from: string, to: string, kind: EngineEdge["kind"] = "supports"): EngineEdge => ({ key: `${from}→${to}→${kind}`, from, to, kind });

describe("assumptions as premise tags", () => {
  it("lays out no assumes line, and an assumption only when a drawn support reaches it", () => {
    const isA = (id: string) => id.startsWith("A");
    const s = layoutScope("g", ["g", "b", "A1", "A2"], [e("g", "b"), e("g", "A1", "assumes"), e("b", "A1", "assumes"), e("b", "A2")], isA);
    expect(s.nodes.sort()).toEqual(["A2", "b", "g"]);
    expect(s.edges.map((x) => x.kind)).toEqual(["supports", "supports"]);
  });
});

describe("clones of shared leaves", () => {
  it("draws a leaf used by two records once under each, keeping the real edge keys", () => {
    const s = splitSharedLeaves("g", ["g", "a", "b", "L"], [e("g", "a"), e("g", "b"), e("a", "L"), e("b", "L")]);
    expect(s.nodes.sort()).toEqual(["a", "b", "g", occurrenceId("L", "a"), occurrenceId("L", "b")].sort());
    expect(s.edges.map((x) => x.key).sort()).toEqual([e("g", "a"), e("g", "b"), e("a", "L"), e("b", "L")].map((x) => x.key).sort());
    expect(s.shared.get("L")).toBe(2);
    for (const lid of s.nodes) expect(recordOf(lid)).toBe(lid.split("@@")[0]);
    expect(consumerOf(occurrenceId("L", "a"))).toBe("a");
  });
  it("keeps a shared record with drawn inputs as one node", () => {
    const s = splitSharedLeaves("g", ["g", "a", "b", "M", "L"], [e("g", "a"), e("g", "b"), e("a", "M"), e("b", "M"), e("M", "L")]);
    expect(s.nodes).toContain("M");
    expect(s.shared.has("M")).toBe(false);
  });
  it("puts each clone one rank under its consumer, with no long edges, on the captured goals", () => {
    const graph = graphFixture();
    for (const goal of ["full_support", "scalar_value", "qaoa_thermodynamic_first"]) {
      const expanded = new Set([...reach(graph, goal)].filter((id) => id !== goal && usesOf(graph, id).length));
      const visible = visibleSet(graph, goal, expanded);
      const sk = transitiveReduction(visible, visibleEdges(graph, goal, visible, expanded));
      const scope = layoutScope(goal, visible, sk.edges, (id) => graph.nodes.get(id)!.kind === "assumption");
      const split = splitSharedLeaves(goal, scope.nodes, scope.edges);
      const { layout } = layoutTree({ root: goal, nodes: split.nodes, edges: split.edges, size: () => ({ w: 176, h: 100 }), metrics: METRICS });
      for (const lid of layout.boxes.keys()) {
        const c = consumerOf(lid);
        if (c) expect(layout.rank.get(lid)).toBe(layout.rank.get(c)! + 1);
      }
      // Every record is still drawn; unique records are counted once.
      expect(new Set([...layout.boxes.keys()].map(recordOf)).size).toBe(scope.nodes.length);
    }
  });
});
