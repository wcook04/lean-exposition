// @vitest-environment node
import { describe, expect, it } from "vitest";
import { graphFixture } from "./fixtures";
import { reach, usesOf, visibleEdges, visibleSet, routeTo } from "../src/map/treeModel";
import { transitiveReduction } from "../src/map/engine/skeleton";
import { layoutScope, recordOf, splitSharedLeaves } from "../src/map/engine/occurrences";
import { layoutTree } from "../src/map/engine/layout";
import { route, roundedPath, samplePolyline, type Plan, type Routed } from "../src/map/engine/router";
import { isotonic, spacedWithin } from "../src/map/engine/pav";
import { twoLayerCrossings } from "../src/map/engine/order";
import { METRICS, type EngineEdge, type Layout } from "../src/map/engine/types";

const graph = graphFixture();
const GOALS = ["full_support", "scalar_value", "qaoa_thermodynamic_first"];

const e = (from: string, to: string, kind: EngineEdge["kind"] = "supports"): EngineEdge => ({ key: `${from}→${to}→${kind}`, from, to, kind });

function scene(goal: string, expanded: Set<string>, prev?: Layout | null, pin?: string | null) {
  const visible = visibleSet(graph, goal, expanded);
  const edges = visibleEdges(graph, goal, visible, expanded);
  const sk = transitiveReduction(visible, edges);
  // What the map lays out: assumptions as tags (no lines), shared leaves as clones.
  const scope = layoutScope(goal, visible, sk.edges, (id) => graph.nodes.get(id)!.kind === "assumption");
  const split = splitSharedLeaves(goal, scope.nodes, scope.edges);
  const size = (lid: string) => {
    const id = recordOf(lid);
    return id === goal ? { w: 800, h: 250 } : { w: graph.nodes.get(id)!.kind === "declaration" ? 196 : 176, h: 96 + (id.length % 3) * 17 };
  };
  const { layout, plan } = layoutTree({ root: goal, nodes: split.nodes, edges: split.edges, size, metrics: METRICS, prev, pin });
  return { visible, edges, sk, scope, layout, plan };
}

const allOpen = (goal: string) => new Set([...reach(graph, goal)].filter((id) => id !== goal && usesOf(graph, id).length));

function frame(layout: Layout) {
  return { boxes: layout.boxes, dummyX: (k: string) => layout.dummies.get(k)!.x };
}

describe("transitive reduction", () => {
  it("drops an edge that a longer path implies", () => {
    const sk = transitiveReduction(["a", "b", "c"], [e("a", "b"), e("b", "c"), e("a", "c")]);
    expect(sk.edges.map((x) => x.key).sort()).toEqual([e("a", "b").key, e("b", "c").key].sort());
    expect([...sk.implied]).toEqual([e("a", "c").key]);
  });
  it("keeps a diamond and drops only the shortcut", () => {
    const edges = [e("a", "b"), e("a", "c"), e("b", "d"), e("c", "d"), e("a", "d")];
    const sk = transitiveReduction(["a", "b", "c", "d"], edges);
    expect(sk.edges).toHaveLength(4);
    expect(sk.implied.has(e("a", "d").key)).toBe(true);
  });
  it("judges implication only on visible nodes", () => {
    const sk = transitiveReduction(["a", "c"], [e("a", "b"), e("b", "c"), e("a", "c")]);
    expect(sk.edges.map((x) => x.key)).toEqual([e("a", "c").key]);
  });
  it("never hides an assumption or a Lean correspondence, whatever other route exists", () => {
    const sk = transitiveReduction(["a", "b", "c"], [e("a", "b", "formalizes"), e("b", "c", "assumes"), e("a", "c", "assumes")]);
    expect(sk.implied.size).toBe(0);
    const sk2 = transitiveReduction(["a", "b", "c"], [e("a", "b"), e("b", "c"), e("a", "c", "formalizes")]);
    expect(sk2.implied.size).toBe(0);
  });
  it("hides a support only when a support-only path joins its ends", () => {
    // a -> b is an assumption, b -> c support: the direct support a -> c stays.
    const mixed = transitiveReduction(["a", "b", "c"], [e("a", "b", "assumes"), e("b", "c"), e("a", "c")]);
    expect(mixed.implied.size).toBe(0);
    const pure = transitiveReduction(["a", "b", "c"], [e("a", "b"), e("b", "c"), e("a", "c")]);
    expect([...pure.implied]).toEqual([e("a", "c").key]);
  });
});

describe("helpers", () => {
  it("pool-adjacent-violators is exact on a small case", () => {
    expect(isotonic([3, 1, 2], [1, 1, 1]).map((v) => +v.toFixed(6))).toEqual([2, 2, 2]);
    expect(isotonic([1, 3, 2, 4], [1, 1, 3, 1])).toEqual([1, 2.25, 2.25, 4]);
  });
  it("spaced ports stay ordered, spaced and inside", () => {
    const xs = spacedWithin([10, 10, 10, 200], 14, 0, 120);
    for (let i = 1; i < xs.length; i++) expect(xs[i] - xs[i - 1]).toBeGreaterThanOrEqual(14 - 1e-9);
    expect(xs[0]).toBeGreaterThanOrEqual(0);
    expect(xs[xs.length - 1]).toBeLessThanOrEqual(120);
  });
  it("counts crossings between two layers", () => {
    const down = new Map([
      ["a", [{ id: "y", w: 1 }]],
      ["b", [{ id: "x", w: 1 }]],
    ]);
    expect(twoLayerCrossings(["a", "b"], ["x", "y"], down)).toBe(1);
    expect(twoLayerCrossings(["a", "b"], ["y", "x"], down)).toBe(0);
  });
  it("routeTo is the union of goal-to-target chains", () => {
    const goal = "full_support";
    const target = [...reach(graph, goal)].find((id) => id !== goal && !usesOf(graph, id).length)!;
    const set = routeTo(graph, goal, [target]);
    expect(set.has(goal)).toBe(true);
    expect(set.has(target)).toBe(true);
    for (const id of set) if (id !== goal) expect((graph.in.get(id) ?? []).some((x) => set.has(x.from))).toBe(true);
  });
});

describe.each(GOALS)("layout of %s, fully unfolded", (goal) => {
  const { layout, plan, sk, edges, scope } = scene(goal, allOpen(goal));

  it("puts the root alone at the top and runs every drawn edge from a deeper rank up to a shallower one", () => {
    expect(layout.layers[0]).toEqual([goal]);
    for (const edge of layout.edges) expect(layout.rank.get(edge.to)!).toBeGreaterThan(layout.rank.get(edge.from)!);
  });

  it("draws only the reduction", () => {
    expect(sk.edges.length + sk.implied.size).toBe(edges.length);
    expect(layout.edges.length).toBe(scope.edges.length);
  });

  it("leaves no overlaps within a rank, and keeps long-edge columns clear of cards", () => {
    for (const layer of layout.layers) {
      const items = layer.map((id) => (id.startsWith("§") ? { id, x0: layout.dummies.get(id)!.x, x1: layout.dummies.get(id)!.x, dummy: true } : { id, x0: layout.boxes.get(id)!.x, x1: layout.boxes.get(id)!.x + layout.boxes.get(id)!.w, dummy: false }));
      for (let i = 1; i < items.length; i++) {
        const gap = items[i].x0 - items[i - 1].x1;
        expect(gap).toBeGreaterThanOrEqual((items[i].dummy || items[i - 1].dummy ? METRICS.sepDummy : METRICS.sepCard) - 0.01);
      }
    }
  });

  it("records its crossings (for the report)", () => {
    console.log(`[engine] ${goal}: ${layout.boxes.size} cards, ${layout.edges.length} lines for ${sk.edges.length} drawn relations of ${edges.length}, weighted crossings ${layout.seedCrossings} seeded -> ${layout.crossings}`);
    expect(layout.crossings).toBeLessThanOrEqual(layout.seedCrossings);
  });

  it("routes inside the gaps and around every card", () => {
    const routed = route(plan, frame(layout));
    checkRoute(layout, plan, routed);
  });

  it("lays out within 10 ms and routes a frame within 1 ms after JIT warmup", () => {
    const size = (id: string) => (id === goal ? { w: 800, h: 250 } : { w: 176, h: 100 });
    const nodes = [...layout.boxes.keys()];
    const reps = 20;
    // Measure repeated interaction after compilation, rather than mixing V8's
    // cold compilation with layout time on a fresh hosted worker.
    for (let i = 0; i < reps; i++) layoutTree({ root: goal, nodes, edges: layout.edges, size, metrics: METRICS, prev: layout, pin: null });
    let t = performance.now();
    for (let i = 0; i < reps; i++) layoutTree({ root: goal, nodes, edges: layout.edges, size, metrics: METRICS, prev: layout, pin: null });
    const layoutMs = (performance.now() - t) / reps;
    t = performance.now();
    const f = frame(layout);
    for (let i = 0; i < 200; i++) {
      const r = route(plan, f);
      for (const re of r.edges.values()) roundedPath(re.points, 8);
    }
    const routeMs = (performance.now() - t) / 200;
    console.log(`[engine] ${goal}: layout ${layoutMs.toFixed(2)} ms, route+paths ${routeMs.toFixed(3)} ms per frame`);
    expect(layoutMs).toBeLessThan(10);
    expect(routeMs).toBeLessThan(1);
  });
});

function checkRoute(layout: Layout, plan: Plan, routed: Routed) {
  const rowTop = layout.layers.map((_, r) => Math.min(...plan.rows[r].map((id) => layout.boxes.get(id)!.y)));
  const rowBottom = layout.layers.map((_, r) => Math.max(...plan.rows[r].map((id) => layout.boxes.get(id)!.y + layout.boxes.get(id)!.h)));
  const boxes = [...layout.boxes.values()];
  const inside = (p: { x: number; y: number }) => boxes.some((b) => p.x > b.x + 0.5 && p.x < b.x + b.w - 0.5 && p.y > b.y + 0.5 && p.y < b.y + b.h - 0.5);
  for (const re of routed.edges.values()) {
    const pts = re.points;
    for (let i = 1; i < pts.length; i++) {
      const a = pts[i - 1];
      const b = pts[i];
      // Orthogonal only.
      expect(Math.abs(a.x - b.x) < 1e-6 || Math.abs(a.y - b.y) < 1e-6).toBe(true);
      if (Math.abs(a.y - b.y) < 1e-6 && Math.abs(a.x - b.x) > 1e-6) {
        // A horizontal run is a track: strictly inside some gap.
        const g = rowBottom.findIndex((bot, r) => r + 1 < rowTop.length && a.y > bot && a.y < rowTop[r + 1]);
        expect(g, `track at y=${a.y} of ${re.key}`).toBeGreaterThanOrEqual(0);
      }
    }
    for (const p of samplePolyline(pts, 3)) expect(inside(p), `${re.key} enters a card at ${p.x},${p.y}`).toBe(false);
    // Corners: radius at most half of each adjacent leg.
    checkCorners(roundedPath(pts, METRICS.radius));
  }
  // Exactly one arrowhead per bus; bus edges carry none of their own.
  const parents = new Set(layout.edges.filter((x) => x.kind === "supports").map((x) => x.from));
  expect(routed.buses.size).toBe(parents.size);
  for (const b of routed.buses.values()) expect(b.head).toHaveLength(3);
  for (const key of routed.heads.keys()) expect(plan.edges.get(key)!.bus).toBe(false);
}

function checkCorners(d: string) {
  const tokens = d.match(/[MLQ][^MLQ]*/g) ?? [];
  const verts: { x: number; y: number }[] = [];
  const rhos: { at: number; rho: number }[] = [];
  let cur = { x: 0, y: 0 };
  for (const t of tokens) {
    const nums = t.slice(1).split(/[ ,]+/).filter(Boolean).map(Number);
    if (t[0] === "M") {
      cur = { x: nums[0], y: nums[1] };
      verts.push(cur);
    } else if (t[0] === "L") {
      cur = { x: nums[0], y: nums[1] };
    } else {
      const b = { x: nums[0], y: nums[1] };
      rhos.push({ at: verts.length, rho: Math.hypot(cur.x - b.x, cur.y - b.y) });
      verts.push(b);
      cur = { x: nums[2], y: nums[3] };
    }
  }
  verts.push(cur);
  for (const { at, rho } of rhos) {
    const a = verts[at - 1];
    const b = verts[at];
    const c = verts[at + 1];
    expect(rho).toBeLessThanOrEqual(Math.hypot(b.x - a.x, b.y - a.y) / 2 + 0.15);
    expect(rho).toBeLessThanOrEqual(Math.hypot(c.x - b.x, c.y - b.y) / 2 + 0.15);
    expect(rho).toBeLessThanOrEqual(METRICS.radius + 0.15);
  }
}

describe("stability when one card unfolds", () => {
  for (const goal of GOALS) {
    it(`keeps order and the pinned card in place (${goal})`, () => {
      // Unfold step by step in breadth-first order from the root's uses.
      const expanded = new Set<string>();
      let prev = scene(goal, expanded).layout;
      let steps = 0;
      const queue = usesOf(graph, goal).map((x) => x.to);
      const seen = new Set(queue);
      while (queue.length && steps < 25) {
        const id = queue.shift()!;
        if (!usesOf(graph, id).length || !prev.boxes.has(id)) continue;
        expanded.add(id);
        const before = prev.boxes.get(id)!;
        const { layout, plan } = scene(goal, expanded, prev, id);
        const after = layout.boxes.get(id)!;
        expect(Math.abs(after.x - before.x)).toBeLessThan(0.5);
        expect(Math.abs(after.y - before.y)).toBeLessThan(0.5);
        // Cards that were already there, on an unchanged rank: same relative order unless crossings fell.
        for (let r = 0; r < layout.layers.length; r++) {
          const keep = (list: string[]) => list.filter((x) => !x.startsWith("§") && prev.boxes.has(x) && prev.rank.get(x) === r && layout.rank.get(x) === r);
          const oldOrder = keep(prev.layers[r] ?? []);
          const seeded = keep(layout.seedLayers[r]);
          const final = keep(layout.layers[r]);
          expect(seeded).toEqual(oldOrder);
          if (final.join() !== seeded.join()) expect(layout.crossings).toBeLessThan(layout.seedCrossings);
        }
        checkRoute(layout, plan, route(plan, frame(layout)));
        prev = layout;
        steps++;
        for (const x of usesOf(graph, id)) if (!seen.has(x.to)) {
          seen.add(x.to);
          queue.push(x.to);
        }
      }
      expect(steps).toBeGreaterThan(2);
    });
  }
});
