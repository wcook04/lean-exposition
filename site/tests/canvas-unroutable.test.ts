// A map whose edges form a cycle: the layered layout puts the cycle's cards on one row, so an edge
// between them has no gap to run through. The router used to throw (an array of negative length),
// then silently gave such an edge no route at all. It must now keep the edge, mark it unroutable,
// draw it as a straight line between the two cards, count it, and say so in the console.
import { afterEach, describe, expect, it, vi } from "vitest";
import { layoutTree } from "../src/map/engine/layout";
import { route } from "../src/map/engine/router";
import { METRICS, type EngineEdge } from "../src/map/engine/types";

const edges: EngineEdge[] = [
  { key: "goal>a", from: "goal", to: "a", kind: "supports" },
  { key: "a>b", from: "a", to: "b", kind: "supports" },
  { key: "b>c", from: "b", to: "c", kind: "supports" },
  // Closes the cycle a -> b -> c -> a.
  { key: "c>a", from: "c", to: "a", kind: "supports" },
  { key: "b>d", from: "b", to: "d", kind: "assumes" },
];
const nodes = ["goal", "a", "b", "c", "d"];
const size = (id: string) => (id === "goal" ? { w: 400, h: 120 } : { w: 176, h: 90 });

afterEach(() => vi.restoreAllMocks());

describe("an edge the layered layout cannot route", () => {
  it("is kept, marked, counted, drawn straight between its cards and reported with its key", () => {
    const warn = vi.spyOn(console, "warn").mockImplementation(() => {});
    const { layout, plan } = layoutTree({ root: "goal", nodes, edges, size, metrics: METRICS });
    // Every recorded edge is still in the plan.
    expect([...plan.edges.keys()].sort()).toEqual(edges.map((e) => e.key).sort());
    const stuck = [...plan.edges.values()].filter((pe) => pe.rankTo <= pe.rankFrom).map((pe) => pe.key);
    expect(stuck.length).toBeGreaterThan(0);
    expect([...plan.unroutable].sort()).toEqual(stuck.sort());
    for (const key of stuck) {
      const pe = plan.edges.get(key)!;
      expect(pe.unroutable).toBe(true);
      expect(pe.bus).toBe(false);
      expect(pe.arrow).toBe(false);
      expect(warn.mock.calls.some(([message]) => String(message).includes(key))).toBe(true);
    }
    // Routable edges are not marked.
    for (const pe of plan.edges.values()) if (!stuck.includes(pe.key)) expect(pe.unroutable).toBeFalsy();

    const routed = route(plan, { boxes: layout.boxes, dummyX: (k) => layout.dummies.get(k)!.x });
    for (const key of stuck) {
      const pe = plan.edges.get(key)!;
      const re = routed.edges.get(key)!;
      // A visible line: two distinct points, from the prerequisite's centre to the consumer's.
      expect(re.points).toHaveLength(2);
      const [a, z] = re.points;
      const child = layout.boxes.get(pe.to)!;
      const parent = layout.boxes.get(pe.from)!;
      expect(a).toEqual({ x: child.x + child.w / 2, y: child.y + child.h / 2 });
      expect(z).toEqual({ x: parent.x + parent.w / 2, y: parent.y + parent.h / 2 });
      expect(Math.hypot(z.x - a.x, z.y - a.y)).toBeGreaterThan(1);
    }
    // No routed path contains a non-finite coordinate.
    for (const re of routed.edges.values()) for (const p of re.points) expect(Number.isFinite(p.x) && Number.isFinite(p.y)).toBe(true);
  });

  it("is reported once per edge, not on every layout", () => {
    const warn = vi.spyOn(console, "warn").mockImplementation(() => {});
    const once = [...edges, { key: "c>b-once", from: "c", to: "b", kind: "supports" as const }];
    layoutTree({ root: "goal", nodes, edges: once, size, metrics: METRICS });
    const first = warn.mock.calls.filter(([m]) => String(m).includes("c>b-once")).length;
    expect(first).toBe(1);
    layoutTree({ root: "goal", nodes, edges: once, size, metrics: METRICS });
    expect(warn.mock.calls.filter(([m]) => String(m).includes("c>b-once")).length).toBe(first);
  });

  it("leaves an acyclic map with nothing unroutable", () => {
    const acyclic = edges.filter((e) => e.key !== "c>a");
    const { plan } = layoutTree({ root: "goal", nodes, edges: acyclic, size, metrics: METRICS });
    expect(plan.unroutable).toEqual([]);
  });
});
