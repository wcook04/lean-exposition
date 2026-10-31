import { describe, expect, it } from "vitest";
import { parseRoute, routeHref } from "../src/app/router";
import { leanLevelCounts, leanSentence } from "../src/map/levels";
import type { ArgGraph } from "../src/model/graph";

describe("the Lean graph has an address", () => {
  it("keeps the view, the lens and the declaration through the URL", () => {
    const route = { view: "map" as const, lean: true, lens: "short" as const, decl: "OAI.X.y", declModule: "OAI.M" };
    const parsed = parseRoute(new URL(routeHref(route), "http://localhost"));
    expect(parsed).toMatchObject(route);
  });

  it("leaves an address without them as it was", () => {
    expect(routeHref({ view: "map", node: "a" })).not.toMatch(/[?&](v|d|dm)=/);
  });
});

describe("what the lens counts in the Lean graph", () => {
  const graph = {
    nodes: new Map([
      ["a", { papers: { short: { roles: ["mapped_x"], direct: 1 } } }],
      ["b", { papers: { short: { roles: ["support"], direct: 0 }, long: { roles: ["mapped_x"], direct: 1 } } }],
    ]),
  } as unknown as ArgGraph;
  const alignment = { records: { a: { lean: [{ name: "x" }, { name: "y" }] }, b: { lean: [{ name: "y" }, { name: "z" }] } } } as never;

  it("counts declarations once, and only what a level's own passages discuss", () => {
    const counts = leanLevelCounts(graph, new Set(["a", "b"]), alignment);
    expect(counts).toEqual({ all: 3, long: 2, short: 2, expository: 0 });
    expect(leanSentence(counts, "short")).toContain("2 of this argument's 3 Lean declarations");
  });
});
