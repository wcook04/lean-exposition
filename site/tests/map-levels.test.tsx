// The level lens and the arrow-key walk: their rules, against the captured graph.
import { describe, expect, it } from "vitest";
import { graphFixture } from "./fixtures";
import { LENS_ORDER, firstSections, hasLean, inLevel, levelCounts, levelRecords, lensSentence, walkPassages } from "../src/map/levels";
import { lensArgument, reach, scopedGraph, usesOf } from "../src/map/treeModel";
import { walkStep } from "../src/map/walk";
import type { PaperStructure } from "../src/api/types";

const graph = graphFixture();
const goal = "full_support";
const scoped = scopedGraph(graph, goal);
const argument = reach(scoped, goal);

describe("the level lens", () => {
  it("counts from the records each paper's own passages discuss, not from everything listed under it", () => {
    const counts = levelCounts(graph, argument);
    expect(counts.all).toBe(argument.size);
    expect(counts.total).toBe(graph.nodes.size);
    for (const stage of LENS_ORDER) expect(counts[stage]).toBe([...argument].filter((id) => inLevel(graph.nodes.get(id)!, stage)).length);
  });

  it("states the count in a sentence and never claims one level contains another", () => {
    const counts = { all: 30, total: 131, long: 30, short: 23, expository: 21 };
    expect(lensSentence(counts, undefined)).toBe("This argument has 30 of the 131 steps on this site.");
    expect(lensSentence(counts, "expository")).toBe("The exposition discusses 21 of the 30 steps in this argument.");
  });

  it("does not assume the levels nest", () => {
    const short = levelRecords(graph, "short");
    const exposition = levelRecords(graph, "expository");
    // A fixture may or may not have such records: the sets are computed, each on its own.
    expect([...exposition].filter((id) => !short.has(id)).every((id) => inLevel(graph.nodes.get(id)!, "expository"))).toBe(true);
  });

  it("closes up what a paper leaves out, so every record it uses stays joined to the goal", () => {
    for (const stage of LENS_ORDER) {
      const keep = levelRecords(graph, stage);
      const seen = lensArgument(scoped, goal, keep);
      const drawn = reach(seen, goal, keep);
      for (const id of drawn) if (id !== goal) expect(keep.has(id)).toBe(true);
      for (const id of argument) if (keep.has(id)) expect(drawn.has(id)).toBe(true);
    }
  });

  it("keeps recorded lines as they are and marks the ones it adds", () => {
    const keep = new Set([...argument].filter((_, i) => i % 3 === 0));
    const seen = lensArgument(scoped, goal, keep);
    for (const id of [goal, ...keep]) for (const e of usesOf(seen, id, keep)) {
      const recorded = scoped.edges.some((x) => x.key === e.key);
      expect(recorded || !!(e as { through?: string[] }).through?.length).toBe(true);
    }
    expect(seen.edges.length).toBeGreaterThanOrEqual(scoped.edges.length);
  });
});

describe("the Lean word", () => {
  it("marks a declaration, and a record with nothing linked stays bare", () => {
    expect(hasLean("not-in-the-index", { kind: "declaration" } as never)).toBe(true);
    expect(hasLean("not-in-the-index", { kind: "claim" } as never)).toBe(false);
  });
});

describe("the paper walk", () => {
  const span = (start_byte: number) => ({ start_byte, end_byte: start_byte + 10 });
  const structure = {
    paper: {
      sections: [
        { ref: "s1", title: "5.3 Strict curvature", level: 2, heading_span: span(200) },
        { ref: "s0", title: "1. Start", level: 2, heading_span: span(0) },
      ],
      passages: [
        { anchor: "later", section_ref: "s1", block_span: span(210), content_span: span(210), claim_ids: ["a", "b"], assumption_ids: [] },
        { anchor: "early", section_ref: "s0", block_span: span(10), content_span: span(10), claim_ids: ["a"], assumption_ids: ["outside"] },
        { anchor: "other", section_ref: "s0", block_span: span(30), content_span: span(30), claim_ids: ["outside"], assumption_ids: [] },
      ],
    },
  } as unknown as PaperStructure;

  it("goes in reading order, keeps only this argument's passages and names the section", () => {
    const walk = walkPassages(structure, new Set(["a", "b"]));
    expect(walk.map((p) => [p.anchor, p.place, p.records])).toEqual([
      ["early", "§1 Start", ["a"]],
      ["later", "§5.3 Strict curvature", ["a", "b"]],
    ]);
  });

  it("gives each record the section that first discusses it", () => {
    expect([...firstSections(walkPassages(structure, new Set(["a", "b"])))]).toEqual([
      ["a", "§1"],
      ["b", "§5.3"],
    ]);
  });
});

describe("walking the graph", () => {
  const box = (x: number) => ({ x, y: 0, w: 100, h: 40 });
  const scene = {
    boxes: new Map([
      ["goal", box(100)],
      ["left", box(0)],
      ["mid", box(120)],
      ["right", box(240)],
      ["low", box(120)],
    ]),
    rank: new Map([
      ["goal", 0],
      ["left", 1],
      ["mid", 1],
      ["right", 1],
      ["low", 2],
    ]),
    edges: ["left", "mid", "right"].map((to) => ({ key: to, from: "goal", to, kind: "supports" as const })).concat({ key: "low", from: "mid", to: "low", kind: "supports" as const }),
  };

  it("goes up to the result that uses it and down to its first input", () => {
    expect(walkStep(scene, "low", "ArrowUp")).toBe("mid");
    expect(walkStep(scene, "goal", "ArrowDown")).toBe("left");
    expect(walkStep(scene, "goal", "ArrowUp")).toBeNull();
    expect(walkStep(scene, "low", "ArrowDown")).toBeNull();
  });

  it("goes left and right among siblings, and stops at the end of the row", () => {
    expect(walkStep(scene, "mid", "ArrowLeft")).toBe("left");
    expect(walkStep(scene, "mid", "ArrowRight")).toBe("right");
    expect(walkStep(scene, "right", "ArrowRight")).toBeNull();
  });
});
