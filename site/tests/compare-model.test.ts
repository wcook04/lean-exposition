import type { ArgGraph } from "../src/model/graph";
import { describe, expect, it } from "vitest";
import type { RecordAlignment } from "../src/api/lean";
import { LEVELS } from "../src/app/router";
import {
  argumentOutline,
  arrangeLevels,
  columnWeight,
  defaultColumns,
  filterByLevel,
  filterOutline,
  pressLevel,
  leanAbsence,
  toggleLevel,
  walk,
  walkListed,
} from "../src/compare/model";
import { reach, scopedGraph, usesOf } from "../src/map/treeModel";
import { graphFixture } from "./fixtures";

const graph = graphFixture();

function slice(paper: "long" | "short" | "expository", role: RecordAlignment["statements"][number]["role"], chars = 400, start = 0): RecordAlignment["statements"][number] {
  return { paper, role, markdown: "x".repeat(chars), start_byte: start, end_byte: start + chars, anchor: null, section: "1. Start", heading_id: null };
}

const lean = { name: "A.b", module: "A", line: 1, end_line: 2, relation: "states", note: "" } as const;
const full: RecordAlignment = { short: "t", lean: [lean], statements: [slice("long", "statement"), slice("short", "derivation"), slice("expository", "mention")] };
const noLean: RecordAlignment = { short: "t", lean: [], statements: [slice("long", "statement", 2000)] };

describe("the outline", () => {
  const goal = "full_support";
  const scoped = scopedGraph(graph, goal);
  const rows = argumentOutline(scoped, goal);

  it("starts at the goal and lists each record once", () => {
    expect(rows[0]).toEqual({ id: goal, depth: 0 });
    expect(new Set(rows.map((r) => r.id)).size).toBe(rows.length);
  });

  it("is depth first: a row sits under the last row one level up, and that row uses it", () => {
    rows.forEach((row, i) => {
      if (i === 0) return;
      expect(row.depth).toBeGreaterThan(0);
      expect(row.depth).toBeLessThanOrEqual(rows[i - 1].depth + 1);
      const parent = rows.slice(0, i).reverse().find((r) => r.depth === row.depth - 1)!;
      expect(usesOf(scoped, parent.id).some((e) => e.to === row.id)).toBe(true);
    });
  });

  it("holds every record of the goal's argument, so its size is the map's", () => {
    expect(new Set(rows.map((row) => row.id))).toEqual(reach(scoped, goal));
  });

  it("filters by every word of a title", () => {
    const titles: Record<string, string> = { a: "Full contact gives moments", b: "Moments of the gradient" };
    const list = [{ id: "a" }, { id: "b" }];
    expect(filterOutline(list, "moments FULL", (id) => titles[id]).map((r) => r.id)).toEqual(["a"]);
    expect(filterOutline(list, "  ", (id) => titles[id])).toHaveLength(2);
  });
});

describe("walking", () => {
  const rows = [{ id: "a" }, { id: "b" }, { id: "c" }];
  it("moves one row and stops at the ends", () => {
    expect(walk(rows, "a", 1)?.id).toBe("b");
    expect(walk(rows, "b", -1)?.id).toBe("a");
    expect(walk(rows, "a", -1)).toBeNull();
    expect(walk(rows, "c", 1)).toBeNull();
  });
  it("enters the list at its top from a record outside it", () => {
    expect(walk(rows, "z", 1)?.id).toBe("a");
  });
});

describe("the level filter", () => {
  const rows = [{ id: "a" }, { id: "b" }, { id: "c" }];
  const papers = (...stages: string[]) => ({ papers: Object.fromEntries(stages.map((stage) => [stage, { roles: ["mapped_claim"], direct: 1 }])) });
  const graph = { nodes: new Map([["a", papers("long", "short")], ["b", papers("long")], ["c", { papers: { long: { roles: ["support"], direct: 0 } } }]]) } as unknown as ArgGraph;
  it("narrows the outline to the steps a level discusses", () => {
    expect(filterByLevel(rows, "short", graph).map((r) => r.id)).toEqual(["a"]);
    expect(filterByLevel(rows, "long", graph).map((r) => r.id)).toEqual(["a", "b"]);
    expect(filterByLevel(rows, "all", graph)).toHaveLength(3);
  });
  it("walks from a record the filter left out to the nearest listed row", () => {
    const listed = [{ id: "a" }, { id: "c" }];
    expect(walkListed(rows, listed, "b", 1)?.id).toBe("c");
    expect(walkListed(rows, listed, "b", -1)?.id).toBe("a");
    expect(walkListed(rows, listed, "a", 1)?.id).toBe("c");
    expect(walkListed(rows, listed, "c", 1)).toBeNull();
  });
});

describe("collapsing levels", () => {
  const state = (slots: ReturnType<typeof arrangeLevels>) => Object.fromEntries(slots.map((s) => [s.level, s.state]));

  it("defaults to four, three, then two columns as the window narrows", () => {
    expect([defaultColumns(1920), defaultColumns(1680), defaultColumns(1679), defaultColumns(1280), defaultColumns(1279)]).toEqual([4, 4, 3, 3, 2]);
  });

  it("keeps all four levels in order, wide", () => {
    const slots = arrangeLevels(full, 1920);
    expect(slots.map((s) => s.level)).toEqual([...LEVELS]);
    expect(slots.every((s) => s.state === "column" || s.state === "empty")).toBe(true);
  });

  it("gives a level with nothing no column", () => {
    expect(state(arrangeLevels(noLean, 1920))).toEqual({ lean: "empty", long: "column", short: "empty", expository: "empty" });
  });

  it("at three columns leaves out the level with the least to say, and keeps it one press away", () => {
    expect(state(arrangeLevels(full, 1440))).toEqual({ lean: "column", long: "column", short: "column", expository: "folded" });
  });

  it("follows a reader's choice exactly, and a chosen level with nothing gets no column", () => {
    expect(state(arrangeLevels(noLean, 1440, ["long", "short"]))).toEqual({ lean: "empty", long: "column", short: "empty", expository: "empty" });
    expect(state(arrangeLevels(full, 1920, ["long"]))).toEqual({ lean: "folded", long: "column", short: "folded", expository: "folded" });
  });

  it("pressing a level changes what is shown and keeps a choice for records that have it", () => {
    expect(pressLevel(arrangeLevels(full, 1440), undefined, "expository")).toEqual(["lean", "long", "short", "expository"]);
    expect(pressLevel(arrangeLevels(full, 1440), undefined, "lean")).toEqual(["long", "short"]);
    expect(pressLevel(arrangeLevels(noLean, 1440, ["lean", "long"]), ["lean", "long"], "short")).toEqual(["lean", "long", "short"]);
  });

  it("will not hide the last column", () => {
    expect(pressLevel(arrangeLevels(noLean, 1440), undefined, "long")).toEqual(["long"]);
  });

  it("sets aside a choice that would leave the bench empty", () => {
    expect(state(arrangeLevels(noLean, 1440, ["short"])).long).toBe("column");
  });

  it("gives longer text more of the width, within limits", () => {
    expect(columnWeight(100)).toBe(1);
    expect(columnWeight(1125)).toBe(1.5);
    expect(columnWeight(100000)).toBe(2);
  });

  it("toggles keep the levels' order and leave one on", () => {
    expect(toggleLevel(["expository", "lean"], "short")).toEqual(["lean", "short", "expository"]);
    expect(toggleLevel(["lean"], "lean")).toEqual(["lean"]);
  });
});

describe("empty Lean states", () => {
  it("say what is true for a circuit record and for a step without a link", () => {
    expect(leanAbsence("circuit.color_exclusion")).toContain("has no declaration for this result");
    expect(leanAbsence("support.x")).toContain("No Lean declaration is linked to this step");
  });
});
