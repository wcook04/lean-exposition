import { describe, expect, it } from "vitest";
import type { PaperStructure, Stage } from "../src/api/types";
import { LINK_BONUS, alignPapers, recordWeights, type AlignUnit, type AlignedRow } from "../src/compare/paperAlignment";
import { structureFixture } from "./fixtures";

const unit = (part: number, records: string[], size = 1000): AlignUnit => ({ part, records, size });

function unitsOf(structure: PaperStructure): AlignUnit[] {
  const anchors = new Map(structure.paper.passages.map((p) => [p.anchor, p]));
  return structure.paper.document_parts.map((part, i) => {
    const passage = part.passage_ref ? anchors.get(part.passage_ref.slice(part.passage_ref.lastIndexOf("/") + 1)) : undefined;
    return unit(i, passage ? [...passage.claim_ids, ...passage.assumption_ids] : [], part.span.end_byte - part.span.start_byte);
  });
}

function expectComplete(rows: AlignedRow[], left: number, right: number) {
  const across = (side: "left" | "right") => rows.flatMap((r) => r[side]);
  const l = across("left");
  const r = across("right");
  expect(l).toEqual(Array.from({ length: left }, (_, i) => i));
  expect(r).toEqual(Array.from({ length: right }, (_, i) => i));
}

describe("aligning two papers", () => {
  it("pairs passages that share a record", () => {
    const rows = alignPapers([unit(0, ["a"]), unit(1, ["b"])], [unit(0, ["a"]), unit(1, ["b"])]);
    expect(rows.map((r) => [r.left, r.right, r.shared])).toEqual([
      [[0], [0], ["a"]],
      [[1], [1], ["b"]],
    ]);
  });

  it("stays monotone: a crossing pair loses to the stronger order and is listed as also linked", () => {
    const left = [unit(0, ["a", "x", "y"]), unit(1, ["b"])];
    const right = [unit(0, ["b"]), unit(1, ["a", "x", "y"])];
    const rows = alignPapers(left, right);
    expectComplete(rows, 2, 2);
    const paired = rows.find((r) => r.left.length && r.right.length)!;
    expect(paired.left).toEqual([0]);
    expect(paired.right).toEqual([1]);
    expect(rows.flatMap((r) => r.also).length).toBeGreaterThan(0);
  });

  it("weights a rare record above a common one", () => {
    const left = [unit(0, ["common", "rare"]), unit(1, ["common"]), unit(2, ["common"])];
    const right = [unit(0, ["common"]), unit(1, ["common", "rare"])];
    const weights = recordWeights(left, right);
    expect(weights.get("rare")!).toBeGreaterThan(weights.get("common")!);
    expect(alignPapers(left, right).find((r) => r.shared.includes("rare"))?.shared[0]).toBe("rare");
  });

  it("an authored reading link decides between equal passages", () => {
    const left = [unit(0, ["a"])];
    const right = [unit(0, ["a"]), unit(1, ["a"])];
    const free = alignPapers(left, right);
    const linked = alignPapers(left, right, [{ left: 0, right: 1 }]);
    expect(free.find((r) => r.left.length)?.right).toContain(0);
    expect(linked.find((r) => r.left.length)?.right).toContain(1);
    expect(LINK_BONUS).toBeGreaterThan(0);
  });

  it("merges a gap passage into the row it shares a record with", () => {
    const left = [unit(0, ["a"]), unit(1, ["a", "b"])];
    const right = [unit(0, ["a", "b"])];
    const rows = alignPapers(left, right);
    expect(rows).toHaveLength(1);
    expect(rows[0].left).toEqual([0, 1]);
  });

  it("keeps text with no partner on its own row, in order", () => {
    const rows = alignPapers([unit(0, ["a"]), unit(1, [], 5000), unit(2, ["b"])], [unit(0, ["a"]), unit(1, ["b"])]);
    expectComplete(rows, 3, 2);
    expect(rows[1].right).toEqual([]);
  });

  it("carries a heading with the passage it heads", () => {
    const rows = alignPapers([unit(0, [], 40), unit(1, ["a"])], [unit(0, ["a"])]);
    expect(rows).toHaveLength(1);
    expect(rows[0].left).toEqual([0, 1]);
  });

  it("handles a paper with nothing in common", () => {
    expectComplete(alignPapers([unit(0, ["a"])], [unit(0, ["b"]), unit(1, [])]), 1, 2);
    expect(alignPapers([], [])).toEqual([]);
  });

  const pairs: [Stage, Stage][] = [["short", "expository"], ["expository", "short"], ["long", "short"], ["long", "expository"]];
  it.each(pairs)("places every part of %s and %s exactly once, in reading order", (a, b) => {
    const left = unitsOf(structureFixture(a));
    const right = unitsOf(structureFixture(b));
    const rows = alignPapers(left, right);
    expectComplete(rows, left.length, right.length);
    expect(rows.some((r) => r.left.length && r.right.length && r.shared.length)).toBe(true);
    rows.forEach((r, i) => {
      for (const also of r.also) expect(also.row).not.toBe(i);
      expect(r.left.length + r.right.length).toBeGreaterThan(0);
    });
  });
});
