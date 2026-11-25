// The link previewed between links is the link Next lands on; graph choices map only to recorded places.
import { describe, expect, it } from "vitest";
import { hasOpeningMap, inspectionTarget, linkPreview, stepTarget, type Side, type StepFrom, type StepWays } from "../src/reader/page/nextLink";

// Four statements: 0 and 1 in part 2, 2 in part 5, 3 in part 9. Segment = statement index.
const part = [2, 2, 5, 9];
function ways(side: Record<number, Side> = {}): StepWays {
  const stops = [0, 1, 2, 3];
  return {
    stops,
    stepFrom: (segment, by) => stops[by > 0 ? stops.findIndex((t) => t > segment) : stops.findLastIndex((t) => t < segment)] ?? null,
    segmentOf: (t) => t,
    partOf: (t) => part[t],
    side: (t) => side[t],
  };
}
const at = (t: number) => `b${t * 10}-${t * 10 + 5}`;
const from = (over: Partial<StepFrom>): StepFrom => ({ unstarted: false, pinned: null, segment: null, part: 0, ...over });

describe("the link preview and Next", () => {
  it("previews the first link at the opening, and Next lands there", () => {
    const f = from({ unstarted: true });
    expect(linkPreview(f, ways(), at)).toEqual({ tie: 0, at: at(0), kind: "next" });
    expect(stepTarget(1, f, ways())).toBe(0);
  });

  it("in a gap, skips a link of the same part already passed, whether or not the next part is mounted", () => {
    const f = from({ part: 2 });
    const w = ways({ 0: "above" }); // statement 1 is not laid out: undefined counts as ahead
    expect(linkPreview(f, w, at)?.tie).toBe(1);
    expect(stepTarget(1, f, w)).toBe(1);
    expect(stepTarget(-1, f, w)).toBe(0);
  });

  it("between parts, previews the first link of a later part", () => {
    const f = from({ part: 6 });
    expect(linkPreview(f, ways(), at)).toEqual({ tie: 3, at: at(3), kind: "next" });
    expect(stepTarget(1, f, ways())).toBe(3);
  });

  it("after the last link, keeps the last one passed with its own cue, and Next has nowhere to go", () => {
    const f = from({ part: 12 });
    expect(linkPreview(f, ways(), at)).toEqual({ tie: 3, at: at(3), kind: "last" });
    expect(stepTarget(1, f, ways())).toBeNull();
  });

  it("follows the segment at the line rather than previewing", () => {
    expect(stepTarget(1, from({ segment: 1, part: 2 }), ways())).toBe(2);
    expect(stepTarget(1, from({ pinned: 2, part: 0 }), ways())).toBe(3);
  });
});

describe("what the pane opens on, and where a graph choice goes", () => {
  const on = (id: string) => ["goal", "a"].includes(id);
  it("has an opening map only with the main result on the graph and a passage naming a graph record", () => {
    expect(hasOpeningMap(on, "goal", [{ claim_ids: ["a"], assumption_ids: [] }])).toBe(true);
    expect(hasOpeningMap(on, "goal", [{ claim_ids: ["x"], assumption_ids: [] }])).toBe(false);
    expect(hasOpeningMap(on, undefined, [{ claim_ids: ["a"], assumption_ids: [] }])).toBe(false);
  });

  it("offers a statement, else a recorded passage, else nothing", () => {
    expect(inspectionTarget(3, at, "p")).toEqual({ at: at(3), tie: 3 });
    expect(inspectionTarget(null, at, "p")).toEqual({ anchor: "p" });
    expect(inspectionTarget(null, at, null)).toBeNull();
  });
});
