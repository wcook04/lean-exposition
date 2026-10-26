import { describe, expect, it } from "vitest";
import type { Stage } from "../src/api/types";
import { coverageOf, firstSentence, relationName, stepVerb, unusedBy, warrantStatus } from "../src/panels/model";
import { fixture, graphFixture } from "./fixtures";

const graph = graphFixture();
const papers = fixture<{ stage: Stage; paper_scope: { selected_goal_ids: string[] } }[]>("papers.json");
const goals = (stage: Stage) => papers.find((p) => p.stage === stage)!.paper_scope.selected_goal_ids;

describe("account coverage", () => {
  it("counts the long record's own, relied-on and left-out records", () => {
    const c = coverageOf(graph, "long");
    expect([c.own.length, c.relied.length, c.out.length]).toEqual([120, 3, 6]);
    expect(c.relied.sort()).toEqual(["support.endpoint_chord_area", "support.strict_increase", "support.terminal_defect"]);
  });

  it("counts the short paper and the exposition", () => {
    const s = coverageOf(graph, "short");
    const e = coverageOf(graph, "expository");
    expect([s.own.length, s.relied.length]).toEqual([49, 50]);
    expect([e.own.length, e.relied.length]).toEqual([35, 60]);
  });

  it("finds that no result the long record proves uses the records it leaves out", () => {
    for (const id of coverageOf(graph, "long").out) expect(unusedBy(graph, id, goals("long"))).toBe(true);
    expect(unusedBy(graph, "support.strict_increase", goals("long"))).toBe(false);
  });
});

describe("step wording", () => {
  it("names each relation as recorded and reads it from the consumer", () => {
    expect(stepVerb("supports")).toBe("uses");
    expect(stepVerb("assumes")).toBe("assumes");
    expect(relationName("supports")).toBe("Recorded support");
    expect(relationName("assumes")).toBe("Explicit assumption");
    expect(relationName("formalizes")).toBe("Recorded Lean correspondence");
  });

  it("never calls a review independent unless that is what is not run", () => {
    expect(warrantStatus("not_run")).toBe("Recorded explanation · independent review not run");
    expect(warrantStatus("passed")).toBe("Recorded explanation · review record: passed");
    expect(warrantStatus("passed")).not.toMatch(/independently reviewed/);
  });

  it("takes the first sentence as a gist", () => {
    expect(firstSentence("For a positive height, q' is below its chord. Hence more.")).toBe("For a positive height, q' is below its chord.");
    expect(firstSentence("No full stop here")).toBe("No full stop here");
  });
});
