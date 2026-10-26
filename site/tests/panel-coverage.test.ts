import { describe, expect, it } from "vitest";
import type { Stage } from "../src/api/types";
import { coverageOf, firstSentence, stepVerb, unusedBy, warrantStatus } from "../src/panels/model";
import { fixture, graphFixture } from "./fixtures";

const graph = graphFixture();
const papers = fixture<{ stage: Stage; paper_scope: { selected_goal_ids: string[] } }[]>("papers.json");
const goals = (stage: Stage) => papers.find((p) => p.stage === stage)!.paper_scope.selected_goal_ids;

describe("account coverage", () => {
  it("counts the long record's own, relied-on and left-out records", () => {
    const c = coverageOf(graph, "long");
    expect([c.own.length, c.relied.length, c.out.length]).toEqual([109, 3, 6]);
    expect(c.relied.sort()).toEqual(["support.endpoint_chord_area", "support.strict_increase", "support.terminal_defect"]);
  });

  it("counts the short paper and the exposition", () => {
    const s = coverageOf(graph, "short");
    const e = coverageOf(graph, "expository");
    expect([s.own.length, s.relied.length]).toEqual([46, 47]);
    expect([e.own.length, e.relied.length]).toEqual([35, 57]);
  });

  it("finds that no result the long record proves uses the records it leaves out", () => {
    for (const id of coverageOf(graph, "long").out) expect(unusedBy(graph, id, goals("long"))).toBe(true);
    expect(unusedBy(graph, "support.strict_increase", goals("long"))).toBe(false);
  });
});

describe("step wording", () => {
  it("reads each kind of step from the prerequisite to the consumer", () => {
    expect(stepVerb("supports")).toBe("helps prove");
    expect(stepVerb("assumes")).toBe("is assumed by");
    expect(stepVerb("formalizes")).toBe("states in Lean");
  });

  it("states a warrant's review honestly", () => {
    expect(warrantStatus("not_run", "Authored relation warrant; independent semantic acceptance not run")).toBe(
      "Recorded by the authors; not independently reviewed.",
    );
    expect(warrantStatus("not_run", "Source-located authored warrant; independent semantic review pending")).toBe(
      "Located in the sources by the authors; not independently reviewed.",
    );
    expect(warrantStatus("passed", "x")).toMatch(/independently reviewed\.$/);
  });

  it("takes the first sentence as a gist", () => {
    expect(firstSentence("For a positive height, q' is below its chord. Hence more.")).toBe("For a positive height, q' is below its chord.");
    expect(firstSentence("No full stop here")).toBe("No full stop here");
  });
});
