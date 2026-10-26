import { describe, expect, it } from "vitest";
import { evidenceCitations } from "../src/model/graph";
import { editionGraphFixture, tableFixture } from "./fixtures";

const graph = editionGraphFixture();
const edges = tableFixture("edges");
const evidence = new Map(tableFixture("evidence").map((e) => [e.id, e]));

describe("warrant sharing from evidence identity", () => {
  const cited = evidenceCitations(edges);

  it("counts how many stored relations cite each evidence record", () => {
    const id = "ordinary_deductions_review_20261026_r9";
    expect(cited.get(id)).toBe(edges.filter((e) => e.evidence_ids.includes(id)).length);
    expect(cited.get(id)).toBeGreaterThan(1);
  });

  it("marks a warrant shared exactly when its evidence is cited by more than one relation", () => {
    const withWarrant = graph.edges.filter((e) => e.warrant);
    expect(withWarrant.length).toBeGreaterThan(0);
    for (const edge of withWarrant) {
      const w = edge.warrant!;
      expect(w.sharedWith).toBe(cited.get(w.evidenceId));
      expect(w.shared).toBe(w.sharedWith > 1);
      expect(w.details).toBe(evidence.get(w.evidenceId)!.details);
    }
    const shared = withWarrant.filter((e) => e.warrant!.shared);
    const own = withWarrant.filter((e) => !e.warrant!.shared);
    expect(shared.length).toBeGreaterThan(0);
    expect(own.length).toBeGreaterThan(shared.length);
  });

  it("keeps each recorded application on the edge that makes it", () => {
    const stored = edges.filter((e) => e.application);
    const applied = graph.edges.filter((e) => e.application);
    expect(applied.map((e) => `${e.from}→${e.to}`).sort()).toEqual(stored.map((e) => `${e.from}→${e.to}`).sort());
    for (const edge of applied) {
      const record = stored.find((e) => e.from === edge.from && e.to === edge.to)!;
      expect(edge.application!.record).toEqual(record.application);
      expect(Object.keys(edge.application!.shared).length).toBeGreaterThan(0);
    }
  });
});
