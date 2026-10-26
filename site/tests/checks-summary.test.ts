import { describe, expect, it } from "vitest";
import type { GraphMap } from "../src/api/types";
import type { Edition } from "../src/app/data";
import { checkSummary, goalCheckLine, kindHeadline, outcomeCounts, standingSentence } from "../src/checks/summary";
import { editionGraphFixture, fixture } from "./fixtures";

const map = fixture<GraphMap>("graph-map.json");
const graph = editionGraphFixture();
// Only the parts of an edition the summaries read.
const edition = { map, graph } as unknown as Edition;
const cards = new Map(map.records.evidence.map((e) => [e.id, e]));
const recordsOf = (id: string) => graph.nodes.get(id)!.evidenceIds!.map((e) => cards.get(e)!);

describe("check outcomes stay distinct", () => {
  it("counts every outcome per kind for the main Lean statement", () => {
    expect(Object.fromEntries(outcomeCounts(recordsOf("lean.full_support")))).toEqual({
      source_hash: { passed: 2 },
      lean_build: { not_run: 2 },
      comparator: { not_run: 2, unavailable: 2, failed: 1 },
      extraction: { not_run: 1, unavailable: 1 },
      semantic_review: { not_run: 1 },
    });
    expect([...outcomeCounts(recordsOf("lean.full_support")).keys()]).toEqual(["source_hash", "lean_build", "comparator", "extraction", "semantic_review"]);
  });

  it("heads each kind with its outcomes kept apart", () => {
    const full = outcomeCounts(recordsOf("lean.full_support"));
    expect(kindHeadline("comparator", full.get("comparator")!)).toBe("No successful Comparator result is recorded · 1 failed · 2 unavailable · 2 not run");
    expect(kindHeadline("source_hash", full.get("source_hash")!)).toBe("Source identity · 2 passed");
    expect(kindHeadline("lean_build", full.get("lean_build")!)).toBe("No Lean build run is recorded · 2 not run");
    expect(kindHeadline("extraction", full.get("extraction")!)).toBe("No successful dependency extraction result is recorded · 1 unavailable · 1 not run");
    const value = outcomeCounts(recordsOf("lean.value_consequences"));
    expect(kindHeadline("comparator", value.get("comparator")!)).toBe("No successful Comparator result is recorded · 1 failed · 1 unavailable · 2 not run");
    expect(kindHeadline("comparator", {})).toBe("No Comparator records");
    expect(kindHeadline("lean_build", { passed: 1, failed: 1 })).toBe("Lean build · 1 passed · 1 failed");
  });

  it("never says a run is missing when a failed or unavailable run is recorded, and never says independent", () => {
    const samples: Record<string, number>[] = [{ failed: 1 }, { unavailable: 1 }, { failed: 1, not_run: 2 }, { passed: 1 }, { passed: 1, unavailable: 1 }, { not_run: 3 }];
    for (const kind of ["source_hash", "lean_build", "comparator", "extraction", "semantic_review", "platform"])
      for (const counts of samples) {
        const line = kindHeadline(kind, counts);
        expect(line).not.toMatch(/independent|verified/i);
        if (counts.failed || counts.unavailable) {
          expect(line).not.toMatch(/no completed|run is recorded/i);
          expect(standingSentence({ kind, title: kind, counts })).not.toMatch(/no completed run|has not been run|has been run/i);
        }
      }
  });

  it("keeps the record panel's rows distinct for the real evidence", () => {
    for (const id of ["lean.full_support", "lean.value_consequences", "full_support", "scalar_value"]) {
      const rows = checkSummary(edition, graph.nodes.get(id)!.evidenceIds!);
      const comparator = rows.find((r) => r.kind === "comparator")!;
      expect(comparator.tone).toBe("failed");
      expect(comparator.outcome).toMatch(/^none passed: 1 failed, \d unavailable and 2 not run$/);
      expect(comparator.outcome).not.toMatch(/no completed/);
      expect(comparator.headline).toMatch(/^No successful Comparator result is recorded · 1 failed/);
      expect(rows.find((r) => r.kind === "extraction")!.outcome).toBe("none passed: 1 unavailable and 1 not run");
      expect(rows.find((r) => r.kind === "extraction")!.tone).toBe("open");
      expect(rows.find((r) => r.kind === "lean_build")!.outcome).toBe("not run (2)");
      expect(rows.find((r) => r.kind === "source_hash")!.outcome).toBe("passed (2)");
      expect(rows.find((r) => r.kind === "source_hash")!.tone).toBe("passed");
    }
    // A pass next to a failure is not shown as a pass.
    expect(checkSummary({ map: { records: { evidence: [{ id: "a", kind: "lean_build", status: "passed" }, { id: "b", kind: "lean_build", status: "failed" }] } } } as unknown as Edition, ["a", "b"])[0]).toMatchObject({
      tone: "failed",
      outcome: "1 passed; 1 failed",
    });
  });

  it("gives the theorem plate one short line and the number of check records", () => {
    expect(goalCheckLine(edition, "lean.full_support")).toEqual({ line: "No successful Comparator result recorded", total: 12 });
    expect(goalCheckLine(edition, "full_support")).toEqual({ line: "No successful Comparator result recorded", total: 12 });
    expect(goalCheckLine(edition, "lean.value_consequences")).toEqual({ line: "No successful Comparator result recorded", total: 11 });
    const qaoa = goalCheckLine(edition, "qaoa_thermodynamic_first");
    expect(qaoa).toEqual({ line: "No correspondence review run recorded", total: 3 });
    expect(goalCheckLine(edition, "lean.full_support", [])).toEqual({ line: "No check records", total: 0 });
  });
});
