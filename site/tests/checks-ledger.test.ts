import { describe, expect, it } from "vitest";
import type { GraphMap } from "../src/api/types";
import { countsInWords, failureLine, groupByKind, identifierDate, inStatedTimeOrder, standingSentence, statedDate, type EvidenceCard } from "../src/checks/summary";
import { batches } from "../src/checks/evidence";
import { fixture } from "./fixtures";

const card = (id: string, kind: string, status: string): EvidenceCard => ({ id, kind, status, label: id, ref: `r/${id}` });

describe("check grouping", () => {
  it("keeps every kind separate, in the page's order, including empty kinds", () => {
    const groups = groupByKind([card("a", "comparator", "failed"), card("b", "source_hash", "passed"), card("c", "comparator", "not_run"), card("d", "zz_new", "passed")]);
    expect(groups.map((g) => g.kind)).toEqual(["source_hash", "lean_build", "comparator", "extraction", "semantic_review", "platform", "zz_new"]);
    expect(groups.find((g) => g.kind === "comparator")!.counts).toEqual({ failed: 1, not_run: 1 });
    expect(groups.find((g) => g.kind === "platform")!.cards).toEqual([]);
  });

  it("groups the captured edition's evidence without losing a record", () => {
    const map = fixture<GraphMap>("graph-map.json");
    const cards = map.records.evidence as EvidenceCard[];
    const groups = groupByKind(cards);
    expect(groups.reduce((s, g) => s + g.cards.length, 0)).toBe(cards.length);
    const comparator = groups.find((g) => g.kind === "comparator")!;
    if (comparator.cards.length > 0 && !comparator.counts.passed) expect(standingSentence(comparator)).toMatch(/^No successful Comparator result is recorded/);
  });

  it("words counts and standing without claiming verification", () => {
    expect(countsInWords({ not_run: 4, failed: 2, unavailable: 2 })).toBe("2 failed, 2 unavailable and 4 not run");
    expect(countsInWords({ passed: 3 })).toBe("3 passed");
    const source = standingSentence({ kind: "source_hash", title: "Source files", counts: { passed: 3 } });
    expect(source).toMatch(/SHA-256 hash and length/);
    expect(source).toMatch(/do not examine whether the mathematics/);
    for (const kind of ["source_hash", "lean_build", "comparator", "extraction", "semantic_review", "platform"])
      for (const counts of [{}, { passed: 2 }, { not_run: 3 }, { failed: 1, passed: 1 }] as Record<string, number>[])
        expect(standingSentence({ kind, title: kind, counts })).not.toMatch(/verified/i);
    expect(standingSentence({ kind: "semantic_review", title: "Correspondence review", counts: { not_run: 204 } })).toBe(
      "None of the 204 correspondence reviews has been run.",
    );
  });

  it("reads dates only from a record's text and orders by them", () => {
    expect(statedDate("Observed 2026-10-23T17:03:01.081472+00:00. The executable was absent")).toEqual({ key: "2026-10-23T17:03:01.081472", text: "23 October 2026" });
    expect(statedDate("Observed 24 October 2026: every file matched")?.key).toBe("2026-10-24");
    expect(statedDate("Unperformed command at 450c8947971dbad9be943b8705ea96f822240961")).toBeNull();
    const { dated, undated } = inStatedTimeOrder([
      { id: "late", details: "Observed 2026-10-25T17:48:54+00:00." },
      { id: "none", details: "No run." },
      { id: "early", details: "Observed 2026-10-23T17:03:01+00:00." },
    ]);
    expect(dated.map((d) => d.record.id)).toEqual(["early", "late"]);
    expect(undated.map((d) => d.id)).toEqual(["none"]);
  });

  it("says when and what for a recorded failure, and never invents a date", () => {
    expect(identifierDate("full_support_solution_build_failure_20261023")).toBe("23 October 2026");
    expect(identifierDate("lean_build_not_run")).toBeNull();
    expect(failureLine({ id: "full_support_solution_build_failure_20261023", label: "x" })).toMatch(/^23 October 2026\. Comparator stopped .*AbsIncrement/);
    expect(failureLine({ id: "other", label: "A label" }, { details: "Stopped early." })).toBe("Stopped early.");
    expect(failureLine({ id: "other", label: "A label" })).toBe("A label");
  });

  it("batches record requests at 32 refs", () => {
    const refs = Array.from({ length: 70 }, (_, i) => `r${i}`);
    expect(batches(refs).map((b) => b.length)).toEqual([32, 32, 6]);
  });
});
