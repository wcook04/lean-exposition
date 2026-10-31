import { describe, expect, it } from "vitest";
import { editionNote, outcomeParts, rowNote } from "../src/checks/ChecksPage";
import { pageWindow } from "../src/search/SearchPage";

const card = (kind: string, status: string, i: number) => ({ id: `${kind}-${i}`, kind, status, label: "", ref: "" });

describe("check rows keep outcomes distinct", () => {
  it("lists failures first and never merges failed, unavailable and not run", () => {
    expect(outcomeParts({ not_run: 2, failed: 1, unavailable: 2 })).toEqual([
      { status: "failed", n: 1 },
      { status: "unavailable", n: 2 },
      { status: "not_run", n: 2 },
    ]);
  });

  it("says no successful Comparator result is recorded only when none passed", () => {
    expect(rowNote("comparator", { failed: 1, unavailable: 2, not_run: 2 })).toBe("No successful Comparator result is recorded.");
    expect(rowNote("comparator", { passed: 1, failed: 1 })).toBeNull();
    expect(rowNote("lean_build", { not_run: 2 })).toBeNull();
    expect(rowNote("extraction", { unavailable: 1, not_run: 1 })).toBe("No successful run is recorded.");
    expect(rowNote("semantic_review", { not_run: 207 })).toMatch(/^All written, none independently run\./);
    expect(rowNote("semantic_review", { not_run: 3, passed: 1 })).toBeNull();
  });

  it("states the edition's position once, from the counts", () => {
    const cards = [
      ...Array.from({ length: 6 }, (_, i) => card("semantic_review", "not_run", i)),
      card("source_hash", "passed", 0),
      card("comparator", "failed", 0),
    ];
    const note = editionNote(cards);
    expect(note).toContain("Most recorded checks on this site have not been run (6 of 8).");
    expect(note).toContain("no recorded explanation of why one record is used for another has been independently reviewed");
    expect(note).not.toMatch(/%|verified/);
    const reviewed = editionNote([card("semantic_review", "passed", 0), card("lean_build", "not_run", 0), card("comparator", "failed", 1)]);
    expect(reviewed).toContain("the reviewer is not recorded as independent");
  });
});

describe("search result pages", () => {
  it("covers every result exactly once across pages", () => {
    expect(pageWindow(51, 1)).toEqual({ from: 1, to: 20, pages: 3, page: 1 });
    expect(pageWindow(51, 3)).toEqual({ from: 41, to: 51, pages: 3, page: 3 });
    expect(pageWindow(51, 9).page).toBe(3);
    expect(pageWindow(0, 1)).toEqual({ from: 0, to: 0, pages: 1, page: 1 });
  });
});
