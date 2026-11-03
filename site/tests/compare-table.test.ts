// The table's rules: what a row is, what order rows come in, and what they say about themselves.
import { describe, expect, it } from "vitest";
import type { AlignedLean, AlignedStatement, RecordAlignment } from "../src/api/lean";
import type { Stage } from "../src/api/types";
import { defaultLevels, holds, orderWords, rowFor, rowsSentence, sayings, tableRows } from "../src/compare/table";

const slice = (paper: Stage, role: AlignedStatement["role"], start: number): AlignedStatement => ({
  paper,
  role,
  markdown: `${paper} at ${start}`,
  start_byte: start,
  end_byte: start + 10,
  anchor: null,
  section: "1 One",
  heading_id: null,
});

const decl = (name: string, line = 1): AlignedLean => ({ name, module: "M", line, end_line: line + 1, relation: "states", note: "" });

const record = (statements: AlignedStatement[], lean: AlignedLean[] = []): RecordAlignment => ({ short: "t", lean, statements });

const records = {
  main: record([slice("short", "statement", 500), slice("expository", "statement", 90)], [decl("main")]),
  early: record([slice("short", "statement", 100), slice("expository", "explanation", 300)], [decl("early")]),
  late: record([slice("short", "derivation", 300), slice("expository", "statement", 40)], [decl("late")]),
  named: record([slice("short", "mention", 50), slice("expository", "statement", 60)]),
  shortOnly: record([slice("short", "statement", 400)]),
  leanOnly: record([], [decl("only", 7)]),
};

describe("a cell", () => {
  it("shows the strongest thing a paper says, and a bare mention says nothing", () => {
    const both = record([slice("short", "derivation", 1), slice("short", "statement", 9), slice("short", "mention", 0)]);
    expect(sayings(both, "short").map((s) => s.role)).toEqual(["statement", "derivation"]);
    expect(holds(records.named, "short")).toBe(false);
    expect(holds(records.named, "expository")).toBe(true);
    expect(holds(records.leanOnly, "lean")).toBe(true);
  });
});

describe("rows", () => {
  it("lists only steps every level shown has, so each row compares something", () => {
    expect(tableRows(records, ["short", "expository"], false).map((r) => r.id)).toEqual(["early", "late", "main"]);
    expect(tableRows(records, ["lean", "short", "expository"], false).map((r) => r.id)).toEqual(["early", "late", "main"]);
  });

  it("follows the first paper shown, so its column reads down as the paper does", () => {
    expect(tableRows(records, ["expository"], false).map((r) => r.id)).toEqual(["late", "named", "main", "early"]);
  });

  it("puts the main result first", () => {
    expect(tableRows(records, ["short", "expository"], false, "main").map((r) => r.id)).toEqual(["main", "early", "late"]);
  });

  it("adds the steps some levels lack after the first paper's own, and the Lean's own last", () => {
    expect(tableRows(records, ["lean", "short", "expository"], true).map((r) => r.id)).toEqual(["early", "late", "shortOnly", "main", "named", "leanOnly"]);
  });

  it("gives two steps that would say the very same words one row", () => {
    const twin = { ...records, twin: record(records.early.statements, records.early.lean) };
    const rows = tableRows(twin, ["short", "expository"], false);
    expect(rows.map((r) => r.id)).toEqual(["early", "late", "main"]);
    expect(rows[0].also).toEqual(["twin"]);
    expect(rowFor(rows, "twin")?.id).toBe("early");
  });

  it("keeps two steps apart when one column differs", () => {
    const other = { ...records, other: record(records.early.statements, [decl("different")]) };
    expect(tableRows(other, ["lean", "short"], false).map((r) => r.id)).toContain("other");
  });
});

describe("words", () => {
  it("says how many steps appear, and where", () => {
    expect(rowsSentence(["short"], 44)).toBe("44 steps appear in the short paper.");
    expect(rowsSentence(["short", "expository"], 30)).toBe("30 steps appear in both the short paper and the exposition.");
    expect(rowsSentence(["lean", "short", "expository"], 25)).toBe("25 steps appear in all three columns shown.");
    expect(rowsSentence(["lean", "long", "short", "expository"], 1)).toBe("1 step appears in all four columns shown.");
    expect(rowsSentence(["short", "expository"], 50, true)).toBe("50 steps appear in at least one column shown.");
  });

  it("says whose order the rows are in", () => {
    expect(orderWords(["lean", "short"])).toBe("In the order of the short paper.");
    expect(orderWords(["lean"])).toBe("In the order of the source.");
  });
});

describe("starting levels", () => {
  it("fit the width, with the Lean first", () => {
    expect(defaultLevels(1920)).toEqual(["lean", "long", "short", "expository"]);
    expect(defaultLevels(1440)).toEqual(["lean", "short", "expository"]);
    expect(defaultLevels(1100)).toEqual(["lean", "short"]);
  });
});
