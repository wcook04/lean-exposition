import { describe, expect, it } from "vitest";
import { changeAtLine, counterpart, kindWords, type ChangeMap } from "../src/reader/adapted/changes";

// Authors: paragraphs at 10, 14, 18, 22. Edition: 10 unchanged, 14 changed (c1), 18 added (c2), 22 = authors' 18, 26 = 22.
const map: ChangeMap = {
  schema: "adapted-changes/1",
  authors: "short",
  adapted: "long",
  changes: [
    { id: "c1", part: "E1", kind: "clarification", authors: ["1#2"], note: "n1", sources: [], status: "", adapted: ["1#2"], adapted_lines: [[14, 16]], adapted_text: "B2", replaced: ["1#2"], authors_text: "B", authors_lines: [[14, 16]] },
    { id: "c2", part: "E1", kind: "added-justification", authors: ["1#2"], note: "n2", sources: [], status: "", adapted: ["1#3"], adapted_lines: [[18, 20]], adapted_text: "New", replaced: [], authors_text: "", authors_lines: [] },
  ],
  paragraphs: [
    { authors: "1#1", adapted: "1#1", change: null, authors_lines: [10, 12], adapted_lines: [10, 12] },
    { authors: "1#2", adapted: "1#2", change: "c1", authors_lines: [14, 16], adapted_lines: [14, 16] },
    { authors: null, adapted: "1#3", change: "c2", authors_lines: null, adapted_lines: [18, 20] },
    { authors: "1#3", adapted: "1#4", change: null, authors_lines: [18, 20], adapted_lines: [22, 24] },
    { authors: "1#4", adapted: "1#5", change: null, authors_lines: [22, 24], adapted_lines: [26, 28] },
  ],
};

describe("an adapted edition's paragraph alignment", () => {
  it("keeps the place by paragraph in both directions", () => {
    expect(counterpart(map, "adapted", 22)).toEqual({ line: 18, exact: true });
    expect(counterpart(map, "authors", 18)).toEqual({ line: 22, exact: true });
    expect(counterpart(map, "adapted", 27)).toEqual({ line: 22, exact: true });
    expect(counterpart(map, "adapted", 14)).toEqual({ line: 14, exact: true });
  });

  it("lands an added paragraph on the one before it, and says so", () => {
    expect(counterpart(map, "adapted", 18)).toEqual({ line: 14, exact: false });
  });

  it("keeps a heading's distance before the next shared paragraph", () => {
    expect(counterpart(map, "adapted", 25)).toEqual({ line: 21, exact: true });
  });

  it("finds the change a line of the edition shows", () => {
    expect(changeAtLine(map, 19)?.id).toBe("c2");
    expect(changeAtLine(map, 23)).toBeNull();
  });

  it("names each kind in words", () => {
    expect(kindWords("added-justification")).toBe("Added justification");
    expect(kindWords("formal-note")).toBe("Note on the formal statement");
    expect(kindWords("edition-credit")).toBe("Edition credit");
  });
});
