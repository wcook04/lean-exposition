// An edge of the argument that rests only on the paper's own stated logic (evidence paper_logic.*)
// is told apart from one a Lean dependency also supports: the graph draws the first dashed.
import { describe, expect, it } from "vitest";
import { onlyPaperLogic, type ArgEdge } from "../src/model/graph";

const edge = (evidenceIds?: string[]): ArgEdge => ({
  key: "a>b", from: "a", to: "b", kind: "supports", linkIds: [], scoped: false, semanticClass: "graph_edge", evidenceIds,
});

describe("paper-logic edges", () => {
  it("an edge with only the paper's stated logic is the paper's", () => {
    expect(onlyPaperLogic(edge(["paper_logic.theorem-1.1.corollary-7.2"]))).toBe(true);
    expect(onlyPaperLogic(edge(["paper_logic"]))).toBe(true);
  });
  it("an edge Lean's dependencies also support stays a Lean edge", () => {
    expect(onlyPaperLogic(edge(["lean_dependencies", "paper_logic.proposition-b.14.lemma-b.2"]))).toBe(false);
    expect(onlyPaperLogic(edge(["lean_dependencies"]))).toBe(false);
    expect(onlyPaperLogic(edge(undefined))).toBe(false);
  });
});
