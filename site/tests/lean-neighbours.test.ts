// A declaration that is no step of the map is drawn with its Lean neighbours: itself as the root,
// what its statement uses before what its proof uses, at most eight and "and N more", and the
// project's declarations that use it listed apart. Names from outside the project are left out.
import { describe, expect, it } from "vitest";
import { declarationNeighbourhood } from "../src/reader/page/leanNeighbours";

const row = { kind: "lemma", module: "M", line: 1 };
const project = new Set(["A.s1", "A.p1", "A.p2", "A.u1", ...Array.from({ length: 10 }, (_, i) => `A.q${i}`), ...Array.from({ length: 11 }, (_, i) => `A.v${i}`)]);

function build(uses: string[], usedBy: string[]) {
  return declarationNeighbourhood({
    name: "A.d",
    title: "The declaration",
    kind: "theorem",
    statement: "theorem d (h : s1 x) : True",
    uses,
    usedBy,
    rowOf: (name) => (project.has(name) ? row : undefined),
    titleOf: (name) => `Title of ${name}`,
    origin: "authored" as never,
  });
}

describe("a declaration's Lean neighbourhood", () => {
  it("roots the drawing at the declaration, statement uses first, outside names left out", () => {
    const n = build(["A.p1", "Mathlib.foo", "A.s1", "A.p2"], ["A.u1", "Mathlib.bar"]);
    expect(n.graph.goals).toEqual(["A.d"]);
    expect(n.graph.nodes.get("A.d")!.kind).toBe("goal");
    expect(n.graph.out.get("A.d")!.map((e) => [e.to, e.kind])).toEqual([
      ["A.s1", "lean_type_dependency"],
      ["A.p1", "supports"],
      ["A.p2", "supports"],
    ]);
    expect(n.users).toEqual([{ name: "A.u1", title: "Title of A.u1", plain: true }]);
    expect(n.moreUsers).toBe(0);
  });

  it("draws at most eight uses and counts the rest, and lists at most eight users", () => {
    const n = build(Array.from({ length: 10 }, (_, i) => `A.q${i}`), Array.from({ length: 11 }, (_, i) => `A.v${i}`));
    expect(n.graph.out.get("A.d")!.length).toBe(9);
    expect(n.graph.nodes.get("A.d#more")!.label).toBe("and 2 more it uses");
    expect(n.moreUses).toBe(2);
    expect(n.users.length).toBe(8);
    expect(n.moreUsers).toBe(3);
  });
});
