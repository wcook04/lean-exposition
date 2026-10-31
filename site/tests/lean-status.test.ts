import { describe, expect, it } from "vitest";
import { leanFill, markOfDeclaration, markOfRelations, markWords } from "../src/model/leanStatus";

describe("what the Lean holds of a record", () => {
  it("reads two signals from the alignment's relations", () => {
    expect(markOfRelations(["states", "defines"], false)).toEqual({ shape: "round", statement: "whole", proof: "whole" });
    expect(markOfRelations(["contains", "proof"], false)).toEqual({ shape: "round", statement: "whole", proof: "whole" });
    expect(markOfRelations(["part"], false)).toEqual({ shape: "round", statement: "part", proof: "part" });
    expect(markOfRelations(["part", "proof"], false)).toEqual({ shape: "round", statement: "part", proof: "whole" });
    expect(markOfRelations(["proof"], false)).toEqual({ shape: "round", statement: "none", proof: "whole" });
  });

  it("draws a definition as a box, with nothing to prove", () => {
    expect(markOfRelations(["defines"], false)).toEqual({ shape: "box", statement: "whole", proof: "none" });
    expect(markOfRelations(["defines", "part"], true)).toEqual({ shape: "box", statement: "whole", proof: "part" });
  });

  it("invents nothing for a record with no Lean", () => {
    const mark = markOfRelations([], false);
    expect(mark).toEqual({ shape: "round", statement: "none", proof: "none" });
    expect(markWords(mark)).toBe("No Lean linked");
  });

  it("takes a declaration's kind from the index, and a sorry away from its proof", () => {
    expect(markOfDeclaration("theorem", false)).toEqual({ shape: "round", statement: "whole", proof: "whole" });
    expect(markOfDeclaration("theorem", true).proof).toBe("none");
    expect(markOfDeclaration("structure", false)).toEqual({ shape: "box", statement: "whole", proof: "none" });
  });
});

describe("the card's fill", () => {
  it("is green for what the Lean holds whole, pale for a part, plain for none", () => {
    expect(leanFill(markOfRelations(["states"], false))).toBe("whole");
    expect(leanFill(markOfRelations(["defines"], false))).toBe("whole");
    expect(leanFill(markOfRelations(["part", "proof"], false))).toBe("part");
    expect(leanFill(markOfRelations(["proof"], false))).toBe("part");
    expect(leanFill(markOfRelations([], false))).toBe("none");
  });

  it("is pale for a theorem whose proof has a sorry", () => {
    expect(leanFill(markOfDeclaration("theorem", true))).toBe("part");
    expect(leanFill(markOfDeclaration("structure", false))).toBe("whole");
  });
});
