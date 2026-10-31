// @vitest-environment jsdom
import { readFileSync } from "node:fs";
import { join } from "node:path";
import { describe, expect, it } from "vitest";
import type { Alignment, LeanModule, LeanNames } from "../src/api/lean";
import { buildCode } from "../src/lean/CodeView";
import { buildIndex, collectLocals, findDecl, makeScope, mathlibUrl, resolveName, statementShape, type Scope } from "../src/lean/resolve";
import { texHtml } from "../src/figures/tex";
import { tokenize } from "../src/lean/tokenize";

const root = join(__dirname, "../public/edition");
const json = (name: string) => JSON.parse(readFileSync(join(root, name), "utf8"));
const startup = json("index.json");
const names: LeanNames = json(startup.responses["/lean/names"]);
const alignment: Alignment = json(startup.responses["/alignment"]);
const index = buildIndex(names);
const terms = new Map(alignment.dictionary.map((t) => [t.name, t]));
const main: LeanModule = json("lean/module/OAI.Probability.SKSupport.Main.json");

function scopeOf(short: string): Scope {
  const decl = main.declarations.find((d) => d.short === short)!;
  const scope = makeScope(decl, main, index, terms);
  const lines = main.source.split("\n").slice(decl.line - 1, decl.end_line).join("\n");
  collectLocals(tokenize(lines), scope.locals);
  return scope;
}

describe("name resolution", () => {
  const scope = scopeOf("full_support");

  it("prefers the proved declaration over the challenge copy", () => {
    expect(findDecl(index, "OAI.ZeroTemperatureSK.full_support")?.module).toBe("OAI.Probability.SKSupport.Main");
    expect(findDecl(index, "OAI.ZeroTemperatureSK.full_support", "ComparatorChallenges.SKFullSupport")?.module).toBe("ComparatorChallenges.SKFullSupport");
  });

  it("finds a short name through what the declaration uses", () => {
    const found = resolveName("minimizer_full_support_actual", scope);
    expect(found).toMatchObject({ kind: "decl", row: { name: "OAI.ZeroTemperatureSK.minimizer_full_support_actual" } });
  });

  it("attaches the dictionary term", () => {
    const found = resolveName("OrderParameter", scope);
    expect(found?.kind === "decl" && found.term?.tex).toBe("\\mathcal U");
  });

  it("leaves bound names alone but reads a field through the binder's type", () => {
    expect(resolveName("hmin", scope)).toBeNull();
    expect(resolveName("γ", scope)).toBeNull();
    expect(resolveName("γ.val", scope)).toMatchObject({ kind: "decl", row: { name: "OAI.ZeroTemperatureSK.OrderParameter.val" } });
  });

  it("calls a library name Mathlib's and links its search page", () => {
    expect(resolveName("Real.toNNReal", scope)).toEqual({ kind: "mathlib", name: "Real.toNNReal" });
    expect(resolveName("integral_congr_ae", scope)).toEqual({ kind: "mathlib", name: "integral_congr_ae" });
    expect(resolveName("ℝ", scope)).toMatchObject({ kind: "mathlib", name: "Real" });
    expect(mathlibUrl("Set.Ico")).toBe("https://leanprover-community.github.io/mathlib4_docs/search.html?q=Set.Ico");
  });

  it("does not guess at short unknown words", () => {
    expect(resolveName("zz", scope)).toBeNull();
  });
});

describe("the dictionary", () => {
  it("typesets every term and points at a declaration", () => {
    for (const term of alignment.dictionary) {
      if (term.tex) expect(() => texHtml(term.tex as string)).not.toThrow();
      expect(index.byName.has(term.name), term.name).toBe(true);
      expect(term.words).not.toMatch(/—/);
    }
  });
});

describe("what a statement says", () => {
  it("finds a conclusion that is one predicate, and its hypotheses", () => {
    const shape = statementShape(tokenize("theorem full_support (W : BrownianSystem Ω) (γ : OrderParameter)\n    (hmin : IsMinimizer W γ) : FullSupportConclusion W γ := by"));
    expect(shape.conclusion).toBe("FullSupportConclusion");
    expect(shape.hypotheses).toEqual(["BrownianSystem", "OrderParameter", "IsMinimizer"]);
  });

  it("reads past an implication and a quantifier", () => {
    expect(statementShape(tokenize("lemma a : ∀ x, P x → Q x := by")).conclusion).toBe("Q");
  });

  it("has no single conclusion for a conjunction or an equation", () => {
    expect(statementShape(tokenize("lemma a : P x ∧ Q x := by")).conclusion).toBeUndefined();
    expect(statementShape(tokenize("lemma a : f x = 1 := by")).conclusion).toBeUndefined();
  });
});

describe("a clause in the code", () => {
  const scope = scopeOf("full_support");
  const tokens = tokenize("theorem t (W : S) :\n    IsMinimizer W γ := by");

  it("marks the tokens it covers, spaces included", () => {
    const code = buildCode(tokens, 1, scope, "IsMinimizer W");
    expect(code.marked).toBe(true);
    const marked = code.lines.flatMap((l) => l.parts).filter((p) => p.className.includes("lean-clause")).map((p) => p.text);
    expect(marked.join("")).toBe("IsMinimizer W");
  });

  it("changes nothing when the clause is absent", () => {
    const code = buildCode(tokens, 1, scope, "not here");
    expect(code.marked).toBe(false);
    expect(code.lines.flatMap((l) => l.parts).some((p) => p.className.includes("lean-clause"))).toBe(false);
  });
});
