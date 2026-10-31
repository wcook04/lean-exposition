// @vitest-environment node
import { readFileSync, readdirSync } from "node:fs";
import { join } from "node:path";
import { describe, expect, it } from "vitest";
import { collectLocals } from "../src/lean/resolve";
import { tokenLines, tokenize } from "../src/lean/tokenize";

const edition = join(__dirname, "../public/edition/lean/module");
const moduleSource = (name: string): string => JSON.parse(readFileSync(join(edition, `${name}.json`), "utf8")).source;
const kinds = (src: string, signature = true) => tokenize(src, { signature }).filter((t) => t.kind !== "space").map((t) => `${t.kind}:${t.text}`);

describe("the Lean tokenizer on real source", () => {
  it("returns every module unchanged and quickly", () => {
    const files = readdirSync(edition).filter((f) => f.endsWith(".json"));
    expect(files.length).toBeGreaterThan(300);
    let largest = "";
    for (const file of files) {
      const source: string = JSON.parse(readFileSync(join(edition, file), "utf8")).source;
      if (source.length > largest.length) largest = source;
      expect(tokenize(source).map((t) => t.text).join("")).toBe(source);
    }
    const doubled = Array.from({ length: Math.ceil(2000 / largest.split("\n").length) }, () => largest).join("\n");
    const start = performance.now();
    tokenize(doubled);
    expect(performance.now() - start).toBeLessThan(100);
  });

  it("reads the main theorem's proof", () => {
    const source = moduleSource("OAI.Probability.SKSupport.Main");
    const k = kinds(source);
    expect(k).toContain("tactic:have");
    expect(k).toContain("tactic:simpa");
    expect(k).toContain("tactic:refine");
    expect(k).toContain("tactic:filter_upwards");
    expect(k).toContain("name:minimizer_full_support_actual");
    expect(k).toContain("type:Real.toNNReal".replace("type:", "name:"));
    expect(k).toContain("op:=ᵐ");
    expect(k).toContain("binder:ξ");
  });
});

describe("the Lean tokenizer on each form", () => {
  it("nests comments and separates docstrings", () => {
    expect(kinds("/- a /- b -/ c -/ def x")[0]).toBe("comment:/- a /- b -/ c -/");
    expect(kinds("/-- says -/ def x")[0]).toBe("doc:/-- says -/");
    expect(kinds("-- end\ndef x")[0]).toBe("comment:-- end");
  });

  it("reads strings, numbers, attributes and dotted names", () => {
    expect(kinds('"a\\"b"')).toEqual(['string:"a\\"b"']);
    expect(kinds("(0.5 : ℝ)")).toContain("number:0.5");
    expect(kinds("@[simp] lemma a")[0]).toBe("attr:@[simp]");
    expect(kinds("hs.2.1 Set.Ico")).toEqual(["name:hs.2.1", "type:Set.Ico"]);
    expect(kinds("t.property.1,NNReal.coe_one")).toEqual(["name:t.property.1", "op:,", "name:NNReal.coe_one"]);
  });

  it("does not take a field called bound for the tactic", () => {
    expect(kinds("structure C where\n  bound : ∀ s, s", true)).toContain("name:bound");
    expect(kinds("by\n  bound", false)).toContain("tactic:bound");
  });

  it("marks binders in signatures but not type ascriptions in a body", () => {
    const k = kinds("theorem t (W : S Ω) {μ : M} : f (g x : ℝ) = 0 := by\n  intro a b\n  obtain ⟨c, hc⟩ := h\n  have d := c");
    for (const name of ["W", "μ", "a", "b", "c", "hc", "d"]) expect(k).toContain(`binder:${name}`);
    expect(k).toContain("name:g");
  });

  it("records the type written on a binder", () => {
    const locals = new Map<string, string | undefined>();
    collectLocals(tokenize("theorem t (γ : OrderParameter) (x y : ℝ) : True"), locals);
    expect(locals.get("γ")).toBe("OrderParameter");
    expect(locals.get("y")).toBe("ℝ");
  });

  it("splits lines and keeps the indent out of the pieces", () => {
    const lines = tokenLines(tokenize("a\n    b /- x\n  y -/ c"));
    expect(lines).toHaveLength(3);
    expect(lines[1].indent).toBe(4);
    expect(lines[1].pieces[0].text).toBe("b");
    expect(lines[2].pieces[0].text).toBe("  y -/");
  });
});
