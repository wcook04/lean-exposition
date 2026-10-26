import { describe, expect, it } from "vitest";
import { formatLeanSignature, tokenizeLean } from "../src/panels/leanTokens";

describe("laying out a Lean signature", () => {
  const full = "theorem full_support (W : BrownianSystem Ω) (γ : OrderParameter) (hmin : IsMinimizer W γ) : FullSupportConclusion W γ";

  it("puts each binder and the type on its own indented line", () => {
    expect(formatLeanSignature(full)).toBe(
      [
        "theorem full_support",
        "  (W : BrownianSystem Ω)",
        "  (γ : OrderParameter)",
        "  (hmin : IsMinimizer W γ) :",
        "  FullSupportConclusion W γ",
      ].join("\n"),
    );
  });

  it("changes only whitespace", () => {
    const squash = (s: string) => s.replace(/\s+/g, "");
    expect(squash(formatLeanSignature(full))).toBe(squash(full));
    expect(tokenizeLean(formatLeanSignature(full)).map((t) => t.text).join("")).toBe(formatLeanSignature(full));
  });

  it("keeps nested brackets and implicit binders together", () => {
    const s = "lemma foo {α : Type} [Group α] (f : α → (α × α)) : f = f";
    expect(formatLeanSignature(s)).toBe(["lemma foo", "  {α : Type}", "  [Group α]", "  (f : α → (α × α)) :", "  f = f"].join("\n"));
  });

  it("leaves prose and multi-line text alone", () => {
    const prose = "OAI.SKValue.value_consequences is the three-part universally quantified conjunction";
    expect(formatLeanSignature(prose)).toBe(prose);
    expect(formatLeanSignature("theorem a :\n  b")).toBe("theorem a :\n  b");
  });
});
