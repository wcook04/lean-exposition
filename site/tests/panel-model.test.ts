import { describe, expect, it } from "vitest";
import { tokenizeLean } from "../src/panels/leanTokens";
import { collapsePath, defaultAccount, groupPassages, relationLine, shortRevision, treatmentWords, webUrl } from "../src/panels/model";
import type { AlignedPassage } from "../src/api/types";

const kinds = (src: string) => tokenizeLean(src).filter((t) => t.kind !== "space").map((t) => `${t.kind}:${t.text}`);

describe("Lean tokenizer", () => {
  const statement =
    "theorem full_support (W : BrownianSystem Ω) (γ : OrderParameter) (hmin : IsMinimizer W γ) : FullSupportConclusion W γ";

  it("returns the input unchanged when the tokens are joined", () => {
    for (const src of [statement, "∀ x ∈ s, f x ≤ g x → True", "def f := fun (n : ℕ) => n + 1", "  odd   spacing\n", ""]) {
      expect(tokenizeLean(src).map((t) => t.text).join("")).toBe(src);
    }
  });

  it("separates keywords, binders, brackets and identifiers", () => {
    const k = kinds(statement);
    expect(k[0]).toBe("keyword:theorem");
    expect(k[1]).toBe("ident:full_support");
    expect(k).toContain("binder:W");
    expect(k).toContain("binder:γ");
    expect(k).toContain("binder:hmin");
    expect(k).toContain("ident:BrownianSystem");
    expect(k).toContain("ident:Ω");
    expect(k).toContain("bracket:(");
    expect(k.filter((x) => x === "binder:W")).toHaveLength(1);
    expect(k.at(-1)).toBe("ident:γ");
  });

  it("does not mark an application in brackets as a binder", () => {
    expect(kinds("(f x)")).toEqual(["bracket:(", "ident:f", "ident:x", "bracket:)"]);
  });

  it("reads arrows, quantifiers and their bound names", () => {
    const k = kinds("∀ x y, P x → Q y ↔ R");
    expect(k.slice(0, 3)).toEqual(["keyword:∀", "binder:x", "binder:y"]);
    expect(k).toContain("arrow:→");
    expect(k).toContain("arrow:↔");
    expect(kinds("a := b")).toContain("arrow::=");
    expect(kinds("fun n => n")).toEqual(["keyword:fun", "binder:n", "arrow:=>", "ident:n"]);
  });

  it("keeps dotted names whole and numbers separate", () => {
    expect(kinds("OAI.ZeroTemperatureSK.full_support 2")).toEqual(["ident:OAI.ZeroTemperatureSK.full_support", "number:2"]);
    expect(kinds("x.")).toEqual(["ident:x", "punct:."]);
  });
});

describe("panel wording", () => {
  it("collapses a long path to the first item and the last two", () => {
    expect(collapsePath(["a", "b", "c"])).toEqual(["a", "b", "c"]);
    expect(collapsePath(["a", "b", "c", "d", "e", "f"])).toEqual(["a", null, "e", "f"]);
  });

  it("says how an account relates to a result without a passage", () => {
    expect(relationLine("short", ["recorded_prerequisite"])).toBe("No passage is linked directly to this record.");
    expect(relationLine("short", [])).toBe("No passage in this account is linked to this record, and the recorded argument for the account’s main results does not use it.");
    expect(relationLine("long", undefined)).toBe("No passage in this account is linked to this record, and the recorded argument for the account’s main results does not use it.");
  });

  it("never shows internal field names", () => {
    for (const roles of [[], ["mapped_claim"], ["mapped_assumption"], ["recorded_prerequisite"], ["recorded_prerequisite", "mapped_claim"]]) {
      expect(relationLine("long", roles)).not.toMatch(/_/);
    }
    expect(treatmentWords([], "x", "assumption_ids").join(" ")).not.toMatch(/_/);
  });

  it("chooses the account: the reader's choice, then the lens, then the first with passages", () => {
    expect(defaultAccount({ expository: 0, short: 2, long: 4 }, null)).toBe("short");
    expect(defaultAccount({ expository: 0, short: 2 }, null, "long")).toBe("long");
    expect(defaultAccount({ expository: 3 }, "long", "short")).toBe("long");
    expect(defaultAccount({}, null)).toBe("expository");
  });

  it("uses only the treatments recorded for this record", () => {
    const t = [
      { claim_id: "a", kinds: ["statement", "derivation"] },
      { claim_id: "b", kinds: ["illustration"] },
    ];
    expect(treatmentWords(t, "a")).toEqual(["states it", "derives it"]);
    expect(treatmentWords(t, "c")).toEqual([]);
  });

  it("groups passages by account in account order without duplicates", () => {
    const p = (stage: AlignedPassage["stage"], anchor: string) => ({ stage, anchor }) as AlignedPassage;
    const g = groupPassages([p("long", "x"), p("short", "y"), p("long", "x"), p("long", "z")]);
    expect([...g.keys()]).toEqual(["expository", "short", "long"]);
    expect(g.get("long")!.map((q) => q.anchor)).toEqual(["x", "z"]);
    expect(g.get("expository")).toEqual([]);
  });

  it("shortens revisions and offers only web links", () => {
    expect(shortRevision("450c8947971dbad9be943b8705ea96f822240961")).toBe("450c894");
    expect(shortRevision("sha256:d78d6fca27b4c360f899a9b2c13772abcbb6a15531728601b85e48a875cf0083")).toBe("sha256:d78d6fca27b4");
    expect(shortRevision("arXiv:1606.05335v2")).toBe("arXiv:1606.05335v2");
    expect(webUrl("urn:sha256:abc")).toBeNull();
    expect(webUrl("https://arxiv.org/abs/1606.05335v2")).toBe("https://arxiv.org/abs/1606.05335v2");
  });
});
