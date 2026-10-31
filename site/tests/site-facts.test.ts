import { describe, expect, it } from "vitest";
import { heroHtml, heroLinks } from "../src/home/heroMarkup";
import { siteFacts, withoutComments } from "../src/home/siteFacts";

describe("what the site states about itself", () => {
  const facts = siteFacts();

  it("reads the build and the axioms from the published observation", () => {
    expect(facts.build?.module).toBe("OAI.Probability.SKSupport.Main");
    expect(facts.build?.returncode).toBe(0);
    expect(facts.extraction?.root).toBe("OAI.ZeroTemperatureSK.full_support");
    expect(facts.extraction?.axioms.sort()).toEqual(["Classical.choice", "Quot.sound", "propext"]);
    expect(facts.extraction?.hasSorry).toBe(false);
  });

  it("finds sorry only where a Comparator challenge stands in for a proof", () => {
    expect(facts.scan?.sorry.map((row) => row.file)).toEqual(["ComparatorChallenges/SKFullSupport.lean", "ComparatorChallenges/SKValue.lean"]);
    expect(facts.scan?.axiomDeclarations).toBe(0);
  });

  it("does not count a word in a comment", () => {
    expect(withoutComments("theorem a := by\n  simp -- not sorry\n/- sorry\nsorry -/")).not.toContain("sorry");
  });

  it("leaves a sentence out rather than state a number it cannot read", () => {
    const empty = siteFacts("/no/such/place", "/no/such/place");
    expect(empty).toMatchObject({ ties: null, references: null, lean: null, theorem1: null, build: null, extraction: null, scan: null });
  });
});

describe("the first screen's ways in", () => {
  const html = (theorem1?: { at: string; anchor: string | null }) => heroHtml(heroLinks("/", theorem1), (tex) => tex);

  it("leads with reading a paper", () => {
    const primary = /class="front__primary" href="([^"]+)"/.exec(html())?.[1];
    expect(primary).toBe("/read/short");
    expect(html()).toContain('class="front__secondary" href="/read/expository"');
  });

  it("derives Theorem 1's address from the alignment", () => {
    expect(html({ at: "b1-2", anchor: "main-result" })).toContain('href="/read/short?l=b1-2&n=full_support#main-result"');
    expect(html()).toContain("Theorem 1 with its Lean open");
  });
});
