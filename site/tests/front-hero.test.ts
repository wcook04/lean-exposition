import { readFileSync } from "node:fs";
import { resolve } from "node:path";
import { describe, expect, it } from "vitest";
import { frameHtml, heroHtml, heroLinks, HERO_ROWS } from "../src/home/heroMarkup";

const lean = readFileSync(resolve("../examples/qaoa-sk/upstream/lean/ComparatorChallenges/SKFullSupport.lean"), "utf8");
const theorem = JSON.parse(readFileSync(resolve("../examples/qaoa-sk/alignment/main-theorem.json"), "utf8")) as {
  pairs: { lean: string; tex: string }[];
};

describe("the first screen", () => {
  it("quotes OpenAI's Lean statement exactly", () => {
    for (const row of HERO_ROWS) expect(lean).toContain(row.lean);
  });

  it("pairs each clause as the authored correspondence does", () => {
    const authored = theorem.pairs.map((pair) => pair.lean).join("\n");
    for (const row of HERO_ROWS.slice(1)) {
      const clause = row.lean.startsWith("∀ a b") ? "γ.val a < γ.val b" : row.lean;
      expect(authored).toContain(clause);
    }
  });

  it("links with the site's base path, and gives every clause a row", () => {
    const html = heroHtml(heroLinks("/lean-exposition-site/"), (tex) => `<i>${tex}</i>`);
    expect(html).toContain('href="/lean-exposition-site/read/expository"');
    expect(html.match(/class="rosetta__row"/g)).toHaveLength(HERO_ROWS.length);
  });

  it("draws the same five jobs as the top bar", () => {
    const html = frameHtml("/");
    for (const job of ["Map", "Compare", "Read", "Lean", "Checks"]) expect(html).toContain(`>${job}</a>`);
  });
});
