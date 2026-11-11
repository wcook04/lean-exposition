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
    expect(html).toContain('href="/lean-exposition-site/read/short"');
    expect(html).toContain('href="/lean-exposition-site/read/expository"');
    expect(html.match(/class="rosetta__row"/g)).toHaveLength(HERO_ROWS.length);
  });

  it("puts the short video of this website first and the long video of the result after it, as the catalogue lists them", () => {
    const links = heroLinks("/lean-exposition-site/");
    expect(links.films.map((film) => [film.id, film.href, film.clock])).toEqual([
      ["short-sk-website", "https://www.youtube.com/watch?v=8ge7rwRMkhI", "1:32"],
      ["sk-no-gap", "https://www.youtube.com/watch?v=IUAhxUriDVw", "12:28"],
      ["short-sk-no-gap", "https://www.youtube.com/watch?v=x901wkmxCMQ", "1:38"],
    ]);
    const html = heroHtml(links, (tex) => tex);
    const lead = html.indexOf("front__lead");
    expect(lead).toBeGreaterThan(-1);
    expect(html.indexOf("8ge7rwRMkhI")).toBeGreaterThan(lead);
    expect(html.indexOf("8ge7rwRMkhI")).toBeLessThan(html.indexOf("IUAhxUriDVw"));
    expect(html).toContain('src="/lean-exposition-site/films/short-sk-website-640.webp"');
    // The picture and the title open the same video; only the title is in the Tab order.
    expect(html.match(/class="film-slot__frame"[^>]*tabindex="-1"/g)).toHaveLength(3);
    expect(html).toContain(", video on YouTube, 1 minute 32 seconds</span>");
  });

  it("draws five pictures of the site in use, the first chosen, each opening the view it is of", () => {
    const html = heroHtml(heroLinks("/lean-exposition-site/", { at: "b1-2", anchor: "main-result" }), (tex) => tex);
    const values = [...html.matchAll(/name="front-shot" value="([a-z]+)"( checked)?/g)].map((m) => [m[1], Boolean(m[2])]);
    expect(values).toEqual([["follow", true], ["tick", false], ["card", false], ["compare", false], ["checks", false]]);
    for (const [id] of values) {
      expect(html).toContain(`src="/lean-exposition-site/stills/tour-${id}-light-1440.webp"`);
      expect(html).toContain(`src="/lean-exposition-site/stills/tour-${id}-dark-1440.webp"`);
    }
    expect(html).toContain('class="shots__pic shots__pic--tick" href="/lean-exposition-site/read/short?l=b1-2&n=full_support#main-result"');
    expect(html).toContain('class="shots__pic shots__pic--checks" href="/lean-exposition-site/checks"');
    // The pictures come before the videos, and the table of clauses after the first screen.
    expect(html.indexOf("shots__frame")).toBeLessThan(html.indexOf("front__watch"));
    expect(html.indexOf("front__watch")).toBeLessThan(html.indexOf("rosetta__table"));
  });

  it("draws the same five jobs as the top bar", () => {
    const html = frameHtml("/");
    for (const job of ["Read", "Map", "Compare", "What ran", "Lean index"]) expect(html).toContain(`>${job}</a>`);
  });
});
