// The resting phrase underline is one pixel, from the design token; pointing at a phrase, focusing
// it and selecting it all draw a heavier line. The browser check (scripts/check_library_paper.py,
// "underline") measures the same rules as drawn, in both schemes.
import { readFileSync } from "node:fs";
import { fileURLToPath } from "node:url";
import { describe, expect, it } from "vitest";

const read = (path: string) => readFileSync(fileURLToPath(new URL(path, import.meta.url)), "utf8");
const phrases = read("../src/reader/phrases.css").replace(/\/\*[\s\S]*?\*\//g, "");
const tokens = read("../src/styles/tokens.css").replace(/\/\*[\s\S]*?\*\//g, "");

/** The declarations of the rule whose selector list is exactly `selector`. */
function rule(selector: string): string {
  for (const match of phrases.matchAll(/([^{}]+)\{([^{}]*)\}/g)) {
    const selectors = match[1].split(",").map((s) => s.trim());
    if (selectors.includes(selector)) return match[2];
  }
  throw new Error(`no rule for ${selector}`);
}
// The design branch names the existing three-pixel phrase-end gap.
const lineOf = (body: string) => body.replace("var(--tie-end-gap)", "3px").match(/background-size:\s*calc\(100% - 3px\)\s*([^;]+);/)?.[1].trim();

describe("phrase underline", () => {
  it("defines the resting line's token as one pixel", () => {
    expect(tokens).toMatch(/--tie-rule:\s*1px;/);
    expect(tokens).toMatch(/--tie-end-gap:\s*3px;/);
  });

  it("sets the line of a phrase in running text 3px below its words, and leaves a display's padding alone", () => {
    expect(rule(".paper .tie:not(.math-display)")).toMatch(/padding-bottom:\s*3px;/);
    expect(rule(".paper .tie")).toMatch(/padding-bottom:\s*1px;/);
  });

  it("uses the same faint ink and tint for text and PDF phrase links", () => {
    const pdf = read("../src/reader/pdf/pdf-view.css");
    expect(tokens).toMatch(/--tie-rest-line-opacity:\s*8%;/);
    expect(tokens).toMatch(/--tie-rest-fill-opacity:\s*10%;/);
    for (const css of [rule(".paper .tie"), pdf]) {
      expect(css).toContain("var(--tie-rest-line-opacity)");
      expect(css).toContain("var(--tie-rest-fill-opacity)");
    }
  });

  it("draws a phrase at rest with the token", () => {
    expect(lineOf(rule(".paper .tie"))).toBe("var(--tie-rule)");
  });

  it("keeps hover, keyboard focus and a pointed-at phrase at 2px over a faint tint", () => {
    for (const selector of [".paper .tie:hover", ".paper .tie:focus-visible", ".paper .tie[data-point]"]) {
      const body = rule(selector);
      expect(lineOf(body), selector).toBe("2px");
      expect(body, selector).toMatch(/background-color:\s*color-mix\(in oklab, var\(--tie-color\) 21%, transparent\)/);
    }
  });

  it("keeps the 1px resting line under the prose of a selected whole statement", () => {
    expect(lineOf(rule(".paper .tie[data-pin][data-pin-block]"))).toBe("var(--tie-rule)");
  });

  it("keeps a selected phrase at 2px in amber", () => {
    const body = rule(".paper .tie[data-pin]");
    expect(lineOf(body)).toBe("2px");
    expect(body).toMatch(/var\(--lit-line\)/);
  });
});
