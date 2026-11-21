// The topic colours are computed and stored (scripts/topic-colours.ts). These checks read the stored
// colours as the pages publish them: every list keeps its two floors in both themes and under
// deuteranopia and protanopia simulation, every colour keeps 3:1 against its page as an underline
// draws it and lies in sRGB, and recomputing from the data gives the stored files byte for byte, so a
// change to topics, families or phrases shows up as a reviewed diff.
import { readFileSync } from "node:fs";
import { beforeAll, describe, expect, it } from "vitest";
import {
  FAMILY_FLOOR, MAX_FAMILIES, MAX_SHADES, MIN_CONTRAST, SHADE_FLOOR, THEMES, checkFloors, deriveFamilies, inGamut, oklabToLinear,
  palette, parseOklch, relatedness, seriate,
} from "../src/reader/palette";
import { topicColourCss } from "../src/reader/topicColours";
import { FIXTURE, compute, report, type Computed } from "../scripts/topic-colours";

let computed: Computed;
let again: Computed;
beforeAll(() => {
  computed = compute();
  again = compute();
}, 120_000);

interface StoredPart {
  key: string;
  families: { id: string; name: string; named: boolean; hue: number; topics: string[] }[];
  topics: Record<string, { index: number; family: string; light: string; dark: string }>;
}

describe("topic colours", () => {
  it("are deterministic and stored as computed, with the orders in the fixture", () => {
    expect(again.fixture).toBe(computed.fixture);
    expect([...again.files]).toEqual([...computed.files]);
    expect(computed.files.size).toBeGreaterThan(0);
    for (const [path, content] of computed.files) expect(readFileSync(path, "utf8"), `${path} is stale: run node site/scripts/topic-colours.ts`).toBe(content);
    expect(readFileSync(FIXTURE, "utf8")).toBe(computed.fixture);
  });

  it("give every page of a shared topic list the same colours", () => {
    const byKey = new Map<string, string>();
    for (const content of computed.files.values())
      for (const part of JSON.parse(content).parts as StoredPart[]) {
        const text = JSON.stringify([part.families, part.topics]);
        expect(byKey.get(part.key) ?? text).toBe(text);
        byKey.set(part.key, text);
      }
  });

  it("keep both floors, 3:1 contrast and the sRGB gamut in both themes and every vision", () => {
    const lines: string[] = [`floors: families ΔE2000 ≥ ${FAMILY_FLOOR.normal} (dichromats ≥ ${FAMILY_FLOOR.dichromat}), shades ΔE2000 ≥ ${SHADE_FLOOR}, contrast ≥ ${MIN_CONTRAST}:1`];
    for (const [path, content] of computed.files) {
      for (const [n, part] of (JSON.parse(content).parts as StoredPart[]).entries()) {
        expect(part.families.length, path).toBeLessThanOrEqual(MAX_FAMILIES);
        const groups = part.families.map((family) => {
          expect(family.topics.length, `${path} ${family.id}`).toBeLessThanOrEqual(MAX_SHADES);
          return family.topics.map((id) => [part.topics[id].light, part.topics[id].dark]);
        });
        for (const colour of groups.flat(2)) for (const v of oklabToLinear(parseOklch(colour))) expect(v > -1e-3 && v < 1 + 1e-3, colour).toBe(true);
        expect(groups.flat(2).every((c) => inGamut(oklabToLinear(parseOklch(c)), 1e-3))).toBe(true);
        let familyLeast = Infinity;
        let shadeLeast = Infinity;
        for (const row of checkFloors(groups)) {
          const where = `${path}#${n} ${row.theme} ${row.vision}`;
          expect(row.contrast, where).toBeGreaterThanOrEqual(MIN_CONTRAST);
          expect(row.family, where).toBeGreaterThanOrEqual(row.vision === "normal" ? FAMILY_FLOOR.normal : FAMILY_FLOOR.dichromat);
          expect(row.shade, where).toBeGreaterThanOrEqual(SHADE_FLOOR);
          if (row.vision === "normal") familyLeast = Math.min(familyLeast, row.family);
          shadeLeast = Math.min(shadeLeast, row.shade);
        }
        lines.push(`${path.replace(/.*\/(examples|instances)\//, "$1/")}#${n}: ${Object.keys(part.topics).length} topics, ${part.families.length} families; least ΔE2000 between families ${familyLeast.toFixed(1)}, between shades ${Number.isFinite(shadeLeast) ? shadeLeast.toFixed(1) : "—"}`);
      }
    }
    console.log(lines.join("\n") + "\n" + report(computed));
  });

  it("order families round the circle with the most related side by side", () => {
    const rel = [
      [0, 9, 0, 1, 0],
      [9, 0, 8, 0, 0],
      [0, 8, 0, 7, 0],
      [1, 0, 7, 0, 6],
      [0, 0, 0, 6, 0],
    ];
    const order = seriate(rel);
    const score = (o: number[]) => o.reduce((s, f, i) => s + rel[f][o[(i + 1) % o.length]], 0);
    const all = (left: number[]): number[][] => (left.length ? left.flatMap((f) => all(left.filter((g) => g !== f)).map((rest) => [f, ...rest])) : [[]]);
    expect(score(order)).toBe(Math.max(...all([0, 1, 2, 3, 4]).map(score)));
    expect(score(order)).toBe(30);
    expect(order[0]).toBe(0);
    expect(seriate(rel)).toEqual(order);
  });

  it("derive families of at most three from relatedness when none are named", () => {
    const topics = ["a", "b", "c", "d", "e", "f"];
    const phrases = [
      ...["a", "b"].flatMap((t) => [{ topic: t, section: "1", lean: ["x"] }, { topic: t, section: "1", lean: [] }]),
      ...["c", "d"].flatMap((t) => [{ topic: t, section: "2", lean: ["y"] }]),
      ...["e", "f"].flatMap((t) => [{ topic: t, section: "3", lean: ["z"] }]),
    ];
    const rel = relatedness(topics, phrases);
    expect(rel[0][1]).toBe(5);
    expect(deriveFamilies(rel)).toEqual([[0, 1], [2, 3], [4, 5]]);
    const p = palette({ topics: topics.map((id) => ({ id })), related: rel });
    expect(p.families.map((f) => f.topics.length)).toEqual([2, 2, 2]);
    expect(p.families.every((f) => !f.named)).toBe(true);
  });

  it("set one colour per topic for each theme as CSS", () => {
    const css = topicColourCss([
      { id: "a", name: "A", description: "", part: 0, tone: 0, light: "oklch(0.450 0.080 30.0)", dark: "oklch(0.700 0.100 30.0)" },
      { id: "b", name: "B", description: "", part: 0, tone: 1 },
    ]);
    expect(css).toContain(":root { --tone-0: oklch(0.450 0.080 30.0); }");
    expect(css).toContain(':root[data-theme="dark"] { --tone-0: oklch(0.700 0.100 30.0); }');
    expect(css).toContain('[data-tone="0"] { --tone: var(--tone-0); }');
    expect(css).not.toContain("tone-1");
    expect(topicColourCss([])).toBe("");
    expect(THEMES).toEqual(["light", "dark"]);
  });
});
