// The topic colours tell topics apart. For every paper and part of every example with phrase
// ties, any two of its topics differ by CIEDE2000 ΔE ≥ 15 as drawn: each shade as an underline
// (80% over the page ground, mixed in Oklab as CSS color-mix does), shade against shade, in the
// light and the dark theme. Each shade also stands off the ground and lies in the sRGB gamut.
import { readdirSync, readFileSync } from "node:fs";
import { resolve } from "node:path";
import { describe, expect, it } from "vitest";

const CSS = readFileSync(resolve(__dirname, "../src/reader/phrases.css"), "utf8");
const TOKENS = readFileSync(resolve(__dirname, "../src/styles/tokens.css"), "utf8");
const EXAMPLES = resolve(__dirname, "../../examples");
const MIN_DE = 15;
const MIN_GROUND_DE = 25;

type Vec = [number, number, number];

function block(source: string, selector: string): string {
  const at = source.indexOf(selector);
  if (at < 0) throw new Error(`no ${selector}`);
  return source.slice(at, source.indexOf("}", at));
}

function tones(selector: string): Vec[] {
  const body = block(CSS, selector);
  const out: Vec[] = [];
  for (const m of body.matchAll(/--tone-(\d+): oklch\(([\d.]+) ([\d.]+) ([\d.]+)\)/g)) {
    const [l, c, h] = [Number(m[2]), Number(m[3]), Number(m[4])];
    out[Number(m[1])] = [l, c * Math.cos((h * Math.PI) / 180), c * Math.sin((h * Math.PI) / 180)];
  }
  return out;
}

const hexLinear = (hex: string): Vec =>
  [1, 3, 5].map((i) => {
    const c = parseInt(hex.slice(i, i + 2), 16) / 255;
    return c <= 0.04045 ? c / 12.92 : ((c + 0.055) / 1.055) ** 2.4;
  }) as Vec;

function oklabToLinear([L, a, b]: Vec): Vec {
  const l = (L + 0.3963377774 * a + 0.2158037573 * b) ** 3;
  const m = (L - 0.1055613458 * a - 0.0638541728 * b) ** 3;
  const s = (L - 0.0894841775 * a - 1.291485548 * b) ** 3;
  return [4.0767416621 * l - 3.3077115913 * m + 0.2309699292 * s, -1.2684380046 * l + 2.6097574011 * m - 0.3413193965 * s, -0.0041960863 * l - 0.7034186147 * m + 1.707614701 * s];
}

function linearToOklab([r, g, b]: Vec): Vec {
  const [l, m, s] = [0.4122214708 * r + 0.5363325363 * g + 0.0514459929 * b, 0.2119034982 * r + 0.6806995451 * g + 0.1073969566 * b, 0.0883024619 * r + 0.2817188376 * g + 0.6299787005 * b].map(Math.cbrt);
  return [0.2104542553 * l + 0.793617785 * m - 0.0040720468 * s, 1.9779984951 * l - 2.428592205 * m + 0.4505937099 * s, 0.0259040371 * l + 0.7827717662 * m - 0.808675766 * s];
}

function linearToLab([r, g, b]: Vec): Vec {
  const X = (0.4124564 * r + 0.3575761 * g + 0.1804375 * b) / 0.95047;
  const Y = 0.2126729 * r + 0.7151522 * g + 0.072175 * b;
  const Z = (0.0193339 * r + 0.119192 * g + 0.9503041 * b) / 1.08883;
  const f = (t: number) => (t > 216 / 24389 ? Math.cbrt(t) : ((24389 / 27) * t + 16) / 116);
  return [116 * f(Y) - 16, 500 * (f(X) - f(Y)), 200 * (f(Y) - f(Z))];
}

/** CIEDE2000 (Sharma, Wu and Dalal 2005). */
export function deltaE2000([L1, a1, b1]: Vec, [L2, a2, b2]: Vec): number {
  const rad = Math.PI / 180;
  const Cb = (Math.hypot(a1, b1) + Math.hypot(a2, b2)) / 2;
  const G = 0.5 * (1 - Math.sqrt(Cb ** 7 / (Cb ** 7 + 25 ** 7)));
  const [a1p, a2p] = [(1 + G) * a1, (1 + G) * a2];
  const [C1p, C2p] = [Math.hypot(a1p, b1), Math.hypot(a2p, b2)];
  const hue = (b: number, a: number) => ((Math.atan2(b, a) / rad) % 360 + 360) % 360;
  const [h1p, h2p] = [hue(b1, a1p), hue(b2, a2p)];
  let dh = h2p - h1p;
  if (C1p * C2p === 0) dh = 0;
  else if (dh > 180) dh -= 360;
  else if (dh < -180) dh += 360;
  const dLp = L2 - L1;
  const dCp = C2p - C1p;
  const dHp = 2 * Math.sqrt(C1p * C2p) * Math.sin((dh / 2) * rad);
  const Lbp = (L1 + L2) / 2;
  const Cbp = (C1p + C2p) / 2;
  let hbp = h1p + h2p;
  if (C1p * C2p !== 0) hbp = Math.abs(h1p - h2p) <= 180 ? (h1p + h2p) / 2 : h1p + h2p < 360 ? (h1p + h2p + 360) / 2 : (h1p + h2p - 360) / 2;
  const T = 1 - 0.17 * Math.cos((hbp - 30) * rad) + 0.24 * Math.cos(2 * hbp * rad) + 0.32 * Math.cos((3 * hbp + 6) * rad) - 0.2 * Math.cos((4 * hbp - 63) * rad);
  const dTheta = 30 * Math.exp(-(((hbp - 275) / 25) ** 2));
  const Rc = 2 * Math.sqrt(Cbp ** 7 / (Cbp ** 7 + 25 ** 7));
  const Sl = 1 + (0.015 * (Lbp - 50) ** 2) / Math.sqrt(20 + (Lbp - 50) ** 2);
  const Sc = 1 + 0.045 * Cbp;
  const Sh = 1 + 0.015 * Cbp * T;
  const Rt = -Math.sin(2 * dTheta * rad) * Rc;
  return Math.sqrt((dLp / Sl) ** 2 + (dCp / Sc) ** 2 + (dHp / Sh) ** 2 + Rt * (dCp / Sc) * (dHp / Sh));
}

const groundOf = (selector: string) => /--ground: (#[0-9a-f]{6})/.exec(block(TOKENS, selector))![1];
const THEMES = [
  { theme: "light", tones: tones(":root {"), ground: groundOf(":root {") },
  { theme: "dark", tones: tones(':root[data-theme="dark"] {'), ground: groundOf(':root[data-theme="dark"] {') },
] as const;

/** A shade as an underline draws it: 80% of the tone over the ground, in CIELAB. */
function drawn(tone: Vec, ground: string): Vec {
  const g = linearToOklab(hexLinear(ground));
  const mixed = tone.map((v, i) => 0.8 * v + 0.2 * g[i]) as Vec;
  return linearToLab(oklabToLinear(mixed).map((v) => Math.min(1, Math.max(0, v))) as Vec);
}

/** Topic count of every paper and part, from the phrase files. */
function papers(): { name: string; topics: number }[] {
  const out: { name: string; topics: number }[] = [];
  for (const example of readdirSync(EXAMPLES)) {
    let files: string[] = [];
    try {
      files = readdirSync(resolve(EXAMPLES, example, "alignment")).filter((n) => /^phrases-.*\.json$/.test(n));
    } catch {
      continue;
    }
    for (const file of files) {
      const data = JSON.parse(readFileSync(resolve(EXAMPLES, example, "alignment", file), "utf8"));
      for (const part of data.parts) out.push({ name: `${example} ${data.paper}${part.name ? ` ${part.name}` : ""}`, topics: part.topics.length });
    }
  }
  return out;
}

describe("topic colours", () => {
  it("define two shades for nine topics in each theme, in gamut and apart from the ground", () => {
    for (const { theme, tones: all, ground } of THEMES) {
      expect(all.length, theme).toBe(18);
      const g = linearToLab(hexLinear(ground));
      for (const tone of all) {
        for (const v of oklabToLinear(tone)) expect(v, theme).toBeGreaterThanOrEqual(-0.002);
        for (const v of oklabToLinear(tone)) expect(v, theme).toBeLessThanOrEqual(1.002);
        expect(deltaE2000(drawn(tone, ground), g), theme).toBeGreaterThanOrEqual(MIN_GROUND_DE);
      }
    }
  });

  it("tell every pair of topics apart by ΔE2000 ≥ 15 in every paper and part, in both themes", () => {
    const rows = papers();
    expect(rows.length).toBeGreaterThan(0);
    const report: string[] = [];
    for (const { name, topics } of rows) {
      expect(topics, name).toBeLessThanOrEqual(9);
      for (const { theme, tones: all, ground } of THEMES) {
        let least = Infinity;
        for (let i = 0; i < topics; i++)
          for (let j = i + 1; j < topics; j++)
            for (const a of [2 * i, 2 * i + 1])
              for (const b of [2 * j, 2 * j + 1]) least = Math.min(least, deltaE2000(drawn(all[a], ground), drawn(all[b], ground)));
        report.push(`${name} (${topics} topics), ${theme}: min ΔE2000 ${least.toFixed(1)}`);
        expect(least, `${name}, ${theme}`).toBeGreaterThanOrEqual(MIN_DE);
      }
    }
    console.log(report.join("\n"));
  });
});
