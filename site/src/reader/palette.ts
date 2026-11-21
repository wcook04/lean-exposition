// Topic colours, computed. A paper's topics fall into at most eight families; each family takes
// one hue and each topic in it one shade of that hue, so related topics look related and every
// family stands apart from every other.
//
// 1. Families sit on the hue circle in the order that puts the most related families side by side
//    (circular seriation, by brute force: at most 7! orders).
// 2. Their hues are evenly spaced, then nudged (each by at most an eighth of the spacing) to raise
//    the least CIEDE2000 distance between any two colours of different families.
// 3. Each theme has one OKLCH lightness and one chroma for every family: a lightness that keeps
//    every shade at 3:1 against the page as an underline draws it, and the largest chroma at which
//    every shade of every family lies in sRGB, searched together with the hues.
// 4. A family's shades step evenly in lightness (one step either side of the family's lightness),
//    with a smaller step in chroma and a hue offset that stays inside the family's arc.
//
// 5. Each family may move its own lightness by at most MAX_LIFT off its theme's, and the search
//    weighs distances under deuteranopia and protanopia simulation (Machado, Oliveira and Fernandes
//    2009, severity 1) as well as normal vision: at one shared lightness two families whose hues
//    mirror across the blue–yellow axis look the same to a dichromat.
//
// Two floors are checked for every list, in both themes and in every vision: FAMILY_FLOOR between
// any two colours of different families, SHADE_FLOOR between any two shades of one family.
// Everything here is deterministic: the same topics, families and counts give the same colours.

export type Vec = [number, number, number];

const RAD = Math.PI / 180;

export const MAX_FAMILIES = 8;
export const MAX_SHADES = 3;
/** The opacity at which an underline draws the topic colour over the page (phrases.css: 80%). */
export const UNDERLINE = 0.8;
/** WCAG contrast of every drawn colour against its page. */
export const MIN_CONTRAST = 3;
/**
 * CIEDE2000 between any two colours of different families, in both themes: with normal vision, and
 * under full deuteranopia or protanopia simulation. A dichromat sees only lightness and one hue
 * axis, and the 3:1 band leaves little lightness, so the dichromat floor is the one that holds for
 * the largest lists in use (14 and 16 topics in 7 families), not a large one.
 */
export const FAMILY_FLOOR = { normal: 10, dichromat: 2.5 };
/** CIEDE2000 between any two shades of one family, in both themes and every vision. */
export const SHADE_FLOOR = 6;

/** The two pages a colour is drawn on (styles/tokens.css `--ground`). */
export const GROUNDS = { light: "#f8f0e2", dark: "#1c1526" } as const;
export type ThemeName = keyof typeof GROUNDS;
export const THEMES: ThemeName[] = ["light", "dark"];

/** A shade's step either side of its family, in OKLCH lightness, as a share of chroma, and in hue (share of the spacing). */
export const SHADE_STEP = { lightness: 0.085, chroma: 0.12, hue: 0.12 };

// ---- Colour arithmetic ------------------------------------------------------------------------

export const oklch = (L: number, C: number, h: number): Vec => [L, C * Math.cos(h * RAD), C * Math.sin(h * RAD)];

export function oklabToLinear([L, a, b]: Vec): Vec {
  const l = (L + 0.3963377774 * a + 0.2158037573 * b) ** 3;
  const m = (L - 0.1055613458 * a - 0.0638541728 * b) ** 3;
  const s = (L - 0.0894841775 * a - 1.291485548 * b) ** 3;
  return [4.0767416621 * l - 3.3077115913 * m + 0.2309699292 * s, -1.2684380046 * l + 2.6097574011 * m - 0.3413193965 * s, -0.0041960863 * l - 0.7034186147 * m + 1.707614701 * s];
}

export function linearToOklab([r, g, b]: Vec): Vec {
  const [l, m, s] = [0.4122214708 * r + 0.5363325363 * g + 0.0514459929 * b, 0.2119034982 * r + 0.6806995451 * g + 0.1073969566 * b, 0.0883024619 * r + 0.2817188376 * g + 0.6299787005 * b].map(Math.cbrt);
  return [0.2104542553 * l + 0.793617785 * m - 0.0040720468 * s, 1.9779984951 * l - 2.428592205 * m + 0.4505937099 * s, 0.0259040371 * l + 0.7827717662 * m - 0.808675766 * s];
}

export function linearToLab([r, g, b]: Vec): Vec {
  const X = (0.4124564 * r + 0.3575761 * g + 0.1804375 * b) / 0.95047;
  const Y = 0.2126729 * r + 0.7151522 * g + 0.072175 * b;
  const Z = (0.0193339 * r + 0.119192 * g + 0.9503041 * b) / 1.08883;
  const f = (t: number) => (t > 216 / 24389 ? Math.cbrt(t) : ((24389 / 27) * t + 16) / 116);
  return [116 * f(Y) - 16, 500 * (f(X) - f(Y)), 200 * (f(Y) - f(Z))];
}

export const hexToLinear = (hex: string): Vec =>
  [1, 3, 5].map((i) => {
    const c = parseInt(hex.slice(i, i + 2), 16) / 255;
    return c <= 0.04045 ? c / 12.92 : ((c + 0.055) / 1.055) ** 2.4;
  }) as Vec;

const clip = (v: Vec): Vec => v.map((x) => Math.min(1, Math.max(0, x))) as Vec;
export const inGamut = (lin: Vec, eps = 1e-4) => lin.every((x) => x >= -eps && x <= 1 + eps);
export const luminance = ([r, g, b]: Vec) => 0.2126729 * r + 0.7151522 * g + 0.072175 * b;
export const contrast = (y1: number, y2: number) => (Math.max(y1, y2) + 0.05) / (Math.min(y1, y2) + 0.05);

/** CIEDE2000 (Sharma, Wu and Dalal 2005). */
export function deltaE2000([L1, a1, b1]: Vec, [L2, a2, b2]: Vec): number {
  const Cb = (Math.hypot(a1, b1) + Math.hypot(a2, b2)) / 2;
  const G = 0.5 * (1 - Math.sqrt(Cb ** 7 / (Cb ** 7 + 25 ** 7)));
  const [a1p, a2p] = [(1 + G) * a1, (1 + G) * a2];
  const [C1p, C2p] = [Math.hypot(a1p, b1), Math.hypot(a2p, b2)];
  const hue = (b: number, a: number) => ((Math.atan2(b, a) / RAD) % 360 + 360) % 360;
  const [h1p, h2p] = [hue(b1, a1p), hue(b2, a2p)];
  let dh = h2p - h1p;
  if (C1p * C2p === 0) dh = 0;
  else if (dh > 180) dh -= 360;
  else if (dh < -180) dh += 360;
  const dLp = L2 - L1;
  const dCp = C2p - C1p;
  const dHp = 2 * Math.sqrt(C1p * C2p) * Math.sin((dh / 2) * RAD);
  const Lbp = (L1 + L2) / 2;
  const Cbp = (C1p + C2p) / 2;
  let hbp = h1p + h2p;
  if (C1p * C2p !== 0) hbp = Math.abs(h1p - h2p) <= 180 ? (h1p + h2p) / 2 : h1p + h2p < 360 ? (h1p + h2p + 360) / 2 : (h1p + h2p - 360) / 2;
  const T = 1 - 0.17 * Math.cos((hbp - 30) * RAD) + 0.24 * Math.cos(2 * hbp * RAD) + 0.32 * Math.cos((3 * hbp + 6) * RAD) - 0.2 * Math.cos((4 * hbp - 63) * RAD);
  const dTheta = 30 * Math.exp(-(((hbp - 275) / 25) ** 2));
  const Rc = 2 * Math.sqrt(Cbp ** 7 / (Cbp ** 7 + 25 ** 7));
  const Sl = 1 + (0.015 * (Lbp - 50) ** 2) / Math.sqrt(20 + (Lbp - 50) ** 2);
  const Sc = 1 + 0.045 * Cbp;
  const Sh = 1 + 0.015 * Cbp * T;
  const Rt = -Math.sin(2 * dTheta * RAD) * Rc;
  return Math.sqrt((dLp / Sl) ** 2 + (dCp / Sc) ** 2 + (dHp / Sh) ** 2 + Rt * (dCp / Sc) * (dHp / Sh));
}

/** Dichromat simulations on linear sRGB (Machado, Oliveira and Fernandes 2009, severity 1.0). */
export const VISIONS = {
  normal: null,
  deuteranopia: [[0.367322, 0.860646, -0.227968], [0.280085, 0.672501, 0.047413], [-0.01182, 0.04294, 0.968881]],
  protanopia: [[0.152286, 1.052583, -0.204868], [0.114503, 0.786281, 0.099216], [-0.003882, -0.048116, 1.051998]],
} as const;
export type Vision = keyof typeof VISIONS;
export const VISION_NAMES = Object.keys(VISIONS) as Vision[];

const simulate = (lin: Vec, vision: Vision): Vec => {
  const m = VISIONS[vision];
  if (!m) return lin;
  return clip(m.map((row) => row[0] * lin[0] + row[1] * lin[1] + row[2] * lin[2]) as Vec);
};

const encode = (c: number) => {
  const v = Math.min(1, Math.max(0, c));
  return v <= 0.0031308 ? 12.92 * v : 1.055 * v ** (1 / 2.4) - 0.055;
};
const decode = (c: number) => (c <= 0.04045 ? c / 12.92 : ((c + 0.055) / 1.055) ** 2.4);
const GROUND_LINEAR = { light: hexToLinear(GROUNDS.light), dark: hexToLinear(GROUNDS.dark) };

/**
 * A colour as an underline draws it. `color-mix(in oklab, tone 80%, transparent)` is the tone at
 * 80% opacity, and the browser composites that over the page in gamma-encoded sRGB.
 */
export function drawnLinear(tone: Vec, theme: ThemeName): Vec {
  const t = clip(oklabToLinear(tone));
  const g = GROUND_LINEAR[theme];
  return t.map((v, i) => decode(UNDERLINE * encode(v) + (1 - UNDERLINE) * encode(g[i]))) as Vec;
}

/** The drawn colour in CIELAB as one vision sees it. */
export const seen = (tone: Vec, theme: ThemeName, vision: Vision): Vec => linearToLab(simulate(drawnLinear(tone, theme), vision));

export const groundContrast = (tone: Vec, theme: ThemeName) => contrast(luminance(drawnLinear(tone, theme)), luminance(hexToLinear(GROUNDS[theme])));

// ---- Relatedness, families and their order ---------------------------------------------------

export interface TopicIn {
  id: string;
  name?: string;
  family?: string;
}
export interface FamilyIn {
  id: string;
  name: string;
  description?: string;
}
/** One phrase, as relatedness counts it: its topic, its section and the Lean declarations it names. */
export interface PhraseIn {
  topic: string;
  section: string;
  lean: string[];
}

/**
 * How related two topics are: the number of pairs of their phrases that share a section, plus the
 * number of pairs that name the same Lean declaration. Symmetric, zero on the diagonal.
 */
export function relatedness(topics: string[], phrases: PhraseIn[]): number[][] {
  const at = new Map(topics.map((id, i) => [id, i]));
  const n = topics.length;
  const out = Array.from({ length: n }, () => new Array<number>(n).fill(0));
  const add = (groups: Map<string, number[]>) => {
    for (const counts of groups.values())
      for (let i = 0; i < n; i++)
        for (let j = i + 1; j < n; j++) {
          const v = counts[i] * counts[j];
          out[i][j] += v;
          out[j][i] += v;
        }
  };
  const bySection = new Map<string, number[]>();
  const byDecl = new Map<string, number[]>();
  for (const p of phrases) {
    const i = at.get(p.topic);
    if (i === undefined) continue;
    const s = bySection.get(p.section) ?? new Array<number>(n).fill(0);
    s[i]++;
    bySection.set(p.section, s);
    for (const name of new Set(p.lean)) {
      const d = byDecl.get(name) ?? new Array<number>(n).fill(0);
      d[i]++;
      byDecl.set(name, d);
    }
  }
  add(bySection);
  add(byDecl);
  return out;
}

/** Relatedness scaled to [0, 1] by each pair's totals (cosine-like), so busy topics do not dominate. */
function similarity(rel: number[][]): number[][] {
  const tot = rel.map((row) => row.reduce((a, b) => a + b, 0));
  return rel.map((row, i) => row.map((v, j) => (i === j ? 1 : tot[i] && tot[j] ? v / Math.sqrt(tot[i] * tot[j]) : 0)));
}

/** Mean silhouette of a partition under distance 1 − similarity; a singleton scores 0. */
function silhouette(groups: number[][], dist: number[][]): number {
  let sum = 0;
  let count = 0;
  for (const g of groups)
    for (const i of g) {
      count++;
      if (g.length === 1) continue;
      const a = g.filter((j) => j !== i).reduce((s, j) => s + dist[i][j], 0) / (g.length - 1);
      let b = Infinity;
      for (const h of groups) if (h !== g) b = Math.min(b, h.reduce((s, j) => s + dist[i][j], 0) / h.length);
      if (b === Infinity) continue;
      sum += (b - a) / Math.max(a, b, 1e-12);
    }
  return count ? sum / count : 0;
}

/**
 * Families for topics that name none: average-linkage clustering on relatedness, never merging past
 * MAX_SHADES topics, cut at the level with the best mean silhouette among the cuts with at most
 * MAX_FAMILIES families (ties go to more families). Topic indices in, groups of indices out, in topic order.
 */
export function deriveFamilies(rel: number[][]): number[][] {
  const n = rel.length;
  const sim = similarity(rel);
  const dist = sim.map((row) => row.map((v) => 1 - v));
  let groups = Array.from({ length: n }, (_, i) => [i]);
  const levels: number[][][] = [groups.map((g) => [...g])];
  for (;;) {
    let best: [number, number, number] | null = null;
    for (let a = 0; a < groups.length; a++)
      for (let b = a + 1; b < groups.length; b++) {
        if (groups[a].length + groups[b].length > MAX_SHADES) continue;
        let s = 0;
        for (const i of groups[a]) for (const j of groups[b]) s += sim[i][j];
        s /= groups[a].length * groups[b].length;
        if (s > 0 && (!best || s > best[0] + 1e-12)) best = [s, a, b];
      }
    if (!best) break;
    const [, a, b] = best;
    groups = groups.filter((_, k) => k !== a && k !== b).concat([[...groups[a], ...groups[b]].sort((x, y) => x - y)]);
    groups.sort((x, y) => x[0] - y[0]);
    levels.push(groups.map((g) => [...g]));
  }
  const admissible = levels.filter((l) => l.length <= MAX_FAMILIES);
  if (!admissible.length) throw new Error(`${n} topics cannot fall into ${MAX_FAMILIES} families of at most ${MAX_SHADES}`);
  let pick = admissible[0];
  let score = silhouette(pick, dist);
  for (const l of admissible.slice(1)) {
    const s = silhouette(l, dist);
    if (s > score + 1e-9) [pick, score] = [l, s];
  }
  return pick;
}

/**
 * The circular order of families that maximises the summed relatedness of neighbours, by brute
 * force. The first family stays first (rotation) and of a mirrored pair the lexicographically
 * smaller order is kept, so the answer is unique.
 */
export function seriate(rel: number[][]): number[] {
  const n = rel.length;
  if (n <= 2) return Array.from({ length: n }, (_, i) => i);
  let best: number[] = [];
  let bestScore = -Infinity;
  const rest = Array.from({ length: n - 1 }, (_, i) => i + 1);
  const permute = (prefix: number[], left: number[]) => {
    if (!left.length) {
      const order = [0, ...prefix];
      if (order[1] > order[n - 1]) return; // the mirror image is visited too
      let s = 0;
      for (let i = 0; i < n; i++) s += rel[order[i]][order[(i + 1) % n]];
      if (s > bestScore + 1e-9) [best, bestScore] = [order, s];
      return;
    }
    for (let k = 0; k < left.length; k++) permute([...prefix, left[k]], [...left.slice(0, k), ...left.slice(k + 1)]);
  };
  permute([], rest);
  return best;
}

// ---- Hues, lightness, chroma and shades ------------------------------------------------------

/** The shade positions of a family of k topics, in steps of lightness: evenly spaced around 0. */
export const shadeSteps = (k: number): number[] => (k <= 1 ? [0] : k === 2 ? [-0.5, 0.5] : [-1, 0, 1]);

/** How far a family's own lightness may move off its theme's lightness, so that colour-blind readers can tell families apart. */
export const MAX_LIFT = 0.1;
/** The weights that trade the three distances against each other in the search. */
const WEIGHT = { dichromat: 3, shade: 1.6 };

interface Layout {
  hues: number[]; // per family position
  lift: number[]; // per family position, added to the theme's lightness
  L: Record<ThemeName, number>;
  C: Record<ThemeName, number>;
}

/** Every colour of a layout in one theme: per family position, per shade step. */
function colours(hues: number[], lift: number[], sizes: number[], L: number, C: number): Vec[][] {
  const spacing = 360 / sizes.length;
  return sizes.map((k, f) =>
    shadeSteps(k).map((t) => oklch(L + lift[f] + t * SHADE_STEP.lightness, C * (1 - t * SHADE_STEP.chroma), hues[f] + t * SHADE_STEP.hue * spacing)),
  );
}

/** Least ΔE2000 between different families and between shades of one family, in one theme and vision. */
function floors(all: Vec[][], theme: ThemeName, vision: Vision): { family: number; shade: number } {
  const seenAll = all.map((fam) => fam.map((c) => seen(c, theme, vision)));
  let family = Infinity;
  let shade = Infinity;
  for (let f = 0; f < seenAll.length; f++) {
    for (let i = 0; i < seenAll[f].length; i++) {
      for (let j = i + 1; j < seenAll[f].length; j++) shade = Math.min(shade, deltaE2000(seenAll[f][i], seenAll[f][j]));
      for (let g = f + 1; g < seenAll.length; g++) for (const other of seenAll[g]) family = Math.min(family, deltaE2000(seenAll[f][i], other));
    }
  }
  return { family, shade };
}

/** Largest chroma at which every colour of the theme lies in sRGB (bisection), to 0.001. */
function maxChroma(hues: number[], lift: number[], sizes: number[], L: number): number {
  let lo = 0;
  let hi = 0.4;
  for (let it = 0; it < 20; it++) {
    const mid = (lo + hi) / 2;
    if (colours(hues, lift, sizes, L, mid).flat().every((c) => inGamut(oklabToLinear(c)))) lo = mid;
    else hi = mid;
  }
  return Math.floor(lo * 1000) / 1000;
}

/** Whether every colour of the theme keeps MIN_CONTRAST against its page. */
const contrastHolds = (all: Vec[][], theme: ThemeName) => all.flat().every((c) => groundContrast(c, theme) >= MIN_CONTRAST);

/**
 * The search's score of one theme's colours: a soft minimum (temperature SOFT) of every weighted
 * distance, family pairs in each vision and shade pairs, so that the search sees every near pair
 * and not only the nearest.
 */
const SOFT = 1.5;
function themeScore(all: Vec[][], theme: ThemeName): number {
  let sum = 0;
  for (const vision of VISION_NAMES) {
    const w = vision === "normal" ? 1 : WEIGHT.dichromat;
    const s = all.map((fam) => fam.map((c) => seen(c, theme, vision)));
    for (let f = 0; f < s.length; f++)
      for (let i = 0; i < s[f].length; i++) {
        for (let j = i + 1; j < s[f].length; j++) sum += Math.exp(-(WEIGHT.shade * deltaE2000(s[f][i], s[f][j])) / SOFT);
        for (let g = f + 1; g < s.length; g++) for (const other of s[g]) sum += Math.exp(-(w * deltaE2000(s[f][i], other)) / SOFT);
      }
  }
  return sum ? -SOFT * Math.log(sum) : 0;
}

/**
 * The theme's lightness and chroma: of the lightnesses in the range at which every shade keeps 3:1,
 * the one whose largest common in-gamut chroma scores best.
 */
function fitTheme(hues: number[], lift: number[], sizes: number[], theme: ThemeName, range: [number, number]): { L: number; C: number; score: number } | null {
  let best: { L: number; C: number; score: number } | null = null;
  for (let k = Math.round(range[0] * 200); k <= Math.round(range[1] * 200); k++) {
    const L = k / 200;
    const C = maxChroma(hues, lift, sizes, L);
    const all = colours(hues, lift, sizes, L, C);
    if (!contrastHolds(all, theme)) continue;
    const score = themeScore(all, theme);
    if (!best || score > best.score + 1e-9) best = { L, C, score };
  }
  return best;
}

const FULL: [number, number] = [0.3, 0.9];

function evaluate(hues: number[], lift: number[], sizes: number[], near?: Layout): { layout: Layout; score: number } | null {
  const range = (t: ThemeName): [number, number] => (near ? [near.L[t] - 0.02, near.L[t] + 0.02] : FULL);
  const light = fitTheme(hues, lift, sizes, "light", range("light"));
  const dark = fitTheme(hues, lift, sizes, "dark", range("dark"));
  if (!light || !dark) return null;
  return { layout: { hues, lift, L: { light: light.L, dark: dark.L }, C: { light: light.C, dark: dark.C } }, score: Math.min(light.score, dark.score) };
}

const norm = (h: number) => Math.round((((h % 360) + 360) % 360) * 100) / 100;
const round3 = (v: number) => Math.round(v * 1000) / 1000;

/**
 * Hues for n families: evenly spaced from the best starting angle (3° grid), then each hue nudged
 * within an eighth of the spacing, and each family's lightness within MAX_LIFT, by coordinate
 * ascent while the score improves.
 */
function fitLayout(sizes: number[]): { layout: Layout; score: number } {
  const n = sizes.length;
  const spacing = 360 / n;
  const flat = new Array<number>(n).fill(0);
  let best: { layout: Layout; score: number; start: number } | null = null;
  for (let start = 0; start < spacing; start += 3) {
    const r = evaluate(sizes.map((_, i) => norm(start + i * spacing)), flat, sizes);
    if (r && (!best || r.score > best.score + 1e-9)) best = { ...r, start };
  }
  if (!best) throw new Error("no lightness keeps 3:1 for every shade");
  const even = sizes.map((_, i) => best!.start + i * spacing);
  const bound = spacing / 8;
  let current = { layout: best.layout, score: best.score };
  for (const [hueStep, liftStep] of [[4, 0.04], [2, 0.02], [1, 0.01], [0.5, 0.005]]) {
    let improved = true;
    while (improved) {
      improved = false;
      for (let f = 0; f < n; f++)
        for (const dir of [1, -1]) {
          const hues = [...current.layout.hues];
          const offset = ((hues[f] - even[f] + 540) % 360) - 180 + dir * hueStep;
          if (Math.abs(offset) <= bound + 1e-9) {
            hues[f] = norm(even[f] + offset);
            const r = evaluate(hues, current.layout.lift, sizes, current.layout);
            if (r && r.score > current.score + 1e-6) [current, improved] = [r, true];
          }
          if (n < 2) continue;
          const lift = [...current.layout.lift];
          lift[f] = round3(lift[f] + dir * liftStep);
          if (Math.abs(lift[f]) <= MAX_LIFT + 1e-9) {
            const r = evaluate(current.layout.hues, lift, sizes, current.layout);
            if (r && r.score > current.score + 1e-6) [current, improved] = [r, true];
          }
        }
    }
  }
  return current;
}

// ---- The palette of one topic list -----------------------------------------------------------

export interface PaletteIn {
  topics: TopicIn[];
  families?: FamilyIn[];
  /** Topic-by-topic relatedness, in `topics` order (see relatedness()). */
  related: number[][];
}

export interface PaletteFamily {
  id: string;
  name: string;
  /** False when the family was derived from relatedness rather than named by the authors. */
  named: boolean;
  hue: number;
  topics: string[];
}

export interface PaletteTopic {
  id: string;
  family: string;
  /** The topic's place in colour order (families round the circle, shades dark to light). */
  index: number;
  light: string;
  dark: string;
}

export interface FloorRow {
  theme: ThemeName;
  vision: Vision;
  family: number;
  shade: number;
  contrast: number;
}

export interface Palette {
  families: PaletteFamily[];
  topics: PaletteTopic[];
  lightness: Record<ThemeName, number>;
  chroma: Record<ThemeName, number>;
  floors: FloorRow[];
}

const css = ([L, a, b]: Vec) => {
  const C = Math.hypot(a, b);
  const h = ((Math.atan2(b, a) / RAD) % 360 + 360) % 360;
  return `oklch(${L.toFixed(3)} ${C.toFixed(3)} ${h.toFixed(1)})`;
};

/** Parse what css() writes back to Oklab, so checks read the colours exactly as published. */
export function parseOklch(text: string): Vec {
  const m = /^oklch\(([\d.]+) ([\d.]+) ([\d.]+)\)$/.exec(text);
  if (!m) throw new Error(`not an oklch colour: ${text}`);
  return oklch(Number(m[1]), Number(m[2]), Number(m[3]));
}

/** Check published colours: per theme and vision, the least family and shade distances and contrast. */
export function checkFloors(groups: string[][][]): FloorRow[] {
  // groups[family][shade] = [light, dark]
  const rows: FloorRow[] = [];
  for (const [ti, theme] of THEMES.entries()) {
    const all = groups.map((fam) => fam.map((pair) => parseOklch(pair[ti])));
    const least = Math.min(...all.flat().map((c) => groundContrast(c, theme)));
    for (const vision of VISION_NAMES) rows.push({ theme, vision, ...floors(all, theme, vision), contrast: least });
  }
  return rows;
}

/** The palette of one topic list. Deterministic. */
export function palette(input: PaletteIn): Palette {
  const ids = input.topics.map((t) => t.id);
  const n = ids.length;
  if (!n) return { families: [], topics: [], lightness: { light: 0, dark: 0 }, chroma: { light: 0, dark: 0 }, floors: [] };
  // Families: as named, or derived.
  let groups: number[][];
  let named: boolean;
  let famMeta: FamilyIn[];
  if (input.topics.some((t) => t.family)) {
    const declared = input.families ?? [];
    const order = [...declared.map((f) => f.id), ...input.topics.map((t) => t.family ?? t.id)].filter((v, i, a) => a.indexOf(v) === i);
    groups = order.map((fid) => input.topics.flatMap((t, i) => ((t.family ?? t.id) === fid ? [i] : []))).filter((g) => g.length);
    famMeta = groups.map((g) => {
      const fid = input.topics[g[0]].family ?? input.topics[g[0]].id;
      return declared.find((f) => f.id === fid) ?? { id: fid, name: input.topics[g[0]].name ?? fid };
    });
    named = true;
  } else {
    groups = deriveFamilies(input.related);
    famMeta = groups.map((g) => ({ id: `family-${ids[g[0]]}`, name: g.map((i) => input.topics[i].name ?? ids[i]).join(" · ") }));
    named = false;
  }
  if (groups.length > MAX_FAMILIES) throw new Error(`${groups.length} families; at most ${MAX_FAMILIES}`);
  for (const [k, g] of groups.entries()) if (g.length > MAX_SHADES) throw new Error(`family ${famMeta[k].id} has ${g.length} topics; at most ${MAX_SHADES}`);
  // Family relatedness and circular order.
  const famRel = groups.map((a) => groups.map((b) => (a === b ? 0 : a.reduce((s, i) => s + b.reduce((t, j) => t + input.related[i][j], 0), 0))));
  const order = seriate(famRel);
  const ordered = order.map((k) => groups[k]);
  // Inside a family, the topic most related to the family before it on the circle takes the darkest
  // shade and the one most related to the family after it the lightest; otherwise authored order.
  const sizes = ordered.map((g) => g.length);
  const { layout } = fitLayout(sizes);
  const familiesOut: PaletteFamily[] = [];
  const topicsOut: PaletteTopic[] = [];
  const pairs: string[][][] = [];
  const lightAll = colours(layout.hues, layout.lift, sizes, layout.L.light, layout.C.light);
  const darkAll = colours(layout.hues, layout.lift, sizes, layout.L.dark, layout.C.dark);
  let index = 0;
  for (const [pos, g] of ordered.entries()) {
    const prev = ordered[(pos + ordered.length - 1) % ordered.length];
    const next = ordered[(pos + 1) % ordered.length];
    const lean = (i: number) => next.reduce((s, j) => s + input.related[i][j], 0) - prev.reduce((s, j) => s + input.related[i][j], 0);
    const inFamily = [...g].sort((a, b) => lean(a) - lean(b) || a - b);
    const meta = famMeta[order[pos]];
    familiesOut.push({ id: meta.id, name: meta.name, named, hue: layout.hues[pos], topics: inFamily.map((i) => ids[i]) });
    const famPairs: string[][] = [];
    inFamily.forEach((i, s) => {
      const light = css(lightAll[pos][s]);
      const dark = css(darkAll[pos][s]);
      famPairs.push([light, dark]);
      topicsOut.push({ id: ids[i], family: meta.id, index: index++, light, dark });
    });
    pairs.push(famPairs);
  }
  return { families: familiesOut, topics: topicsOut, lightness: layout.L, chroma: layout.C, floors: checkFloors(pairs) };
}
