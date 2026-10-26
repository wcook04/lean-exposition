// How a record is drawn at a screen scale k (DESIGN.md, "Two scales, three
// representations"). The camera never shrinks prose below reading size: past
// a threshold the card changes form instead.

export type Rep = "card" | "compact" | "mark";

/** Card at k >= CARD_K, compact title down to MARK_K, a mark below. */
export const CARD_K = 0.8;
export const MARK_K = 0.5;

/** Steps opens at k = 1; it accepts down to this only when that buys the whole first row. */
export const STEPS_K = 1;
export const STEPS_FLOOR = 0.85;
/** The side pane's tree uses smaller cards and a lower floor. */
export const COMPACT_FLOOR = 0.75;
export const MIN_K = 0.1;
export const MAX_K = 1.8;

export function repFor(k: number): Rep {
  if (k >= CARD_K - 1e-6) return "card";
  if (k >= MARK_K - 1e-6) return "compact";
  return "mark";
}

export type MapMode = "steps" | "overview";

/** The compact tile's box on screen (tree.css .card__compact): padding and border, in screen pixels. */
export const TILE = { padTop: 10, padBottom: 7, padX: 8, border: 1 } as const;

export type TitleKind = "card" | "lean" | "root";

/** Title sizes tried in a compact tile, largest first, and their line heights. */
export const TITLE_SIZES: Record<TitleKind, { sizes: number[]; lineH: number }> = {
  card: { sizes: steps(13, 11), lineH: 1.22 },
  lean: { sizes: steps(12, 10), lineH: 1.22 },
  root: { sizes: steps(18, 15), lineH: 1.2 },
};

function steps(hi: number, lo: number): number[] {
  const out: number[] = [];
  for (let s = hi; s >= lo - 1e-9; s -= 0.5) out.push(s);
  return out;
}

/** Room for title lines: the tile's height on screen less its padding, border and (on the plate) the "MAIN RESULT" line. */
function roomOf(h: number, k: number, kind: TitleKind): number {
  // The plate's "MAIN RESULT" line (11px at line height 1.2) and the 5px gap under it.
  const above = kind === "root" ? 11 * 1.2 + 5 : 0;
  return h * k - 2 * TILE.border - TILE.padTop - TILE.padBottom - above;
}

/**
 * Compact form at the largest title size: how many lines fit in a tile of world
 * height `h` at scale k. Never fewer than one line.
 */
export function compactLines(h: number, k: number, kind: TitleKind): number {
  const { sizes, lineH } = TITLE_SIZES[kind];
  return Math.max(1, Math.floor((roomOf(h, k, kind) + 0.5) / (sizes[0] * lineH)));
}

/**
 * A title as the pieces a line may break between, measured once at a reference
 * size (REF_PX): words (a line may also break after a hyphen), or a Lean name's
 * pieces (LEAN_BREAK). `gap` is what joins a piece to the one before it on the
 * same line: a space, or nothing.
 */
export interface MeasuredTitle {
  pieces: { w: number; gap: number }[];
}

export const REF_PX = 100;

/**
 * Where a Lean name may break in a compact tile: after a dot or underscore, and
 * between a lower-case letter or digit and the capital that starts the next word of
 * a camel-case name ("ZeroTemperature|SK"). Never inside a word. A full card, which
 * has room, breaks after dots and underscores only.
 */
export const LEAN_BREAK = /(?<=[._])|(?<=[a-z0-9])(?=[A-Z])/;

/** Split a title into the pieces a line may break between; `space` marks a piece that follows a space. */
export function titlePieces(text: string, lean: boolean): { text: string; space: boolean }[] {
  if (lean) return text.split(LEAN_BREAK).map((t) => ({ text: t, space: false }));
  const out: { text: string; space: boolean }[] = [];
  text
    .trim()
    .split(/\s+/)
    .forEach((word, i) => word.split(/(?<=-)(?=.)/).forEach((part, j) => out.push({ text: part, space: i > 0 && j === 0 })));
  return out;
}

/** Greedy wrap at `size`: the number of lines, or Infinity when one piece is wider than the line. */
export function wrapLines(t: MeasuredTitle, size: number, width: number): number {
  const scale = size / REF_PX;
  let lines = 1;
  let cur = 0;
  for (const p of t.pieces) {
    const w = p.w * scale;
    if (w > width + 0.01) return Infinity;
    const next = cur === 0 ? w : cur + p.gap * scale + w;
    if (next > width + 0.01) {
      lines++;
      cur = w;
    } else cur = next;
  }
  return lines;
}

/**
 * Compact form: the largest title size (13px down to 11px; Lean 12 to 10; the
 * plate 18 to 15) at which the whole title fits the tile on screen, and the
 * number of lines the tile holds at that size. Only a title that cannot fit
 * even at the smallest size is clamped (`fits` false), at the smallest size.
 */
export function fitTitle(t: MeasuredTitle, w: number, h: number, k: number, kind: TitleKind): { size: number; lines: number; fits: boolean } {
  const { sizes, lineH } = TITLE_SIZES[kind];
  const width = (kind === "root" ? Math.min(w, 560 / k) : w) * k - 2 * TILE.border - 2 * TILE.padX;
  const room = roomOf(h, k, kind);
  for (const size of sizes) {
    const max = Math.max(1, Math.floor((room + 0.5) / (size * lineH)));
    if (wrapLines(t, size, width) <= max) return { size, lines: max, fits: true };
  }
  const size = sizes[sizes.length - 1];
  return { size, lines: Math.max(1, Math.floor((room + 0.5) / (size * lineH))), fits: false };
}
