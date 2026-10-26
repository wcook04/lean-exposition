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
