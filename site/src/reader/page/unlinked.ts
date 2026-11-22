// Where nothing in the Lean is linked to the paragraph being read, the pane shows the whole proof
// map (MapPane.tsx). It highlights the step nearest that place in the paper whose statement there
// has Lean, as a place to start; the line over the map says what that highlight is.

import type { TieModel } from "../ties";
import { startOf } from "./focusModel";

/** The step of the nearest statement with Lean to `at` (a byte of the paper), or null. */
export function nearestWithLean(ties: TieModel, at: number | null, drawn: (id: string) => boolean): string | null {
  let best: string | null = null;
  let gap = Infinity;
  for (const t of ties.order) {
    const tie = ties.index.ties[t];
    if (!tie.lean || !tie.record || !drawn(tie.record)) continue;
    const d = Math.abs((startOf(tie.at) ?? 0) - (at ?? 0));
    if (d < gap) [best, gap] = [tie.record, d];
  }
  return best;
}
