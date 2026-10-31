// A record's Lean mark away from the canvas: a small tile with the map's own shape and bars,
// for the key, the outline and the sheet. The words are always given beside it or as its name.

import type { LeanLevel, LeanMark } from "../model/leanStatus";
import { markWords } from "../model/leanStatus";
import "./lean-glyph.css";

export function LeanGlyph({ mark, label }: { mark: Pick<LeanMark, "shape"> & { statement?: LeanLevel; proof?: LeanMark["proof"] }; label?: string }) {
  const named = label ?? (mark.statement && mark.proof ? markWords(mark as LeanMark) : undefined);
  return <span className="lean-glyph" data-shape={mark.shape} data-s={mark.statement} data-p={mark.proof} role={named ? "img" : undefined} aria-label={named} aria-hidden={named ? undefined : true} />;
}
