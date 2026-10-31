// A record's Lean mark away from the canvas: a small tile with the map's own shape and fill,
// for the key, the outline and the sheet. The words are always given beside it or as its name.

import type { LeanLevel, LeanMark } from "../model/leanStatus";
import { leanFill, markWords } from "../model/leanStatus";
import "./lean-glyph.css";

export function LeanGlyph({ mark, fill, label }: { mark?: LeanMark; fill?: LeanLevel; label?: string }) {
  const named = label ?? (mark ? markWords(mark) : undefined);
  const level = fill ?? (mark ? leanFill(mark) : "none");
  return <span className="lean-glyph" data-shape={mark?.shape ?? "round"} data-fill={level} role={named ? "img" : undefined} aria-label={named} aria-hidden={named ? undefined : true} />;
}
