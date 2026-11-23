// The level lens: All, Long record, Short paper, Exposition, each with the number of
// steps of this argument it uses, as plain words: the one chosen is underlined.

import type { Account as Stage } from "../api/types";
import { PAPER_NAMES, STAGE_ORDER } from "../app/papers";
import { LENS_ORDER, type LevelCounts } from "./levels";

export type LensUnit = "records" | "declarations";

const COUNTS: Record<LensUnit, string> = {
  records: "Steps of this argument in each paper",
  declarations: "Lean declarations linked from each paper",
};

export function LensControl({ lens, counts, unit = "records", onLens }: { lens?: Stage; counts: Pick<LevelCounts, "all" | Stage>; unit?: LensUnit; onLens(stage: Stage | undefined): void }) {
  const choices: { id?: Stage; label: string; n: number }[] = [
    { label: "All", n: counts.all },
    ...LENS_ORDER.filter((id) => STAGE_ORDER.includes(id)).map((id) => ({ id, label: PAPER_NAMES[id].short, n: counts[id] })),
  ];
  return (
    <div className="map-lensbox">
      <span className="map-lensbox__label">{COUNTS[unit]}</span>
      <div className="map-lens" role="radiogroup" aria-label={COUNTS[unit]}>
        {choices.map((c) => (
          <button key={c.label} type="button" role="radio" aria-checked={lens === c.id} onClick={() => onLens(c.id)}>
            {c.label} <span className="map-lens__n">{c.n}</span>
          </button>
        ))}
      </div>
    </div>
  );
}
