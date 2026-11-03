// With a paper lens on, one quiet bar for that paper: step through its passages about
// this argument in reading order, each one lighting its records on the map.

import { useEffect, useMemo, useState } from "react";
import type { PaperStructure, Stage } from "../api/types";
import { loadPaperStructure } from "../app/data";
import { PAPER_NAMES } from "../app/papers";
import { routeHref } from "../app/router";
import { firstSections, walkPassages, type WalkPassage } from "./levels";

/** The lens's paper, loaded when a lens is chosen. */
export function useWalk(lens: Stage | undefined, argument: ReadonlySet<string>): { passages: WalkPassage[]; sections: ReadonlyMap<string, string> | null } {
  const [loaded, setLoaded] = useState<{ stage: Stage; structure: PaperStructure } | null>(null);
  useEffect(() => {
    if (!lens) return;
    let alive = true;
    void loadPaperStructure(lens).then(
      (structure) => alive && setLoaded({ stage: lens, structure }),
      () => undefined,
    );
    return () => {
      alive = false;
    };
  }, [lens]);
  return useMemo(() => {
    if (!lens || loaded?.stage !== lens) return { passages: [], sections: null };
    const passages = walkPassages(loaded.structure, argument);
    return { passages, sections: firstSections(passages) };
  }, [lens, loaded, argument]);
}

export function WalkBar({ stage, passages, at, onStep }: { stage: Stage; passages: WalkPassage[]; at: number | null; onStep(delta: number): void }) {
  const here = at === null ? null : passages[at];
  return (
    <div className="walkbar" role="group" aria-label={`Passages of the ${PAPER_NAMES[stage].short.toLowerCase()}`}>
      <button type="button" className="walkbar__step" aria-label="Previous passage" title="Previous passage ([)" disabled={!at} onClick={() => onStep(-1)}>
        ◀
      </button>
      <button type="button" className="walkbar__step" aria-label="Next passage" title="Next passage (])" disabled={at === passages.length - 1 || !passages.length} onClick={() => onStep(1)}>
        ▶
      </button>
      <p className="walkbar__place" aria-live="polite">
        {here ? here.place : `Step through the ${passages.length} passages of the ${PAPER_NAMES[stage].short.toLowerCase()} on this argument`}
      </p>
      {here && <a href={routeHref({ view: "read", stage, anchor: here.anchor })}>Read here</a>}
    </div>
  );
}
