// The level lens: All, Long record, Short paper, Exposition, each with the number of
// records of this argument it uses. One pill whose thumb slides to the level shown,
// in the same grammar as the view switch beside it.

import { useLayoutEffect, useRef, useState } from "react";
import type { Stage } from "../api/types";
import { PAPER_NAMES } from "../app/papers";
import { LENS_ORDER, type LevelCounts } from "./levels";

export function LensControl({ lens, counts, onLens }: { lens?: Stage; counts: LevelCounts; onLens(stage: Stage | undefined): void }) {
  const group = useRef<HTMLDivElement>(null);
  const [thumb, setThumb] = useState<{ x: number; w: number } | null>(null);
  useLayoutEffect(() => {
    const el = group.current;
    if (!el) return;
    const place = () => {
      const b = el.querySelector<HTMLElement>('[aria-checked="true"]');
      setThumb(b ? { x: b.offsetLeft, w: b.offsetWidth } : null);
    };
    place();
    const observer = new ResizeObserver(place);
    observer.observe(el);
    return () => observer.disconnect();
  }, [lens, counts]);
  const choices: { id?: Stage; label: string; n: number }[] = [
    { label: "All", n: counts.all },
    ...LENS_ORDER.map((id) => ({ id, label: PAPER_NAMES[id].short, n: counts[id] })),
  ];
  return (
    <div className="map-lens" role="radiogroup" aria-label="Records used by each level" ref={group}>
      {thumb && <span className="map-views__thumb" aria-hidden="true" style={{ transform: `translateX(${thumb.x}px)`, width: thumb.w }} />}
      {choices.map((c) => (
        <button key={c.label} type="button" role="radio" aria-checked={lens === c.id} onClick={() => onLens(c.id)}>
          {c.label} <span className="map-lens__n">{c.n}</span>
        </button>
      ))}
    </div>
  );
}
