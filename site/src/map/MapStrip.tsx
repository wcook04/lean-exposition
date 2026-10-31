// The strip under the canvas.

import type { RefObject } from "react";
import { LeanGlyph } from "./LeanGlyph";
import { Sample } from "./Sample";

/** Where the Lean graph's lines come from, in the words the index gives. */
export function usesSource(source: string | undefined): string {
  return source === "elaborated" ? "Lines from the compiler's report" : "Lines from a text scan of the source";
}

interface StripLean {
  source?: string;
  note?: string;
  leftOut?: number;
  /** How much of the graph is drawn, when that is only a part. */
  place?: string;
}

/**
 * The strip under the canvas: the key a newcomer needs, always on the page, and Fit. What the
 * pointer rests on is named here for that moment, so a caption can never cover a target.
 */
export function MapStrip({ lean, captionRef, onFit, onNear }: { lean?: StripLean; captionRef: RefObject<HTMLParagraphElement | null>; onFit(): void; onNear?(): void }) {
  return (
    <div className="map-strip">
      <div className="map-strip__text">
        <p ref={captionRef} className="map-caption" hidden />
        {lean ? (
          <ul className="map-legend" aria-label="Key to the Lean graph">
            {lean.place && <li className="map-legend__place">{lean.place}</li>}
            <li>
              <Sample kind="supports" /> Proof uses
            </li>
            <li>
              <Sample kind="lean_type_dependency" /> Statement uses
            </li>
            <li>
              <Sample kind="lean_via" /> Through helpers
            </li>
            <li title={lean.note} className="map-legend__source">
              {usesSource(lean.source)}
            </li>
          </ul>
        ) : (
          <ul className="map-legend" aria-label="Key to the argument">
            <li>
              <LeanGlyph fill="whole" /> Proved in Lean
            </li>
            <li>
              <LeanGlyph fill="part" /> Some of it in Lean
            </li>
            <li>
              <LeanGlyph fill="none" /> Not in Lean
            </li>
            <li>A box is a definition</li>
          </ul>
        )}
      </div>
      {onNear && (
        <button type="button" className="map-fit" onClick={onNear}>
          Around this step
        </button>
      )}
      <button type="button" className="map-fit" title="Show the whole map (0)" onClick={onFit}>
        <svg viewBox="0 0 16 16" width="14" height="14" aria-hidden="true">
          <path d="M2.5 6V2.5H6M10 2.5h3.5V6M13.5 10v3.5H10M6 13.5H2.5V10" fill="none" stroke="currentColor" strokeWidth="1.5" strokeLinecap="round" strokeLinejoin="round" />
        </svg>
        Fit
      </button>
    </div>
  );
}
