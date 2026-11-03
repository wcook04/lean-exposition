// What other parts of the reader may show on the right page without knowing how it is
// built. Small on purpose: anything in the paper can import it.

import type { ReactNode } from "react";
import { Signal } from "./signal";

/** The statement holding the reading line, once it has held it. */
export interface Followed {
  tie: number | null;
  /** The passage at the line. */
  anchor: string | null;
  part: number;
}

/** What the pointer has rested on. A card with no statement in this paper has only a record. */
export interface Pointed {
  tie: number | null;
  record: string;
}

/** What the address names. `tie` is null for a record this paper has no statement of. */
export interface Pin {
  record: string;
  tie: number | null;
}

/** Everything that changes while reading. Written outside React; see signal.ts. */
export interface ReaderSignals {
  heading: Signal<string | null>;
  part: Signal<number>;
  follow: Signal<Followed>;
  point: Signal<Pointed | null>;
  /** The passage of an untied paragraph under the pointer. */
  caption: Signal<string | null>;
}

/** Content that stands in for the Lean page for as long as something is being pointed at. */
export const rightPreview = new Signal<ReactNode>(null);

/**
 * Show a preview on the right page, such as a theorem or a citation under the pointer, and
 * pass null when the pointer leaves: what was there comes back. Nothing moves and the
 * address does not change. Call it after the short dwell the reader's other previews use
 * (`POINT_DWELL`).
 */
export function previewOnRightPage(content: ReactNode | null): void {
  rightPreview.set(content ?? null);
}

/** The Lean page while it stands open. The scroll path asks on every frame, and a search walks the whole paper. */
export const leanPage: { current: HTMLDivElement | null } = { current: null };

/** How long a pointer rests before the right page previews what it is on, in ms. */
export const POINT_DWELL = 150;
/** How long a statement holds the reading line before the right page follows it, in ms. */
export const FOLLOW_HOLD = 200;
