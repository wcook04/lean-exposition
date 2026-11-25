// What other parts of the reader may show on the right page without knowing how it is
// built. Small on purpose: anything in the paper can import it.

import type { ReactNode } from "react";
import type { Alignment, Tie } from "../../api/lean";
import type { PaneMode } from "./ModeToggle";
import type { LinkPreview } from "./nextLink";
import { Signal } from "./signal";

/** The statement holding the reading line, once it has held it. */
export interface Followed {
  tie: number | null;
  /** The passage at the line. */
  anchor: string | null;
  /** Null until the reading position is measured. */
  part: number | null;
  /** The paper is at its top, where Auto shows the whole map. */
  atTop?: boolean;
  /** The pane shows a link the reading line has not reached (nextLink.ts), not one under it. */
  preview?: "next" | "last";
}

/** The pane for a statement or an explicitly selected record, using its Lean dock's sources. */
export function paneForStatement(tie: Tie | undefined, alignment: Alignment | null | undefined, record = tie?.record): PaneMode {
  if (tie && !tie.lean) return "graph";
  if (tie?.rows) return tie.rows.length ? "lean" : "graph";
  // Older ties name their first declaration directly or get their rows from the alignment.
  if (tie?.name && tie.module) return "lean";
  if (!record) return "graph";
  if (alignment === undefined) return "lean";
  const row = alignment?.records[record];
  const statement = tie && row?.statements.find((value) => value.at === tie.at);
  return statement?.lean?.length || row?.lean.length ? "lean" : "graph";
}

/** An exact PDF mark remains the reading position until the reader scrolls. */
export function pdfReadingAt(
  marks: ReadonlyMap<string, unknown>, addressed: string | undefined, measured: string | undefined, scrolled: boolean,
): string | undefined {
  return !scrolled && addressed && marks.has(addressed) ? addressed : measured;
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
  /** The pane keeps its last linked passage while the paper crosses an unlinked area. */
  paneFollow?: Signal<Followed>;
  /** With no link at the reading line: the link Next lands on, or the last one passed. */
  linkPreview?: Signal<LinkPreview | null>;
  /** The annotation whose subject is actually visible in the pane. */
  shownTie: Signal<{ tie: number; at: string } | null>;
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
