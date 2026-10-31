// The reading position of each history entry, so Back returns to the line a
// reader left rather than to the top or to a stale #anchor. A position names
// the edition, the account, the part (by its passage anchor or first heading
// when it has one) and an offset into it, which survives parts above it
// changing height; it is never a raw page Y.
//
// A visit to another treatment keeps its origin in the history entry's state
// (`lxVisit`), so "Return to Short paper §4" can restore exactly the line the
// reader left, separately from Back and from closing the visit.

import type { Stage } from "../../api/types";
import { arrivedBy, entryKey } from "../../app/trail";

export interface ReadingPosition {
  /** The edition the offsets were measured in; another edition's position is not reused. */
  edition?: string;
  stage: string;
  part: number;
  /** A stable name for the part: its passage anchor or first heading id. */
  partId?: string;
  offset: number;
}

export interface VisitOrigin {
  /** The history key whose saved position is the place to return to. */
  key: string;
  stage: Stage;
  /** The passage the visit started from, when there was one. */
  anchor?: string;
  /** "Short paper §4", for "Return to Short paper §4". */
  label: string;
}

const PREFIX = "lx-read:";

function state(): Record<string, unknown> {
  return (window.history.state ?? {}) as Record<string, unknown>;
}

/** Merge keys into the current history entry's state (the map keeps its own keys there). */
export function patchHistoryState(patch: Record<string, unknown>): void {
  const next = { ...state(), ...patch };
  for (const [k, v] of Object.entries(patch)) if (v === undefined) delete next[k];
  try {
    window.history.replaceState(next, "", window.location.href);
  } catch {
    /* A sandboxed frame may refuse; the state is then not kept. */
  }
}

/** The key of the current history entry. */
export function historyKey(): string {
  return entryKey();
}

/** The current entry's key when Back or Forward arrived at it; null on a new entry. */
export function existingHistoryKey(): string | null {
  return arrivedBy() === "pop" ? entryKey() : null;
}

export function visitOrigin(): VisitOrigin | null {
  const v = state().lxVisit as VisitOrigin | undefined;
  return v && typeof v.key === "string" && typeof v.label === "string" ? v : null;
}

/** A key whose saved position this entry should open at (set by Return). */
export function restoreKey(): string | null {
  const r = state().lxRestore;
  return typeof r === "string" ? r : null;
}

export function savePosition(key: string, position: ReadingPosition): void {
  try {
    sessionStorage.setItem(PREFIX + key, JSON.stringify(position));
  } catch {
    /* Storage can be unavailable (private windows); Back then opens at the anchor. */
  }
}

export function loadPosition(key: string): ReadingPosition | null {
  try {
    const raw = sessionStorage.getItem(PREFIX + key);
    if (!raw) return null;
    const value = JSON.parse(raw) as ReadingPosition;
    return typeof value.part === "number" && typeof value.offset === "number" ? value : null;
  } catch {
    return null;
  }
}

/**
 * The part a saved position names in this document: by its stable id when it
 * still exists, else by index. Null when the position belongs to another
 * account or edition.
 */
export function partOfPosition(
  position: ReadingPosition,
  here: { stage: string; edition?: string; parts: { index: number; anchor?: string; headings: { id: string }[] }[] },
): number | null {
  if (position.stage !== here.stage) return null;
  if (position.edition && here.edition && position.edition !== here.edition) return null;
  if (position.partId) {
    const found = here.parts.find((p) => partIdOf(p) === position.partId);
    if (found) return found.index;
  }
  return position.part >= 0 && position.part < here.parts.length ? position.part : null;
}

export function partIdOf(part: { anchor?: string; headings: { id: string }[] }): string | undefined {
  return part.anchor ?? part.headings[0]?.id;
}
