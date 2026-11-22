// An adapted edition's changes (docs/reader-design.md, "Adapted editions"): the change map that
// scripts/adapted_edition.py writes as alignment/changes-<slot>.json and the build publishes at
// changes/<slot>.json. It lists every change in the order of the edition's text, with the
// authors' paragraphs it replaces and the edition's paragraphs that show it, and aligns the two
// texts paragraph by paragraph so a switch between them keeps the reader's place.

import site from "@instance/site";
import type { Stage } from "../../api/types";

export interface ChangeSource { kind: string; ref: string; url?: string; title?: string; where?: string }
export interface Change {
  id: string;
  part: string;
  kind: string;
  /** The authors' paragraphs the change names ("<heading>#<block>"). */
  authors: string[];
  note: string;
  sources: ChangeSource[];
  status: string;
  /** The edition's paragraphs that show the change, with their lines in its paper.md ([start, end)). */
  adapted: string[];
  adapted_lines: [number, number][];
  adapted_text: string;
  /** The authors' paragraphs the change replaces, and their text; none for an addition. */
  replaced: string[];
  authors_text: string;
  authors_lines: [number, number][];
  /** The change is to the TeX's build lines alone: the reading copy's words are the authors'. */
  text_unchanged?: boolean;
}
export interface ParagraphRow {
  authors: string | null;
  adapted: string | null;
  change: string | null;
  authors_lines: [number, number] | null;
  adapted_lines: [number, number] | null;
}
export interface ChangeMap { schema: string; authors: Stage; adapted: Stage; changes: Change[]; paragraphs: ParagraphRow[] }

export const ADAPTED = site.adapted ?? null;

/** Whether a slot is one side of an adapted edition: the edition or the authors' document it adapts. */
export function editionSide(stage: Stage): "adapted" | "authors" | null {
  if (!ADAPTED) return null;
  if (stage === ADAPTED.slot) return "adapted";
  if (stage === ADAPTED.of) return "authors";
  return null;
}

let loaded: Promise<ChangeMap | null> | null = null;
/** The change map, once per page; null when the build published none. */
export function loadChanges(): Promise<ChangeMap | null> {
  if (!ADAPTED) return Promise.resolve(null);
  loaded ??= fetch(`${import.meta.env.BASE_URL}changes/${ADAPTED.slot}.json`)
    .then((r) => (r.ok ? (r.json() as Promise<ChangeMap>) : null))
    .catch(() => null);
  return loaded;
}

const KIND_WORDS: Record<string, string> = {
  clarification: "Clarification",
  "added-justification": "Added justification",
  "formal-note": "Note on the formal statement",
  "edition-credit": "Edition credit",
  correction: "Correction",
  restatement: "Restatement",
  cut: "Cut",
};
export const kindWords = (kind: string) => KIND_WORDS[kind] ?? kind.replace(/-/g, " ").replace(/^./, (c) => c.toUpperCase());

/**
 * The place on the other side for a line of this side: the start of the partner of the
 * paragraph that holds the line, else of the nearest paragraph before it that has one. `exact`
 * is false when the paragraph itself has no counterpart (an addition, or a cut).
 */
export function counterpart(map: ChangeMap, from: "adapted" | "authors", line: number): { line: number; exact: boolean } | null {
  const to = from === "adapted" ? "authors" : "adapted";
  const mine = (r: ParagraphRow) => (from === "adapted" ? r.adapted_lines : r.authors_lines);
  const theirs = (r: ParagraphRow) => (to === "adapted" ? r.adapted_lines : r.authors_lines);
  const rows = map.paragraphs;
  const at = rows.findIndex((r) => {
    const lines = mine(r);
    return !!lines && lines[0] <= line && line < lines[1];
  });
  if (at < 0) {
    // A line between paragraphs (a heading, an anchor): the same distance before the next paragraph
    // that both texts share.
    const next = rows.find((r) => mine(r) && theirs(r) && mine(r)![0] > line);
    if (next) return { line: Math.max(1, theirs(next)![0] - (mine(next)![0] - line)), exact: true };
    return null;
  }
  for (let k = at; k >= 0; k--) {
    const other = theirs(rows[k]);
    if (other) return { line: other[0], exact: k === at };
  }
  return null;
}

/** The change shown by the edition's paragraph at this line, if any. */
export function changeAtLine(map: ChangeMap, line: number): Change | null {
  return map.changes.find((c) => c.adapted_lines.some(([a, b]) => a <= line && line < b)) ?? null;
}

/**
 * A place carried across the switch: the reader opens the other text at `line`, with a notice
 * when the paragraph had no counterpart. Read once by the reader that mounts next.
 */
let pending: { stage: Stage; line: number; notice: string | null; at: number } | null = null;
export function carryPlace(next: { stage: Stage; line: number; notice: string | null }) {
  pending = { ...next, at: Date.now() };
}
export function takePlace(stage: Stage) {
  // Read, not removed: the reader may mount twice for one switch (while its text loads), and the
  // place is let go when it has been used (clearPlace) or a newer switch replaces it.
  return pending && pending.stage === stage && Date.now() - pending.at < 15000 ? pending : null;
}
export function clearPlace() {
  pending = null;
}
