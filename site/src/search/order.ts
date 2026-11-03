// What comes first when a reader searches. A theorem's number or a step's exact title, then the
// main result, then what the papers say in plain words, with raw Lean names last unless what
// was typed is itself a Lean name. rank.ts orders within a kind; this file orders the kinds.

import type { SearchItem } from "../api/types";
import { canonicalWord, holdsWord } from "./rank";

const NUMBERED = /^(theorem|lemma|proposition|corollary|definition|question|remark|conjecture)\s+(\d+(?:\.\d+)*)$/i;

/** "Theorem 1" as a kind of result and its number, or null for anything else. */
export function numberedQuery(q: string): { word: string; number: string } | null {
  const found = NUMBERED.exec(q.trim());
  return found ? { word: found[1], number: found[2] } : null;
}

/** Whether a slice opens by stating that numbered result: "**Theorem 1 (full support)" and not "Theorem 1.1". */
export function opensAs(item: SearchItem, wanted: { word: string; number: string }): boolean {
  if (item.excerpt_start_character) return false;
  const opening = new RegExp(`^[\\s*_]*${wanted.word}\\s+${wanted.number.replace(/\./g, "\\.")}(?![\\d]|\\.\\d)`, "i");
  return opening.test(String(item.excerpt ?? ""));
}

/** Whether what was typed has the shape of a Lean name: `full_support`, `IsMinimizer`, `SKValue.parisi`. */
export function leanShaped(q: string): boolean {
  const text = q.trim();
  return !/\s/.test(text) && (/[_.]/.test(text) || /[a-z0-9][A-Z]/.test(text));
}

const plain = (text: string) => text.toLowerCase().split(/\s+/).filter(Boolean).map(canonicalWord).join(" ");

export interface StepTitles {
  /** The step's main result id, where there is one. */
  main: string | null;
  /** A step's titles, full and short. */
  titles(id: string): readonly string[];
  idOf(item: SearchItem): string;
  /** Whether the step is a bare Lean declaration, which reads as a raw name. */
  isDeclaration(id: string): boolean;
}

export interface Found {
  q: string;
  /** Every matching step, best first. */
  steps: readonly SearchItem[];
  statements: readonly SearchItem[];
  text: readonly SearchItem[];
}

const PAPER_ORDER = ["short", "long", "expository"];
const paperOf = (item: SearchItem) => PAPER_ORDER.indexOf(String((item.papers as string[] | undefined)?.[0]));

/** The few results that are exactly what was asked for, best first. */
export function bestMatches(found: Found, steps: StepTitles): SearchItem[] {
  const best: SearchItem[] = [];
  const wanted = numberedQuery(found.q);
  if (wanted) {
    const stated = found.statements.filter((item) => opensAs(item, wanted));
    const pool = stated.length ? stated : found.text.filter((item) => opensAs(item, wanted));
    best.push(...[...pool].sort((a, b) => paperOf(a) - paperOf(b)).slice(0, 3));
  }
  const asked = plain(found.q);
  for (const item of found.steps) if (steps.titles(steps.idOf(item)).some((title) => plain(title) === asked)) best.push(item);
  // The main result comes next when its title holds the words. A Lean name asks for the Lean.
  const main = found.steps.find((item) => steps.idOf(item) === steps.main);
  const words = found.q.toLowerCase().split(/\s+/).filter(Boolean);
  const titled = main && steps.titles(steps.idOf(main)).some((title) => words.every((word) => holdsWord(title.toLowerCase(), word)));
  if (main && titled && !leanShaped(found.q) && !best.includes(main)) best.push(main);
  return best;
}

/** Steps with plain titles first; a step that is only a Lean name after them. */
export function plainSteps(items: readonly SearchItem[], steps: StepTitles): SearchItem[] {
  const raw = (item: SearchItem) => Number(steps.isDeclaration(steps.idOf(item)));
  return items.map((item, i) => ({ item, i })).sort((a, b) => raw(a.item) - raw(b.item) || a.i - b.i).map((row) => row.item);
}
