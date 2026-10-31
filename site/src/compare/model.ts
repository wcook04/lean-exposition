// The rules of the bench, with no DOM and no network, so they are tested directly:
// which rows the outline lists and in what order, what each level does with a record,
// and which levels get a column at a given width.

import type { RecordAlignment, StatementRole, LeanRelation } from "../api/lean";
import type { Stage } from "../api/types";
import type { ArgGraph } from "../model/graph";
import { LEVELS, type Level } from "../app/router";
import { usesOf } from "../map/treeModel";
import { inLevel } from "../map/levels";

export const LEVEL_NAMES: Record<Level, string> = {
  lean: "Lean",
  long: "Long record",
  short: "Short paper",
  expository: "Exposition",
};

const IN_PROSE: Record<Level, string> = {
  lean: "OpenAI's Lean",
  long: "the long record",
  short: "the short paper",
  expository: "the exposition",
};

export interface OutlineRow {
  id: string;
  depth: number;
}

/** The argument as a reading outline: depth first from the goal, each record once, at its first use. */
export function argumentOutline(graph: ArgGraph, goal: string): OutlineRow[] {
  const rows: OutlineRow[] = [];
  const seen = new Set<string>();
  const walk = (id: string, depth: number) => {
    seen.add(id);
    rows.push({ id, depth });
    for (const e of usesOf(graph, id)) {
      if (!seen.has(e.to)) walk(e.to, depth + 1);
    }
  };
  if (graph.nodes.has(goal)) walk(goal, 0);
  return rows;
}

/** Rows whose title holds every word typed, in any order. */
export function filterOutline<T extends { id: string }>(rows: readonly T[], query: string, titleOf: (id: string) => string): T[] {
  const words = query.toLowerCase().split(/\s+/).filter(Boolean);
  if (!words.length) return [...rows];
  return rows.filter((row) => {
    const title = titleOf(row.id).toLowerCase();
    return words.every((word) => title.includes(word));
  });
}

/** The next row from `id`, staying at the ends. A record outside the list starts at its top. */
export function walk<T extends { id: string }>(rows: readonly T[], id: string | undefined, step: 1 | -1): T | null {
  const at = rows.findIndex((row) => row.id === id);
  if (at < 0) return rows[0] ?? null;
  return rows[at + step] ?? null;
}

// ----------------------------------------------------------- level filter

/** The whole argument, or the steps one paper discusses: that paper as a subgraph of the argument. */
export type LevelFilter = "all" | Stage;

export const LEVEL_FILTERS: { id: LevelFilter; label: string }[] = [
  { id: "all", label: "All" },
  { id: "long", label: "Long record" },
  { id: "short", label: "Short paper" },
  { id: "expository", label: "Exposition" },
];

export function filterByLevel<T extends { id: string }>(rows: readonly T[], filter: LevelFilter, graph: ArgGraph): T[] {
  return filter === "all" ? [...rows] : rows.filter((row) => {
    const node = graph.nodes.get(row.id);
    return !!node && inLevel(node, filter);
  });
}

/** The next listed row, measured along the whole outline when the current record is not listed. */
export function walkListed<T extends { id: string }>(outline: readonly T[], listed: readonly T[], id: string | undefined, step: 1 | -1): T | null {
  if (listed.some((row) => row.id === id)) return walk(listed, id, step);
  const at = outline.findIndex((row) => row.id === id);
  if (at < 0) return listed[0] ?? null;
  const ahead = step === 1 ? outline.slice(at + 1) : outline.slice(0, at).reverse();
  return ahead.find((row) => listed.some((l) => l.id === row.id)) ?? null;
}

// ----------------------------------------------------------------- levels

export const ROLE_ORDER: StatementRole[] = ["statement", "definition", "derivation", "explanation", "example", "mention"];

const ROLE_VERBS: Record<StatementRole, string> = {
  statement: "States it",
  definition: "Defines it",
  derivation: "Derives it",
  explanation: "Explains it",
  example: "Works an example",
  mention: "Mentions it",
};

export const roleWords = (role: StatementRole) => ROLE_VERBS[role];

const LEAN_ORDER: LeanRelation[] = ["states", "defines", "contains", "part", "proof"];

const LEAN_VERBS: Record<LeanRelation, string> = {
  states: "States it",
  defines: "Defines it",
  contains: "Contains it in a wider statement",
  part: "States a part of it",
  proof: "Carries a proof step",
};

export function statementsOf(record: RecordAlignment, stage: Stage) {
  return record.statements
    .filter((s) => s.paper === stage)
    .sort((a, b) => ROLE_ORDER.indexOf(a.role) - ROLE_ORDER.indexOf(b.role) || a.start_byte - b.start_byte);
}

/** What a level does with a record, strongest first; null when it has nothing. */
export function levelVerb(record: RecordAlignment, level: Level): string | null {
  if (level === "lean") {
    const relation = LEAN_ORDER.find((r) => record.lean.some((row) => row.relation === r));
    return relation ? LEAN_VERBS[relation] : null;
  }
  const first = statementsOf(record, level)[0];
  return first ? ROLE_VERBS[first.role] : null;
}

/** How much a level has to show, in characters, a declaration counting as a short paragraph. */
function amount(record: RecordAlignment, level: Level): number {
  if (level === "lean") return record.lean.length * 700;
  return statementsOf(record, level).reduce((n, s) => n + s.markdown.length, 0);
}

/** How much a level matters for this record: a level that states it before one that mentions it. */
function strength(record: RecordAlignment, level: Level): number {
  if (level === "lean") return record.lean.length ? 6 : 0;
  const first = statementsOf(record, level)[0];
  return first ? ROLE_ORDER.length - ROLE_ORDER.indexOf(first.role) : 0;
}

/** How many columns the bench shows by default at a width of the window. */
export function defaultColumns(width: number): number {
  if (width >= 1680) return 4;
  if (width >= 1280) return 3;
  return 2;
}

export const STACK_BELOW = 1000;

export type Slot =
  | { level: Level; state: "column"; weight: number }
  /** The level has nothing for this record. */
  | { level: Level; state: "empty" }
  /** The level has something, but the width left it out; its strip opens it. */
  | { level: Level; state: "folded" };

/**
 * One slot per level, most formal first. A reader's own choice is followed exactly,
 * except that a chosen level with nothing becomes a strip. Without a choice the levels
 * with most to say get the columns the width allows, and the rest stay reachable as
 * strips. Widths follow what each column holds.
 */
export function arrangeLevels(record: RecordAlignment, width: number, chosen?: readonly Level[]): Slot[] {
  const has = (level: Level) => amount(record, level) > 0;
  const column = (level: Level): Slot => ({ level, state: "column", weight: columnWeight(amount(record, level)) });
  // A choice with nothing for this record would leave the bench empty, so it is set aside here.
  if (chosen?.some(has)) {
    return LEVELS.filter((level) => chosen.includes(level)).map((level) => (has(level) ? column(level) : { level, state: "empty" }));
  }
  const ranked = LEVELS.filter(has).sort((a, b) => strength(record, b) - strength(record, a) || LEVELS.indexOf(a) - LEVELS.indexOf(b));
  const shown = new Set(ranked.slice(0, defaultColumns(width)));
  return LEVELS.map((level) => (shown.has(level) ? column(level) : { level, state: has(level) ? "folded" : "empty" }));
}

/** Between one and two shares, growing slowly with the text. */
export function columnWeight(characters: number): number {
  return Math.round(Math.min(2, Math.max(1, Math.sqrt(characters / 500))) * 100) / 100;
}

/** "Not in the exposition", for a level with nothing on this record. */
export function absentWords(level: Level): string {
  return `Not in ${IN_PROSE[level]}`;
}

/** The sentence for a step with no linked declaration, which depends on what the Lean covers. */
export function leanAbsence(id: string): string {
  if (id.startsWith("circuit.") || id.startsWith("qaoa_")) return "OpenAI's Lean covers full support and the scalar value, and has no declaration for this result.";
  return "No Lean declaration is linked to this step. OpenAI's Lean covers full support and the scalar value; the steps it uses and is used by may have their own.";
}

// --------------------------------------------------------- reader's choice

const STORE = "lx-compare-levels";

export function storedLevels(): Level[] | undefined {
  try {
    const raw = window.localStorage.getItem(STORE);
    if (!raw) return undefined;
    const levels = raw.split(",").filter((v): v is Level => (LEVELS as readonly string[]).includes(v));
    return levels.length ? levels : undefined;
  } catch {
    return undefined;
  }
}

export function storeLevels(levels: readonly Level[] | undefined): void {
  try {
    if (levels) window.localStorage.setItem(STORE, levels.join(","));
    else window.localStorage.removeItem(STORE);
  } catch {
    // The choice still lives in the address.
  }
}

/** A level toggled on or off, keeping the levels' order. At least one stays on. */
export function toggleLevel(shown: readonly Level[], level: Level): Level[] {
  const next = shown.includes(level) ? shown.filter((l) => l !== level) : [...shown, level];
  return next.length ? LEVELS.filter((l) => next.includes(l)) : [...shown];
}
