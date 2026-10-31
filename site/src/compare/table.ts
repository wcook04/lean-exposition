// The proof as a table: a row is one step of the argument, a column is a level, and a
// cell is what that level says about that step. These are its rules, with no DOM and no
// network, so they are tested directly.

import type { AlignedStatement, RecordAlignment } from "../api/lean";
import type { Stage } from "../api/types";
import { LEVELS, type Level } from "../app/router";
import { defaultColumns, statementsOf } from "./model";

/** What a paper says about a step, strongest first. A bare mention says nothing about it. */
export function sayings(record: RecordAlignment, stage: Stage): AlignedStatement[] {
  return statementsOf(record, stage).filter((s) => s.role !== "mention");
}

export function holds(record: RecordAlignment, level: Level): boolean {
  return level === "lean" ? record.lean.length > 0 : sayings(record, level).length > 0;
}

const isPaper = (level: Level): level is Stage => level !== "lean";

/** One row: the step it is named for, and any others whose cells would say the same words. */
export interface TableRow {
  id: string;
  also: string[];
}

/** Where a cell's words start, as a key. Two slices that start together are the same statement. */
function cellKey(record: RecordAlignment, level: Level): string {
  if (level === "lean") return record.lean[0]?.name ?? "";
  return String(sayings(record, level)[0]?.start_byte ?? "");
}

/** The row that stands for a step, if any does. */
export const rowFor = (rows: readonly TableRow[], id: string): TableRow | undefined => rows.find((row) => row.id === id || row.also.includes(id));

/**
 * The rows a table of these levels lists. By default every level must hold the step, so
 * each row compares something; `any` keeps a step that at least one level holds. The main
 * result comes first, then the first paper's reading order, so its column reads down as
 * the paper does; steps it lacks follow, in the next paper's order, and steps only the
 * Lean has come last, in the order of the source. Steps whose cells would start with the
 * same words share a row, so a table never repeats itself.
 */
export function tableRows(records: Readonly<Record<string, RecordAlignment>>, levels: readonly Level[], any: boolean, main?: string): TableRow[] {
  const papers = LEVELS.filter((level) => levels.includes(level)).filter(isPaper);
  const listed = Object.keys(records).filter((id) => (any ? levels.some((l) => holds(records[id], l)) : levels.every((l) => holds(records[id], l))));
  const place = (id: string): { paper: number; at: number } => {
    const paper = papers.findIndex((stage) => sayings(records[id], stage).length > 0);
    return paper < 0 ? { paper: papers.length, at: records[id].lean[0]?.line ?? 0 } : { paper, at: sayings(records[id], papers[paper])[0].start_byte };
  };
  const leanModule = (id: string) => records[id].lean[0]?.module ?? "";
  listed.sort((a, b) => {
    if (a === main || b === main) return a === main ? -1 : 1;
    const pa = place(a);
    const pb = place(b);
    if (pa.paper !== pb.paper) return pa.paper - pb.paper;
    if (pa.paper === papers.length) return leanModule(a).localeCompare(leanModule(b)) || pa.at - pb.at;
    return pa.at - pb.at;
  });
  const rows = new Map<string, TableRow>();
  for (const id of listed) {
    const key = levels.map((level) => cellKey(records[id], level)).join("|");
    const row = rows.get(key);
    if (row) row.also.push(id);
    else rows.set(key, { id, also: [] });
  }
  return [...rows.values()];
}

/** The levels a table starts with: the Lean first, then the levels furthest apart, as many as the width holds. */
export function defaultLevels(width: number): Level[] {
  const columns = defaultColumns(width);
  if (columns >= 4) return [...LEVELS];
  return columns === 3 ? ["lean", "short", "expository"] : ["lean", "short"];
}

const IN_WORDS: Record<Level, string> = {
  lean: "the Lean",
  long: "the long record",
  short: "the short paper",
  expository: "the exposition",
};

const COUNT_WORDS = ["", "one", "both", "all three", "all four"];

/** "24 steps appear in both the short paper and the exposition." With `any`, in at least one of them. */
export function rowsSentence(levels: readonly Level[], count: number, any = false): string {
  const steps = `${count} ${count === 1 ? "step" : "steps"}`;
  const lead = count === 1 ? `${steps} appears` : `${steps} appear`;
  if (levels.length === 1) return `${lead} in ${IN_WORDS[levels[0]]}.`;
  if (any) return `${lead} in at least one of these levels.`;
  if (levels.length === 2) return `${lead} in both ${IN_WORDS[levels[0]]} and ${IN_WORDS[levels[1]]}.`;
  return `${lead} at ${COUNT_WORDS[levels.length]} levels.`;
}

/** Where the rows' order comes from, in words. */
export function orderWords(levels: readonly Level[]): string {
  const first = LEVELS.find((level) => levels.includes(level) && isPaper(level));
  return first ? `In the order of ${IN_WORDS[first]}.` : "In the order of the source.";
}

/** A row's height before it is typeset, so the scroll bar is nearly right from the start. */
export function holdHeight(record: RecordAlignment, levels: readonly Level[], columnWidth: number): number {
  const perLine = Math.max(24, columnWidth / 9);
  const cell = (level: Level) => {
    if (level === "lean") return record.lean.length ? 260 : 40;
    const statement = isPaper(level) ? sayings(record, level)[0] : undefined;
    return statement ? Math.ceil(statement.markdown.length / 1.4 / perLine) * 26 + 64 : 40;
  };
  return Math.max(...levels.map(cell));
}
