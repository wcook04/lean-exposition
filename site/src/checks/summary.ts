// Plain-language summaries of the recorded checks. Each kind of check answers
// a different question, so outcomes are never merged across kinds, and a run
// that did not finish is not reported as a verdict on the mathematics.

import type { Edition } from "../app/data";

export interface CheckKindInfo {
  title: string;
  question: string;
}

export const CHECK_KINDS: Record<string, CheckKindInfo> = {
  source_hash: {
    title: "Source files",
    question: "Are the cited files byte-for-byte the ones recorded? This says nothing about their mathematics.",
  },
  lean_build: {
    title: "Lean build",
    question: "Does the Lean project compile with the pinned toolchain?",
  },
  comparator: {
    title: "Comparator",
    question: "Does the Lean proof establish the separately stated challenge, using only the permitted axioms?",
  },
  extraction: {
    title: "Dependency extraction",
    question: "Which declarations does the elaborated Lean proof actually use?",
  },
  semantic_review: {
    title: "Correspondence review",
    question: "Does the recorded statement faithfully say what the paper or source says?",
  },
  platform: {
    title: "Platform label",
    question: "What does an external platform report? This is not a local proof check.",
  },
};

export const STATUS_WORDS: Record<string, string> = {
  passed: "passed",
  failed: "failed",
  unavailable: "unavailable",
  not_run: "not run",
};

export interface CheckRow {
  kind: string;
  title: string;
  tone: "passed" | "failed" | "open";
  outcome: string;
  counts: Record<string, number>;
  ids: string[];
}

export function checkSummary(edition: Edition, evidenceIds: readonly string[]): CheckRow[] {
  const cards = new Map(edition.map.records.evidence.map((e) => [e.id, e]));
  const byKind = new Map<string, { counts: Record<string, number>; ids: string[] }>();
  for (const id of evidenceIds) {
    const card = cards.get(id);
    if (!card) continue;
    const entry = byKind.get(card.kind) ?? { counts: {}, ids: [] };
    entry.counts[card.status] = (entry.counts[card.status] ?? 0) + 1;
    entry.ids.push(id);
    byKind.set(card.kind, entry);
  }
  const order = ["source_hash", "lean_build", "comparator", "extraction", "semantic_review", "platform"];
  const kinds = [...byKind.keys()].sort((a, b) => (order.indexOf(a) + 99) % 99 - (order.indexOf(b) + 99) % 99);
  return kinds.map((kind) => {
    const { counts, ids } = byKind.get(kind)!;
    return { kind, title: CHECK_KINDS[kind]?.title ?? kind.replace(/_/g, " "), ...describe(counts), counts, ids };
  });
}

function describe(counts: Record<string, number>): { tone: CheckRow["tone"]; outcome: string } {
  const passed = counts.passed ?? 0;
  const failed = counts.failed ?? 0;
  const unavailable = counts.unavailable ?? 0;
  const notRun = counts.not_run ?? 0;
  const parts: string[] = [];
  if (failed) parts.push(`${failed} failed`);
  if (unavailable) parts.push(`${unavailable} unavailable`);
  if (notRun) parts.push(`${notRun} not run`);
  if (passed && !failed && !unavailable) {
    return { tone: "passed", outcome: notRun ? `passed (${passed}); ${notRun} not run` : passed > 1 ? `passed (${passed})` : "passed" };
  }
  if (passed) return { tone: "passed", outcome: `${passed} passed; ${parts.join(", ")}` };
  if (failed || unavailable) return { tone: failed ? "failed" : "open", outcome: `no completed run (${parts.join(", ")})` };
  return { tone: "open", outcome: "not run" };
}

// ------------------------------------------------------------ the ledger
// Added for the checks page. Everything below groups or words what the
// evidence records already say; nothing is inferred about the mathematics.

/** The order in which the kinds of check are presented. */
export const CHECK_ORDER = ["source_hash", "lean_build", "comparator", "extraction", "semantic_review", "platform"] as const;

/** Outcome names for a single record, capitalised for a row's lead. */
export const OUTCOME_NAMES: Record<string, string> = {
  passed: "Passed",
  failed: "Failed",
  unavailable: "Unavailable",
  not_run: "Not run",
};

/** What each outcome means, in plain words, for the page's key. */
export const OUTCOME_MEANINGS: { status: string; meaning: string }[] = [
  { status: "passed", meaning: "the program ran and reported success for the inputs it examined." },
  { status: "failed", meaning: "a run was recorded and it ended in failure. The record says where it stopped." },
  { status: "unavailable", meaning: "a run was attempted but no outcome was obtained, for example because the checker never started." },
  { status: "not_run", meaning: "the check is described and planned, but no run of it is recorded." },
];

export interface EvidenceCard {
  id: string;
  kind: string;
  status: string;
  label: string;
  ref: string;
}

export interface KindGroup {
  kind: string;
  title: string;
  question: string;
  cards: EvidenceCard[];
  counts: Record<string, number>;
}

const STATUS_ORDER = ["passed", "failed", "unavailable", "not_run"];

/**
 * Group evidence cards by kind of check, in the page's order. Every known
 * kind appears, even with no records, so an absent kind is stated rather
 * than silently missing; unknown kinds follow in alphabetical order.
 */
export function groupByKind(cards: readonly EvidenceCard[]): KindGroup[] {
  const by = new Map<string, EvidenceCard[]>();
  for (const card of cards) {
    if (!by.has(card.kind)) by.set(card.kind, []);
    by.get(card.kind)!.push(card);
  }
  const known: string[] = [...CHECK_ORDER];
  const extra = [...by.keys()].filter((k) => !known.includes(k)).sort();
  return [...known, ...extra].map((kind) => {
    const list = by.get(kind) ?? [];
    const counts: Record<string, number> = {};
    for (const card of list) counts[card.status] = (counts[card.status] ?? 0) + 1;
    return {
      kind,
      title: CHECK_KINDS[kind]?.title ?? kind.replace(/_/g, " "),
      question: CHECK_KINDS[kind]?.question ?? "",
      cards: list,
      counts,
    };
  });
}

/** "2 failed, 2 unavailable and 4 not run" (known outcomes first, then others). */
export function countsInWords(counts: Record<string, number>): string {
  const keys = [...STATUS_ORDER.filter((s) => counts[s]), ...Object.keys(counts).filter((s) => !STATUS_ORDER.includes(s) && counts[s]).sort()];
  const parts = keys.map((s) => `${counts[s]} ${STATUS_WORDS[s] ?? s.replace(/_/g, " ")}`);
  if (parts.length === 0) return "none";
  if (parts.length === 1) return parts[0];
  return `${parts.slice(0, -1).join(", ")} and ${parts[parts.length - 1]}`;
}

/** "1 record" or "8 records". */
export function recordsWord(n: number): string {
  return `${n} ${n === 1 ? "record" : "records"}`;
}

const MONTHS = ["January", "February", "March", "April", "May", "June", "July", "August", "September", "October", "November", "December"];

export interface StatedDate {
  /** Sortable key, YYYY-MM-DD with the time when the record gives one. */
  key: string;
  /** "23 October 2026". */
  text: string;
}

/**
 * The first calendar date a record's own text states, as an ISO date
 * (2026-10-23, optionally with a time) or as "24 October 2026". Dates in
 * identifiers or file names are deliberately not read.
 */
export function statedDate(details: string | undefined | null): StatedDate | null {
  if (!details) return null;
  const iso = /\b(\d{4})-(\d{2})-(\d{2})(?:T(\d{2}:\d{2}(?::\d{2}(?:\.\d+)?)?))?/.exec(details);
  const named = new RegExp(`\\b(\\d{1,2}) (${MONTHS.join("|")}) (\\d{4})\\b`).exec(details);
  const candidates: { at: number; date: StatedDate }[] = [];
  if (iso) {
    const [, y, m, d, time] = iso;
    const month = Number(m);
    if (month >= 1 && month <= 12 && Number(d) >= 1 && Number(d) <= 31)
      candidates.push({ at: iso.index, date: { key: `${y}-${m}-${d}${time ? `T${time}` : ""}`, text: `${Number(d)} ${MONTHS[month - 1]} ${y}` } });
  }
  if (named) {
    const [, d, month, y] = named;
    const m = String(MONTHS.indexOf(month) + 1).padStart(2, "0");
    candidates.push({ at: named.index, date: { key: `${y}-${m}-${d.padStart(2, "0")}`, text: `${Number(d)} ${month} ${y}` } });
  }
  candidates.sort((a, b) => a.at - b.at);
  return candidates[0]?.date ?? null;
}

/**
 * Split records into those whose text states a date (earliest first; ties
 * keep the given order) and those that state none (given order).
 */
export function inStatedTimeOrder<T extends { details?: string | null }>(records: readonly T[]): { dated: { record: T; date: StatedDate }[]; undated: T[] } {
  const dated: { record: T; date: StatedDate; i: number }[] = [];
  const undated: T[] = [];
  records.forEach((record, i) => {
    const date = statedDate(record.details);
    if (date) dated.push({ record, date, i });
    else undated.push(record);
  });
  dated.sort((a, b) => (a.date.key < b.date.key ? -1 : a.date.key > b.date.key ? 1 : a.i - b.i));
  return { dated: dated.map(({ record, date }) => ({ record, date })), undated };
}

const KIND_NOUNS: Record<string, string> = {
  source_hash: "source-file checks",
  lean_build: "Lean build records",
  comparator: "Comparator records",
  extraction: "dependency extraction records",
  semantic_review: "correspondence reviews",
  platform: "platform records",
};

const KIND_RUN: Record<string, string> = { lean_build: "Lean build", comparator: "Comparator" };

function singular(noun: string): string {
  return noun.replace(/s$/, "");
}

/**
 * One sentence on where a kind of check stands in this edition, from its
 * counts alone. Never says "verified"; a passed source hash is described as
 * byte identity, not as a statement about the mathematics.
 */
export function standingSentence(group: Pick<KindGroup, "kind" | "title" | "counts">): string {
  const total = Object.values(group.counts).reduce((s, n) => s + n, 0);
  const passed = group.counts.passed ?? 0;
  const notRun = group.counts.not_run ?? 0;
  const name = KIND_NOUNS[group.kind] ?? `${group.title.toLowerCase()} records`;
  if (total === 0) return `No ${name} are part of this edition.`;
  if (group.kind === "comparator" && passed === 0)
    return `No completed Comparator acceptance is recorded for this edition. Its ${recordsWord(total)}: ${countsInWords(group.counts)}.`;
  if (passed === total) {
    const lead = total === 1 ? `The one ${singular(name)} passed.` : `All ${total} ${name} passed.`;
    if (group.kind === "source_hash")
      return `${lead} They show that the named files are byte-for-byte the recorded ones; they say nothing about whether the mathematics in them is correct.`;
    return lead;
  }
  if (passed === 0 && notRun === total)
    return total === 1 ? `The one ${singular(name)} has not been run.` : `None of the ${total} ${name} has been run.`;
  if (passed === 0) return `No ${KIND_RUN[group.kind] ?? group.title.toLowerCase()} run has passed. Its ${recordsWord(total)}: ${countsInWords(group.counts)}.`;
  return `${passed} of ${recordsWord(total)} passed. All of them: ${countsInWords(group.counts)}.`;
}
