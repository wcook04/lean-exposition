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
    question: "Whether each cited file still has exactly the bytes recorded for it, compared by hash. It does not read the mathematics in the files.",
  },
  lean_build: {
    title: "Lean build",
    question: "Whether the Lean project compiles with the Lean version recorded for it.",
  },
  comparator: {
    title: "Comparator",
    question: "Whether Comparator, a program that compares a Lean proof with a separately written statement of the theorem, accepts the proof as proving that statement using only the permitted axioms.",
  },
  extraction: {
    title: "Dependency extraction",
    question: "Which Lean declarations the proof uses, as listed by Lean after it has processed the proof.",
  },
  semantic_review: {
    title: "Correspondence review",
    question: "Whether a second reader, comparing a recorded step with the paper or source it was taken from, finds that they say the same thing.",
  },
  platform: {
    title: "Platform label",
    question: "What an outside platform reports about a statement. This is that platform’s label, not a proof check run for these records.",
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
  /** "passed" only when something passed and nothing failed or was unavailable. */
  tone: "passed" | "failed" | "open";
  outcome: string;
  /** The kind's one-line headline (see kindHeadline). */
  headline: string;
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
    return { kind, title: CHECK_KINDS[kind]?.title ?? kind.replace(/_/g, " "), ...describe(counts), headline: kindHeadline(kind, counts), counts, ids };
  });
}

// Each outcome is named separately: a failed run and an unavailable one are
// recorded events, not the absence of a run, and neither is merged with "not run".
function describe(counts: Record<string, number>): { tone: CheckRow["tone"]; outcome: string } {
  const passed = counts.passed ?? 0;
  const failed = counts.failed ?? 0;
  const unavailable = counts.unavailable ?? 0;
  const notRun = counts.not_run ?? 0;
  const others = countsInWords(withoutPassed(counts));
  const tone: CheckRow["tone"] = failed ? "failed" : passed && !unavailable ? "passed" : "open";
  if (passed && !failed && !unavailable && !notRun && others === "none") return { tone, outcome: passed > 1 ? `passed (${passed})` : "passed" };
  if (passed) return { tone, outcome: `${passed} passed; ${others}` };
  if (failed || unavailable) return { tone, outcome: `none passed: ${others}` };
  if (notRun && others === `${notRun} not run`) return { tone, outcome: notRun > 1 ? `not run (${notRun})` : "not run" };
  return { tone, outcome: others };
}

function withoutPassed(counts: Record<string, number>): Record<string, number> {
  const { passed: _passed, ...rest } = counts;
  return rest;
}

// --------------------------------------------------------- outcome summaries

/** Records of any shape that name their check kind and outcome. */
export interface OutcomeRecord {
  kind: string;
  status: string;
}

/**
 * Outcome counts per kind of check, kinds in the page's order (unknown kinds
 * last, alphabetically). Every status is counted under its own name; nothing
 * is merged.
 */
export function outcomeCounts(records: readonly OutcomeRecord[]): Map<string, Record<string, number>> {
  const by = new Map<string, Record<string, number>>();
  for (const r of records) {
    const counts = by.get(r.kind) ?? {};
    counts[r.status] = (counts[r.status] ?? 0) + 1;
    by.set(r.kind, counts);
  }
  const known: string[] = [...CHECK_ORDER];
  const kinds = [...known.filter((k) => by.has(k)), ...[...by.keys()].filter((k) => !known.includes(k)).sort()];
  return new Map(kinds.map((k) => [k, by.get(k)!]));
}

/** Names for a kind in a headline: what a passed record of that kind shows. */
const HEADLINE_NAMES: Record<string, string> = {
  source_hash: "Source file hashes",
  lean_build: "Lean build",
  comparator: "Comparator",
  extraction: "Dependency extraction",
  semantic_review: "Correspondence review",
  platform: "Platform label",
};

function headlineName(kind: string): string {
  return HEADLINE_NAMES[kind] ?? CHECK_KINDS[kind]?.title ?? kind.replace(/_/g, " ");
}

/** The name inside a sentence: lower case, except the names Comparator and Lean. */
function inSentence(name: string): string {
  return /^(Comparator|Lean)\b/.test(name) ? name : name.charAt(0).toLowerCase() + name.slice(1);
}

function outcomeParts(counts: Record<string, number>): string[] {
  const keys = [...STATUS_ORDER.filter((s) => counts[s]), ...Object.keys(counts).filter((s) => !STATUS_ORDER.includes(s) && counts[s]).sort()];
  return keys.map((s) => `${counts[s]} ${STATUS_WORDS[s] ?? s.replace(/_/g, " ")}`);
}

/**
 * The lead of a kind's line: its name when something passed, otherwise what
 * is missing. It never says a run is missing when a failed or unavailable run
 * is recorded.
 */
export function kindLead(kind: string, counts: Record<string, number>): string {
  const name = headlineName(kind);
  if (outcomeParts(counts).length === 0) return `No ${inSentence(name)} records`;
  const passed = counts.passed ?? 0;
  const recordedRun = passed + (counts.failed ?? 0) + (counts.unavailable ?? 0);
  if (kind === "extraction" && !passed) {
    return recordedRun ? "No successful extraction projection is recorded for this graph" : "No extraction projection run is recorded for this graph";
  }
  return passed ? name : recordedRun ? `No successful ${inSentence(name)} result is recorded` : `No ${inSentence(name)} run is recorded`;
}

/**
 * One line for a kind of check, every outcome kept apart:
 * "No successful Comparator result is recorded (1 failed, 2 unavailable and 2 not run)",
 * "No Lean build run is recorded (2 not run)", "Source file hashes (2 passed)".
 * It never calls a pass independent.
 */
export function kindHeadline(kind: string, counts: Record<string, number>): string {
  const lead = kindLead(kind, counts);
  if (outcomeParts(counts).length === 0) return lead;
  return `${lead} (${countsInWords(counts)})`;
}

/** "View 12 check records" style count, and the line the theorem plate shows. */
export interface GoalCheckLine {
  line: string;
  total: number;
}

// The kinds that bear on a Lean statement, most informative first: Comparator
// is the check that the proof establishes the stated challenge.
const PLATE_ORDER = ["comparator", "lean_build", "extraction", "semantic_review", "platform", "source_hash"];

/**
 * The most informative short line about a record's checks, for the theorem
 * plate, with the number of check records attached. `evidenceIds` defaults to
 * the ids on the node's own record (ArgNode.evidenceIds).
 * E.g. { line: "No Comparator acceptance recorded", total: 12 }.
 */
export function goalCheckLine(edition: Edition, nodeId: string, evidenceIds?: readonly string[]): GoalCheckLine {
  const ids = evidenceIds ?? edition.graph.nodes.get(nodeId)?.evidenceIds ?? [];
  const cards = new Map(edition.map.records.evidence.map((e) => [e.id, e]));
  const records = ids.map((id) => cards.get(id)).filter((c): c is NonNullable<typeof c> => !!c);
  const total = records.length;
  if (total === 0) return { line: "No check records", total };
  const by = outcomeCounts(records);
  const kind = PLATE_ORDER.find((k) => by.has(k)) ?? [...by.keys()][0];
  const counts = by.get(kind)!;
  const passed = counts.passed ?? 0;
  if (kind === "comparator") return { line: passed ? `Comparator passed (${passed} of ${recordsWord(sum(counts))})` : "No successful Comparator result recorded", total };
  if (kind === "source_hash") return { line: passed === sum(counts) ? "Source files match their recorded hashes" : kindHeadline(kind, counts), total };
  if (passed) return { line: `${headlineName(kind)} passed (${passed} of ${recordsWord(sum(counts))})`, total };
  const recordedRun = (counts.failed ?? 0) + (counts.unavailable ?? 0);
  return { line: recordedRun ? `No successful ${inSentence(headlineName(kind))} result recorded` : `No ${inSentence(headlineName(kind))} run recorded`, total };
}

function sum(counts: Record<string, number>): number {
  return Object.values(counts).reduce((s, n) => s + n, 0);
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
  { status: "passed", meaning: "The checking program ran and reported success on the inputs it examined." },
  { status: "failed", meaning: "A run is recorded and it ended in failure. Where it stopped is written in the check record." },
  { status: "unavailable", meaning: "A run was attempted but produced no outcome, for example because the checking program never started." },
  { status: "not_run", meaning: "The check is described and planned, but no run of it is recorded." },
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

/** Plain words for the recorded failures: what stopped, in the record's own terms. */
const FAILURE_WORDS: Record<string, string> = {
  full_support_solution_build_failure_20261023:
    "Comparator stopped while building the proof of the Full support theorem, because a compiled file the proof imports (AbsIncrement) was missing.",
  scalar_value_solution_build_failure_20261024:
    "Comparator stopped while building the proof of the scalar value theorem, because a compiled file the proof imports (IntegralPositiveMulGaussian) was missing.",
};

/** The date a record carries at the end of its identifier, read only for a dated failure. */
export function identifierDate(id: string): string | null {
  const m = /_(\d{4})(\d{2})(\d{2})$/.exec(id);
  return m ? statedDate(`${m[1]}-${m[2]}-${m[3]}`)?.text ?? null : null;
}

/** One sentence on a recorded failure: when, then what happened, in plain words or the record's own. */
export function failureLine(card: Pick<EvidenceCard, "id" | "label">, record?: { details?: string; tool?: string }): string {
  const date = statedDate(record?.details)?.text ?? identifierDate(card.id);
  const what = FAILURE_WORDS[card.id] ?? record?.details ?? record?.tool ?? card.label;
  return date ? `${date}. ${what}` : what;
}

/** "1 check record" or "8 check records". */
export function recordsWord(n: number): string {
  return `${n} ${n === 1 ? "check record" : "check records"}`;
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
  if (total === 0) return `No ${name} are recorded.`;
  if (group.kind === "comparator" && passed === 0)
    return `No successful Comparator result is recorded. The outcomes of its ${recordsWord(total)} are ${countsInWords(group.counts)}.`;
  if (passed === total) {
    const lead = total === 1 ? `The one ${singular(name)} passed.` : `All ${total} ${name} passed.`;
    if (group.kind === "source_hash")
      return `${lead} In each, the SHA-256 hash and length of a named file matched the values recorded for it, so the file has the recorded bytes. These checks do not examine whether the mathematics in the files is correct.`;
    return lead;
  }
  if (passed === 0 && notRun === total)
    return total === 1 ? `The one ${singular(name)} has not been run.` : `None of the ${total} ${name} has been run.`;
  if (passed === 0) return `No ${KIND_RUN[group.kind] ?? group.title.toLowerCase()} run has passed. The outcomes of its ${recordsWord(total)} are ${countsInWords(group.counts)}.`;
  return `${passed} of ${recordsWord(total)} passed. The outcomes of all ${total} are ${countsInWords(group.counts)}.`;
}
