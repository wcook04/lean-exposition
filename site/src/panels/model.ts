// Pure helpers behind the record and step panels: the wording they add around
// a record, the route from the goal, how an account relates to a result, the
// view of an applied theorem and the words for recorded check outcomes.
// Nothing here invents a fact; each sentence restates a field the API serves.
// DESIGN.md § Wording is the reference for every phrase.

import type { AlignedPassage, Stage } from "../api/types";
import { PAPER_NAMES, STAGE_ORDER } from "../app/papers";
import { closure, type ArgGraph, type LinkKind } from "../model/graph";

/** What a passage does with the record, by its authored treatment kinds. */
export const TREATMENT_WORDS: Record<string, string> = {
  statement: "states it",
  derivation: "derives it",
  explanation: "explains it",
  application: "applies it",
  illustration: "illustrates it",
  reference: "refers to it",
};

/** The account name in running text: "the short paper". */
export function accountName(stage: Stage): string {
  return `the ${PAPER_NAMES[stage].short.toLowerCase()}`;
}

/** A record's kind as one word group, set in small capitals (DESIGN.md § Principles). */
export function kindWord(kind: string): string {
  switch (kind) {
    case "goal":
      return "Main result";
    case "declaration":
      return "Lean declaration";
    case "assumption":
      return "Assumption";
    default:
      return "Claim";
  }
}

/**
 * A long path keeps its first item and its last two, with a gap marker
 * between. Short paths are returned whole. `null` marks the gap.
 */
export function collapsePath<T>(items: readonly T[], max = 4): (T | null)[] {
  if (items.length <= max) return [...items];
  return [items[0], null, ...items.slice(-2)];
}

/** Passages grouped by account, in account order, keeping the API's order within each. */
export function groupPassages(passages: readonly AlignedPassage[]): Map<Stage, AlignedPassage[]> {
  const out = new Map<Stage, AlignedPassage[]>();
  for (const stage of STAGE_ORDER) out.set(stage, []);
  const seen = new Set<string>();
  for (const p of passages) {
    const key = `${p.stage}:${p.anchor}`;
    if (seen.has(key) || !out.has(p.stage)) continue;
    seen.add(key);
    out.get(p.stage)!.push(p);
  }
  return out;
}

/**
 * Related reading for a step, chosen separately in each account. A passage
 * mapped to both endpoints is not evidence that it proves their relationship.
 */
export function stepPassages(consumer: readonly AlignedPassage[], prerequisite: readonly AlignedPassage[]): {
  grouped: Map<Stage, AlignedPassage[]>;
  basis: Map<Stage, "both" | "consumer" | "none">;
} {
  const own = groupPassages(consumer);
  const theirs = new Set(prerequisite.map((p) => `${p.stage}:${p.anchor}`));
  const grouped = new Map<Stage, AlignedPassage[]>();
  const basis = new Map<Stage, "both" | "consumer" | "none">();
  for (const stage of STAGE_ORDER) {
    const passages = own.get(stage)!;
    const shared = passages.filter((p) => theirs.has(`${stage}:${p.anchor}`));
    grouped.set(stage, shared.length ? shared : passages);
    basis.set(stage, shared.length ? "both" : passages.length ? "consumer" : "none");
  }
  return { grouped, basis };
}

/** The label above a step's related passages in one account. */
export function stepBasisLabel(basis: "both" | "consumer" | "none" | undefined): string | null {
  if (basis === "both") return "Both records linked";
  if (basis === "consumer") return "Linked to the conclusion only";
  return null;
}

/**
 * Which account to show: the reader's last choice, then the map's lens, then
 * the first account that has a passage, then the first account.
 */
export function defaultAccount(counts: Partial<Record<Stage, number>>, chosen: Stage | null, lens?: Stage): Stage {
  if (chosen) return chosen;
  if (lens) return lens;
  return STAGE_ORDER.find((s) => (counts[s] ?? 0) > 0) ?? STAGE_ORDER[0];
}

// --------------------------------------------------------- account states

/** The state of one account's explanation for a record, in the order the panel resolves it. */
export type AccountState =
  | { kind: "loading" }
  | { kind: "error" }
  | { kind: "direct"; count: number }
  | { kind: "used" }
  | { kind: "outside" };

/**
 * Resolve one account's state. A pending or failed request is never reported
 * as an absence: "used" and "outside" need a successful response.
 */
export function accountState(request: "loading" | "error" | "ready", count: number, roles: readonly string[] | undefined): AccountState {
  if (request === "loading") return { kind: "loading" };
  if (request === "error") return { kind: "error" };
  if (count > 0) return { kind: "direct", count };
  if (roles && roles.length > 0) return { kind: "used" };
  return { kind: "outside" };
}

/** The line under the account tabs for a state (DESIGN.md § Wording). */
export function accountStateLine(state: AccountState): string {
  switch (state.kind) {
    case "loading":
      return "Loading passages…";
    case "error":
      return "The linked passages could not be loaded.";
    case "direct":
      return state.count === 1 ? "1 passage is linked directly to this record" : `${state.count} passages are linked directly to this record`;
    case "used":
      return "No passage is linked directly to this record. These passages are linked to results that use it.";
    case "outside":
      return "No passage in this account is linked to this record, and the recorded argument for the account’s main results does not use it.";
  }
}

/**
 * One line saying how an account relates to a result it has no passage for.
 * Kept for callers that need a sentence rather than a state.
 */
export function relationLine(_stage: Stage, roles: readonly string[] | undefined): string {
  return accountStateLine(accountState("ready", 0, roles)).replace(/ These passages are linked to results that use it\.$/, "");
}

/** What a passage does with this record: its treatments for the record, else how it is mapped. */
export function treatmentWords(
  treatments: readonly { claim_id: string; kinds: string[] }[] | undefined,
  nodeId: string,
  mappingField?: string,
): string[] {
  const own = (treatments ?? []).filter((t) => t.claim_id === nodeId).flatMap((t) => t.kinds);
  const words = [...new Set(own)].map((k) => TREATMENT_WORDS[k] ?? k.replace(/_/g, " "));
  if (words.length === 0 && mappingField === "assumption_ids") return ["lists it as an assumption"];
  return words;
}

/** The status of a record in a few words, for the identity row. */
export function statusWords(status: string, kind: string): string {
  if (kind === "declaration" && status === "unverified") return "No completed Lean proof check is recorded for this declaration.";
  const words: Record<string, string> = {
    unverified: "Not independently checked",
    open: "Unresolved",
    kernel_checked: "Accepted by the Lean kernel",
    conditional: "Conditional on its stated assumptions",
    external: "Imported from an external source",
    axiom: "An axiom",
  };
  return words[status] ?? status.replace(/_/g, " ");
}

/** A revision shortened for display: a 40-hex commit to 7 characters, a content hash to 12. */
export function shortRevision(revision: string | undefined | null): string | null {
  if (!revision) return null;
  if (/^[0-9a-f]{40}$/i.test(revision)) return revision.slice(0, 7);
  const hash = revision.match(/^sha256:([0-9a-f]{12})[0-9a-f]*$/i);
  if (hash) return `sha256:${hash[1]}`;
  return revision;
}

/** Only web links are offered as links; content addresses (urn:) are not. */
export function webUrl(url: string | undefined | null): string | null {
  return url && /^https?:\/\//.test(url) ? url : null;
}

/** "Selected claim: <label>." for the polite live region. */
export function announcement(label: string, kind: string): string {
  return `Selected ${kind.toLowerCase()}: ${label}.`;
}

/** True when no result in `goals` rests on `id`: its consumers never reach them. */
export function unusedBy(graph: ArgGraph, id: string, goals: readonly string[]): boolean {
  const consumers = closure(graph, id, "consumers");
  return !goals.some((g) => consumers.has(g));
}

export interface Coverage {
  own: string[]; // a passage of its own
  relied: string[]; // in the account's argument without a passage of its own
  out: string[]; // outside the account's selection
}

/** How an account covers the records, from each record's recorded membership. */
export function coverageOf(graph: ArgGraph, stage: Stage): Coverage {
  const c: Coverage = { own: [], relied: [], out: [] };
  for (const id of graph.order) {
    const m = graph.nodes.get(id)!.papers[stage];
    if (!m) c.out.push(id);
    else if (m.direct > 0) c.own.push(id);
    else c.relied.push(id);
  }
  return c;
}

/** The coverage words for each role, with the denominator they share. */
export const COVERAGE_WORDS: Record<keyof Coverage, string> = {
  own: "with a passage",
  relied: "used without a passage",
  out: "not used",
};

export function coverageScope(total: number): string {
  return `Across all ${total} records`;
}

/** The first sentence of a recorded text, for a one-line gist. */
export function firstSentence(text: string): string {
  const m = text.match(/^[\s\S]*?[.!?](?=\s+[A-Z(]|$)/);
  return (m ? m[0] : text).trim();
}

// ---------------------------------------------------------------- relations

/** A relation's name in the interface (DESIGN.md § Relations). */
export function relationName(kind: LinkKind | string): string {
  if (kind === "assumes") return "Explicit assumption";
  if (kind === "formalizes") return "Recorded Lean correspondence";
  return "Recorded support";
}

/** The verb joining a step's consumer to its prerequisite: "<consumer> uses <prerequisite>". */
export function stepVerb(kind: string): string {
  if (kind === "assumes") return "assumes";
  if (kind === "formalizes") return "corresponds in Lean to";
  return "uses";
}

/**
 * One honest line on a warrant's review state. A passed review record does
 * not say who reviewed it, so it is never called independent.
 */
export function warrantStatus(status: string): string {
  if (status === "passed") return "An explanation is recorded, and a review of it is recorded as passed";
  if (status === "failed") return "An explanation is recorded, and a review of it is recorded as failed";
  if (status === "unavailable") return "An explanation is recorded; a review of it was attempted but gave no outcome";
  return "An explanation is recorded, but no independent review of it has been run";
}

/**
 * The route from the goal to the record, shown whole when short. A longer
 * route keeps its first item and its last two; the middle opens on request.
 */
export function routeView<T>(ids: readonly T[], open: boolean): { items: T[]; hidden: number; hiddenAt: number } {
  if (open || ids.length <= 4) return { items: [...ids], hidden: 0, hiddenAt: -1 };
  return { items: [ids[0], ...ids.slice(-2)], hidden: ids.length - 3, hiddenAt: 1 };
}

// -------------------------------------------------------- applied theorems

export interface SourceSpan {
  sourceId: string;
  startLine: number | null;
  endLine: number | null;
}

export interface ApplicationView {
  /** "No program has checked this authored application of the theorem" */
  status: string;
  shared: { name: string; value: string }[];
  premises: { premise: string; names: string[]; rationale: string; supplier: string }[];
  remaining: string[];
  rationale: string | null;
  span: SourceSpan | null;
}

interface RawApplication {
  rationale?: string | null;
  bindings?: { assumption: string; names: string[]; rationale: string; supplier: string }[];
  remaining?: string[];
  shared?: unknown;
  status?: string | null;
  sourceSpan?: unknown;
  // The stored record's own spelling, accepted as a fallback.
  premise_bindings?: { assumption_id: string; binding_names?: string[]; rationale?: string; supplier_id: string }[];
  remaining_assumption_ids?: string[];
  shared_bindings?: unknown;
  source_span?: unknown;
}

/** Shared bindings as name/value rows, whether recorded as a map or a list. */
export function sharedObjects(raw: unknown): { name: string; value: string }[] {
  if (!raw) return [];
  if (Array.isArray(raw)) {
    return raw
      .map((r) => {
        const o = r as Record<string, unknown>;
        const name = String(o.name ?? o.binding ?? o.variable ?? "");
        const value = String(o.value ?? o.description ?? o.object ?? "");
        return { name, value };
      })
      .filter((r) => r.name);
  }
  if (typeof raw === "object") return Object.entries(raw as Record<string, unknown>).map(([name, value]) => ({ name, value: String(value) }));
  return [];
}

function sourceSpan(raw: unknown): SourceSpan | null {
  if (!raw || typeof raw !== "object") return null;
  const o = raw as Record<string, unknown>;
  const sourceId = String(o.sourceId ?? o.source_id ?? "");
  if (!sourceId) return null;
  const n = (v: unknown) => (typeof v === "number" ? v : null);
  return { sourceId, startLine: n(o.startLine ?? o.start_line), endLine: n(o.endLine ?? o.end_line) };
}

/** "authored" → "… this authored application …"; the status is the record's, never upgraded. */
function applicationStatus(status: string | null | undefined): string {
  const word = status ? status.replace(/_/g, " ") : "authored";
  return `No program has checked this ${word} application of the theorem`;
}

/**
 * The binding-first view of one applied theorem: the objects held fixed, each
 * premise with its recorded supplier, and what remains assumed. Accepts the
 * site model's application or the stored record's; the two may be merged.
 */
export function applicationView(...sources: (RawApplication | null | undefined)[]): ApplicationView | null {
  const present = sources.filter((s): s is RawApplication => !!s);
  if (!present.length) return null;
  const pick = <K>(f: (s: RawApplication) => K | undefined | null): K | undefined => {
    for (const s of present) {
      const v = f(s);
      if (v !== undefined && v !== null) return v;
    }
    return undefined;
  };
  const premises =
    pick((s) => s.bindings?.map((b) => ({ premise: b.assumption, names: b.names, rationale: b.rationale, supplier: b.supplier }))) ??
    pick((s) =>
      s.premise_bindings?.map((b) => ({ premise: b.assumption_id, names: b.binding_names ?? [], rationale: b.rationale ?? "", supplier: b.supplier_id })),
    ) ??
    [];
  return {
    status: applicationStatus(pick((s) => s.status)),
    shared: sharedObjects(pick((s) => s.shared) ?? pick((s) => s.shared_bindings)),
    premises,
    remaining: pick((s) => s.remaining) ?? pick((s) => s.remaining_assumption_ids) ?? [],
    rationale: pick((s) => s.rationale) ?? null,
    span: sourceSpan(pick((s) => s.sourceSpan) ?? pick((s) => s.source_span)),
  };
}

export const NO_REMAINING = "No remaining assumption is listed for this application";

// ------------------------------------------------------------------ checks

const OUTCOME_ORDER = ["passed", "failed", "unavailable", "not_run"];
const OUTCOME_WORD: Record<string, string> = { passed: "passed", failed: "failed", unavailable: "unavailable", not_run: "not run" };

/** Each recorded outcome of one kind of check, in a fixed order, with its count. */
export function outcomeParts(counts: Record<string, number>): { status: string; word: string; n: number }[] {
  const keys = [...OUTCOME_ORDER.filter((s) => counts[s]), ...Object.keys(counts).filter((s) => !OUTCOME_ORDER.includes(s) && counts[s]).sort()];
  return keys.map((status) => ({ status, word: OUTCOME_WORD[status] ?? status.replace(/_/g, " "), n: counts[status] }));
}

// ---------------------------------------------------------------- excerpts

export interface ExcerptBlock {
  /** "p", "math", "figure", "list", "heading" or "other". */
  role: string;
  height: number;
  /** The block's text ends by introducing what follows (":"). */
  leads?: boolean;
  /** The block's text starts mid-sentence (a qualifying clause after a formula). */
  continues?: boolean;
}

/**
 * How many leading blocks make a complete preview within `budget` pixels.
 * Blocks are never cut: at least one is shown whole; a display formula keeps
 * the sentence that introduces it and the clause that qualifies it.
 */
export function excerptLength(blocks: readonly ExcerptBlock[], budget = 300): number {
  if (blocks.length === 0) return 0;
  let n = 0;
  let used = 0;
  while (n < blocks.length && (n === 0 || used + blocks[n].height <= budget)) used += blocks[n++].height;
  // Pairing: a heading takes what it heads; an introducing sentence takes its
  // formula or list; a formula takes the clause that qualifies it.
  while (n < blocks.length) {
    const last = blocks[n - 1];
    const next = blocks[n];
    if (last.role === "heading") n++;
    else if (last.leads && (next.role === "math" || next.role === "list")) n++;
    else if (last.role === "math" && (next.continues || next.role === "math")) n++;
    else break;
  }
  return n;
}
