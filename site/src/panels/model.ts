// Pure helpers behind the record panel: the wording it adds around the
// record, the collapsed path from the goal, and how an account relates to a
// result when it has no passage of its own. Nothing here invents a fact; each
// sentence restates a field the API serves.

import type { AlignedPassage, Stage } from "../api/types";
import { PAPER_NAMES, STAGE_ORDER } from "../app/papers";
import { closure, type ArgGraph } from "../model/graph";

/** What a passage does with the record, by its authored treatment kinds. */
export const TREATMENT_WORDS: Record<string, string> = {
  statement: "states it",
  derivation: "derives it",
  explanation: "explains it",
  application: "applies it",
  illustration: "illustrates it",
  reference: "points to it",
};

/** The account name in running text: "the short paper". */
export function accountName(stage: Stage): string {
  return `the ${PAPER_NAMES[stage].short.toLowerCase()}`;
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
 * Which account to show: the reader's last choice, then the map's lens, then
 * the first account that has a passage, then the first account.
 */
export function defaultAccount(counts: Partial<Record<Stage, number>>, chosen: Stage | null, lens?: Stage): Stage {
  if (chosen) return chosen;
  if (lens) return lens;
  return STAGE_ORDER.find((s) => (counts[s] ?? 0) > 0) ?? STAGE_ORDER[0];
}

/**
 * One line saying how an account relates to a result it has no passage for,
 * from the account's recorded roles for it. An empty role list means the
 * account's argument does not include the result.
 */
export function relationLine(stage: Stage, roles: readonly string[] | undefined, unused = false): string {
  const name = accountName(stage);
  const Name = name[0].toUpperCase() + name.slice(1);
  if (!roles || roles.length === 0)
    return unused ? `Not in ${name}. No result ${name} proves uses it.` : `Not part of ${name}'s argument.`;
  if (roles.includes("recorded_prerequisite") && !roles.includes("mapped_claim") && !roles.includes("mapped_assumption"))
    return `${Name} relies on it without a passage of its own.`;
  if (roles.includes("mapped_assumption")) return `${Name} lists it as an assumption, without a passage of its own.`;
  return `${Name} includes it in its argument, without a passage of its own.`;
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

/** The status of a record in words. */
export function statusWords(status: string, kind: string): string {
  const words: Record<string, string> = {
    unverified: kind === "declaration" ? "Recorded; no completed proof check in this edition" : "Recorded from the sources; not independently checked",
    open: "Open: the record marks this as not yet established",
    kernel_checked: "Checked by the Lean kernel",
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

/** "Selected: <label>, <kind>." for the polite live region. */
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

/** The first sentence of a recorded text, for a one-line gist. */
export function firstSentence(text: string): string {
  const m = text.match(/^[\s\S]*?[.!?](?=\s+[A-Z(]|$)/);
  return (m ? m[0] : text).trim();
}

/** How a step reads, from the prerequisite to the consumer. */
export function stepVerb(kind: string): string {
  if (kind === "assumes") return "is assumed by";
  if (kind === "formalizes") return "states in Lean";
  return "helps prove";
}

/** One honest sentence on a warrant's review state, adapted to how it was recorded. */
export function warrantStatus(status: string, tool: string): string {
  const located = /source-located|inspected source|source comparison|proof inspection/i.test(tool);
  const how = located ? "Located in the sources by the authors" : "Recorded by the authors";
  if (status === "passed") return `${how}; independently reviewed.`;
  if (status === "failed") return `${how}; an independent review did not accept it.`;
  if (status === "unavailable") return `${how}; an independent review gave no outcome.`;
  return `${how}; not independently reviewed.`;
}
