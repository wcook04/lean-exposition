// The levels of the argument: Lean, the long record, the short paper and the
// exposition. Each paper uses part of one global graph, so a level is a set of
// records and the map's lens is that set. The sets are not strictly nested: the
// exposition uses records the short paper does not, so nothing here or on the
// page may say one level contains another.

import type { PaperStructure, Stage } from "../api/types";
import type { ArgGraph, ArgNode } from "../model/graph";
import { ACCOUNT_IN_PROSE } from "../app/papers";
import type { Alignment } from "../api/lean";
import { passageRecords, sectionTitleIn } from "../reader/page/model";
import { recordLine } from "../compare/useAlignment";

/** The lens order, widest first, as the header lists it. */
export const LENS_ORDER: Stage[] = ["long", "short", "expository"];

/** A record a paper's own passages discuss. Every paper also lists what those records rest on, so membership alone is not enough. */
export function inLevel(node: ArgNode, stage: Stage): boolean {
  return !!node.papers[stage]?.roles.some((r) => r.startsWith("mapped_"));
}

export function levelRecords(graph: ArgGraph, stage: Stage): Set<string> {
  return new Set(graph.order.filter((id) => inLevel(graph.nodes.get(id)!, stage)));
}

export interface LevelCounts {
  all: number;
  total: number;
  long: number;
  short: number;
  expository: number;
}

/** How many records of this argument each level uses, computed from the data. */
export function levelCounts(graph: ArgGraph, argument: ReadonlySet<string>): LevelCounts {
  const counts: LevelCounts = { all: argument.size, total: graph.nodes.size, long: 0, short: 0, expository: 0 };
  for (const id of argument) {
    const node = graph.nodes.get(id);
    if (!node) continue;
    for (const stage of LENS_ORDER) if (inLevel(node, stage)) counts[stage]++;
  }
  return counts;
}

/** The one line under the header. */
export function lensSentence(counts: LevelCounts, lens: Stage | undefined): string {
  if (!lens) return `This argument uses ${counts.all} of the ${counts.total} records on this site.`;
  const name = ACCOUNT_IN_PROSE[lens];
  return `${name.charAt(0).toUpperCase()}${name.slice(1)} uses ${counts[lens]} of the ${counts.all} records in this argument.`;
}

/** How many distinct declarations this argument links, and how many of them each level's records link. */
export function leanLevelCounts(graph: ArgGraph, argument: ReadonlySet<string>, alignment: Pick<Alignment, "records">): Pick<LevelCounts, "all" | Stage> {
  const names = (keep: (id: string) => boolean) => {
    const set = new Set<string>();
    for (const id of argument) if (keep(id)) for (const row of alignment.records[id]?.lean ?? []) set.add(row.name);
    return set.size;
  };
  const at = (stage: Stage) => names((id) => inLevel(graph.nodes.get(id)!, stage));
  return { all: names(() => true), long: at("long"), short: at("short"), expository: at("expository") };
}

export function leanSentence(counts: Pick<LevelCounts, "all" | Stage>, lens: Stage): string {
  const name = ACCOUNT_IN_PROSE[lens];
  return `The records ${name} uses link ${counts[lens]} of this argument's ${counts.all} Lean declarations.`;
}

/** Whether Lean has declarations linked to this record: a declaration, or a record the alignment links. */
export function hasLean(id: string, node?: ArgNode): boolean {
  return (recordLine(id)?.lean ?? 0) > 0 || node?.kind === "declaration";
}

export interface WalkPassage {
  anchor: string;
  /** "§5.3 Strict curvature creates an impossible integral". */
  place: string;
  /** "§5.3"; empty for a passage outside the numbered sections. */
  mark: string;
  records: string[];
}

function plainAnchor(anchor: string): string {
  const words = anchor.replace(/-/g, " ");
  return words.charAt(0).toUpperCase() + words.slice(1);
}

/** A paper's passages about this argument, in reading order. */
export function walkPassages(structure: PaperStructure, argument: ReadonlySet<string>): WalkPassage[] {
  const out: WalkPassage[] = [];
  const passages = [...structure.paper.passages].sort((a, b) => a.block_span.start_byte - b.block_span.start_byte);
  for (const p of passages) {
    const records = passageRecords(p).filter((id) => argument.has(id));
    if (!records.length) continue;
    const title = sectionTitleIn(structure, p.anchor);
    const number = title?.match(/^(\d+(?:\.\d+)*)\.?\s+(.*)$/);
    const place = number ? `§${number[1]} ${number[2]}` : (title ?? plainAnchor(p.anchor));
    out.push({ anchor: p.anchor, place, mark: number ? `§${number[1]}` : "", records });
  }
  return out;
}

/** The section where a paper first discusses each record. */
export function firstSections(passages: readonly WalkPassage[]): Map<string, string> {
  const out = new Map<string, string>();
  for (const p of passages) if (p.mark) for (const id of p.records) if (!out.has(id)) out.set(id, p.mark);
  return out;
}
