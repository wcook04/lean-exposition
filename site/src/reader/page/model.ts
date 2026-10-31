// Pure helpers for the reader page: how a passage, a section, a route and a
// reading position are named and found. Nothing here touches the DOM or the
// network, so the rules are tested directly against the captured fixtures.

import type { AlignedStatement, Alignment, StatementRole } from "../../api/lean";
import type { PaperStructure, Stage, StructurePassage } from "../../api/types";
import type { PreparedDocument, PreparedPart } from "../engine";
import { readerHref } from "../links";
import { tieCounts, type TieCount, type TieModel } from "../ties";
import { PAPER_NAMES, STAGE_ORDER } from "../../app/papers";
import { sectionLabel } from "../../map/TheoremPlate";

export type Structures = Partial<Record<Stage, PaperStructure>>;

const STAGES = new Set<string>(["long", "short", "expository"]);

/** `…/papers/long.json/passages/curvature` -> { stage: "long", anchor: "curvature" }. */
export function parsePassageRef(ref: string): { stage: Stage; anchor: string } | null {
  const match = ref.match(/papers\/([a-z]+)\.json\/passages\/(.+)$/);
  if (!match || !STAGES.has(match[1])) return null;
  return { stage: match[1] as Stage, anchor: match[2] };
}

export function nodeIdOfRef(ref: string): string {
  const at = ref.lastIndexOf("/nodes/");
  return at < 0 ? ref : ref.slice(at + "/nodes/".length);
}

export function passageOf(structure: PaperStructure | undefined, anchor: string): StructurePassage | undefined {
  return structure?.paper.passages.find((p) => p.anchor === anchor);
}

/** The recorded claims and assumptions a passage maps, claims first, without repeats. */
export function passageRecords(passage: StructurePassage | undefined): string[] {
  if (!passage) return [];
  return [...new Set([...passage.claim_ids, ...passage.assumption_ids])];
}

/**
 * The heading a reader lands on for a passage: the first heading inside the
 * passage when it opens with one, otherwise the section containing it. The
 * document title is never used. Mirrors documents.ts#sectionTitleOf, but needs
 * only the structure, so other accounts can be named before their text loads.
 */
export function sectionTitleIn(structure: PaperStructure | undefined, anchor: string): string | null {
  const passage = passageOf(structure, anchor);
  if (!structure || !passage) return null;
  const sections = structure.paper.sections;
  const inside = sections.find(
    (s) => s.heading_span.start_byte >= passage.block_span.start_byte && s.heading_span.start_byte < passage.content_span.end_byte,
  );
  if (inside && inside.level > 1) return inside.title;
  const containing = sections.find((s) => s.ref === passage.section_ref);
  return containing && containing.level > 1 ? containing.title : null;
}

/** "Long record §4.4 How the signs…" for another account; "§4.4 How the signs…" within this one. */
export function placeName(structures: Structures, here: Stage, stage: Stage, anchor: string): string {
  const title = sectionTitleIn(structures[stage], anchor);
  // A passage outside any numbered section is named from its anchor: "abstract" -> "Abstract".
  const plain = anchor.replace(/-/g, " ");
  const where = title ? sectionLabel(title) : plain.charAt(0).toUpperCase() + plain.slice(1);
  return stage === here ? where : `${PAPER_NAMES[stage].short}, ${where}`;
}

/** "Draft; review needs revision." from the structure's state and review state. */
export function statusWords(state: string | undefined, review: string | undefined): string {
  const words = (s: string) => s.replace(/_/g, " ").trim();
  const parts: string[] = [];
  if (state) parts.push(`${words(state).replace(/^./, (c) => c.toUpperCase())}.`);
  if (review) parts.push(`Review recorded as ${review === "needs_revision" ? "needing revision" : words(review)}.`);
  return parts.join(" ");
}

// ------------------------------------------------------------------ routes

export interface Route {
  /** The authored kind: expands, illustrates or answers. */
  kind: string;
  /** incoming: the other passage points at this one; outgoing: this one points at it. */
  relation: "incoming" | "outgoing";
  stage: Stage;
  anchor: string;
  rationale: string;
}

/** Every authored reading link touching one passage, from all three accounts' mappings. */
export function authoredRoutes(structures: Structures, stage: Stage, anchor: string): Route[] {
  const out: Route[] = [];
  const seen = new Set<string>();
  const push = (route: Route) => {
    const key = `${route.relation}:${route.kind}:${route.stage}:${route.anchor}`;
    if (seen.has(key)) return;
    seen.add(key);
    out.push(route);
  };
  for (const link of structures[stage]?.reading_links ?? []) {
    if (link.from_anchor === anchor)
      push({ kind: link.kind, relation: "outgoing", stage: link.to_stage, anchor: link.to_anchor, rationale: link.rationale });
  }
  for (const from of STAGE_ORDER) {
    for (const link of structures[from]?.reading_links ?? []) {
      if (link.to_stage === stage && link.to_anchor === anchor)
        push({ kind: link.kind, relation: "incoming", stage: from, anchor: link.from_anchor, rationale: link.rationale });
    }
  }
  // Fuller treatments, examples and answers first: they are where a reader goes next.
  return out.sort((a, b) => (a.relation === b.relation ? 0 : a.relation === "incoming" ? -1 : 1));
}

/** How the passage being read stands to a route's destination, worded from the reader's side. */
export function relationWord(route: Pick<Route, "kind" | "relation">): string {
  const incoming = route.relation === "incoming";
  switch (route.kind) {
    case "expands":
      // Stored from the fuller treatment to the shorter one.
      return incoming ? "Expanded by" : "Expands";
    case "illustrates":
      return incoming ? "Illustrated by" : "Illustrates";
    case "answers":
      return incoming ? "Answered by" : "Answers";
    default:
      return incoming ? "Linked from" : "Links to";
  }
}

export interface Destination {
  stage: Stage;
  anchor: string;
  /** "Expanded by", "Answers", …; null for a passage found through a shared record. */
  relation: string | null;
  rationale: string;
}

export interface AccountDestinations {
  stage: Stage;
  /** False while that account's structure has not arrived. */
  ready: boolean;
  authored: Destination[];
  /** Passages mapping one of this passage's claims, grouped by the claim that produced the match. */
  shared: { record: string; places: Destination[] }[];
}

const SPECIFIC = new WeakMap<PaperStructure, StructurePassage[]>();

/** A paper's passages, those mapping fewest records first; every bar on the page asks for this. */
function specificFirst(structure: PaperStructure): StructurePassage[] {
  let sorted = SPECIFIC.get(structure);
  if (!sorted) {
    sorted = [...structure.paper.passages].sort(
      (a, b) =>
        a.claim_ids.length + a.assumption_ids.length - (b.claim_ids.length + b.assumption_ids.length) ||
        a.block_span.start_byte - b.block_span.start_byte,
    );
    SPECIFIC.set(structure, sorted);
  }
  return sorted;
}

/**
 * Where the same topic is treated, for the "Passages linked to this one" chooser: for each
 * other account, the authored reading links touching this passage with their
 * direction, then passages that map one of its claims (named by that claim),
 * the most specific first. The reader's own account follows when the authors
 * linked a passage in it. Nothing is inferred beyond the two recorded kinds.
 */
export function sameTopic(structures: Structures, here: { stage: Stage; anchor: string }): AccountDestinations[] {
  const routes = authoredRoutes(structures, here.stage, here.anchor);
  const claims = passageOf(structures[here.stage], here.anchor)?.claim_ids ?? [];
  const taken = new Set([`${here.stage}:${here.anchor}`, ...routes.map((r) => `${r.stage}:${r.anchor}`)]);
  const stages = [...STAGE_ORDER.filter((s) => s !== here.stage), here.stage];
  const out: AccountDestinations[] = [];
  for (const stage of stages) {
    const structure = structures[stage];
    const authored = routes
      .filter((r) => r.stage === stage)
      .map((r) => ({ stage, anchor: r.anchor, relation: relationWord(r), rationale: r.rationale }));
    const shared: AccountDestinations["shared"] = [];
    if (stage !== here.stage && structure) {
      const passages = specificFirst(structure);
      for (const record of claims) {
        const places = passages
          .filter((p) => p.claim_ids.includes(record) && !taken.has(`${stage}:${p.anchor}`))
          .map((p) => ({ stage, anchor: p.anchor, relation: null, rationale: "" }));
        places.forEach((p) => taken.add(`${stage}:${p.anchor}`));
        if (places.length) shared.push({ record, places });
      }
    }
    if (stage === here.stage && !authored.length) continue;
    out.push({ stage, ready: !!structure, authored, shared });
  }
  return out;
}

/** "2 claims and 2 assumptions", "1 claim", counted by each record's kind. */
export function recordTally(ids: string[], graph: { nodes: Map<string, { kind: string }> }): string {
  const assumptions = ids.filter((id) => graph.nodes.get(id)?.kind === "assumption").length;
  const claims = ids.length - assumptions;
  const one = (n: number, word: string) => `${n} ${word}${n === 1 ? "" : "s"}`;
  return [claims ? one(claims, "claim") : "", assumptions ? one(assumptions, "assumption") : ""].filter(Boolean).join(" and ");
}

/** The mapped passages among the parts a selection touches. */
export function passagesBetween(parts: PreparedPart[], a: number, b: number): number {
  let n = 0;
  for (let i = Math.min(a, b); i <= Math.max(a, b); i++) if (parts[i]?.kind === "passage") n++;
  return n;
}

// --------------------------------------------------------------- anchors

/** Where `#anchor` lands: a heading id, alias or `<a id>` first, then a passage anchor. */
export function resolveAnchor(doc: PreparedDocument, anchor: string): { part: number; id?: string } | null {
  const byId = doc.anchorIndex.get(anchor);
  if (byId !== undefined) return { part: byId, id: anchor };
  const part = doc.parts.findIndex((p) => p.kind === "passage" && p.anchor === anchor);
  return part >= 0 ? { part } : null;
}

/**
 * What a passage opened beside shows. Routes name passages, so a passage
 * anchor wins; a fragment from a companion link resolves to the passage that
 * holds it (with the fragment kept, so the pane can scroll to it), and a
 * heading in unmapped text to its section's opening passage.
 */
export function resolveBeside(
  doc: PreparedDocument,
  structure: PaperStructure,
  anchor: string,
): { part: number; passage?: string; fragment?: string } | null {
  const direct = doc.parts.findIndex((p) => p.kind === "passage" && p.anchor === anchor);
  if (direct >= 0) return { part: direct, passage: anchor };
  const at = doc.anchorIndex.get(anchor);
  if (at === undefined) return null;
  const part = doc.parts[at];
  if (part.kind === "passage") return { part: at, passage: part.anchor, fragment: anchor };
  const heading = part.headings.find((h) => h.id === anchor || h.aliases.includes(anchor));
  const section = heading
    ? structure.paper.sections.find((s) => s.title === heading.title && s.heading_span.start_byte >= part.span.start && s.heading_span.start_byte < part.span.end)
    : undefined;
  if (section) {
    const opening = doc.parts.find(
      (p) => p.kind === "passage" && p.span.start >= section.heading_span.start_byte && p.span.start < section.span.end_byte,
    );
    if (opening) return { part: opening.index, passage: opening.anchor };
  }
  return { part: at, fragment: anchor };
}

/** A companion link without a fragment opens that account's first mapped passage. */
export function companionAnchor(structure: PaperStructure | undefined, fragment: string | undefined): string {
  return fragment || structure?.paper.passages[0]?.anchor || "";
}

/** The first passage in an account that discusses any of these records, preferring the first. */
export function firstPassageFor(structure: PaperStructure | undefined, ids: string[]): string | null {
  if (!structure || !ids.length) return null;
  const ordered = [...structure.paper.passages].sort((a, b) => a.block_span.start_byte - b.block_span.start_byte);
  for (const id of ids) {
    const hit = ordered.find((p) => p.claim_ids.includes(id) || p.assumption_ids.includes(id));
    if (hit) return hit.anchor;
  }
  return null;
}

const ROLE_ORDER: StatementRole[] = ["statement", "definition", "derivation", "explanation", "example", "mention"];

/**
 * The alignment's best slice of this paper for a record: statement first, then
 * definition, derivation, explanation, example, mention, the earliest within a role.
 */
export function bestSlice(alignment: Alignment | null, stage: Stage, id: string): AlignedStatement | null {
  const slices = (alignment?.records[id]?.statements ?? []).filter((s) => s.paper === stage);
  return [...slices].sort((a, b) => ROLE_ORDER.indexOf(a.role) - ROLE_ORDER.indexOf(b.role) || a.start_byte - b.start_byte)[0] ?? null;
}

export interface PaperTarget {
  /** The step the landing belongs to, which pins there. */
  record: string;
  slice: AlignedStatement;
  /** The paper states the step, and does not name this declaration at that place. */
  near: boolean;
}

/**
 * Where to send a reader from an open declaration to another paper. Chosen by the Lean:
 * first a slice that itself names this declaration, in this step and then in any step; then
 * a slice of this step whose Lean includes it; then the step's best statement, said to be
 * only that. A landing on unrelated words is the one thing this must never do.
 */
export function paperTarget(alignment: Alignment | null, paper: Stage, record: string, decl: string | null): PaperTarget | null {
  const best = (rows: AlignedStatement[]) => [...rows].sort((a, b) => ROLE_ORDER.indexOf(a.role) - ROLE_ORDER.indexOf(b.role) || a.start_byte - b.start_byte)[0];
  const own = (alignment?.records[record]?.statements ?? []).filter((s) => s.paper === paper);
  if (decl) {
    const names = (s: AlignedStatement) => s.lean?.some((row) => row.name === decl);
    const stated = own.filter((s) => s.lean_source === "statement" && names(s));
    if (stated.length) return { record, slice: best(stated), near: false };
    for (const [id, row] of Object.entries(alignment?.records ?? {})) {
      const found = row.statements.filter((s) => s.paper === paper && s.lean_source === "statement" && names(s));
      if (found.length) return { record: id, slice: best(found), near: false };
    }
  }
  const slice = bestSlice(alignment, paper, record);
  return slice ? { record, slice, near: !!decl } : null;
}

export { sliceAt, statementHref } from "../links";

/** The source lines an `l` value names in this document. */
export function resolveAt(doc: Pick<PreparedDocument, "lineOfByte">, at: string): { start: number; end: number } | null {
  const bytes = /^b(\d+)-(\d+)$/.exec(at);
  if (bytes) return { start: doc.lineOfByte(Number(bytes[1])), end: doc.lineOfByte(Math.max(Number(bytes[1]), Number(bytes[2]) - 1)) };
  const lines = /^(\d+)(?:-(\d+))?$/.exec(at);
  if (!lines) return null;
  const start = Number(lines[1]);
  return { start, end: Math.max(start, Number(lines[2] ?? start)) };
}

/** The parts that hold these lines. */
export function partsOfLines(parts: PreparedPart[], lines: { start: number; end: number }): number[] {
  return parts.filter((p) => !p.blank && p.lines.start <= lines.end && p.lines.end >= lines.start).map((p) => p.index);
}

// ----------------------------------------------------------- reading trail

/** One paper's path through its records, computed once from its structure. */
export interface PaperTrail {
  /** Each passage's position in reading order. */
  order: Map<string, number>;
  /** Each record's first passage in reading order. */
  first: Map<string, number>;
}

export function paperTrail(structure: PaperStructure | undefined): PaperTrail {
  const order = new Map<string, number>();
  const first = new Map<string, number>();
  const passages = [...(structure?.paper.passages ?? [])].sort((a, b) => a.block_span.start_byte - b.block_span.start_byte);
  passages.forEach((passage, i) => {
    order.set(passage.anchor, i);
    for (const id of passageRecords(passage)) if (!first.has(id)) first.set(id, i);
  });
  return { order, first };
}

export interface TrailPlace {
  /** Records reached earlier in the paper, without those in the current passage. */
  passed: Set<string>;
  /** Records the reader has reached, the current passage included. */
  seen: number;
  /** Every record the paper links a passage to. */
  total: number;
}

/** Where a reader at this passage stands on the paper's path; records ahead are the rest. */
export function trailAt(trail: PaperTrail, anchor: string | null, current: readonly string[]): TrailPlace {
  const at = anchor === null ? undefined : trail.order.get(anchor);
  const passed = new Set<string>();
  let seen = 0;
  const here = new Set(current);
  for (const [id, first] of trail.first) {
    if (at === undefined || first > at) continue;
    seen++;
    if (!here.has(id)) passed.add(id);
  }
  return { passed, seen, total: trail.first.size };
}

/**
 * "§3 of 8, 14 of 37 steps so far". Only numbered top-level sections count; in
 * text before the first of them, or after the last, the section is named instead.
 */
export function trailWords(outline: OutlineEntry[], part: number, place: Pick<TrailPlace, "seen" | "total">): string {
  const records = place.total ? `${place.seen} of ${place.total} steps so far` : "";
  const tops = outline.filter((e) => e.parent === null);
  const numbered = tops.filter((e) => /^\d/.test(e.title));
  let at: OutlineEntry | undefined;
  for (const entry of tops) {
    if (entry.part > part) break;
    at = entry;
  }
  let where = "";
  if (at && /^\d/.test(at.title)) where = `${sectionNumber(at.title)} of ${numbered.length}`;
  else if (at) where = at.title;
  else if (numbered.length) where = `Before §1 of ${numbered.length}`;
  return [where, records].filter(Boolean).join(", ");
}

/** How many passages the "Linked passages" chooser offers for this one. */
export function linkedCount(structures: Structures, here: { stage: Stage; anchor: string }): number {
  return sameTopic(structures, here).reduce((n, account) => n + account.authored.length + account.shared.reduce((m, s) => m + s.places.length, 0), 0);
}

// ---------------------------------------------------------------- outline

export interface OutlineEntry {
  id: string;
  title: string;
  level: number;
  part: number;
  /** The id of the entry this one sits under, or null for a top-level section. */
  parent: string | null;
}

/**
 * Sections of levels 2 to 4 as the reader sees them, with their fragment ids
 * and the section each sits under. A level-2 heading set directly under the
 * title (the subtitle) is part of the title block, not a section. Level-4
 * entries are listed so a deep subsection (long §8.1.1) can be reached; the
 * outline shows them only inside the active branch.
 */
export function outlineOf(doc: PreparedDocument): OutlineEntry[] {
  const all = doc.parts.flatMap((part) => part.headings.map((h) => ({ ...h, part: part.index })));
  const out: OutlineEntry[] = [];
  const stack: OutlineEntry[] = [];
  all.forEach((h, i) => {
    if (h.level < 2 || h.level > 4) return;
    const prev = all[i - 1];
    if (prev && prev.level === 1 && h.level === 2 && prev.part === h.part && !/^\d/.test(h.title)) return;
    while (stack.length && stack[stack.length - 1].level >= h.level) stack.pop();
    const entry = { id: h.id, title: h.title, level: h.level, part: h.part, parent: stack[stack.length - 1]?.id ?? null };
    out.push(entry);
    stack.push(entry);
  });
  return out;
}

/** Statements with Lean per outline entry, each section counting its subsections. */
export function outlineTieCounts(entries: OutlineEntry[], structure: PaperStructure, doc: PreparedDocument, ties: TieModel): Map<string, TieCount> {
  const sections = entries.map((entry) => {
    const part = doc.parts[entry.part];
    const heading = structure.paper.sections.find((s) => s.title === entry.title && s.heading_span.start_byte >= part.span.start && s.heading_span.start_byte < part.span.end);
    return { id: entry.id, parent: entry.parent, start: heading?.heading_span.start_byte ?? part.span.start };
  });
  return tieCounts(ties, sections);
}

/** The entries from the top-level section down to `id`: a document breadcrumb, not a history. */
export function chainOf(entries: OutlineEntry[], id: string | null): OutlineEntry[] {
  if (!id) return [];
  const byId = new Map(entries.map((e) => [e.id, e]));
  const chain: OutlineEntry[] = [];
  for (let e = byId.get(id); e; e = e.parent ? byId.get(e.parent) : undefined) chain.unshift(e);
  return chain;
}

/** "8.1.1 Bounds" -> "§8.1.1"; an unnumbered heading keeps its words. */
export function sectionNumber(title: string): string {
  const match = title.match(/^(\d+(?:\.\d+)*)\.?\s/);
  return match ? `§${match[1]}` : title;
}

// ------------------------------------------------------------- rendering

/**
 * A placeholder height for a part not yet rendered, from its byte length.
 * Calibrated against the rendered papers at the desktop measure; the page
 * keeps the reading position fixed when the real height arrives.
 */
export function estimateHeight(part: PreparedPart, columnWidth = 592): number {
  if (part.blank) return 0;
  const bytes = part.span.end - part.span.start;
  const perLine = Math.max(30, columnWidth / 8.6);
  const lines = bytes / perLine;
  return Math.round(lines * 29 * 0.78 + part.headings.length * 56 + part.figures.length * 320 + 16);
}

/** Parts in order of how soon a reader will reach them, nearest first. */
export function idleOrder(count: number, near: number): number[] {
  const order: number[] = [];
  for (let d = 0; order.length < count; d++) {
    if (near + d < count) order.push(near + d);
    if (d > 0 && near - d >= 0) order.push(near - d);
    if (near + d >= count && near - d < 0) break;
  }
  return order;
}

/** The byte span of the parts a selection touches, in document order. */
export function selectionSpan(parts: PreparedPart[], a: number, b: number): { start: number; end: number } {
  const lo = Math.min(a, b);
  const hi = Math.max(a, b);
  return { start: parts[lo].span.start, end: parts[hi].span.end };
}

/**
 * HTML for a second copy of a part: fragment ids become data attributes, so
 * no id repeats on the page, and a link to a fragment of its own account
 * (`#strip-estimates`) opens that place in the reader, wherever the copy is
 * shown, instead of being resolved against the page around it.
 */
export function withoutIds(html: string): string {
  return html
    .replace(/(<[a-z][^>]*?)\sid="/gi, '$1 data-id="')
    .replace(/<a\b[^>]*>/gi, (tag) => {
      const stage = /\sdata-in="([a-z]+)"/.exec(tag)?.[1];
      if (!stage || !STAGES.has(stage)) return tag;
      return tag.replace(/\shref="#([^"]*)"/, (_m, fragment: string) => ` href="${readerHref(stage)}#${fragment}" data-fragment="${fragment}"`);
    });
}

/** "3 claims", "1 claim and 1 assumption", for counts a reader can check against the chips. */
export function recordCount(claims: number, assumptions: number): string {
  const one = (n: number, word: string) => `${n} ${word}${n === 1 ? "" : "s"}`;
  if (claims && assumptions) return `${one(claims, "claim")} and ${one(assumptions, "assumption")}`;
  if (assumptions) return one(assumptions, "assumption");
  return one(claims, "claim");
}


