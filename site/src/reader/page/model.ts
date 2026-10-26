// Pure helpers for the reader page: how a passage, a section, a route and a
// reading position are named and found. Nothing here touches the DOM or the
// network, so the rules are tested directly against the captured fixtures.

import type { PaperStructure, ReadingItem, Stage, StructurePassage } from "../../api/types";
import type { PreparedDocument, PreparedPart } from "../engine";
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
  const where = title ? sectionLabel(title) : `the passage “${anchor.replace(/-/g, " ")}”`;
  return stage === here ? where : `${PAPER_NAMES[stage].short} ${where}`;
}

/** "Draft; review needs revision." from the structure's state and review state. */
export function statusWords(state: string | undefined, review: string | undefined): string {
  const words = (s: string) => s.replace(/_/g, " ").trim();
  const parts: string[] = [];
  if (state) parts.push(words(state).replace(/^./, (c) => c.toUpperCase()));
  if (review) parts.push(`review ${words(review)}`);
  if (!parts.length) return "";
  const sentence = parts.join("; ");
  return sentence.replace(/^./, (c) => c.toUpperCase()) + ".";
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

/** The words that introduce a route, read from the passage the reader is on. */
export function routeLead(route: Route, here: { stage: Stage; anchor: string }, structures: Structures): string {
  if (route.relation === "outgoing") {
    if (route.kind === "expands") return "This expands";
    if (route.kind === "illustrates") return "This is an example of";
    if (route.kind === "answers") return "This answers";
    return "This links to";
  }
  if (route.kind === "expands") return "A fuller treatment";
  if (route.kind === "illustrates") return "An example of this";
  if (route.kind === "answers") {
    if (route.stage !== here.stage) return `Answered in the ${PAPER_NAMES[route.stage].short.toLowerCase()}`;
    const order = structures[here.stage]?.paper.passages ?? [];
    const at = (a: string) => order.find((p) => p.anchor === a)?.block_span.start_byte ?? 0;
    return at(route.anchor) > at(here.anchor) ? "Answered below" : "Answered above";
  }
  return "Linked from";
}

export interface SharedPlace {
  stage: Stage;
  anchor: string;
  shared: number;
}

/**
 * Passages found by a shared claim (derived links), grouped by account in
 * reading order, without the passage itself or any authored destination.
 */
export function sharedPlaces(items: ReadingItem[], here: { stage: Stage; anchor: string }, exclude: Set<string>): SharedPlace[] {
  const found = new Map<string, SharedPlace>();
  for (const item of items) {
    if (!item.derived) continue;
    for (const ref of [item.from, item.to]) {
      const p = parsePassageRef(ref);
      if (!p || (p.stage === here.stage && p.anchor === here.anchor)) continue;
      const key = `${p.stage}:${p.anchor}`;
      if (exclude.has(key)) continue;
      const prior = found.get(key);
      const shared = item.shared_claim_refs?.length ?? 0;
      if (!prior || prior.shared < shared) found.set(key, { ...p, shared });
    }
  }
  const rank = (s: Stage) => (s === here.stage ? -1 : STAGE_ORDER.indexOf(s));
  return [...found.values()].sort((a, b) => rank(a.stage) - rank(b.stage) || b.shared - a.shared);
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

// ---------------------------------------------------------------- outline

export interface OutlineEntry {
  id: string;
  title: string;
  level: number;
  part: number;
}

/**
 * Sections of level 2 and 3 as the reader sees them, with their fragment
 * ids. A level-2 heading set directly under the title (the subtitle) is part
 * of the title block, not a section.
 */
export function outlineOf(doc: PreparedDocument): OutlineEntry[] {
  const all = doc.parts.flatMap((part) => part.headings.map((h) => ({ ...h, part: part.index })));
  const out: OutlineEntry[] = [];
  all.forEach((h, i) => {
    if (h.level < 2 || h.level > 3) return;
    const prev = all[i - 1];
    if (prev && prev.level === 1 && h.level === 2 && prev.part === h.part && !/^\d/.test(h.title)) return;
    out.push({ id: h.id, title: h.title, level: h.level, part: h.part });
  });
  return out;
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

/** HTML for a second copy of a part: fragment ids become data attributes, so no id repeats on the page. */
export function withoutIds(html: string): string {
  return html.replace(/(<[a-z][^>]*?)\sid="/gi, '$1 data-id="');
}

/** The majority region of a passage's records, for its margin rule. */
export function majorityRegion(ids: string[], regionOf: (id: string) => string | undefined): string | null {
  const counts = new Map<string, number>();
  for (const id of ids) {
    const r = regionOf(id);
    if (r) counts.set(r, (counts.get(r) ?? 0) + 1);
  }
  let best: string | null = null;
  let n = 0;
  for (const [r, c] of counts) if (c > n) [best, n] = [r, c];
  return best;
}

/** "3 claims", "1 claim and 1 assumption", for counts a reader can check against the chips. */
export function recordCount(claims: number, assumptions: number): string {
  const one = (n: number, word: string) => `${n} ${word}${n === 1 ? "" : "s"}`;
  if (claims && assumptions) return `${one(claims, "claim")} and ${one(assumptions, "assumption")}`;
  if (assumptions) return one(assumptions, "assumption");
  return one(claims, "claim");
}

/** "claim", "3 claims", "2 claims and 1 assumption", counted by each record's kind. */
export function describeRecords(ids: string[], graph: { nodes: Map<string, { kind: string }> }): string {
  const assumptions = ids.filter((id) => graph.nodes.get(id)?.kind === "assumption").length;
  const claims = ids.length - assumptions;
  if (claims === 1 && !assumptions) return "claim";
  if (assumptions === 1 && !claims) return "assumption";
  return recordCount(claims, assumptions);
}

/**
 * The words a route's link shows. Another section is named by its heading;
 * a passage in the same section is named by where it is, so a question and
 * its answer never point at the heading both sit under.
 */
export function routeTarget(route: Route, here: { stage: Stage; anchor: string }, structures: Structures): string {
  const sameSection =
    route.stage === here.stage && sectionTitleIn(structures[here.stage], route.anchor) === sectionTitleIn(structures[here.stage], here.anchor);
  if (!sameSection) return placeName(structures, here.stage, route.stage, route.anchor);
  const order = structures[here.stage]?.paper.passages ?? [];
  const at = (a: string) => order.find((p) => p.anchor === a)?.block_span.start_byte ?? 0;
  const where = at(route.anchor) > at(here.anchor) ? "below" : "above";
  if (route.kind === "answers") return route.relation === "incoming" ? "see the answer" : `the question ${where}`;
  return `the passage ${where}`;
}
