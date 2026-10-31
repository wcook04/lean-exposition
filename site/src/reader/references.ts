// References: "Lemma 2", "§4", "(5)", "[OpenAI (2026a), Lemma 6.1][FS]" as real links.
//
// What each reference points to was decided by reading its sentence, and that decision is
// data: `examples/qaoa-sk/alignment/references-<paper>.json`, keyed by byte range. A regular
// expression cannot do it. Most numbered results named in these papers belong to OpenAI's
// manuscripts, whose numbering collides with the papers' own, and a link to the wrong
// Theorem 1 is worse than none.
//
// The marks reach the text the way the ties do, and the source bytes never change:
// 1. `markReferences` puts one private-use character at each end of each reference, before
//    the engine's own preprocessing runs.
// 2. Markdown parses around them.
// 3. `linkReferences` turns each pair into a link once the part's HTML is sanitised. A
//    reference that is a Markdown link already (a citation) keeps its own <a> and gains the
//    table row, so it still reads as what it was with no script at all.
//
// `wrapTies` runs after this, and its runs pass through inline elements, so a reference can
// sit inside a tied statement and both work.

import type { Stage } from "../api/types";
import { readerHref } from "./links";

export type RefKind = "label" | "equation" | "figure" | "section" | "other_paper" | "manuscript" | "citation";

export interface RefRow {
  /** For `other_paper`: the section's heading there. */
  title?: string;
  start_byte: number;
  end_byte: number;
  /** The exact words, checked against the paper before the row is used. */
  quote: string;
  kind: RefKind;
  /** An anchor in this paper, or in `paper` for `other_paper`. */
  target?: string;
  paper?: Stage;
  /** A key of `sources`, for a manuscript or a citation. */
  source?: string;
  /** The place in the source, as this paper words it. */
  locator?: string;
}

export interface RefTarget {
  kind: string;
  /** "Lemma 2", "(5)", "§4.5": the name the paper gives it. */
  label: string;
  title?: string;
  start_byte: number;
  end_byte: number;
}

export interface RefSource {
  name: string;
  href: string;
  /** The bytes of its entry in this paper's reference list. */
  entry: [number, number] | null;
}

export interface ReferenceTable {
  paper: Stage;
  targets: Record<string, RefTarget>;
  sources: Record<string, RefSource>;
  references: RefRow[];
}

/** The references usable against these bytes, and the text behind them. */
export interface RefIndex {
  stage: string;
  table: ReferenceTable;
  rows: RefRow[];
  text(start: number, end: number): string;
}

export function loadReferenceTable(stage: Stage): Promise<ReferenceTable | null> {
  const load = {
    short: () => import("virtual:paper-references/short"),
    long: () => import("virtual:paper-references/long"),
    expository: () => import("virtual:paper-references/expository"),
  }[stage];
  return load().then(
    (module) => module.default as ReferenceTable,
    () => null,
  );
}

const decoder = new TextDecoder("utf-8", { ignoreBOM: true });

/**
 * Keep the rows whose words are still at their bytes. A paper edited without a new review
 * loses those links here, and the test fails; it never gains a link that lands wrongly.
 */
export function referenceIndex(table: ReferenceTable, bytes: Uint8Array): RefIndex {
  const text = (start: number, end: number) => decoder.decode(bytes.subarray(start, end));
  const rows = table.references.filter((row) => row.start_byte < row.end_byte && text(row.start_byte, row.end_byte) === row.quote);
  return { stage: table.paper, table, rows, text };
}

// ---- Marks ------------------------------------------------------------------------------

// Math uses U+E000 to U+E005 and ties U+E100 to U+F4FF.
const OPEN = 0xf500;
const CLOSE = 0xf700;
export const MARK_CAPACITY = 0x200;

const MARKS = /[-]/g;
const OPENING = /[-](<a )?/g;
const CLOSING = /[-]/g;

export const stripRefMarks = (text: string) => text.replace(MARKS, "");

const isPassengerCode = (code: number) => code >= 0xe100 && code < 0xf500;

/**
 * Put each row's marks into one part's text, which starts at `startByte` of the paper. The
 * text may already carry tie marks, which stand for no bytes.
 */
export function markReferences(text: string, startByte: number, index: RefIndex | null): string {
  if (!index) return text;
  const inside = index.rows
    .map((row, at) => ({ row, at }))
    .filter(({ row, at }) => at < MARK_CAPACITY && row.start_byte >= startByte && row.end_byte <= startByte + 4 * text.length);
  if (!inside.length) return text;
  const events = inside
    .flatMap(({ row, at }) => [
      { byte: row.start_byte, mark: String.fromCharCode(OPEN + at), order: 1 },
      { byte: row.end_byte, mark: String.fromCharCode(CLOSE + at), order: 0 },
    ])
    .sort((a, b) => a.byte - b.byte || a.order - b.order);
  let out = "";
  let byte = startByte;
  let from = 0;
  let next = 0;
  // Closes go before a tie mark at the same byte and opens after it, so a reference that is
  // a Markdown link keeps its opening mark touching its "[".
  const place = (i: number, order: number) => {
    while (next < events.length && events[next].byte === byte && events[next].order === order) {
      out += text.slice(from, i) + events[next++].mark;
      from = i;
    }
  };
  for (let i = 0; i < text.length && next < events.length; i++) {
    place(i, 0);
    const code = text.charCodeAt(i);
    if (isPassengerCode(code)) continue;
    place(i, 1);
    if (code < 0x80) byte += 1;
    else if (code < 0x800) byte += 2;
    else if (code >= 0xd800 && code <= 0xdbff) {
      byte += 4;
      i++;
    } else byte += 3;
  }
  out += text.slice(from);
  // A reference ending the part closes after its last character.
  while (next < events.length && events[next].byte === byte) out += events[next++].mark;
  return out;
}

const attr = (value: string) => value.replace(/&/g, "&amp;").replace(/"/g, "&quot;").replace(/</g, "&lt;");

/** The opening of a reference that is not a Markdown link already. */
function openingTag(index: RefIndex, row: RefRow, at: number): string {
  const ref = `data-ref="${at}"`;
  const stage = attr(index.stage);
  switch (row.kind) {
    case "other_paper": {
      const paper = attr(row.paper ?? "");
      const target = attr(row.target ?? "");
      return `<a href="${attr(readerHref(row.paper ?? "", row.target ?? ""))}" class="companion" data-companion="${paper}" data-fragment="${target}" ${ref}>`;
    }
    case "manuscript":
      return `<a href="${attr(index.table.sources[row.source ?? ""]?.href ?? "#")}" class="ext" data-external="" target="_blank" rel="noopener noreferrer" ${ref}>`;
    default:
      return `<a href="#${attr(encodeURIComponent(row.target ?? ""))}" data-in="${stage}" ${ref}>`;
  }
}

/** Turn the marks in a part's sanitised HTML into links. */
export function linkReferences(html: string, index: RefIndex | null): string {
  if (!index) return html;
  return html
    .replace(OPENING, (mark: string, tag: string | undefined) => {
      const at = mark.charCodeAt(0) - OPEN;
      const row = index.rows[at];
      if (!row) return tag ?? "";
      return tag ? `<a data-ref="${at}" ` : openingTag(index, row, at);
    })
    .replace(CLOSING, (mark: string) => {
      const row = index.rows[mark.charCodeAt(0) - CLOSE];
      return row && !isOwnLink(row) ? "</a>" : "";
    });
}

/** Whether this row was written as a Markdown link, so that its <a> is already there. */
const isOwnLink = (row: RefRow) => row.quote.startsWith("[") && /\]$|\)$/.test(row.quote);

// ---- Anchors ----------------------------------------------------------------------------

const KIND_ID: Record<string, string> = { Theorem: "thm", Lemma: "lem", Proposition: "prop", Corollary: "cor" };

/** `\tag{4.1}` to `eq-4.1`, or null for an unnumbered display. */
export function equationId(tex: string): string | null {
  const tag = /\\tag\{([^{}]+)\}/.exec(tex);
  return tag ? `eq-${tag[1]}` : null;
}

export const figureId = (number: number) => `fig-${number}`;

/**
 * Ids for the bold run-in labels of one paper, called in document order. A numbered result
 * is `lem-2`; a proof is `proof-` and the result it proves, named or the result before it.
 * "Question 1" has its bookmark in the Markdown already.
 */
export function labelIds(): (lead: string) => string | null {
  let last: string | null = null;
  return (lead) => {
    const words = stripRefMarks(lead).replace(/\s+/g, " ").trim();
    const numbered = /^(Theorem|Lemma|Proposition|Corollary) (\d+(?:\.\d+)*)\b/.exec(words);
    if (numbered) return (last = `${KIND_ID[numbered[1]]}-${numbered[2]}`);
    if (/^Source theorem\b/.test(words)) return (last = "source-theorem");
    if (/^Strict-curvature input\b/.test(words)) return (last = "strict-curvature-input");
    const proof = /^Proof(?: of (Theorem|Lemma|Proposition|Corollary) (\d+(?:\.\d+)*))?\b/.exec(words);
    if (!proof) return null;
    const of = proof[1] ? `${KIND_ID[proof[1]]}-${proof[2]}` : last;
    return of ? `proof-${of}` : null;
  };
}

// ---- What a reference shows -------------------------------------------------------------

export interface RefView {
  /** What the reader meets: "Lemma 2", "§4.5", "OpenAI (2026a)". */
  title: string;
  /** Markdown to typeset exactly as the paper does; null when there is none. */
  body: string | null;
  /** A sentence above the body, in plain words. */
  note: string | null;
  /** The place the source is cited for. */
  locator: string | null;
  /** The leaving link for a source. */
  href: string | null;
  /** The anchor a jump goes to. */
  go: string | null;
  /** The statement's bytes, for the tie to its record. */
  span: [number, number] | null;
}

const manuscriptNote = (quote: string, name: string) =>
  /\d/.test(quote) ? `${quote} of ${name}, in that source's numbering.` : `The ${quote} of ${name}.`;

/** Everything a preview or an inset shows for one row. */
export function refView(index: RefIndex, row: RefRow): RefView {
  const { targets, sources } = index.table;
  if (row.kind === "citation" || row.kind === "manuscript") {
    const source = sources[row.source ?? ""];
    const body = source?.entry ? index.text(source.entry[0], source.entry[1]).replace(/^\s*\n/, "") : null;
    return {
      title: source?.name ?? row.quote,
      body,
      note: row.kind === "manuscript" ? manuscriptNote(row.quote, source?.name ?? "the cited source") : null,
      locator: row.kind === "citation" ? (row.locator ?? null) : null,
      href: source?.href ?? null,
      go: null,
      span: null,
    };
  }
  if (row.kind === "other_paper") {
    return { title: row.quote, body: null, note: `Long record: ${row.title ?? row.target}`, locator: null, href: null, go: null, span: null };
  }
  const target = targets[row.target ?? ""];
  if (!target) return { title: row.quote, body: null, note: null, locator: null, href: null, go: row.target ?? null, span: null };
  return {
    title: target.label,
    body: target.kind === "section" ? null : index.text(target.start_byte, target.end_byte),
    note: target.kind === "section" ? (target.title ?? null) : null,
    locator: null,
    href: null,
    go: row.target ?? null,
    span: [target.start_byte, target.end_byte],
  };
}

/** A click opens these in place. Sections jump, and another paper opens beside this one. */
export const opensInPlace = (row: RefRow) => row.kind !== "section" && row.kind !== "other_paper";

/** The module of a commit-pinned GitHub link into the Lean tree, for the site's own Lean page. */
export function leanModuleOf(href: string): string | null {
  const m = /\/lean\/(OAI|ComparatorChallenges)\/(.+)\.lean(?:#|$)/.exec(href);
  return m ? `${m[1]}.${m[2].replace(/\//g, ".")}` : null;
}

export interface RecordSlice {
  id: string;
  /** The slice's address, where the alignment gives it. */
  at?: string;
}

/** The statement's record with Lean, from the alignment: the one whose slice most overlaps these bytes. */
export function recordOver(
  span: [number, number],
  paper: string,
  records: Record<string, { lean: unknown[]; statements: { paper: string; role: string; start_byte: number; end_byte: number; at?: string }[] }>,
): RecordSlice | null {
  let best: RecordSlice | null = null;
  let score = 0;
  for (const [id, record] of Object.entries(records)) {
    if (!record.lean.length) continue;
    for (const slice of record.statements) {
      if (slice.paper !== paper || slice.role !== "statement") continue;
      const overlap = Math.min(span[1], slice.end_byte) - Math.max(span[0], slice.start_byte);
      if (overlap > score) {
        best = { id, at: slice.at };
        score = overlap;
      }
    }
  }
  return best;
}
