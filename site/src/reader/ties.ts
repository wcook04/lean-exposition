// Ties: which words of a paper are tied to a record, and through it to the Lean.
//
// The edition gives each paper a small index (`ties/<stage>.json`): segments by byte
// range, each inside one Markdown block, each listing its ties with Lean first. A tie is
// one statement, and a statement may run across several segments.
//
// The marks reach the text in three steps, and the source bytes never change:
// 1. `markSource` puts one zero-width private-use character at each end of each segment,
//    before the engine's own preprocessing runs.
// 2. A core rule takes them out of the parser's text tokens into tokens of their own
//    (engine.ts), so smart quotes, dashes and run-in labels see the words they saw before.
// 3. `wrapTies` turns each run between marks into `<span class="tie" data-t="…">` once the
//    part's HTML is whole, treating formulas as atoms. No mark ever reaches the page.
//
// The passage-level fallback lives here too: any paragraph with no exact slice can still
// say what its passage discusses.

import { loadTies as fetchTies, type Alignment, type StatementRole, type TieIndex, type TieSegment } from "../api/lean";
import type { Stage } from "../api/types";

export type { Tie, TieIndex, TiePassage, TieSegment } from "../api/lean";

/** The paper's index, or null for an edition without one: such a paper still reads in full. */
export function loadTies(stage: Stage): Promise<TieIndex | null> {
  return fetchTies(stage).catch(() => null);
}

// ---- Marks ------------------------------------------------------------------------------

const OPEN = 0xe100;
const CLOSE = 0xeb00;
/** Marks per kind. Math uses U+E000 to U+E005, and no paper comes near this many segments. */
const CAPACITY = 0xa00;

export const MARK = "[-]";
const ANY_MARK = new RegExp(MARK);
const MARKS = new RegExp(MARK, "g");

export const openMark = (segment: number) => String.fromCharCode(OPEN + segment);
export const closeMark = (segment: number) => String.fromCharCode(CLOSE + segment);

export const isMarkCode = (code: number) => code >= OPEN && code < CLOSE + CAPACITY;
export const hasMarks = (text: string) => ANY_MARK.test(text);
export const stripMarks = (text: string) => text.replace(MARKS, "");

function readMark(code: number): { open: boolean; segment: number } {
  return code >= CLOSE ? { open: false, segment: code - CLOSE } : { open: true, segment: code - OPEN };
}

/**
 * A line's block syntax has to stay first on its line, so a mark that a slice put in
 * front of it moves in behind it: `#`, a list marker, a quotation or a table's first bar.
 */
const BLOCK_PREFIX = new RegExp(`^([ \\t]*)(${MARK}+)((?:#{1,6}[ \\t]+|[-*+][ \\t]+|\\d+[.)][ \\t]+|>[ \\t]?|\\|[ \\t]*)+)`, "gm");

/** Text a mark must never enter: a TeX figure, whose source is hashed and drawn, not read. */
const TEX_BLOCK = /\\begin\{figure\*?\}[\s\S]*?\\end\{figure\*?\}|^(`{3,}|~{3,})[ \t]*\{=latex\}[^\n]*\n[\s\S]*?^\1[ \t]*$/gm;

/** The segments that fall inside these bytes, in document order. */
export function segmentsIn(segments: readonly TieSegment[], start: number, end: number): { segment: number; start: number; end: number }[] {
  const found: { segment: number; start: number; end: number }[] = [];
  segments.forEach(([from, to], segment) => {
    if (segment < CAPACITY && from >= start && to <= end && from < to) found.push({ segment, start: from, end: to });
  });
  return found;
}

/**
 * One part's text with the marks of its segments in place. Works on bytes because
 * the index does, and leaves the bytes themselves alone: `decode` only ever sees runs of
 * the original, so a sha or a literal comparison is still made on the source.
 */
export function markSource(
  bytes: Uint8Array,
  span: { start: number; end: number },
  segments: { segment: number; start: number; end: number }[],
  decode: (piece: Uint8Array) => string,
): string {
  if (!segments.length) return decode(bytes.subarray(span.start, span.end));
  const events = segments
    .flatMap((s) => [
      { at: s.start, mark: openMark(s.segment), order: 1 },
      { at: s.end, mark: closeMark(s.segment), order: 0 },
    ])
    .sort((a, b) => a.at - b.at || a.order - b.order);
  let text = "";
  let at = span.start;
  for (const event of events) {
    text += decode(bytes.subarray(at, event.at)) + event.mark;
    at = event.at;
  }
  text += decode(bytes.subarray(at, span.end));
  return text.replace(BLOCK_PREFIX, "$1$3$2");
}

/** Take out the marks that fell inside a TeX figure; the slice is then simply not marked there. */
export function clearTexBlocks(text: string): string {
  return text.replace(TEX_BLOCK, (block) => stripMarks(block));
}

// ---- From marks to spans ----------------------------------------------------------------

/** Set whole: a formula is one thing to point at, and its layout code expects its own tree. */
const ATOM = ".katex, .katex-display, .katex-error, .math-display, figure, img, svg";
/** An atom that is marked itself: wrapping it would hide it from the code that fits it to the column. */
const BLOCK_ATOM = ".math-display, figure";

/**
 * Wrap every run between marks in `<span class="tie" data-t="<segment>">`, across any
 * inline nesting: a run that crosses into `<strong>` becomes one span outside and one
 * inside, so each stays inline and the markup around the words is unchanged. An unclosed
 * mark ends with the part. Text is otherwise untouched; the marks go.
 */
export function wrapTies(html: string, document: Document = window.document): string {
  if (!hasMarks(html)) return html;
  const box = document.createElement("template");
  box.innerHTML = html;
  const open: number[] = [];
  let run: ChildNode[] = [];
  let runSegment = -1;

  const flush = () => {
    if (run.length && run.some((node) => node.nodeType !== 3 || (node as Text).data.trim())) {
      const span = document.createElement("span");
      span.className = "tie";
      span.dataset.t = String(runSegment);
      run[0].before(span);
      span.append(...run);
    }
    run = [];
  };
  const leaf = (node: ChildNode) => {
    const segment = open.length ? open[open.length - 1] : -1;
    if (segment < 0) return flush();
    if (run.length && (segment !== runSegment || run[run.length - 1].nextSibling !== node)) flush();
    runSegment = segment;
    run.push(node);
  };
  const mark = (code: number) => {
    flush();
    const { open: opens, segment } = readMark(code);
    if (opens) open.push(segment);
    else {
      const at = open.lastIndexOf(segment);
      if (at >= 0) open.splice(at, 1);
    }
  };
  const walk = (parent: Node) => {
    for (let child = parent.firstChild; child; ) {
      const next = child.nextSibling as ChildNode | null;
      if (child.nodeType === 3) {
        const node = child as Text;
        if (!hasMarks(node.data)) leaf(node);
        else {
          let piece = "";
          const place = () => {
            if (!piece) return;
            const text = document.createTextNode(piece);
            node.before(text);
            leaf(text);
            piece = "";
          };
          for (const char of node.data) {
            const code = char.charCodeAt(0);
            if (char.length === 1 && isMarkCode(code)) {
              place();
              mark(code);
            } else piece += char;
          }
          place();
          node.remove();
        }
      } else if (child.nodeType === 1) {
        const element = child as Element;
        if (element.matches(BLOCK_ATOM)) {
          flush();
          if (open.length) {
            element.classList.add("tie");
            element.setAttribute("data-t", String(open[open.length - 1]));
          }
          // A mark can sit inside a display set in the running text; it still counts.
          closeMarksIn(element);
        } else if (element.matches(ATOM)) leaf(element);
        else {
          flush();
          walk(element);
          flush();
        }
      }
      child = next;
    }
  };
  const closeMarksIn = (element: Element) => {
    const walker = document.createTreeWalker(element, 4);
    for (let node = walker.nextNode() as Text | null; node; node = walker.nextNode() as Text | null) {
      if (!hasMarks(node.data)) continue;
      for (const char of node.data) if (isMarkCode(char.charCodeAt(0))) mark(char.charCodeAt(0));
      node.data = stripMarks(node.data);
    }
  };
  walk(box.content);
  flush();
  return box.innerHTML;
}

// ---- The model the reader works from ----------------------------------------------------

export interface TieModel {
  index: TieIndex;
  /** The segments of each statement, in document order. */
  segmentsOf: number[][];
  /** Statements in paper order, those with marked text only. */
  order: number[];
  /**
   * Where stepping stops: one statement for each place a statement starts. Many slices
   * can open on the same words, and a step must always move.
   */
  stops: number[];
  /** Each statement's place among the stops, or -1. */
  place: number[];
  /** `record|at` to statement. */
  byKey: Map<string, number>;
  /** Each record's statements here, in paper order. */
  byRecord: Map<string, number[]>;
  /** Which statements have Lean, by segment: darkens the margin tick. */
  segmentLean: boolean[];
}

const EMPTY: TieIndex = { segments: [], ties: [], passages: [], meaning: "" };

export function tieModel(index: TieIndex | null): TieModel {
  const source = index ?? EMPTY;
  const segmentsOf: number[][] = source.ties.map(() => []);
  source.segments.forEach(([, , members], segment) => members.forEach((t) => segmentsOf[t]?.push(segment)));
  const order = source.ties.map((_, t) => t).filter((t) => segmentsOf[t].length);
  order.sort((a, b) => segmentsOf[a][0] - segmentsOf[b][0] || segmentsOf[a].length - segmentsOf[b].length || a - b);
  const stops: number[] = [];
  const place = source.ties.map(() => -1);
  source.segments.forEach(([, , members], segment) => {
    const opening = members.find((t) => segmentsOf[t][0] === segment);
    if (opening !== undefined) stops.push(opening);
    for (const t of members) if (segmentsOf[t][0] === segment) place[t] = stops.length - 1;
  });
  const byKey = new Map<string, number>();
  const byRecord = new Map<string, number[]>();
  source.ties.forEach((tie, t) => byKey.set(`${tie.record}|${tie.at}`, t));
  for (const t of order) {
    const rows = byRecord.get(source.ties[t].record);
    if (rows) rows.push(t);
    else byRecord.set(source.ties[t].record, [t]);
  }
  const segmentLean = source.segments.map(([, , members]) => members.some((t) => source.ties[t]?.lean));
  return { index: source, segmentsOf, order, stops, place, byKey, byRecord, segmentLean };
}

/** The statement a segment stands for: its first tie, which has Lean if any does, and is the narrowest. */
export function statementOf(model: TieModel, segment: number): number | null {
  return model.index.segments[segment]?.[2][0] ?? null;
}

/** The other statements on the same words, for "Also here". */
export function sameWords(model: TieModel, t: number): number[] {
  const members = model.index.segments[model.segmentsOf[t]?.[0]]?.[2] ?? [];
  return members.filter((other) => other !== t);
}

/** An exact slice wins; otherwise open an authored statement before a passing mention. */
export function statementFor(model: TieModel, record: string | undefined, at?: string): number | null {
  if (!record) return null;
  if (at) {
    const exact = model.byKey.get(`${record}|${at}`);
    if (exact !== undefined) return exact;
  }
  const rows = model.byRecord.get(record);
  if (!rows?.length) return null;
  const stated = rows.filter((t) => model.index.ties[t].role === "statement");
  return stated.find((t) => model.index.ties[t].lean) ?? stated[0] ?? rows.find((t) => model.index.ties[t].lean) ?? rows[0];
}

/** The next stop after this segment, by a step of +1 or -1; from nothing, the first or the last. */
export function stepFrom(model: TieModel, segment: number | null, step: 1 | -1): number | null {
  const firstSegment = (t: number) => model.segmentsOf[t][0];
  if (segment === null) return model.stops[step > 0 ? 0 : model.stops.length - 1] ?? null;
  if (step > 0) return model.stops.find((t) => firstSegment(t) > segment) ?? null;
  for (let i = model.stops.length - 1; i >= 0; i--) if (firstSegment(model.stops[i]) < segment) return model.stops[i];
  return null;
}

/**
 * What is true of a statement and the Lean, in words a reader can take at face value. The tie
 * index says it; an edition exported before it did has the same facts in the alignment.
 */
export function leanTruth(model: TieModel, t: number, alignment: Alignment | null): { lean: boolean; words: string; note: string | null } {
  const tie = model.index.ties[t];
  const statement = alignment?.records[tie.record]?.statements.find((s) => s.at === tie.at);
  if (!tie.lean) {
    const note = tie.note ?? statement?.note ?? null;
    return { lean: false, words: note ?? "No Lean linked.", note };
  }
  const relation = tie.relation ?? statement?.lean?.[0]?.relation;
  return { lean: true, words: relation === "part" ? "The Lean has some of this" : "Has Lean", note: null };
}

/** The records a passage discusses, whether or not any sentence of it is tied exactly. */
export function passageTopics(model: TieModel, anchor: string | null | undefined): string[] {
  if (!anchor) return [];
  return model.index.passages.find((row) => row[3] === anchor)?.[2] ?? [];
}

export interface TieCount {
  /** Statements with Lean. */
  lean: number;
  /** All statements. */
  all: number;
}

/**
 * Statements per section, each section counting those in its subsections too. `sections`
 * give each outline entry's first byte and its parent; a statement belongs to the last
 * section that starts at or before it.
 */
export function tieCounts(model: TieModel, sections: { id: string; start: number; parent: string | null }[]): Map<string, TieCount> {
  const counts = new Map<string, TieCount>(sections.map((s) => [s.id, { lean: 0, all: 0 }]));
  const byId = new Map(sections.map((s) => [s.id, s]));
  const ordered = [...sections].sort((a, b) => a.start - b.start);
  for (const t of model.order) {
    const byte = model.index.segments[model.segmentsOf[t][0]][0];
    let at: (typeof sections)[number] | undefined;
    for (const section of ordered) {
      if (section.start > byte) break;
      at = section;
    }
    for (let s = at; s; s = s.parent ? byId.get(s.parent) : undefined) {
      const count = counts.get(s.id)!;
      count.all++;
      if (model.index.ties[t].lean) count.lean++;
    }
  }
  return counts;
}

/** What a paper does with a step at this place, as a reader says it. */
export const ROLE_WORDS: Record<StatementRole, string> = {
  statement: "Stated",
  definition: "Defined",
  derivation: "Derived",
  explanation: "Explained",
  example: "Worked as an example",
  mention: "Mentioned",
};
