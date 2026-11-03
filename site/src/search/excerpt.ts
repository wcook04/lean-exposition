// Search excerpts: placing the API's matches in a JavaScript string and
// turning an excerpt into short, readable text with the matches marked.
//
// The API reports matches as Unicode code-point offsets into the indexed
// text; the excerpt begins at `excerpt_start_character` in the same units.
// JavaScript strings index UTF-16 code units, so a character outside the
// Basic Multilingual Plane (𝔼, 𝟙, many emoji) counts once for the API and
// twice for String.prototype.slice. Every function here keeps a per-unit
// mark array alongside the text so later clean-up never moves a highlight.

export interface Match {
  start_character: number;
  end_character: number;
}

/** UTF-16 index of the code point at `codePoint` in `text` (clamped to the end). */
export function utf16IndexOf(text: string, codePoint: number): number {
  if (codePoint <= 0) return 0;
  let cp = 0;
  for (let i = 0; i < text.length; i++) {
    if (cp === codePoint) return i;
    const c = text.charCodeAt(i);
    if (c >= 0xd800 && c <= 0xdbff && i + 1 < text.length) {
      const d = text.charCodeAt(i + 1);
      if (d >= 0xdc00 && d <= 0xdfff) i++;
    }
    cp++;
  }
  return text.length;
}

/**
 * Convert matches (code points in the indexed text) to UTF-16 ranges within
 * the excerpt. Matches that lie wholly outside the excerpt are dropped;
 * matches cut by its edges are clipped.
 */
export function matchRanges(excerpt: string, excerptStart: number, matches: readonly Match[]): [number, number][] {
  const length = [...excerpt].length;
  const out: [number, number][] = [];
  for (const m of matches) {
    const from = Math.max(0, m.start_character - excerptStart);
    const to = Math.min(length, m.end_character - excerptStart);
    if (to <= from) continue;
    out.push([utf16IndexOf(excerpt, from), utf16IndexOf(excerpt, to)]);
  }
  return out.sort((a, b) => a[0] - b[0]);
}

export interface Marked {
  text: string;
  /** One flag per UTF-16 code unit of `text`. */
  marks: boolean[];
}

export function marked(text: string, ranges: readonly [number, number][]): Marked {
  const marks = new Array<boolean>(text.length).fill(false);
  for (const [a, b] of ranges) for (let i = a; i < b && i < text.length; i++) marks[i] = true;
  return { text, marks };
}

function slice(m: Marked, a: number, b = m.text.length): Marked {
  return { text: m.text.slice(a, b), marks: m.marks.slice(a, b) };
}

function concat(parts: Marked[]): Marked {
  return { text: parts.map((p) => p.text).join(""), marks: parts.flatMap((p) => p.marks) };
}

/**
 * Replace every match of `pattern` (which must have the `g` and `d` flags)
 * by the concatenation of the capture groups listed in `keep` (their marks
 * kept) followed by the unmarked `insert`; with no groups to keep, by
 * `insert` alone (marked if any replaced unit was).
 */
export function rewrite(m: Marked, pattern: RegExp, keep: number[], insert = ""): Marked {
  const parts: Marked[] = [];
  let at = 0;
  for (const match of m.text.matchAll(pattern)) {
    const start = match.index!;
    const end = start + match[0].length;
    parts.push(slice(m, at, start));
    if (keep.length) {
      for (const g of keep) {
        const span = match.indices?.[g];
        if (span) parts.push(slice(m, span[0], span[1]));
      }
      if (insert) parts.push({ text: insert, marks: new Array(insert.length).fill(false) });
    } else if (insert) {
      const hit = m.marks.slice(start, end).some(Boolean);
      parts.push({ text: insert, marks: new Array(insert.length).fill(hit) });
    }
    at = end;
  }
  parts.push(slice(m, at));
  return concat(parts);
}

/** Index of the first marked unit, or -1. */
export function firstMark(m: Marked): number {
  return m.marks.indexOf(true);
}

/** Trim leading and trailing whitespace. */
export function trim(m: Marked): Marked {
  const start = m.text.length - m.text.trimStart().length;
  const end = m.text.trimEnd().length;
  return end > start ? slice(m, start, end) : { text: "", marks: [] };
}

/**
 * Start the text a little before its first match, at a word boundary, so the
 * match is visible in a two-line preview. Returns whether text was cut.
 */
export function windowAround(m: Marked, before = 48): { text: Marked; cut: boolean } {
  const first = firstMark(m);
  if (first <= before + 12) return { text: m, cut: false };
  let start = first - before;
  const space = m.text.indexOf(" ", start);
  if (space >= 0 && space < first) start = space + 1;
  // Do not start inside a surrogate pair.
  const c = m.text.charCodeAt(start);
  if (c >= 0xdc00 && c <= 0xdfff) start++;
  return { text: slice(m, start), cut: true };
}

// ------------------------------------------------------------ record excerpts

const UNESCAPES: [RegExp, number[], string][] = [
  [/\\(["\\/])/dg, [1], ""],
  [/\\[nrt]/dg, [], " "],
];

function unescapedQuote(text: string, i: number): boolean {
  if (text[i] !== '"') return false;
  let slashes = 0;
  for (let j = i - 1; j >= 0 && text[j] === "\\"; j--) slashes++;
  return slashes % 2 === 0;
}

/**
 * Record excerpts are windows into serialized JSON. Find the string value
 * holding the first match and the key it belongs to, so a result can say
 * "Statement: …" instead of showing braces and quotes.
 */
export function jsonField(m: Marked): { key: string | null; value: Marked; cutStart: boolean; cutEnd: boolean } | null {
  const first = firstMark(m);
  if (first < 0) return null;
  const text = m.text;
  let open = -1;
  for (let i = first - 1; i >= 0; i--) {
    if (unescapedQuote(text, i)) {
      open = i;
      break;
    }
  }
  // The quote before the match might close a key or an earlier value: a string
  // value is opened by a quote preceded by `: `, `[` or `, `.
  if (open >= 0) {
    const before = text.slice(0, open).trimEnd();
    if (!/[:[,]$/.test(before)) open = -1;
  }
  let close = -1;
  for (let i = first; i < text.length; i++) {
    if (unescapedQuote(text, i)) {
      close = i;
      break;
    }
  }
  const valueStart = open >= 0 ? open + 1 : 0;
  const valueEnd = close >= 0 ? close : text.length;
  let key: string | null = null;
  if (open >= 0) {
    const head = text.slice(0, open);
    const direct = /"((?:[^"\\]|\\.)*)"\s*:\s*$/.exec(head);
    const inList = /"((?:[^"\\]|\\.)*)"\s*:\s*\[[^\]]*$/.exec(head);
    key = direct?.[1] ?? inList?.[1] ?? null;
  }
  let value = slice(m, valueStart, valueEnd);
  for (const [pattern, keep, insert] of UNESCAPES) value = rewrite(value, pattern, keep, insert);
  return { key, value, cutStart: open < 0, cutEnd: close < 0 };
}

// ---------------------------------------------------------- passage excerpts

const MARKDOWN: [RegExp, number[], string][] = [
  [/<!--[\s\S]*?(?:-->|$)/dg, [], ""], // comments, including passage markers
  [/^[^<>$]*?"\s*\/?>/dg, [], ""], // the end of a tag cut by the excerpt's start
  [/<\/?(?:span|a|div|sup|sub|em|strong|b|i|br|img|code|abbr|small)\b[^>]*(?:>|$)/dg, [], ""], // HTML tags, including one cut by the end
  [/^[ \t]*#{1,6}[ \t]+(.*?[.?!:])[ \t]*$/dgm, [1], " "], // headings that end a sentence
  [/^[ \t]*#{1,6}[ \t]+(.*?)[ \t]*$/dgm, [1], ". "], // other headings read as one
  [/!?\[([^\]\n]*)\]\([^)\n]*\)/dg, [1], ""], // [text](url)
  [/\[([^\]\n]*)\]\[[^\]\n]*\]/dg, [1], ""], // [text][ref]
  [/(\*\*|__)(?=\S)([^*\n]+?)\1/dg, [2], ""], // strong
  [/(?<![\w*])\*(?=\S)([^*\n]+?)\*(?![\w*])/dg, [1], ""], // emphasis
  [/`([^`\n]+)`/dg, [1], ""], // code
  [/\s+/dg, [], " "], // whitespace, including line breaks
];

/** Passage text as plain prose: Markdown markup removed, marks preserved. */
export function plainMarkdown(m: Marked): Marked {
  let out = m;
  for (const [pattern, keep, insert] of MARKDOWN) out = rewrite(out, pattern, keep, insert);
  return out;
}

export type Segment = { kind: "text"; text: string; mark: boolean } | { kind: "math"; tex: string; display: boolean; mark: boolean };

const MATH = /\$\$([\s\S]+?)\$\$|\$(?=[^\s$])((?:\\.|[^$\\\n])+?)(?<=[^\s\\])\$(?!\d)/dg;

/**
 * Split text into runs of plain text (merged by mark) and TeX math. A math
 * span is marked as a whole when any part of it matched. A lone `$` left at
 * either cut edge (the excerpt began or ended inside a formula) is removed
 * with the formula fragment beside it.
 */
export function segments(m: Marked, cutStart: boolean, cutEnd: boolean): Segment[] {
  const out: Segment[] = [];
  const pushText = (part: Marked) => {
    let text = part.text;
    let marks = part.marks;
    if (cutStart && out.length === 0) {
      const dollar = text.indexOf("$");
      if (dollar >= 0 && (text.match(/\$/g) ?? []).length % 2 === 1) {
        text = text.slice(dollar + 1);
        marks = marks.slice(dollar + 1);
      }
    }
    for (let i = 0; i < text.length; i++) {
      const last = out[out.length - 1];
      if (last && last.kind === "text" && last.mark === marks[i]) last.text += text[i];
      else out.push({ kind: "text", text: text[i], mark: marks[i] });
    }
  };
  let at = 0;
  for (const match of m.text.matchAll(MATH)) {
    const start = match.index!;
    const end = start + match[0].length;
    pushText(slice(m, at, start));
    const display = match[1] !== undefined;
    out.push({ kind: "math", tex: (display ? match[1] : match[2]).trim(), display: false, mark: m.marks.slice(start, end).some(Boolean) });
    at = end;
  }
  pushText(slice(m, at));
  if (cutEnd) {
    const last = out[out.length - 1];
    if (last && last.kind === "text") {
      const dollar = last.text.lastIndexOf("$");
      if (dollar >= 0) last.text = last.text.slice(0, dollar).replace(/\s*\$*\s*$/, "");
    }
  }
  return out.filter((s) => s.kind === "math" || s.text !== "");
}

// ------------------------------------------------------------- one result

export interface ExcerptSource {
  table: string;
  excerpt?: string;
  excerpt_start_character?: number;
  excerpt_truncated?: boolean;
  matches?: Match[];
}

export interface PreparedExcerpt {
  /** The record field the match is in, for record tables. */
  field: string | null;
  segments: Segment[];
  cutStart: boolean;
  cutEnd: boolean;
}

const RECORD_TABLES = new Set(["nodes", "edges", "citations", "sources", "evidence"]);

/** Turn one search result's excerpt into marked, readable segments. */
export function prepareExcerpt(item: ExcerptSource): PreparedExcerpt | null {
  const excerpt = item.excerpt ?? "";
  if (!excerpt) return null;
  const start = item.excerpt_start_character ?? 0;
  const length = [...excerpt].length;
  let cutStart = start > 0;
  let cutEnd = !!item.excerpt_truncated && !(start > 0 && length < 270);
  let text = marked(excerpt, matchRanges(excerpt, start, item.matches ?? []));
  let field: string | null = null;
  if (RECORD_TABLES.has(item.table)) {
    const found = jsonField(text);
    if (!found) return null;
    field = found.key;
    text = rewrite(found.value, /\s+/dg, [], " ");
    cutStart = found.cutStart && cutStart;
    cutEnd = found.cutEnd && cutEnd;
  } else {
    text = plainMarkdown(text);
  }
  text = trim(text);
  const windowed = windowAround(text);
  return { field, segments: segments(windowed.text, cutStart || windowed.cut, cutEnd), cutStart: cutStart || windowed.cut, cutEnd };
}
