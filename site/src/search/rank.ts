// What a reader's words find, and in what order. The API's search is literal: every word
// must occur somewhere, inside another word or not. That stays as it is. This file is the
// client's reading of it: a word counts only at the start of a word (a word of one or two
// letters, or a number, only as the whole word), and results are ordered by whether the
// words occur in the title and how close together and in order they occur.
//
// In the published edition the full indexed text is at hand, so results are found, ordered
// and excerpted from it. Against the local server only the API's excerpts exist: its rows are
// kept, and they are ordered and highlighted by what their excerpts show.

import { query } from "../api/client";
import type { Page, SearchItem } from "../api/types";

type Fold = (text: string) => string;

/** A word as the reader typed it, reduced to what is compared. */
export function tokensOf(q: string, fold: Fold = lower): string[] {
  return fold(q).split(/\s+/u).filter(Boolean);
}

function lower(text: string): string {
  return text.toLowerCase();
}

const WORD = /[\p{L}\p{N}]/u;

/** Stems that take -ise in British spelling and -ize in American. */
const IZE = /(minim|maxim|optim|normal|regular|general|character|stabil|real|organ|recogn|parametr|discret|symmetr|factor|local|penal|central|summar|util|uniform|marginal)(is|iz)/;
const PAIRS: [string, string][] = [["neighbour", "neighbor"], ["colour", "color"], ["behaviour", "behavior"], ["centre", "center"], ["fibre", "fiber"], ["analyse", "analyze"], ["modelling", "modeling"], ["labelled", "labeled"]];

/** A word and its other spelling, British or American, so either finds both. */
export function spellings(token: string): string[] {
  const forms = new Set([token]);
  const stem = IZE.exec(token);
  if (stem) {
    forms.add(token.replace(IZE, "$1is"));
    forms.add(token.replace(IZE, "$1iz"));
  }
  for (const [british, american] of PAIRS) {
    if (token.includes(british)) forms.add(token.replace(british, american));
    if (token.includes(american)) forms.add(token.replace(american, british));
  }
  return [...forms];
}

/** One spelling for comparing whole titles. */
export const canonicalWord = (word: string) => spellings(word).sort()[0];

/** Whether a text holds a word in either spelling; a cheap test before the real one. */
export const holdsWord = (text: string, token: string) => spellings(token).some((form) => text.includes(form));

/** A token this short, or made of digits, would otherwise match inside "atom" or "25". */
function wholeWordOnly(token: string): boolean {
  return Array.from(token).length <= 2 || /^[\p{N}.,/]+$/u.test(token);
}

/** Whether the character before `at` ends a word: nothing, punctuation, or an escape like \n. */
function startsWord(text: string, at: number): boolean {
  if (at === 0) return true;
  const before = text.slice(Math.max(0, at - 2), at);
  if (/\\[nrt"]$/.test(before)) return true;
  const last = Array.from(before).at(-1)!;
  return !WORD.test(last);
}

function endsWord(text: string, end: number): boolean {
  if (end >= text.length) return true;
  return !WORD.test(Array.from(text.slice(end, end + 2))[0]);
}

export interface Hit {
  /** Which of the query's words this is. */
  token: number;
  start: number;
  end: number;
  whole: boolean;
  /** "two" for a typed 2: it brings the excerpt to the right place but is not a match, so it is not marked. */
  alias?: boolean;
}

const NUMBER_WORDS: Record<string, string> = { "1": "one", "2": "two", "3": "three", "4": "four", "5": "five", "6": "six", "7": "seven", "8": "eight", "9": "nine", "10": "ten" };

/** Every real occurrence of each token in `text`, in order of position. `skip` excludes spans. */
export function wordHits(text: string, tokens: readonly string[], skip: readonly [number, number][] = []): Hit[] {
  const hits: Hit[] = [];
  tokens.forEach((token, index) => {
    const whole = wholeWordOnly(token);
    for (const form of spellings(token)) {
      for (let at = text.indexOf(form); at >= 0; at = text.indexOf(form, at + 1)) {
        const end = at + form.length;
        if (!startsWord(text, at)) continue;
        const isWhole = endsWord(text, end);
        if (whole && !isWhole) continue;
        if (skip.some(([a, b]) => at >= a && at < b)) continue;
        hits.push({ token: index, start: at, end, whole: isWhole });
      }
    }
    const word = NUMBER_WORDS[token];
    if (!word) return;
    for (let at = text.indexOf(word); at >= 0; at = text.indexOf(word, at + 1)) {
      const end = at + word.length;
      if (startsWord(text, at) && endsWord(text, end) && !skip.some(([a, b]) => at >= a && at < b)) hits.push({ token: index, start: at, end, whole: true, alias: true });
    }
  });
  return hits.sort((a, b) => a.start - b.start || a.token - b.token);
}

export interface Cluster {
  start: number;
  end: number;
  /** The tokens occur here in the order typed. */
  ordered: boolean;
}

/** The shortest stretch holding every token, and the shortest holding them in order. */
export function closestCluster(hits: readonly Hit[], tokenCount: number): { any: Cluster; ordered: Cluster | null } | null {
  const present = new Set(hits.filter((h) => !h.alias).map((h) => h.token));
  if (present.size < tokenCount) return null;
  // Shortest window holding each token at least once.
  const seen = new Array<number>(tokenCount).fill(0);
  let distinct = 0;
  let left = 0;
  let any: Cluster | null = null;
  for (let right = 0; right < hits.length; right++) {
    if (seen[hits[right].token]++ === 0) distinct++;
    while (distinct === tokenCount) {
      const span = { start: hits[left].start, end: hits[right].end, ordered: false };
      if (!any || span.end - span.start < any.end - any.start) any = span;
      if (--seen[hits[left].token] === 0) distinct--;
      left++;
    }
  }
  // Shortest run in the order typed, starting from each occurrence of the first token.
  let ordered: Cluster | null = null;
  for (const first of hits) {
    if (first.token !== 0) continue;
    let end = first.end;
    let at = first.end;
    let complete = true;
    for (let token = 1; token < tokenCount; token++) {
      const next = hits.find((h) => h.token === token && h.start >= at);
      if (!next) {
        complete = false;
        break;
      }
      end = next.end;
      at = next.end;
    }
    if (complete && (!ordered || end - first.start < ordered.end - ordered.start)) ordered = { start: first.start, end, ordered: true };
  }
  return any ? { any, ordered } : null;
}

/** Records are stored as JSON: its keys are not words of the record, and its ids say little. */
function jsonParts(text: string): { keys: [number, number][]; label: [number, number] | null; idFields: [number, number][] } {
  const keys: [number, number][] = [];
  const fields: { name: string; from: number }[] = [];
  const pattern = /"((?:[^"\\]|\\.)*)"\s*:\s*/g;
  for (const m of text.matchAll(pattern)) {
    keys.push([m.index!, m.index! + m[0].length]);
    fields.push({ name: m[1], from: m.index! + m[0].length });
  }
  let label: [number, number] | null = null;
  const idFields: [number, number][] = [];
  fields.forEach((field, i) => {
    const to = i + 1 < fields.length ? fields[i + 1].from : text.length;
    if (field.name === "label" || field.name === "title") label ??= [field.from, to];
    if (field.name === "id" || field.name.endsWith("_ids") || field.name.endsWith("_id")) idFields.push([field.from, to]);
  });
  return { keys, label, idFields };
}

const JSON_TABLES = new Set(["nodes", "edges", "citations", "sources", "evidence"]);

export interface Scored {
  tokens: readonly string[];
  score: number;
  hits: Hit[];
  /** The stretch an excerpt should show. */
  focus: number;
}

/**
 * The score of one row's text, or null when a token has no real occurrence.
 * `folded` is the row's text after folding; the title is its label or title field.
 */
export function scoreText(table: string, folded: string, tokens: readonly string[]): Scored | null {
  const json = JSON_TABLES.has(table) ? jsonParts(folded) : null;
  const hits = wordHits(folded, tokens, json?.keys);
  const cluster = closestCluster(hits, tokens.length);
  if (!cluster) return null;
  const title = table === "sections" ? ([0, folded.length] as [number, number]) : json?.label ?? null;
  const titleHits = title ? hits.filter((h) => !h.alias && h.start >= title[0] && h.start < title[1]) : [];
  const inTitle = new Set(titleHits.map((h) => h.token)).size === tokens.length;
  const asTyped = tokens.join(" ").length;
  const closeness = (c: Cluster) => 1 / (1 + Math.max(0, c.end - c.start - asTyped) / 30);
  const inIds = json ? hits.filter((h) => json.idFields.some(([a, b]) => h.start >= a && h.start < b)).length : 0;
  let score = 0;
  if (inTitle) score += 1000;
  score += 300 * closeness(cluster.any);
  if (cluster.ordered) score += 500 * closeness(cluster.ordered);
  score += 40 * new Set(hits.filter((h) => h.whole && !h.alias).map((h) => h.token)).size / tokens.length;
  score += Math.min(10, hits.length - inIds);
  if (inIds === hits.length) score -= 400;
  const best = cluster.ordered && cluster.ordered.end - cluster.ordered.start <= (cluster.any.end - cluster.any.start) * 1.5 ? cluster.ordered : cluster.any;
  return { tokens, score, hits, focus: inTitle ? titleHits[0].start : best.start };
}

// ------------------------------------------------------------- the published text

export interface IndexRow {
  ref: string;
  table: string;
  label?: string | null;
  text: string;
  [key: string]: unknown;
}

interface SearchFile {
  rows: IndexRow[];
  casefold: Record<string, string>;
}

const STATIC = import.meta.env.VITE_STATIC_EDITION === "true";
let file: Promise<SearchFile & { fold: Fold }> | null = null;

/** The captured edition's search file, the one the static transport reads. Fetched on the first query. */
function searchFile(): Promise<SearchFile & { fold: Fold }> {
  const root = `${import.meta.env.BASE_URL}edition/`;
  const json = (name: string) => fetch(root + name).then((r) => {
    if (!r.ok) throw new Error(`Could not load the captured edition (${r.status}).`);
    return r.json();
  });
  file ??= json("index.json").then((index: { search: string }) => json(index.search)).then((found: SearchFile) => ({ ...found, fold: foldWith(found.casefold) })).catch((error: unknown) => {
    file = null;
    throw error;
  });
  return file;
}

const EXCERPT = 280;
const LEAD = 80;

/** A row as a search result: the excerpt shows the closest stretch, and only real matches are marked. */
export function itemFrom(row: IndexRow, folded: string, scored: Scored): SearchItem {
  // Offsets into the folded text. Folding keeps them for all but rare characters, and those only move a mark.
  const toPoint = codePoints(folded);
  const points = Array.from(row.text);
  const focus = toPoint(scored.focus);
  const start = Math.min(Math.max(0, focus - LEAD), Math.max(0, points.length - EXCERPT));
  const { text: _text, ...rest } = row;
  return {
    ...rest,
    excerpt: points.slice(start, start + EXCERPT).join(""),
    excerpt_truncated: points.length > EXCERPT,
    excerpt_start_character: start,
    matches: scored.hits.filter((h) => !h.alias).map((h) => ({ token: scored.tokens[h.token], start_character: toPoint(h.start), end_character: toPoint(h.end) })),
  } as unknown as SearchItem;
}

/** A lookup from UTF-16 index to code-point index, in one pass over the text. */
function codePoints(text: string): (unit: number) => number {
  if (!/[\ud800-\udbff]/.test(text)) return (unit) => unit;
  const table = new Int32Array(text.length + 1);
  let point = 0;
  for (let i = 0; i < text.length; i++) {
    table[i] = point;
    const c = text.charCodeAt(i);
    if (c >= 0xd800 && c <= 0xdbff && i + 1 < text.length) table[++i] = point;
    point++;
  }
  table[text.length] = point;
  return (unit) => table[unit];
}

function foldWith(casefold: Record<string, string>): Fold {
  const known = new Map<string, string>();
  return (text) => {
    let out = known.get(text);
    if (out === undefined) {
      out = "";
      for (const c of text) out += casefold[c] ?? c;
      known.set(text, out);
    }
    return out;
  };
}

/** Rank `rows`, best first; rows without a real match are dropped. Ties keep their given order. */
export function rankRows(rows: readonly IndexRow[], q: string, fold: Fold = lower): Map<string, SearchItem[]> {
  const tokens = tokensOf(q, fold);
  const found: { table: string; item: () => SearchItem; score: number; i: number }[] = [];
  rows.forEach((row, i) => {
    const folded = fold(row.text);
    if (!tokens.every((t) => holdsWord(folded, t))) return;
    const scored = scoreText(row.table, folded, tokens);
    if (scored) found.push({ table: row.table, item: () => itemFrom(row, folded, scored), score: scored.score, i });
  });
  found.sort((a, b) => b.score - a.score || a.i - b.i);
  const by = new Map<string, SearchItem[]>();
  for (const f of found) {
    if (!by.has(f.table)) by.set(f.table, []);
    by.get(f.table)!.push(f.item());
  }
  return by;
}

// ---------------------------------------------------------------- the local server

const PAGE = 200;

async function allOf(q: string, table: string, signal?: AbortSignal): Promise<SearchItem[]> {
  const items: SearchItem[] = [];
  for (let offset = 0; ; offset += PAGE) {
    const { data } = await query<Page<SearchItem>>("/search", { q, table, limit: PAGE, offset }, signal);
    items.push(...data.items);
    if (items.length >= data.total || data.items.length === 0) return items;
  }
}

/** Order server rows by their excerpts, which is all the server returns, and mark only real matches. */
export function rankExcerpts(items: readonly SearchItem[], q: string): SearchItem[] {
  const tokens = tokensOf(q);
  const scored = items.map((item, i) => {
    const excerpt = lower(item.excerpt ?? "");
    const result = scoreText(item.table, excerpt, tokens);
    const hits = wordHits(excerpt, tokens).filter((h) => !h.alias);
    const offset = (item.excerpt_start_character as number | undefined) ?? 0;
    const matches = hits.map((h) => ({ token: tokens[h.token], start_character: offset + Array.from(excerpt.slice(0, h.start)).length, end_character: offset + Array.from(excerpt.slice(0, h.end)).length }));
    return { item: { ...item, matches } as SearchItem, score: result?.score ?? -1, i };
  });
  return scored.sort((a, b) => b.score - a.score || a.i - b.i).map((s) => s.item);
}

// ---------------------------------------------------------------------- the entry

const cache = new Map<string, Promise<Map<string, SearchItem[]>>>();

/** Every result for `q`, by table, best first. */
export function rankedSearch(q: string, tables: readonly string[], signal?: AbortSignal): Promise<Map<string, SearchItem[]>> {
  const known = cache.get(q);
  if (known) return known;
  const work = STATIC
    ? searchFile().then((index) => rankRows(index.rows.filter((row) => tables.includes(row.table)), q, index.fold))
    : Promise.all(tables.map((table) => allOf(q, table, signal).then((items) => [table, rankExcerpts(items, q)] as const))).then((pairs) => new Map(pairs));
  work.catch(() => cache.delete(q));
  if (STATIC) cache.set(q, work);
  return work;
}
