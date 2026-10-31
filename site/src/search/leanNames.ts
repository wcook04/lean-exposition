// Searching the names of the Lean declarations. The names load on the first typed query,
// never at startup, and an edition without the Lean index simply has no such results.

import { loadLeanNames, type LeanKind, type LeanNames } from "../api/lean";

export interface LeanHit {
  name: string;
  /** The name after its namespaces. */
  short: string;
  kind: LeanKind;
  module: string;
  /** UTF-16 ranges of the matches in `name`. */
  marks: [number, number][];
}

let names: Promise<LeanNames | null> | null = null;

export function leanNames(): Promise<LeanNames | null> {
  names ??= loadLeanNames().catch(() => null);
  return names;
}

/** Whether a word of a Lean name starts at `at`: after a dot or underscore, or at a capital after a lower-case letter. */
function startsPart(name: string, at: number): boolean {
  if (at === 0) return true;
  const before = name[at - 1];
  if (/[._'’]/.test(before)) return true;
  return /[\p{Ll}\p{N}]/u.test(before) && /\p{Lu}/u.test(name[at]);
}

function endsPart(name: string, end: number): boolean {
  if (end >= name.length) return true;
  return /[._'’]/.test(name[end]) || (/\p{Lu}/u.test(name[end]) && /[\p{Ll}\p{N}]/u.test(name[end - 1]));
}

function partHits(name: string, folded: string, token: string): [number, number][] {
  const out: [number, number][] = [];
  const whole = Array.from(token).length <= 2;
  for (let at = folded.indexOf(token); at >= 0; at = folded.indexOf(token, at + 1)) {
    const end = at + token.length;
    if (startsPart(name, at) && (!whole || endsPart(name, end))) out.push([at, end]);
  }
  return out;
}

/** Best first: the exact short name, then matches in the short name, then short names over long. */
function score(name: string, short: string, tokens: readonly string[], hits: [number, number][][]): number {
  const shortFrom = name.length - short.length;
  const joined = tokens.join("_");
  let value = 0;
  if (short.toLowerCase() === joined || short.toLowerCase() === tokens.join("")) value += 1000;
  if (name.toLowerCase() === joined) value += 1000;
  if (hits.every((h) => h.some(([a]) => a >= shortFrom))) value += 400;
  if (hits.some((h) => h.some(([a]) => a === shortFrom))) value += 100;
  return value - name.length / 4;
}

/** Declarations whose name holds every word of `q`, best first. */
export function searchLean(index: LeanNames, q: string): LeanHit[] {
  const tokens = q.toLowerCase().split(/\s+/u).filter(Boolean);
  if (!tokens.length) return [];
  const found: { hit: LeanHit; score: number }[] = [];
  for (const [name, kind, module] of index.names) {
    const folded = name.toLowerCase();
    if (!tokens.every((t) => folded.includes(t))) continue;
    const hits = tokens.map((t) => partHits(name, folded, t));
    if (hits.some((h) => h.length === 0)) continue;
    const short = name.slice(name.lastIndexOf(".") + 1);
    found.push({ hit: { name, short, kind, module: index.modules[module], marks: hits.flat().sort((a, b) => a[0] - b[0]) }, score: score(name, short, tokens, hits) });
  }
  return found.sort((a, b) => b.score - a.score || a.hit.name.localeCompare(b.hit.name)).map((f) => f.hit);
}

/** The name in pieces, each marked or not, for highlighting. */
export function markedPieces(text: string, marks: readonly [number, number][]): { text: string; mark: boolean }[] {
  const pieces: { text: string; mark: boolean }[] = [];
  let at = 0;
  for (const [a, b] of marks) {
    if (a < at) continue;
    if (a > at) pieces.push({ text: text.slice(at, a), mark: false });
    pieces.push({ text: text.slice(a, b), mark: true });
    at = b;
  }
  if (at < text.length) pieces.push({ text: text.slice(at), mark: false });
  return pieces;
}
