// Searching the names of the Lean declarations. The names load on the first typed query,
// never at startup, and an edition without the Lean index simply has no such results.

import { loadLeanNames, type DictionaryTerm, type LeanKind, type LeanNames } from "../api/lean";
import { inMainTree, isChallengeCopy, matchName } from "../lean/find";
import { holdsWord, spellings } from "./rank";

export interface LeanHit {
  name: string;
  /** The name after its namespaces. */
  short: string;
  kind: LeanKind;
  module: string;
  /** UTF-16 ranges of the matches in `name`. */
  marks: [number, number][];
  /** What the papers call it, where the dictionary has it. */
  term?: DictionaryTerm;
  /** How well the name matches: 0 is the exact name. */
  tier: number;
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
  for (const form of spellings(token)) {
    for (let at = folded.indexOf(form); at >= 0; at = folded.indexOf(form, at + 1)) {
      const end = at + form.length;
      if (startsPart(name, at) && (!whole || endsPart(name, end))) out.push([at, end]);
    }
  }
  return out;
}

/** Below the name tiers: a name that holds the words only apart, then a dictionary entry that says them. */
const SCATTERED = 6;
const IN_WORDS = 7;

/** Within a tier: matches in the short name, then short names over long. */
function score(name: string, short: string, hits: [number, number][][]): number {
  const shortFrom = name.length - short.length;
  let value = 0;
  if (hits.every((h) => h.some(([a]) => a >= shortFrom))) value += 400;
  if (hits.some((h) => h.some(([a]) => a === shortFrom))) value += 100;
  return value - name.length / 4;
}

function tierOf(folded: string, shortFolded: string, tokens: readonly string[]): number {
  const forms = [tokens, tokens.map((token) => spellings(token).at(-1) as string)];
  const tiers = forms.flatMap((words) => [words.join("_"), words.join("")]).map((joined) => matchName(folded, shortFolded, joined));
  return Math.min(...tiers.map((tier) => tier ?? SCATTERED));
}

export interface LeanSearch {
  /** The dictionary, by full name. */
  terms?: ReadonlyMap<string, DictionaryTerm>;
  /** Whether the papers rest on a name. */
  rests?(name: string): boolean;
}

/** Whether every word occurs in a dictionary entry's words or notation. */
function termSays(term: DictionaryTerm, tokens: readonly string[]): boolean {
  const text = `${term.words} ${term.tex ?? ""}`.toLowerCase();
  return tokens.every((token) => new RegExp(`(?:^|[^\\p{L}\\p{N}])${token.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}`, "u").test(text) || (token.startsWith("\\") && text.includes(token)));
}

/**
 * Declarations whose name holds every word of `q`, or whose dictionary entry says them, best
 * first: the exact name, then names that start with it, then names that hold it. A challenge
 * file's copy of a name is left out when the proof tree has it.
 */
export function searchLean(index: LeanNames, q: string, { terms, rests }: LeanSearch = {}): LeanHit[] {
  const tokens = q.toLowerCase().split(/\s+/u).filter(Boolean);
  if (!tokens.length) return [];
  const found: { hit: LeanHit; score: number }[] = [];
  const inTree = new Set<string>();
  for (const [name, , module] of index.names) if (!isChallengeCopy(index.modules[module])) inTree.add(name);
  for (const [name, kind, moduleIndex] of index.names) {
    const module = index.modules[moduleIndex];
    if (isChallengeCopy(module) && inTree.has(name)) continue;
    const folded = name.toLowerCase();
    const term = terms?.get(name);
    const hits = tokens.every((t) => holdsWord(folded, t)) ? tokens.map((t) => partHits(name, folded, t)) : null;
    const byName = hits !== null && !hits.some((h) => h.length === 0);
    if (!byName && !(term && termSays(term, tokens))) continue;
    const short = name.slice(name.lastIndexOf(".") + 1);
    found.push({
      hit: { name, short, kind, module, marks: byName ? hits.flat().sort((a, b) => a[0] - b[0]) : [], term, tier: byName ? tierOf(folded, short.toLowerCase(), tokens) : IN_WORDS },
      score: (byName ? score(name, short, hits) : 0) + (rests?.(name) ? 200 : 0) + (inMainTree(module) ? 5 : 0),
    });
  }
  return found.sort((a, b) => a.hit.tier - b.hit.tier || b.score - a.score || a.hit.name.localeCompare(b.hit.name)).map((f) => f.hit);
}

export interface ModuleHit {
  module: string;
  /** The file, as a reader knows it. */
  file: string;
  challenge: boolean;
}

/** Modules whose file name is what was typed, or starts with it. */
export function searchModules(index: LeanNames, q: string): ModuleHit[] {
  const typed = q.trim().toLowerCase().replace(/\.lean$/, "");
  if (typed.length < 3 || /\s/.test(typed)) return [];
  const hits = index.modules.flatMap((module) => {
    const file = module.slice(module.lastIndexOf(".") + 1);
    const lower = file.toLowerCase();
    return lower === typed || lower.startsWith(typed) ? [{ module, file: `${file}.lean`, challenge: isChallengeCopy(module), exact: lower === typed }] : [];
  });
  return hits.sort((a, b) => Number(b.exact) - Number(a.exact) || Number(b.challenge) - Number(a.challenge) || a.file.localeCompare(b.file)).map(({ exact: _exact, ...hit }) => hit);
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
