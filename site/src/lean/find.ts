// Which declaration a typed name means. Exact names come first, then names that start with
// what was typed, then names that hold it, so the first result is the one a reader who knows
// the name wanted. Used by the Lean page's find box and by search. No dependencies.

/** The tiers, best first. */
const EXACT = 0;
/** The end of the dotted name: `SKValue.parisi`. */
const TAIL = 1;
const PREFIX = 2;
const FULL_PREFIX = 3;
const SUBSTRING = 4;
const FULL_SUBSTRING = 5;

/** How well `query` matches a name, or null. `lowerName` and `lowerShort` are lower case. */
export function matchName(lowerName: string, lowerShort: string, query: string): number | null {
  if (lowerShort === query || lowerName === query) return EXACT;
  if (lowerName.endsWith(`.${query}`)) return TAIL;
  if (lowerShort.startsWith(query)) return PREFIX;
  if (lowerName.startsWith(query)) return FULL_PREFIX;
  if (lowerShort.includes(query)) return SUBSTRING;
  if (lowerName.includes(query)) return FULL_SUBSTRING;
  return null;
}

/** The Comparator challenge files repeat names from the proof trees, and rank after them. */
export const isChallengeCopy = (module: string) => module.startsWith("ComparatorChallenges");

/** Between two proof trees that share a name, the main theorem's tree comes first. */
export const inMainTree = (module: string) => module.includes(".SKSupport");

export interface Nameable {
  name: string;
  short: string;
  module: string;
}

/**
 * Best first. Within a tier: a name typed with the same capitals, a declaration the papers
 * rest on, one in the proof trees over its challenge copy, then the shorter name.
 */
export function compareNames(a: Nameable & { tier: number }, b: Nameable & { tier: number }, typed: string, rests: (name: string) => boolean): number {
  return (
    a.tier - b.tier ||
    Number(b.short === typed || b.name === typed) - Number(a.short === typed || a.name === typed) ||
    Number(rests(b.name)) - Number(rests(a.name)) ||
    Number(isChallengeCopy(a.module)) - Number(isChallengeCopy(b.module)) ||
    Number(inMainTree(b.module)) - Number(inMainTree(a.module)) ||
    a.short.length - b.short.length ||
    a.name.localeCompare(b.name) ||
    a.module.localeCompare(b.module)
  );
}

export interface Ranked<T> {
  rows: T[];
  total: number;
}

/**
 * Rank declarations for a query. Several words must each match; the first decides the tier,
 * and a name that holds them all only across its namespaces comes last.
 */
export function rankNames<T extends Nameable>(rows: readonly T[], lower: readonly string[], query: string, limit: number, rests: (name: string) => boolean = () => false): Ranked<T> {
  const typed = query.trim();
  const words = typed.toLowerCase().split(/\s+/).filter(Boolean);
  if (!words.length) return { rows: [], total: 0 };
  const hits: (T & { tier: number })[] = [];
  for (let i = 0; i < rows.length; i++) {
    const lowerName = lower[i];
    if (!words.every((word) => lowerName.includes(word))) continue;
    const row = rows[i];
    const lowerShort = lowerName.slice(lowerName.lastIndexOf(".") + 1);
    const tier = matchName(lowerName, lowerShort, words[0]) as number;
    hits.push({ ...row, tier: words.length > 1 ? tier + 1 : tier });
  }
  hits.sort((a, b) => compareNames(a, b, typed, rests));
  return { rows: hits.slice(0, limit), total: hits.length };
}
