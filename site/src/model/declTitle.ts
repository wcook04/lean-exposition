// A declaration's name in plain words. Nobody reads `approxValue_derivative_uniform`, so
// wherever a person reads, a declaration goes by a plain title and the raw name is small print.
// In order: the title authored for it (`names` in the alignment); the short title of the record
// that links it most directly; the dictionary's words for it. A name with none of these has no
// plain title, and the caller says so by showing the name.

interface Row {
  name: string;
  relation: string;
}

export interface TitleSources {
  names?: Record<string, string>;
  records: Record<string, { short: string; lean: readonly Row[] }>;
  dictionary: readonly { name: string; words: string }[];
}

/** Most direct first: a record that states a declaration names it better than one it is part of. */
const STRENGTH = ["states", "contains", "proof", "part", "defines"];

const memo = new WeakMap<object, Map<string, string>>();

export function declTitles(sources: TitleSources): Map<string, string> {
  let titles = memo.get(sources);
  if (titles) return titles;
  titles = new Map(Object.entries(sources.names ?? {}));
  const rank = new Map<string, number>();
  const fromRecord = new Map<string, string>();
  for (const record of Object.values(sources.records)) {
    for (const row of record.lean) {
      const r = STRENGTH.indexOf(row.relation);
      if (record.short && r < (rank.get(row.name) ?? Infinity)) {
        rank.set(row.name, r);
        fromRecord.set(row.name, record.short);
      }
    }
  }
  const words = new Map(sources.dictionary.map((term) => [term.name, term.words.replace(/\.\s*$/, "")]));
  for (const [name, title] of fromRecord) if (!titles.has(name)) titles.set(name, title);
  for (const [name, title] of words) if (!titles.has(name)) titles.set(name, title);
  memo.set(sources, titles);
  return titles;
}

/** The plain title, or null where there is none. */
export function declTitle(sources: TitleSources | null | undefined, name: string): string | null {
  return (sources && declTitles(sources).get(name)) ?? null;
}
