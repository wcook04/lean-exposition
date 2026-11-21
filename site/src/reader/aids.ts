// A paper's optional reading aids, published beside its edition as aids.json by the build
// (site/scripts/library-instance.mjs, from the instance's generated/glossary.json and
// generated/showcase.json): the glossary of formal conventions, each with the cards it bears on,
// and the showcase, a short list of worked examples to start from. A paper without them has no
// file, and every reader of this module then gets empty lists. Section aids are not here: they are
// set into the paper's text when it is prepared (engine.ts).

import { useEffect, useState } from "react";
import site from "@instance/site";

/** One formal convention, stated as mathematics. `cards` name what it bears on: `tie:<phrase id>`, `declaration:<Lean name>` or `result:<Lean name>`. */
export interface Convention {
  term: string;
  convention: string;
  differs_from_paper?: string;
  cards: string[];
}

/** One showcase card: what to open, why it is worth reading, and what the formal statement says. */
export interface ShowcaseCard {
  card: string;
  why: string;
  text: string;
}

export interface ReadingAids {
  glossary: Convention[];
  showcase: ShowcaseCard[];
}

const NONE: ReadingAids = { glossary: [], showcase: [] };
let loading: Promise<ReadingAids> | null = null;

export function loadAids(): Promise<ReadingAids> {
  if (!site.library) return Promise.resolve(NONE);
  loading ??= fetch(`${import.meta.env.BASE_URL}aids.json`)
    .then((r) => (r.ok ? r.json() : NONE))
    .then((data: Partial<ReadingAids>) => ({ glossary: Array.isArray(data.glossary) ? data.glossary : [], showcase: Array.isArray(data.showcase) ? data.showcase : [] }))
    .catch(() => NONE);
  return loading;
}

/** The paper's aids once loaded; empty lists until then and for a paper without any. */
export function useAids(wanted = true): ReadingAids {
  const [aids, setAids] = useState<ReadingAids>(NONE);
  useEffect(() => {
    if (!wanted) return;
    let live = true;
    void loadAids().then((found) => live && setAids(found));
    return () => {
      live = false;
    };
  }, [wanted]);
  return aids;
}

/** The conventions that bear on a card, given every key the card answers to, in the glossary's order. */
export function conventionsFor(aids: ReadingAids, keys: readonly string[]): Convention[] {
  if (!aids.glossary.length || !keys.length) return [];
  const wanted = new Set(keys);
  return aids.glossary.filter((entry) => entry.cards.some((card) => wanted.has(card)));
}

/**
 * The keys a phrase's card answers to: its own, and each Lean declaration it shows, as a declaration
 * and as a result. A paper may also name a card by its bare phrase id or Lean name, so those answer too.
 */
export function cardKeys(phrase: string | null | undefined, names: readonly string[]): string[] {
  return [...(phrase ? [`tie:${phrase}`, phrase] : []), ...names.flatMap((name) => [`declaration:${name}`, `result:${name}`, name])];
}

/** What a card names: linked words, a numbered result or a declaration; a bare id is taken as written. */
export function cardTarget(card: string): { kind: "tie" | "result" | "declaration" | "bare"; id: string } {
  const found = /^(tie|result|declaration):(.+)$/.exec(card);
  return found ? { kind: found[1] as "tie" | "result" | "declaration", id: found[2] } : { kind: "bare", id: card };
}
