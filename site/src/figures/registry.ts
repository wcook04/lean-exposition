// Maps a figure slot from the rendering engine to its redrawn component.
// Slots are keyed by the figure's \label when it has one, else by a hash of
// its source. Hashes change between editions, so we match by label first and
// then by a distinctive phrase of the paper's caption.
import type { ComponentType } from "react";
import { AccountsFigure } from "./AccountsFigure";
import { AreaFigure } from "./AreaFigure";
import { GapFigure } from "./GapFigure";
import { GapIngredientsFigure } from "./GapIngredientsFigure";
import { ReadingJourneyFigure } from "./ReadingJourneyFigure";

const BY_LABEL: Record<string, ComponentType> = {
  "fig:support-increments": GapFigure,
  "fig:shared-claim": AccountsFigure,
  "fig:joint-inputs": GapIngredientsFigure,
  "fig:excursion-return": ReadingJourneyFigure,
};

/** Caption phrases, compared after whitespace and case normalisation. */
const BY_CAPTION: [string, ComponentType][] = [
  ["the same candidate in two representations", GapFigure],
  ["strictness is indispensable", AreaFigure],
  ["why three papers need only one shared record", AccountsFigure],
  ["three passages, one recorded claim", AccountsFigure],
  ["which ingredients does the contradiction use", GapIngredientsFigure],
  ["leave an estimate, recover its argument, return", ReadingJourneyFigure],
];

function normalise(text: string): string {
  return text.replace(/\s+/g, " ").trim().toLowerCase();
}

export function figureForKey(key: string, caption: string): ComponentType | null {
  const byLabel = BY_LABEL[key.trim()];
  if (byLabel) return byLabel;
  const text = normalise(caption);
  for (const [phrase, component] of BY_CAPTION) if (text.includes(phrase)) return component;
  return null;
}
