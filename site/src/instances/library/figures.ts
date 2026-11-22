// A library paper's figures. Most are image files in the reading copy, which the reader shows
// itself. A figure set in TikZ (no image link) is named by its label in instance.json "figures":
// either an image file of papers/<slot>/figures/, or one of the reader's shared figure
// components, which redraw a paper's figure (the SK papers' figures).
import { createElement, type ComponentType } from "react";
import type { FigureForKey } from "../types.ui";
import { figureImageSrc } from "../../reader/engine";
import { AccountsFigure } from "../../figures/AccountsFigure";
import { AreaFigure } from "../../figures/AreaFigure";
import { GapFigure } from "../../figures/GapFigure";
import { GapIngredientsFigure } from "../../figures/GapIngredientsFigure";
import { ReadingJourneyFigure } from "../../figures/ReadingJourneyFigure";
import { PAPER } from "./data";

const COMPONENTS: Record<string, ComponentType> = { AccountsFigure, AreaFigure, GapFigure, GapIngredientsFigure, ReadingJourneyFigure };

/** Caption phrases a figure with no label is known by: "caption:<phrase>" keys of instance.json "figures". */
const normalise = (text: string) => text.replace(/\s+/g, " ").trim().toLowerCase();

export const figureForKey: FigureForKey = (key, caption) => {
  const figures = PAPER.figures ?? {};
  const text = normalise(caption);
  const row = figures[key.trim()] ?? Object.entries(figures).find(([k]) => k.startsWith("caption:") && text.includes(normalise(k.slice(8))))?.[1];
  if (!row) return null;
  if ("component" in row) return COMPONENTS[row.component] ?? null;
  const src = figureImageSrc(row.slot, row.file);
  if (!src) return null;
  return function PaperFigure() {
    return createElement("img", { className: "paper-figure__image paper-figure__image--ink", src, alt: caption, loading: "lazy", decoding: "async" });
  };
};
