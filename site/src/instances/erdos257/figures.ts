// The Erdős #257 papers draw no figure in React. A figure shows its own image file: the paper
// conversion ships it under papers/erdos257/<stage>/figures/ and the build serves it under
// paper-figures/<stage>/. The exposition's one figure is TikZ in the reading copy with no
// \includegraphics, so its file is named here by the figure's label.
import { createElement } from "react";
import type { FigureForKey } from "../types.ui";
import { figureImageSrc } from "../../reader/engine";

const FILES: Record<string, { stage: string; file: string }> = {
  "fig:cycle-mean": { stage: "expository", file: "cycle-mean.svg" },
};

export const figureForKey: FigureForKey = (key, caption) => {
  const row = FILES[key];
  const src = row ? figureImageSrc(row.stage, row.file) : null;
  if (!src) return null;
  return function PaperFigure() {
    return createElement("img", { className: "paper-figure__image paper-figure__image--ink", src, alt: caption, loading: "lazy", decoding: "async" });
  };
};
