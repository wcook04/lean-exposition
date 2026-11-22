// The changes layer on the page. In the adapted edition every paragraph that shows a change gets
// a light wash and, in the right margin, a dotted rule in ink headed by a small open square: the
// button "See what changed here". In the authors' paper nothing is marked; a paragraph the
// edition changes offers, in the same margin, "See this paragraph in the adapted edition".
// The reader renders each part's HTML once (PaperBody, lazily), so the marks are put on its
// blocks (by their source line, data-line) as the parts arrive, and put back if a part redraws.

import { useEffect } from "react";
import type { ChangeMap } from "./changes";

const SQUARE = '<svg viewBox="0 0 12 12" width="12" height="12" aria-hidden="true"><rect x="1.5" y="1.5" width="9" height="9" fill="none" stroke="currentColor" stroke-width="1.4"/></svg>';

/** The top-level blocks of the paper (those with a source line and no block ancestor that has one). */
function blocks(root: HTMLElement): HTMLElement[] {
  return Array.from(root.querySelectorAll<HTMLElement>(".part__text [data-line]")).filter(
    (el) => !el.parentElement?.closest(".part__text [data-line]"),
  );
}

export function useChangeMarks(
  root: React.RefObject<HTMLElement | null>,
  side: "adapted" | "authors" | null,
  map: ChangeMap | null,
  onOpen: (id: string, opener: HTMLElement) => void,
  onCounterpart: (line: number) => void,
) {
  useEffect(() => {
    const el = root.current;
    if (!el || !map || !side) return;
    // line ranges -> change id, on this side
    const ranges: { a: number; b: number; id: string }[] = [];
    for (const c of map.changes) {
      const lines = side === "adapted" ? c.adapted_lines : c.authors_lines;
      for (const [a, b] of lines) ranges.push({ a, b, id: c.id });
    }
    const owner = (line: number) => ranges.find((r) => r.a <= line && line < r.b)?.id ?? null;
    const kind = new Map(map.changes.map((c) => [c.id, c.kind]));
    const decorate = () => {
      const seen = new Set<string>();
      for (const block of blocks(el)) {
        const line = Number(block.dataset.line);
        const id = owner(line);
        if (!id) continue;
        const first = !seen.has(id);
        seen.add(id);
        if (side === "adapted") {
          if (block.dataset.change !== id) block.dataset.change = id;
          if (first && !block.querySelector(":scope > .change-mark")) {
            const button = document.createElement("button");
            button.type = "button";
            button.className = "change-mark";
            button.dataset.changeOpen = id;
            button.setAttribute("aria-label", `See what changed here (${id}, ${kind.get(id)?.replace(/-/g, " ")})`);
            button.title = "See what changed here";
            button.innerHTML = SQUARE;
            block.prepend(button);
          }
        } else if (first && !block.querySelector(":scope > .change-counterpart")) {
          block.dataset.changedInEdition = "";
          const button = document.createElement("button");
          button.type = "button";
          button.className = "change-counterpart";
          button.dataset.counterpartLine = String(line);
          button.setAttribute("aria-label", "See this paragraph in the adapted edition");
          button.title = "See this paragraph in the adapted edition";
          button.innerHTML = SQUARE;
          block.prepend(button);
        }
      }
    };
    decorate();
    let frame = 0;
    const observer = new MutationObserver(() => {
      cancelAnimationFrame(frame);
      frame = requestAnimationFrame(decorate);
    });
    observer.observe(el, { childList: true, subtree: true });
    const onClick = (event: MouseEvent) => {
      const target = (event.target as Element | null)?.closest<HTMLElement>("[data-change-open], [data-counterpart-line]");
      if (!target || !el.contains(target)) return;
      event.preventDefault();
      event.stopPropagation();
      if (target.dataset.changeOpen) onOpen(target.dataset.changeOpen, target);
      else onCounterpart(Number(target.dataset.counterpartLine));
    };
    el.addEventListener("click", onClick, true);
    return () => {
      observer.disconnect();
      cancelAnimationFrame(frame);
      el.removeEventListener("click", onClick, true);
    };
  }, [root, side, map, onOpen, onCounterpart]);
}

/**
 * The source line of the paragraph at the reading line: the block under a point in the middle of
 * the paper's column, just below the reading line, else the first one a little further down.
 */
export function lineInView(root: HTMLElement | null, readingTop: number): number | null {
  if (!root) return null;
  const column = (root.querySelector(".paper") ?? root).getBoundingClientRect();
  const x = column.left + Math.min(column.width / 2, 200);
  for (let y = readingTop + 24; y < window.innerHeight; y += 12) {
    const hit = document.elementFromPoint(x, y);
    const block = hit?.closest<HTMLElement>(".part__text [data-line]");
    if (!block || !root.contains(block)) continue;
    let top: HTMLElement = block;
    for (let up = top.parentElement?.closest<HTMLElement>(".part__text [data-line]"); up; up = up.parentElement?.closest<HTMLElement>(".part__text [data-line]")) top = up;
    return Number(top.dataset.line);
  }
  return null;
}
