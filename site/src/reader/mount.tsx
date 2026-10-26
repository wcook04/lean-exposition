// Mount the redrawn paper figures into the slots the rendering engine leaves
// where a TikZ figure stood in the manuscript.

import { createRoot, type Root } from "react-dom/client";
import { figureForKey } from "../figures/registry";

export function mountFigures(container: HTMLElement): () => void {
  const roots: Root[] = [];
  const slots: HTMLElement[] = [];
  container.querySelectorAll<HTMLElement>("[data-figure-slot]").forEach((slot) => {
    if (slot.dataset.mounted) return;
    const key = slot.dataset.figureSlot ?? "";
    const caption = slot.closest("figure")?.querySelector("figcaption")?.textContent ?? "";
    const Figure = figureForKey(key, caption);
    if (!Figure) {
      slot.dataset.missing = "true";
      return;
    }
    slot.dataset.mounted = "true";
    slots.push(slot);
    const root = createRoot(slot);
    root.render(<Figure />);
    roots.push(root);
  });
  return () => {
    const pending = roots.splice(0);
    slots.forEach((slot) => delete slot.dataset.mounted);
    setTimeout(() => pending.forEach((root) => root.unmount()), 0);
  };
}
