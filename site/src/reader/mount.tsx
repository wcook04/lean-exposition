// Mount the paper figures into the slots the rendering engine leaves where a figure stood in
// the manuscript: the instance's redrawn React figure when it has one for the slot (the SK
// site redraws its TikZ figures), otherwise the figure's own image file, when the paper
// ships one (data-figure-image, set by the engine to a path under paper-figures/).

import { createRoot, type Root } from "react-dom/client";
import { figureForKey } from "@instance/figures";
import { FIGURE_SIZES } from "virtual:paper-figure-sizes";

export function mountFigures(container: HTMLElement): () => void {
  const roots: Root[] = [];
  const slots: HTMLElement[] = [];
  const images: HTMLImageElement[] = [];
  container.querySelectorAll<HTMLElement>("[data-figure-slot]").forEach((slot) => {
    if (slot.dataset.mounted) return;
    const key = slot.dataset.figureSlot ?? "";
    const caption = slot.closest("figure")?.querySelector("figcaption")?.textContent ?? "";
    const Figure = figureForKey(key, caption);
    if (!Figure) {
      const src = slot.dataset.figureImage;
      if (src) {
        const img = document.createElement("img");
        img.className = "paper-figure__image";
        img.src = src;
        // Its own size, so the box is held before the file loads and nothing under it moves.
        const size = FIGURE_SIZES[src.split("/paper-figures/").pop() ?? ""];
        if (size) {
          img.width = Math.round(size[0]);
          img.height = Math.round(size[1]);
        }
        // The caption below says what the picture shows; the alt text repeats the paper's own words for it.
        img.alt = slot.dataset.figureAlt ?? caption;
        img.loading = "lazy";
        img.decoding = "async";
        slot.dataset.mounted = "true";
        slots.push(slot);
        slot.appendChild(img);
        images.push(img);
        return;
      }
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
    images.splice(0).forEach((img) => img.remove());
    setTimeout(() => pending.forEach((root) => root.unmount()), 0);
  };
}
