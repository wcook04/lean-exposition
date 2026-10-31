// The free space in the top bar, where a pointed Lean name is read on pages that have it. One
// element, shared by every block on the page, so nothing inside the page waits for a hover and
// nothing can sit over the code. This file holds no Lean code.

import { useEffect, useLayoutEffect, useState } from "react";
import { BAR_LINE } from "../app/TopBar";

let line: HTMLElement | null = null;
let users = 0;

/** Where the bar hides its line (see `.topbar__line` in app.css). */
const BAR_LINE_SHOWN = "(min-width: 68.75em)";

/** Whether the bar shows its line at this width. */
export function useBarLineShown(): boolean {
  const [shown, setShown] = useState(() => window.matchMedia?.(BAR_LINE_SHOWN).matches ?? false);
  useEffect(() => {
    const media = window.matchMedia?.(BAR_LINE_SHOWN);
    if (!media) return;
    const update = () => setShown(media.matches);
    update();
    media.addEventListener("change", update);
    return () => media.removeEventListener("change", update);
  }, []);
  return shown;
}

/** The slot, or null where the bar has no room for it. */
export function useBarLine(): HTMLElement | null {
  const [slot, setSlot] = useState<HTMLElement | null>(line);
  useLayoutEffect(() => {
    const bar = document.getElementById(BAR_LINE);
    if (!bar) return;
    users += 1;
    if (!line) {
      line = document.createElement("div");
      line.className = "lean-slot lean-slot--compact lean-slot--bar";
      bar.append(line);
    }
    setSlot(line);
    return () => {
      users -= 1;
      if (users === 0) {
        line?.remove();
        line = null;
      }
    };
  }, []);
  return slot;
}
