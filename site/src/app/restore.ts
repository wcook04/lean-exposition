// One way of putting a page's scroll back, for the window and every inner scroller.
//
// Content arrives late (a lazy page, a fetched record, a chart), so restoring is
// a short loop: each frame, set each scroller to where it was, for as long as
// something still moves or has not yet appeared. Any input from the reader ends
// it at once, so a restore never fights a hand on the wheel.

import { useEffect, useLayoutEffect, useRef } from "react";
import type { Route } from "./router";
import { arrivedBy, onLeave, readEntry, useEntryKey, writeEntry } from "./trail";

/** A saved place. `window` may be a function when the place is measured, as the paper's is. */
export interface KeptScroll {
  window?: number | (() => number | null);
  inner?: Record<string, [top: number, left: number]>;
}

/** The scrollers whose place is kept. A new one needs only an entry here, or a `data-keep` attribute. */
export const SCROLLERS = [
  ".panel__body",
  ".record-dock__scroll",
  ".inspector__scroll",
  ".outline__list",
  ".map-page__main > .outline",
  ".lean-left",
  ".lean-side",
  ".lean-scroll",
  ".bench-rail__list",
  ".bench-col__scroll",
  ".bench--stacked .bench-main",
  ".table-scroll",
  ".visit__scroll",
  "[data-keep]",
];

const ENTRY_NAME = "scroll";
/**
 * How long a place must hold still, in ms, before the loop stops. Generous: the
 * cost is a few reads a frame, and a section that arrives above a restored
 * place would otherwise carry it off (the browser anchors to whatever is on screen).
 */
const SETTLE = 1200;
/** The longest a restore waits for late content; the reader's own input ends it sooner. */
const LIMIT = 5000;
/** How long after settling late fonts may still move the text. */
const REFIT = 3000;
const INPUT = ["wheel", "touchstart", "pointerdown", "keydown"] as const;

function find(id: string): HTMLElement | null {
  const at = id.lastIndexOf("@");
  return document.querySelectorAll<HTMLElement>(id.slice(0, at))[Number(id.slice(at + 1))] ?? null;
}

/** Where every kept scroller is now; the window too unless the page keeps its own place. */
export function snapshotScroll(withWindow: boolean): KeptScroll {
  const inner: NonNullable<KeptScroll["inner"]> = {};
  for (const selector of SCROLLERS) {
    document.querySelectorAll<HTMLElement>(selector).forEach((el, i) => {
      const scrolls = el.scrollHeight > el.clientHeight || el.scrollWidth > el.clientWidth;
      if (scrolls) inner[`${selector}@${i}`] = [Math.round(el.scrollTop), Math.round(el.scrollLeft)];
    });
  }
  return { ...(withWindow ? { window: Math.round(window.scrollY) } : {}), inner };
}

/**
 * Put a saved place back. Returns a function that stops trying. With `refit`, the
 * place is put back once more if late fonts reflow the text, for a few seconds after
 * it has settled. The reader's own input ends all of it, at any stage: scrolling
 * brings new fonts into use, and a refit then would pull the page out of their hand.
 */
export function restoreScroll(kept: KeptScroll, options: { onDone?(): void; limit?: number; settle?: number; refit?: boolean } = {}): () => void {
  const limit = options.limit ?? LIMIT;
  const settle = options.settle ?? SETTLE;
  const fonts = options.refit ? document.fonts : undefined;
  let begun = 0;
  let still = 0;
  let frame = 0;
  let watch: ReturnType<typeof setTimeout> | undefined;
  let tall = -1;
  let ended = false;

  const end = () => {
    if (ended) return;
    ended = true;
    cancelAnimationFrame(frame);
    clearTimeout(watch);
    fonts?.removeEventListener("loadingdone", begin);
    for (const type of INPUT) window.removeEventListener(type, end, { capture: true });
  };

  const settled = () => {
    options.onDone?.();
    if (ended) return;
    if (!fonts) return end();
    fonts.addEventListener("loadingdone", begin, { once: true });
    watch = setTimeout(end, REFIT);
  };

  const step = () => {
    let waiting = false;
    let moved = false;
    if (kept.window !== undefined) {
      const y = typeof kept.window === "function" ? kept.window() : kept.window;
      if (y === null) waiting = true;
      else {
        const room = document.documentElement.scrollHeight - window.innerHeight;
        if (y > room + 1) waiting = true;
        const wanted = Math.max(0, Math.min(y, room));
        // Half a pixel: a looser test lets each save and restore creep by one.
        if (Math.abs(window.scrollY - wanted) > 0.5) {
          window.scrollTo({ top: wanted, behavior: "instant" as ScrollBehavior });
          moved = true;
        }
      }
    }
    for (const [id, [top, left]] of Object.entries(kept.inner ?? {})) {
      const el = find(id);
      if (!el) {
        waiting = true;
        continue;
      }
      if (top > el.scrollHeight - el.clientHeight + 1 || left > el.scrollWidth - el.clientWidth + 1) waiting = true;
      if (Math.abs(el.scrollTop - top) > 1 || Math.abs(el.scrollLeft - left) > 1) {
        el.scrollTo({ top, left, behavior: "instant" as ScrollBehavior });
        if (Math.abs(el.scrollTop - top) > 1 || Math.abs(el.scrollLeft - left) > 1) waiting = true;
        moved = true;
      }
    }
    const height = document.documentElement.scrollHeight + Object.keys(kept.inner ?? {}).reduce((sum, id) => sum + (find(id)?.scrollHeight ?? 0), 0);
    if (height !== tall) moved = true;
    tall = height;
    const now = performance.now();
    if (moved || waiting) still = now;
    if (now - still >= settle || now - begun >= limit) settled();
    else frame = requestAnimationFrame(step);
  };

  function begin() {
    clearTimeout(watch);
    begun = still = performance.now();
    step();
  }

  for (const type of INPUT) window.addEventListener(type, end, { passive: true, capture: true });
  begin();
  return end;
}

/**
 * Keep the place of every scroller for each history entry. Mounted once by App.
 * The paper keeps the window's place itself, by part and offset, because its
 * height changes as parts render.
 */
export function useKeptPlace(view: Route["view"]): void {
  const key = useEntryKey();
  const viewRef = useRef(view);
  const shown = useRef(view);
  viewRef.current = view;
  useEffect(() => onLeave(() => writeEntry(ENTRY_NAME, snapshotScroll(viewRef.current !== "read"))), []);
  useLayoutEffect(() => {
    const previous = shown.current;
    shown.current = viewRef.current;
    if (arrivedBy() === "push") {
      // A new page opens at its top, unless it has a place of its own to go to.
      if (previous !== viewRef.current && viewRef.current !== "read" && !window.location.hash) window.scrollTo({ top: 0, behavior: "instant" as ScrollBehavior });
      return;
    }
    const kept = readEntry<KeptScroll>(ENTRY_NAME);
    return kept ? restoreScroll(kept) : undefined;
  }, [key]);
}
