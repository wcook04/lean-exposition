// On a phone the panel is a bottom sheet with two resting heights: a peek
// that leaves the map visible above it, and full. The handle drags between
// them and, as a button, toggles them.

import { useRef, useState, type PointerEvent } from "react";

export type SheetState = "peek" | "full";

export function useSheet() {
  const [state, setState] = useState<SheetState>("peek");
  const [drag, setDrag] = useState<number | null>(null); // live height in px while dragging
  const start = useRef<{ y: number; h: number; moved: boolean } | null>(null);

  const onPointerDown = (event: PointerEvent<HTMLButtonElement>) => {
    const sheet = event.currentTarget.closest<HTMLElement>(".panel");
    if (!sheet) return;
    start.current = { y: event.clientY, h: sheet.getBoundingClientRect().height, moved: false };
    event.currentTarget.setPointerCapture(event.pointerId);
  };
  const onPointerMove = (event: PointerEvent<HTMLButtonElement>) => {
    const s = start.current;
    if (!s) return;
    const dy = event.clientY - s.y;
    if (Math.abs(dy) > 4) s.moved = true;
    if (s.moved) setDrag(Math.max(120, Math.min(window.innerHeight - 64, s.h - dy)));
  };
  const onPointerUp = (event: PointerEvent<HTMLButtonElement>) => {
    const s = start.current;
    start.current = null;
    if (!s) return;
    if (!s.moved) {
      setState((v) => (v === "peek" ? "full" : "peek"));
    } else {
      const dy = event.clientY - s.y;
      setState(dy < -40 ? "full" : dy > 40 ? "peek" : state);
    }
    setDrag(null);
  };

  const handle = (
    <button
      type="button"
      className="panel__handle"
      aria-label={state === "peek" ? "Expand the panel" : "Shrink the panel"}
      aria-expanded={state === "full"}
      onPointerDown={onPointerDown}
      onPointerMove={onPointerMove}
      onPointerUp={onPointerUp}
      onPointerCancel={() => {
        start.current = null;
        setDrag(null);
      }}
      onClick={(event) => {
        // Pointer handlers decide; keyboard activation (detail 0) toggles here.
        if (event.detail === 0) setState((v) => (v === "peek" ? "full" : "peek"));
      }}
    >
      <span className="panel__grip" aria-hidden="true" />
    </button>
  );

  const style = drag !== null ? { ["--sheet-drag" as string]: `${drag}px` } : undefined;
  return { state, dragging: drag !== null, handle, style };
}
