// Adapted from the Apache-licensed Proof Reader PaperSplit and Quartic ReaderSplit.
// The divider changes one CSS width while the paper and companion measure themselves.
import { useLayoutEffect, useRef, useState, type KeyboardEvent, type PointerEvent } from "react";

const KEY = `lx-reader-paper-share:${import.meta.env.BASE_URL}`;
const MIN_PANE = 400;

function savedShare(): number | null {
  try {
    const value = Number(localStorage.getItem(KEY));
    return value > 0.2 && value < 0.8 ? value : null;
  } catch {
    return null;
  }
}

export function PaperSplit() {
  const handle = useRef<HTMLDivElement>(null);
  const share = useRef<number | null>(null);
  const stopDrag = useRef<(() => void) | null>(null);
  const [percent, setPercent] = useState(50);
  const [limits, setLimits] = useState({ min: 25, max: 75 });

  function layout() {
    const grip = handle.current;
    const reader = grip?.closest<HTMLElement>(".reader");
    const paper = reader?.querySelector<HTMLElement>(":scope > .reader__paper");
    const companion = grip?.parentElement;
    if (!grip || !reader || !paper || !companion) return null;
    return { grip, reader, paper, companion };
  }

  function write(value: number | null, available: number) {
    const reader = layout()?.reader;
    if (!reader || !available) return;
    const min = Math.min(0.43, Math.max(0.22, MIN_PANE / available));
    const next = value === null ? null : Math.min(1 - min, Math.max(min, value));
    share.current = next;
    reader.toggleAttribute("data-paper-split", next !== null);
    if (next === null) reader.style.removeProperty("--reader-split-width");
    else reader.style.setProperty("--reader-split-width", `${Math.round(next * available)}px`);
  }

  function save() {
    try {
      if (share.current === null) localStorage.removeItem(KEY);
      else localStorage.setItem(KEY, String(share.current));
    } catch {
      // The divider still works with storage disabled.
    }
  }

  function resize(value: number | null) {
    const elements = layout();
    if (!elements) return;
    write(value, elements.paper.clientWidth + elements.companion.clientWidth);
    save();
  }

  useLayoutEffect(() => {
    const elements = layout();
    if (!elements) return;
    const { reader, paper, companion } = elements;
    let capacity = paper.clientWidth + companion.clientWidth;
    const ratio = savedShare();
    if (ratio !== null) write(ratio, capacity);
    const measure = () => {
      const width = paper.clientWidth + companion.clientWidth;
      if (!width) return;
      if (width !== capacity && share.current !== null) {
        capacity = width;
        write(share.current, width);
      }
      const min = Math.round(100 * Math.min(0.43, Math.max(0.22, MIN_PANE / width)));
      setLimits((previous) => previous.min === min ? previous : { min, max: 100 - min });
      setPercent(Math.round(100 * paper.clientWidth / width));
    };
    measure();
    const observer = new ResizeObserver(measure);
    observer.observe(paper);
    observer.observe(companion);
    return () => {
      observer.disconnect();
      stopDrag.current?.();
      reader.removeAttribute("data-paper-split");
      reader.style.removeProperty("--reader-split-width");
    };
  }, []);

  function drag(event: PointerEvent<HTMLDivElement>) {
    const elements = layout();
    if (event.button !== 0 || !elements) return;
    const { grip, reader, paper, companion } = elements;
    const available = paper.clientWidth + companion.clientWidth;
    if (!available) return;
    event.preventDefault();
    grip.focus({ preventScroll: true });
    grip.setPointerCapture(event.pointerId);
    reader.classList.add("reader--resizing");
    const start = event.clientX;
    const initial = paper.clientWidth;
    let x = start;
    let frame = 0;
    let moved = false;
    const draw = () => {
      frame = 0;
      if (moved) write((initial + x - start) / available, available);
    };
    const move = (next: globalThis.PointerEvent) => {
      x = next.clientX;
      moved ||= Math.abs(x - start) > 1;
      if (!frame) frame = requestAnimationFrame(draw);
    };
    const end = () => {
      if (frame) cancelAnimationFrame(frame);
      draw();
      grip.removeEventListener("pointermove", move);
      grip.removeEventListener("pointerup", end);
      grip.removeEventListener("pointercancel", end);
      grip.removeEventListener("lostpointercapture", end);
      reader.classList.remove("reader--resizing");
      stopDrag.current = null;
      if (moved) save();
    };
    grip.addEventListener("pointermove", move);
    grip.addEventListener("pointerup", end);
    grip.addEventListener("pointercancel", end);
    grip.addEventListener("lostpointercapture", end);
    stopDrag.current = end;
  }

  function key(event: KeyboardEvent<HTMLDivElement>) {
    const { key } = event;
    if (!["ArrowLeft", "ArrowRight", "Home", "Enter"].includes(key)) return;
    event.preventDefault();
    event.stopPropagation();
    if (key === "Home" || key === "Enter") resize(null);
    else resize(percent / 100 + (key === "ArrowRight" ? 0.025 : -0.025));
  }

  return (
    <div ref={handle} className="reader__split" role="separator" tabIndex={0}
      aria-orientation="vertical" aria-label="Resize paper and companion panes"
      aria-valuemin={limits.min} aria-valuemax={limits.max} aria-valuenow={percent}
      aria-valuetext={`Paper ${percent}%`}
      title="Drag to resize. Use arrow keys to adjust or double-click to reset."
      onPointerDown={drag} onKeyDown={key} onDoubleClick={() => resize(null)}>
      <span aria-hidden="true" />
    </div>
  );
}
