// The map's key, behind one button: the drawing is plain enough to need no legend on
// screen, and the Key says everything in words, including the keys, the links the map
// leaves out and how the map is drawn. The samples reuse the connector classes the map
// draws with.

import { useCallback, useEffect, useRef, useState } from "react";

import { routeHref } from "../app/router";

/** A short piece of one kind of line, drawn with the map's own classes at the map's reading scale. */
export function Sample({ kind, head = true, className }: { kind: "supports" | "assumes" | "formalizes"; head?: boolean; className?: string }) {
  return (
    <svg className={`map-key__sample${className ? ` ${className}` : ""}`} viewBox="0 0 48 16" width="48" height="16" aria-hidden="true" style={{ ["--k" as string]: 1 }}>
      <path className={`link link--${kind}`} d={head ? "M3 8H37" : "M3 8H46"} />
      {head && <path className={`head head--${kind}`} d="M46 8 L36 4.4 L36 11.6 Z" />}
    </svg>
  );
}

/** The Key: everything the map's marks mean, in words. */
export function KeyPopover({ onNotesHost }: { onNotesHost(host: HTMLElement | null): void }) {
  const [open, setOpen] = useState(false);
  const root = useRef<HTMLDivElement>(null);
  const close = useCallback(() => setOpen(false), []);
  useEffect(() => {
    if (!open) return;
    const onDown = (event: PointerEvent) => {
      if (!root.current?.contains(event.target as Node)) close();
    };
    // Capture phase, so the page's own Escape (which clears the selection) waits.
    const onKey = (event: KeyboardEvent) => {
      if (event.key !== "Escape") return;
      event.preventDefault();
      event.stopPropagation();
      close();
      root.current?.querySelector("button")?.focus();
    };
    document.addEventListener("pointerdown", onDown);
    window.addEventListener("keydown", onKey, true);
    return () => {
      document.removeEventListener("pointerdown", onDown);
      window.removeEventListener("keydown", onKey, true);
    };
  }, [open, close]);
  return (
    <div className="map-keypop" ref={root}>
      <button type="button" className="map-head__key" aria-expanded={open} aria-haspopup="dialog" onClick={() => setOpen((v) => !v)}>
        <svg viewBox="0 0 16 16" width="15" height="15" aria-hidden="true">
          <rect x="2" y="3" width="4" height="4" rx="1" fill="currentColor" />
          <path d="M8.5 5h5.5M2 11.5h4M8.5 11.5h5.5" fill="none" stroke="currentColor" strokeWidth="1.5" strokeLinecap="round" />
        </svg>
        Key
      </button>
      {open && (
        <div className="map-keypop__panel" role="dialog" aria-label="Key to the argument map">
          <p className="map-keypop__h">Records</p>
          <ul className="map-keypop__channels">
            <li>Each box is one record: a claim, an assumption or a Lean declaration. Select one to read it in Lean and in each paper.</li>
            <li>
              <span className="keyrow__tag" aria-hidden="true" /> An assumption is a tag on each result that assumes it.
            </li>
            <li>
              <span className="keyrow__clone" aria-hidden="true" /> A band along the foot marks a record drawn again under each result that uses it.
            </li>
          </ul>
          <p className="map-keypop__h">Lines</p>
          <ul className="map-keypop__channels">
            <li>
              <Sample kind="supports" /> A record used in the argument for the result above it.
            </li>
            <li>
              <Sample kind="formalizes" head={false} /> A Lean declaration recorded for that result.
            </li>
            <li>Under a paper's lens, a line may pass over records that paper leaves out.</li>
          </ul>
          <p className="map-keypop__h">Moving around</p>
          <ul className="map-keypop__channels">
            <li>Scroll to pan, or drag from anywhere. Pinch, or Ctrl or ⌘ with the wheel, zooms. The + and − keys zoom too.</li>
            <li>↑ goes to the result that uses this one, ↓ to its first input, ← and → to the inputs beside it. Enter opens its inputs and Esc clears the selection.</li>
            <li>With a paper chosen, [ and ] step through its passages.</li>
          </ul>
          <div ref={onNotesHost} />
          <a href={routeHref({ view: "about", anchor: "about-key" })}>How the map is drawn</a>
        </div>
      )}
    </div>
  );
}
