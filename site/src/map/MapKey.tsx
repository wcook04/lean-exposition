// The map's key, behind one button: what the colours and line styles mean and
// how to go deeper. The samples reuse the connector classes the map draws with.

import { useEffect, useRef, useState } from "react";
import type { OriginFamily } from "../model/graph";

export function SourceSwatches({ origins, className }: { origins: OriginFamily[]; className?: string }) {
  return (
    <ul className={`map-key__sources${className ? ` ${className}` : ""}`} aria-label="Colour shows where each statement comes from">
      {origins
        .filter((o) => o.slot > 0)
        .map((o) => (
          <li key={o.family} data-slot={o.slot}>
            <span className="map-key__swatch" aria-hidden="true" />
            {o.label}
          </li>
        ))}
      <li data-slot={0}>
        <span className="map-key__swatch" aria-hidden="true" />
        Published papers and the long record
      </li>
    </ul>
  );
}

function Sample({ kind, head = true }: { kind: "supports" | "assumes" | "formalizes"; head?: boolean }) {
  const cls = kind === "supports" ? "link" : `link link--${kind}`;
  return (
    <svg className="map-keypop__sample" viewBox="0 0 48 16" width="48" height="16" aria-hidden="true">
      <path className={cls} d={head ? "M2 8H37" : "M2 8H46"} />
      {head && <path className="head" d="M46 8 L36 4.4 L36 11.6 Z" />}
    </svg>
  );
}

export function MapKey({ origins }: { origins: OriginFamily[] }) {
  const [open, setOpen] = useState(false);
  const root = useRef<HTMLDivElement>(null);

  useEffect(() => {
    if (!open) return;
    const onDown = (event: PointerEvent) => {
      if (!root.current?.contains(event.target as Node)) setOpen(false);
    };
    // Capture phase, so the map page's own Escape (which clears the selection) waits.
    const onKey = (event: KeyboardEvent) => {
      if (event.key !== "Escape") return;
      event.preventDefault();
      setOpen(false);
      root.current?.querySelector("button")?.focus();
    };
    document.addEventListener("pointerdown", onDown);
    window.addEventListener("keydown", onKey, true);
    return () => {
      document.removeEventListener("pointerdown", onDown);
      window.removeEventListener("keydown", onKey, true);
    };
  }, [open]);

  return (
    <div className="map-keypop" ref={root}>
      <button type="button" className="control" aria-expanded={open} aria-controls="map-key-panel" onClick={() => setOpen((v) => !v)}>
        Key
      </button>
      {open && (
        <div id="map-key-panel" className="map-keypop__panel" role="dialog" aria-label="How to read the map">
          <p className="map-keypop__title">Colour: where each statement comes from</p>
          <SourceSwatches origins={origins} className="map-keypop__sources" />
          <p className="map-keypop__title">Lines</p>
          <ul className="map-keypop__lines">
            <li>
              <Sample kind="supports" />
              helps prove the result it points to
            </li>
            <li>
              <Sample kind="assumes" />
              an assumption the result relies on
            </li>
            <li>
              <Sample kind="formalizes" head={false} />
              the same statement in Lean
            </li>
          </ul>
          <p className="map-keypop__title">Going deeper</p>
          <p className="map-keypop__note">
            Double-click a card, or use its foot, to unfold what it uses. Point at an arrow to read how that step is made;
            click it to open the step.
          </p>
        </div>
      )}
    </div>
  );
}
