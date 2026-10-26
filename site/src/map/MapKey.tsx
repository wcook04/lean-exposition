// The map's key, behind one button: one visual channel per meaning, the
// three relations, the three representations, and how to go deeper. The
// samples reuse the connector classes the map draws with.

import { useEffect, useLayoutEffect, useRef, useState } from "react";
import type { OriginFamily } from "../model/graph";

export function SourceSwatches({ origins, className }: { origins: OriginFamily[]; className?: string }) {
  return (
    <ul className={`map-key__sources${className ? ` ${className}` : ""}`} aria-label="The colour of each source">
      {origins
        .filter((o) => o.slot > 0)
        .map((o) => (
          <li key={o.family} data-slot={o.slot}>
            <span className="map-key__swatch src-sq" aria-hidden="true" />
            {o.label}
          </li>
        ))}
      <li data-slot={0}>
        <span className="map-key__swatch src-sq" aria-hidden="true" />
        Published papers and the long record
      </li>
    </ul>
  );
}

function Sample({ kind, head = true }: { kind: "supports" | "assumes" | "formalizes"; head?: boolean }) {
  // The same classes the map draws with, at the map's reading scale.
  return (
    <svg className="map-keypop__sample" viewBox="0 0 48 16" width="48" height="16" aria-hidden="true" style={{ ["--k" as string]: 1 }}>
      <path className={`link link--${kind}`} d={head ? "M3 8H37" : "M3 8H46"} />
      {head && <path className={`head head--${kind}`} d="M46 8 L36 4.4 L36 11.6 Z" />}
    </svg>
  );
}

export function MapKey({ origins }: { origins: OriginFamily[] }) {
  const [open, setOpen] = useState(false);
  const root = useRef<HTMLDivElement>(null);
  const panel = useRef<HTMLDivElement>(null);
  const [shift, setShift] = useState(0);

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

  // Keep the panel inside the viewport (on a phone the button sits near the left edge).
  useLayoutEffect(() => {
    if (!open) {
      setShift(0);
      return;
    }
    const place = () => {
      const el = panel.current;
      if (!el) return;
      el.style.right = "";
      const r = el.getBoundingClientRect();
      const margin = 16;
      let dx = 0;
      if (r.left < margin) dx = margin - r.left;
      else if (r.right > window.innerWidth - margin) dx = window.innerWidth - margin - r.right;
      setShift(-dx);
    };
    place();
    window.addEventListener("resize", place);
    return () => window.removeEventListener("resize", place);
  }, [open]);

  return (
    <div className="map-keypop" ref={root}>
      <button type="button" className="control" aria-expanded={open} aria-controls="map-key-panel" onClick={() => setOpen((v) => !v)}>
        Key
      </button>
      {open && (
        <div ref={panel} id="map-key-panel" className="map-keypop__panel" role="dialog" aria-label="Key to the argument map" style={shift ? { right: shift } : undefined}>
          <p className="map-keypop__title">Colours, words and marks on a card</p>
          <ul className="map-keypop__channels">
            <li>
              Each card has a small coloured square beside the name of the source its record comes from. Records from the same
              source have the same colour.
            </li>
            <li>
              A word in small capitals names the kind of record: claim, assumption, main result or Lean declaration. Only
              assumption cards have a dashed border.
            </li>
            <li>
              <span className="cov-mark" aria-hidden="true" /> <span className="cov-mark cov-mark--relied" aria-hidden="true" />{" "}
              <span className="cov-mark cov-mark--outside" aria-hidden="true" /> When you choose an account under “Records used
              by”, each card carries one of these three marks: the record has a passage of its own in that account, the account
              uses it without a passage of its own, or the account does not use it.
            </li>
            <li>The card or line you have selected, a route you have traced and the keyboard focus are outlined in amber.</li>
          </ul>
          <p className="map-keypop__title">Sources</p>
          <SourceSwatches origins={origins} className="map-keypop__sources" />
          <p className="map-keypop__title">Lines and tags</p>
          <p className="map-keypop__note">
            A line joins a record to a result whose argument uses it, with the arrowhead at the result.
          </p>
          <ul className="map-keypop__lines">
            <li>
              <Sample kind="supports" />
              Recorded support
            </li>
            <li>
              <span className="tag map-keypop__tag" aria-hidden="true">
                Assumption
              </span>
              Explicit assumption, a tag on each result that assumes it
            </li>
            <li>
              <Sample kind="formalizes" head={false} />
              Recorded Lean correspondence, from a result to its recorded Lean declaration
            </li>
          </ul>
          <p className="map-keypop__title">Records drawn more than once</p>
          <p className="map-keypop__note">
            When several results use a record that has no recorded inputs of its own, the record is drawn under each of them,
            with a coloured band along the bottom of each copy.
          </p>
          <p className="map-keypop__title">Zooming</p>
          <p className="map-keypop__note">
            As you zoom out, each card first shows only its title and then becomes a small tile in its source’s colour. The main
            result and the selected record keep their names when zoomed out.
          </p>
          <p className="map-keypop__title">Moving around</p>
          <p className="map-keypop__note">
            Selecting a card opens its record in the panel. The card’s “Inputs” button, or the Space key, shows the records it
            uses, and the arrow keys move between cards. Pointing at a line shows a short description of that step, and
            selecting the line opens the step.
          </p>
        </div>
      )}
    </div>
  );
}
