// The map's key, behind one button: the drawing is plain enough to need no legend on
// screen, and the Key says everything in words, including the keys, the links the map
// leaves out and how the map is drawn. The samples reuse the connector classes the map
// draws with.

import { useCallback, useEffect, useRef, useState } from "react";

import { routeHref } from "../app/router";
import { LeanGlyph } from "./LeanGlyph";
import { Sample } from "./Sample";
import { usesSource } from "./MapStrip";

export { Sample };

/** The Key: everything the map's marks mean, in words. */
export function KeyPopover({ onNotesHost, lean }: { onNotesHost(host: HTMLElement | null): void; lean?: { source?: string; note?: string; leftOut?: number } }) {
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
            <li>A record many results use, with nothing drawn below it, is drawn again under each of them.</li>
          </ul>
          <p className="map-keypop__h">Lean</p>
          <ul className="map-keypop__channels">
            <li>
              <LeanGlyph fill="whole" /> Green: the Lean states and proves it, or defines it. A proof here is a theorem or lemma in OpenAI's source with no <code>sorry</code> in its text.
            </li>
            <li>
              <LeanGlyph fill="part" /> Pale green: part of it is in Lean, or a Lean proof carries the step in a different form.
            </li>
            <li>
              <LeanGlyph fill="none" /> Plain: no declaration is linked.
            </li>
            <li>A box is a definition and a rounded shape a result. Each record's sheet says its status in words.</li>
            <li>Links are read by people or agents and not checked as equivalent. Whether a build ran is in each record's checks.</li>
          </ul>
          {lean && (
            <>
              <p className="map-keypop__h">Lean graph</p>
              <ul className="map-keypop__channels">
                <li>
                  <Sample kind="supports" /> The proof uses the declaration below.
                </li>
                <li>
                  <Sample kind="lean_type_dependency" /> The statement uses it: its name is written in the statement's lines.
                </li>
                <li>
                  <Sample kind="lean_via" /> Reached only through helpers no record links. Point at the line to see how many.
                </li>
                <li>
                  {usesSource(lean.source)}. {lean.note}
                </li>
                {!!lean.leftOut && <li>{lean.leftOut} uses are not drawn, because a longer chain already says them. Each declaration's sheet lists all of its uses.</li>}
              </ul>
            </>
          )}
          <p className="map-keypop__h">Lines</p>
          <ul className="map-keypop__channels">
            <li>
              <Sample kind="supports" /> Each line runs from a record up to the result that uses it.
            </li>
            <li>
              <Sample kind="formalizes" head={false} /> A Lean declaration recorded for that result.
            </li>
            <li>Under a paper's lens, a line may pass over records that paper leaves out.</li>
          </ul>
          <p className="map-keypop__h">Moving around</p>
          <ul className="map-keypop__channels">
            <li>Scroll to pan, or drag from anywhere. Pinch, or Ctrl or ⌘ with the wheel, zooms. The + and − keys zoom too, Shift with an arrow key pans, and 0 fits the whole map.</li>
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
