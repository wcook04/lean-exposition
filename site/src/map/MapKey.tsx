// The map's key, behind one button: the drawing is plain enough to need no legend on
// screen, and the Key says everything in words, including the keys, the links the map
// leaves out and how the map is drawn. The samples reuse the connector classes the map
// draws with.

import site from "@instance/site";
import { useCallback, useEffect, useRef, useState } from "react";

import { routeHref } from "../app/router";
import { LeanDot, LeanGlyph, TopicSwatch } from "./LeanGlyph";
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
          <p className="map-keypop__h">Colours</p>
          <ul className="map-keypop__channels">
            <li>
              <TopicSwatch colour="var(--tone-0, var(--lean-fill))" /> <TopicSwatch colour="var(--tone-1, var(--lean-fill-part))" /> Each card has the colour of its topic, the same colours as the topic list beside the paper.
            </li>
            <li>
              <TopicSwatch colour="var(--tone-0, var(--lean-fill))" soft /> A step the paper does not name, such as a Lean helper, takes a softer shade of the step it serves.
            </li>
            <li>Zoomed out past reading size, cards become plain colour chips. Point at one to read it.</li>
          </ul>
          <p className="map-keypop__h">Lean</p>
          <ul className="map-keypop__channels">
            <li>
              <LeanDot fill="whole" /> A filled dot: an AI agent linked this step to Lean that states and proves it, or defines it. A proof here is a theorem or lemma in {site.lean.ownerSource} with no <code>sorry</code> in its text.
            </li>
            <li>
              <LeanDot fill="part" /> A ring: the linked Lean has some of it, or proves it in a different form.
            </li>
            <li>No dot: no Lean is linked.</li>
            <li>
              A card with no topic shows the same as a fill: <LeanGlyph fill="whole" /> proved, <LeanGlyph fill="part" /> some of it, <LeanGlyph fill="none" /> none.
            </li>
            <li>An AI agent made each link, and no program tests whether the two sides say the same thing. Each card's sheet gives its status in words, and its run records say whether a build ran.</li>
          </ul>
          <p className="map-keypop__h">Cards</p>
          <ul className="map-keypop__channels">
            <li>{site.words.mapKeyIntro.replace(/^Each box\b/, "Each card")}</li>
            <li>A box is a definition and a rounded card a result.</li>
            <li>
              <span className="keyrow__tag" aria-hidden="true" /> An assumption is a tag on each result that assumes it.
            </li>
            <li>A step many results use, with nothing drawn below it, is drawn again under each of them.</li>
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
                  <Sample kind="lean_via" /> Reached only through helpers no step links. Point at the line to see how many.
                </li>
                <li>
                  {usesSource(lean.source)}. {lean.note}
                </li>
                <li>Definitions are listed under the drawing: nearly every result uses them. Each sheet lists all of a declaration's uses.</li>
                {!!lean.leftOut && <li>{lean.leftOut} uses are not drawn, because a longer chain already draws them. Each declaration's sheet lists all of its uses.</li>}
              </ul>
            </>
          )}
          <p className="map-keypop__h">Lines</p>
          <ul className="map-keypop__channels">
            <li>
              <Sample kind="supports" /> Each line runs from a step up to the result that uses it.
            </li>
            <li>
              <Sample kind="formalizes" head={false} /> A Lean declaration recorded for that result.
            </li>
            <li>With a paper chosen, a line may pass over steps that paper leaves out.</li>
          </ul>
          <p className="map-keypop__h">Moving around</p>
          <ul className="map-keypop__channels">
            <li>Scroll up to zoom in at the pointer, and down to zoom out, as far as the whole map. Drag to pan, or scroll sideways. Pinching also zooms. The + and − keys zoom too, Shift with an arrow key pans, and 0 or Fit shows the whole map.</li>
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
