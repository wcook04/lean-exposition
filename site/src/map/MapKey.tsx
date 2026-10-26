// The map's key, as a row in the page's flow under the map's header: the
// source colours, the two kinds of line, the assumption tag and the band on a
// record drawn more than once. It sits in the flow so the canvas gives it room
// and nothing is drawn under it; the items wrap when the window is narrow.
// The samples reuse the connector classes the map draws with. The full
// explanation lives on the About page, which the row links to.

import type { OriginFamily } from "../model/graph";
import { routeHref } from "../app/router";

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

/** A short piece of one kind of line, drawn with the map's own classes at the map's reading scale. */
export function Sample({ kind, head = true, className }: { kind: "supports" | "assumes" | "formalizes"; head?: boolean; className?: string }) {
  return (
    <svg className={`map-key__sample${className ? ` ${className}` : ""}`} viewBox="0 0 48 16" width="48" height="16" aria-hidden="true" style={{ ["--k" as string]: 1 }}>
      <path className={`link link--${kind}`} d={head ? "M3 8H37" : "M3 8H46"} />
      {head && <path className={`head head--${kind}`} d="M46 8 L36 4.4 L36 11.6 Z" />}
    </svg>
  );
}

/** The key row under the map's header. `hidden` keeps it in the document for the Key button's aria-controls. */
export function KeyRow({ id, origins, hidden }: { id: string; origins: OriginFamily[]; hidden?: boolean }) {
  return (
    <section id={id} className="keyrow" aria-label="Key to the argument map" hidden={hidden}>
      <SourceSwatches origins={origins} className="keyrow__sources" />
      <ul className="keyrow__marks">
        <li>
          <Sample kind="supports" />
          Used in the argument for
        </li>
        <li>
          <Sample kind="formalizes" head={false} />
          Lean declaration for
        </li>
        <li>
          <span className="keyrow__tag" aria-hidden="true" />
          Assumption, shown as a tag on each result that assumes it
        </li>
        <li>
          <span className="keyrow__clone" aria-hidden="true" />
          A record drawn again under each result that uses it
        </li>
        <li className="keyrow__more">
          <a href={routeHref({ view: "about", anchor: "about-key" })}>How the map is drawn</a>
        </li>
      </ul>
    </section>
  );
}
