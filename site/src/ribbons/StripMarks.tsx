// One account in reading order, as the dock's bar draws it: each passage linked
// to records is a mark spanning its place in the paper, in the source colour of
// the records it discusses. Shared by the dock and the front page.

import type { Strip } from "./useReadings";

export function StripMarks({ strip, lit, className = "dockbar__bars" }: { strip?: Strip; lit?: ReadonlySet<string>; className?: string }) {
  return (
    <svg className={className} viewBox="0 0 1000 5" preserveAspectRatio="none" aria-hidden="true">
      {/* A hairline for the whole paper, start to end, so a stretch with no linked passage reads as part of it. */}
      <rect className="strip__track" x={0} y={2} width={1000} height={1} />
      {strip?.passages.map((p) => (
        <rect
          key={p.key}
          x={(p.start / strip.length) * 1000}
          width={Math.max(2, ((p.end - p.start) / strip.length) * 1000 - 3)}
          height={5}
          data-slot={p.slot}
          className={`dockbar__seg${lit?.has(p.key) ? " dockbar__seg--lit" : ""}${p.claims.length ? "" : " dockbar__seg--example"}`}
        />
      ))}
    </svg>
  );
}
