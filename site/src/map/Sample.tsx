// A short piece of one kind of line, for the key and the sheets.

/** A short piece of one kind of line, drawn with the map's own classes at the map's reading scale. */
export function Sample({ kind, head = true, className }: { kind: "supports" | "assumes" | "formalizes" | "lean_type_dependency" | "lean_via"; head?: boolean; className?: string }) {
  return (
    <svg className={`map-key__sample${className ? ` ${className}` : ""}`} viewBox="0 0 48 16" width="48" height="16" aria-hidden="true" style={{ ["--k" as string]: 1 }}>
      <path className={`link link--${kind}`} d={head ? "M3 8H37" : "M3 8H46"} />
      {head && <path className={`head head--${kind}`} d="M46 8 L36 4.4 L36 11.6 Z" />}
    </svg>
  );
}
