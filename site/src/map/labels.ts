// Plain-language names for node kinds and relations, shared by the map and the panels.

/** Plain-language name of a node kind, as the map's cards and key say it. */
export function kindName(kind: string): string {
  switch (kind) {
    case "goal":
      return "Main result";
    case "declaration":
      return "Lean declaration";
    case "assumption":
      return "Assumption";
    default:
      return "Claim";
  }
}

/** A relation's name in the interface (DESIGN.md, Relations). */
export function relationName(kind: string): string {
  switch (kind) {
    case "assumes":
      return "Explicit assumption";
    case "formalizes":
      return "Recorded Lean correspondence";
    case "cites":
      return "Citation";
    default:
      return "Recorded support";
  }
}

/** The relation between two named records, in words that say only what was recorded. */
export function relationPhrase(kind: string, from: string, to: string): string {
  if (kind === "assumes") return `${from} assumes ${to}`;
  if (kind === "formalizes") return `${from} has a recorded Lean correspondence with ${to}`;
  return `${from} uses ${to}`;
}
