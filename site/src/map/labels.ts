// Plain-language names for node kinds, shared by the map and the panels.

/** Plain-language name of a node kind, as the map's key says it. */
export function kindName(kind: string): string {
  switch (kind) {
    case "goal":
      return "Main result";
    case "declaration":
      return "Lean statement";
    case "assumption":
      return "Assumption";
    default:
      return "Claim";
  }
}
