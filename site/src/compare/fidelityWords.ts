// How the site says what a Lean statement says against a paper's, and who linked a paper's
// statement to its Lean. One owner for the words, used by Compare, the step view, the tick's
// Lean panel, the reader's tie panel and the front page. Plain functions: no browser API,
// no import.meta, because the first screen is built in vite.config.ts with them too.

/** The Lean says the same as the paper, more than it, or less. */
export type Fidelity = "same" | "stronger" | "weaker";

/** Who compared them: the source repository's own evidence record, or an AI agent for this site. */
export type FidelitySource = "recorded" | "ai";

/** Who made a tie from a paper's statement to its Lean. */
export type TieOrigin = "evidence_record" | "ai";

export const FIDELITIES: readonly Fidelity[] = ["same", "stronger", "weaker"];

/** "Says the same as the paper", "Says more than the paper", "Says less than the paper". */
export function verdictWords(fidelity: Fidelity, noun = "paper"): string {
  if (fidelity === "same") return `Says the same as the ${noun}`;
  if (fidelity === "stronger") return `Says more than the ${noun}`;
  return `Says less than the ${noun}`;
}

/** The sentence a Lean panel leads with: "The Lean statement says the same as the paper." */
export function fidelitySentence(fidelity: Fidelity): string {
  if (fidelity === "same") return "The Lean statement says the same as the paper.";
  if (fidelity === "stronger") return "The Lean statement says more than the paper.";
  return "The Lean statement says less than the paper.";
}

/** Who made the comparison, in plain words. */
export function fidelitySourceWords(source: FidelitySource | undefined): string {
  if (source === "recorded") return "Compared in the source repository’s own evidence record.";
  if (source === "ai") return "Compared by an AI agent for this site; no mathematician has reviewed the comparison.";
  return "Who made this comparison is not recorded.";
}

/** Who linked a paper's statement to its Lean, in plain words; null for a tie that does not say. */
export function originWords(origin: TieOrigin | undefined | null): string | null {
  if (origin === "evidence_record") return "This link from the printed result to its Lean declaration is copied from the papers’ published evidence mapping.";
  if (origin === "ai") return "An AI agent read the statement and the Lean and made this link for this site.";
  return null;
}

/** A short tag for a tie's origin, for lists. */
export function originTag(origin: TieOrigin | undefined | null): string | null {
  if (origin === "evidence_record") return "From the evidence mapping";
  if (origin === "ai") return "Linked by an AI agent";
  return null;
}

export const isFidelity = (value: unknown): value is Fidelity => value === "same" || value === "stronger" || value === "weaker";
export const isTieOrigin = (value: unknown): value is TieOrigin => value === "evidence_record" || value === "ai";
