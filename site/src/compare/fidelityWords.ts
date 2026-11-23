// How the site says what a Lean statement says against a paper's, and who linked a paper's
// statement to its Lean. One owner for the words, used by Compare, the step view, the tick's
// Lean panel, the reader's tie panel and the front page. Plain functions: no browser API,
// no import.meta, because the first screen is built in vite.config.ts with them too.

/** The Lean says the same as the paper, more than it, less, or something neither implies. */
export type Fidelity = "same" | "stronger" | "weaker" | "different";

/**
 * Every state a comparison can be in. A verdict is one of the four above; "held" means a
 * comparison exists and is not shown yet; "unassessed" means none is recorded. A missing
 * comparison is never read as "same".
 */
export type Assessment = Fidelity | "held" | "unassessed";

/** "Not assessed": what the site says where no comparison of a statement and its Lean is recorded. */
export const NOT_ASSESSED = "Not assessed";
export const NOT_ASSESSED_DETAIL = "No comparison of these words with this Lean is recorded.";

/** Who compared them: the source repository's own evidence record, or an AI agent for this site. */
export type FidelitySource = "recorded" | "ai";

/** Who made a tie from a paper's statement to its Lean. */
export type TieOrigin = "evidence_record" | "ai";

export const FIDELITIES: readonly Fidelity[] = ["same", "stronger", "weaker", "different"];

/** "Says the same as the paper", "Says more than the paper", "Says less than the paper". */
export function verdictWords(fidelity: Fidelity, noun = "paper"): string {
  if (fidelity === "same") return `Says the same as the ${noun}`;
  if (fidelity === "stronger") return `Says more than the ${noun}`;
  if (fidelity === "different") return `States it differently from the ${noun}`;
  return `Says less than the ${noun}`;
}

/** The sentence a Lean panel leads with: "The Lean statement says the same as the paper." */
export function fidelitySentence(fidelity: Fidelity): string {
  if (fidelity === "same") return "The Lean statement says the same as the paper.";
  if (fidelity === "stronger") return "The Lean statement says more than the paper.";
  if (fidelity === "different") return "The Lean statement states it differently from the paper.";
  return "The Lean statement says less than the paper.";
}

/** How a phrase's Lean compares with the phrase, at the head of its note: "Lean states less". */
export function phraseVerdict(fidelity: Fidelity): string {
  if (fidelity === "same") return "Lean states the same as this phrase";
  if (fidelity === "stronger") return "Lean states more";
  if (fidelity === "different") return "Lean states it differently";
  return "Lean states less";
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

export const isFidelity = (value: unknown): value is Fidelity =>
  value === "same" || value === "stronger" || value === "weaker" || value === "different";
export const isAssessment = (value: unknown): value is Assessment => isFidelity(value) || value === "held" || value === "unassessed";
export const isTieOrigin = (value: unknown): value is TieOrigin => value === "evidence_record" || value === "ai";
