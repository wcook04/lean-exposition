// How the site names the three accounts and what each is for. The sentences
// follow the documents' own introductions and the repository's reading guide;
// titles come from the documents themselves.

import type { Stage } from "../api/types";

export const PAPER_NAMES: Record<Stage, { short: string; job: string; reader: string }> = {
  expository: {
    short: "Exposition",
    job: "The objects and the idea of the proof, starting from a calculation with two spins.",
    reader: "Written for readers who know algebra and calculus; probability and measures are introduced through calculations.",
  },
  short: {
    short: "Short paper",
    job: "The result, how it relates to earlier work and its proof, which cites the curvature estimate it depends on.",
    reader: "Written for readers who know Itô calculus and martingale convergence.",
  },
  long: {
    short: "Long record",
    job: "The derivations, with the source of each step and of each imported estimate, continuing to the circuits of the quantum approximate optimization algorithm (QAOA).",
    reader: "Written so that a reader can start at any step they want to examine.",
  },
};

export const STAGE_ORDER: Stage[] = ["expository", "short", "long"];

/** Each account as a sentence names it: "the short paper". */
export const ACCOUNT_IN_PROSE: Record<Stage, string> = {
  expository: "the exposition",
  short: "the short paper",
  long: "the long record",
};

/** Which accounts state a main result, in reading order: "In the exposition, the short paper and the long record". */
export function statedIn(stages: readonly Stage[]): string {
  const names = STAGE_ORDER.filter((s) => stages.includes(s)).map((s) => ACCOUNT_IN_PROSE[s]);
  if (names.length === 0) return "";
  const list = names.length === 1 ? names[0] : `${names.slice(0, -1).join(", ")} and ${names[names.length - 1]}`;
  return `In ${list}`;
}
