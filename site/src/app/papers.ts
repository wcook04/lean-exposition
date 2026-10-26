// How the site names the three accounts and what each is for. The sentences
// follow the documents' own introductions and the repository's reading guide;
// titles come from the documents themselves.

import type { Stage } from "../api/types";

export const PAPER_NAMES: Record<Stage, { short: string; job: string; reader: string }> = {
  expository: {
    short: "Exposition",
    job: "Explains the objects and the idea of the proof, starting from a calculation with two spins.",
    reader: "Written for readers who know calculus, integration against a measure and expectation.",
  },
  short: {
    short: "Short paper",
    job: "States the result, relates it to earlier work and proves it.",
    reader: "Written for readers who know Itô calculus and martingale convergence.",
  },
  long: {
    short: "Long record",
    job: "Reconstructs each derivation and assumption, names the source of each step, and continues to the QAOA circuits.",
    reader: "Written so that a reader can start at any step they want to examine.",
  },
};

export const STAGE_ORDER: Stage[] = ["expository", "short", "long"];
