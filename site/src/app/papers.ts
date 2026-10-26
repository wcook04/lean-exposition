// How the site names the three accounts and what each is for. The sentences
// follow the documents' own introductions and the repository's reading guide;
// titles come from the documents themselves.

import type { Stage } from "../api/types";

export const PAPER_NAMES: Record<Stage, { short: string; job: string; reader: string }> = {
  expository: {
    short: "Exposition",
    job: "Learn the objects and the idea of the proof, starting from a two-spin calculation.",
    reader: "Assumes calculus, integration against measures and expectation.",
  },
  short: {
    short: "Short paper",
    job: "The result, its place in the literature and the decisive proof.",
    reader: "Assumes Itô calculus and martingale convergence.",
  },
  long: {
    short: "Long record",
    job: "Derivations, assumptions and source destinations, continuing to the QAOA circuits.",
    reader: "Enter at the step you want to check.",
  },
};

export const STAGE_ORDER: Stage[] = ["expository", "short", "long"];
