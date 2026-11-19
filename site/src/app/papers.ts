// How the site names the three accounts and what each is for: the selected instance's
// words (src/instances/<id>/site.ts).

import site from "@instance/site";
import type { Stage } from "../api/types";

export const PAPER_NAMES: Record<Stage, { short: string; job: string; reader: string }> = site.paperNames;

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
