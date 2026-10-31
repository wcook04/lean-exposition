// What an address names that the edition does not hold, in one plain sentence. The page itself
// stays usable and opens as it would with the name left out.

import type { Route } from "./router";

const AT = /^(?:\d+(?:-\d+)?|b\d+-\d+)$/;

/** Whether a reader's `l=` can land: well formed, and inside a paper of this many bytes and lines. */
export function atFits(at: string, bytes: number, lines: number): boolean {
  if (!AT.test(at)) return false;
  const numbers = at.replace(/^b/, "").split("-").map(Number);
  return at.startsWith("b") ? numbers[0] < numbers[1] && numbers[1] <= bytes : numbers.every((n) => n >= 1 && n <= lines) && numbers[0] <= numbers[numbers.length - 1];
}

export function addressProblem(route: Route, hasStep: (id: string) => boolean, paper?: { bytes: number; lines: number }): string | null {
  if (route.view === "map" && route.node && !hasStep(route.node)) return `No step named “${route.node}” on this map. This is the whole argument.`;
  if (route.view === "compare" && route.node && !hasStep(route.node)) return `No step named “${route.node}”. This is the table of every step.`;
  if (route.view === "read") {
    if (route.node && !hasStep(route.node)) return `No step named “${route.node}”. This is the paper.`;
    if (route.at && (paper ? !atFits(route.at, paper.bytes, paper.lines) : !AT.test(route.at))) return `No place “${route.at}” in this paper. This is the paper.`;
  }
  return null;
}
