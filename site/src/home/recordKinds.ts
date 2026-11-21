// The graph's records counted in the papers' terms, for an instance that sorts them
// (SiteInstance.recordKind). Runs in the browser and in vite.config.ts: no browser API.

import type { RecordKind } from "../instances/types.ts";

export const KIND_ORDER: RecordKind[] = ["result", "step", "cited", "open", "declaration"];

const WORDS: Record<RecordKind, { one: string; many: string; brief: [string, string] }> = {
  result: { one: "result printed in the papers", many: "results printed in the papers", brief: ["result", "results"] },
  step: { one: "proof step an AI agent wrote out from the papers", many: "proof steps an AI agent wrote out from the papers", brief: ["proof step", "proof steps"] },
  cited: { one: "cited result", many: "cited results", brief: ["cited result", "cited results"] },
  open: { one: "open question", many: "open questions", brief: ["open question", "open questions"] },
  declaration: { one: "Lean declaration", many: "Lean declarations", brief: ["Lean declaration", "Lean declarations"] },
};

export type KindCounts = Record<RecordKind, number>;

export function countKinds(nodes: Iterable<{ id: string; kind: string; status: string }>, kindOf: (node: { id: string; kind: string; status: string }) => RecordKind): KindCounts {
  const out: KindCounts = { result: 0, step: 0, cited: 0, open: 0, declaration: 0 };
  for (const node of nodes) out[kindOf(node)] += 1;
  return out;
}

const n = (value: number) => value.toLocaleString("en-GB");

function list(parts: string[]): string {
  return parts.length < 2 ? parts.join("") : `${parts.slice(0, -1).join(", ")} and ${parts[parts.length - 1]}`;
}

/** "184 results printed in the papers, 35 proof steps … and 458 Lean declarations"; zero counts are left out. */
export function kindsInWords(counts: KindCounts, brief = false): string {
  return list(
    KIND_ORDER.filter((kind) => counts[kind] > 0).map((kind) => {
      const words = WORDS[kind];
      const word = brief ? words.brief[counts[kind] === 1 ? 0 : 1] : counts[kind] === 1 ? words.one : words.many;
      return `${n(counts[kind])} ${word}`;
    }),
  );
}
