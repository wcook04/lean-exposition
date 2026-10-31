// What ran, in the words of the What ran page, built from the same records and
// the same counting. The Lean page's first screen says it once and links to the page itself.

import { useMemo, type ReactNode } from "react";
import { useEdition } from "../app/data";
import { useEvidence } from "../checks/evidence";
import { countsInWords, groupByKind, recordsWord, statedDate, type EvidenceCard } from "../checks/summary";

export function useCheckedWords(): ReactNode {
  const { graph, map } = useEdition();
  const cards = map.records.evidence as EvidenceCard[];
  const groups = useMemo(() => groupByKind(cards), [cards]);
  const of = (kind: string) => groups.find((group) => group.kind === kind);
  const passed = useMemo(() => cards.filter((card) => card.kind === "lean_build" && card.status === "passed"), [cards]);
  const evidence = useEvidence(useMemo(() => passed.map((card) => card.ref), [passed]));
  const record = evidence.status === "ready" && passed[0] ? evidence.records.get(passed[0].ref) : undefined;
  const module = /\bOAI(?:\.\w+)+/.exec(record?.details ?? "")?.[0];
  const version = /(\d+\.\d+\.\d+)/.exec(record?.tool ?? "")?.[1];
  const date = statedDate(record?.details);
  const subject = record?.subject_ids?.[0] ? graph.nodes.get(record.subject_ids[0]) : undefined;
  const comparator = of("comparator");
  const reviews = of("semantic_review");
  return (
    <>
      {record ? (
        <>
          Lean compiled {module ? <code>{module}</code> : "the Lean file"}
          {subject ? <>, the module recorded for <code>{subject.label}</code>,</> : null} without an error
          {version ? ` on version ${version}` : ""}
          {date ? `; the run record of that build is dated ${date.text}` : ""}.{" "}
        </>
      ) : passed.length === 0 ? (
        <>No Lean build is recorded as passed. </>
      ) : null}
      {comparator && comparator.cards.length > 0 && (
        <>
          Comparator has {comparator.counts.passed ? `${comparator.counts.passed} passed` : "no successful result"}: of its {recordsWord(comparator.cards.length)}, {countsInWords(comparator.counts)}.{" "}
        </>
      )}
      {reviews && reviews.cards.length > 0 && !reviews.counts.passed && <>The {reviews.cards.length} correspondence reviews are written but none has been independently run, so no one has confirmed that the papers and the Lean say the same thing. </>}
    </>
  );
}
