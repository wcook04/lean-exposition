// The SK site's What ran lead: the terms, then the table of what ran and what it leaves open
// (Standing.tsx), and the note on the one published build and extraction observation.

import site from "./site";
import type { EvidenceCard, KindGroup } from "../../checks/summary";
import { Standing } from "./Standing";

export function ChecksIntro({ groups }: { groups: KindGroup[] }) {
  return (
    <>
      <p className="standing-terms">{site.words.checksTerms}</p>
      <Standing groups={groups} />
    </>
  );
}

export function ChecksNote({ cards }: { cards: readonly EvidenceCard[] }) {
  if (!cards.some((card) => card.id === "full_support_v2_receipt_binding_20261026")) return null;
  return (
    <p className="checks__edition">
      The build and the extraction of 26 October 2026 are described in <a href={`${import.meta.env.BASE_URL}verification/full-support-build-extraction-observation-20261026.json`}>
        one published file
      </a>. That extraction covers the main theorem only, and its graph is partial and is not in this edition, so it changes no outcome above and says nothing about Comparator.
    </p>
  );
}
