// What ran, for a library paper: the terms; the table by kind follows.
import site from "./site";
import type { EvidenceCard, KindGroup } from "../../checks/summary";

export function ChecksIntro(_: { groups: KindGroup[] }) {
  return <p className="checks__terms">{site.words.checksTerms}</p>;
}

export function ChecksNote(_: { cards: readonly EvidenceCard[] }) {
  return null;
}
