// What the Lean holds of a record, read from the alignment and from nothing else.
//
// A blueprint has one signal for "the statement is in Lean" and one for "the proof is in
// Lean". The alignment says the same thing more finely, row by row, in its relations
// (docs/record-alignment.md): `states` and `contains` give the record's claim, `part` gives
// one part of it, `proof` carries the step in a different form, and `defines` gives an
// object. So each signal has three levels: the whole of it, part of it, or none.
//
// In this edition all 162 rows keep one rule: a row other than `defines` names a theorem or
// a lemma, with no `sorry` in its text. That is what "proved in Lean" means on this site: a
// proof is written in OpenAI's source. useLeanGraph reads the text of each declaration it
// draws; the record marks rest on the rule. Whether a build ran is a separate record, in the
// sheet's checks.

export type LeanLevel = "whole" | "part" | "none";

export interface LeanMark {
  /** A box for a definition, a rounded shape for a result. */
  shape: "box" | "round";
  statement: LeanLevel;
  proof: LeanLevel;
}

export type RecordLeanRelation = "states" | "contains" | "part" | "proof" | "defines";

/** The Lean mark of a record, from its rows' relations. `definition` says the papers define it, or that it is an assumption. */
export function markOfRelations(relations: readonly string[], definition: boolean): LeanMark {
  const has = (r: RecordLeanRelation) => relations.includes(r);
  const states = has("states") || has("contains");
  const onlyDefines = has("defines") && !states && !has("part") && !has("proof");
  const box = definition || onlyDefines;
  return {
    shape: box ? "box" : "round",
    statement: states || (box && has("defines")) ? "whole" : has("part") ? "part" : "none",
    proof: states || has("proof") ? "whole" : has("part") ? "part" : "none",
  };
}

/** The mark of one Lean declaration. A theorem or lemma states and proves; a definition states, and has nothing to prove. */
export function markOfDeclaration(kind: string, hasSorry: boolean): LeanMark {
  const result = kind === "theorem" || kind === "lemma";
  return { shape: result ? "round" : "box", statement: "whole", proof: result && !hasSorry ? "whole" : "none" };
}

/**
 * The card's fill. Green for a record the Lean holds whole: stated and proved, or defined.
 * Much paler for a part of it, which takes in a proof carried in a different form. Plain for none.
 */
export function leanFill({ shape, statement, proof }: LeanMark): LeanLevel {
  if (statement === "none" && proof === "none") return "none";
  return statement === "whole" && (proof === "whole" || shape === "box") ? "whole" : "part";
}

/** The mark in words, as the outline, the sheet and the caption say it. */
export function markWords(mark: LeanMark): string {
  const { shape, statement, proof } = mark;
  if (statement === "none" && proof === "none") return "No Lean linked";
  if (shape === "box") return proof === "none" ? "Linked to a Lean definition" : "Linked to a Lean definition, with some of it proved";
  if (statement === "whole") return proof === "whole" ? "Linked to Lean that states and proves it" : proof === "part" ? "Linked to a Lean statement, with some of it proved" : "Linked to a Lean statement with no proof";
  if (statement === "part") return proof === "whole" ? "Linked Lean states some of it and proves the step" : "Linked Lean states and proves some of it";
  return proof === "whole" ? "Linked Lean proves the step in a different form" : "Linked Lean proves some of it";
}
