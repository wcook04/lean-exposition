// Lean marks for the records of the argument. The relations ship in the record index, so the
// marks are there at first paint with nothing Lean-related on the startup path.

import type { ArgNode } from "../model/graph";
import { markOfDeclaration, markOfRelations, type LeanMark } from "../model/leanStatus";
import { recordLine } from "../compare/useAlignment";

/** Whether the papers treat this record as a definition: every level's strongest use of it defines it. */
function isDefinition(id: string, node: Pick<ArgNode, "kind">): boolean {
  if (node.kind === "assumption") return true;
  const levels = Object.values(recordLine(id)?.levels ?? {});
  return levels.length > 0 && levels.every((role) => role === "definition");
}

/** A record's mark. Pass it to ArgumentTree as `statusOf`. */
export function recordMark(id: string, node: Pick<ArgNode, "kind">): LeanMark {
  return markOfRelations(recordLine(id)?.relations ?? [], isDefinition(id, node));
}

export { markOfDeclaration };
