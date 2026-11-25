// Where Next and Previous go from the reading line, and what the paper shows of that before
// the reader presses either. One rule serves both, so a previewed link is the link Next lands on.

/** Where a statement stands against the reading line; undefined while it is not laid out. */
export type Side = "above" | "below" | undefined;

export interface StepFrom {
  /** The reader has not moved the paper since it opened at its start. */
  unstarted: boolean;
  /** The statement held by a selection, which steps start from. */
  pinned: number | null;
  /** The segment at the reading line, or null in an unlinked stretch. */
  segment: number | null;
  /** The part at the reading line. */
  part: number;
}

export interface StepWays {
  /** The tied statements a step can land on, in order. */
  stops: readonly number[];
  /** The step from a segment (ties.ts `stepFrom` over the same stops). */
  stepFrom(segment: number, by: 1 | -1): number | null;
  /** The opening segment of a statement. */
  segmentOf(t: number): number;
  partOf(t: number): number;
  /** Where a statement in the reading line's part stands against that line. */
  side?(t: number): Side;
}

/** The statement a step lands on, or null when there is none that way. */
export function stepTarget(by: 1 | -1, from: StepFrom, ways: StepWays): number | null {
  const { stops } = ways;
  if (from.unstarted && from.pinned === null) return stops[0] ?? null;
  const segment = from.pinned === null ? from.segment : ways.segmentOf(from.pinned);
  if (segment !== null) return ways.stepFrom(segment, by);
  // Between statements: from the reading line. In its own part a statement already passed is behind it.
  const passed = (t: number) => ways.side?.(t) === "above";
  const found = by > 0
    ? stops.find((t) => ways.partOf(t) > from.part || (ways.partOf(t) === from.part && !passed(t)))
    : stops.findLast((t) => ways.partOf(t) < from.part || (ways.partOf(t) === from.part && passed(t)));
  return found ?? null;
}

/** The link the paper shows before a step: the one Next lands on, else the last one behind the line. */
export interface LinkPreview {
  tie: number;
  at: string;
  /** "next": Next lands here. "last": nothing linked follows; this is the last link before the line. */
  kind: "next" | "last";
}

export function linkPreview(from: StepFrom, ways: StepWays, atOf: (t: number) => string): LinkPreview | null {
  const next = stepTarget(1, from, ways);
  if (next !== null) return { tie: next, at: atOf(next), kind: "next" };
  const last = stepTarget(-1, from, ways);
  return last === null ? null : { tie: last, at: atOf(last), kind: "last" };
}

export function samePreview(a: LinkPreview | null, b: LinkPreview | null): boolean {
  return a === b || (!!a && !!b && a.tie === b.tie && a.kind === b.kind);
}

/**
 * Whether the pane opens on the whole proof map at the top of this paper (MapPane's opening
 * view): the edition's main result is on the graph and the paper's passages name records on it.
 * A paper without one previews its next link instead.
 */
export function hasOpeningMap(
  onGraph: (id: string) => boolean,
  home: string | undefined,
  passages: readonly { claim_ids: readonly string[]; assumption_ids: readonly string[] }[],
): boolean {
  if (!home || !onGraph(home)) return false;
  return passages.some((p) => p.claim_ids.some(onGraph) || p.assumption_ids.some(onGraph));
}

/** The record or declaration a graph card names, and the passage of this paper that maps it. */
export interface GraphInspection {
  record?: string;
  decl?: { name: string; module?: string };
  /** Only a mapping this paper records: a tied statement, else a passage that names the record. */
  target: { at: string; tie: number } | { anchor: string } | null;
}

/**
 * The place a graph inspection's passage is mapped to: the statement the tie index gives the
 * record or declaration, else a passage of the paper that names the record. Nothing is inferred.
 */
export function inspectionTarget(
  statement: number | null,
  atOf: (t: number) => string,
  passage: string | null,
): GraphInspection["target"] {
  if (statement !== null) return { at: atOf(statement), tie: statement };
  return passage ? { anchor: passage } : null;
}
