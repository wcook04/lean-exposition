// The Lean index and the record alignment: two read-only sidecars of an edition.
// The index holds every declaration of OpenAI's vendored Lean with its source text;
// the alignment says where each record is stated, in Lean and in each paper. Neither
// is part of the startup data: pages load them when a reader first needs them. The tie
// index is the small part of the alignment a reader needs to mark one paper.
//
// A static edition also splits the alignment: a core that says where every statement is
// and which Lean it names, and one file for each paper with what that paper's statements
// say. The core and the paper files together are exactly `/alignment`, and one record can be
// asked for whole.

import { get } from "./client";
import type { Stage } from "./types";

export type LeanKind = "theorem" | "lemma" | "def" | "abbrev" | "structure" | "class" | "instance" | "inductive" | "opaque" | "axiom";

export interface LeanModuleRow {
  module: string;
  path: string;
  lines: number;
  declarations: number;
  sha256: string;
}

export interface LeanFolder {
  path: string;
  modules: LeanModuleRow[];
}

export interface LeanModules {
  revision: string;
  /** Prefix for a repository line link, or the DOI of an archived source. */
  base_url: string;
  toolchain: string;
  /** How `uses` and `used_by` were obtained; the site says so wherever it shows them. */
  dependency_source: "source_text" | "elaborated";
  /** What that way of finding names can miss, in words. */
  dependency_note?: string;
  counts: Record<string, number>;
  folders: LeanFolder[];
}

/** One declaration, packed for lookup: full name, kind, index into `modules`, first and last line. */
export type LeanNameRow = [name: string, kind: LeanKind, module: number, line: number, endLine: number];

export interface LeanNames {
  modules: string[];
  names: LeanNameRow[];
}

export interface LeanDeclaration {
  name: string;
  short: string;
  kind: LeanKind;
  namespace: string;
  line: number;
  /** The line where the statement ends, before `:=`, `by` or `where`. */
  signature_end_line: number;
  end_line: number;
  doc: string | null;
  private: boolean;
  uses: string[];
  used_by: string[];
  /** Set where an elaborated report covers this declaration. */
  dependency_source?: "source_text" | "elaborated";
}

export interface LeanModule {
  module: string;
  path: string;
  sha256: string;
  imports: string[];
  source: string;
  declarations: LeanDeclaration[];
}

/** How a Lean declaration relates to a record. docs/record-alignment.md defines each. */
export type LeanRelation = "states" | "contains" | "part" | "proof" | "defines";

export type { Fidelity, FidelitySource, TieOrigin } from "../compare/fidelityWords";

/**
 * What a Lean statement says against the paper's, where it has been compared: the same, more
 * (stronger) or less (weaker), with a note, and who compared them: "recorded" (taken from the
 * source repository's own evidence record) or "ai" (an AI agent, for this site). Optional:
 * an edition without them reads as before.
 */
export interface FidelityFields {
  /** A verdict, or "held" / "unassessed" (see Assessment); absent in editions that do not record one. */
  fidelity?: import("../compare/fidelityWords").Assessment;
  fidelity_note?: string;
  fidelity_source?: import("../compare/fidelityWords").FidelitySource;
}

/** One phrase's own comparison of a Lean row, kept when overlapping phrases share one tie. */
export interface PhraseAssessment {
  phrase: string;
  fidelity: import("../compare/fidelityWords").Assessment;
  fidelity_note?: string;
}

/** A phrase a merged tie holds: its id, its own words, role and topic. */
export interface MergedPhrase {
  id: string;
  quote: string;
  role?: string;
  topic?: string;
}

/** First and last line, both inclusive and counted from 1. */
export type LineRange = [first: number, last: number];

export interface AlignedLean extends FidelityFields {
  name: string;
  module: string;
  line: number;
  end_line: number;
  relation: LeanRelation;
  note: string;
  /** The declaration's plain title, where one is authored. */
  plain?: string;
  /** The lines to light, inside this declaration: the clause if it sits here, else the statement. Every row an edition delivers has them. */
  lines?: LineRange;
  /** A theorem's body, where it runs past the statement. Definitions have none. */
  proof_lines?: LineRange;
  /** An exact substring of the declaration's source, or of a definition shown under it. */
  clause?: string;
  /** The definition that holds the clause, when it is not this declaration. */
  clause_in?: string;
  clause_module?: string;
  clause_lines?: LineRange;
}

/** The Lean one statement means. `relation` is null for a name the record does not list. */
export type StatementLean = Omit<AlignedLean, "relation"> & { relation: LeanRelation | null };

export type StatementRole = "statement" | "definition" | "explanation" | "derivation" | "example" | "mention";

export interface AlignedStatement {
  paper: Stage;
  role: StatementRole;
  /** The exact slice of the paper's Markdown. */
  markdown: string;
  start_byte: number;
  end_byte: number;
  /** The slice's address, `b<start_byte>-<end_byte>`, shared with its tie. Delivered on every slice, like the next two. */
  at?: string;
  /** The Lean this slice means, most direct first. */
  lean?: StatementLean[];
  /** "statement" where the slice names its own Lean, "record" where it shows the record's rows. */
  lean_source?: "statement" | "record";
  /** The passage that holds the slice, if any, for a link into the reader. */
  anchor: string | null;
  /** The title of the section that holds the slice. */
  section: string;
  heading_id: string | null;
  note?: string;
  /**
   * Who tied the slice to its Lean: "evidence_record" (copied from the papers' published
   * evidence mapping) or "ai" (an AI agent read both and linked them for this site).
   */
  origin?: import("../compare/fidelityWords").TieOrigin;
}

export interface RecordAlignment {
  short: string;
  lean: AlignedLean[];
  statements: AlignedStatement[];
}

/** A statement as the core gives it: its place and the names of its Lean, not its words. */
export type StatementPlace = Omit<AlignedStatement, "markdown" | "lean" | "note"> & { lean?: { name: string }[] };

export interface RecordCore {
  short: string;
  lean: AlignedLean[];
  statements: StatementPlace[];
}

/** Every record's Lean, the place of every statement, the dictionary, the plain names and the steps. */
export interface AlignmentCore extends Omit<Alignment, "records"> {
  records: Record<string, RecordCore>;
  /** Set on a static edition's core, which needs its paper files to make `/alignment`. */
  representation?: "alignment_core";
}

/** What a paper's statements add to the core, each record's rows in the core's order. */
export interface AlignmentPaper {
  paper: Stage;
  records: Record<string, Pick<AlignedStatement, "markdown" | "lean" | "note">[]>;
}

export interface DictionaryTerm {
  /** Full Lean name, or `Structure.field` for a field. */
  name: string;
  module: string;
  line: number;
  tex: string | null;
  words: string;
  paper?: Stage;
  markdown?: string;
  anchor?: string | null;
}

export interface Alignment {
  records: Record<string, RecordAlignment>;
  dictionary: DictionaryTerm[];
  /** Plain titles of declarations, by full name, where authored. A title says what to call it, not what it proves. */
  names?: Record<string, string>;
  /** For a step between two records with Lean links, keyed by `ArgEdge.key`: the chain of names found in the source, or null. */
  steps?: Record<string, { route: string[] | null }>;
}

/**
 * One Lean row of a phrase tie: a declaration that states the phrase, the lines that do,
 * and how it compares with the phrase, as an AI agent judged it. `note` is the row's link
 * note (at most 25 words), `plain` the declaration's title in this part of this paper.
 */
export interface AnnotationReference {
  /** UTF-16 offsets in the exact exported annotation, excluding the end. */
  start: number;
  end: number;
  /** A target key in this edition's paper-reference manifest. */
  key: string;
}

export interface PhraseLean extends FidelityFields {
  /** Edited note for this passage and this declaration in this edition. */
  annotation?: string;
  /** An empty list records a review with no local destination. */
  annotation_references?: AnnotationReference[];
  name: string;
  module: string;
  line: number;
  end_line: number;
  lines: LineRange;
  /** The return named these lines; otherwise `lines` is the whole statement. */
  exact_lines?: boolean;
  proof_lines?: LineRange;
  relation: LeanRelation;
  note: string;
  plain?: string;
  /** In a tie that holds several overlapping phrases: every phrase's own comparison of this Lean. */
  assessments?: PhraseAssessment[];
  /** Whether this comparison's difference bears on the paper's main result, where the paper's data says. */
  matters?: ComparisonMatters;
}

/** One source an explanation rests on: what it is, where in it, and what it supports. */
export interface ExplanationCitation {
  ref: string;
  title: string;
  url?: string | null;
  where?: string;
  supports?: string;
}

/**
 * What a linked passage says, in the paper's notation, with the sources it rests on. `grounded`
 * false means part of it is not settled from the sources; `open` then says what is not.
 */
export interface PhraseExplanation {
  text: string;
  citations?: ExplanationCitation[];
  grounded?: boolean;
  open?: string;
}

/** Whether a difference between words and Lean bears on the main result, with one line of why. */
export interface ComparisonMatters {
  kind: "scope" | "granularity" | "convention" | "genuine-gap" | (string & {});
  affects_main_result: "yes" | "no" | "not settled" | (string & {});
  line?: string;
}

/**
 * A topic of a paper's phrase ties, in colour order: `part` is the part of the paper that lists it,
 * `tone` its index (the `--tone-N` it sets), `family` the family whose hue it takes a shade of, and
 * `light` and `dark` its stored colour in each theme (absent for a paper not yet coloured).
 */
export interface PhraseTopic {
  id: string;
  name: string;
  description: string;
  part: number;
  tone: number;
  family?: string;
  light?: string;
  dark?: string;
}

/** A family of topics, in hue order round the circle; `named` is false when derived from relatedness. */
export interface PhraseFamily {
  id: string;
  name: string;
  named: boolean;
  part: number;
  topics: string[];
}

/** A stretch of a paper with its own topics (one for most papers). */
export interface PhrasePart {
  name: string;
  start_byte: number;
  end_byte: number;
}

/** The titles and reading notes of each part of a paper, by declaration (`/phrases/<paper>`). */
export interface PhraseNotes {
  parts: { name: string; lines: LineRange; titles: Record<string, string>; notes: Record<string, string> }[];
  meaning: string;
}

/** One marked statement. A landed pointer, never a check that the two texts mean the same. */
export interface Tie {
  /**
   * The step on the argument map. A phrase that no step's Lean holds has none from the
   * server; the reader names it `phrase:<id>` so it can still be opened and addressed.
   */
  record: string;
  /** Phrase layer only: the phrase's id, topic, part, colour shade and every Lean row. */
  phrase?: string;
  /** Phrase layer only: what these words say, with its sources, where the paper's data carries it. */
  explanation?: PhraseExplanation;
  topic?: string;
  part?: number;
  /** The topic's colour index (see PhraseTopic.tone). */
  tone?: number;
  rows?: PhraseLean[];
  /** The phrases this tie holds when the source's phrases overlapped and were merged into one. */
  merged?: MergedPhrase[];
  role: StatementRole;
  /** Whether the statement has any Lean. The other Lean fields are null when it has none. */
  lean: boolean;
  /** How the first Lean row stands to the statement: `part` means it covers only part of it. */
  relation?: LeanRelation;
  /** Where a statement has no Lean, what its authors say about that. */
  note?: string;
  /** The most direct declaration; the rest are on the statement with this `at` in the alignment. */
  name: string | null;
  /** That declaration's plain title, where one is authored. */
  plain?: string;
  module: string | null;
  lines: LineRange | null;
  anchor: string | null;
  at: string;
  /** Who made the tie (see AlignedStatement.origin); absent in editions that do not say. */
  origin?: import("../compare/fidelityWords").TieOrigin;
  /** What the first Lean row says against the statement (see FidelityFields). */
  fidelity?: import("../compare/fidelityWords").Assessment;
  fidelity_note?: string;
  fidelity_source?: import("../compare/fidelityWords").FidelitySource;
}

/** UTF-8 byte range and indices into `ties`, Lean first and then the narrowest slice. */
export type TieSegment = [startByte: number, endByte: number, ties: number[]];

/** A mapped passage's range, the records it discusses, and its anchor. */
export type TiePassage = [startByte: number, endByte: number, records: string[], anchor: string];

export interface TieIndex {
  /** "phrases" when each tie is a phrase that one or more declarations state. */
  layer?: "phrases";
  /** The paper's main result in words, for "Does this affect the main result?". */
  main_result?: string;
  /**
   * Each record's one canonical target in this paper: the tie at its statement block, and the
   * block's UTF-8 byte range. An address, search result, Copy link, Compare and the graph that name
   * the record without a place all land here; with no tie there (null), on the block itself.
   * Absent in editions exported before it existed.
   */
  canonical?: Record<string, [tie: number | null, startByte: number, endByte: number]>;
  topics?: PhraseTopic[];
  families?: PhraseFamily[];
  parts?: PhrasePart[];
  segments: TieSegment[];
  ties: Tie[];
  passages: TiePassage[];
  meaning: string;
}

/** Whether this edition carries the sidecars. An edition without them still reads in full. */
export const loadLeanModules = () => get<LeanModules>("/lean/modules").then((r) => r.data);
export const loadLeanNames = () => get<LeanNames>("/lean/names").then((r) => r.data);
export const loadLeanModule = (name: string) => get<LeanModule>("/lean/module", { name }).then((r) => r.data);
export const loadAlignment = () => get<Alignment>("/alignment").then((r) => r.data);
export const loadAlignmentCore = () => get<AlignmentCore>("/alignment/core").then((r) => r.data);
export const loadAlignmentRecord = (id: string) => get<RecordAlignment>("/alignment/record", { id }).then((r) => r.data);
export const loadAlignmentPaper = (stage: Stage) => get<AlignmentPaper>(`/alignment/${stage}`).then((r) => r.data);
export const loadTies = (stage: Stage) => get<TieIndex>(`/ties/${stage}`).then((r) => r.data);
export const loadPhraseNotes = (stage: Stage) => get<PhraseNotes>(`/phrases/${stage}`).then((r) => r.data);

/** The core with the words of these papers' statements put back. With all three it equals `/alignment`. */
export function withPapers<T extends AlignmentCore>(core: T, papers: readonly AlignmentPaper[]): T {
  const stages = new Set(papers.map((paper) => paper.paper));
  const records = Object.fromEntries(
    Object.entries(core.records).map(([id, record]) => {
      const left = new Map(papers.map((paper) => [paper.paper, [...(paper.records[id] ?? [])]]));
      const statements = record.statements.map((row) => (stages.has(row.paper) ? { ...row, ...left.get(row.paper)!.shift() } : row));
      return [id, { ...record, statements }];
    }),
  );
  return { ...core, records };
}

/** The pinned repository lines or the authors’ archived source record. */
export function leanSourceUrl(modules: Pick<LeanModules, "base_url" | "revision">, path: string, line: number, endLine?: number): string {
  if (modules.revision.startsWith("https://doi.org/")) return modules.revision;
  return `${modules.base_url}${path}#L${line}${endLine && endLine !== line ? `-L${endLine}` : ""}`;
}
