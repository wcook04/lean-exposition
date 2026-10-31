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
  /** Prefix of a line link: append `<path>#L<a>-L<b>`. */
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

/** First and last line, both inclusive and counted from 1. */
export type LineRange = [first: number, last: number];

export interface AlignedLean {
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

/** One marked statement. A landed pointer, never a check that the two texts mean the same. */
export interface Tie {
  record: string;
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
}

/** UTF-8 byte range and indices into `ties`, Lean first and then the narrowest slice. */
export type TieSegment = [startByte: number, endByte: number, ties: number[]];

/** A mapped passage's range, the records it discusses, and its anchor. */
export type TiePassage = [startByte: number, endByte: number, records: string[], anchor: string];

export interface TieIndex {
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

/** A line link into OpenAI's repository at the pinned revision. */
export function leanSourceUrl(modules: Pick<LeanModules, "base_url">, path: string, line: number, endLine?: number): string {
  return `${modules.base_url}${path}#L${line}${endLine && endLine !== line ? `-L${endLine}` : ""}`;
}
