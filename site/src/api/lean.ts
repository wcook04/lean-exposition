// The Lean index and the record alignment: two read-only sidecars of an edition.
// The index holds every declaration of OpenAI's vendored Lean with its source text;
// the alignment says where each record is stated, in Lean and in each paper. Neither
// is part of the startup data: pages load them when a reader first needs them.

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

export interface AlignedLean {
  name: string;
  module: string;
  line: number;
  end_line: number;
  relation: LeanRelation;
  note: string;
}

export type StatementRole = "statement" | "definition" | "explanation" | "derivation" | "example" | "mention";

export interface AlignedStatement {
  paper: Stage;
  role: StatementRole;
  /** The exact slice of the paper's Markdown. */
  markdown: string;
  start_byte: number;
  end_byte: number;
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
}

/** Whether this edition carries the sidecars. An edition without them still reads in full. */
export const loadLeanModules = () => get<LeanModules>("/lean/modules").then((r) => r.data);
export const loadLeanNames = () => get<LeanNames>("/lean/names").then((r) => r.data);
export const loadLeanModule = (name: string) => get<LeanModule>("/lean/module", { name }).then((r) => r.data);
export const loadAlignment = () => get<Alignment>("/alignment").then((r) => r.data);

/** A line link into OpenAI's repository at the pinned revision. */
export function leanSourceUrl(modules: Pick<LeanModules, "base_url">, path: string, line: number, endLine?: number): string {
  return `${modules.base_url}${path}#L${line}${endLine && endLine !== line ? `-L${endLine}` : ""}`;
}
