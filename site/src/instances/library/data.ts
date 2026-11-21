// The library paper this build is for, as data: instances/<LX_PAPER>/instance.json, copied to
// current.json by scripts/library-instance.mjs before a build. No code here is a paper's own.
import current from "./current.json";

export interface LibraryDocument {
  id: string;
  /** One of the three accounts (long, short, expository), or a companion's own page name (digest, library-07). */
  slot: string;
  slug: string;
  title: string;
  noun: string;
  main?: boolean;
  pdf?: { file: string; sha256: string; bytes: number; url: string };
  /** A companion document: read in its own right, grouped and ordered in the paper's contents. */
  kind?: "companion";
  group?: string;
  group_title?: string;
  order?: number;
  credit?: string;
}
export interface LibraryInstance {
  schema: string;
  id: string;
  title: string;
  short_title: string;
  authors: string[];
  venue: string;
  credit_lines: string[];
  /** The credit line companion pages carry: the authors and their repository only. */
  companion_credit?: string;
  /** The authors' licence for their paper and Lean, as the source states it. */
  licence?: string;
  host: string;
  review: string;
  source: { proof_reader?: { repository: string; commit: string; page: string }; upstream: { repository: string; commit: string; paper?: string }; lean_scope?: string };
  documents: LibraryDocument[];
  families: { id: string; name: string }[];
  topics: { id: string; name: string; description: string; family: string | null }[];
  topic_order: string[];
  goal: string;
  main_lean?: string | null;
  comparisons_hidden?: boolean;
  comparisons_held_text?: string;
  /** Written by scripts/library-instance.mjs: supports links ("from→to") whose only evidence is the Lean's dependencies. */
  lean_derived_supports?: string[];
}

export const PAPER = current as LibraryInstance;
export const MAIN = PAPER.documents.find((d) => d.main) ?? PAPER.documents[0];
export const LIBRARY_ROOT = "https://wcook04.github.io/library/";
