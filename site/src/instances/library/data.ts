// The library paper this build is for, as data: instances/<LX_PAPER>/instance.json, copied to
// current.json by scripts/library-instance.mjs before a build. No code here is a paper's own.
import current from "./current.json";

/**
 * One document of the paper. A document in this build has a slot; a document of the same paper read in
 * another build (a fourth document, or the page a guide belongs to) has no slot and an `href`, its
 * address under the library root ("pcp/reading-guide/").
 */
export interface LibraryDocument { id: string; slot?: "long" | "short" | "expository"; href?: string; slug: string; title: string; noun: string; main?: boolean; pdf?: { file: string; sha256: string; bytes: number; url: string } }
export interface LibraryInstance {
  schema: string;
  id: string;
  /** Where the paper is served under the library root, when not at its id ("pcp/reading-guide"). */
  path?: string;
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
  source: { proof_reader?: { repository: string; commit: string; page: string }; upstream: { repository: string; commit: string; paper?: string | null }; lean_scope?: string };
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
export const MAIN = (PAPER.documents.find((d) => d.main) ?? PAPER.documents[0]) as LibraryDocument & { slot: NonNullable<LibraryDocument["slot"]> };
/** The documents this build carries. */
export const BUILT = PAPER.documents.filter((d): d is LibraryDocument & { slot: NonNullable<LibraryDocument["slot"]> } => !!d.slot);
export const LIBRARY_ROOT = "https://wcook04.github.io/library/";
