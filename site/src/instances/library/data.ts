// The library paper this build is for, as data: instances/<LX_PAPER>/instance.json, copied to
// current.json by scripts/library-instance.mjs before a build. No code here is a paper's own.
import current from "./current.json";

/** A PDF of a document; `label` names it in the header ("PDF with changes marked"). */
export interface LibraryPdf { file: string; sha256?: string; bytes?: number; url?: string; name?: string; alias?: string; label?: string }
export interface LibraryDocument {
  id: string;
  /** One of the three accounts (long, short, expository), or a companion's own page name (digest, library-07). */
  slot: string;
  slug: string;
  title: string;
  noun: string;
  main?: boolean;
  /** The authors' PDF. `name` and `alias` publish it under pdf/ by those names (a reader that moved into the library keeps its PDF addresses). */
  pdf?: LibraryPdf;
  /** A companion document: read in its own right, grouped and ordered in the paper's contents. */
  kind?: "companion" | "adapted";
  group?: string;
  group_title?: string;
  order?: number;
  credit?: string;
  /** An adapted edition of another document (`of`, its id): a companion page with its own credit, a
   *  change map and its PDF with changes marked; read only when `published` (or in a local preview). */
  adapted?: boolean;
  of?: string;
  published?: boolean;
  aux_pdf?: LibraryPdf;
  /** What the document does and who it is written for, in place of the reader's default account line. */
  job?: string;
  reader?: string;
}

/** A section of About, in the paper's own words: TeX between single dollar signs is typeset. */
export interface AboutSection { heading: string; paragraphs?: string[]; links?: { label: string; href: string }[] }

/**
 * The reader settings a paper that moved into the library from its own reader keeps (the SK and
 * Erdős #257 readers): every field is plain data, read into the library instance (site.ts) in
 * place of its default. Absent fields keep the library's defaults.
 */
export interface ReaderSettings {
  publish_receipts?: boolean;
  public_observations?: { file: string; name: string }[];
  observation?: string | null;
  tie_audit?: string | null;
  theorem?: { record: string | null; paper: "long" | "short" | "expository"; pattern: string | null };
  hero_step?: string | null;
  models_step?: string | null;
  level_goals?: Partial<Record<"long" | "short" | "expository", string>> | null;
  levels_lean_snippet?: string | null;
  lean_level_who?: string;
  /** Graph ids matching this pattern are proof steps written out from the papers (recordKind "step"). */
  step_records?: string;
  link_caveat?: string;
  region_titles?: Record<string, string>;
  films?: { id: string; kicker: string }[];
  lean?: Partial<{
    mainTheorem: string | null; valueTheorem: string | null; minimizer: string | null; challengeFile: string | null; valueChallengeFile: string | null;
    mainTree: string | null; valueModel: string | null; folderWords: Record<string, string>; folderPrefix: string; moduleRoot: string | null;
    roots: string[] | null; owner: string; ownerSource: string;
  }>;
  words?: Partial<{
    argumentFor: string; stepTerms: string; mapKeyIntro: string; extractionNote: string; failureWords: Record<string, string>;
    valueModelNote: string; valueModelLink: string; checksTerms: string;
    /** Compare's note on a step with no Lean: the first rule whose prefix the step's id starts with, else `default`. */
    leanAbsence: { default: string; prefixes?: { prefix: string; text: string }[] };
  }>;
  /** The lead of What ran: "ledger" (a table from the run receipts), "observation" (from the published build and extraction observation), or none. */
  checks_lead?: "ledger" | "observation";
  /** Rows the What ran lead adds after its own: a question, what ran and what that leaves open. */
  checks_rows?: { name: string; did: string; open: string }[];
  /** A note under What ran's table, shown when the run record `card` is listed, linking one published file. */
  checks_note?: { card: string; before: string; link: string; file: string; after: string };
  /** More PDFs to publish under pdf/ (an architectural companion), relative to the repository root. */
  extra_pdfs?: Record<string, { file: string; name: string }>;
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
  /** The paper's own levels, in order (document slots), where it has several accounts of one argument (SK, #257). */
  levels?: string[];
  comparisons_hidden?: boolean;
  /** What the formal development does in each section, by section number or title (generated/section-aids.json). */
  section_aids?: Record<string, string>;
  /** Which guides the paper has, known to the build (generated/showcase.json, route.json). */
  reading_aids?: { showcase: boolean; route: boolean };
  comparisons_held_text?: string;
  /** About's own sections, before the reader's shared ones. */
  about?: AboutSection[];
  /** Figures drawn from a file of the reading copy (`file` in papers/<slot>/figures/) or by a shared figure component, by the figure's label. */
  figures?: Record<string, { slot: string; file: string } | { component: string }>;
  reader?: ReaderSettings;
  /** Written by scripts/library-instance.mjs: supports links ("from→to") whose only evidence is the Lean's dependencies. */
  lean_derived_supports?: string[];
}

export const PAPER = current as LibraryInstance;
export const MAIN = PAPER.documents.find((d) => d.main) ?? PAPER.documents[0];
export const LIBRARY_ROOT = "https://wcook04.github.io/library/";
