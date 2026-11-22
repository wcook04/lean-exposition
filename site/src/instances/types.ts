// What one example of the site supplies: the SK example ("qaoa-sk") or Erdős problem #257
// ("erdos257"). The build chooses one with LX_INSTANCE (default "qaoa-sk"); the browser
// code reads it through the alias "@instance/site", and vite.config.ts reads the same object
// from the registry. Everything here is plain data and plain functions: no browser API, no
// import.meta and no React, because vite.config.ts runs it in Node.

import type { SiteFacts } from "../home/siteFacts.ts";

/** A document slot: one of the three accounts, or (a library paper's) a companion page. */
export type InstanceStage = string;

/** A record of the graph in a paper's terms (recordKind). */
export type RecordKind = "result" | "step" | "cited" | "open" | "declaration";

export interface InstancePdf {
  /** Relative to the repository root. */
  file: string;
  /** The published name under pdf/. */
  name: string;
  /** A second published path, keeping the papers' relative links between PDFs. */
  alias?: string;
}

export interface SiteInstance {
  /** The value of LX_INSTANCE that selects it. */
  id: string;
  /** The website's name in the family registry and the bar. */
  siteName: string;
  /** Its entry in the family registry (app/family.json), if it has one. */
  familyId: string | null;
  /** examples/<name> and papers/<name>, relative to the repository root. */
  example: string;
  papers: string;
  /** The edition's title, as the front page and the browser tab give it. */
  editionTitle: string;
  /** index.html's head and noscript text. */
  html: {
    description: string;
    ogTitle: string;
    ogDescription: string;
    /** HTML after the noscript paragraph's fixed first sentence. */
    noscript: string;
    /** Whether public/og.png is this site's card. */
    ogImage: boolean;
  };
  /** The published address when LX_SITE_URL is unset; null means the build has none. */
  defaultSiteUrl: string | null;
  /** The PDFs the build copies and counts pages of. */
  pdfs: Record<string, InstancePdf>;
  /** Verification files published under verification/, relative to the repository root. */
  publicObservations: { file: string; name: string }[];
  /**
   * Publish every receipt an evidence record of the graph names, and read them into the
   * What ran page's table of runs (checks/runs.ts). The SK site lists its one observation instead.
   */
  publishReceipts: boolean;
  sitePages: string[];
  routeTitles: Record<string, string>;
  /** README.md of the published repository. */
  readme(siteUrl: string, facts: SiteFacts): string;
  llms(siteUrl: string, facts: SiteFacts): string;
  /** The family registry's films this site shows, lead first. None hides every film slot. */
  films: { id: string; kicker: string }[];
  /** The first screen, as HTML, for the site's base path; `tex` typesets TeX. */
  hero(base: string, facts: SiteFacts, tex: (source: string) => string): string;
  /** Who linked a paper to the Lean, said one way everywhere. */
  linkCaveat: string;
  /** The step recording that two Lean models are not connected, where there is one. */
  modelsStep: string | null;
  /** The main theorem's record and how to find its statement in the short paper. */
  theorem: { record: string | null; paper: InstanceStage; pattern: string | null };
  /** The exposition step the first screen opens from its card. */
  heroStep: string | null;
  /** Build and extraction observation the facts read, relative to the example folder. */
  observation: string | null;
  /** The tie audit summary, relative to the example folder. */
  tieAudit: string | null;
  /** The Lean tree's own root folders and their descriptions. */
  lean: {
    mainTheorem: string | null;
    valueTheorem: string | null;
    minimizer: string | null;
    challengeFile: string | null;
    valueChallengeFile: string | null;
    /** A module of the main proof tree contains this, for ranking names. */
    mainTree: string | null;
    /** The module prefix of a separate model, for its note in the Lean view. */
    valueModel: string | null;
    /** Folder path to one sentence about it. */
    folderWords: Record<string, string>;
    /** Stripped from a folder path to name it. */
    folderPrefix: string;
    /** The root namespace a build record names its module under ("OAI"); null reads any dotted capitalised name. */
    moduleRoot: string | null;
    /** The Lean tree's top folders that a GitHub source link into lean/ may name; null takes any capitalised folder. */
    roots: string[] | null;
    /** Whose Lean this is, inside a sentence: "OpenAI’s". */
    owner: string;
    /** The vendored source, inside a sentence: "OpenAI's source". */
    ownerSource: string;
  };
  /** Short names for the argument's regions, keyed by goal id. */
  regionTitles: Record<string, string>;
  /** Each account's name and who it is for. */
  paperNames: Record<InstanceStage, { short: string; job: string; reader: string }>;
  /**
   * Sorts a record of the graph into the papers' terms, so that a sentence counting records says
   * what they are (results, proof steps, Lean declarations). Null keeps the SK site's single
   * word for every record, "step".
   */
  /**
   * The document slots this example uses, in reading order. Absent means all three
   * (exposition, short paper, long record); a library paper uses only the slots its data names.
   */
  stages?: InstanceStage[];
  /** The reader's line on who made the document and its links, in place of the draft and review words; absent keeps them. */
  paperStatus?: string;
  /** Shown where a comparison would be, when the paper's comparisons are held (fidelity "held"). */
  comparisonsHeld?: string;
  /**
   * A library paper: its id, its main document, its page slugs (page -> document), and its companion
   * documents in reading order, grouped (each a document of its own, answered from its own edition).
   */
  library?: {
    paper: string;
    main: InstanceStage;
    pages?: Record<string, string>;
    /** `id` names the companion's folder in its source (`<id>/paper.md`), so links between companions resolve. */
    companions?: { slot: string; id?: string; title: string; group: string; group_title: string; order: number }[];
  };
  /**
   * An adapted edition of the main document (instances/<paper>/adapted/, docs/reader-design.md
   * "Adapted editions"): a changed version of the authors' text in its own slot, read beside the
   * authors' own, with every change marked. Absent: the paper has none, or its flag is off.
   */
  adapted?: {
    slot: string;
    /** The authors' document it adapts. */
    of: InstanceStage;
    /** The edition's credit, verbatim, for its header and About. */
    credit: string;
    /** The authors' paper online, linked beside the credit. */
    authorsPaper?: string;
    /** The edition's PDFs, each with its label ("PDF with changes marked"). */
    pdfs: { label: string; name: string }[];
  };
  recordKind: ((node: { id: string; kind: string; status: string }) => RecordKind) | null;
  /**
   * The `supports` links ("from→to", node ids) the edition derived from the Lean's dependencies
   * rather than from the paper's own statements. Labels and counts call these "derived from the
   * Lean", never the paper's argument. Absent: every `supports` link is the paper's (or its
   * warrant says otherwise).
   */
  leanDerivedSupports?: ReadonlySet<string>;
  /**
   * A paper whose argument for the main theorem is its own record (the #257 exposition proves
   * Theorem A.1 at base two as its Theorem 1): the levels band draws that record's argument at
   * that paper's level. Null draws the main theorem's argument at every level.
   */
  levelGoals: Partial<Record<InstanceStage, string>> | null;
  /** The goal the front page's levels band and Compare start from; null takes the graph's first. */
  mainGoal: string | null;
  /** The Lean the levels band shows when a paper has no first-page picture. */
  levelsLeanSnippet: string | null;
  /** The levels band's line on the Lean level: whose statements and proofs. */
  leanLevelWho: string;
  /** Sentences shared components say about this example. */
  words: InstanceWords;
  /**
   * Wording the author writes, where the build warns about any slot still holding
   * "TODO(copy)"; null for an instance whose wording lives in its components.
   */
  copySlots: unknown;
}

export interface InstanceWords {
  /** Before a goal's name: "In the Sherrington–Kirkpatrick (SK) model, argument for". */
  argumentFor: string;
  /** Compare's definition of a step. */
  stepTerms: string;
  /** Compare's note on a step with no Lean. */
  leanAbsence(id: string): string;
  /** The map key's first sentence. */
  mapKeyIntro: string;
  /** The Lean view's note on a module of the separate model (lean.valueModel), and its link. */
  valueModelNote: string;
  valueModelLink: string;
  /** The checks page's first paragraph. */
  checksTerms: string;
  /** What ran: the note on dependency extraction records when none passed. */
  extractionNote: string;
  /** What ran: plain words for recorded failures, by evidence id. */
  failureWords: Record<string, string>;
}
