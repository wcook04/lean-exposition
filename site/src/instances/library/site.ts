// The library instance: one paper of the reading library, read entirely from its data
// (data.ts, from instances/<paper>/instance.json). Every sentence about the paper is the
// data's; the sentences here are about how the reader works. No browser API, no import.meta.

import type { SiteFacts } from "../../home/siteFacts.ts";
import type { RecordKind, SiteInstance } from "../types.ts";
import { PAPER, MAIN, LIBRARY_ROOT } from "./data.ts";

const ADAPTED = PAPER.documents.find((d) => d.adapted);

const n = (value: number) => value.toLocaleString("en-GB");
const plain = (text: string) => text.replace(/\$([^$]+)\$/g, "$1");
const authors = (list: string[]) => (list.length < 2 ? list.join("") : `${list.slice(0, -1).join(", ")} and ${list[list.length - 1]}`);
const BY = authors(PAPER.authors);
const LINK_CAVEAT = PAPER.review;
const empty = { short: "", job: "", reader: "" };
const paperNames = { long: empty, short: empty, expository: empty } as SiteInstance["paperNames"];
// The account line reads as sentences: "<title>, by <authors>." then the status sentence. A
// sentence ending in a formula or abbreviation keeps its own stop.
const sentence = (text: string) => (/[.!?]$/.test(text.trim()) ? text.trim() : `${text.trim()}.`);
/**
 * The credit lines without what the review sentence already says. A paper's credit line often carries
 * its own "made with AI" sentence, and the account line then adds the review; each sentence about AI
 * and review is said once, in the review, followed by "No mathematician has reviewed them.".
 */
export function creditWithoutReview(credit: readonly string[], review: string): string {
  const sentences = (text: string) => text.split(/(?<=[.!?])\s+(?=[A-Z])/).map((t) => t.trim()).filter(Boolean);
  const said = new Set(sentences(review ?? "").map((t) => t.replace(/[.!?]$/, "")));
  const aboutAi = /\bwith AI\b|\bAI-(?:drafted|assessed)\b/i;
  const reviewSaysAi = aboutAi.test(review ?? "");
  return credit
    .flatMap((line) => sentences(sentence(line)))
    .filter((t) => !said.has(t.replace(/[.!?]$/, "")) && !(reviewSaysAi && aboutAi.test(t)))
    .map(sentence)
    .join(" ");
}
const CREDIT = creditWithoutReview(PAPER.credit_lines, PAPER.review);
/**
 * The paper's credit as one short line under its authors: the first sentence of the credit (the authors,
 * their repository and commit, and Anthropic where the paper thanks it), then the review sentence. About
 * carries the whole credit.
 */
export function frontCreditLine(credit: string, review: string): string {
  // A sentence ends at a stop after a word, not after an initial ("Matei P. Coiculescu").
  const first = credit.split(/(?<=[a-z0-9)\]][.!?])\s+(?=[A-Z])/)[0]?.trim() ?? "";
  return [first, review.trim()].filter(Boolean).join(" ");
}
const isAdapted = (d: (typeof PAPER.documents)[number]) => !!d.adapted || d.kind === "adapted";
/** The documents a reader opens from Read: the authors' paper, its own levels where it has them, and an adapted edition. */
const READ_MENU = [
  ...(PAPER.levels?.length ? PAPER.levels.filter((slot) => PAPER.documents.some((d) => d.slot === slot)) : [MAIN.slot]),
  ...PAPER.documents.filter(isAdapted).map((d) => d.slot),
];
/** Compare's levels: the Lean, then the paper's own documents in the three level slots, never one it lacks. */
const LEVEL_SLOTS = ["long", "short", "expository"] as const;
const COMPARE_LEVELS = ["lean" as const, ...LEVEL_SLOTS.filter((slot) => PAPER.documents.some((d) => d.slot === slot && !isAdapted(d) && (d.main || (PAPER.levels ?? []).includes(slot))))];
// The paper itself is the authors': its header carries their full credit line, once. A companion page
// (an account or a guide) is about it, written for this reader with AI, and names the authors and their
// repository only (companion_credit).
// A document that says what it does and who it is for (doc.job, doc.reader) keeps its own words.
for (const doc of PAPER.documents)
  paperNames[doc.slot] = doc.adapted
    ? // The adapted edition's header carries its own credit, whole; the authors' paper keeps theirs.
      { short: "Adapted edition", job: sentence(`${doc.title}, an adapted edition`), reader: doc.credit ?? "" }
    : doc.main
    ? { short: doc.title, job: doc.job ?? sentence(`${doc.title}, by ${BY}`), reader: doc.reader ?? CREDIT }
    : {
        short: doc.title,
        job: doc.job ?? sentence(`${doc.title}: a ${doc.noun} to ${PAPER.title}, written for this reader with AI`),
        reader: doc.reader ?? (PAPER.companion_credit ? sentence(PAPER.companion_credit) : ""),
      };

// The settings of a paper that moved in from its own reader (instance.json "reader"); absent keeps the defaults.
const R = PAPER.reader ?? {};
const stepRecords = R.step_records ? new RegExp(R.step_records) : null;
const absence = R.words?.leanAbsence;

function readme(siteUrl: string, facts: SiteFacts): string {
  const at = (path: string) => (siteUrl ? `${siteUrl}${path}` : path);
  return `# ${plain(PAPER.title)}

By ${BY}. ${CREDIT}

**[Read it](${at("")})** · [The library](${LIBRARY_ROOT}) · [Source and tools](https://github.com/wcook04/lean-exposition)

${PAPER.review}
${facts.lean ? `\nThe Lean shown here has ${n(facts.lean.modules)} modules and ${n(facts.lean.declarations)} declarations.\n` : ""}`;
}

function llms(siteUrl: string, facts: SiteFacts): string {
  const at = (path: string) => (siteUrl ? `${siteUrl}${path}` : path);
  return `# ${plain(PAPER.title)}

> ${plain(PAPER.title)}, by ${BY}, read beside its Lean. ${CREDIT}

${PAPER.review}

## Read

- [${plain(MAIN.title)}](${at("")})

## Data

All data is static JSON under ${at("edition/")}. Start at edition/index.json: it maps API routes to files.
${facts.lean ? `\nThe Lean index has ${n(facts.lean.modules)} modules and ${n(facts.lean.declarations)} declarations.\n` : ""}`;
}

function recordKind(node: { id: string; kind: string; status: string }): RecordKind {
  if (node.kind === "declaration") return "declaration";
  if (node.status === "open") return "open";
  if (node.status === "external") return "cited";
  if (stepRecords?.test(node.id)) return "step";
  return "result";
}

const site = {
  id: "library",
  siteName: plain(PAPER.short_title),
  familyId: null,
  example: `instances/${PAPER.id}`,
  papers: `instances/${PAPER.id}/papers`,
  editionTitle: plain(PAPER.title),
  html: {
    description: `${plain(PAPER.title)}, by ${BY}, read sentence by sentence beside its Lean.`,
    ogTitle: plain(PAPER.title),
    ogDescription: `By ${BY}. Each phrase opens the Lean that states it.`,
    noscript: `The paper and its Lean are in the repository under <code>instances/${PAPER.id}/</code>.`,
    ogImage: false,
  },
  defaultSiteUrl: `${LIBRARY_ROOT}${PAPER.id}/`,
  pdfs: {
    ...Object.fromEntries(
      PAPER.documents
        .filter((d) => d.pdf)
        .map((d) => [d.slot, { file: `instances/${PAPER.id}/papers/${d.slot}/${d.pdf!.file}`, name: d.pdf!.name ?? (d.slug ? `${d.slug}.pdf` : "paper.pdf"), ...(d.pdf!.alias ? { alias: d.pdf!.alias } : {}) }]),
    ),
    ...(R.extra_pdfs ?? {}),
  },
  publicObservations: R.public_observations ?? [],
  publishReceipts: R.publish_receipts ?? false,
  sitePages: [""],
  routeTitles: {
    map: "Argument map", compare: "Compare", lean: "Lean index", checks: "What ran", about: "About", search: "Search",
    ...Object.fromEntries(PAPER.documents.map((d) => [`read/${d.slot}`, plain(d.title)])),
  },
  readme,
  llms,
  films: R.films ?? [],
  hero: () => "",
  linkCaveat: R.link_caveat ?? LINK_CAVEAT,
  modelsStep: R.models_step ?? null,
  theorem: R.theorem ?? { record: PAPER.goal, paper: MAIN.slot, pattern: null },
  heroStep: R.hero_step ?? null,
  observation: R.observation ?? null,
  tieAudit: R.tie_audit ?? null,
  lean: {
    mainTheorem: PAPER.main_lean ?? null, valueTheorem: null, minimizer: null, challengeFile: null, valueChallengeFile: null,
    mainTree: null, valueModel: null, folderWords: {}, folderPrefix: "", moduleRoot: null, roots: null,
    owner: `${BY}’s`, ownerSource: `${BY}’s source`,
    ...R.lean,
  },
  regionTitles: R.region_titles ?? {},
  paperNames,
  // The reader's accounts; companion documents are listed apart (library.companions), by group.
  stages: PAPER.documents.filter((d) => d.kind !== "companion").map((d) => d.slot),
  paperStatus: PAPER.review ? sentence(PAPER.review) : undefined,
  frontCredit: { [MAIN.slot]: frontCreditLine(CREDIT, PAPER.review) },
  readMenu: READ_MENU,
  readMenuJobs: Object.fromEntries(
    PAPER.documents.filter((d) => READ_MENU.includes(d.slot)).map((d) => [d.slot, isAdapted(d) ? "An adapted edition, every change marked" : d.main && !PAPER.levels?.length ? `By ${BY}` : undefined]),
  ),
  compareLevels: COMPARE_LEVELS,
  // A paper with one account calls it the authors' paper; with its own levels, their names stand.
  levelWords: {
    lean: { name: "Lean", prose: "the Lean" },
    ...(PAPER.levels?.length ? {} : { [MAIN.slot]: { name: "Authors’ paper", prose: "the authors’ paper" } }),
  },
  comparisonsHeld: PAPER.comparisons_hidden ? PAPER.comparisons_held_text : undefined,
  sectionAids: PAPER.section_aids ? { [MAIN.slot]: PAPER.section_aids } : undefined,
  readingAids: PAPER.reading_aids,
  library: {
    paper: PAPER.id,
    main: MAIN.slot,
    pages: Object.fromEntries(PAPER.documents.filter((d) => !d.main && d.slug).map((d) => [d.slug, d.slot])),
    companions: PAPER.documents
      .filter((d) => d.kind === "companion")
      .map((d) => ({ slot: d.slot, id: d.id, title: d.title, group: d.group ?? "", group_title: d.group_title ?? "", order: d.order ?? 0 }))
      .sort((a, b) => a.order - b.order),
    guide: PAPER.documents.find((d) => !d.main && d.noun === "guide")?.slot,
  },
  adapted: ADAPTED
    ? {
        slot: ADAPTED.slot,
        of: (PAPER.documents.find((d) => d.id === ADAPTED.of) ?? MAIN).slot,
        credit: ADAPTED.credit ?? "",
        authorsPaper: PAPER.source.upstream.paper,
        pdfs: [ADAPTED.pdf, ADAPTED.aux_pdf].filter((p): p is NonNullable<typeof p> => !!p).map((p) => ({ label: p.label ?? "PDF", name: p.name ?? p.file })),
      }
    : undefined,
  recordKind,
  leanDerivedSupports: new Set(PAPER.lean_derived_supports ?? []),
  levelGoals: R.level_goals ?? null,
  mainGoal: PAPER.goal,
  leanLevelWho: R.lean_level_who ?? `Statements and proofs by ${BY}`,
  levelsLeanSnippet: R.levels_lean_snippet ?? null,
  words: {
    argumentFor: "Argument for",
    stepTerms: "A step is one record of the argument: a result as the authors number it, or a Lean declaration linked to it.",
    mapKeyIntro: "Each box is a numbered result of the paper or a Lean declaration linked to it. Select one to read it in the paper and in Lean.",
    extractionNote: "No run is recorded for this edition.",
    failureWords: {},
    valueModelNote: "",
    valueModelLink: "",
    checksTerms: "Lean is a programming language whose compiler rejects a proof with a wrong step. This edition reads the authors' Lean source; it records no run of its own.",
    ...R.words,
    leanAbsence: (id: string) => (absence ? (absence.prefixes?.find((rule) => id.startsWith(rule.prefix))?.text ?? absence.default) : "No Lean declaration is linked to this step."),
  },
  copySlots: null,
} satisfies SiteInstance;

export default site;
