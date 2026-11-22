// The library instance: one paper of the reading library, read entirely from its data
// (data.ts, from instances/<paper>/instance.json). Every sentence about the paper is the
// data's; the sentences here are about how the reader works. No browser API, no import.meta.

import type { SiteFacts } from "../../home/siteFacts.ts";
import type { RecordKind, SiteInstance } from "../types.ts";
import { PAPER, MAIN, BUILT, LIBRARY_ROOT } from "./data.ts";

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
// The paper itself is the authors': its header carries their full credit line, once. A companion page
// (an account or a guide) is about it, written for this reader with AI, and names the authors and their
// repository only (companion_credit).
for (const doc of BUILT)
  paperNames[doc.slot] = doc.main
    ? { short: doc.title, job: sentence(`${doc.title}, by ${BY}`), reader: CREDIT }
    : {
        short: doc.title,
        job: sentence(`${doc.title}: ${/^[aeiou]/i.test(doc.noun) ? "an" : "a"} ${doc.noun} to ${PAPER.title}, written for this reader with AI`),
        reader: PAPER.companion_credit ? sentence(PAPER.companion_credit) : "",
      };

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
  defaultSiteUrl: `${LIBRARY_ROOT}${PAPER.path ?? PAPER.id}/`,
  pdfs: Object.fromEntries(BUILT.filter((d) => d.pdf).map((d) => [d.slot, { file: `instances/${PAPER.id}/papers/${d.slot}/${d.pdf!.file}`, name: d.slug ? `${d.slug}.pdf` : "paper.pdf" }])),
  publicObservations: [],
  publishReceipts: false,
  sitePages: [""],
  routeTitles: {
    map: "Argument map", compare: "Compare", lean: "Lean index", checks: "What ran", about: "About", search: "Search",
    [`read/${MAIN.slot}`]: plain(MAIN.title),
  },
  readme,
  llms,
  films: [],
  hero: () => "",
  linkCaveat: LINK_CAVEAT,
  modelsStep: null,
  theorem: { record: PAPER.goal, paper: MAIN.slot, pattern: null },
  heroStep: null,
  observation: null,
  tieAudit: null,
  lean: {
    mainTheorem: PAPER.main_lean ?? null, valueTheorem: null, minimizer: null, challengeFile: null, valueChallengeFile: null,
    mainTree: null, valueModel: null, folderWords: {}, folderPrefix: "", moduleRoot: null, roots: null,
    owner: `${BY}’s`, ownerSource: `${BY}’s source`,
  },
  regionTitles: {},
  paperNames,
  stages: BUILT.map((d) => d.slot),
  paperStatus: PAPER.review ? sentence(PAPER.review) : undefined,
  comparisonsHeld: PAPER.comparisons_hidden ? PAPER.comparisons_held_text : undefined,
  library: {
    paper: PAPER.id,
    main: MAIN.slot,
    pdfOnly: BUILT.filter((d) => d.pdf_only).map((d) => d.slot),
    pages: Object.fromEntries(BUILT.filter((d) => !d.main && d.slug).map((d) => [d.slug, d.slot])),
    external: PAPER.documents
      .filter((d) => d.href && !d.slot)
      .map((d) => ({ title: d.title, job: sentence(`${d.title}: the ${d.noun}`), href: `${LIBRARY_ROOT}${d.href}` })),
  },
  recordKind,
  leanDerivedSupports: new Set(PAPER.lean_derived_supports ?? []),
  levelGoals: null,
  mainGoal: PAPER.goal,
  leanLevelWho: `Statements and proofs by ${BY}`,
  levelsLeanSnippet: null,
  words: {
    argumentFor: "Argument for",
    stepTerms: "A step is one record of the argument: a result as the authors number it, or a Lean declaration linked to it.",
    leanAbsence: () => "No Lean declaration is linked to this step.",
    mapKeyIntro: "Each box is a numbered result of the paper or a Lean declaration linked to it. Select one to read it in the paper and in Lean.",
    extractionNote: "No run is recorded for this edition.",
    failureWords: {},
    valueModelNote: "",
    valueModelLink: "",
    checksTerms: "Lean is a programming language whose compiler rejects a proof with a wrong step. This edition reads the authors' Lean source; it records no run of its own.",
  },
  copySlots: null,
} satisfies SiteInstance;

export default site;
