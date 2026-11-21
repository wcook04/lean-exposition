// The library instance: one paper of the reading library, read entirely from its data
// (data.ts, from instances/<paper>/instance.json). Every sentence about the paper is the
// data's; the sentences here are about how the reader works. No browser API, no import.meta.

import type { SiteFacts } from "../../home/siteFacts.ts";
import type { RecordKind, SiteInstance } from "../types.ts";
import { PAPER, MAIN, LIBRARY_ROOT } from "./data.ts";

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
for (const doc of PAPER.documents) paperNames[doc.slot] = { short: doc.title, job: sentence(`${doc.title}, by ${BY}`), reader: "" };

function readme(siteUrl: string, facts: SiteFacts): string {
  const at = (path: string) => (siteUrl ? `${siteUrl}${path}` : path);
  return `# ${plain(PAPER.title)}

By ${BY}. ${PAPER.credit_lines.join(" ")}

**[Read it](${at("")})** · [The library](${LIBRARY_ROOT}) · [Source and tools](https://github.com/wcook04/lean-exposition)

${PAPER.review}
${facts.lean ? `\nThe Lean shown here has ${n(facts.lean.modules)} modules and ${n(facts.lean.declarations)} declarations.\n` : ""}`;
}

function llms(siteUrl: string, facts: SiteFacts): string {
  const at = (path: string) => (siteUrl ? `${siteUrl}${path}` : path);
  return `# ${plain(PAPER.title)}

> ${plain(PAPER.title)}, by ${BY}, read beside its Lean. ${PAPER.credit_lines.join(" ")}

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
  defaultSiteUrl: `${LIBRARY_ROOT}${PAPER.id}/`,
  pdfs: Object.fromEntries(PAPER.documents.filter((d) => d.pdf).map((d) => [d.slot, { file: `instances/${PAPER.id}/papers/${d.slot}/${d.pdf!.file}`, name: d.slug ? `${d.slug}.pdf` : "paper.pdf" }])),
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
    mainTheorem: null, valueTheorem: null, minimizer: null, challengeFile: null, valueChallengeFile: null,
    mainTree: null, valueModel: null, folderWords: {}, folderPrefix: "", moduleRoot: null, roots: null,
    owner: `${BY}’s`, ownerSource: `${BY}’s source`,
  },
  regionTitles: {},
  paperNames,
  stages: PAPER.documents.map((d) => d.slot),
  paperStatus: PAPER.review ? sentence(PAPER.review) : undefined,
  library: { paper: PAPER.id, main: MAIN.slot, pages: Object.fromEntries(PAPER.documents.filter((d) => !d.main && d.slug).map((d) => [d.slug, d.slot])) },
  recordKind,
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
