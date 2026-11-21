// The Erdős problem #257 example. Its wording is the author's, in copy.ts; everything else
// here is paths, structure and sentences about how the site works. Three identifiers of the
// #257 data are typed here, for the main theorem: its record (short.res-reciprocal-support,
// Theorem A.1), its pattern in the short paper and its Lean declaration. No count is typed:
// every number comes from the edition or the PDFs. No browser API and no import.meta:
// vite.config.ts reads it.

import type { SiteFacts } from "../../home/siteFacts.ts";
import type { RecordKind, SiteInstance } from "../types.ts";
import { COPY, isTodo } from "./copy.ts";
import { heroHtml } from "./hero.ts";
import { siteFilms } from "../../app/siteFilms.ts";
import { kindsInWords } from "../../home/recordKinds.ts";

const EXAMPLE = "examples/erdos257";
const PAPERS = "papers/erdos257";

/** What no one has checked about the ties, said once wherever their counts are given. */
const TIE_REVIEW = "No independent mathematician has reviewed the ties, and no program tests whether the two sides say the same thing.";
const LINK_CAVEAT = `Each tie says who made it: copied from the papers’ published evidence mapping, or made by an AI agent for this site. ${TIE_REVIEW}`;

/** The family registry's films this site shows, lead first. */
const FILMS = [
  { id: "short-mathematics", kicker: "Erdős’s 1968 case in brief" },
  { id: "mathematics", kicker: "Erdős’s 1968 case, proved from fractions" },
  { id: "short-funnel", kicker: "How the three papers are made" },
];

const n = (value: number) => value.toLocaleString("en-GB");
const plain = (text: string) => text.replace(/\$([^$]+)\$/g, "$1");

function readme(siteUrl: string, facts: SiteFacts): string {
  const at = (path: string) => (siteUrl ? `${siteUrl}${path}` : path);
  return `# ${COPY.siteName} website

${plain(COPY.strapline)}

${plain(COPY.opening)}

**[Website](${at("")})** · [Source and tools](https://github.com/wcook04/lean-exposition) · [Will Cook's projects](https://wcook04.github.io/)

## Read and explore

| Start with | What you can inspect |
| --- | --- |
| [${COPY.levels.expository.short}](${at("read/expository/")}) | ${plain(COPY.levels.expository.job)} |
| [${COPY.levels.short.short}](${at("read/short/")}) | ${plain(COPY.levels.short.job)} |
| [${COPY.levels.long.short}](${at("read/long/")}) | ${plain(COPY.levels.long.job)} |
| [Argument map](${at("map/")}) · [Compare](${at("compare/")}) | The recorded steps of the argument and their statements in each paper |
| [Lean index](${at("lean/")}) · [What ran](${at("checks/")}) | The Lean code and every recorded run, passed or not |
${facts.ties ? `\nThe papers have ${n(facts.ties.statements)} marked statements, ${n(facts.ties.withLean)} of them with Lean.\n` : ""}
The three papers are also available in [PDF](pdf/).

## Source and generated files

This repository contains the built website, not the tools that produce it.
Make changes in [lean-exposition](https://github.com/wcook04/lean-exposition).

| Generated path | Contents |
| --- | --- |
| [read/](read/) | The three paper readers |
| [edition/](edition/) | Copies of the papers, proof-step data and check results used by the site |
| [pdf/](pdf/) | The three papers as PDFs |
| [verification/](verification/) | The run receipts the What ran page lists |
`;
}

function llms(siteUrl: string, facts: SiteFacts): string {
  const at = (path: string) => (siteUrl ? `${siteUrl}${path}` : path);
  return `# ${plain(COPY.title)}

> ${plain(COPY.llms)}

${facts.kinds && facts.steps ? `The site holds ${n(facts.steps)} records joined by what uses what: ${kindsInWords(facts.kinds)}. Each paper states a narrower part of them.` : "Each paper states a narrower part of one graph of records."}
${facts.ties && facts.origins ? `The papers have ${n(facts.ties.statements)} marked statements joined to the records by ${n(facts.ties.total)} ties: ${n(facts.origins.evidenceRecord)} copied from the papers' published evidence mapping and ${n(facts.origins.ai)} made by an AI agent for this site. ${TIE_REVIEW}` : LINK_CAVEAT}

## Read

- [${COPY.levels.expository.short}](${at("pdf/exposition.pdf")})
- [${COPY.levels.short.short}](${at("pdf/short-paper.pdf")})
- [${COPY.levels.long.short}](${at("pdf/long-record.pdf")})

## Data

All data is static JSON under ${at("edition/")}. Start at edition/index.json: it maps API routes to files.

- The route "/alignment": for each record, its Lean declarations with relation, comparison (\`fidelity\`) and exact \`lines\`, and exact statement slices in each paper with who linked them (\`origin\`)
- The routes "/ties/short", "/ties/long" and "/ties/expository": each paper's marked statements and their ties${facts.ties ? ` (${n(facts.ties.statements)} marked statements, ${n(facts.ties.withLean)} with Lean, in ${n(facts.ties.total)} ties)` : ""}
- The routes "/lean/modules", "/lean/names" and "/lean/module": the Lean index${facts.lean ? ` (${n(facts.lean.modules)} modules, ${n(facts.lean.declarations)} declarations)` : ""}
- verification/: the receipts of the runs listed on the What ran page

## Source

- [Repository](https://github.com/wcook04/lean-exposition): papers, records, tools and this website
`;
}

const levels = COPY.levels;

/**
 * The graph's records in the papers' terms. The step records an AI agent wrote out from the
 * papers have ids beginning step., exp.step. or context. (examples/erdos257/authored/argument.json);
 * cited literature has status external and open questions status open; every other claim is a
 * result printed in a paper.
 */
function recordKind(node: { id: string; kind: string; status: string }): RecordKind {
  if (node.kind === "declaration") return "declaration";
  if (node.status === "open") return "open";
  if (node.status === "external") return "cited";
  if (/^(step|exp\.step|context)\./.test(node.id)) return "step";
  return "result";
}

const site = {
  id: "erdos257",
  siteName: COPY.siteName,
  familyId: null,
  example: EXAMPLE,
  papers: PAPERS,
  editionTitle: COPY.title,
  html: {
    description: plain(isTodo(COPY.opening) ? COPY.strapline : COPY.opening),
    ogTitle: plain(COPY.title),
    ogDescription: plain(COPY.strapline),
    noscript: `The papers are also available as Markdown and PDF in the repository under <code>${PAPERS}/</code>.`,
    // public/og.png is the SK site's card; this site has none yet.
    ogImage: false,
  },
  defaultSiteUrl: null,
  pdfs: {
    long: { file: `${PAPERS}/long/reasoning-record.pdf`, name: "long-record.pdf", alias: "long/reasoning-record.pdf" },
    short: { file: `${PAPERS}/short/paper.pdf`, name: "short-paper.pdf", alias: "short/paper.pdf" },
    expository: { file: `${PAPERS}/expository/main.pdf`, name: "exposition.pdf", alias: "expository/main.pdf" },
  },
  publicObservations: [],
  publishReceipts: true,
  sitePages: ["", "read/short", "read/expository", "read/long", "map", "compare", "checks", "about", "lean", "lean?list=papers"],
  routeTitles: {
    map: "Argument map",
    compare: "Compare side by side",
    lean: "Lean index",
    checks: "What ran",
    about: "About",
    search: "Search",
    "read/long": plain(levels.long.short),
    "read/short": plain(levels.short.short),
    "read/expository": plain(levels.expository.short),
  },
  readme,
  llms,
  films: FILMS,
  hero: (base: string, facts: SiteFacts, tex: (source: string) => string) => heroHtml(base, facts, tex, LINK_CAVEAT, TIE_REVIEW, siteFilms(base, FILMS)),
  linkCaveat: LINK_CAVEAT,
  modelsStep: null,
  // Theorem A.1 of the short paper, the case Erdős stated in 1968: the clause table's theorem.
  theorem: { record: "short.res-reciprocal-support", paper: "short", pattern: "^\\*\\*Theorem A\\.1\\b" },
  heroStep: "exp.thm-main",
  observation: null,
  tieAudit: null,
  lean: {
    mainTheorem: "Erdos249257.irrational_erdosSupportSeries_of_summable_reciprocal",
    valueTheorem: null,
    minimizer: null,
    challengeFile: null,
    valueChallengeFile: null,
    mainTree: null,
    valueModel: null,
    folderWords: {},
    folderPrefix: "",
    moduleRoot: null,
    roots: ["ErdosProblems", "Erdos249257"],
    owner: "the",
    ownerSource: "the Lean source on this site",
  },
  regionTitles: {},
  paperNames: { long: levels.long, short: levels.short, expository: levels.expository },
  recordKind,
  levelGoals: { expository: "exp.thm-main" },
  mainGoal: "short.res-reciprocal-support",
  leanLevelWho: levels.lean.who,
  // The main theorem's statement as the Lean source writes it (Erdos249257/AllBaseReciprocalSupportIrrationality.lean, lines 395 to 398).
  levelsLeanSnippet: "theorem irrational_erdosSupportSeries_of_summable_reciprocal (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable (reciprocalSupportTerm A)) : Irrational (erdosSupportSeries b A)",
  words: {
    argumentFor: "Argument for",
    stepTerms:
      "A step is one record of the argument: a result printed in a paper, a proof step an AI agent wrote out from the papers, a cited result, an open question or a Lean declaration. The Lean column is the Lean linked to that step, with what it says against each paper where that has been compared.",
    leanAbsence: () => "No Lean declaration is linked to this step. The steps it uses and is used by may have their own.",
    mapKeyIntro: "Each box is one step of the recorded argument: a claim, an assumption or a declaration in Lean. Select one to read it in Lean and in each paper.",
    extractionNote: "No successful run is among these records.",
    failureWords: {},
    valueModelNote: "",
    valueModelLink: "",
    checksTerms:
      "Lean is a programming language whose compiler rejects a proof with a wrong step. Comparator is a program that checks a Lean proof against a separately written statement, using only permitted axioms. A GitHub Actions run is a recorded job on GitHub’s machines, with its commit, date and outcome. A step, or record, is one result printed in a paper, proof step written out from the papers, cited result, open question or Lean declaration in the argument, a tie joins a statement in a paper to a step, and a run record says what ran or was planned and with what outcome.",
  },
  copySlots: COPY,
} satisfies SiteInstance;

export default site;
