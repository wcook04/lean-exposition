// The Sherrington–Kirkpatrick example, as the site has always been built: the instance the
// build selects when LX_INSTANCE is unset. Every value reproduces what the site showed
// before instances existed. No browser API and no import.meta: vite.config.ts reads it.

import type { SiteFacts } from "../../home/siteFacts.ts";
import type { SiteInstance } from "../types.ts";
import { EDITION_TITLE, FILMS, LINK_CAVEAT, MODELS_STEP, SITE_NAME, SITE_URL } from "./constants.ts";
import { heroHtml, heroLinks } from "./hero.ts";

// The public repository that receives the static build has no other README.
const readme = () => `# ${SITE_NAME} website

Read a mathematical paper with the exact Lean statement beside the paragraph
that describes it. Lean is a language for writing statements and proofs that a
computer can check. The papers and their links to the Lean are drafts awaiting
mathematical review.

**[Open Theorem 1 with its Lean](https://wcook04.github.io/lean-exposition-site/read/short/?l=b5970-6319&n=full_support#main-result)** · [Website](https://wcook04.github.io/lean-exposition-site/) · [Source and tools](https://github.com/wcook04/lean-exposition) · [Will Cook's projects](https://wcook04.github.io/)

[![The short paper with Theorem 1 highlighted beside its Lean statement.](stills/reader-theorem-1-light-1440.webp)](https://wcook04.github.io/lean-exposition-site/read/short/?l=b5970-6319&n=full_support#main-result)

The website contains three explanations of a theorem about interacting spins
in the Sherrington–Kirkpatrick model. Start with the exposition for a two-spin
example, or the short paper for the specialist statement and proof.
The mathematics comes from
[OpenAI's mathematics release, example 281](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/docs/281.md).
These are drafts explaining existing results; mathematical and reader review
remain open. The [source repository](https://github.com/wcook04/lean-exposition#the-worked-example)
gives the exact scope of the Lean and the recorded checks.

## Read and explore

| Start with | What you can inspect |
| --- | --- |
| [Exposition](https://wcook04.github.io/lean-exposition-site/read/expository/) | An explanation beginning with a calculation for two spins |
| [Short paper](https://wcook04.github.io/lean-exposition-site/read/short/) | The precise mathematical statement and its proof |
| [Long reasoning record](https://wcook04.github.io/lean-exposition-site/read/long/) | Detailed calculations, source references and remaining steps for OpenAI's separate claim about the limiting energies of quantum circuits |
| [Argument map](https://wcook04.github.io/lean-exposition-site/map/) · [Compare](https://wcook04.github.io/lean-exposition-site/compare/) | The recorded proof steps and their passages in each paper |
| [Lean index](https://wcook04.github.io/lean-exposition-site/lean/) · [What ran](https://wcook04.github.io/lean-exposition-site/checks/) | The named statements in the Lean code and recorded check results |
| [About](https://wcook04.github.io/lean-exposition-site/about/) | A paper explaining how the website connects the papers to the proof steps |

Each phrase that a Lean declaration states is underlined in the colour of its topic and opens that Lean beside the paper, with a plain title, a comparison with the phrase and an AI-drafted reading note.
The three explanations and the paper under About are also available in [PDF](pdf/).
[Plectis Atlas](https://wcook04.github.io/plectis-atlas/families/281.html)
lists the same OpenAI manuscripts and Lean files.

## Videos

[How different can two nearly best answers be?](https://www.youtube.com/watch?v=IUAhxUriDVw)
starts with four magnets and explains the mathematical question.
[Read a maths paper beside its argument map](https://www.youtube.com/watch?v=sYMDcT7vyng)
walks through this website.

## Source and generated files

This repository contains the built website, not the tools that produce it.
Make changes in [lean-exposition](https://github.com/wcook04/lean-exposition).
Its [main-branch build workflow](https://github.com/wcook04/lean-exposition/blob/main/.github/workflows/pages.yml)
replaces this repository's files with the built website. Installation,
local development and contribution instructions live in that source repository.

| Generated path | Contents |
| --- | --- |
| [read/](read/) | The three paper readers |
| [edition/](edition/) | Copies of the papers, proof-step data and check results used by the site |
| [pdf/](pdf/) | The three explanations and the paper about the website, as PDFs |
| [assets/](assets/) · [stills/](stills/) | Built application files and website screenshots |

Will Cook directs this project. His other projects and videos are linked below.
[Projects](https://wcook04.github.io/) · [Videos](https://www.youtube.com/@willcook2004)
`;

// For readers that fetch text rather than run the page. It describes the same files the
// browser reads, and no page loads it.
const llms = (SITE_URL: string, facts: SiteFacts) => `# Why the Sherrington–Kirkpatrick order parameter has no gaps

> One theorem from OpenAI's mathematics release, family 281: every minimiser of the zero-temperature Parisi functional for the pure zero-field Sherrington-Kirkpatrick model has full support on [0,1). The site holds OpenAI's Lean beside three written accounts, and one graph of ${facts.steps ?? "many"} steps joins them. The data calls a step a record.

Each paper is a narrower part of the same graph. Papers and records are drafts; no independent mathematical review has been done. Ties between the papers and the Lean are pointers written by AI agents after reading both sides. No independent mathematician has reviewed them, and a program confirms only that both ends of each one still exist.
${facts.build && facts.extraction ? `
Lean ${facts.build.toolchain.split(":").pop()} compiled ${facts.build.module} (\`${facts.build.command}\`, exit ${facts.build.returncode}) at OpenAI revision ${facts.build.revision.slice(0, 7)}, recorded ${facts.build.date}. Lean's extraction lists these axioms for ${facts.extraction.root}: ${facts.extraction.axioms.join(", ")}. The theorem assumes a minimiser. Comparator, a program that compares a Lean proof with a separately written statement, has accepted neither main statement, and the scalar value result has no successful build on record.
` : ""}
## Read

- [Exposition](${SITE_URL}pdf/exposition.pdf): objects and ideas, from a calculation with two spins
- [Short paper](${SITE_URL}pdf/short-paper.pdf): the result and proof for specialists
- [Long record](${SITE_URL}pdf/long-record.pdf): each step with its source, continuing to the QAOA circuits
- [Architectural companion](${SITE_URL}pdf/architecture.pdf): why the papers share one graph

## Data

All data is static JSON under ${SITE_URL}edition/. Start at edition/index.json: it maps API routes to files, and \`route_maps\` holds further maps for per-module and per-record routes.

- The route "/alignment": for each record, its short title, Lean declarations with relation and exact \`lines\`, and exact statement slices in each paper, each slice with the Lean it means; a dictionary from Lean names to the papers' notation; \`names\`, plain titles for ${facts.plainTitles ?? "many"} declarations
- The routes "/ties/short", "/ties/long" and "/ties/expository": non-overlapping byte ranges of each paper, each with its ties to records and Lean lines${facts.ties ? ` (${facts.ties.statements.toLocaleString("en-GB")} marked statements, ${facts.ties.withLean} with Lean, in ${facts.ties.total.toLocaleString("en-GB")} ties)` : ""}. A tie is a pointer. No program tests whether the two texts mean the same thing.
- The reference tables behind the papers' links to theorems, equations, sections, figures and citations${facts.references ? ` (${facts.references} links)` : ""}, in examples/qaoa-sk/alignment/references-*.json in the repository
- The routes "/lean/modules", "/lean/names" and "/lean/module": the Lean index${facts.lean ? ` (${facts.lean.modules} modules, ${facts.lean.declarations.toLocaleString("en-GB")} declarations at ${facts.lean.toolchain.split(":").pop()})` : ""}, one file per module with source, declarations and name references. ${facts.lean?.dependencySource === "elaborated" ? "Dependencies come from Lean's compiled declarations." : "Dependencies come from the source text and are not elaborated."}
- The route "/graph" in edition/index.json: the whole recorded graph, with typed edges running from consumer to prerequisite

## Source

- [Repository](https://github.com/wcook04/lean-exposition): papers, records, tools and this website
- [Web API](https://github.com/wcook04/lean-exposition/blob/main/docs/web-api.md): routes and field meanings
`;

// How the site names the three accounts and what each is for. The sentences follow the
// documents' own introductions and the repository's reading guide.
const paperNames: SiteInstance["paperNames"] = {
  expository: {
    short: "Exposition",
    job: "The objects and the idea of the proof, starting from a calculation with two spins.",
    reader: "Written for readers who know algebra and calculus; probability and measures are introduced through calculations.",
  },
  short: {
    short: "Short paper",
    job: "The result, how its proof compares with the earlier crossing proof, and the proof, with the polynomial identity behind the curvature estimate printed in full.",
    reader: "Written for readers who know the Parisi variational theory and Itô calculus.",
  },
  long: {
    short: "Long record",
    job: "The derivations, with the source of each step and of each imported estimate, continuing to the circuits of the quantum approximate optimization algorithm (QAOA).",
    reader: "Written so that a reader can start at any step they want to examine.",
  },
};

// One plain sentence on each folder of OpenAI's Lean source, written from reading the
// module names and the theorems inside each folder at the pinned revision.
const folderWords: Record<string, string> = {
  ComparatorChallenges: "The definitions and the two main statements copied out alone, with sorry in place of each proof, as challenge files for a Comparator run.",
  "OAI/Probability/SKSupport": "The definitions of the model and the final full support theorem.",
  "OAI/Probability/SKSupport/Backward": "Solutions of the backward equation: their shape, comparison, gradient bounds and what happens on a terminal plateau.",
  "OAI/Probability/SKSupport/Control": "The control problem behind the value function: payoffs, grid approximations, and the value's Lipschitz and convexity properties.",
  "OAI/Probability/SKSupport/Density": "Densities on finite grids, Gaussian tails and the ratio comparisons that give coercivity.",
  "OAI/Probability/SKSupport/Diffusion": "The diffusion driven by the gradient: its construction by Picard iteration, feedback verification and uniqueness.",
  "OAI/Probability/SKSupport/Foundations": "Groundwork used throughout: the cascade, semigroups, variance heat curves, step data and finite values.",
  "OAI/Probability/SKSupport/Moments": "The square moment and curvature moment along the diffusion, and the equations they satisfy.",
  "OAI/Probability/SKSupport/Parabolic": "Comparison principles for parabolic inequalities, and Burgers, forward and tilted evolutions.",
  "OAI/Probability/SKSupport/Regularity": "Smoothness of the value function: its derivatives, their bounds and their limits.",
  "OAI/Probability/SKSupport/Support": "The final argument: contact, the variational inequality and the exclusion of gaps.",
  "OAI/Probability/SKValue": "The definitions and the main statement of the ground-state value result.",
  "OAI/Probability/SKValue/Coercivity": "Coercivity estimates, pointwise and integrated, including the zero-gap case.",
  "OAI/Probability/SKValue/Control": "Controls and verification for the value: progressive controls, stability and regularity on strips.",
  "OAI/Probability/SKValue/Equations": "Estimates for the equations: comparison principles, polynomial moments, forced generators and strip bounds.",
  "OAI/Probability/SKValue/Evolution": "The Parisi evolution: Cole-Hopf, heat kernel bounds, grid convergence and assembly of the Parisi value.",
  "OAI/Probability/SKValue/Gaussian": "Gaussian building blocks: Brownian coordinates, density derivatives and split profile estimates.",
  "OAI/Probability/SKValue/GroundState": "The passage to the ground state: Guerra bounds, tree and cascade laws, Gumbel maxima and rounding to spins.",
  "OAI/Probability/SKValue/Processes": "Diffusion processes for the value: existence, Euler meshes, martingale facts and gradient isometries.",
  "OAI/Probability/SKValue/Variation": "First variations, contact at a minimiser and the ground-state value derived from contact.",
};

const site = {
  id: "qaoa-sk",
  siteName: SITE_NAME,
  familyId: "lean-exposition",
  example: "examples/qaoa-sk",
  papers: "papers/qaoa-sk",
  editionTitle: EDITION_TITLE,
  html: {
    description:
      "Why a minimising Parisi order parameter of the zero-temperature Sherrington–Kirkpatrick spin glass has no gaps. Read three papers on the proof: an underlined phrase opens the OpenAI Lean that states it beside the text, and a graph of the proof moves to the statement you are reading.",
    ogTitle: EDITION_TITLE,
    ogDescription:
      "Read a paper on this theorem as you would any paper: an underlined phrase opens the OpenAI Lean that states it beside the text, and a graph of the proof moves to the statement you are reading.",
    // The line break and indent keep the built index.html byte for byte as it was.
    noscript: "The\n        papers are also available as Markdown and PDF in the repository under <code>papers/qaoa-sk/</code>.",
    ogImage: true,
  },
  defaultSiteUrl: SITE_URL,
  // The three accounts and architectural companion, as the repository renders them.
  pdfs: {
    long: { file: "papers/qaoa-sk/long/reasoning-record.pdf", name: "long-record.pdf", alias: "long/reasoning-record.pdf" },
    short: { file: "papers/qaoa-sk/short/paper.pdf", name: "short-paper.pdf", alias: "short/paper.pdf" },
    expository: { file: "papers/qaoa-sk/expository/main.pdf", name: "exposition.pdf", alias: "expository/main.pdf" },
    architecture: { file: "papers/architecture/paper.pdf", name: "architecture.pdf" },
  },
  // One intentionally published observation. Keep this an explicit file list; verification
  // directories also contain artifacts that the website does not use.
  publicObservations: [{
    file: "examples/qaoa-sk/verification/full-support-build-extraction-observation-20261026.json",
    name: "full-support-build-extraction-observation-20261026.json",
  }],
  publishReceipts: false,
  sitePages: ["", "read/short", "read/expository", "read/long", "map", "compare", "checks", "about", "lean", "lean?list=papers"],
  routeTitles: {
    map: "Argument map",
    compare: "Compare side by side",
    lean: "Lean index",
    checks: "What ran",
    about: "About",
    search: "Search",
    "read/long": "Long record",
    "read/short": "Short paper",
    "read/expository": "Exposition",
  },
  readme,
  llms,
  films: FILMS,
  hero: (base: string, facts: SiteFacts, tex: (source: string) => string) => heroHtml(heroLinks(base, facts.theorem1, facts.ties), tex),
  linkCaveat: LINK_CAVEAT,
  modelsStep: MODELS_STEP,
  theorem: { record: "full_support", paper: "short", pattern: "^\\*\\*Theorem 1\\b" },
  heroStep: "support.diffusion",
  observation: "verification/full-support-build-extraction-observation-20261026.json",
  tieAudit: "verification/tie-audit.json",
  lean: {
    mainTheorem: "OAI.ZeroTemperatureSK.full_support",
    valueTheorem: "OAI.SKValue.value_consequences",
    minimizer: "OAI.ZeroTemperatureSK.IsMinimizer",
    challengeFile: "ComparatorChallenges.SKFullSupport",
    valueChallengeFile: "ComparatorChallenges.SKValue",
    mainTree: ".SKSupport",
    valueModel: "OAI.Probability.SKValue",
    folderWords,
    folderPrefix: "OAI/Probability/",
    moduleRoot: "OAI",
    roots: ["OAI", "ComparatorChallenges"],
    owner: "OpenAI’s",
    ownerSource: "OpenAI's source",
  },
  regionTitles: {
    full_support: "Full support",
    scalar_value: "Value identities",
    qaoa_thermodynamic_first: "QAOA circuits",
  },
  paperNames,
  recordKind: null,
  levelGoals: null,
  mainGoal: "full_support",
  leanLevelWho: "OpenAI’s statements and proofs, written for the Lean compiler.",
  levelsLeanSnippet: "theorem full_support (W) (γ) (hmin) : FullSupportConclusion W γ := by have hμ := parameterMeasure_isStieltjes γ",
  words: {
    argumentFor: "In the Sherrington–Kirkpatrick (SK) model, argument for",
    stepTerms:
      "A step is one claim, assumption or result in the proof that minimisers of the Sherrington–Kirkpatrick (SK) model have full support. The Lean column is OpenAI’s proof in Lean, a programming language for proofs. That Lean has two separate models, the support model for full support and the value model for the value theorem.",
    leanAbsence(id: string): string {
      if (id.startsWith("circuit.") || id.startsWith("qaoa_")) return "OpenAI's Lean covers full support and the scalar value, and has no declaration for this result.";
      return "No Lean declaration is linked to this step. OpenAI's Lean covers full support and the scalar value; the steps it uses and is used by may have their own.";
    },
    mapKeyIntro:
      "This is the argument for a theorem about the Sherrington–Kirkpatrick (SK) spin glass. Each box is one step: a claim, an assumption or a declaration in Lean, the language of OpenAI’s proof. Select one to read it in Lean and in each paper.",
    extractionNote: "No successful run is among these records. The extraction that finished, on 26 October 2026, is in the first table.",
    failureWords: {
      full_support_solution_build_failure_20261023:
        "Comparator stopped while building the proof of the Full support theorem, because a compiled file the proof imports (AbsIncrement) was missing.",
      scalar_value_solution_build_failure_20261024:
        "Comparator stopped while building the proof of the scalar value theorem, because a compiled file the proof imports (IntegralPositiveMulGaussian) was missing.",
    },
    valueModelNote: "This is OpenAI’s value model.",
    valueModelLink: "No Lean theorem connects it to the full-support model.",
    checksTerms:
      "OpenAI’s proof is written in Lean, a programming language whose compiler rejects a proof with a wrong step. Comparator is a program that compares a Lean proof with a separately written statement. An extraction is a program run inside Lean that lists what a compiled theorem uses and which axioms it depends on. The main theorem here is the full-support theorem for the Sherrington–Kirkpatrick (SK) spin glass. A step is one claim, assumption or Lean declaration in its argument, a tie joins a statement in a paper to a step, and a run record says what ran or was planned and with what outcome.",
  },
  copySlots: null,
} satisfies SiteInstance;

export default site;
