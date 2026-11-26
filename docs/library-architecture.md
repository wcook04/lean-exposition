# The library: one reader engine, every paper as data

Status: plan, 21 November 2026, awaiting confirmation. Nothing below is built or published yet.

Five reader sites are live today. They run on three engines:

- **lean-exposition** runs SK (`lean-exposition-site`) and Erdős #257 (`erdos-257-reader`). It has path routes, phrase ties, the argument map, Compare, What ran and search.
- **Proof Reader** (`proof-reader`, hash routes) has 49 pages and the Physlib map.
- **The quartic reader** (`quartic-query-lean` gh-pages, hash routes) is its own app. It borrows code from both of the others.

The aim is one engine that reads every paper from data. All of it sits under one address, has one index, and keeps every old link working.

## 1. Decisions, and where this plan overrules the brief

1. **Host.** The host is a new public repo, `wcook04/library`, served by GitHub Pages from its `main` branch at `https://wcook04.github.io/library/`.
   - Not the user site `wcook04.github.io`. That repo is the landing site ("edition 3"), and its designer owns it. A library deploy should never touch it.
   - Not one repo per paper. One repo gives one origin, one catalog file, one 404 fallback and atomic deploys of the index together with a paper.
   - The landing site links to `/library/`.
2. **The engine is built once. Papers are built as data (this overrules "builds per instance" as Vite builds).** Today each lean-exposition instance is a separate Vite build with its own components (FrontPage.tsx, copy.ts, and so on). That is per-paper code, and it is why a deploy rebuilds everything.
   - **The new split:**
     - The engine is one bundle at `/library/_engine/<engine-hash>/`.
     - Each paper is a folder of data plus prerendered HTML shells that load the engine.
   - **What a content change costs:** the Python data pipeline for that paper and its shells run, and only that folder is deployed. No Vite build runs.
   - **What an engine change costs:** one Vite build, plus a cheap re-render of every paper's shells. The paper data stays as it is.
   - The 20-minute full rebuild goes away in both cases.
3. **No per-paper home pages.** `/<paper>/` opens the reader at the top of the paper's text. Front matter that a landing page carried moves into the reader's header line and its About panel. That covers credit, the "what this is" line and the shelf of companion pages. The landing pages themselves become redirects: the 257 and SK front pages, the quartic front page and Proof Reader's per-paper fronts.
4. **Proof Reader's Euler and Navier–Stokes pages.** The earlier brief said to leave them up. Item 4 of the new brief says every old address redirects deeply. I follow the new brief: each Proof Reader page becomes a redirect once its library address passes its browser check. Before that, it stays up unchanged. *Please confirm.*
5. **Navier–Stokes before the checked typeset copy.** `/navier-stokes/` opens the digest, and its header says the authors' paper is coming. When the verified copy arrives, it becomes the paper's main document and the digest moves to `/navier-stokes/digest/`. The digest's tie ids do not change, so links made in between still resolve. No page is ever set from the PDF's text layer.
6. **Quartic's pinned editions are kept as snapshots.** The `?ed=` links went out in emails as fixed, checkable versions. Each old edition is published once, from the quartic gh-pages history, as a static read-only snapshot at `/library/quartic/editions/<ed>/`. Each snapshot carries a one-line banner linking to the current reading. An old `?ed=` link redirects to its snapshot. The current source reader at `/library/quartic/source/` uses the last snapshot’s verified data for OpenAI’s paper and the verification supplement. Its application assets are built separately by the Quartic repository. No new frozen editions are made.

## 2. URL scheme

All addresses are under `https://wcook04.github.io/library/`.

| Address | Opens |
|---|---|
| `/` | The library index. It lists every paper with its companion pages beneath it and has one search box across all papers. This is the only home page. |
| `/<paper>/` | The paper's main document, at the top of the text |
| `/<paper>/<page>/` | A companion page, such as `/navier-stokes/part-1/` or `/erdos-257/record/` |
| `…/#<section>` | A section in the paper's own numbering, such as `/euler/#5.6` (also `#5.5.1`, `#appendix-a`) |
| `…/<result>/` | A numbered result in the authors' numbering: `/euler/theorem-1.1/`, `/navier-stokes/proposition-7.5/`, `/erdos-257/theorem-a.1/` |
| `…/@<tie-id>` | One phrase or sentence, by its tie id. It is selected and its card is open. |
| `…/lean/<full.name>` | A Lean declaration. Its card is open and every phrase that states it is highlighted. |
| `…/topic/<topic-id>/` | The paper, filtered to that topic |
| `…/map/`, `…/compare/`, `…/checks/`, `…/source/`, `…/about/` | The per-paper views: argument map, Compare (only when the instance declares levels), What ran, the Lean tree, About |
| `/search/?q=` | Search across the whole library |

**Rules.**

- **Pane state.** Pane mode and secondary state travel in the query string, keeping today's lean-exposition names: `v=lean|graph`, `d`, `dm`, `n`, `l`, `beside`, `page` (PDF page), `t` (topic filter, when combined with another address).
- **Reserved words.** The words `lean`, `topic`, `map`, `compare`, `checks`, `source`, `about` and `search` are reserved. So is any word that matches a result slug (`^(theorem|proposition|lemma|corollary|definition|remark|conjecture|problem|example|assumption|claim|step)-[0-9a-z.]+$`). The catalog build fails if a page slug collides with one of them.
- **Copy-link.** "Copy link" writes exactly the address the reader would parse back. A test round-trips every route kind through `routeHref` and `parseRoute`.
- **How addresses are served.** Static `index.html` shells are prerendered for each paper, page, result, topic and view. Each shell has its own title, description and canonical tag, so link previews work. `/library/404.html` is the single-page-app fallback for tie ids and Lean names.
- **Lean names in paths.** They are percent-encoded. Dots and primes stay as they are.

## 3. Instance format (content as data only)

Every paper is one folder in lean-exposition, `instances/<paper>/`, and holds no code.

```
instances/<paper>/
  instance.json      id, title, short title, authors[], credit (who wrote, who formalised, the source pins),
                     host line, about[] sections, documents[] (id, slug, title, noun, kind: markdown|pdf|api-map,
                     source path, main: true on one), levels (optional: ordered document ids for Compare),
                     families[], topics[] (id, name, description, family), topic_order (the seriated colour order,
                     stored with the topic list), shelf groups (e.g. "Library guide"),
                     credit_lines[] (the source's own credit, intact: authors, repo, commit, thanks such as Anthropic)
  documents/<doc>/   reading.md (KaTeX-ready, \tag{n}, explicit anchors) or paper.pdf + reading.md transcription;
                     figures/*; numbering.json (label → printed number, used for result and section addresses)
  alignment/         phrases-<doc>.json (phrase-ties/1: ties with id, from/to, role, topic, lean[], comparisons
                     [{lean, fidelity, note, source}]), names.json (2–6 word titles), notes.json (text, summary,
                     on: lean|phrase), results.json (result slug → tie id and Lean names)
  lean/              the vendored upstream sources the instance cites, unchanged, plus source-lock.json
  generated/         lean-index.json(.gz) (declarations, lines, dependencies), checks.json (supplementary Lean),
                     comparator/ (receipts), unnamed.json (declarations no sentence names)
  graph.json         optional evidence graph; when absent the engine draws the map from ties and Lean dependencies
```

**Labels and credit.** Every comparison, title and note carries `source: ai | recorded`. The cards print "AI-assessed" (comparisons) or "AI-drafted" (titles, notes). The header and About carry `credit_lines[]` intact, for example Physlib, Euler and Navier–Stokes. About says no mathematician has reviewed the AI-made links.

Paper figures are published under `paper-figures/<slot>/` from the instance's
`papers/<slot>/figures/`. The Proof Reader importer also accepts an image
referenced beside the source manuscript. The Library build checks both forms
of reference. The Contextual Embeddings charts are the vector crops from the
Proof Reader's copy of the authors' PDF.

**Existing instances.** SK and #257 keep their `examples/` and `papers/` folders. Their `instance.json` points at those folders, so nothing moves on the first pass. Their `copy.ts` slots become `instance.json` fields. Their FrontPage, AboutPage, LeanLanding and ChecksIntro components are dropped, because there are no front pages; any sentences they hold become `about[]`.

**`scripts/from_proof_reader.py`.** This converter turns a Proof Reader page (`paper.toml`, `links.json`, paper source, `generated/lean.json(.gz)`, `checks/`) into this format:

- **Lean source.** A pinned GitHub tree in `[lean].source` supplies the repository, revision and `upstream_lean_root` in the source lock. The root is the path after the revision, or an empty string at the repository root. An archived Lean project keeps its record DOI.
- **Passages.** Each passage becomes a tie, and its id is kept.
- **Claims.** Each claim becomes a result slug. For example, `result-1.1` with the title "Theorem 1.1" becomes `theorem-1.1`.
- **Titles and notes.** `plain` becomes `names.json` and `notes` becomes `notes.json`.
- **Unnamed declarations.** `show_also` becomes `unnamed.json`.
- **Companions.** `[shelf]` and `[reading.companions]` become `documents[]` and in-text links.

The same converter later moves PCP, coupled-spring, contextual-embeddings, SMT-LIB and Physlib.

**Checks.** `lean-exposition validate`, `check-alignment` (extended to ties' `comparisons` and `family`) and a new `check-instance` run on each instance. `check-instance` checks that every result slug, section anchor, tie id and Lean name the catalog lists resolves.

## 4. Engine module map

The base is lean-exposition `site/src`, which is about 40k lines today. These are the changes per module.

| Module | Today | Change |
|---|---|---|
| `app/` (router, restore, trail, TopBar, VideosMenu, SisterSites) | One instance; routes `/read/<stage>` | **Router.** Route `/<paper>/<page>/…`. **Library header.** Add a paper switcher that reads `/library/catalog.json`. **Positions.** Remember the reading position per paper and per page; this is quartic's `switchPaper` plus "Return" after a cross-paper link. |
| `api/` (static edition loader, types) | `Stage = long\|short\|expository`; data inlined at build | **Stages.** Replace them with document ids from `instance.json`. **Loading.** Load `/<paper>/data/*.json` at runtime and shard the Lean index by module, so Euler's 8,072 declarations load lazily. |
| `reader/` (ReaderPage, ties, phrases, anchors, references, math) | Markdown reading copy, phrase ties, topics | **Families.** Colours come from families, after the palette change in flight. **Copying.** Copying a formula gives Unicode (Proof Reader `copyMaths.ts` and `plainMaths.ts`). **PDF.** Add a PDF document kind (below). |
| `reader/pdf/` (new) | none | Proof Reader `PdfPane.tsx`: pdf.js pages, zoom anchored at the reading line, link marks from passage rectangles. Statements are placed at the PDF's named destinations, as quartic does with `PdfPaper.tsx`. |
| `panels/` (RecordPanel, DeclPanel, LeanCode) | Phrase card and Lean card | **Phrase card.** Show comparisons with fidelity and the note on the card. **Lean card.** Show reading notes on Lean (`on: lean`), the supplementary-Lean pane (Proof Reader `SupplementaryProofs`) and Comparator results per declaration (quartic `ComparatorEvidence.tsx`). |
| `map/` (ArgumentTree, FocusGraph, engine, canvas) | Argument map and focus graph | **Graph tab.** Keep the split phrase/graph view (quartic `PhraseSplit.tsx`, already partly in PR #85). **Fallback.** When there is no `graph.json`, draw the map from ties and Lean dependencies. |
| `compare/` | The levels funnel | Shown only when `levels` is declared (SK, #257, quartic). |
| `lean/` (LeanPage, CodeView, tree) | Lean tree browser | **Unnamed list.** Add the list of declarations no sentence names. **Large guides.** Large library guides page the index from the gz report. |
| `checks/` (runs ledger, receipts) | What ran | Unchanged. It also reads Proof Reader's comparator folders. |
| `search/` | One instance | **Per paper.** Each paper emits `search.json` (statements, plain titles, Lean names, topics). **Across papers.** `/search/` and the index box fetch the shards lazily. |
| `library/` (new) | none | The index page, `catalog.json` reader and cross-paper links (below). |
| `reader/view/` (new) | none | **PDF or typeset toggle.** It appears on every document that has both the authors' PDF and a typeset reading copy (Euler, Navier–Stokes once its checked copy lands, quartic, SMT-LIB with a transcription). Each tie id maps to PDF rectangles and named destinations, and to its place in the text. A switch keeps the same statement or paragraph in view and keeps the selected phrase and the pane mode. Phrase links are clickable in both views with the same topic colours: underlines in text, marks on the PDF. The address carries `view=pdf\|text` next to `page`, and Copy link includes it. A document with only one form shows no toggle. |
| `reader/view/` Open PDF (new) | Download links only | **Open PDF.** Every document with a PDF gets an "Open PDF" link in the header beside the toggle, and again in About. It opens the authors' original file, byte for byte and credited, at `<paper>/<doc>/paper.pdf` in a new tab (`target="_blank" rel="noopener"`). It has no `download` attribute, so the browser's own viewer zooms, prints and downloads. With a page selected, the link adds `#page=N`. |
| `app/settings` (new) | Theme toggle only | **Settings menu.** One small menu, remembered per viewer in localStorage behind try/catch. It holds light or dark, plain titles or Lean names first on cards, topic colours on or off, and text size. A setting is added only where it changes what a reader can do. |
| `apimap/` (new) | none | Proof Reader `PhyslibMap.tsx` and `DependencyMap.tsx`, as the `api-map` document kind. |
| `instances/` | Per-instance code | **Deleted.** `registry.ts` becomes the `instance.json` loader. |

**Cross-paper links.** The catalog build compares the papers' exports:

- non-Mathlib Lean declaration names with their source repo and commit;
- cited works by DOI or arXiv id.

A phrase card and the About panel then list "also in <paper>". Euler and Navier–Stokes share an author and literature, so they will be the first pair.

## 5. Feature-merge table

| Feature | Source engine | Kept or dropped | Why |
|---|---|---|---|
| Phrase-to-Lean ties, phrase cards, topics | lean-exposition | Kept (base) | The UI Will prefers |
| Topic families and family colours | lean-exposition (palette change in flight), data from Proof Reader | Kept | The new Euler and NS data carries them; the palette lands separately |
| Topic colour tests | quartic (single ΔE ≥ 15 test), replaced | Kept, as a two-level family palette test | One floor between families and one between shades within a family. Both are tested on the light and dark themes and under deuteranopia and protanopia simulation. The colour order is seriated once per shared topic list and stored with the list, so identical lists get identical colours. The palette module is a separate task. |
| Argument map, focus graph, edge panel | lean-exposition | Kept | Already shared with the other two by copying |
| Phrase/graph split with draggable divider; local neighbourhood | quartic | Kept | Better than a tab switch on wide screens |
| Compare (levels funnel) | lean-exposition | Kept, only for instances with levels | Only SK, #257 and quartic have several levels of one argument |
| Cross-paper statement view ("Does Lean prove this?" per account) | quartic | Kept, merged into Compare | Same job as Compare for quartic's four papers |
| What ran (runs ledger, receipts) | lean-exposition | Kept | |
| Comparator results per declaration and per page | Proof Reader, quartic | Kept, one component | Three versions today |
| Supplementary-Lean pane (our checks against their Lean) | Proof Reader | Kept | Euler and coupled-spring use it |
| Reading notes on Lean (`on: lean`, summary) | Proof Reader | Kept | Euler has 7,985 |
| Plain titles beside Lean names | all three | Kept (`names.json`) | |
| Declarations no sentence names | Proof Reader (`show_also`) | Kept, in the Lean view | Euler has 6,946 |
| PDF reading, zoom, link marks | Proof Reader | Kept | SMT-LIB and the NS authors' PDF |
| Statements at PDF named destinations | quartic | Kept, in the PDF kind | More exact than rectangles alone |
| Companion pages under their paper; grouped guides | Proof Reader (shelf) | Kept, as `documents[]` and the index | 43 NS pages |
| Large library guides with gz Lean report | Proof Reader | Kept, sharded by module | 30 NS guides, about 43k declarations |
| Copy formula as Unicode | Proof Reader | Kept | |
| Physlib API and dependency maps | Proof Reader | Kept, as the `api-map` kind | |
| Results index (every statement with its Lean verdict) | quartic | Kept, as each paper's `results/` list in About | The numbered-result addresses need it anyway |
| Authored journeys and path panel | quartic | Kept, optional data (`journeys.json`) | Only quartic has authored journeys |
| Per-paper position memory and Return | quartic | Kept | Needed once papers switch inside one site |
| Videos menu with chapters | lean-exposition, quartic | Kept, one menu | |
| Search | lean-exposition | Kept, across papers | |
| Hash-verified immutable editions, `?ed=` | quartic | Kept, as frozen snapshots under `quartic/editions/<ed>/` | Emailed links name fixed, checkable versions; see §1.6 |
| "AI-assessed" and "AI-drafted" labels on comparisons, titles and notes | lean-exposition, quartic | Kept on every phrase and Lean card | About also says no mathematician has reviewed them, as #257 does now |
| Per-instance front pages and hero (`FrontPage.tsx`, levels band) | lean-exposition | Dropped | No home pages per paper; credit and the "what this is" line move into the header and About |
| Proof Reader shelf front page | Proof Reader | Dropped, replaced by the library index | One home page |
| Phone statement sheet (`@sheet`) | Proof Reader | Kept as the reader's phone layout | lean-exposition's phone layout is the base; the sheet transition is adopted if it tests better |
| PDF or typeset toggle, keeping the place and selection | new, from Proof Reader's PDF pane and lean-exposition's reader | Kept | Will, 21 Nov: one document, two forms |
| Settings menu (theme, name order, topic colours, text size) | new | Kept | Only settings that change what a reader can do |
| Hash routes | Proof Reader, quartic | Dropped | Path routes give previews and static shells; redirects cover old links |

## 6. Redirects (every old address goes to its deep match)

`L` is `https://wcook04.github.io/library`. Each old site is replaced by a redirect stub, a small `index.html` and `404.html` that hold one mapping script. The stub keeps the query and fragment, and it calls `location.replace`, so Back is not broken. Each stub also prerenders a `<link rel=canonical>` and a visible link, for readers without JavaScript.

**`erdos-257-reader` (path routes; repo `wcook04/erdos-257-reader`, main).** Paper: `erdos-257`. The main document is the short paper; the pages are `record` (long) and `exposition`.

- `/` → `L/erdos-257/`. With map parameters (`g n t lens e`), it goes to `L/erdos-257/map/?…`.
- `/read/short/?…#a` → `L/erdos-257/?…#a`
- `/read/long/?…#a` → `L/erdos-257/record/?…#a`
- `/read/expository/?…#a` → `L/erdos-257/exposition/?…#a`
- `beside=<stage>:<anchor>` is rewritten to the new page slug.
- `/map/?…` → `L/erdos-257/map/?…`. `/compare/?…`, `/lean/?…` (to `source/`), `/checks/?…`, `/about/#…` and `/search/?…` → the same view under `L/erdos-257/`.
- `/verification/…` and `/pdf/…` files → the same paths under `L/erdos-257/`, as copied files, not scripts.
- **The plectis forwarding page.** The #257 problem page (`forward/erdos_257.html`, generated by `build_forward.py`) has its reader address constant changed to `L/erdos-257/`. It then forwards in one hop.

**`lean-exposition-site` (SK; path routes).** The same table, with paper `sk`, main document the short paper, and pages `record` and `exposition`. The SK Pages workflow then publishes the stub. The library carries the site.

**`quartic-query-lean` (gh-pages; hash routes).** The Library opens the expert companion by default. The current source reader opens OpenAI’s original paper and its verification supplement.

- `#/` → `L/quartic/`
- `#/about` → `L/quartic/about/`
- `#/results` → `L/quartic/about/#results`
- An unpinned `#/read/original?…` or `#/read/verification?…` goes to `L/quartic/source/` with the complete hash route.
- An unpinned `#/read/expert?…` goes to `L/quartic/`. The exposition and reconstruction use `L/quartic/<p>/`. Their parameters map as follows:
  - `st=<statement>` → `/<result>/`, using the converter's statement-to-result table
  - `d=<decl>` → `/lean/<decl>`
  - `ph=<phrase>` → `/@<tie>`, with ids kept
  - `s=<selection>` → `@<tie>`, or `?l=<start>-<end>` for `l…` line selections
  - `p=<page>` → `?page=`
  - `a=<id>` → `#<id>`
  - `v` → `v`, where `passage` and `closed` drop out
  - `j`, `step` → `?j=&step=`
  - `e=from→to→kind` → `map/?e=from~to~kind`
  - `ed=<hash>` goes to `L/quartic/editions/<hash>/` with the same route, which is the frozen snapshot (§1.6)
- `reading-api/v1/*` stays served for one release, for any outside reader.

**`proof-reader` (hash routes; `wcook04/proof-reader`, Actions Pages).** Every slug maps to a paper and page:

| Old slug | New address |
|---|---|
| `euler` | `L/euler/` |
| `navier-stokes-paper` | `L/navier-stokes/`, then `paper/` until the checked copy is the main document (§1.5) |
| `navier-stokes-digest` | `L/navier-stokes/digest/` |
| `navier-stokes-part-1`, `-part-2` | `L/navier-stokes/part-1/`, `/part-2/` |
| `navier-stokes` | `L/navier-stokes/what-the-lean-states/` |
| `navier-stokes-{index, appendix-b, cell-fidelity, cell-guide, cell-reference, certificate-checker, routes, route-details, statement-files}` | `L/navier-stokes/<same suffix>/` |
| `navier-stokes-library-NN` | `L/navier-stokes/library-NN/` |
| `pcp-full-argument`, `pcp-exposition`, `pcp-specialist`, `pcp-reading-guide` | `L/pcp/` (the main document: *to confirm* which of the four is the paper), then `L/pcp/<exposition\|specialist\|reading-guide\|full-argument>/` |
| `coupled-spring`, `contextual-embeddings`, `smtlib-2-7` | `L/coupled-spring/`, `L/contextual-embeddings/`, `L/smtlib/` |
| `physlib-gauge-theory` | `L/physlib-gauge-theory/` |

The parts after the slug map as follows:

- `@<passage-id>` → `@<tie-id>`. The ids are kept by the converter.
- `<claim-id>` (`result-1.1`) → `<result>/` (`theorem-1.1/`), using the converter's claim table.
- `<declaration name>` → `lean/<name>`
- `@<heading-id>` and legacy `#<heading>` → `#<section>`, using `heading_aliases`
- `@page-<n>` → `?page=<n>`
- `@declarations` → `source/?list=papers`
- `@file` → `source/?file=all`
- `@sheet` → the same address, with the phone sheet open
- Physlib's `@lean-N`, `@ref-N` and `@index` keep their meaning under `L/physlib-gauge-theory/`.
- An unknown name lands on the page with the reader's "not found" line, never on the root.

The static `/proof-reader/<slug>/index.html` stubs and `404.html` get the same table.

**The landing site.** Its links to the five old sites are changed to library addresses. This is a separate PR on `wcook04.github.io`.

Each redirect table is data: `redirects/<old-site>.json`, which lists old patterns, new patterns and examples. The stubs are generated from it. A test runs every example row through the stub's script and through the library's `parseRoute`.

## 7. Build, deploy and CI

**Source.** `wcook04/lean-exposition` holds the engine, `instances/*`, the converter and the redirect tables. **Output.** `wcook04/library` `main` holds the published files.

```
library/
  index.html, catalog.json, search/…, 404.html      (built by the catalog step)
  _engine/<engine-hash>/assets/*                     (one Vite build per engine change; old hashes kept while referenced)
  <paper>/data/*.json, <paper>/**/index.html shells  (per paper: data pipeline + shell prerender)
  <paper>/deployed.json                              (engine hash, content hash, source commit)
```

### Passage annotations

Author notes in `instances/<paper>/annotations/<slot>.json`. Each file maps a
`tie.phrase` in that document to an object whose keys are exact Lean declaration
names from `tie.rows` and whose values are nonempty note strings. A declaration
can have a different note in each passage. Use the document slot from
`instance.json` for companions. Euler and Navier–Stokes use `adapted.json` for
their adapted documents.

When a passage uses a mathematical idea the reader may be meeting for the
first time, show the smallest case in which the idea does work. Give the reader
a calculation, a move, or a case they can check, then name the hypothesis,
construction, or conclusion it prepares them to read. Check the connection
against the actual passage and the linked Lean statement. A small residual in
a scalar equation, for example, only becomes useful once the reader sees how
the linear correction changes it and where the quadratic error comes from.

Use the authors' paper, its cited literature, and the pinned Lean sources to
choose that example. Say what the example establishes and which extra inputs
the paper or Lean statement needs. If a previous note already teaches the
operation, use the space to explain what changes in this passage. For rows
that only identify a definition or record a precise difference in scope, a
short direct note is enough. Read the changed notes in passage order and
check that both the mathematical example and the return to the passage make
sense without additional notation.

State the mathematical move or claim in the passage, then point to the Lean
binder, field, or expression that lets the reader recognise it. When a Lean
declaration narrows the claim, say which hypothesis sets the boundary and
what is guaranteed inside it. Give a note enough space to explain both the
math and the code that the reader has open.

Use a specialist source to choose what the reader should do first. Look for
the simpler problem the source solves before using the general result, or the
first computation its argument expects a reader to be able to do. Choose an
exercise whose outcome helps the reader make a decision in the target
passage. For example, a diagonal strain makes phase transport easy to
calculate, while a shear exposes the error from transposing the forward map.
Record the source section and the passage it prepares in the
[reading routes](literature.md#what-to-work-out-before-each-paper).

The Library build uses [apply_passage_annotations.py](../scripts/apply_passage_annotations.py)
to add `annotation` to the matching Lean row in the static tie response. For a
companion or an adapted document the response is under
`edition/docs/<slot>/ties/short.json`. The build applies the notes after copying
the companion export, so its cache stays reusable. When an instance has an
`annotations/` directory, the build requires notes for all its active passage
and Lean pairs. Wrap Lean code in backticks and mathematical notation in
`$...$` so the reader can render each correctly.

To validate or update a local copy of a built reader, pass its `edition`
directory to the same script.

```sh
python scripts/apply_passage_annotations.py instances/euler /path/to/staged/euler/edition --complete
python scripts/apply_passage_annotations.py instances/euler /path/to/staged/euler/edition --complete --write
```

The first command checks that every exported phrase and Lean declaration pair
has an authored note. The second applies those notes after validation. The
script updates only the fixed-path tie JSONs named in the edition indexes and
preserves the snapshot hashes. Omit `--complete` to check only authored pairs.
An adapted document participates when the capture contains that companion
edition. The normal build requires its companion index when the adapted edition
is enabled.

**Workflow `library.yml` in lean-exposition.** It runs on push to main, on PRs (build and test only) and on dispatch.

1. **`plan`.**
   - It computes the engine hash, from `site/`, `src/lean_exposition/` and the lockfiles.
   - It computes each instance's content hash, from `instances/<paper>/` plus the folders it points at.
   - It reads each `deployed.json` from `wcook04/library`.
   - It writes a matrix of the papers whose content changed, and an `engine` flag.
2. **`engine`** (only if the engine changed). It runs `npm ci` with the npm cache, typechecks, runs the engine unit tests and runs one Vite build to `_engine/<hash>/`.
3. **`paper` (matrix, one job per changed paper, in parallel).**
   - It runs `check-instance`, `check-alignment` and `validate`.
   - It writes the data and prerenders the shells against the current engine hash.
   - It runs Playwright on that paper: one test per address kind (below), at 1440×900 and 2560×1440.
   - An engine change re-renders shells for every paper, which takes seconds per paper. Playwright then runs on the smoke set only, unless the PR is labelled `full`.
4. **`smoke`.** A fixed set runs on every deploy:
   - the library index;
   - `/euler/`, with a cold-cache load budget at 1440 width;
   - a Navier–Stokes library guide (the 43k-declaration case), with its own cold-cache load budget at 1440 width;
   - `/erdos-257/record/`;
   - `/navier-stokes/part-1/`;
   - the quartic PDF page;
   - one redirect from each old site.
5. **`deploy`** (main only, concurrency group `library-deploy`, never cancelled).
   - It checks out `wcook04/library` and replaces only the changed `<paper>/` folders and `_engine/<hash>/`.
   - It rebuilds `index.html`, `catalog.json` and the search shards' index.
   - It prunes engine hashes that no `deployed.json` references.
   - It scans for secret-shaped strings, commits "Publish <papers> from lean-exposition <sha>", and pushes with the deploy key (the pattern SK uses today).
6. **Redirect stubs.** These are published by a separate dispatch-only workflow per old site. Each one runs only after the paper it targets has deployed and passed smoke.

**Browser tests, one per address kind, on each changed paper:**

1. `/<paper>/` opens at the top of the main text.
2. `/<paper>/<page>/` opens that companion.
3. `#<section>` scrolls to the section.
4. `/<result>/` selects the result's statement and opens its Lean.
5. `@<tie>` selects the phrase and shows its card, with comparisons and note.
6. `lean/<name>` opens the card and highlights every phrase that states it.
7. `topic/<id>/` filters to the topic.
8. Copy link reproduces the address for each of 3–7.
9. Clicking a phrase opens its Lean.
10. Topic colours show.
11. The Graph view draws.
12. For each old-site table, five sample redirects land on their deep matches.
13. The Open PDF link exists, points at the PDF path, opens a new tab, and the file returns 200 with `application/pdf`.
14. Each toggle and setting has a test. One test switches between PDF and text with a phrase selected and checks that the selection and the reading position are kept.

**Local publish scripts.** `scripts/publish_library.sh <paper…>` runs the same steps as the matrix and deploy jobs. It is for use when Actions is unavailable.

## 8. Migration order

Each step goes live only after its browser check at 1440×900 and 2560×1440.

1. Engine generalisation (documents in place of stages, runtime data, library router), with SK and #257 still building as today.
2. Euler, through the converter.
3. Navier–Stokes: the digest and Parts I–II first, then the other companions, then the paper when the checked copy arrives.
4. #257 and SK move into the library, and their old sites become redirect stubs.
5. Quartic, which needs a converter from its reading-api edition.
6. The remaining Proof Reader pages, and the Proof Reader redirect stubs.

## Open points for confirmation

- Proof Reader Euler and NS pages redirect after their check (§1.4), against the earlier brief's "leave them up".
- Which PCP page is the paper (`pcp-full-argument` or `pcp-specialist`).
- The repo name `wcook04/library` and the address `/library/`.

## Status, 21 November 2026 (branch claude/euler-ns-readers-20261121, PR #88)

Built and checked:
- **The `library` instance.** It reads one paper from `instances/<paper>/instance.json`.
- **Addresses.** `/`, `/#<section>`, `/<result>/`, `/@<tie>`, `/lean/<name>`, `/<page>/` and `view=pdf&page=N` all work, and Copy link round-trips them (`site/tests/library-address.test.ts`).
- **PDF toggle.** The Text | PDF toggle uses pdf.js. Phrases are placed on the PDF by `scripts/pdf_marks.py`.
- **Open PDF.** The link opens the PDF and carries `#page=N`.
- **Reading notes.** Notes on any Lean card come from `lean-notes.json`.
- **Supplementary checks.** They are listed in About.
- **Converter.** `scripts/from_proof_reader.py` has `--reimport`, `--guide` and `--pdf`, and it carries Comparator folders. A re-import keeps every old tie id as an address: a phrase merged into another is an alias of the tie that holds it, and a tie that is gone is retired (`aliases.json` `retired`), so its address opens a notice with the date and the nearest current phrase instead of landing on a neighbour. A comparison is assessed (a verdict), held, or `unassessed`; a missing one is never written as `same`. Overlapping phrases share one tie that lists them (`merged`) and keeps each phrase's own comparison on every Lean row (`assessments`). Each numbered result's statement is its block from the authors' bold label to the end of that paragraph; the tie index names that block and its tie as the result's canonical target (`canonical`), which addresses, search, Copy link, Compare and the graph use.
- **Publishing.** The private-source guard runs before every publish. `library.yml` handles per-paper builds, browser checks and deploys.

Changed from the plan:
- **Engine bundle.** Each paper is still its own Vite build, about 10 seconds, deployed only when it changes. Splitting out one shared engine bundle is deferred: it does not change what a reader sees or what a deploy costs.
- **Encoding guide.** The guide to how the Lean encodes the paper is an instance document, a companion page at `/<paper>/how-the-lean-encodes-it/`, rather than an About section. It keeps its own addresses and phrases.

Not yet built:
- the library index search;
- the settings menu;
- the redirect stubs;
- a Comparator pane, which waits for the receipt at the authors' final commit;
- topic filter addresses (`/topic/<id>/`).

## Status, 22 November 2026: the remaining Proof Reader papers

PCP, the coupled spring page, Contextual Embeddings and the SMT-LIB standard are library papers, converted by `scripts/from_proof_reader.py`. The engine and converter gained these, each optional in the instance format:

- **Results the paper states without a number.** A result Proof Reader titles in words keeps the number the paper prints for it ("Lemma 4.1 (standard low-degree test)" gives `/lemma-4.1/`); one with no printed number keeps its claim id as its address (`/claim-source-13/`), so the old claim address maps onto it exactly. `--goal document` makes the document itself the map's root for a paper that numbers no results (SMT-LIB).
- **A fourth document.** A build carries three documents. A paper with more names the others as documents read in another build (`documents[]` entries with `href` and no slot), and the Read menu links to them. The other build is an instance served at its own `path` under the paper (`pcp-reading-guide` at `/pcp/reading-guide/`). Publishing and CI keep such nested folders when the paper's folder is replaced (`.library-paper` marks), and the library's 404 page sends their addresses to their own shell.
- **Companion phrase and Lean addresses.** `/<page>/@<tie>` and `/<page>/lean/<name>` open a phrase or a declaration on a companion page (`addresses.json` `pages`).
- **Not found.** A phrase address that names no phrase opens the document at its top with a "Not found" line, never a guessed place.
- **PDF-only documents.** A document whose only form is the authors' PDF (`pdf_only`) opens in the PDF with no Text toggle. Its phrases, cards and search come from an index of the passages Proof Reader quotes from it, in page order, which is never shown as text.
- **Converter input.** Proof Reader's own passage markers and YAML front matter are stripped; GitHub heading fragments in links between pages become section numbers; other relative links resolve against the page's repository URL; quotes are found through inline Markdown markup (code, emphasis, links); `--authors`, `--companion-credit`, a noun per companion, `--path` and `--external`.
- **Checks.** `authored/check.json` may list declarations whose bodies use only Mathlib (`no_uses`). `check_library_paper.py` has `--no-pdf` and `--pdf-only`, accepts result addresses after a phrase click, and checks the "Not found" line.
- **Redirects.** `scripts/proof_reader_redirects.py` writes `redirects/proof-reader.json` and the stub Proof Reader loads first (`web/public/library-redirects.js`), only for pages whose library address answers 200.

The Physlib gauge-theory map stays on Proof Reader. Its page is an API map, not a paper: its addresses `@lean-N`, `@ref-N` and `@index` name Physlib's own reference lists, and its dependency map is drawn from module imports. The engine has no `api-map` document kind yet, and a conversion as a plain document would break those addresses.

## Adapted editions (built 22 November 2026, off for every paper)

The design is docs/reader-design.md, "Adapted editions". What is built:

- **Converter.** `scripts/adapted_edition.py convert` sets an edition's reading copy from its TeX with the same route as the authors' (Proof Reader's `reading_copy.py`; it first checks that this route reproduces the authors' reading copy byte for byte). It aligns the two texts paragraph by paragraph, by Proof Reader's paragraph ids (`<heading>#<block>`, `site/scripts/source-blocks.mjs`), and gives each differing paragraph its change from the public change map (`CHANGES.json`). It carries every phrase tie whose paragraph is the authors' unchanged. It stops unless every `% CHANGE` mark has its row, every differing paragraph has a change, every change shows in a paragraph, and no TeX line differs from the authors' source outside a marked paragraph. It writes `instances/<paper>/adapted/` (`edition.json` holds the flag `published`).
- **The flag.** A build includes the edition only when `published` is true, or for a local preview with `LX_PREVIEW_ADAPTED=1`; `scripts/build_library_paper.sh` stages it into a free document slot and takes it out again. With the flag off, or with no `adapted/` folder, a paper builds exactly as before.
- **Reader.** The switch "Authors' paper / Adapted edition" in the strip keeps the place by paragraph and says when a paragraph has no counterpart. In the edition each changed paragraph has a faint ink wash and a dotted ink rule in its right margin, headed by an open square that opens the change (both texts, kind, note, sources) in the pane; "Show changes" lists every change. The authors' paper carries no marks, only a quiet square on a paragraph the edition changes. The edition's header and About carry its credit, verbatim, beside a link to the authors' paper. The PDF view opens the declared ordinary reading PDF when available. Older editions use their declared PDF. The build places phrase ties on the file shown in the reader (`scripts/pdf_marks.py`). Editorial controls live in Show changes and the marked archive.
- **Downloads.** Besides `pdf` (the marked download) and `aux_pdf`, `edition.json` may declare `reading_pdf` (the ordinary PDF shown in the reader) and `aux_reading_pdf`, `source_overlay` (the TeX revisions against the authors' source, the only public TeX archive) and `result_comparison.reading` and `.data` (the result-by-result comparison, Markdown and JSON). Each is `{file, name, label?, bytes, sha256}`. The build checks that the file is inside `adapted/` and has the declared bytes and digest, then copies it byte for byte: PDFs to `pdf/<name>`, the others to `<slug>/<name>`, one level below the paper root, where the comparison's relative links (`../?l=`, `../adapted/?l=`, `../lean/?m=`) resolve. About lists the declared downloads (the comparison's JSON as data) and sets the comparison itself as its own section, `about/#result-comparison`, rendered from its Markdown with its links resolved against the address it is published at; a cold link to that address lands on it.
- **Private words.** `convert` refuses a change map whose notes or sources carry a transcription paragraph id, a review-card id, a local file name of the literature or a dotted Lean name. The build of a converted edition does not repeat this check.
- **Checks.** `tests/test_adapted_edition.py`, `site/tests/adapted-changes.test.ts`, and `scripts/check_adapted_edition.py` in a browser at 390, 1100, 1440, 2000 and 2560, with each paper's own credit (`document.credit`, unless `--credit` is given). The Library workflow runs it for every paper whose edition is published.
- **Publishing**, once agreed: `scripts/publish_adapted_edition.sh <paper> <library checkout>`.
