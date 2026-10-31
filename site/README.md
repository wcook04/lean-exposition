# Reading website

Read the [published website](https://wcook04.github.io/lean-exposition-site/).
The published edition runs entirely on GitHub Pages.
[lean-exposition](https://github.com/wcook04/lean-exposition) owns the source,
papers and build workflow.
[lean-exposition-site](https://github.com/wcook04/lean-exposition-site) holds
the generated website; make changes here and let the workflow publish them.

The website shows one captured edition of the worked example as a reader would
want to explore it:

- **The argument map.** The main result is at the top, with the records its
  recorded argument uses beneath it. Selecting "Inputs" on a card draws the
  records that card uses. A line runs from a record to the result that uses it,
  and each line opens the recorded explanation of that step. Assumptions are
  drawn as tags on the results that assume them. A switch narrows the map to the
  records one paper discusses. On a phone the same argument is an outline you
  scroll.
- **Compare.** The proof as a table. Each row is one step and each column is a
  level, so a step's Lean declaration sits beside its exact statement in the long
  record, the short paper and the exposition. Choose which levels show, and open
  any row to read that step in full and walk through the proof.
- **The papers.** The exposition, the short paper and the long reasoning record.
  The pane facing the paper has two modes, Graph and Lean. The graph follows the statement
  you are reading, and pointing at a marked statement lights its card and names it. Clicking
  a statement or a card goes to its Lean, and any Back returns to the graph and your place.
  Choosing Lean yourself keeps the Lean following the text.
  Beside any passage you can list the records linked to it and open passages in
  the other accounts that are linked to the same records.
- **The Lean index.** OpenAI's source, every module and declaration, at the back of
  the book: plain titles first, each central name explained in the papers' notation,
  and the names each declaration mentions.
- **The checks.** What compiled, which axioms, any `sorry`, what Comparator has and
  has not done, and what people or agents read. Then, for each kind of check, what
  it tests and the outcome of each recorded run: passed, failed, unavailable or not run.
- **The architectural companion.** The About page includes the paper on why
  several accounts share one record, with a link to its standalone PDF.
- **The papers and PDFs.** The front page's levels band (the Read menu's "All papers
  and PDFs") shows each paper's first page, who it is for, and links to read it here
  or open its PDF.
- **The videos.** [How to use this site](https://www.youtube.com/watch?v=sYMDcT7vyng),
  near the top of the front page, and [the mathematics](https://www.youtube.com/watch?v=IUAhxUriDVw),
  at the end of its layers. Both open on YouTube.

Search with <kbd>/</kbd>, or <kbd>Ctrl</kbd>/<kbd>⌘</kbd>+<kbd>K</kbd>. The design
rules (type, colour, the map's drawing conventions, motion and wording) are in
[DESIGN.md](DESIGN.md).

The argument map, the three accounts and the recorded checks come from the
read-only [web API](../docs/web-api.md). The site pins the edition it opened, and if the
server starts serving a different edition it says so and asks you to reload.

## Build the GitHub Pages edition

After installing the Python package, assemble and export the bundle from the
repository root:

```sh
lean-exposition assemble examples/qaoa-sk/evidence-graph.json \
  --long papers/qaoa-sk/long/reasoning-record.md papers/qaoa-sk/long/reasoning-record.json \
  --short papers/qaoa-sk/short/paper.md papers/qaoa-sk/short/correspondence.json \
  --expository papers/qaoa-sk/expository/main.md papers/qaoa-sk/expository/correspondence.json \
  --out build/reading-edition
python site/scripts/export-static.py build/reading-edition \
  --lean-tree examples/qaoa-sk/upstream/lean \
  --alignment examples/qaoa-sk/alignment
cd site
npm ci
REQUIRE_STATIC_PARITY=true npm test
VITE_STATIC_EDITION=true VITE_BASE_PATH=/lean-exposition-site/ npm run build
```

The exporter captures responses from the existing Python application. The
browser loads those files, pages captured record tables, matches text selections
to whole passages, and searches the server's indexed fields with Python's Unicode
casefold rules. Tests compare search results and highlights against the server.
This transport supports the reading website; it is not a complete hosted API.
The bundle's draft, review and publication metadata remain visible.

The export is deterministic and replaces any earlier export. Each response is a
content-addressed file. `index.json` holds only what startup needs; the maps for
`/record`, `/papers/query`, `/papers/reading` and `/lean/module` load when a reader
first asks for that route.

Record requests for one table load only that table's file, and a request with no
table reads the same per-table files. The static edition carries only what the
reader reads: a smaller paper structure without the expanded correspondence edges,
paper queries reduced to their matches, and record responses whose passage text is
restored from the paper's own bytes. The live API keeps the full responses. The
exporter writes unpublished samples of those to `build/edition-oracle/`, and
`tests/static-edition.test.ts` compares the static edition with them.

The Lean index and record alignment have fixed paths (`lean/modules.json`,
`lean/names.json`, `lean/module/<module>.json`, `alignment.json`), load on demand,
and change no paper file. An alignment row that fails is printed and left out, so a
reading edition survives a file still being written;
`lean-exposition check-alignment examples/qaoa-sk/alignment` is the strict check.

The build writes route entry files for direct paper, map, search and checks
links, so a page reload needs no Python server. `site/public/edition/` and
`site/dist/` are generated output and stay out of the source repository.
The build also copies the four maintained PDFs into `pdf/`: `long-record.pdf`,
`short-paper.pdf`, `exposition.pdf` and `architecture.pdf`. These are the rendered
files already in `papers/`; render and inspect them before publishing a new edition.
The three mathematical PDFs are also copied unchanged to
`long/reasoning-record.pdf`, `short/paper.pdf` and `expository/main.pdf`. These
aliases preserve their relative links to one another, including links opened
from the existing `pdf/` downloads.
The companion's Markdown is embedded from `papers/architecture/paper.md` at build
time rather than included as a fourth account in the captured bundle.
The papers shelf shows each PDF's first page from `public/paper-pages/`, rendered with
`python site/scripts/render-paper-pages.py` (Poppler's `pdftocairo` and `cwebp`).
Its `manifest.json` records each PDF's SHA-256: the build shows a picture only while it
matches its PDF, and `npm test` fails until a re-rendered PDF's picture is rendered
again.
The build also publishes the explicitly listed Support build and extraction
observation at `verification/full-support-build-extraction-observation-20261026.json`.
The Checks page links to it. `publicObservations()` in `vite.config.ts` owns this
one-file list and serves the same JSON during local development.

The [publishing workflow](../.github/workflows/pages.yml) rebuilds on pushes to
`main`, checks the static search against the server, and pushes only `site/dist/`
to `wcook04/lean-exposition-site`. That repository serves its `main` branch with
GitHub Pages. `PAGES_DEPLOY_KEY` is a repository secret containing a write-enabled
deploy key scoped to that public output repository. Only the built website is copied into the deployment repository.

## The family of websites

This site is one of [Will Cook's websites](https://wcook04.github.io/), which share a
header lockup (the Plectis plait, which opens the home page, a short rule, then this
site's mark and name), film slots and a footer list of the other sites, as the [family contract](https://github.com/wcook04/wcook04.github.io/blob/main/docs/family.md)
describes. `src/app/family.json` is an unchanged copy of that repository's `sites.json`
and `src/styles/family.css` of its `assets/family/family.css`; `src/styles/tokens.css`
maps the stylesheet's `--fam-*` names onto this site's tokens. `public/plectis.svg` is an unchanged
copy of that repository's `assets/family/marks/plectis.svg`, served beside the site. A film without a
YouTube address is held "In preparation". When one is published, copy the updated
`sites.json` to `src/app/family.json` and the film's two stills
(`assets/films/<id>-640.webp` and `-1280.webp`) to `public/films/`, then rebuild: its
slot shows the still, play chip and running time and opens YouTube. The tests check
that every released film this site shows has both stills.

## Run it locally

You need Python 3.11 or newer with the package installed (see the
[development setup](../CONTRIBUTING.md#setup)) and Node.js 20.19 or newer.

1. [Assemble the authored papers](../papers/README.md#assemble-the-authored-bundle)
   into `build/qaoa-sk-authored`.
2. Serve the bundle from the repository root. The document paths let the API
   [resolve links between the papers](../docs/web-api.md#resolve-captured-companion-links):

   ```sh
   lean-exposition serve build/qaoa-sk-authored --port 8000 \
     --document-path long long/reasoning-record.md \
     --document-path short short/paper.md \
     --document-path expository expository/main.md
   ```

3. In a second terminal, start the site:

   ```sh
   cd site
   npm install
   npm run dev
   ```

Open <http://localhost:5173>. The development server forwards `/api` to
`127.0.0.1:8000`. Set `LEAN_EXPOSITION_API` to use another address.

## Build and deploy

```sh
npm run build
npm run preview
```

`npm run build` type-checks the code and writes a static site to `site/dist`.
`npm run preview` serves that build on <http://localhost:4173> with the same
`/api` forwarding.

To deploy, serve the API and the site from one origin:

- Host the [WSGI application](../docs/web-api.md#run-a-captured-edition) at the
  origin root, which keeps its `/api/v1` routes.
- Serve the files in `dist/` for every other path. Fall back to `index.html` for
  unknown paths, because the site uses routes such as `/read/short`.

To call an API on another origin instead, set `VITE_API_ORIGIN` when building.
Then start `serve` with `--allow-origin` set to the site's origin.

## Check it

```sh
npm run typecheck
npm test
```

The tests read fixtures captured from a running server in `tests/fixtures/`, so
they need no server. After you reassemble the bundle, recapture them with
`node scripts/capture-fixtures.mjs http://127.0.0.1:8000`. Check visual changes
in a browser at desktop and phone widths, in both colour schemes.

After a paper or reader change, exercise a companion link in the built site under
its deployed base path. Confirm that the opened view contains the intended
argument, not just its heading, and that returning restores the reading position.
A new inner scroller needs a `data-keep` attribute or an entry in `SCROLLERS` in
`src/app/restore.ts`, and a new tab or open panel uses `useEntryState` from
`src/app/trail.ts`, so that Back restores them.
Also open the link normally or copy its address: an in-app click handler can hide
an invalid public URL. Check the actual paper sources for print-only layout
commands leaking into the reader, while preserving mathematical notation and
literal code examples. Anchor existence, matching file hashes and successful
rendering are necessary checks; they do not establish that a reader can recover
the promised explanation.

## Where the code lives

| Folder | What it does |
| --- | --- |
| `src/api/` | API types and the client. The client pins the edition by its manifest hash. |
| `src/home/` | The front page at "/": the first screen as plain HTML (`heroMarkup.ts`), the levels band with the argument narrowing (`LevelsBand.tsx`), the mathematics and the recorded checks |
| `src/compare/` | Compare: the table of every step at each level (`table.ts`, `StepTable.tsx`), one step in full (`StepBench.tsx`), the record alignment's hook and the slice renderer |
| `src/lean/` | The Lean viewer (`LeanBlock`), its tokenizer and data hooks, and the Lean browser at "/lean" |
| `src/model/` | The argument graph built from the API: records, typed edges with their warrants and theorem applications, sources and the papers' selections. Traversal keeps each application's supplied premises within that use, as the backend does. |
| `src/map/` | The map page at "/map" and its state (`MapPage`, `scene.ts`), its header and strip, the argument tree (`ArgumentTree`), its screen-space layer (`canvas/`), the phone outline (`ArgumentOutline`), the Lean graph (`useLeanGraph`, built by `model/leanGraph.ts`) and the layout and routing engine (`engine/`) |
| `src/panels/` | The inspector that opens when you select a record or a step |
| `src/ribbons/` | The three account strips (`StripMarks`, shared with the front page), folded into a bar under the map until opened |
| `src/reader/` | The paper reader: Markdown and KaTeX rendering, anchors, links, reviewed references that open in place, the reading page, its passage inspector, the linked-passage chooser and side-by-side visits |
| `src/figures/` | Redrawn paper figures: the mathematical plots and the companion's shared claim, joint inputs and reading journey; the missing-area plot has an optional Explore mode |
| `src/checks/`, `src/search/` | The checks page, the search palette and the full search results page |
| `src/styles/` | Design tokens and shared classes; see [DESIGN.md](DESIGN.md). `family.css` is the family's shared stylesheet, copied unchanged |
| `src/app/` | The frame: routes, the top bar with the family's lockup, the edition's data, the film slot and the sister sites (`FilmSlot.tsx`, `SisterSites.tsx`, from `family.json`) |

## Conventions

- **Edges.** Stored edges run from a consumer to its prerequisite, as everywhere
  in this repository. The map draws arrows the other way, from a record to the
  result that uses it, as Lean blueprint dependency graphs do.
- **What the map draws.** A support link is not drawn when another drawn route
  of support links already joins the same two records; the map says how many
  links it leaves out and lists them, and the inspector lists every direct link.
  Assumption and Lean links are always drawn. A record with no recorded inputs
  that several results use is drawn under each of them.
- **Readable at every scale.** Steps keeps card titles at reading size. When you
  zoom out, cards become titles and then tiles in their source colour.
- **Colour.** The three source colours were checked together for colour-vision
  deficiency in both colour schemes. Each relation type has its own line colour
  and pattern. Amber is kept for selection and traces. Every colour is
  accompanied by a text label.
- **Motion.** All motion follows the reader's reduced-motion setting, which the
  site reads again whenever it changes.

## Limitations

- The published site contains one captured edition. Local development can read
  an edition from the Python server; neither mode provides an edition archive.
- A text selection is matched to whole passages, and the reader says so.
- Passages are linked to records, not to individual steps. A passage linked to
  both records of a step is related reading, not a located proof of that step.
- Each warrant is an authored account of a step taken from the sources. The
  edition records no independent review of these warrants, and the site reports
  their status as recorded.

## Licences

The site is licensed under Apache-2.0, like the rest of the repository. The
layout and routing code adapts algorithms from MIT-licensed projects; see
[third-party notices](THIRD_PARTY_NOTICES.md). Each dependency keeps its own
licence:

- React, KaTeX and markdown-it: MIT
- d3 modules: ISC
- DOMPurify: MPL-2.0 or Apache-2.0
- STIX Two Text, Source Sans 3 and JetBrains Mono fonts: SIL Open Font License 1.1
