# Reading website

The website shows one captured edition of the worked example as a reader would
want to explore it:

- **The argument map.** The main result is at the top, with the records its
  recorded argument uses beneath it. Selecting "Inputs" on a card draws the
  records that card uses. A line runs from a record to the result that uses it,
  and each line opens the recorded explanation of that step. Assumptions are
  drawn as tags on the results that assume them. On a phone the same argument is
  an outline you scroll.
- **The papers.** The exposition, the short paper and the long reasoning record.
  Beside any passage you can list the records linked to it and open passages in
  the other accounts that are linked to the same records.
- **The checks.** For each kind of check, what it tests and the outcome of each
  recorded run: passed, failed, unavailable or not run.

Search with <kbd>/</kbd>, or <kbd>Ctrl</kbd>/<kbd>⌘</kbd>+<kbd>K</kbd>. The design
rules (type, colour, the map's drawing conventions, motion and wording) are in
[DESIGN.md](DESIGN.md).

Everything shown comes from the read-only [web API](../docs/web-api.md). The site
adds layout and wording, not facts. It pins the edition it opened, and if the
server starts serving a different edition it says so and asks you to reload.

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

## Where the code lives

| Folder | What it does |
| --- | --- |
| `src/api/` | API types and the client. The client pins the edition by its manifest hash. |
| `src/model/` | The argument graph built from the API: records, typed edges with their warrants and theorem applications, sources and the papers' selections. Traversal keeps each application's supplied premises within that use, as the backend does. |
| `src/map/` | The map page and its state (`MapPage`, `scene.ts`), the argument tree (`ArgumentTree`), its screen-space layer (`canvas/`), the phone outline (`ArgumentOutline`) and the layout and routing engine (`engine/`) |
| `src/panels/` | The inspector that opens when you select a record or a step |
| `src/ribbons/` | The three account strips, folded into a bar under the map until opened |
| `src/reader/` | The paper reader: Markdown and KaTeX rendering, anchors, links, the reading page, its passage inspector, the linked-passage chooser and side-by-side visits |
| `src/figures/` | Interactive versions of the papers' figures |
| `src/checks/`, `src/search/` | The checks page, the search palette and the full search results page |
| `src/styles/` | Design tokens and shared classes; see [DESIGN.md](DESIGN.md) |

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

- The site reads one edition from a running server; it has no offline copy.
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
