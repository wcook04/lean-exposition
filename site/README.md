# Reading website

The website shows one captured edition of the worked example as a reader would
want to explore it:

- **The map.** The main result sits at the top with its recorded argument beneath
  it. Unfold any result into what it uses. Colour shows where each step comes
  from, and each arrow runs from a result to the one it helps prove. An arrow
  carries the recorded warrant for that step.
- **The papers.** The exposition, the short paper and the long reasoning record,
  each with the claims of the passage you are reading beside the text and routes
  to where the other accounts treat the same mathematics.
- **The checks.** What each recorded check examined and what it found.

Search with <kbd>/</kbd>, or <kbd>Ctrl</kbd>/<kbd>⌘</kbd>+<kbd>K</kbd>.

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
| `src/model/` | The argument graph built from the API: records, typed edges with their warrants, sources and the papers' selections |
| `src/map/` | The map page, the unfolding argument tree and its layout and connector engine |
| `src/panels/` | The record panel that opens when you select a result or a step |
| `src/ribbons/` | The three account strips docked under the map |
| `src/reader/` | The paper reader: Markdown and KaTeX rendering, anchors, links and the reading page |
| `src/figures/` | Interactive versions of the papers' figures |
| `src/checks/`, `src/search/` | The checks page and the search palette |
| `src/styles/` | Design tokens and base styles |

## Conventions

- **Edges.** Stored edges run from a consumer to its prerequisite, as everywhere
  in this repository. The map draws arrows the other way, from a result to the
  one it helps prove, as Lean blueprint dependency graphs do.
- **What the map draws.** It draws the shortest skeleton of the visible records.
  A direct use that a longer visible route already implies is not drawn, but it
  is still listed in the record panel.
- **Colour.** The three source colours were checked together for colour-vision
  deficiency in both colour schemes. Amber is kept for selection and traces.
  Every colour is accompanied by a text label.
- **Motion.** All motion follows the reader's reduced-motion setting.

## Limitations

- The site reads one edition from a running server; it has no offline copy.
- A text selection is matched to whole passages, and the reader says so.
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
