# Serve the graph and papers

The web backend serves one assembled explanation bundle through a read-only,
versioned JSON API. It supplies the shared corpus, paper subgraphs, exact text,
passage correspondences and navigation witnesses. A client can build a graph
explorer, a paper reader or an agent tool against the same data. This package
does not supply a frontend.

## Riemann Hypothesis paper backend

The RH backend packages Qui Vincit and Fable's version 1.5 exposition and
one-page outline under CC BY 4.0. It pins the paper and Lean separately. The
paper data are static. The full compiled graph uses a separate read-only index
that is about 1.8 GB.

Download `decls.parquet`, `decl_edges.parquet`, `constants.parquet` and
`edges.parquet` from [the compiled dependency release][rh-dependencies].
Clone [the paper repository][rh-paper]. From the Lean Exposition checkout,
use Python 3.11 or newer with NumPy, PyArrow, SciPy and PyPDF, Node 22.18 or
newer for the shared reader palette, and Poppler's `pdftotext`:

```sh
python scripts/build_rh_index.py /path/to/dataset build/rh-index
python scripts/build_rh_paper.py /path/to/paper-checkout /path/to/dataset/decls.parquet build/rh-index
PYTHONPATH=src python scripts/serve_library.py instances/riemann-hypothesis/edition 43843 --proof-index build/rh-index
curl http://127.0.0.1:43843/paper/manifest.json
curl 'http://127.0.0.1:43843/api/proof/neighbourhood?name=Deduction.zeroFree_of_rpow_window'
```

The paper build reads the pinned Git revision, verifies both PDF hashes and
checks Lean declaration names and line spans against the pinned export.
Use `--out` to stage the static assets elsewhere. The server puts the static
paper and graph API on one origin for local checks.

For an existing index, use the four pinned Parquet files to add the statement
neighbourhoods without rebuilding the full adjacency.

```sh
python scripts/build_rh_index.py /path/to/dataset build/rh-index --statement-neighbourhoods-only
```

### Connect the Library reader

The Library site uses the same reader and argument map as the Euler and
Navier–Stokes editions. After generating the paper and proof index above,
install the site's npm dependencies and build the RH edition.

```sh
npm ci --prefix site
PYTHONPATH=src python scripts/build_rh_library.py \
  --proof-index build/rh-index --lean-source /path/to/rh-lean-checkout
```

For the standalone GitHub Pages candidate, add `--public` to the same
command. Serve the build as `/riemann-hypothesis-reader/` and keep its
`404.html` for deep links. This build exports module metadata and fetches
Lean source directly from the pinned community repository. It checks the
SHA-256 of each file before displaying it. The public build does not bundle
the Lean source files or require a proof server.

To preview the built reader and the module API on one origin, serve them
together with the paper manifest.

```sh
preview=$(mktemp -d)
mkdir -p "$preview/library"
ln -s "$PWD/site/dist" "$preview/library/riemann-hypothesis"
ln -s "$PWD/instances/riemann-hypothesis/edition/paper" "$preview/paper"
cp site/dist/404.html "$preview/library/404.html"
PYTHONPATH=src python scripts/serve_library.py "$preview" 43843 \
  --proof-index build/rh-index --lean-source /path/to/rh-lean-checkout
```

Open `http://127.0.0.1:43843/library/riemann-hypothesis/`. The Map page
uses direct compiled references and recorded predecessor paths between the
paper-linked declarations in the proof. An edge can pass through intermediate
declarations. The Lean graph uses these paths without loading the module text.
Opening Lean fetches the pinned module and offers notes and reviewed PDF links
at the corresponding lines. The full compiled graph stays on the server. On a
hosted reader, route `/api/proof/` to that server on the reader's origin.

The edition's `reader.json` supplies the display title for every paper-linked
declaration. The map, reader and Lean API use those titles. The Lean names
identify the source declarations and their links.
Its optional `graph_titles` supplies aliases for additional compiled
neighbours and proof-route helpers. These aliases change display text while
preserving the neighbour selection and the exact Lean identifiers.

| Reader surface | Input and join |
| --- | --- |
| PDF | Pass `paper.pdf` and `pdf-marks.json` to the existing PDF view. Its mark ID opens `passages.json.passages[id]` first, then `annotations.json.annotations[id]`. The first contains whole passages and the second contains individual Lean references. |
| Topics | Pass `topics.json.topics` to the existing topic colour helper. `tone` identifies the same colour in the PDF marks and graph. `sections.json` gives each numbered section its topic and PDF page. |
| Lean | Each target supplies its full name, module, pinned file URL and declaration lines. Inspected boundaries supply `statement_lines` and, when present, `proof_lines`. Each passage also links to its source TeX lines. |
| Lean checks | `lean-checks.json` binds two sources to the paper edition. `archive` links to the paper authors’ `#print axioms` and kernel replay results for the five named theorems in `Main`. `graph` gives axiom declarations reachable in the compiled dependency graph for each linked declaration in the RH proof. The Lean module API projects these as `archive_check` and `graph_axioms`. |
| Lean notes | `lean-notes.json.notes` uses the Library reader's existing full-name to `{text}` format. `sources[name]` keeps individual excerpts, attribution, note source links and `lean_lines` for a line-specific inspector. |
| Lean line selection and search | `lean-lines.json.modules[module]` lists declarations by source line. A row's `canonical` is the preferred PDF address for the declaration. Its `links` give source ranges, topic, role and mark ID. Its `notes` point by zero-based index into `lean-notes.json.sources[name]`. |
| Graph and reverse links | For a target with `in_proof: true`, use the full Lean name with `/api/proof/neighbourhood`. `lean-notes.json.bindings[name]` supplies its source, topics, whole passage IDs and clickable PDF mark IDs. The same topics can label graph nodes. |

The existing Euler and Navier–Stokes editions ship longer notes and reading aids
as separate files. The PCP readers use compact declaration notes. The RH reader
can load the PDF marks and topic palette with the paper, then load the line
index and note sources when a reader opens Lean, searches for a declaration,
or follows a graph node back to the paper.

### Serve inline Lean for the paper

Install Lean Exposition in the server's Python environment. With a local Git
checkout containing the archived Lean commit, start the server with
`--lean-source`. The server reads the pinned Git blobs for the modules named
by the generated paper links and checks those links against the paper manifest
and compiled proof at startup.

```sh
PYTHONPATH=src python scripts/serve_library.py instances/riemann-hypothesis/edition 43843 \
  --proof-index build/rh-index --lean-source /path/to/rh-lean-checkout
curl http://127.0.0.1:43843/api/proof/lean/modules
curl 'http://127.0.0.1:43843/api/proof/lean/module?name=Main'
```

`/api/proof/manifest` advertises `lean_sources` when configured. `lean/modules`
gives the folder index and `lean/names` the compact declaration rows. The
`declarations` field in `lean/names` includes display titles, statement boundaries, module
paths and direct type and value references within this catalogue. It carries
no Lean source text. Request one module from `lean/module?name=…` when its
source is needed. Its payload
matches the [Lean module contract](#serve-the-lean-index-and-record-alignment)
and includes `paper_links` for the matching PDF marks and Lean notes. RH
endpoints return these data objects directly.

Each response includes the Lean and paper revisions and the paper manifest
hash. Pass that hash as `manifest` on a Lean source request to get **409** if
the server has opened another paper edition. A module outside the paper-linked
catalogue returns **404**. The module's `uses` and `used_by` list direct compiled
references among the linked declarations. The full adjacency remains available
through the proof neighbourhood API.

The module response can also give each declaration a `neighbourhood`. It shows
up to 12 named dependencies and 12 named users, preferring project declarations
and paper links. Each neighbour lists the recorded `kinds` (`type`, `value` or
both). The `counts` give totals before the display limit. The `dataset` and
`scope` identify the compiled evidence.

| Scope | Recorded references |
| --- | --- |
| `riemann_hypothesis_closure` | Direct constant references in the Riemann Hypothesis theorem's closure. |
| `published_theorem_export` | Direct constant references for statements from the other theorems in the same export. |
| `compiled_project_declarations` | Direct references between project declarations in Main's compiled environment. The export groups some auxiliary constants into their owning declarations. |

An absent `neighbourhood` means that the configured index cannot supply this
view. An empty list with a zero count means the recorded scope contains no
neighbours in that direction.

Each declaration's `signature_source`
records whether its statement boundary came from the paper alignment, the
Lean source parser, or the full declaration range.

For example, `st:landau` opens PDF page 13 and links to the statement on Lean
lines 11–13 and the proof on lines 13–14. Looking up the same declaration in
`bindings` returns that passage and its Landau topic. A mark's `at` is a UTF-8
interval in `paper.txt`, the PDF word stream. A whole passage's `reference_ids`
also lists the individual ties inside its highlight. Those references use
`covered_by` to point back to the containing mark.

Curated sentence links can specify `focus_lines` and a `focus_note` on each
Lean target. The line index marks those links `reviewed_span`. Other links
carry a broader declaration or statement range. For a selected line, give
matching reviewed spans priority over the declaration's canonical address.
The PDF placement records whether the mark uses a unique section match, a
reviewed name in context, or the boundaries of a reviewed passage.
A passage's `compiled_edges`
lists direct type or proof dependencies checked against the pinned graph on
each build. For the sentence that applies the count identity, the two
recorded proof edges run through `CharacterBalanceMoves.core` before
`ch_balance`.

The build writes unresolved declaration names and ambiguous PDF placements to
`build/rh-paper-review.json`. A resolved pointer identifies where to look.
Statement fidelity remains unassessed until reviewed.

[rh-dependencies]: https://github.com/james-shore/rh-proof-dependencies/releases/tag/v0.2.1
[rh-paper]: https://github.com/vincitamore/riemann-lean-account

## Run a captured edition

Install the package with Python 3.11 or newer from the repository root, then
[assemble the authored papers](../papers/README.md#assemble-the-authored-bundle)
into an empty output directory. A validated bundle ZIP works too.

```sh
lean-exposition serve build/qaoa-sk-authored --port 8000
curl http://127.0.0.1:8000/api/v1
curl http://127.0.0.1:8000/api/v1/overview
```

The server prints its URL and manifest SHA-256 after validating the bundle.
Its default address is `127.0.0.1`. For a frontend on another local origin:

```sh
lean-exposition serve build/qaoa-sk-authored \
  --allow-origin http://localhost:5173
```

The command uses Python's reference WSGI server for local development. A host
can load the same callable with its production WSGI server:

```python
from pathlib import Path
from lean_exposition.web import create_app

application = create_app(Path("/srv/explanation-bundle"))
```

Mount the application at the origin root, preserving `/api/v1`. Put TLS,
authentication if needed, request concurrency/timeouts and rate limits in the
hosting server. The package adds no hosting dependency or account requirement.
CORS accepts one explicitly configured origin; it is not access control.
For that origin, a preflight permits an explicitly supplied `If-None-Match`
request header, so a browser client can revalidate its own saved ETag.
Serving does not rewrite the bundle's `publication: local_only` metadata or
publish it to an external service. Choose a bundle intended for that audience.

Construction captures and validates the eight contract files in memory.
Requests never reopen the bundle, so an edit or deletion on disk cannot mix
editions during a reading session. Reassemble and restart the application to
serve a new edition. This guarantees capture consistency, not that the captured
sources are the latest upstream versions.

## Response and edition contract

JSON success responses have `api_version`, `snapshot` and `data`. API version
`1.4` retains the `/api/v1` routes, default full representations and opt-in
summary, map and matches representations, keeps passage reading guidance and the
optional [Lean and alignment sidecars](#serve-the-lean-index-and-record-alignment),
and adds exact Lean lines to the alignment and the `/ties` routes.
JSON is compact UTF-8;
clients must parse fields rather than depend on whitespace or earlier ETags.
Exact document routes still return the original captured bytes. `snapshot`
includes the exact manifest and graph hashes, bundle identity and existing
corpus-view cache key. Errors replace `data` with an `error` containing `code`
and `message`. Original consumer projections remain inside `data`; their
versions, coverage and evidence qualifications are preserved.

Every resource accepts `manifest=<64 lowercase hex characters>`. A different
edition returns HTTP **409** (`edition_mismatch`); a malformed pin returns
**400**. Returned continuation and detail links include the pin. Record and
section refs are exact-edition identifiers, not paths: send them as URL-encoded
query values. In JavaScript, construct queries with `URLSearchParams`.

Successful GET responses include a body-hash `ETag`,
`X-Manifest-SHA256` and `Cache-Control: private, max-age=0, must-revalidate`.
`If-None-Match` supports revalidation, including weak tags, and returns **304**
without a body on a match. HEAD returns the GET headers and content length
without a body. OPTIONS advertises the read methods. Other methods return
**405**. Errors use JSON and `Cache-Control: no-store`.

Unknown paths return **404**; unknown, empty, malformed or duplicate scalar
parameters return **400**. Lists use repeated query keys, with distinct values
and at most 32 selections per key. Queries are limited to 8,192 bytes and 128
fields. A longer query returns **414**.

The same bounds apply to generated links. If a paged selection fits in the
request but its pinned continuation would not, the request returns **414**
(`generated_query_too_long`) instead of a broken `next` URL. The check reserves
space for every remaining page, including larger offsets. Narrow the query to
page that selection. Selections requiring offsets above 999,999,999 return
**400** (`pagination_out_of_range`).

An unusually long record, passage or section identifier can make an optional
detail or navigation link too long even in a valid captured edition. In that
case the link field is `null` and its sibling `<field>_unavailable_reason`
explains the limit. The edition still loads, the identifier remains exact, and
full record bodies remain available in paged `/records` or `/corpus` responses,
subject to the response-size limit.

## Choose a resource

All routes below start with `/api/v1`. The discovery response at that address
lists routes, query parameters, exact document hashes and configured limits.

| Resource | What it supplies |
| --- | --- |
| `/overview` | Corpus identity/scope, recorded node statuses, typed relation counts and three paper summaries |
| `/records` | Paged records or summary cards; filter by `table`, `kind`, `status`, `paper`, literal-token `q` or repeated exact `ref` |
| `/facets` | Record counts and available kind/status values, optionally restricted by `paper` |
| `/record?ref=…` | One exact record, adjacent typed links, support memberships and directly aligned paper passages |
| `/relations` | Paged links; repeated `family` filters and optional `paper` restriction |
| `/neighborhood?ref=…` | Existing typed traversal, witnesses, induced links, supplementary context and explicit frontier |
| `/connection?from=…&to=…` | One deterministic witness connecting two records within that bounded traversal |
| `/graph` | Dependency view or compact map, cycle components, condensation and scope-qualified assumption data |
| `/papers` | Reading-stage summaries, review states, coverage and links to each paper |
| `/papers/long` | Complete existing paper projection; `short` and `expository` work likewise |
| `/papers/long/structure` | Whole document graph: section and passage cards, reading/overlap links and correspondence to shared record refs |
| `/papers/long/document` | Exact captured Markdown bytes |
| `/papers/long/sections` | Paged heading outline with exact spans and refs |
| `/papers/long/passages` | Paged mapped passages with text, spans and authored mapping fields |
| `/papers/long/parts` | Paged document parts, including unmapped text, in original order |
| `/papers/query` | Paper correspondence by stage, passage, section, text selection or node; optional matches-only representation |
| `/papers/reading` | Explicit passage treatments, authored reading routes and separately labelled shared-claim alternatives |
| `/papers/resolve-link` | Resolve a source-relative companion href using explicitly configured authoring paths |
| `/compare?left=long&right=expository` | Paged union of two paper support sets, with shared/exclusive membership and direct passage mappings |
| `/search?q=curvature` | Paged literal-token search across records, heading titles and mapped passage text |
| `/corpus` | Complete existing corpus projection for a client that wants one capture |
| `/documents/graph.json` | Exact graph bytes; discovery lists the other seven allowlisted contract documents |
| `/lean/modules` | Lean revision, base link, toolchain, counts and modules by folder, without source |
| `/lean/names` | One compact row per Lean declaration: name, kind, module index, first and last line |
| `/lean/module?name=…` | One Lean module with its source and declarations |
| `/alignment` | Where each record is stated in Lean and in each paper, with exact Lean lines for each row and statement, the dictionary of Lean names, and the chain of names behind each step between Lean-linked records |
| `/ties/long` | One paper's marked statements, compact enough for first paint; `short` and `expository` work likewise |
| `/phrases/long` | Where a paper has phrase ties (`alignment/phrases-<paper>.json`): each part's AI-drafted declaration titles and reading notes. `/ties/<paper>` then lists one tie per phrase, with its topic, colour shade and every Lean row with its comparison (`same`, `stronger`, `weaker` or `different`); 404 for a paper without phrase ties |

The static reading edition also carries `/alignment/core`, `/alignment/long` (and `short`,
`expository`) and `/alignment/record?id=…`, so that a page can load part of `/alignment`, and
smaller startup forms of `/overview` and `/graph`. Those exist only there; this server answers
the routes above, and the site falls back to them.

Record tables are `nodes`, `edges`, `sources`, `citations` and `evidence`.
Relation families are `declarations`, `arguments`, `citations`, `platform` and
`provenance`. Paged resources accept `offset` (default 0) and `limit` (default 50,
maximum 200), returning `items`, `total`, `offset`, `limit` and a pinned `next`
URL or null. Ordering is deterministic within the captured edition. Paper lists
retain document order. A page beyond the end is empty.

`/search` additionally accepts `table` (including `sections` and `passages`)
and `paper`. It uses case-folded literal AND matching, with 1–16 tokens and
at most 256 characters. Results carry exact refs and detail/query links;
excerpts contain at most 280 characters around the first matching token and mark
truncation explicitly. `excerpt_start_character` and each entry in `matches`
use Unicode code-point offsets in the indexed text; these are neither browser
UTF-16 positions nor manuscript byte spans. Subtract the excerpt start to place
a visible match within the excerpt; some token matches may lie outside it.
Record text is indexed as serialized JSON; passage text is the captured content
and section text is its heading title. Search preserves case-folded matching,
including expansions such as `Straße` matching `STRASSE`.
Ordering is by table and exact ref, not a semantic relevance score. Unmapped
prose is readable through paper parts, but is not indexed as a mapped passage.
Each part includes its exact source `text`; concatenating all pages in order
recovers the captured Markdown, including passage markers and unmapped prose.

## Build a useful reading journey

Start with `/overview` to choose the corpus or one reading account. Enumerate
records and relations for the chosen scope; load full text and supporting
records only when needed. Paper support sets overlap and share the same record
refs. A paper summary retains its own selected goals and review state, so a
shorter account does not acquire the scope or review status of the long record.

For a small first load and expansion on selection:

1. Read `/overview` and retain its manifest pin for subsequent requests.
2. Read `/facets?paper=short` and
   `/records?paper=short&table=nodes&representation=summary`. Facets describe the
   chosen support set; they are counts, not a ranking of mathematical value.
3. Request `/graph?view=arguments&representation=map` for the selected goals,
   or add `node` selectors for a chosen focus. Use `scope=corpus` for the global
   map. Start a paper map from its `structure_href`; use paged `parts` for text.
4. Resolve a selection with `/record?ref=…`, or fetch several exact bodies with
   `/records?ref=…&ref=…`. Request related text through
   `/papers/query?node=…&relation=prerequisites&representation=matches`.

Summary cards contain `ref`, `table`, `label`, available `id`/`kind`/`status`, a
pinned detail `href`, and per-paper membership roles and direct passage counts.
Graph map cards omit the repeated paper memberships and URLs; their table is
the enclosing `records` key. Node cards retain an available Lean declaration
identity, and extraction cards retain their subject IDs. These fields let a
compact client preserve formal axiom and proof-hole occurrences when following
an authored theorem application. A map's pinned `records_href` accepts repeated
`ref` parameters to fetch exact bodies. All links, selected record refs, cycle
components, application bindings, assumptions and query scope are preserved.
The full representation is still available by omitting `representation`.

Batch record selection accepts at most 32 distinct refs and intersects other
filters. Any unknown ref returns 404. Results retain canonical record order,
not request order; join them by `ref`. Follow the normal page contract even
when requesting a batch. This supports overview cards, selected graph regions,
comparison panels and linked paper passages without fetching the whole corpus.

Select a record through `/record?ref=…`. `aligned_passages` contains the actual
mapped text and byte span in each paper, together with its mapping field and
mapping ref. `usage.paper_memberships` separately shows prerequisite-only
membership. A prerequisite can be relevant without a direct passage mapping.
Following `neighborhood_href` opens its source, evidence or argument context.
For a node, `lenses` links to its prerequisites, consumers, direct passages and
prerequisite uses. Aligned passages include a pinned `query_href` for that passage.

To compare two accounts, use `/compare`. Every overlap is backed by exact
record refs and direct passage mappings. Exclusive support membership does not
establish that the other prose never mentions the record. Shared sources do
not establish equivalent arguments or a proof relationship between papers.

For dependency or impact views, request `/graph?view=arguments&node=…` with
`direction=prerequisites` or `direction=consumers`. `assumptions=true` includes
explicit assumptions where supported. `scope=corpus` selects every recorded
node (declarations/assumptions only for the declaration view); it cannot be
combined with `node`. The default `scope=focus` retains the graph's selected
goals unless explicit nodes are supplied. Components preserve cycles and
condensation links retain their constituent relation refs; the graph is not
assumed to be a DAG. See the [graph-view contract](bundle-consumers.md) for the
distinction between stored edges and scoped theorem applications.

`/neighborhood` and `/connection` accept repeated `family`, optional `paper`,
`direction=incoming|outgoing|both` (default both), `depth` (default 1, maximum 8)
and `budget` (default 100, maximum 500 selected records). Neighborhoods accept
repeated `ref`; connections require exactly one `from` and `to`. Stored arrows
retain their original directions during incoming traversal. Connection outcomes
are `reached` or `not_reached_within_query`. The latter does not assert global
unreachability: inspect the original neighborhood frontier, query bounds and
paper restriction. A witness is one recorded route, not logical sufficiency.

## Serve the Lean index and record alignment

Two read-only sidecars can sit beside a captured edition:

```sh
lean-exposition serve build/qaoa-sk-authored \
  --lean-tree examples/qaoa-sk/upstream/lean \
  --alignment examples/qaoa-sk/alignment
```

`--lean-tree` takes a Lean tree or a JSON file from
`lean-exposition lean-index <tree> --out index.json`; `create_app(...)` takes the
same values as `lean_index=` and `alignment=`. Without them, these routes answer
**404**. Neither sidecar enters the bundle: `check-bundle`, the manifest hash and
every other response stay the same. Discovery's `sidecars` object records whether
each is available and its SHA-256, the hash of its canonical JSON. The `/ties` routes
are computed from the alignment and hashed under `sidecars.ties`.

The index is read from source text with no Lean toolchain, and covers every
module under `OAI/` and `ComparatorChallenges/`. Structure fields and constructors
are declarations of kind `def` named `Structure.field`, with `parent` set. An
anonymous instance has a stable synthetic name and `synthetic: true`. `uses` lists
indexed names found in a declaration's text, resolved through its namespaces,
`open`s and the module's imports; `used_by` is the reverse. Generalized field
notation resolves only when the last component is unique in the index, apart from
common names such as `add` or `le`. When a name exists in two modules, `uses_modules`
says which one a use means. `dependency_source: "source_text"` tells a reader that
these are reading aids: a name reached through notation, a tactic or elaboration is
absent, and a shadowed name can appear. `lean-index --extraction <report.json>` replaces both
lists with elaborated dependencies for the declarations a report covers and
records `dependency_source: "elaborated"` on each. Line links are
`<base_url><path>#L<a>-L<b>`.

A partial alignment directory is valid: `/alignment` covers the records authored so
far. When serving, a failing row is left out and listed in the application's
`alignment_errors`. `lean-exposition check-alignment <dir>` is strict and exits
nonzero on any failure. [Record alignment](record-alignment.md) owns the format,
the [tie index](record-alignment.md#the-tie-index), and
[what a reader may conclude](record-alignment.md#what-a-reader-may-conclude).
Neither sidecar checks that a Lean statement and a paper statement are equivalent: a
landed pointer says nothing about the mathematics, and `lines` makes it no stronger.

## Resolve a text selection

### Resolve captured companion links

The native bundle preserves exact manuscript bytes under `papers/{stage}.md`.
Their original relative links may refer to a different directory layout. Supply
that layout explicitly when serving a reading edition:

```sh
lean-exposition serve build/qaoa-sk-authored \
  --document-path long long/reasoning-record.md \
  --document-path short short/paper.md \
  --document-path expository expository/main.md
```

The equivalent Python option is
`create_app(bundle, document_paths={"long": "long/reasoning-record.md", "short": "short/paper.md", "expository": "expository/main.md"})`.
These are logical portable paths in a shared authoring namespace, not local
filesystem paths. Supply every stage exactly once with distinct normalized
relative POSIX paths. Absolute paths, parent components, backslashes, control
characters, query strings and fragments are not valid configuration values.
No files are opened through this map. The mapping is copied at construction;
changing the caller's dictionary cannot change the captured application.

Send `paper=short` and the original link value as `href` to
`/papers/resolve-link`, using `URLSearchParams` or equivalent encoding. For
example, `href=../long/reasoning-record.md#gap-elimination` resolves against
the configured short-paper base and matches the configured long-paper target.
The response reports the original href, `status`, `reason`, decoded `fragment`
and, when resolved, a `target` with stage, captured Markdown identity and pinned
`paper_href`, `document_href` and `structure_href`. Relative path normalization
does not authorize file access: only an exact declared target can resolve.

Discovery's `companion_resolution` object exposes the configured logical map,
its `config_sha256`, `configured` state and `resolver_version: 0.1.0`. Resolution
results retain this configuration identity. It is separate from the bundle's
manifest hash: the same captured papers can be hosted with different declared
authoring layouts. The map supplies a navigation interpretation, not new
mathematical evidence or a change to the eight-file bundle contract.

Without configuration, fragment-only links can resolve to the selected paper;
other relative destinations remain explicitly unresolved. Unknown companions
also remain unresolved. The resolver does not guess stages from filenames or
matching anchors, fetch external URLs, allow arbitrary file routes, or silently
discard local query strings. External and unsupported schemes are classified
without providing an executable navigation URL.

Resolution establishes the document identity only. The returned fragment is
unverified; renderer-specific heading IDs and explicit HTML anchors still need
to exist in the rendered document. A client must also sanitize Markdown and
link schemes. This route supplies the captured destination without rewriting
source bytes or claiming that a fragment points to a particular proof.

### Follow an explanation, a derivation or an answer

`/papers/reading` requires `paper=long|short|expository`. Select passages with
repeated `passage` anchors, `section` refs, or one pinned `start`/`end` byte
range, using the same selection rules as `/papers/query`. With no selectors,
it uses all mapped passages in the paper. Optional `target` restricts the
other endpoint to one reading stage. `offset` and `limit` page the links.

The response supplies `source_passage_refs`, compact `passage_cards` and
paged link `items`. Cards cover the source selection and this page's link
endpoints, carrying `stage`, `anchor`, exact content span, containing section,
direct `claim_refs`, evidence class and authored `treatments`. Each treatment
names a claim, one or more `kinds` and a rationale. Kinds are `statement`,
`derivation`, `explanation`, `application`, `illustration` and `reference`.
An empty treatment list means unspecified; do not infer roles from stage or
evidence class. `query_href` loads the passage's text and support through the
compact paper query; `reading_href` makes it the next navigation selection.
Both retain the edition pin. Cards omit prose and full graph records.

Links preserve two distinct bases:

| Link | Basis and direction |
| --- | --- |
| `expands` | Authored fuller treatment → the passage it expands |
| `illustrates` | Authored example → the passage it illustrates |
| `answers` | Authored answer → its question |
| `shared_claim` | Derived selected passage → a passage with intersecting direct claim IDs |

Authored links carry `derived: false`, `annotation_basis: authored_reading_link`,
both endpoint hashes, rationale and their mapping-file/index provenance.
Shared-claim links carry `derived: true`, `annotation_basis: shared_claim_ids`,
the shared claim refs, explicit treatments at both ends and both mapping refs.
They use other stages by default; an explicit `target` can select the same
stage. No prerequisites, citation similarity or semantic similarity enter
this matching rule. Sharing a claim does not mean providing the same argument.

`selection_relation` is `incoming`, `outgoing` or `internal` relative to the
source selection. Keep the stored `from` and `to`: selecting a question finds
an incoming answer link, and selecting a summary can find incoming expansions.
The response's `reading_view_version`, query, coverage and cache key identify
the projection. `coverage.query_truncated` is true when pagination omits part
of the link set; the source passage selection remains complete. The HTTP
`total`, `limit` and `next` describe the page.
Card order follows stage and source position. Link order is deterministic,
not a usefulness score. Pagination is applied during link construction, so
off-page shared-claim pairs do not allocate link bodies or endpoint cards.
Exact totals still require examining the selected passages' claim memberships;
pagination does not make that work constant-time. Invalid paging values are
rejected before this query work.

Three maintained-paper journeys exercise different information:

1. `/papers/reading?paper=expository&passage=density-and-approximation&target=short`
   starts at a further-reading pointer. Its treatment is `reference`; the
   `density-consequence` passage carries the short derivation. A shared-claim
   match and an authored expansion remain separate links. Density is a further
   consequence, not an extra premise of the scalar or circuit construction.
2. `/papers/reading?paper=expository&passage=changed-cases` finds the authored
   answer. The question has no claim selection; the answer selects the
   terminal-gap argument it reconstructs. The tilted-chord example is not
   labelled an instance of a theorem whose slope hypotheses it does not satisfy.
3. `/papers/reading?paper=expository&passage=curvature-transfer&target=long`
   offers the long calculation. Its treatment rationale distinguishes the
   analytic identity and certificate from the surrounding support argument.

Attach the manifest pin from `/overview` to these requests. Reading guidance
is optional artifact `1.2` metadata, checked against both endpoint texts when
the bundle is captured. Editing either endpoint invalidates its old link
binding. It does not validate the recommendation, certify a proof, discharge a
hypothesis or improve a paper's review state. Unknown annotations remain
unknown. The [authoring guide](authoring.md#describe-the-role-of-a-passage)
owns how these judgements are recorded and revised.

### Navigate the document before loading its prose

`/papers/{stage}/structure` returns a `document_structure` representation with
its own version. It retains document identity, review state, paper scope,
coverage, all sections, passage cards, unmapped segment spans and document
parts. It omits manuscript text, passage rationale and full graph record bodies.

`reading_order`, `outline_links` and `section_passage_links` are copied from the
existing paper projection. Containment and overlap remain separate: a passage
can cross headings and overlap sections other than its containing section.
`correspondence_links` joins passage refs to directly mapped claims, assumptions
and citations. `support_record_refs` also includes their recorded prerequisites;
it is not a direct mapping list. Document order and overlap are not proof edges.

A client can show the whole outline, select a section, highlight its overlapping
passages and shared graph records, then request the selected text. Append
`section=<section ref>` or `passage=<anchor>` to `resources.query_href`; it already
selects the paper, compact matches representation and manifest pin. Append
repeated `ref` values to `resources.records_href` for full record bodies, or one
`ref` to `resources.record_href` for evidence and aligned passages. All document
parts remain discoverable, including unmapped text. This intermediate structure
supports expansion at several levels without choosing a graph renderer or layout.
For artifact `1.2`, the structure also preserves authored passage treatments
and mapping-level reading links. `resources.reading_href` leads to the resolved
reading query; append the same passage or section selectors used for text.

### Query exact correspondence

`/papers/query` accepts `paper=long|short|expository`, repeated `passage`,
`section`, `node`, and `relation=direct|prerequisites`. Omit `paper` to search
node correspondence across all three accounts. Passage and section selectors
require one paper. Selectors are unions within a family and intersections
between families, as in the [consumer contract](bundle-consumers.md).

Add `representation=matches` to return `matches`, `support_boundary`, selected
`passages` and their `correspondence_links` without each full `view`. A
`document` object retains exact bundle identity, path, lengths, review state,
scope and whole-document coverage. Its coverage describes the source document,
not just the selected passages. The response identifies the representation as
`selected_passages` with its own `representation_version` and cache key.
Witnesses, selected source text and UTF-8 spans retain the full query semantics.

For a text highlight, send `paper`, `start` and `end` together with an explicit
`manifest` pin. Offsets are half-open **UTF-8 byte positions** in the exact
Markdown, not browser UTF-16 indices, rendered DOM positions or PDF coordinates.
For example, `TextEncoder` can convert a source-string prefix to its byte
length. Both offsets must be character boundaries. The response returns whole
mapped passages with non-whitespace overlap, while retaining the selected range
and its intersection semantics. A rendered reader must maintain its own map
back to these source positions.

## Boundaries for a client and host

The application prepares paper structure, record membership, graph relation
and traversal indexes, and search text once per captured edition. New graph
selections reuse the prepared edition even before an HTTP cache entry exists.
A bounded LRU stores successful
serialized responses and their ETags, shared by GET, HEAD and conditional GET.
Concurrent identical cache misses share a build when the result fits the cache;
errors and oversized entries are not retained. Edition validation still applies
to every request. Parameter names are normalized for cache lookup; repeated
selector order and explicit manifest presence remain part of the key.

Defaults are 32 MiB of cached body bytes and 128 entries per application. Set
`create_app(..., cache_bytes=..., cache_entries=...)` to tune these limits; zero
for either disables response caching. The byte limit counts cached bodies,
not Python object overhead, captured source bytes, prepared indexes or work in
flight. Multiple worker processes each have their own application and memory
budget. Preparation adds startup work in exchange for cheaper navigation.

The response limit is 16 MiB by default, configurable through
`create_app(..., max_response_bytes=...)`. A larger response returns **413**;
consumer fields are never silently cut. The selected-record budget does not
bound supplementary context or frontier size. Use paged records, relations,
sections and passages when a full projection is too large, and retain frontier
and application qualifications when displaying traversal results.

Only the captured eight files are accessible, with the two optional sidecars
above. Source and receipt locators are
returned as recorded data; the server does not follow them, browse a directory,
run Lean, fetch a URL, or serve arbitrary repository files. PDFs and other
companions are outside this bundle contract. A future PDF reader needs a
separately bound asset edition and a PDF-to-source coordinate map; Markdown
byte spans cannot supply PDF highlight positions.

Manuscript text, source URLs and labels remain untrusted content. A frontend
must escape labels, sanitise rendered Markdown and validate link schemes before
navigation. Exact Markdown preserves authored relative links; the frontend
must resolve supported bundle links deliberately rather than exposing a
filesystem. The bundle does not record the original authoring-directory layout.
Use the API's pinned reading and paper-query destinations for mapped navigation,
or the [configured companion resolver](#resolve-captured-companion-links) for
ordinary source-relative links. No layout coordinates,
graph renderer or visual styling is imposed
by this API. Hash consistency and graph reachability do not certify mathematics.

## Measure a real bundle

The repository's [benchmark runner](../scripts/benchmark_web.py) measures
application preparation, cold requests, warm repeats, conditional GET and body
sizes. With the package installed, run it on the assembled authored example:

```sh
python scripts/benchmark_web.py build/qaoa-sk-authored \
  --node support.positive_curvature --source support_tex_curvature \
  --repetitions 5 --out build/web-benchmark.json
```

Use recorded IDs from another bundle when measuring it. The report binds its
measurements to the manifest hash. It measures in-process WSGI work, not browser
rendering, network transfer or production load. Warm timings assume entries
remain in the configured cache; large responses may be evicted. Regression
tests check reuse, concurrency, bounds and semantic equivalence without fragile
timing thresholds.
