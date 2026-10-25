# Serve the graph and papers

The web backend serves one assembled explanation bundle through a read-only,
versioned JSON API. It supplies the shared corpus, paper subgraphs, exact text,
passage correspondences and navigation witnesses. A client can build a graph
explorer, a paper reader or an agent tool against the same data. This package
does not supply a frontend.

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
Serving does not rewrite the bundle's `publication: local_only` metadata or
publish it to an external service. Choose a bundle intended for that audience.

Construction captures and validates the eight contract files in memory.
Requests never reopen the bundle, so an edit or deletion on disk cannot mix
editions during a reading session. Reassemble and restart the application to
serve a new edition. This guarantees capture consistency, not that the captured
sources are the latest upstream versions.

## Response and edition contract

JSON success responses have `api_version`, `snapshot` and `data`. API version
`1.2` retains the `/api/v1` routes, default full representations and opt-in
summary, map and matches representations, and adds passage reading guidance.
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
the enclosing `records` key. A map's pinned `records_href` accepts repeated
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
   answer while both teaching passages retain empty claim selections. The
   tilted-chord example is not labelled an instance of a theorem whose slope
   hypotheses it does not satisfy.
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

Only the captured eight files are accessible. Source and receipt locators are
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
