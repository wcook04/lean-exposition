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

JSON success responses have `api_version`, `snapshot` and `data`. `snapshot`
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
| `/records` | Paged records; filter by `table`, `kind`, `status`, `paper` or literal-token `q` |
| `/record?ref=…` | One exact record, adjacent typed links, support memberships and directly aligned paper passages |
| `/relations` | Paged links; repeated `family` filters and optional `paper` restriction |
| `/neighborhood?ref=…` | Existing typed traversal, witnesses, induced links, supplementary context and explicit frontier |
| `/connection?from=…&to=…` | One deterministic witness connecting two records within that bounded traversal |
| `/graph` | Existing dependency view, cycle components, condensation and scope-qualified assumption data |
| `/papers` | Reading-stage summaries, review states, coverage and links to each paper |
| `/papers/long` | Complete existing paper projection; `short` and `expository` work likewise |
| `/papers/long/document` | Exact captured Markdown bytes |
| `/papers/long/sections` | Paged heading outline with exact spans and refs |
| `/papers/long/passages` | Paged mapped passages with text, spans and authored mapping fields |
| `/papers/long/parts` | Paged document parts, including unmapped text, in original order |
| `/papers/query` | Existing paper correspondence query by stage, passage, section, text selection or node |
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
excerpts contain at most 280 characters and mark truncation explicitly.
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

`/papers/query` accepts `paper=long|short|expository`, repeated `passage`,
`section`, `node`, and `relation=direct|prerequisites`. Omit `paper` to search
node correspondence across all three accounts. Passage and section selectors
require one paper. Selectors are unions within a family and intersections
between families, as in the [consumer contract](bundle-consumers.md).

For a text highlight, send `paper`, `start` and `end` together with an explicit
`manifest` pin. Offsets are half-open **UTF-8 byte positions** in the exact
Markdown, not browser UTF-16 indices, rendered DOM positions or PDF coordinates.
For example, `TextEncoder` can convert a source-string prefix to its byte
length. Both offsets must be character boundaries. The response returns whole
mapped passages with non-whitespace overlap, while retaining the selected range
and its intersection semantics. A rendered reader must maintain its own map
back to these source positions.

## Boundaries for a client and host

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
filesystem. No layout coordinates, graph renderer or visual styling is imposed
by this API. Hash consistency and graph reachability do not certify mathematics.
