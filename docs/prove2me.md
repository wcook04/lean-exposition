# Read-only Prove2Me intake

`prove2me` turns a selected **public theorem** into a local evidence graph and
filtered metadata snapshots. It authenticates with an existing API key, reads the
theorem and its decomposition prerequisites, and records the platform environment.
It does not submit proofs, create accounts, comment, vote, upload, or publish.

```sh
lean-exposition prove2me https://prove2.me/theorems/e9f7d6cb-af95-435c-b432-ce5018f08276 --out build/prove2me
lean-exposition validate build/prove2me/graph.json
lean-exposition scaffold build/prove2me/graph.json --out build/prove2me-papers
```

The example is the platform's `OAI.ZeroTemperatureSK.full_support` target. Its
upstream source reference is preserved as a link; it does not imply the platform
target and the upstream corpus have identical Lean environments or proof bodies.
The separate [QAOA / SK example](../examples/qaoa-sk/README.md) contains pinned,
licensed upstream sources. No automatic equivalence between these intakes is asserted.

Supply `PROVE2ME_API_KEY` through your environment, or pass
`--credentials "$PROVE2ME_CREDENTIALS"` with the path of an existing JSON file
containing an `api_key` string. Keep that file outside this repository and the
output directory, with owner-only permissions. The adapter reads it without
modifying it. Keys, access tokens, credential paths and authentication response
bodies are never written to the graph or snapshots. The only POST exchanges the
existing API key at the documented `/agent/refresh` authentication endpoint.

The adapter is reviewed against Prove2Me API documentation version **0.13.2**.
A different authentication version stops intake before any metadata fetch.
Recheck the official documentation before updating that version boundary:
[setup](https://prove2.me/references/setup.md),
[discovery](https://prove2.me/references/discover.md),
[decompositions](https://prove2.me/references/prove.md), and
[missions](https://prove2.me/references/missions.md).
Those documents also describe write operations; this adapter does not implement them.

## What the files mean

The empty output directory receives `graph.json` and `snapshots/*.json` only after
collection and graph validation succeed. Snapshots contain selected factual fields:
public IDs, declaration names, status, visibility, Mathlib revision, deprecation
flags, safe HTTPS source references, decomposition groups and matching toolchains.
They exclude proof/definition bodies, natural-language statements, comments,
audits, account metadata and unrelated environment rows.

Deprecation is `true` for a reported timestamp, `false` for an explicit null,
and `null` when the field was omitted. Invalid timestamp values stop intake.
New graphs also retain these observations in the platform evidence receipt's
`platform_deprecation`: `entities` bind flags to node and source IDs; `groups`
bind each submission, its flag, public child IDs and omitted-child count to the
decomposition snapshot. The same child can occur in both current and deprecated
groups. Older graphs may lack this receipt field; absence means unknown.

Each snapshot's source record binds its retained bytes with SHA-256 and observation
time. The platform observation receipt separately records the SHA-256 of the raw
response read in memory. A filtered snapshot cannot reproduce the raw response
hash; these are deliberately separate provenance claims. Authentication responses
are not included in either provenance list.

Keep the intake directory when retaining an exported paper bundle. The existing
`scaffold` and `export` commands package the graph and paper files; they do not
copy source snapshot files into that bundle.

Every node keeps its platform UUID and explicit `visibility: public`. Its local
status is `unverified`, even when the platform says `Proved`. Definitions use
platform status `not_reported`, because their detail endpoint has no theorem
status. A platform observation receipt passing means metadata intake succeeded;
it does not mean a proof passed.

Edges point from the consuming theorem to its prerequisite and have kind
`platform_decomposition`. They come from `/theorems/UUID/decompositions`, not from
the direction of arrows in the website's graph. Alternative submission groups
remain in the filtered snapshots and new graph receipts; their union provides
navigation and must not be read as one conjunctive proof obligation. A null
submission ID is preserved as an unattributed prerequisite group. Deprecation
belongs to the individual observation or group, not to a union edge.
The normal argument closure excludes these edges; platform closure is separate.

## Boundaries and omissions

Defaults are 100 attempted entities, depth 10 and a 30-second per-request timeout.
`--max-nodes` accepts 1–200, `--max-depth` 0–10, and `--timeout` up to 60 seconds.
Requests are bounded, each response is limited to 2 MB, and all response bytes
together to 20 MB. All requests use the fixed HTTPS API origin with redirects
disabled, including credential-bearing requests.

Every theorem and definition is checked individually for explicit public visibility
before any of its metadata is retained. Missing, private or visibility-unknown
children are excluded, with an omission count; their IDs and names are not exported.
The selected root must be public or the command fails without writing output.

The resulting platform closure is always **partial**. Depth and node limits are
reported; definition dependencies and proof-body dependencies are not expanded;
hidden platform relations remain unknown. An empty decomposition response does
not establish complete formal dependencies or a complete assumption audit. No
capped graph overview is presented as complete. Lean extraction, local replay,
Comparator and assumption audit remain `not_run`.

The intake does not download accepted proof source: public visibility alone does
not establish redistribution rights, and platform licensing/attribution needs a
separate selected-source contract. Metadata sources therefore remain
`reference_only` with licence `NOASSERTION`. Mission URLs, mission listings,
submission listings and theorem-to-mission navigation are not currently imported;
select the mission's public goal theorem URL instead.

For a paper handoff, use the existing [bundle and review convention](bundle-consumers.md#identify-a-revision-before-requesting-review).
This adapter does not provide a paper-upload or review-history API. A future
platform integration would need its own documented artifact-version, attachment
and feedback contract. A mission discussion or theorem status must not be
silently reinterpreted as review of a particular paper edition.

The Python wrapper interface is
`intake_prove2me(url, out, credentials=None, max_nodes=100, max_depth=10, timeout=30.0)`
with the options after `out` passed as keywords. It returns a small JSON-compatible
report. `Prove2MeError` is a `ContractError` with a safe-to-display message.
