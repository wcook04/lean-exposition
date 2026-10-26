# Contracts and architecture

The package has one local command interface and one evidence graph. `cli.py`
coordinates operations; `intake.py` acquires locked public bytes; `verification.py`
invokes Lean tools; `extraction.py` translates their report; `contracts.py` checks
shape and references; `bundle.py` packages the result; `consumer.py` projects
read-only graph and paper views from those validated records. The optional `prove2me.py`
adapter reads public platform metadata into that same graph. Agent skills describe how to
write from the evidence. Runtime code does not load those instructions.

`web.py` transports these consumer views through a read-only WSGI API. It uses
`bundle.py::BundleCapture` to validate and freeze one directory or ZIP edition
at application construction. Existing consumers accept that capture wherever
they accept a bundle path. `load_bundle(capture)` returns a fresh dictionary
of immutable bytes; no query reopens the original filesystem. HTTP discovery,
pagination, literal search and paper-overlap views belong to the transport;
mathematical traversal and correspondence remain in `consumer.py`. No second
stored graph or renderer-specific layout is introduced. The [web API guide](web-api.md)
owns routes, limits, deployment and client responsibilities.

Optional web `document_paths` configuration records a portable authoring
namespace for the three captured papers. The transport resolves relative
companion hrefs only against this explicit map and exposes its own digest,
separate from the manifest. It never infers source paths, rewrites stored prose
or opens arbitrary files. Document resolution does not verify rendered
fragment anchors. The bundle format and mathematical mappings are unchanged.

`consumer.py::ConsumerSession` prepares private edition indexes once and returns
detached projections for concurrent readers. It shares the standalone consumer
algorithms and retains their default result contracts. Compact paper queries
have a separate representation version and cache key. The transport owns its
bounded cache of serialized response bytes, summary cards and map records;
these omit detail explicitly without changing stored graph relationships or
the scope of a theorem application. Its prepared reading index resolves explicit
passage treatments, authored reading links and exact shared-claim alternatives.
Reading guidance never changes proof traversal, evidence or review status.

The schemas are packaged under
[`src/lean_exposition/resources/schemas/`](../src/lean_exposition/resources/schemas/).
JSON decoding rejects duplicate keys, non-finite numbers and unpaired Unicode
surrogates in keys or values; valid escaped surrogate pairs remain supported.
Graph version `1.0` remains supported; version `1.1` adds the Lean declaration
kind and safety fields for new extraction. Artifact `1.0` retains its original
rule that each paper selects exactly the graph's selected goals. Artifact `1.1`
allows each paper to select its own nonempty set of existing graph nodes. This
may include a node outside the graph's default focus. Artifact `1.2` retains
that rule and permits optional passage treatments and hash-bound reading links.
All versions require
an authored paper to cover its own selected goals and retain the assumptions,
citations and unresolved obligations of all its claims and explicit assumptions.
Unknown fields and unsupported versions fail validation.

The eight-file bundle format remains `0.1.0`, with manifest schema `1.0`.
Its graph and each paper mapping independently declare schema `1.0`, `1.1` or `1.2`.
The independent example reader supports this matrix for transport checks;
its `full_contract_validation` remains false: in particular, it does not validate
treatments or reading-link references and hashes. Older readers must reject versions
they do not support rather than silently applying the old goal rule.

The raw Lean extraction report has its own version. New runs emit version `2`,
which records `is_unsafe` and `is_partial` for each in-scope declaration. Their
graph translation uses the `lean-extraction-v2` projection profile. That digest
binds the Lean declaration kind, safety flags and displayed locator alongside the previously bound
formal fields. Lean can store `partial def` or its recursive auxiliary as an
opaque constant whose `ConstantInfo.isPartial` is false; an opaque declaration records
`is_partial: null` (unknown), rather than a misleading `false`. The graph
validator also rejects an opaque declaration labelled `false`, even if its
projection digest is recomputed. A passed build
promotes only declarations explicitly classified as neither unsafe nor partial
and without `sorryAx`. The build receipt remains
visible for the other declarations. Direct translation can still read a version
`1` raw report, but the live extractor requires version `2`. Translating legacy
data cannot create a new `kernel_checked` status because its
safety classification is unknown. Already retained version `1` graphs validate
under their original projection profile; validation of that historical binding
does not add the missing safety or locator assurance. Do not rehash an old graph
under the new profile as though its extractor had emitted new fields.

The derived `formal_result_assurance` reports recorded safety separately from
current authoring eligibility. Current eligibility also requires a matching
passed build observation, the extraction request and driver hashes, valid
matching stdout hashes, and the retained report-to-stdout binding. An older or
incomplete receipt remains readable but does not become current by losing
fields. These observations are not authenticated execution or mathematical
acceptance. Strict authoring validation can require this current eligibility;
historical bundle reads do not rewrite older evidence.

The research checkout, source distribution, installed wheel and explanation
bundle serve different purposes. The checkout carries authored papers and
source history; the source distribution is an installable Python package
source archive; the wheel supplies runtime code and packaged schemas, templates
and Lean helper; the eight-file bundle exchanges one selected authored result.
Offline execution means dependencies and the selected toolchain are already
installed. A bundle reader can inspect its captured files offline without the
original source or receipt paths; that does not rerun Lean or certify the paper.

## Documentation and rendering boundaries

[AGENTS.md](../AGENTS.md) routes an agent's work;
[CONTRIBUTING.md](../CONTRIBUTING.md) owns setup and validation;
[the consumer guide](bundle-consumers.md) owns runnable navigation and API details.
[The architectural companion](../papers/architecture/paper.md) explains the
human reading relationships. Keep commands, schemas and run histories in these
technical owners rather than duplicating them in the companion.

The graph stores shared records; paper mappings bind each account to them.
Corpus and paper projections are derived views, not additional stored sources
of truth. Markdown owns authored prose; neither graph traversal nor a template
generates its reasoning. Optional writing skills guide authors and agents but
are not imported by the runtime or required for installation.

The companion PDF is a reading rendition outside the bundle. Its optional
`portable-local-links` rendering policy removes local file actions while
retaining descriptive reference text, internal links and public URLs.
It changes no graph, mapping or bundle contract. See the
[reading-copy link policy](bundle-consumers.md#distribute-reading-copies-with-working-links).

## Graph

A graph names selected goals and retains source, citation, node, typed-edge and
verification records. IDs are stable within the graph; source revision and hashes
identify the actual edition. API snapshots need observation time and response hashes
in their provenance, not a fabricated upstream Git revision.

Every dependency edge points **from the consumer to its prerequisite**. The
`closure` operation follows that direction. It uses a visited set, so mutually
recursive or structural declarations do not cause an infinite traversal.

| Edge | Meaning |
| --- | --- |
| `lean_type_dependency` | Constant appears in an elaborated declaration type |
| `lean_value_dependency` | Constant appears in the declaration's elaborated value/proof |
| `lean_structural_dependency` | Inductive/constructor/recursor structural reference |
| `platform_decomposition` | Relation reported by a platform; not a Lean expression edge |
| `formalizes` | Curated correspondence from an informal goal to its selected formal statement |
| `supports` | Curated argument relation from a claim to an ingredient |
| `cites` | Reference relationship; not logical entailment |

The default argument closure follows Lean, formalization and support edges plus
explicit assumptions. Platform closure is reported separately. Curated edges require
mathematical interpretation; neither their direction nor the existence of a path
certifies an argument.

Citation requirements follow a separate reference closure through `cites` edges.
This retains attribution without importing a cited work's assumptions as logical
prerequisites of the selected result. The documentary seeds include premise
records named by traversed applications even when those premises are supplied.

Graph `1.2` can annotate a `supports` edge with one authored theorem application.
The edge still points from conclusion to conditional theorem. Its `application`
records shared parameter/witness bindings, premise-to-supplier bindings, remaining
free assumptions, a source span and a rationale. Each supplier also needs an
ordinary support edge from the conclusion. The conditional proof stays reachable;
only its supplied premise occurrences are discharged in this application.
An independent use of that premise, or a supplier that still requires it, remains
free. Queries retain the bindings; they do not check their mathematical meaning.
An extracted Lean axiom dependency or `sorryAx` remains an obligation of its
retained declaration even if an authored binding names the same node. A binding
does not change the Lean proof term. Older `remaining_assumption_ids` values may
reflect the earlier scoping rule; they remain authored records, while queries
recompute effective requirements and must not treat the field as a complete
formal dependency audit.

The format supports one application layer. Nested applications and cycles through
an application consumer are rejected; ordinary dependency cycles still work.
Bindings have status `authored`, never `kernel_checked`. Reference and scope checks
cannot establish witness equality, source-span truth or logical sufficiency.
Graphs `1.0` and `1.1` remain supported without application annotations. Directly
selecting a conditional theorem still exposes its own free assumptions.

`select` changes the selected IDs while preserving the whole graph. That keeps failed
checks and adjacent unresolved claims inspectable. It does not convert the platform's
capped overview into a complete dependency closure. An exported graph can be partial
if excluded dependencies and missing bodies remain explicit.

## Evidence and assumptions

Nodes identify goals, formal declarations, assumptions or claims. Statuses distinguish
unverified, kernel-checked, conditional, open, external and axiom records. A checked
formal declaration must identify its statement, source and matching successful build
receipt. An English claim cannot gain this status through a platform label.

Receipts distinguish source hashes, builds, extraction, Comparator, platform observations
and semantic review. Each names its subjects, sources, tool, command, outcome and scope.
A failed or unavailable check is retained. A successful process exit alone cannot make
its result a broader equivalence or correctness claim.

Extraction receipts bind the report with `report_sha256`, its formal declaration
projection with `projection_sha256`, and the project bytes with `source_hashes`.
`source_changed` records drift during a tool run. Exported graph evidence retains
output hashes rather than raw process diagnostics. These bindings detect changed or
inconsistent evidence; they do not authenticate who ran a check.
The current adapter also records an extraction request and packaged-template
digest. Before translating a raw report, it compares the complete current
source inventory with the recorded one. Repeated roots remain in the raw
request, while the graph selection lists each declaration once.
The shared process-receipt validator rejects contradictory success/process
statuses and invalid UTF-8 stdout for successful extraction. When valid UTF-8
is recorded, raw-byte hashes must agree with retained text or its normalized
digest. During raw-report translation, retained diagnostic text remains the
authority for legacy text hashes; new byte hashes are never rewritten to make
them agree. Direct graph ingestion validates its supplied text/hash pairs.
Legacy receipts may omit the additive fields; their absence supplies no new
execution evidence.
New Comparator process receipts retain configuration scope and before/after
configuration and first-launch-executable observations. Their `process_status`
is separate from an input-binding failure. The `comparator-process-v2` receipt
profile is an additive process record, not a graph-schema revision or a new
proof-verdict format; effective nested checker, cache and sandbox identities
remain explicitly unestablished. Passing v2 receipts must have internally
consistent process, configuration and first-launch observations; failed or
legacy receipts preserve their distinct outcomes. A passing legacy receipt
without the v2 profile is a historical process claim, not evidence of current
v2 input checks or an authenticated Comparator verdict; removing v2 fields
cannot add those observations. See the [receipt field contract](verification.md#reading-a-new-comparator-process-receipt).
The extraction projection also binds its completeness state and each declaration's
inspection boundary. Regenerate the receipt after changing those fields.

Lean axiom discovery and theorem hypotheses have different representations. Transitive
axioms are explicit assumption nodes. Quantified hypotheses remain in the recorded
Lean type; the author must explain their meaning. Imported dependencies outside the
selected module scope remain boundary nodes. `sorryAx` is an unresolved obligation.
A partial extraction or an empty uninspected assumption list must not be advertised
as a complete assumption audit. A `kernel_checked` label is rejected when a
recorded Lean type/value dependency path or extracted axiom inventory reaches
`sorryAx`; structural edges do not by themselves establish that dependency.

Source hashes bind bytes, not meaning. Public URLs identify references, not permissions.
The source lock distinguishes exact fetched bytes from explicitly modified configuration.
`audit-sources` checks both. `fetch` materializes only recorded source URLs and inline
derived configurations into an empty destination; it never executes fetched code.
Fetch accepts HTTPS source URLs and checks each redirect before following it. It
rejects credentials, queries, fragments, localhost and non-public IP literals;
hostname DNS and proxies are not verified or pinned. Treat source locks and
hostname resolution as trusted inputs, not an SSRF boundary. Byte hashes establish
equality to the lock, not meaning or source authenticity.

## Papers and bundles

`scaffold` creates three empty documents and mapping records. Every mapping binds the
exact graph and document hashes, selected goals, claims, citations, assumptions,
unresolved obligations, passage correspondence and authoring/review state.
The [authoring guide](authoring.md) describes how a writer fills those records.

Short and expository papers may focus on a smaller argument, but they retain the
paper-selected goals and all assumptions, citations and unresolved obligations
that affect their claims. Explicitly mapped assumptions also seed these checks,
including their own prerequisites and citation requirements. Every authored
passage must contain non-whitespace text. Passage-level bindings preserve the
local dependencies too. Historical mappings remain readable under their original
citation rule, and query views expose any missing current documentary credit.
Strict new-authoring checks require current credit at document and passage level. Review
notes describe work actually performed; a schema check cannot confer expert acceptance.

A local bundle contains `graph.json`, three Markdown/JSON paper pairs and
`manifest.json`. The manifest records the exact exported file set and hashes. Export
captures that fixed set, validates the captured bytes, then writes a ZIP of those bytes.
Unknown files and symlinks are not included. Sources can remain external references;
the eight-file bundle contains neither the source corpus nor external receipt files.
Relative source paths refer to the original intake or project root; their hashes
identify those bytes. The bundle does not silently redistribute every cited work.

The versioned bundle can be hosted or attached by a consumer. The optional web
transport serves a captured edition locally; it has no publication call.
A platform adapter belongs at the intake boundary
and must preserve platform IDs and the distinction between platform and local evidence.
An artifact attachment API requires its own documented contract and authorization.

## Corpus and paper projections

`consumer.project_corpus` derives one complete record pool from one validated
bundle capture. Paper views refer into that pool; `record_usage` provides the
reverse lookup. A paper's declared focus, mapped claims, prerequisites and
associated evidence are different relationships. Shared record membership adds
no implication between papers. All disconnected and unselected records remain
in the pool, including outside subjects named by relevant evidence.

Each link retains its kind and origin. Declaration, curated argument, citation,
platform and provenance relations have separate collections. Document order and
passage correspondence remain in the paper views. Cycles are permitted; existing
node-root views expose strongly connected components without pretending that all
relations form a proof DAG. Exact graph bytes qualify record references; mapping
bytes and passage selection qualify paper subgraphs. Manifest hashes pin the
whole edition. These indexes are derived on demand and add no persisted graph,
frontend or formal acceptance claim. See the
[consumer contract](bundle-consumers.md#view-the-whole-recorded-corpus).

`query_corpus` uses this same captured pool for bounded, typed neighbourhoods
rooted at any record class. Traversal selects records; the induced relation set
keeps all eligible links between them. Deterministic witness parents explain
selection without replacing those links. Incoming traversal retains the stored
direction. A paper filter uses recorded support membership and cannot silently
expand through an outside evidence subject. Explicit frontier reasons distinguish
the paper boundary, depth cutoff and selected-record budget. Supplementary link
owners and boundary endpoints are separate from the selected graph; the record
budget is not a total response-size guarantee.

Paper query `0.4.1` also resolves half-open UTF-8 byte ranges against an explicitly
pinned edition. It selects whole mapped passages on non-whitespace content
overlap and preserves their complete requirements. It does not infer mappings
for unannotated prose or translate PDF, browser or formal-source coordinates.
These are read-only query contracts, not new graph evidence or persisted formats.
The paper query and graph views use application scopes for prerequisite traversal.
The whole-corpus relation pool also retains the original assumption references:
it is a documentary index, not a flat list of free proof obligations. Do not
recompute free assumptions by ignoring the application annotations.

## Passage treatments and reading links

Artifact `1.2` adds optional `treatments` to each passage. Each entry names one
of that passage's existing `claim_ids`, one or more treatment kinds and an
authored rationale. Kinds are `statement`, `derivation`, `explanation`,
`application`, `illustration` and `reference`. A claim can have several roles;
an absent annotation means unspecified. No role is inferred from paper stage,
evidence class, shared claims or prose. A `derivation` label records the author's
description of the passage; it does not certify the argument.

Optional mapping-level `reading_links` connect a local `from_anchor` to a
`to_stage` and `to_anchor`. `expands` points from a fuller treatment to the
passage it expands; `illustrates` from an example to the passage it illustrates;
`answers` from an answer to its question. Both endpoints carry the exact
passage `text_sha256`, and each link has an authored rationale. Local validation
checks the source; bundle validation resolves the target in the other captured
mappings, including links to a later stage. Unknown references, stale hashes
and duplicate links fail. Artifact `1.0` and `1.1` reject these new fields.
The [authoring contract](authoring.md#describe-the-role-of-a-passage) gives the
field names and revision procedure.

`consumer.query_reading` is a separate, versioned navigation projection. It
returns selected passage cards, incident authored links and derived
`shared_claim` links based solely on intersecting direct `claim_ids`. These
two bases remain labelled and separate. Reading links can connect passages
with no mapped claims, such as an exercise and its answer. They neither add
proof edges nor discharge hypotheses. Mapping-file references retain the
authorship provenance; the captured manifest pins the complete selection.
