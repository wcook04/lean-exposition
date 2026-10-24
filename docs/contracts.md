# Contracts and architecture

The package has one local command interface and one evidence graph. `cli.py`
coordinates operations; `intake.py` acquires locked public bytes; `verification.py`
invokes Lean tools; `extraction.py` translates their report; `contracts.py` checks
shape and references; `bundle.py` packages the result; `consumer.py` projects
read-only graph and paper views from those validated records. The optional `prove2me.py`
adapter reads public platform metadata into that same graph. Agent skills describe how to
write from the evidence. Runtime code does not load those instructions.

The schemas are packaged under
[`src/lean_exposition/resources/schemas/`](../src/lean_exposition/resources/schemas/).
Graph version `1.0` remains supported; version `1.1` adds the Lean declaration
kind and safety fields for new extraction. Artifact version `1.0` and bundle format `0.1.0`
are unchanged. Unknown schema
fields fail validation. A consumer should reject unsupported versions rather than
silently guessing new semantics.
The eight-file bundle can therefore contain either a graph `1.0` or graph `1.1`
while its manifest and paper mappings remain at schema `1.0` and its bundle
format stays `0.1.0`. The independent example reader accepts that matrix as a
transport check; its `full_contract_validation` remains false. A previous
reader with a strict graph `1.0` gate should reject graph `1.1` explicitly.

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

The research checkout, source distribution, installed wheel and explanation
bundle serve different purposes. The checkout carries authored papers and
source history; the source distribution is an installable Python package
source archive; the wheel supplies runtime code and packaged schemas, templates
and Lean helper; the eight-file bundle exchanges one selected authored result.
Offline execution means dependencies and the selected toolchain are already
installed. A bundle reader can inspect its captured files offline without the
original source or receipt paths; that does not rerun Lean or certify the paper.

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
prerequisites of the selected result.

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
remain explicitly unestablished. See the [receipt field contract](verification.md#reading-a-new-comparator-process-receipt).
The extraction projection also binds its completeness state and each declaration's
inspection boundary. Regenerate the receipt after changing those fields.

Lean axiom discovery and theorem hypotheses have different representations. Transitive
axioms are explicit assumption nodes. Quantified hypotheses remain in the recorded
Lean type; the author must explain their meaning. Imported dependencies outside the
selected module scope remain boundary nodes. `sorryAx` is an unresolved obligation.
A partial extraction or an empty uninspected assumption list must not be advertised
as a complete assumption audit.

Source hashes bind bytes, not meaning. Public URLs identify references, not permissions.
The source lock distinguishes exact fetched bytes from explicitly modified configuration.
`audit-sources` checks both. `fetch` materializes only recorded source URLs and inline
derived configurations into an empty destination; it never executes fetched code.

## Papers and bundles

`scaffold` creates three empty documents and mapping records. Every mapping binds the
exact graph and document hashes, selected goals, claims, citations, assumptions,
unresolved obligations, passage correspondence and authoring/review state.
The [authoring guide](authoring.md) describes how a writer fills those records.

Short and expository papers may focus on a smaller argument, but they retain the
selected goals and all assumptions, citations and unresolved obligations that affect
that selection. Passage-level bindings preserve the local dependencies too. Review
notes describe work actually performed; a schema check cannot confer expert acceptance.

A local bundle contains `graph.json`, three Markdown/JSON paper pairs and
`manifest.json`. The manifest records the exact exported file set and hashes. Export
captures that fixed set, validates the captured bytes, then writes a ZIP of those bytes.
Unknown files and symlinks are not included. Sources can remain external references;
the eight-file bundle contains neither the source corpus nor external receipt files.
Relative source paths refer to the original intake or project root; their hashes
identify those bytes. The bundle does not silently redistribute every cited work.

The versioned bundle can be hosted or attached by a future consumer. The current core
has no publication call or server. A platform adapter belongs at the intake boundary
and must preserve platform IDs and the distinction between platform and local evidence.
An artifact attachment API requires its own documented contract and authorization.
