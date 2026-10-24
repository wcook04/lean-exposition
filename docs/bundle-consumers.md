# Consuming explanation bundles

A bundle is a local, versioned exchange format for an application that wants to
inspect a selected mathematical goal, its evidence and its paper records. It is
ordinary JSON and UTF-8 Markdown in a directory or ZIP. No service is required.

The [independent example](../examples/consumer/README.md) reads an exported ZIP
with Python's standard library. The installed package additionally validates the
graph and passage contracts.

## Select and inspect

```sh
lean-exposition inspect examples/qaoa-sk/evidence-graph.json
lean-exposition inspect examples/qaoa-sk/evidence-graph.json --goal scalar_value
lean-exposition select examples/qaoa-sk/evidence-graph.json --goal scalar_value --out build/selected.json
lean-exposition scaffold build/selected.json --out build/selected
lean-exposition export build/selected --out build/selected.zip
lean-exposition inspect-bundle build/selected.zip
```

`inspect` changes only the displayed selection. `select` writes a new graph and
retains every node, typed edge and evidence record. Any existing node ID can be
selected, including a formal declaration. `inspect-bundle` validates one captured
set of bytes and inspects that same capture. It accepts either the directory or
its ZIP and does not extract the archive.

The graph view exposes labels, exact recorded statements, selected IDs, assumptions,
unresolved nodes, citations, sources and every evidence record. Nodes carry
`selected`, `in_argument_closure` and `in_platform_closure` flags. Evidence carries
`relevant_to_argument` and `relevant_to_platform` flags, derived from subjects and
explicit node/edge references. These flags identify relationships to the selected
node sets; they never change the evidence's kind or status. An unrelated failed
check stays visible with its original scope.

Read `kind`, `status`, `subject_ids`, `source_ids` and `details` together. A passing
source hash, Lean build, Comparator invocation or platform observation answers a
different question. `not_run`, `unavailable` and `failed` remain separate outcomes.
An empty failed-evidence list does not imply that checks ran. Argument closure and
platform closure have distinct [edge semantics](contracts.md#graph).

## Follow one kind of relationship

For a focused view of the same recorded graph, choose a relation and a root:

```sh
lean-exposition inspect examples/minimal/evidence-graph.json --view declarations --goal Minimal.result
lean-exposition inspect examples/qaoa-sk/evidence-graph.json --view arguments --goal full_support --include-assumptions
lean-exposition inspect examples/qaoa-sk/evidence-graph.json --view arguments --goal assumptions.full_support_minimizer --direction consumers --include-assumptions
lean-exposition inspect examples/qaoa-sk/evidence-graph.json --view citations --goal full_support
lean-exposition inspect examples/qaoa-sk/evidence-graph.json --view provenance --goal lean.full_support
```

The five views are `declarations`, `arguments`, `citations`, `platform` and
`provenance`. Declaration views follow elaborated Lean relationships; choose a
formal declaration explicitly as the root. Argument views follow curated
support and formalisation correspondence; they do not also traverse Lean
expression edges. Explicit assumptions are an opt-in traversal in these two views.
Citation views retain attribution without turning cited assumptions into proof
premises. Platform decomposition remains its own relation. Provenance views
connect records through their stored source and evidence references.

Each returned link retains its original `from` and `to`, its exact `kind`, and a
`semantic_class`. Stored graph edges have `derived: false` and `record_ref`;
links projected from record fields have `derived: true`, `owner_ref` and
`source_field`. `traversal.recorded_from_to` confirms that a reverse query changes
reachability only, while `orientation_by_kind` and `relation_semantics` state the
meaning and source of each kind. In particular:

| Kind | Returned `from → to` means |
| --- | --- |
| `lean_type_dependency` | Declaration → constant in its elaborated type |
| `lean_value_dependency` | Declaration → constant in its elaborated value or proof |
| `lean_structural_dependency` | Declaration → structural inductive, constructor or recursor reference |
| `supports` | Curated claim → recorded ingredient; mathematical sufficiency is not certified |
| `formalizes` | Informal goal or claim → selected formal declaration; correspondence, not implication |
| `cites` | Citing node → referenced node; attribution, not a premise |
| `platform_decomposition` | Platform item → reported child; not a Lean expression edge |
| `assumption_ids` | Node → explicitly named assumption, projected from its field |

Provenance links point from the field-owning record to the named record:
`source_id`/`source_ids` → source, `evidence_ids` → evidence, `citation_ids` →
citation, `subject_ids` → subject node, and graph-edge fields `from`/`to` →
their original endpoint nodes. These field links are navigation references,
not argument edges. The output's kind-specific orientation map distinguishes
them even when a view contains no link of a particular kind.

`--direction consumers` follows reverse recorded relationships while retaining
their original consumer-to-prerequisite orientation in the output. It is available
for declaration, argument and platform views. This can help find affected passages,
but a partial graph cannot establish a complete change-impact analysis.

View format `0.1.0` binds record handles to the exact graph bytes. Cycles are
retained as strongly connected components; the component graph is acyclic without
pretending the original relations are. The view preserves statuses and reports
its completeness limits. It is a read-only projection, not a replacement graph,
proof checker or interactive viewer. An empty traversal means no relation was
recorded, not that the declarations are independent.
`relation_scope: recorded_relation_reachability` means SCCs are calculated over
that view's returned links only. A provenance node–evidence–subject cycle is a
cycle of references, not of proofs. Components list their internal link IDs and
kinds; condensation links list both contributing IDs and kinds, so aggregation
does not hide the original relation types.

## The eight files

Bundle format `0.1.0` contains exactly:

```text
manifest.json
graph.json
papers/long.md
papers/long.json
papers/short.md
papers/short.json
papers/expository.md
papers/expository.json
```

The manifest and paper mappings use schema `1.0`. The graph may use `1.0` or
`1.1`; graph `1.1` carries the declaration safety fields bound by version 2
extraction. Historical `1.0` graphs keep their original evidence and its limits.
An older consumer that supports graph `1.0` alone must reject `1.1` explicitly.

The manifest names the graph and three paper stages, with SHA-256 hashes of the
other seven files. Each paper mapping binds its exact Markdown bytes and exact
graph bytes, selected goals, passages, claims, assumptions, citations and unresolved
obligations. The manifest is not self-hashed; `inspect-bundle` reports its hash and
`export` reports the SHA-256 of the complete ZIP. A hash establishes byte identity,
not the identity of an author or the truth of a statement.

The source corpus and external receipt files are not members of this format.
Their URLs, pins and hashes remain in `graph.json`. Relative source and receipt
paths refer to the original intake or Lean project root, not the bundle directory.
The inspector lists these under `external_resources` with `included: false`.
Consumers must obtain those bytes separately before claiming to have checked them.
Embedded receipt records remain available in the graph.

Reject unsupported schema or bundle versions. Reject duplicate JSON keys, duplicate
archive members, missing or extra archive files, links and hash mismatches. The
package reader accepts stored and deflated ZIP entries, with limits of 32 MiB per
member, 64 MiB of expanded content, and 65 MiB for the archive. It never follows
paths from ZIP metadata to write files. Directory reads capture only the fixed
eight files; unrelated directory files are not exported.

Exported ZIPs use stored entries, a fixed timestamp and fixed Unix file metadata.
Identical captured bytes produce identical exports without depending on a
compression-library version. Existing destinations are not overwritten.

## Python interface

```python
from pathlib import Path
from lean_exposition.bundle import load_bundle
from lean_exposition.consumer import inspect_bundle, inspect_graph
from lean_exposition.contracts import read_json

graph = read_json(Path("examples/qaoa-sk/evidence-graph.json"))
view = inspect_graph(graph, goals=["scalar_value"])
payload = load_bundle(Path("build/selected.zip"))  # dict[str, bytes]
bundle_view = inspect_bundle(Path("build/selected.zip"))
```

`load_bundle` returns the exact validated eight-file capture. `inspect_graph`
returns the graph validation summary plus the readable records described above.
`inspect_bundle` returns:

| Field | Meaning |
| --- | --- |
| `schema_version`, `bundle_version`, `bundle_id` | Contract and graph identity |
| `status`, `publication` | Paper-derived bundle state and local bundle designation |
| `manifest_sha256`, `files` | Hash of the manifest capture and its seven file records |
| `contract_valid` | All package structural and cross-record checks passed |
| `graph` | Complete inspection view, including selection and evidence |
| `papers` | Three complete mapping records with their mapping paths |
| `external_resources` | Source and external receipt records, explicitly not included |
| `semantic_certification` | Always `false`; structural checks do not certify mathematics |

Paper `state` and `review_state` are separate. A scaffold is empty, an authored
document has correspondence records, and a review state reports a distinct review
step. A consumer should display those states without upgrading them because ZIP
or schema validation passed. Full contract validation also does not authenticate
the reported checks or replace mathematical or reader review.

## View one paper as a graph

Each authored paper already has its own passage mapping. The paper view joins
that mapping to the exact Markdown and evidence graph in a validated bundle:

```sh
lean-exposition inspect-bundle build/qaoa-sk-authored --paper short
lean-exposition inspect-bundle build/qaoa-sk-authored --paper short --passage main-result
```

The Python entry is `project_paper(bundle_path, stage, passages=None)` in
`lean_exposition.consumer`. A stage is `long`, `short` or `expository`; the
optional passage list selects explicit anchors from that paper. A directory
and a ZIP containing the same eight files give the same view. Invalid or stale
paper mappings fail the existing bundle checks before projection.

The view has two connected parts. Its document structure identifies sections
and passages, their text and locations, and their order in the actual Markdown.
Its support subgraph follows the selected passages' recorded claims,
assumptions and citations to the relevant declarations, sources and checks.
Containment and reading order are document relations; they are never used as
proof dependencies. The mathematical relations retain their existing kinds
and statuses. A platform observation remains separate from a Lean dependency.

Snapshot references and the exact manifest, graph, text and mapping hashes let
a consumer join these parts without inventing another graph authority. The
same graph record has the same graph reference in different paper views of
that snapshot. A passage reference identifies its paper edition; it is not a
promise of unchanged meaning across revisions. Text locations address UTF-8
Markdown bytes and lines, not coordinates in a rendered PDF.

The outline recognises ATX Markdown headings and excludes fenced code and YAML
front matter; it does not parse Setext or HTML headings. Containment links keep
their literal meaning. Separate section–passage overlap links expose exact
nonempty text intersections when a passage contains subheadings or crosses a
section boundary. These navigation links add no mathematical support claim.

Every paper-view link retains a `kind` and `semantic_class`. Document links are
derived from exact Markdown bytes and carry its `source_ref`: `next_in_text`
orders the start positions of headings and passage markers, `subsection` runs
parent section → child section, `contains_passage` runs an enclosing section →
the full passage marker block, and `text_overlap` runs section → passage with
the exact nonempty `overlap_span` of their text intervals. A passage can have
several overlap links, including ancestors, without acquiring several claims.
All these document links have `derived: true`; none enters argument reachability.

`correspondence_links` run selected passage → mapped graph record. `maps_claim`
comes from the mapping's `claim_ids` (which can name a declaration),
`maps_citation` from `citation_ids`, and `maps_assumption` from
`assumption_ids`. Each link names the exact mapping `source_ref`, anchor and
field. These correspondences do not certify a sentence or create a graph edge.

The graph part calls its selected relation set `argument_links`: stored Lean
references, curated `supports`, curated `formalizes`, and node-field
`assumption_ids`, each retaining its own kind, class and stored-edge or field
origin. `relation_scope: recorded_argument_relation_reachability` applies to
its SCCs and condensation, not to proof correctness. Condensation entries
expose `link_kinds` alongside `link_ids`. `provenance_links` separately connect
the field-owning node, citation, evidence or edge record to named sources,
citations, evidence, subjects or edge endpoints. These are field-derived
references with owner and field metadata; they never enter the argument SCC.

A front end can therefore open a passage from the graph, show its local support,
or find other passages referring to the same claim. It can switch between the
short, long and expository accounts while retaining the common evidence
references. It need not duplicate the evidence graph or interpret reading order
as logical implication.

The output identifies text outside mapped passages and the scope of a selected
view. Unmapped text is still part of the document; it has no inferred claim or
verification link. Selecting one passage does not remove the rest from the
bundle. The view reports recorded correspondence, not complete mathematical
dependence, sentence-level formal verification or reader acceptance. No website
or additional persistent bundle member is required for this API.

## Query sections and find passages across papers

The optional query entry point joins the existing three passage maps to one validated bundle capture:

```python
from pathlib import Path
from lean_exposition.consumer import query_papers

# All passages whose mappings directly name this node.
answer = query_papers(Path("build/qaoa-sk-authored"), node_ids=["support.full_relative_support"])

# Passages whose mapped claims or assumptions reach this recorded prerequisite.
answer = query_papers(
    Path("build/qaoa-sk-authored"),
    node_ids=["assumptions.full_support_minimizer"],
    relation="prerequisites",
)
```

The corresponding command is:

```sh
lean-exposition query-papers build/qaoa-sk-authored --node support.full_relative_support
lean-exposition query-papers build/qaoa-sk-authored --paper short --passage gap-proof
lean-exposition query-papers build/qaoa-sk-authored --node assumptions.full_support_minimizer --relation prerequisites
```

`query_papers(bundle_path, *, stage=None, passages=None, section_refs=None, node_ids=None, relation="direct", expected_manifest_sha256=None)` uses the same bundle, graph, text and mappings as `project_paper`. It adds no persistent index. Omitting `stage` searches all three stages. Passage and section selectors require one explicit stage. Values within a selector family are alternatives; different supplied selector families are intersected. An explicitly empty list selects nothing, while an omitted selector adds no filter.

Use a section's exact `ref` from the returned outline with `section_refs=[ref]` or `--section REF`. Titles can repeat, and offsets can move after edits. Unknown or stale references fail; the API does not guess a replacement. A section matches every passage with a content-span overlap containing non-whitespace text; a blank line before a heading does not select the next passage. The returned passage keeps its full mapping and prerequisites; `section_overlaps` identifies the exact intersection, and `whole_passage_extends_beyond_selected_sections` exposes a passage crossing the chosen boundary. This prevents a paragraph selection from silently dropping conditions elsewhere in its mapped passage.

The default `direct` node relation matches explicitly mapped `claim_ids` and `assumption_ids`. The `prerequisites` relation additionally follows the existing argument relation families and explicit assumptions. Its shortest typed witness paths explain why a passage matched. Citation, platform, reading-order and containment links do not become argument steps. A zero-length path is a direct match; `root_mapping_field` distinguishes a mapped claim from a mapped assumption. A path is recorded reachability, not a certificate that its premises suffice.

Each returned paper includes a `view` with the established paper-view shape, a list of matching passages, and a `support_boundary`. The latter distinguishes mapped roots from retained prerequisites, reports required assumptions and unresolved nodes, preserves node boundary text, and names graph records outside the selected closure. A node “not mapped as a claim” is not necessarily absent from the prose. The map does not support that stronger conclusion. Empty matches mean no matching recorded correspondence, while unrecorded dependencies and unmarked text remain unknown.

### Keep caches and bookmarks attached to the right edition

For a review of an independently retained edition, supply its expected manifest digest with `expected_manifest_sha256` or `--expect-manifest`. The guard accepts exactly 64 lowercase hexadecimal characters and rejects a different validated capture before returning a query. It does not fetch a replacement or infer the expected edition from the input being checked. The guard is not a selector and need not enter the cache key because the snapshot already binds the edition.

`paper_query_version`, `snapshot`, the normalized query and `cache_key` identify the result's contract and inputs. Cache by these values, not the filesystem path, paper title or modification time. Namespace an application's cache by its implementation build too, and change the public query version if output semantics change. A valid ZIP re-encoding can retain the same payloads and query result while having a different archive digest.

The existing graph references remain shared across paper views of the same graph snapshot. A section reference identifies exact Markdown bytes. A passage reference also incorporates its mapping identity, so a mapping-only change is visible even if the prose is identical. Logical bookmarks such as a stage and anchor can help locate a successor, but cannot migrate a prior review or its evidence classification automatically.

The spans are half-open UTF-8 byte intervals, with one-based line ranges for navigation. They are neither PDF coordinates nor browser character offsets. In particular, W3C Web Annotation `TextPositionSelector` counts normalized Unicode code points; a future adapter must convert deliberately or use byte-coordinate semantics. A rendition requires its own identity and a tested mapping to source coordinates. [Web Annotation Data Model, §§4.2.4–4.2.6 and 4.3](https://www.w3.org/TR/2017/REC-annotation-model-20170223/#selectors).

Recompute a query after any manifest change. A text-only edit can move section offsets; a mapping-only edit can change the correspondence; a graph-only edit can change support, source identity or evidence. Source records still name external bytes: this query does not open them, and source access remains explicitly false in the view. A query cache is disposable presentation data. The graph and mappings remain its owners.

### A source-grounded example

After assembling the maintained QAOA/SK drafts, inspect the short paper's
curvature and gap arguments:

```sh
lean-exposition query-papers build/qaoa-sk-authored --paper short --passage curvature
lean-exposition query-papers build/qaoa-sk-authored --paper short --passage gap-proof
lean-exposition query-papers build/qaoa-sk-authored --node support.positive_curvature
lean-exposition query-papers build/qaoa-sk-authored --node support.positive_curvature --relation prerequisites
```

The `support.*`, `scalar.*` and `circuit.*` records describe distinct source
arguments in the same graph. Their source locators and edge evidence explain
what each ingredient supplies. All authored claims remain unverified; none is
an elaborated dependency extraction or an accepted semantic review.

A direct curvature query finds passages that name the ingredient in their map.
The prerequisite query also finds consumers such as gap exclusion. Curvature
has an admissibility and plateau guard, without a minimizer hypothesis; contact
and gap exclusion quantify over admissible minimizers. The positive and zero
plateau cases remain separate. Finite rational algebra, analytic signs, zero
boundary flux and approximation have their own records.

The scalar clauses distinguish supplied-diffusion hypotheses from the Parisi
identity that constructs its diffusion internally. The circuit primary and
positive-temperature routes remain separately selectable: the alternative uses
citation navigation so traversal does not silently conjoin their hypotheses.
Scoped existence and application steps are stated explicitly because this
backend does not discharge hypotheses or bind mathematical witnesses.

## Assemble authored papers

Keep `scaffold` for new empty documents. To assemble completed or in-progress
paper records, supply the graph file and exactly one Markdown/mapping pair for
each stage:

```text
lean-exposition assemble GRAPH --long LONG_MD LONG_JSON --short SHORT_MD SHORT_JSON --expository EXPOSITORY_MD EXPOSITORY_JSON --out DIRECTORY
```

The equivalent Python entry is
`assemble_bundle(graph_path, stage_pairs, out)`, where `stage_pairs` maps `long`,
`short` and `expository` to `(markdown_path, mapping_path)` tuples. It captures the
original bytes, checks every mapping against the supplied graph and Markdown, and
then writes the fixed bundle layout. Mapping paths must already be the canonical
`papers/STAGE.md` paths inside the resulting bundle. The assembler never rewrites
hashes or repairs stale bindings. Correct the authoring records at their source
before retrying. See the [authoring guide](authoring.md) for passage bindings.
The [QAOA paper guide](../papers/README.md#assemble-the-authored-bundle) gives the
complete command for the three maintained authored drafts.

### Paper links after assembly

Read each manuscript from its exported location, `papers/STAGE.md`, when checking
links. A checkout-relative link such as `../long/reasoning-record.md` can work in
the source tree and fail in the bundle. Assembly preserves that text; successful
hash validation does not establish that its hyperlinks resolve.

For documents authored together in the bundle layout, a sibling link such as
`long.md#gap-elimination` can point to an explicit anchor in `papers/long.md`.
When source documents use a different layout, use an exact companion title and
section reference in the prose, and keep checkout navigation in their README.
Use pinned public URLs for cited sources that are outside the bundle. Supporting
scripts and bibliographies outside the eight files need explicit companion
locators; a relative link does not include them in the export.

Make these editorial changes before updating document and passage hashes. The
assembler does not rewrite links or rebind reviewed passages. Check both the
source reader path and the exported reader path after changes.

## Extension boundary

### Identify a revision before requesting review

Keep three identities separate: `bundle_id` names the continuing work,
`bundle_version` names its format, and `manifest_sha256` identifies one exact
captured revision. Preserve the original manifest bytes; reformatting its JSON
changes that last identity. The ZIP digest identifies the delivered archive.
Re-encoding an otherwise identical archive can change its ZIP digest without
changing its manifest or payloads.

Retain the expected manifest digest independently and compare it with the
validated capture. Internal consistency alone cannot tell you whether a valid
successor is the edition a reviewer was asked to read. A download location helps
retrieve the edition but does not guarantee its identity or continued availability.

Keep the request and response beside the bundle, outside its fixed eight files.
Name the exact question, paper path, content and mapping hashes, selected goals
and intended coverage. For a passage, retain its anchor and `text_sha256` too.
A PDF or HTML rendition requires its own digest and locator; the Markdown hash
neither identifies its rendered bytes nor verifies its appearance. Record which
external sources were actually accessible and opened.

Feedback remains attached to the edition and question actually assessed. Preserve
the original response, the author's disposition and any later reviewer confirmation
as separate records. A corrected paper creates a successor; it does not make the
reviewer an assessor of that successor. Even unchanged prose can have a changed
mapping rationale, assumption, source or evidence classification that needs review.
Refreshing hashes cannot carry acceptance forward automatically.

Store a review outside the artifact it assesses. If feedback on edition A leads
to edition B, record the adoption decision after B exists and name both digests.
This avoids making a bundle contain a claim about its own future hash. Preserve
old responses and corrections against a retained previous checkpoint. Hashes can
detect changes relative to that checkpoint; they do not authenticate a reviewer.
The [bounded reader-review guide](reader-review.md) gives a practical first session.

An application can consume these files without importing the CLI or agent skills.
Keep application-specific storage and presentation outside the eight-file
contract. A changed contract requires an explicit supported version; an extra
unrecognised ZIP member is not an extension mechanism. Platform intake belongs
before graph creation; see the [read-only Prove2Me adapter](prove2me.md).
