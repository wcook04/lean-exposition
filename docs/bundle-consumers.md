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

## The eight files

Bundle format `0.1.0`, with schema version `1.0`, contains exactly:

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

An application can consume these files without importing the CLI or agent skills.
Keep application-specific storage and presentation outside the eight-file
contract. A changed contract requires an explicit supported version; an extra
unrecognised ZIP member is not an extension mechanism. Platform intake belongs
before graph creation; see the [read-only Prove2Me adapter](prove2me.md).
