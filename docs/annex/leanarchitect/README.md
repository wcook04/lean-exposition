# LeanArchitect source study

This selection preserves eight unmodified files from
[LeanArchitect](https://github.com/hanwenzhu/LeanArchitect/tree/9f3bb53916b9d6fa05b7777389e1844f82b1c9a6),
revision `9f3bb53916b9d6fa05b7777389e1844f82b1c9a6`, for reading alongside
the [evidence graph contracts](../../contracts.md). The upstream project and its
contributors supply these files under [Apache-2.0](LICENSE). Original paths and
file contents are retained. The [reference record](../../references.json) owns
their source URLs and SHA-256 hashes.

The selection contains `Architect/Basic.lean`, `Architect/CollectUsed.lean`,
`Architect/Content.lean`, `Architect/Attribute.lean`, `Architect/Output.lean`,
`lakefile.lean`, `lean-toolchain` and `LICENSE`. Its toolchain file records
`leanprover/lean4:v4.35.0`. This is a source-study selection, not a runnable
installation: it omits other imported modules and dependencies. The
lean-exposition runtime does not import these files. No upstream build or test
run is claimed by this study.

## What the implementation establishes

The five selected Lean modules and Lake configuration were read to trace how
annotations, dependency collection and export interact. These observations
support the following design decisions in lean-exposition.

| Source and mechanism | Consequence for our graph and writing stages |
| --- | --- |
| [CollectUsed.lean](Architect/CollectUsed.lean): `CollectUsed.collect` traverses helpers, stopping at other tagged blueprint nodes and axioms. `collectUsed` makes statement and proof sets disjoint except for `sorryAx`. | This is a compressed dependency view over selected nodes. Preserve raw direct type, value and structural edges separately; a display convention must not erase an occurrence in both a type and a proof. |
| [Basic.lean](Architect/Basic.lean): `NodePart` stores additions and exclusions; several Lean names may share one LaTeX label. [Output.lean](Architect/Output.lean): `NodePart.inferUses` combines inferred and authored uses, applies exclusions and converts names to labels. | Keep declaration identity and observed edges separate from authored presentation choices. A manuscript label is not a unique declaration ID. |
| [Attribute.lean](Architect/Attribute.lean): `mkStatementPart` and `mkProofPart` store configured dependency arrays. [Output.lean](Architect/Output.lean): `NodeWithPos.toJson` serializes the stored parts; `moduleToJson` does not invoke `Node.inferUses`. | The JSON facet exports metadata. Consuming it as a fully inferred dependency graph would require an additional, explicit extraction step. |
| [Output.lean](Architect/Output.lean): `NodePart.inferUses` derives `leanOk` from the absence of `sorryAx` in the combined, filtered uses. | A presentation flag has its own scope. Preserve separate source bindings, build receipts, axiom evidence and mathematical review rather than converting it into a general correctness result. |
| [lakefile.lean](lakefile.lean): module facets wait for Lean artifacts and pass module options to the exporter. [Content.lean](Architect/Content.lean): content is sorted by declaration position. | Keep export tied to its compilation environment. Source order helps navigation; the long record, short paper and exposition still need deliberately chosen argument and teaching order. |

These are architecture and authoring decisions drawn from the pinned
implementation. The study does not establish the quality of a generated paper
or a reader's understanding; those require inspection of the authored artifact.
