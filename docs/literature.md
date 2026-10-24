# Sources and implementation choices

Lean Exposition starts with a small exporter over compiled Lean declarations. It records evidence for authors and reviewers; it does not turn proof acceptance into approval of an English claim. Sources were retrieved on 23 October 2026, with scholarly software credits checked on 24 October. [references.json](references.json) records immutable source pins, selected-file hashes, license evidence, and the disposition of each reference.

The papers credit Lean through de Moura and Ullrich's [2021 system
description](https://doi.org/10.1007/978-3-030-79876-5_37), and mathlib through
[The mathlib Community's 2020 library paper](https://doi.org/10.1145/3372885.3373824).
These explain the software's design and contribution; they do not identify
the exact software edition or certify a target proof. The source lock and
execution receipts retain the actual toolchain and dependency pins. Full
reading copies of these two papers remain in the private annex; the public
repository retains bibliographic metadata and links.

## Extract evidence before drafting prose

Lean already exposes the relevant building blocks: declaration types, declaration bodies, `Expr.getUsedConstants`, and axiom collection. Its [axiom collector](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Util/CollectAxioms.lean) walks types and bodies, handles the different declaration forms, and uses a visited cache. This supports a small exporter that runs under the source project's own pinned toolchain.

[LeanArchitect](https://github.com/hanwenzhu/LeanArchitect/tree/9f3bb53916b9d6fa05b7777389e1844f82b1c9a6)
is the closest implementation reference. The
[selected source study](annex/leanarchitect/README.md) traces its collector,
annotations and output paths. The collector traverses helpers until a tagged
node or axiom, then subtracts statement dependencies from proof dependencies
except for `sorryAx`. Its LaTeX path combines inferred and authored uses and
applies exclusions. Its JSON facet instead serializes stored node metadata;
that path does not invoke dependency inference. These are different views.
The later [LeanArchitect ITP 2026 paper](https://doi.org/10.4230/LIPIcs.ITP.2026.25)
credits Thomas Zhu, Pietro Monticone, Sean Welleck and Jeremy Avigad for the
published design. Its article, archived software artifact and the selected
implementation commit are separate editions; the commit remains the evidence
for the JSON-path observation here.
The exporter here preserves direct type, value and structural references as
separate edge categories, with toolchain identity. Authored presentation choices
must not silently replace those observations.

Compiled dependencies describe the implementation that was inspected. They do not establish that every edge is mathematically necessary, that absent edges prove independence, or that every prerequisite appears in the reader's argument. Keep direct references, transitive closure, and an author's exposition dependencies distinguishable. A local check for `sorry` in a proof body also differs from checking the axioms of its dependency closure.

## Reuse documentation boundaries selectively

[doc-gen4's JSON schema](https://github.com/leanprover/doc-gen4/blob/0e1ffe2e4ba5ecfdfaf15c65b8d3805dbb7134ae/DocGen4/Output/ToJson.lean) provides a compact model for names, declaration kinds, documentation, source links, line locations, and module imports. Its declaration index is useful navigation evidence; it is not a theorem dependency graph or a semantic review. Keep source locations tied to a commit. The project recommends a separate documentation build and versions matched to Lean, so installing its full renderer is unnecessary for the initial exporter.

[Verso](https://github.com/leanprover/verso/tree/304b8561790c50222551c937ce02928df0d5b445) supplies extensible, Lean-aware document authoring and proof-state annotations. [Verso Blueprint](https://github.com/leanprover/verso-blueprint/tree/4932a7e3b283dd763f546e949ece88c3aed58a5a) is a richer optional consumer: it keeps original-source provenance, informal content, and formal declarations separate, and distinguishes statement and proof dependencies. Its [public integration documentation](https://github.com/leanprover/verso-blueprint/blob/4932a7e3b283dd763f546e949ece88c3aed58a5a/doc/API.md) explicitly requires clients to pin a version; APIs and generated data may change. Its CLI query JSON is not a public compatibility contract. These are reference designs, not runtime dependencies.

[leanblueprint](https://github.com/PatrickMassot/leanblueprint/tree/56e066d30fb7b608a63f4241fee80982d7eae3ef) remains a useful LaTeX/plasTeX publication adapter with established project examples. A blueprint can exist before formal statements or proofs. Preserve author-declared planning edges instead of silently replacing them with extracted proof references.

## Natural language needs a separate review

[Hattori, Matsuzaki and Fujiwara, INLG 2025](https://aclanthology.org/2025.inlg-main.23/) combine premise explanations, tactic templates, proof-state extraction, and recursive summarization along the proof structure. This is a useful drafting recipe. Their study used 17 textbook proofs and 21 supporting lemmas, with manual step evaluation by the first author; its reported 86% key-point coverage does not establish reliable exposition of arbitrary research mathematics. The [companion implementation](https://github.com/hattori-matsuzakilab/AutoInformalizationWithTemplate/tree/b140d32223f48e06ab210c346d76a9928cf37e09) is retained as a link only because a repository-wide license was not found.

A generated explanation must retain its source links and review status. Human review must check the hypotheses, definitions, quantifiers, conclusion, omitted cases, and whether each prose step follows. Readability review is another judgment. Neither can be inherited from compilation, an axiom report, or a proof checker.

## Comparator has a version and platform boundary

The [standalone Comparator repository](https://github.com/leanprover/comparator/blob/865edc14486c3388e9225daa971da8e157488c3e/README.md) is deprecated following integration into Lean 4.35.0. Current integration should follow [Lake's challenge and checker interface](https://lean-lang.org/doc/reference/4.35.0/Build-Tools-and-Distribution/Lake/) and record the exact toolchain, trusted challenge, solution, permitted axioms, checker configuration, exit status, and output. The core sandbox uses Linux facilities. A portable exporter should report checker availability instead of assuming every host can run that sandbox.

The [Lean validation guide](https://lean-lang.org/doc/reference/4.35.0/ValidatingProofs/) distinguishes proof validity from statement meaning. Comparator checks a solution against a trusted formal challenge; it does not certify that the challenge expresses an English theorem or that a manuscript explains its proof.

The extractor's structural traversal adaptation uses
[Comparator/Util.lean at `d03acab`](https://github.com/leanprover/comparator/blob/d03acab154d269c06e60e4de7e4cc85deebff94b/Comparator/Util.lean),
with Lean FRO, LLC and Henrik Böving attribution retained in its source header.
That Apache-2.0 input has its own pinned record in the annex. The later README
pin above documents migration; it is not the adaptation's acquisition revision.

## Collaborative formalization and source handoff

[Chen, Marwaha, Lu, Yuen and Peng, Prove2Me (arXiv:2608.28433v2)](https://arxiv.org/abs/2608.28433v2) describe immutable theorem statements separate from proof submissions, with pinned Lean environments and optional source links (§3). A mission captain audits the goal, definitions and selected milestones for fidelity to the source; a separate agent translates Lean statements back into ordinary mathematics for human comparison (§3.3). Sorry-free proof-sketches may depend on open child theorems and resolve when those children receive proofs (§4.2); source-linked milestones give contributors a shared target (§4.4). This is a useful model for keeping statement meaning, dependency closure and human judgment distinct. The paper’s mission results are case studies, not a controlled comparison, and its cost columns use different conventions (§5).

The [local Prove2Me intake](prove2me.md) reads public theorem metadata and decomposition links. The paper does not specify a generic versioned-paper attachment, external evidence manifest or scoped-feedback contract for that adapter. It therefore informs the design of a future source handoff without establishing a current submission channel or independent review of this repository. The exact v2 PDF and version record are retained only in the private source annex; this public checkout records their hashes and selected reading in [references.json](references.json).

## A small reference annex

### QAOA and the SK model

The following primary sources locate the mathematical inputs and the scope of
the motivating question. The annex records the exact inspected editions,
statement locators, PDF hashes and rights decisions. The QAOA example's two
formal interfaces remain separate from the broader circuit-energy argument.

| Reference | Use and boundary |
| --- | --- |
| [Basso, Farhi, Marwaha, Villalonga and Zhou, TQC 2022](https://doi.org/10.4230/LIPIcs.TQC.2022.7) | Section 4, Theorem 1 relates fixed-depth SK performance to the large-degree graph expression. Section 5, equation (5.2) conjectures eventual Parisi optimality. Preserve the thermodynamic-first order and distinguish the theorem from the conjecture; the proceedings sends the theorem's proof to the [full arXiv:2110.14206v3](https://arxiv.org/abs/2110.14206v3), §6. A separate 23 October reading inspected that section, not every auxiliary proof. |
| [Farhi, Goldstone, Gutmann and Zhou, Quantum 2022](https://doi.org/10.22331/q-2022-07-07-759) | Section 4 gives fixed-depth energy-moment limits and concentration at fixed angles. These results provide context for circuit energies at infinite system size; they do not establish optimality as depth grows. |
| [Montanari, Optimization of the Sherrington–Kirkpatrick Hamiltonian](https://arxiv.org/abs/1812.10897v2) | In the inspected 2019 preprint, Assumption 1 and Theorem 2 give a conditional classical comparison. The support hypothesis concerns all sufficiently large finite inverse temperatures; zero-temperature full support alone does not discharge it. Remark 1.2 specifies the oracle operations included in the computation model. |
| [Auffinger and Chen, Parisi formula for the ground state energy](https://arxiv.org/abs/1606.05335v2) | Theorem 1 identifies the limiting ground-state energy with a zero-temperature variational infimum. The proof of Lemma 3 constructs an attaining coefficient when combined with the upper bound. Cite that argument when choosing a minimizer; neither result supplies full support or QAOA convergence. |
| [Auffinger, Chen and Zeng, Infinite Step Replica Symmetry Breaking](https://arxiv.org/abs/1703.06872v2) | Theorem 1 gives infinitely many support points. Remark 1 explicitly separates that conclusion from interval support. Infinite support and full relative support on `[0,1)` are different claims. |
| [Boulebnane and coauthors, arXiv:2609.40309v1](https://arxiv.org/abs/2609.40309v1) | Corollary S3.1 states an explicit finite-size mean-energy threshold for a fixed QAOA word in its mixed-spin model. This 30 September 2026 source postdates the OpenAI manuscript's displayed 25 September date. Its statement and model were inspected; its full cavity and majorisation proof was not independently checked. It does not give an efficient choice of depth or angles, or a measurement-tail rate. |

The two QAOA publisher editions carry CC-BY-4.0 and are retained unmodified in
the [selected source readings](annex/README.md), with attribution, licence and
original notes on their applied use. The inspected Basso full preprint and the
three earlier SK preprints use arXiv's non-exclusive distribution licence,
which grants rights to arXiv rather than general permission to redistribute
their PDFs; they remain references only. The later Boulebnane preprint's exact
arXiv version carries CC-BY-4.0, but its PDF is kept in the private reading
annex, outside this repository. Citation links neither certify the
prose-to-Lean correspondence nor extend formal coverage.

The reference records distinguish retained sources from link-only references.
The packaged Lean extractor separately adapts Comparator's structural traversal
cases under Apache-2.0; its source header retains the attribution. The QAOA
example also contains licensed upstream sources recorded in its own source
lock. Lean's expression/axiom API, LeanArchitect's traversal boundary,
doc-gen4's source index, and Verso Blueprint's separation of provenance,
content, and formal evidence informed the implementation choices. The
natural-language paper informs an optional draft stage.

The license records deliberately preserve inconsistencies: leanblueprint's actual license is Apache-2.0 despite an MIT packaging classifier; Verso Blueprint's inspected Lean file has an Apache-2.0 header but its repository root lacks the referenced LICENSE file. Any future source copying needs a file-level license inventory, retained notices, and a recorded change history.

Community discovery sharpened these choices. A [September 2025 Zulip discussion](https://leanprover-community.github.io/archive/stream/113489-new-members/topic/Is.20it.20possible.20to.20map.20dependencies.20of.20theorems.3F.html) distinguishes a plan written before formalization from a graph extracted afterward. An [April 2024 maintainer reply](https://leanprover-community.github.io/archive/stream/113489-new-members/topic/How.20to.20make.20blueprint.html) directs users away from copying an old project's folders and toward leanblueprint's maintained instructions. These discussions are discovery context; the technical choices above rely on the linked primary implementations.


## Exact-edition mathematical comparisons

The reference register now identifies five additional primary editions used in
bounded comparisons: Basso–Gamarnik–Mei–Zhou v2 for the uniform finite-depth
higher-spin obstruction; Chou–Love–Sandhu–Shi v3 for its sparse antecedent;
Sellke v4 for optimizability and scalar value methods; and Lopatto's
external-field v1 and zero-field v4 for positive-temperature comparisons.
The v3 and v4 Lopatto texts remain distinct, as do finite-temperature probability
measures and zero-temperature Stieltjes measures. Complete reading copies are
retained privately; the public register carries source URLs, byte hashes and
reading scopes. These citations supply mathematical context and method credit,
not a new proof dependency or verification verdict. The long paper states the
applicable theorem hypotheses and the scope of each comparison.
