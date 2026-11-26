# Sources and implementation choices

Lean Exposition starts with a small exporter over compiled Lean declarations. It records evidence for authors and reviewers; it does not turn proof acceptance into approval of an English claim. Initial sources were retrieved on 23 October 2026, scholarly software credits checked on 24 October, and TheoremGraph added on 25 October. [references.json](references.json) records each source's acquisition date, immutable pins, selected-file hashes, license evidence, and disposition.

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

## Formal and informal graph correspondence

[Kurgan et al., TheoremGraph (arXiv:2606.25363v1)](https://arxiv.org/abs/2606.25363v1)
connect informal statement dependencies with typed dependencies extracted from
compiled Lean declarations. Its “Formal Graph” section separates signature,
proof, definition, structural and documentation references. “Bridging the
Corpora” proposes formal/informal statement matches using generated summaries,
retrieval and model judgments; its accepted match class includes inexact
relationships such as special cases and one direction of an implication.
The limitations section describes the loss of context and limited expert
calibration. These are useful precedents for inspectable, typed relations,
without making a retrieved match a proof of equivalence.

This repository's authored passage maps identify which captured text and claims
are being compared. They retain that correspondence's review boundary rather
than assigning proof status from matching text. The exact v1 paper and TeX
source are held in the private annex; the public record retains their hashes
and reading scope. No claim of novelty follows merely from using a graph.

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
| [Farhi, Goldstone and Gutmann, arXiv:1411.4028v1](https://arxiv.org/abs/1411.4028v1) | Section II, equations (14)–(26), explains cancellation outside the support of an edge observable at fixed QAOA depth. The long record uses this for the finite-tree calculation; the later dense-SK transfer requires its own theorem. The exact original PDF is retained privately and fingerprinted in the reference index. |
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


## What to work out before each paper

These routes are reading exercises drawn from the cited specialists' arguments
and teaching order. Each tells you where the exercise pays off in the reader.

- **Navier–Stokes.** Before estimating the period map, apply the heat equation
  to one Fourier mode and let the frequency approach zero. This identifies
  where the uniform strict contraction has to come from. Before the vector
  certificate, follow the one-parameter construction cited in §7.4. Solve at a
  fixed parameter and then use opposite signs to remove the scalar obstruction.
  [Tao, 254A Notes 1, heat estimates and Theorem 45](https://terrytao.wordpress.com/2018/09/16/254a-notes-1-local-well-posedness-of-the-navier-stokes-equations/) ·
  [Donninger–Schörkhuber, §2.3, steps 7–8](https://arxiv.org/html/2406.16597v3#S2.SS3)
- **Euler.** Solve phase transport and check self-advection for one wave on a
  constant affine strain before following the succession of localized waves.
  Then repeat the phase-gradient calculation in a shear, where the forward
  transpose and inverse transpose give opposite signs. This prepares the
  affine material-acceleration identity and the localized chain rule.
  [Coiculescu, §§1–2, equation (3), and §4](https://terrytao.wordpress.com/2026/11/23/finite-time-singularity-formation-for-the-three-dimensional-euler-equations/)
- **Contextual Embeddings.** Identify the binder before counting outward.
  Compare renaming the inner binder with changing which binder an occurrence
  refers to. This prepares the indexed variable and context-extension rules.
  [Wadler, Kokke and Siek, “A second example”](https://plfa.github.io/DeBruijn/#a-second-example)
- **Coupled spring.** Check an off-axis slice after the two coordinate slices.
  A large mixed coefficient can turn a point with positive coordinate
  curvatures into a saddle. The spring test evaluates the full quadratic form.
  [Strang, *Calculus*, §13.6, Examples 6–7](https://ocw.mit.edu/ans7870/textbooks/Strang/Edited/Calculus/13.5-13.7.pdf)
- **SMT-LIB 2.7.** Walk one declare–assert–check interaction before reading
  the grammar tables. Move the declaration after the assertion and see which
  layer rejects the unchanged assertion. This prepares the grammar witness
  and the separate check of the declared names.
  [Cok, Chapter 2, “Basic Boolean example”](https://smtlib.github.io/jSMTLIB/SMTLIBTutorial.pdf#page=14)
- **PCP.** In the exposition, corrupt one table entry and ask whether the
  question is exact low degree or distance from low degree. In the short
  paper, reconstruct one value from random lines. In the long record, practice
  a masked Hadamard read before the product check. The reading guide starts
  by enumerating all seeds for one fixed proof.
  [Sudan, Lectures 1 §5, 2 §4 and 3 §§2.5–2.6](https://people.csail.mit.edu/madhu/papers/2004/pcp-ias.pdf) ·
  [Arora–Barak, §11.2.1, Remark 11.6](https://theory.cs.princeton.edu/complexity/ab_pcpchap.pdf)
- **Quartic query separation.** Trace the first differing query for a blank
  certificate array in the short paper. In the reconstruction, factor an
  adaptive transcript into restrictions on independent inputs. In the
  exposition, apply the two Grover reflections and check the conditional
  distribution in the flagged component.
  [Aaronson–Ben-David–Kothari, Lemma 6](https://obj.umiacs.umd.edu/cheat_sheet/1511.01937.pdf) ·
  [Drucker, Lemmas 3.1–3.2](https://people.csail.mit.edu/andyd/SDPT.pdf) ·
  [de Wolf, §§7.2–7.3](https://homepages.cwi.nl/~rdewolf/qcnotes.pdf)
- **Erdős #257.** Work out quotient and remainder in a fixed denominator,
  then follow one residue row through a full and a partial period. This
  prepares the use of one common shift and the correction for leftover
  entries. The [Erdős guide](erdos-method-transfer.md#before-opening-a-library-paper)
  gives a corresponding exercise for each catalogue paper that opens as a PDF.
  [Conrad, §2, Theorem 2.4](https://kconrad.math.uconn.edu/blurbs/ugradnumthy/modarith.pdf) ·
  [Erdős, pp. 223 and 226](https://www.renyi.hu/~p_erdos/1969-09.pdf) ·
  [Duverney–Tachiya, §2, equations (2.3) and (2.6)–(2.9)](https://danielduverney.fr/documents/theorie-des-nombres/DuverneyTachiya190522.pdf)
- **QAOA/SK.** Maximize the two-spin energy with disorder fixed. Next work
  out the contact derivative and one Cole–Hopf step. For the finite Gaussian
  approximation, couple with the same Brownian increment and check the pairing
  at size one before reading the limit.
  [Panchenko, §§1–2](https://arxiv.org/pdf/1412.0170) ·
  [Chen, Propositions 3.2 and 3.10](https://arxiv.org/html/2607.18032v1) ·
  [Full-support preprint, §7, Proposition 7.2](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/main.pdf)
- **Talagrand–Parisi.** Derive Guerra's bound at a single trial overlap
  before working through the cascades. Complete the square in the pressure
  derivative and track the sign. Then average the mass-one field in
  Talagrand's setup to recover the simpler interpolation with a constant shift.
  [Bolthausen, §3.3, Theorem 3.8](https://www.kurims.kyoto-u.ac.jp/~kumagai/EB-LN_Kyoto_finaL.pdf#page=29) ·
  [Montanari–Sen, §2.7.2](https://arxiv.org/pdf/2204.02909v2#page=98)
- **Riemann reader.** For the analytic argument, expand the ordinary
  nonnegative Dirichlet series around a real point before handling the signed
  series in §4.1. Compute the residue of the logarithmic derivative near a
  simple and a double zero. For the arithmetic argument, draw a three-slope polygon and apply
  the minimum-slope inequality to the map onto its retained image before §5.4.
  [Kedlaya, §1, Theorem 2](https://kskedlaya.org/18.785/dseries.pdf#page=1) ·
  [Bost, Appendix A.2–A.3](https://www.numdam.org/article/SB_1994-1995__37__115_0.pdf#page=33) ·
  [Bost, §4.3.1, Proposition 4.3](https://www.numdam.org/article/SB_1994-1995__37__115_0.pdf#page=18)
- **PhysLib gauge theory.** Compute the field strength of a pure gradient with
  both indices down, then change to the reader's index convention. Compare
  a constant gauge transformation with one whose derivative is nonzero.
  Finally test the central element on one particle representation before
  opening the group-theoretic declaration.
  [Tong, *Electromagnetism*, §§5.3.1–2](https://www.damtp.cam.ac.uk/user/tong/em/em4.pdf#page=12) ·
  [Tong, *Gauge Theory*, §2.1.2](https://davidtong.org/pdfs/teaching/gauge-theory/gauge2.pdf#page=6) ·
  [Tong, *Line Operators in the Standard Model*, §3](https://arxiv.org/pdf/1705.01853#page=10)
- **Quantum programs.** Choose the first check by the operation used in the
  linked proof.
  - For **arcsin**, do fixed-width addition through wraparound, then undo it.
    [Häner, Roetteler and Svore, Appendix A](https://arxiv.org/pdf/1805.12445v1#page=6)
  - For **Grover**, obtain the oracle phase in one slot before applying the
    simultaneous oracle. [Zalka, §1](https://arxiv.org/pdf/quant-ph/9711070v2#page=2)
  - For **fusion**, track the electron and projectile momentum separately to
    see what happens to the cached electron sum.
    [Rubin et al., §II.A, equations (5), (7) and (8)](https://arxiv.org/pdf/2308.12352v1#page=5)
  - For **photochemistry**, write the joint electron–nucleus Hamiltonian, then
    work both outcomes of one-bit measurement cleanup.
    [Pocrnic et al., §II](https://arxiv.org/html/2602.11272v1#S2) ·
    [Gidney, Figure 3](https://arxiv.org/html/1709.06648v3#Sx3.F3)
  - For **P450**, decode phase to energy, apply the cap to each result and
    then compute the root-mean-square error. A large error on rare outcomes
    can use the whole allowance.
    [Babbush et al., §II.3, equations (21)–(23)](https://arxiv.org/html/1805.03662v2#S2.SS3)
  - For **verification**, apply partial and total correctness to the same
    coin program and track the trace lost to nontermination.
    [Feng and Ying, Definition 4.9](https://arxiv.org/html/2008.06812v2#S4.Thmtheorem9)

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
