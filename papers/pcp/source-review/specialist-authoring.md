# Specialist paper authoring record

## Scope and reader

The specialist reader knows the PCP theorem, finite fields, low-degree testing,
and the distinction between randomness and bit-query complexity. The paper's
subject is the algebraic construction of Amireddy, Behera, Srinivasan, Sudan and
Willumsgaard and the exact route formalized by Troy Lee. It is an explanatory
reconstruction, not a new PCP theorem or a claim that the present author wrote
the formal proof.

The central mechanism is that a line polynomial is encoded as a constant-degree
set-multilinear polynomial, then each field value is encoded by a low-degree
Hadamard word. Lagrange-weighted local tests and corrections permit the outer
polynomial checks to be performed with constantly many bit reads. Vanishing
certificates then express the two graph-colouring constraints without an
iterated PCP-composition construction.

## Inputs and initial decisions

- Formal source: Troy Lee's `tcs-formalizations` at
  `a0ce13ed0fa264f051c1278e039596ce65557fa4`.
- Mathematical reference: *A Simple Algebraic Proof of the PCP Theorem*,
  arXiv:2608.17429v2, 22 October 2026, including its appendices; v1 is used only
  to understand the corrected generator test.
- The source-level evidence graph is a navigational/curated graph. It is not
  a compiled dependency extraction or a new Lean validation receipt.
- Read exact endpoint and verifier definitions, the source README's deviation
  account, Hadamard encoding and the final soundness-budget interfaces.
- Read the completed algebra, binary and theorem chapters in full before
  finishing the manuscript. The shortened account preserves their common
  decoding, actual sampling distributions and exact error contracts.

Theorem one will keep the quantifier order: for each fixed NP language, there
are one polynomial-time verifier, constants and a polynomial proof bound, all
chosen before the input and its random seed. Query complexity is a per-run
upper bound, not an expected count. The verifier has perfect completeness and
soundness at most one half against every fixed purported proof.

## Planned allocation

1. Exact theorem and the construction's mechanism.
2. Two polynomial identities expressing three-colouring; one certificate
   polynomial for each vanishing claim.
3. Digit encoding of line polynomials and its cost; Hadamard query translation.
4. The corrected weighted test, binary low-degree decoding, and the
   point-versus-line input. Full bivariate proof belongs in the long record.
5. Local correction at nonuniform certificate points and the soundness
   argument for the assembled verifier.
6. Explicit resources, amplification, NP reduction and converse.
7. Compact formal correspondence and conventional references.

## Version differences to preserve

- Pinned Lean uses `2r+4` Hadamard-test queries (10 at degree three), whereas
  v2 describes an 8-query top-degree test. The lower-degree checks remain in
  the pinned implementation even though its proof does not need them.
- The inner binary tester chooses between two checks with a fair coin.
- The outer line parameter and the grid seeds are sampled from the whole
  field; the grid check accepts immediately at a zero exceptional parameter.
- Auxiliary line tables have degree-one labels. The additional proximity
  guarantee is for homogeneous linear labels, which suffices at its use.
- The pinned proof has an independent-seed implementation and an averaged
  rejection-transfer argument for derived oracles.
- The final concrete parameters differ from the asymptotic parameters in
  the paper. Exact runtime and NP reduction are additional formal work.

## Completed selection and omitted proofs

The manuscript has 14 paired passages and approximately 4,400 whitespace-delimited
words. The title, abstract and theorem promise one account of the algebraic PCP
construction. Sections 3–6 contain the decisive mathematical work: both encodings,
the tests' two simultaneous proximity guarantees, correction at arbitrary targets,
the ZERO rejection inequality and the common decoding contradiction. The theorem
and resource conclusion retain one fixed proof before every random choice.

The bivariate error-locator proof, mixed-plane/ruled-surface counting and degree-zero
case remain in the full algebra chapter, which was read in full and checked as the
actual proof destination. The short paper states the exact point-line theorem and
explains its mechanism. Detailed BLR Fourier calculations and row-decoding budgets
remain in the full binary chapter; the specialist paper retains the bilinear defect
argument and the resulting constants. Machine-state simulation, tableau clauses,
colouring gadgets and code-size accounting remain in the theorem chapter. The short
paper retains the runtime obligation, reduction size-to-randomness inequality and
complete elementary converse. These cuts keep the two encodings and correction
argument central rather than replacing them by source links.

## Prior review dispositions applied

Read `work/prior-funnel-routes.md`, the quartic round-nine expert revision in
`/Users/willcook/src/quartic-query-lean/research/adjudication/round9_expert_revision.md`,
the later round-ten remaining-revision account, and the QAOA/SK
`source-review/references-and-adversarial-review.md`, including its review-driven
revision and method-transfer account. The transferred decisions are concrete:

- State local contracts before invoking them: the total rejection threshold,
  common decoded polynomial, label distribution and degree capacity are visible.
- Keep the same mathematical witness through successive arguments: all seven
  checks use one four-polynomial decoding, as the SK work keeps one supplier.
- Preserve the observable needed downstream: homogeneous proximity is stated
  separately from full-label proximity; no stronger affine claim is inferred.
- Keep ordinary deductions separate from formal endpoints: the infinite old-test
  counterexample is identified as explanatory mathematics, without a Lean label.
- Show the mechanism locally and link omitted derivations to their actual proofs.
  A dependency count or source inventory would not meet the specialist purpose.

## Source-grounded language review

The primary prose model was arXiv v2's introduction, technical tools, binary
low-degree test and PCP verifier sections. Their relevant moves were applied in
original prose: state the bit-alphabet obstacle before defining encodings; give the
evaluation identity immediately after the digit substitution; identify nonuniform
query locations before using correction; state the error budget beside the
soundness conclusion. The specimen "the low-degree test is the bottleneck" from
`source-v2/low_degree_test.tex` identifies the allocation choice, not a borrowed
sentence in the manuscript. No named author's voice is imitated.

The repository's register profiler compared the manuscript with the five substantial
v2 TeX sections. The comparison is section-based, not five independent papers. First
measurement: 3,535 extracted prose words, mean sentence length 14.2, semicolon rate
6.79 per thousand words, no apparatus rate, 12 features beyond the comparison's IQR
threshold. After semantic line edits: 3,539 extracted prose words, mean sentence
length 14.2, semicolon rate 6.78, again 12 features beyond the threshold. These
statistics describe extraction and style; they do not measure correctness or
reader comprehension. Differences in mathematical vocabulary, imperative proof
sentences and first-person use were inspected without forcing the source's rates.
The temporary profile file was removed after the results were recorded here.

## Sequential paragraph review and repairs

Every paragraph was read in manuscript order, with the mathematical role and
following inference checked. The grouped decisions below cover all 14 passages.

| Passage | Reader task and retained content | Decision or repair |
| --- | --- | --- |
| Abstract | Recover theorem, encoding mechanism and attribution. | Retained exact resources and explanatory-contribution ceiling. |
| Theorem | Recover common quantifier order and distinguish symbols from bits. | Retained per-run query budget and one proof fixed before coins. |
| Colour constraints | Derive two grid identities and understand each constraint. | Retained K4/F4 boundary example and certificate construction. |
| Digit encoding | Calculate substituted evaluations and decoded degree. | Changed total degree "is c" to "at most c" to include the zero polynomial; fixed b,c positive. |
| Hadamard encoding | Recover binary observables and fixed-request correction. | Generalized the elementary masking explanation to any additive functional, as needed by the subsequent proof; repaired label types after independent review. |
| Weighted test | Recover exact and robust characterization and reason for weights. | Retained strict threshold, full generator and counterexample's limited scope. |
| Binary decoding | Understand why a low-rejection row is an evaluation word. | Made epsilon the combined tester's rejection, so each check is bounded; stated the r=1 case separately. |
| Outer decoding | Follow row decoding through corrected line observations to a global polynomial. | Retained exact field/rejection thresholds; separated full bivariate and point-line proof destinations. |
| Outer correction | Recover the pointwise-in-target, label-averaged guarantee. | Retained actual rejection term, arbitrary auxiliary table and failure including rejection. |
| ZERO | Recover ideal rejection and coupled correction losses. | Retained the multiplying factor on derived-read error and polynomial degree premise. |
| Assembly | Use one decoding to force a proper colouring. | Added explicit m(h−1)≤D hypothesis for the public adjacency degree; checked every term in (19). |
| Resources | Derive both grid capacity and resource upper bounds. | Retained minimality argument, exact sampling loss, actual 187-read count and fixed-proof amplification. |
| Complexity | Recover runtime, reduction and converse. | Removed an imprecise closing phrase about exponentially many inspections; the mathematical conclusion now ends at the proved equality. |
| Formal correspondence | Find source theorem and distinguish exposition from formal proof. | Added complete declaration-type line ranges and retained one compact provenance account. |

The independent foundations agent identified the label mismatch: the first draft
called homogeneous labels maps on F but wrote L(ρ(A(u))). The accepted repair
identifies affine labels with maps F→F2 through ρ and writes L(A(u)); the reviewer
confirmed the intermediate repaired edition `55894a0c`. No new mathematical
content was inferred from agreement with a reviewer. The counterexample's earlier
independent source/hypothesis review is retained in
`work/pcp-reviews/old-test-counterexample.md`.

## Validation and remaining integration

Read the exact forward declaration and concrete reverse theorem and the full
types of encoded-line soundness, local correction and assembled soundness in the
pinned checkout. Public hyperlinks highlight those declaration types through their
conclusion. Read the primary TeX passages and all three complete long chapters;
the chapter evidence records provide further source-body locators.

A finite exact-rational check recomputed c=4 constants:
K=105408, J=1054138, S=1054166, C=1054082,
g4=1/71115455156448, and delta=g4/16=1/1137847282503168.
Paired passage markers were checked for uniqueness and matching order, and all
candidate graph IDs were resolved against the current source-level graph.
All six immutable Lean declaration hyperlinks were resolved in the pinned checkout
and their highlighted ranges include the complete conclusion. All seven internal
full-argument fragment links resolve against the integrated long record. The final
precision pass makes the counterexample's dimension and ambient fraction explicit,
and adds the concrete-class/reference-NP equivalence with its exact source link.

Current manuscript SHA256:
`72d165920fbc02aa7b58bc626c3e6899cd2f099089a80cb10efa792279127577`.
`work/pcp-chapters/short-evidence.json` binds this edition and preserves claims,
source identities, long-proof destinations and evidence limits. It is candidate
mapping evidence for the parent, not a canonical checked bundle.

No Lean build, Comparator run, independent human reading or rendered-page inspection
was performed by this authoring agent. The parent owns assembled bundle checks,
rendering, reader navigation, source verification account and publication. A
source-assisted independent paper review is in progress; its final disposition
must be bound to the final manuscript, not inferred from this self-review.
