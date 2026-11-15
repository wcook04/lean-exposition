# PCP exposition authoring record

## Edition and purpose

This is the authoring and source-check record for
`work/lean-exposition/papers/pcp/expository/main.md`, prepared on 15 November 2026.
The first edition handed to the separate sequential reader has SHA-256
`9d04a0bc03eea71be08d68854a442606c3966cf3e089c558663d411cd99365dc`.
It has 18 paired passage markers. Changes after that edition must be listed
below and the mapper must rebind their passages.

The reader is mathematically literate, comfortable with polynomial arithmetic,
finite sums and elementary probability, but new to complexity theory and coding
theory. The intended outcome is to reconstruct why a frequently accepted binary
proof would determine a genuine colouring: common low-degree decoding,
difference consistency and locally corrected grid certificates have to refer to
the same decoded objects. The reader should also distinguish polynomial proof
length, logarithmic randomness, constant bit queries and polynomial running
time.

The article explains the complete route to one classical theorem, rather than
announcing a new theorem. The construction belongs to Amireddy, Behera,
Srinivasan, Sudan and Willumsgaard; Troy Lee formalised it. AI agents wrote the
new explanatory account under Will Cook's direction. No human-review or
measured-learning outcome is asserted.

## Inspected authority and transition inputs

The author inspected the main theorem and verifier definitions at Lean source
revision `a0ce13ed0fa264f051c1278e039596ce65557fa4`, the PCP guide and its listed
formalisation differences, and the corrected v2 TeX sources for the algebraic
tests, encoding, local correction, ZERO and final verifier. The mathematical
source is *A Simple Algebraic Proof of the PCP Theorem*, arXiv:2608.17429v2;
the retained PDF has SHA-256
`764824336d1de4f95e1fe9c774d157e419578157c408dfd016f3903d73d73795`.

The following completed long chapters were read in full before the exposition's
final proof narrative was settled:

| Chapter | SHA-256 inspected |
| --- | --- |
| `work/pcp-chapters/algebra.md` | `5d22ab32ab81f127bb8e13a63d746948cb894f6f294f8fabee1198598c08c093` |
| `work/pcp-chapters/binary.md` | `c76a06272c4c2d9eb5d2bfc7344ac3c1b7e8cfb6ad1da2293d63c91dae7f8819` |
| `work/pcp-chapters/theorem.md` | `2b631d1bcd117c38a41b4f20d8d510d0575b6c2168d214aa1a1f54efedf35937` |

The specialist paper's theorem, scope and initial encoding/constraint sections
were read at SHA-256
`72d165920fbc02aa7b58bc626c3e6899cd2f099089a80cb10efa792279127577`.
This was a scope-consistency check, not a claim to have independently reviewed
every paragraph of that companion.

The prior funnel method was taken from the actual `record-to-expository` and
authoring guidance, the retained quartic examples-first lessons incorporated
there, and the QAOA–SK exposition and its
`source-review/references-and-adversarial-review.md`. The transferred decisions
were: teach the operation before its abstraction; do not let a toy calculation
inherit a theorem with unmet hypotheses; separate a changed-case question from
its answer; require the same decoded object across successive uses; and record
an author's reconstruction separately from an independent reader attempt.
The new manuscript does not claim the teaching method has been validated on
this audience.

Applied method versions:

| Method | SHA-256 |
| --- | --- |
| `record-to-expository/SKILL.md` | `a789263d95a63b62ede93b78e19809cecade4789d2bebfadd5159289133ffcbb` |
| `register/SKILL.md` | `622f4a69c9eeb3fcf39a4b709b7a1657ac6b1ae1f918eb56d9c70c2e30f87215` |
| mathematical-reasoning | `4b05f286c2d503cfa7647663c2142814188e51c04549f890ad1778ce4e732086` |
| formal-math-exposition | `b661cf21d6648c287b272284efe640f0989412d10c1a78939576a9618b37729d` |
| the-deliverable | `5b234d4446bf4b7ac79c38586147730dc41370581daa38661326875d5b50951c` |
| mathematical-writing-mechanics | `2527ee0d0ec1b7927b953e22fff9437c8593f352e727e8a869694f98925b539d` |
| full-exposition-guide | `153459602e211b17007026a19ca30116a91b8f60b7a3dcaa01017eac2ed97e30` |
| bounded humanizer gate | `bc633bce381ae129d3a4ec35f88c367ce97135db66248a983dcec612207e1745` |

## Prerequisite ladder and example decisions

All IDs in the next table have prefix `pcp-expository-`. Each example either
teaches an operation used later or exposes a false inference that would break
the final proof.

| Passage | Operation available to the reader afterwards | Authority and boundary |
| --- | --- | --- |
| opening; colouring | State the certificate problem and calculate why raw edge sampling can lose its gap. | K4 plus proper disjoint triangles; exact finite checks and a direct counting formula. This is not a PCP parameter instance. |
| theorem | Keep the order of verifier, input, fixed proof and random seed; enumerate all logarithmically many random bits. | Exact formal endpoint, ordinary elementary converse explanation. |
| polynomial-distance | Apply the univariate root bound and understand the total-degree generalisation. | Root bound explained; multivariate induction is an explicitly accepted theorem whose proof is in the long account. |
| interpolation | Compute the weights before using Lagrange interpolation to extend a grid. | All 125 F5 quadratics checked; general formula justified by its basis values. |
| colour-polynomials | Interpret both vertex and edge equations in characteristic two. | GF4 residual table; all-four-colours K4 example explains why vertex validity cannot be omitted. |
| grid-certificate | Substitute the two arguments of M and infer grid vanishing. | F5 worked polynomial and both identities; polynomial division explains the general existence direction. Nonempty H is present in the construction. |
| digit-encoding | Expand an exponent in base three, form its monomial in new variables and recover its evaluation. | Five finite substitutions checked; general digit identity derived. Small field example illustrates encoding, not soundness parameters. |
| weighted-test | Distinguish test soundness from local correction; use uniform marginals and a union bound. | Corrected generator theorem stated with its exact threshold; full proof referred to the long record. |
| hadamard | Compute a parity codeword, distinguish messages in half the positions and count BLR failures. | Explicit degree-one homogeneous example. It does not instantiate the complete degree-three test. |
| hadamard-correction | Recover a fixed requested bit using two randomly translated entries. | Exact six-of-eight and eight-of-eight counts; x=0 boundary retained. |
| cubic-labels | View a nonlinear expression as a label; explain why linearity in labels is insufficient. | Bilinearity of field multiplication is the stated linear-algebra fact. A four-label counterexample is enumerated; product and unit tests are required. |
| binary-tests | Incorporate a scalar weight into a homogeneous label; distinguish full and restricted-label proximity; correct nonuniform certificate points. | Exact decoded object shared by both guarantees; honest ZERO completeness includes primary, certificate and auxiliary line data. |
| assembly | Reconstruct a colouring from high acceptance and identify which decoded objects are only used in the analysis. | Four low-degree tests, two ZERO checks and one difference check; fixed positive gap belongs to the whole assembled verifier. |
| resources | Count coordinate bits, explain parameter minimality, fair-bit conversion, repetition and NP reduction. | Actual formal parameter family and gap. A separate NAE gadget example makes the last reduction concrete. Machine implementation is an accepted formal result, not inferred from query count. |
| answers | Diagnose four changed information/hypothesis patterns and distinguish failed argument from false conclusion. | Answers separated from questions; sqrt(n) randomness invalidates this NP-converse proof without proving nonmembership in NP. |
| correction | Explain why completeness of an old test did not imply its soundness. | Unbounded x^4 family reviewed separately by parent; GF16 enumeration illustrates it, but does not prove the family. |
| evidence | Identify original authorship, formal edition, computational examples and further proof destinations. | Source-bound reconstruction, no new build or human-review claim. |

The worked examples use modular arithmetic, parity and finite counting, all
introduced before their first consequential use. Bivariate agreement, robust
low-degree testing, the full Hadamard soundness proof, binary local-corrector
constants and the concrete machine implementation are stated inputs with
destinations in the long account. The exposition explains their logical roles
without pretending to reprove all of them at this prerequisite level.

## Source and mathematical repairs during author self-review

The author read the complete initial manuscript in source order, then reread
the revised passages against the long chapters. This is author self-review;
the author already knew the proof and cannot supply a cold-reader result.

| Located difficulty | Decision and retained conditions |
| --- | --- |
| Opening began with a general complexity claim before the finite object. | Opened with the graph/colouring certificate, while retaining the theorem's full scope immediately afterwards. |
| Point-versus-line input was only described as a large-field theorem. | Added the actual all-field sample distribution, degree bound, rejection threshold and 2-delta conclusion, plus the plane/crossing/plurality proof mechanism. |
| Vertex-validity necessity was stated but not demonstrated. | Added K4 with all four GF4 elements: edge equations pass, but zero violates vertex validity. |
| ZERO completeness could be read as requiring only a correct primary table. | Explicitly required the honest primary encoding, certificate and encoded line data. |
| Resource paragraph could make polynomial time sound automatic from short addresses. | Gave actual parameters and minimality argument, then separated address/seed counting from the concrete machine implementation. |
| Conversion from arbitrary NP relations to colouring was too compressed. | Added bounded tableau, fixed finite relations, one-hot Boolean coding and an explicit OR/NAE/triangle derivation. |
| Answer 2 stated fixed-location corruption without the x=0 boundary. | Restricted the failing example to nonzero x and retained the exact cancellation at zero. |
| A formatting typo joined “identities,+binary”. | Removed the accidental plus and restored the line break. |
| Original-paper DOI links were not grounded in the retained manifest. | Used the exact acquired primary PDF destinations instead. No bibliographic identity was inferred from a guessed DOI. |
| Source interpretation distinguished points used for analysis from verifier operations too indirectly. | Replaced the negative rhetorical paragraph by the direct statement that decoded objects exist in the soundness analysis. |
| Old-test example could have been mistaken for a merely small-field defect. | Included the unbounded q=2^(2k) family, the 1-4/q distance argument and its exact limited target. |

Paragraph-level jobs were reviewed within every passage listed above: definitions
introduce the next operation, examples execute it, theorem paragraphs state the
input contract, comparisons explain a necessary restriction, and transitions
restore the current object. Successful numerical derivations and hypothesis
sentences were retained. In particular, the negative clauses about nonuniform
queries, unrelated decoded witnesses and x=0 were not removed merely to lower a
style metric. Bounded humanizer edits affected expository framing, not formulas,
theorem hypotheses, citations or limitations.

## Literature-grounded register pass

The teaching comparison is Arora–Barak's retained January 2007 internet draft,
Chapter 18, especially pp. 18.1–18.4: it introduces a familiar certificate,
states a verifier definition and theorem, and follows with the exhaustive-seed
converse and repetition observation. The inspected introductory specimen
“Suppose somebody wants to convince you that a Boolean formula is satisfiable”
identifies the object and the communication problem before its definition.
The new exposition adapts that move to its actual graph construction.

The source-paper comparison is ABSSW v2, introduction and Sections 3–7. Its
set-multilinear introduction explains why a line coefficient vector is too
expensive before introducing the new variables. That dependency supplies the
ordering in exposition Section 6. The source's opening phrase “Ever since the
discovery of the PCP theorem in the early 90s” introduces history; this was not
copied as the newcomer opening because the reader first needs the certificate
problem. Research-paper prose is not a numerical target for a teaching article.

Using the repository's `lean_exposition.register` parser and feature functions,
the author measured the initial and revised manuscript, the retained v2 text,
and Chapter 18's text extraction (lines 17591–19400). Selected measurements:

| Feature | Initial draft | Revised reader edition | Arora–Barak Ch.18 | ABSSW v2 |
| --- | ---: | ---: | ---: | ---: |
| Parsed prose words | 5243 | 5928 | 12915 | 15002 |
| Mean parsed sentence length | 13.29 | 13.44 | 20.11 | 19.49 |
| Sentence-length coefficient of variation | .457 | .448 | .672 | .632 |
| Mean parsed paragraph length | 43.43 | 45.00 | 40.13 | 39.09 |
| Negation feature per 1000 words | 11.44 | 10.63 | 4.80 | 2.73 |
| Contrast feature per 1000 words | 1.91 | 1.69 | .39 | .27 |
| Status-vocabulary feature per 1000 words | 10.30 | 9.62 | 4.72 | 4.80 |

These measurements nominated prose for inspection, not an effectiveness score.
The PDF text extractions contain mathematical layout damage; paragraph and
sentence segmentation are consequently only descriptive context, not calibrated
distributions. The additions lengthened the exposition because they supplied
missing operations and resource justifications. The reductions in negation and
contrast rates do not establish improved comprehension. No rate was pursued as
an editing objective. Rendered-page inspection remains with the integration
and reader-review lanes.

## Reproducible finite checks

The existing `work/pcp-examples/check_examples.py` has SHA-256
`c5a19323b19b05bd6d5d474a23ed714838436e2b68799db31eb0c25afc676be5`.
Its retained run covers GF16 weights and the old/new scalar-test comparison,
Hadamard/BLR/correction counts, the original grid polynomial, GF4 colouring
residuals and the toy repetition fraction. The parent reran that original
checker. The current author inspected its code and uses those exact results.

The additional executable companion is
`work/pcp-examples/check_exposition_examples.py`, current SHA-256
`b1c375fa0c8ab21ed9f415cbe375ac449252bdeefc074094539925e6e8016cfe`.
Its initial checked edition was `93daee0c4077a7f2daf7196ce21e85b881a27c7f7688b43b85d7256a3a7372f3`;
the current edition adds the OR-gate, mismatch-flag and toy-error-budget checks
used in the reader-driven revision.
It uses Python's standard library, exact integers and `Fraction`; its explicit
checks remain active under Python optimisation. Run:

```sh
python3 work/pcp-examples/check_exposition_examples.py
```

Observed exit status: 0. Observed output:

```text
K4: all 81 three-colour assignments checked; displayed assignment has one bad edge;
  disjoint-triangle construction checked for 0..11 triangles; t=3 gives 1/15.
F5: all 125 quadratics satisfy the [1,2,3] interpolation formula;
  both certificate identities checked at 25 ambient points; P(2,2)=4;
  P=M=1 shows why the first identity cannot be omitted.
Digit encoding: substitution equality checked at all five field elements; lambda=2 gives 4.
Label counterexample: all 256 BLR pairs pass; none of four evaluation points matches.
NAE: all eight Boolean cases checked for OR conversion and triangle extension;
  palette gadget permits exactly the complementary pairs (0,1), (1,0).
Review additions: all eight OR-gate cases and 64 prefix-mismatch cases pass;
  toy soundness budgets give 7/32 < 3/8 and equality 3/8 at the boundary.
All additional exposition checks passed.
```

Finite checking supports exactly the enumerated cases. The formula for any
number of disjoint triangles, the general interpolation identity and the
unbounded old-test counterexample are ordinary mathematical deductions given in
the prose. The small-field calculations do not establish the full PCP theorem's
asymptotic soundness or instantiate its actual enormous field.

## Review boundary and remaining integration checks

The separate `exposition_reader_review` agent began a sequential first pass on
the frozen reader edition before consulting the long record or the answers.
Its located findings and subsequent revisions belong in that review and in the
revision entries below. No successful independent human reconstruction is
claimed. The changed-case questions and the unassisted reconstruction task are
available for a future reader; merely including them is not evidence of
learning.

This authoring lane does not claim a fresh Lean build, compiled extraction,
rendered-PDF inspection, public publication or a completed bundle check. Parent
integration owns those outcomes and the final exact passage bindings. The
manuscript deliberately links to the complete proof and shorter paper rather
than duplicating machine-state derivations or every error constant.

The main theorem, its opening summary, the quantifier explanations and the
final reduction were compared with the same endpoint source. Material
differences from paper v2 are retained at their uses: generator weights,
all-field point-line parameters, the ten-query degree-three Hadamard test,
homogeneous-label guarantees and actual implemented parameter/query counts.

No generic method change is asserted from this one authoring pass. The existing
point-of-use prerequisite and evidence-boundary rules already required the
repairs above. `nothing_to_refine` pending the independent reader's findings.

## Subsequent review dispositions

The independent agent's sequential first pass on edition `9d04a0...` is retained
in `work/pcp-reviews/exposition-reader-review.md`. It distinguished reconstructing
the reason for each component from reconstructing the final error budget. The
second task failed at the original Sections 8–9: “controlled errors” had no
stated bound, so the reader could not infer a remaining positive gap or resolve
the corrector's dependence on its own rejection rate. This was a substantive
expository omission, not a cosmetic preference.

All requested repairs were incorporated:

| Finding | Revision and source check |
| --- | --- |
| Missing quantitative decoding contract | Section 8 now defines K,E,S,C, states the field and E-kappa threshold, and gives simultaneous full/homogeneous error S-kappa for one polynomial. Checked against binary chapter B11 and B14–B16. |
| Corrector's own rejection rate unresolved | Its exact rejection-or-wrong-output bound is stated, including average over homogeneous labels. The final test's rejection contains correction rejection; Section 9 applies this to the same derived ZERO test. |
| No usable constant-gap inference | Section 9 includes the difference inequality, actual derived-ZERO inequality and the 3/16 versus 3/8 contradiction. It explains why the derived-read loss is multiplied by 1+2C. Checked against the final soundness chapter. |
| Generator undefined for the audience | Section 6 defines it by powers exhausting the nonzero field elements, explicitly treats cyclicity as a standard algebraic input, and sets a_i=zeta^(i+1). |
| Decoded degree bound appeared without derivation | Section 6 bounds each substituted variable's degree by (b−1)b^(c−1); Section 10 identifies b=s and obtains D=4s^4. |
| Honest capacity and ZERO field ratios not checked | Sections 9–10 now require and verify 5s(s−1)<s^4, show Q≥100Dh, and derive the three root-term bounds used in the gap calculation. |
| Degree of packaged vanishing certificate absent | Section 5 now gives degQ_j+h≤degP for nonzero quotients and derives degM≤degP for h≥1. This supplies the later honest degree bound. |
| Fixed-arity relation to three-literal clauses omitted | The actual prefix-mismatch flags and their three-clause OR gate are shown before the NAE gadget. All eight OR-gate assignments and 64 three-bit pattern/input pairs were checked. |
| GF16 quotient notation unfamiliar | Section 12 explains binary polynomial representatives and reduction by t^4=t+1 before reporting the test counts. |
| Final changed-case task was only qualitative | Added Question 5, a strict error-budget boundary with separate answer. The question was sent to the reviewer before its answer was written. |

The reviewer's first response to Question 5, before seeing the answer, was:
ideal rejection is at most `5*kappa+1/16`; at `kappa≤1/32` this is `7/32<3/8`,
so a false grid condition is excluded; at `kappa≤1/16` equality leaves the
test inconclusive. The response also distinguished inconclusive estimates from
a false PCP theorem and observed that strict `kappa<1/16` would suffice. This
was an agent response after consulting the long record during diagnosis, not an
unassisted human-learning measurement. Its exact conditions and response are
preserved in the reader's record.

The final author edition, after these repairs, has SHA-256
`2e2333ca4727a5f8d510f5de8f184a4139f33122ae2d12ca3d29f2b9bec4d913`.
The author reran the extra checker successfully and checked all 18 unique paired
passage markers, display-delimiter parity and absence of placeholders or the
earlier formatting typo. The final register measurements are: 6884 parsed prose
words, mean sentence length 13.60, sentence-length CV .447, mean paragraph length
46.57, negation feature 10.17, contrast feature 1.45 and status-vocabulary feature
8.57 per 1000 words. These do not constitute a comprehension score. Every new
paragraph supplies the precise contract, calculation or first-use definition
identified by the reader; no formula or condition was altered to change a rate.

The reader accepted the main quantitative and parameter repairs at edition
`7dff5d...`, then accepted final source edition `2e2333ca...` after checking the
certificate-degree clarification. All consequential findings from that pass
were resolved. The reviewer also read and ran the current author checker at
`b1c375fa...`, including the OR-gate, mismatch-flag and rational-budget additions.
The old canonical-copy discrepancy was identified as a copy awaiting the
inventory owner's refresh, not a missing author-source run. Rendered HTML/PDF
review and bundle validation remain integration tasks, not outcomes claimed by
this authoring receipt.
