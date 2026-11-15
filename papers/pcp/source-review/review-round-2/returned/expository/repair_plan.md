# A bounded revision plan

## Aim and status

Revise the worked exposition so that its declared reader can perform the representation changes and reconstruct the soundness implication from the explicitly imported theorems. Preserve the current mathematical content and successful quantitative repairs. This plan proposes a small sequence of edits; it does not record author incorporation, a new paper edition or publication.

The independent findings remain in `findings.json`. The paragraph-by-paragraph decisions and complete high-impact replacement passages are in `line_edits.md`. An eventual editor should attach an incorporation, supersession, reasoned rejection or deferral to each recommendation; the review itself does not make those decisions.

## 1. Repair the label-domain route and the one formal association

**Why first.** The eight-bit example, full Boolean label space and homogeneous label family are different objects. This distinction determines both what is queried and which formal statement supports the explanation.

**Source locations.** Exposition Section 7, `pcp-expository-hadamard` (lines 518–567), `pcp-expository-cubic-labels` (604–642), and Section 8, `pcp-expository-binary-tests` (667–704). The selected reader link is `reader/edition.json` → `linked-source-18`, attached to lines 532–536.

**Changes.** Explain parity labels without a constant term before calling them homogeneous. Introduce the full label family as all coefficient choices, not a list of individual monomials. Use one small coordinate example to compute an actual label for a field expression, then apply the two-query random-mask correction to that requested label. Keep the same decoded polynomial explicit when full and homogeneous distance bounds are combined. A compact eight/16/256-position comparison or the checked full-versus-restricted-distance example can show why one average does not imply the other.

Retarget the selected half-distance association from `PCP.Algebraic.Hadamard.relativeDistance_encodeFunction_map` to `PCP.Algebraic.Hadamard.relativeDistance_linearEncode`, with its `linearEncode` definition available. Both are in the pinned `PCP/Algebraic/Hadamard.lean`; the desired theorem is at lines 173–180, with its definition at 137–143. Add the declaration to the reader index if necessary. Keep the full-domain theorem for passages that actually use full coefficient labels.

**Validation needed.** Check label domains, sampled distributions and every output in the new small example. Confirm the retargeted theorem's exact type and rendered source destination. No change to the Lean proof is proposed. Retargeting a valid theorem does not require a new whole-project kernel build.

**Companion dependencies.** The specialist already supplies the relevant operation in Section 3, `pcp-short-hadamard-encoding`, especially equations (6)–(9), and distinguishes label domains in Section 4, `pcp-short-binary-decoding` / `pcp-short-outer-decoding`. The long record already has `pcp-long-hadamard-labels`, `pcp-long-hadamard-composition`, `pcp-long-hadamard-self-correction` and `pcp-long-derived-constraints`. Use these as precise deeper destinations; do not copy the learner's arithmetic primer into both companions or make either companion a prerequisite for the exposition.

## 2. Supply the few missing elementary operations

**Source locations.** Exposition Section 2's resource language (lines 86–141); Section 3's total-degree and grid extension passages (163–233); Section 4's field change (239–285); Section 6's digit encoding (415–462).

**Changes.** Give a short meaning of a polynomial resource bound and total degree at first use. Explain (H^m) as tuples and show one two-dimensional interpolation basis product. For F4, compute with (1+omega=omega^2), subtraction equal to addition, and (u=a+bomega); calculate a nonzero colour difference and explain why the three displayed cubic roots exhaust the legal values.

Replace the degree-five polynomial over F5 with the checked nearby example (Y^4+2Y+3), or explicitly delimit the original as formal polynomial syntax. The replacement keeps base three and two digit positions: (4=1+3). Update the encoded polynomial, substitution, evaluated value and executable check together. The original calculation was correct; the reason for changing it is that (Y^5=Y) as a function on F5, which obscures the degree distinction being taught.

**Validation needed.** Exact finite checks of the replacement polynomial and F4 label calculation are required before incorporation. State where the tiny example simplifies a general degree bound. A successful toy computation does not instantiate the production field-size hypotheses. The unchanged general encoding theorem and larger soundness degree (D=cb^c) should still follow immediately.

**Companion dependencies.** No mathematical statement change is needed in specialist Section 2 (`pcp-short-colour-constraints`) or Section 3 (`pcp-short-digit-encoding`), nor in the long record's `pcp-long-colour-equations` and `pcp-long-set-multilinear`. If a new worked-example pointer is added, link from those existing passages to the exposition; retain their specialist level and existing notation.

## 3. Reorder the composed test and expose the event calculation

**Why this is the largest repair.** The manuscript now states the right quantitative results. The learner must still track which table gives each bit, which polynomial is fixed by decoding, when correction rejects and why a small observed rejection rate controls the error term.

**Source and destination moves.**

| Current source | Proposed destination | Content that stays on the main route |
|---|---|---|
| Section 9, `pcp-expository-assembly`, lines 767–774: four polynomial roles | Start of Section 8, before line 648's combined-encoding discussion | A compact four-row inventory identifying the colouring, difference and two vanishing certificates, each with its line table. Section 9 retains the eight-table/seven-check count and assembly. |
| Section 8, lines 676–704: K,E,S,C and combined theorem | Keep a role-based statement at the same mathematical point; put the unchanged expansions in a clearly titled parameter note at the end of Section 8, before Section 9 | Positive constants depending only on c; both field/rejection hypotheses; one decoded polynomial; degree bound; simultaneous full/homogeneous distances averaged over points and labels. |
| Section 8, lines 706–727: outer corrector | Same section, after the table inventory and label operation | Fixed target, sampled line, tested comparison, rejection, returned origin bit, and the precise rejection-or-error theorem with random-label scope. |
| Section 8, lines 736–761, and Section 9, lines 825–888 | Keep the elementary event comparison beside ZERO; retain the full actual soundness budget in Section 9 | Ideal rejection ≤ actual rejection + changed-verdict probability; both certificate calls; their rejection events; the derived-read replacement; the exact strict comparison. |

**Changes.** Show a single corrector request as a sequence of concrete operations. The output is either rejection or a bit; the verifier does not reconstruct the polynomial. For the error budget, first name actual and ideal decisions on the same random seed. If the ideal test rejects while the actual test accepts, at least one substituted answer changed the decision. Apply the union bound to those events, then use the existing correction bound. Preserve the factor ((1+2C)) on the entire (kappa+2arepsilon) term. The (2arepsilon) from the fresh derived read is not an independent unmultiplied afterthought.

Name the decoded vertex and edge *constraint* polynomials explicitly in the concluding paragraph; avoid the ambiguous phrase “two decoded colouring polynomials.” Keep the four decoded polynomials fixed throughout. A short common-witness counterexample should explain the failure caused by replacing them with separate witnesses for separate tests.

**Validation needed.** Trace the proposed prose against the exact theorem and event definitions. Check the correction bound still includes rejection, averages over a random homogeneous label and assumes neither honesty of auxiliary rows nor small correction rejection. Check all three field inequalities and the strict budget conclusion. These are source-correspondence checks for an explanatory rewrite; they do not authorize changing a theorem or proving a new guarantee.

**Companion dependencies.** Preserve specialist Section 5 (`pcp-short-outer-correction`, `pcp-short-zero`, equations (14)–(16)) and Section 6 (`pcp-short-assembly`, especially (18)–(20)). The long record already contains the deeper derivation in `pcp-long-outer-correction-soundness`, `pcp-long-zero-soundness`, `pcp-long-derived-oracle-transfer`, `pcp-long-decoding-contract`, `pcp-long-difference-soundness` and `pcp-long-assembled-zero-soundness`. These are exact destinations for proof pointers. The notation differs across papers—expository E corresponds to the specialist's line-error constant J—so preserve each paper's established notation and state the correspondence in the mapping rather than globally renaming symbols.

## 4. Recover space without weakening the proof route

Keep the main exposition approximately its present scale by reallocating material rather than adding a second full argument.

| Material | Source | Destination and retained summary |
|---|---|---|
| Deep point-versus-line proof sketch | Exposition Section 6, lines 398–408 | An optional “Behind the point-line theorem” note at the end of Section 6, or an exact link to the long record's “Bivariate agreement” and “Point-versus-line soundness” sections. The full theorem statement and its use remain before the digit encoding. |
| Fixed-arity mismatch-flag compiler | Exposition Section 10, lines 1009–1051 | Optional endnote “How the NP reduction constructs clauses,” after the main reduction conclusion. Reuse the full proof already in `pcp-long-np-tableau`, `pcp-long-local-constraints` and `pcp-long-clause-reduction`; do not append a duplicate to the long record. The main text retains the exact polynomial-time equivalence and resource transfer. |
| NAE colouring gadget | Exposition Section 10, lines 1053–1081 | Retain as a worked optional reduction example, preferably with a small labelled adjacency diagram or incidence list. Its existing detailed destination is `pcp-long-colouring-gadget`. |
| Historical faulty-test calculation | Exposition Section 12, `pcp-expository-correction` | Keep after the main proof as a clearly labelled boundary example. Add the short squaring-twice explanation; preserve old-version scope, family argument and credit. No relocation into the opening is recommended. |

The specialist's Section 7, `pcp-short-complexity`, already gives the right compressed reduction/runtime statement and should not inherit the detailed learner appendix. The long record's reduction and runtime proofs remain their existing destinations. Amend only navigation labels and links required by an actual move.

**Validation needed.** Read every optional route from its departure point to its return using only definitions retained on the main route. In particular, moving the clause compiler must not recreate the previously repaired unproved transition from fixed-arity constraints to three-literal clauses. Imported theorem plus precise proof destination is acceptable; an unexplained “standard reduction” is not the proposed repair.

## 5. Fix the reader's observed navigation/layout faults

The live desktop sample and frozen source associations are different evidence surfaces. The live reader was observed at 1900×1052; it was not established to be byte-identical to the frozen edition.

The useful route—opening the theorem, following InNP and NPCertificate, then returning—worked in the sampled journey. Preserve it. Two graph nodes titled “Decoding a low-degree polynomial” should have distinct visible qualifiers identifying the inner fixed-degree and outer encoded-line results. Their full statements must remain available.

After Graph → Close, the contents navigation occupied the full 1900-pixel width and about 516 pixels of height; the article began below approximately y=772. The state persisted across full-argument navigation and Back in the sampled journey. Repair the pane/column state so closing the proof pane restores the reading layout. Retest that exact sequence before treating the UI repair as complete. Check whether selection and scroll position are preserved. Responsive behavior and other device sizes remain unassessed; do not claim an exhaustive UI audit from this desktop reproduction.

Update the retargeted homogeneous-distance association in the reader's source index and displayed passage link as part of this same bounded reader repair. The fact that a frozen source link exists does not establish that the live interface displays it correctly.

## Finalization checks and boundaries

The following checks are concrete completion work for the proposed edits, not a new external approval process:

1. **New examples.** Run the exact finite checks for the replacement digit example, explicit field-coordinate label, masked correction and any label-domain counterexample. Record the range and output. The two original packet scripts already ran successfully; their success does not cover modified examples automatically. The parent subsequently ran the new-example checks successfully; `audit_checks.json` and `coverage.json` record that completion. Any further changed example needs its own focused check.
2. **Mathematical correspondence.** Recompare affected statements and source links, including shared witnesses, label distributions, correction rejection, honest/decoded degree, strict bounds and the unchanged formal constants. No fresh whole-project Lean build is required solely because explanatory paragraphs or link targets changed.
3. **Publication artifacts.** If the manuscript is actually revised, regenerate its PDF/reader content and inspect the changed pages plus their continuations and the source/further-reading links. The existing eighteen-page overview is evidence about the original render, not a future one.
4. **Reader route.** Retest the exact desktop graph/close/back sequence and the sixteen selected associations affected by reindexing; broaden only if the change creates a concrete cross-route risk.
5. **Review record.** Preserve the original first attempt and findings. Record incorporated, superseded, rejected-with-reason or deferred decisions; a repaired passage, a passing finite script and a human-learning result remain different evidence classes.

## Deliberate non-changes

Preserve the theorem's quantifier order and all three resource guarantees; the K4 dilution family; both grid-certificate identities; generator nodes with their actual weights; the honest/decoded degree distinction; the same decoded polynomial for full and homogeneous labels; rejection-aware, random-label correction; the strict soundness budget; fixed proof with fresh independent seeds; the distinction between failed seed enumeration and nonmembership in NP; the impractical constants; and the source/AI/evidence disclosures.

Do not add a new research programme, an outside reviewer gate, a fresh prerequisite course in the specialist paper or copies of proofs already present in the long record. The proposed changes do not alter or publish the pinned source manuscripts by themselves.
