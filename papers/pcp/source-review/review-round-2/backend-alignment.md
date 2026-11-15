# PCP source and reader alignment

The Lean pin is `a0ce13ed0fa264f051c1278e039596ce65557fa4`. Source paths below are relative to the pinned Lean tree under `proof-reader/papers/pcp-full-argument/lean/`. The tracked tree matches the reader freeze `db6737b25fdcb02eef0af5010b2f289cc3931c9e`. For all 74 returned passage associations, I matched the declarations and line starts to the frozen link rows, compared the local source bytes with those in the supplied formal snapshot, checked reviewer SHA-256 values where present, and reconciled the review’s semantic classification with the relevant source. The detailed [association and verification receipt](backend-alignment.json) records each original classification, rationale, locator and current destination.

| Account | Returned source association assessment |
| --- | --- |
| Full argument | 40 direct contextual supports, five ingredient or subclaim links, one narrower source variant. |
| Specialist | 12 selected parts supported. Three rely on the reference-NP bridge. The base ZERO association supports Eq. (15), the resource association covers semantic resources, and the runtime association concerns the graph verifier. |
| Worked exposition | 15 local selections supported, including contextual specializations. One used the wrong Hadamard label domain. |

The direct classifications apply to the selected content in context. For example, the forward endpoint uses the concrete `InNP Machine.PolyTimeRel L` definition and the witness prefix applies to all branches. The compressed classical NP statement also uses the separate `PCP.ReferenceNP.inNP_iff_mem` theorem at `PCP/Complexity/ReferenceNPConverse.lean:39–41`. The local statement, its assumptions and the execution status remain distinct.

## Accepted repairs

| Selection | Source correspondence and repair |
| --- | --- |
| Full argument, digit encoding | `PCP/Algebraic/SetMultilinear.lean:67–69` defines formal polynomial substitution. `decode_encode:89–98` uses the strict natural-degree bound and replaces the digit remainder by the original exponent. `eval_encode:101–107` proves the pointwise evaluation identity. `encode_injective_on:116–121` applies the decoder to equal encodings and uses formal recovery for both inputs. There are separate exact links for all four. The finite-field objection is valid. Over `F₂`, `Y²+Y` and zero agree on every field element, yet give different bounded-degree encodings for radix 2 and two digits. |
| Worked exposition, homogeneous Hadamard distance | `PCP/Algebraic/Hadamard.lean:119–123` operates on concatenated full coefficient-label words and halves the underlying functions' distance. Its domain includes constant coefficients, giving 16 degree-one labels at three message coordinates. The example has eight homogeneous positions. `relativeDistance_linearEncode:173–180` is exactly the half-distance theorem on that domain, and `linearEncode:137–139` supplies the parity map, with dot-product evaluation at `linearEncode_apply:141–143`. The finite check found four differing positions for all 28 distinct message pairs. The full-label link is kept at the long account's full-label passage. |
| Specialist, derived ZERO | The base statement at `PCP/Algebraic/BinaryZeroOnGridSoundness.lean:249–267` uses homogeneous proximity of both the primary table and the certificate. The derived statement at `PCP/Algebraic/DerivedZeroOnGridSoundness.lean:246–264` uses full-label error `δP` in the received input to the derived query and homogeneous certificate error `δM`. Its conclusion places `2·δP` inside the multiplier of the rejection term. The proof transfers rejection using fresh primary randomness, substitutes an exact primary encoding in the base inequality and multiplies the transfer by the nonnegative coefficient. Eq. (16) opens its result lines 261–264. Eq. (15) retains its original target. |
| Full argument, crossing agreement | The previous selection at `PCP/Algebraic/BivariateCrossingSoundness.lean:32–45` supplies the global best-approximation specialization. The prose minimizes only at the crossing, after applying bivariate agreement. The new first target is `PCP/Algebraic/PointLineCrossing.lean:246–292`, where a nearby bivariate polynomial is supplied and nearestness is required at the two selected slices. Its radius hypothesis follows by taking the comparison error at most four times the original error and applying (A26). A separate link to `PCP/Algebraic/CandidateCrossing.lean:27–89` covers the candidate-row case, with an extra bound on the candidate's own error. |
| Full argument, four remaining ingredient selections | The separate rigidity-budget inequality links `PCP/Algebraic/PointLineConstants.lean:62–72`. The introductory field bound retains `field_bounds:32–34`. Honest encoded-line completeness under strict capacity links `PCP/Algebraic/EncodedLineLowDegreeTest.lean:114–134`. The query list count retains `queries_length_le:72–74`. The algorithm description links `PCP/Algebraic/BinaryLocalCorrection.lean:45–67`. The bound (B16) links the rejection-or-wrong-bit theorem at `PCP/Algebraic/BinaryLocalCorrectionSoundness.lean:222–236`. The four simultaneous decodings open `PCP/Algebraic/ThreeColorVerifierSoundness.lean:90–97` inside `colorable_of_rejection_lt:58–112`, alongside the reusable single-pair theorem. |
| Specialist, reference NP (FA04) | The opening theorem's precise NP quantifier now links contextually to `PCP.ReferenceNP.inNP_iff_mem` at `PCP/Complexity/ReferenceNPConverse.lean:39–41`. The fixed-proof and soundness clauses still open the concrete `PCP.np_subset_pcp` theorem. The credits provide another route to the bridge. |
| Worked exposition, optional clause calculation | `PCP/Reduction/FiniteBooleanConstraints.lean:82–88` builds one flag chain per pattern, with the stated initial and final clauses and false padding. `orGate_iff:47–62` checks the exact three displayed clauses. Both displays have their own reader links. This local construction precedes graph colouring and polynomial-time reduction. |
| Index and graph cards | The 20 names formerly absent from the long published index already existed, with titles, in the reader’s declaration input and pinned Lean source. The generic builder had kept only the claim-head dependency closure. It now also retains targets selected by the paper’s passages. The inner weighted test recovers a degree-`c` field polynomial. The outer encoded-line test gives full and restricted binary bounds at degree `c·m^c`. Their cards now have distinct names in all relevant editions. |
| Evidence display | The freeze listed 24, 11 and 15 supposedly axiom-free results in the long, specialist and worked readers. All were source excerpts or the one retained statement-only compilation in each reader. Empty arrays on those records carry no axiom or proof-dependency report. The generic builder now restricts axiom-freedom analytics to extracted axiom reports. Visible scope text describes the mixed records. |

The 20 index omissions were a publication problem, so source-existence concerns do not apply. The distinct provenance states coexist legitimately. An elaborated statement alone contributes no proof replay or transitive axiom report. The long digit-encoding repair keeps the valid injectivity assertion and supplies the missing warrant. The exposition keeps the correct example and changes its source association.

## Canonical evidence graph

Four source-level declarations were added for bounded digit injectivity, homogeneous encoding, the dot-product evaluation rule and homogeneous half-distance. The six new authored support edges reflect the inspected consumer/prerequisite relations. In particular, injectivity uses formal recovery, the homogeneous-query concatenation proof uses the pointwise half-distance identity, and the derived ZERO bound uses both the transfer and the base lower bound. I left evaluation recovery without a formal-recovery support edge because its actual proof separately expands the encoded sum. The source file hashes for the added declarations were compared with the graph's pinned records.

## Frozen Markdown bindings

Each reader copy matches the canonical Markdown and the content hash stored in its authored paper binding.

| Reader | SHA-256 | Exact passage links |
| --- | --- | ---: |
| pcp-full-argument | `ea1535be69567887bbfb2fb6e82a8705aa6c8c67f38e34bff34a75f604babece` | 54 |
| pcp-specialist | `a8c7cca605a352fae8bae3b6a2ff418c036a609f7d379da28ff5d3654ee52c48` | 15 |
| pcp-exposition | `476ea070f34a13eba34ffc0e23a42c203ab243b77635b5367bc932185bbd2df3` | 19 |

The canonical graph checked in this pass has SHA-256 `9f181f7155ea13922205c6338ba22ed06be053414181f184141cd43e85e22b68`.

## Checks and scope

- All three Proof Reader `paper.py check` commands passed for the revised Markdown mirrors. Exact quotes, unique anchors, declaration names, source ranges and indexed targets were checked. The 20 original long omissions now resolve. The two named decoding cards have distinct labels.
- The static rendered-route audit checked every authored companion Markdown link against its generated Proof Reader route and actual target heading, and checked pinned direct Lean URL paths and line bounds. The Markdown copies retain their authored relative links through the explicit per-paper companion path map.
- `lean-exposition validate` passed. `inspect --view arguments` reached the expected prerequisite records from the digit injectivity, homogeneous distance and derived ZERO declarations. Graph extraction remains `not_run`, the relevant declarations remain `unverified`, and semantic certification remains false.
- Proof Reader’s 115 Python tests and 11 JavaScript source tests passed. Lean Exposition’s working layout and authored-link checks passed. Both repositories passed `git diff --check`.
- The evidence class is source comparison, finite sanity checks and tool-level validation. The pinned Lean tree was not edited. The fresh PDF checks, prose review, paper-to-graph binding hashes and browser journeys are handled separately.
