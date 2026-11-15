# Independent AI reader review of the PCP exposition

## Edition, scope and exposure

- Reviewer: independent AI agent, not a human reader. I have model background in PCPs, polynomial identity testing, BLR/Hadamard codes and arithmetisation. An inference I can supply from that background is not evidence that the stated newcomer can supply it.
- Reviewed source: `work/lean-exposition/papers/pcp/expository/main.md`, SHA-256 `9d04a0bc03eea71be08d68854a442606c3966cf3e089c558663d411cd99365dc`; 1110 lines. Repository HEAD `40e9911a91b21733600e6b612f0a0da3b73eb961`. Author agreed to hold the source stable during this pass.
- Intended reader: mathematically literate outside complexity theory; elementary probability, polynomial arithmetic and basic linear algebra; finite-field operations taught at use.
- Question: does this edition let that reader reconstruct why a verifier reading a constant number of bits is sound, rather than list its components?
- Actual method: sequential section-sized source blocks, saving the encounter before revealing the next. This is not isolated sentence exposure, a rendered-page inspection, or a human learning study.
- Before the manuscript: read repository `AGENTS.md`, `docs/reader-review.md`, `skills/record-to-expository/SKILL.md`, installed `mathematical-reasoning` and relevant skill routing. No long record, specialist paper, original source, example checker or answer section opened before the first pass.
- Protocol limitation: an outline-search command unintentionally exposed the first lines of Answers 1–4: “The second identity alone is insufficient”; “For nonzero x, with r=x fixed, the answer uses only the”; “The difference check would relate the”; and “The number of seeds would be”. Later attempts are before full answer exposure but are not pristine blind attempts. This is retained rather than relabelled as an unassisted test.

## First-pass encounter log

### Lines 1–147: opening and Sections 1–2

Read through the end of Section 2, before any polynomial encoding construction. The opening correctly distinguishes the input-reading time from certificate query complexity and fixes the prover's certificate before random choices. The K4 plus triangles example gives an actual dilution mechanism: one bad edge out of 6+3t, not a vague analogy. The two promised obligations—coherent objects and satisfaction of colouring constraints—are recoverable.

Current knowledge at the transition: the target is a polynomial-length certificate, O(log n) random bits, a fixed number of bit queries, perfect completeness and soundness at most 1/2. The NP converse is fully reconstructible by enumeration of polynomially many seeds; the inequality and the quantifier order are visible. The construction for three-colouring and the NP-to-graph reduction remain promised obligations, appropriately deferred. No unsupported mathematical inference encountered in this block. The exact computable random-budget discussion is more formal than necessary but does not interrupt the route.

### Lines 148–298: Sections 3–4

The mod-5 root example, interpolation weights and grid extension are mutually consistent. I recomputed the weights at 3 as (1,2,3) and the values of X(X−1) as (0,0,2,1,2). The explanation earns its distinction between a low-degree polynomial and an arbitrary received table before promising a test. The multivariate root bound is explicitly an input with a proof destination; this is a permitted exposition boundary, not a missing proof.

At the characteristic-two switch I can reconstruct the colour table from 1+ω=ω², so every difference of two distinct members of {1,ω,ω²} is the remaining member. The printed text supplies the relation but not that one calculation. This is a small first-use teaching opportunity for a finite-field newcomer, not a mathematical defect. It would make the residual table less of a supplied fact. The K4 assignment using all of F4 usefully proves why edge equations alone are insufficient.

Current knowledge at the transition: honest table values on H^m extend with degree h−1 in each coordinate; two low-degree polynomials are far apart if the field exceeds their degree; colouring reduces to two residual polynomials vanishing on a grid, not throughout the ambient field. I cannot yet choose H,m,Q, query the arbitrary received table reliably, or test grid vanishing. Those are explicitly the next obligations. No hidden inference has yet required model-specific PCP knowledge.

### Lines 299–376: Section 5 and Question 1

The ideal-decomposition example and its packaging into M teach the exact operation later consumed. I computed P(2,2)=6+8=14=4 mod 5, and M(2,2,2,2)=4. Crucially, the text distinguishes an ambient identity from grid vanishing and explains why both M identities imply the latter. “Suitable degree bounds” is an accepted deferred obligation; the soundness distance calculation will need the actual bound on the composed polynomial M(X,Z_H(X)).

First response to Question 1, before opening Section 11: choose M(X,U)=1 and P(X)=1. The second identity holds identically, but P fails to vanish anywhere on the grid and M(X,0)=1. Therefore the first check cannot be dropped. This response was primed by the accidental answer-opening fragment recorded above; it is a model reconstruction with the displayed question, not a blind outcome.

Current knowledge at the transition: grid vanishing can be certified by two polynomial identities, each evaluable with a bounded number of intended values. The remaining special-point issue is correctly exposed: global closeness does not ensure accuracy on (x,0) or (x,Z_H(x)). I still need the promised correction procedure and low-degree testing contract.

### Lines 377–499: Section 6

The point-versus-line theorem is clearly identified as an accepted deep input, with quantitative hypotheses. The proof sketch supplies its role without pretending to prove it. The base-3 encoding is an actual worked calculation: at λ=2 the triples are (1,2,4), (1,3,4), and 12+4+3=19=4 mod 5. It correctly warns that arbitrary decoded fixed-degree tables need not retain the special honest monomial form.

First-use stall at lines 458–460: “a generator of the field's multiplicative group” is not defined at the declared prerequisite level. I know from model background that it means an element whose powers enumerate all nonzero elements and that finite fields have one. A newcomer has not been told either fact. The local repair is one definition and an explicit accepted existence fact; no group-theory excursion is needed. These special nodes matter for the converse, so replacing the phrase by “distinct nodes” would erase an assumption.

The correction calculation is complete: nonzero a_i makes v↦u+a_i v uniform, interpolation succeeds if all c+1 sampled values are correct, and the union bound does not need independence. This directly repairs the special-point concern from Section 5. The fixed-degree converse is explicitly a theorem input, not something this example proves.

Current knowledge at the transition: high-degree line values can be encoded as a fixed-degree polynomial in more variables, low-degree testing produces a nearby polynomial, and random local correction can recover its values at designated points. Still owed: the degree after substituting powers into an arbitrary decoded polynomial, how all table-wise distances are aggregated, and how a whole field answer is checked using constant bits. The first is only called “somewhat larger” at this point; later quantitative use must not silently retain the honest degree d.

### Lines 500–627: Section 7 and Question 2

The Hadamard word and the exact 18/64 rejection count are reconstructible. The argument for equal distance 1/2 explicitly pairs zeros with ones. The correction example makes its two sampling marginals visible and separates the x=0 case. These are accepted teaching mechanisms.

First response to Question 2, before full answer exposure: for fixed nonzero x, put one corruption at x and none at zero. With r=x the procedure returns g(x)+g(0), hence is wrong on every execution despite an error fraction only 1/2^t. The proof needed each queried location to be uniform on the whole word; determinism provides no averaging over the corruption set. At x=0 the two equal queried entries cancel, so this counterexample requires nonzero x. The earlier outline exposed the answer's first clause about nonzero x and r=x, so this is not a blind attempt.

The transition to H3 teaches the relevant distinction: linearity as a function of the polynomial label is weaker than being evaluation at a binary message. The inconsistent assignment to Z1,Z2,Z1Z2 is an effective counterexample. I can reconstruct why bilinear multiplication permits a degree-at-most-three label for a linear observation of u³−1. The exact product-test equations and their soundness bound are not supplied in this block; they need to appear as a precise theorem input if later soundness uses them. Merely naming “tests of products and of the constant label” is not yet that contract.

Current knowledge at the transition: unequal field elements can be compared with one random binary linear observation; local correction protects prescribed labels; degree-three labels support the needed algebraic observations. I do not yet know whether passing the actual ten-query code test supplies one field element, its distance/error constants, or how the outer line test and inner code test compose. Those are necessary, rather than optional, next inputs.

### Lines 628–705: Section 8

The weighted-label identity is clear and recovers the use of interpolation coefficients without reading the whole field element. The shared-polynomial warning is exactly the right coherence requirement. The rejection rule for a refusing corrector is also visible.

First consequential contract stall at lines 649–668: “The combined low-degree theorem supplies one polynomial close” lacks both a rejection-rate hypothesis and a distance conclusion; the outer corrector's theorem is only said to depend on three quantities. At lines 688–696 the prose deducts “controlled errors” from the ideal rejection probability and asserts a positive remainder. As of this encounter I cannot perform that subtraction, determine when it is positive, or see how a bound involving the corrector's own rejection probability avoids circularity. Earlier standalone BLR and fixed-degree bounds do not supply the missing combined contract. This is the first substantial gap relative to reconstructing the soundness argument, even if a later section repairs it.

Current knowledge: I can explain why label comparison and special-point correction are needed. I can only state conditionally that a ZERO test rejects if its total answer-error budget is smaller than its ideal rejection probability. I cannot yet derive a constant gap for the actual verifier. The reference to the full argument acknowledges omitted constants, but at least the quantitative shape of the composition inequality is required in the exposition to execute its promised inference.

### Lines 706–776: Section 9 and Question 3

The eight-table inventory and seven-test list give an intelligible certificate architecture. The role of the separate difference table is clear, as is the distinction between existential decoding in the proof and work performed by the verifier. Perfect completeness is reconstructible from the honest constructions.

For soundness the text says each component rejects rarely when the conjunction rarely rejects, which is valid without independence. But the promised quantitative bridge is still absent: neither the difference test's disagreement bound nor the ZERO-test error budget is stated. “Very close”, “much greater disagreement”, and “then force” identify the logical structure but do not show a parameter regime satisfying it. The reader can trace an implication conditional on the supplier theorems being strong enough; the reader cannot check that they are strong enough. This is more consequential than omitting a proof of a correctly stated accepted theorem.

First response to Question 3 before full answers: the difference check observes homogeneous linear labels, so it could identify χ′_linear(x,y)=χ_linear(x)−χ_linear(y). The ZERO checks observe cubic expressions and would constrain χ_cubic and χ′_cubic instead. Without a common decoded interpretation, the exact relation from the difference check does not relate the two polynomials used to infer vertex and edge validity; the final colouring conclusion fails. This exercise assesses coherence of decoded objects and works for that purpose, but does not assess the quantitative soundness step missing above. The outline preview exposed only the answer's opening “The difference check would relate the”.

Current knowledge: all seven checks have a purpose and their ideal exact implications lead to a proper colouring. I cannot compute or bound the minimum rejection probability for an arbitrary false proof, nor check the thresholds selecting the four decoded polynomials. Author and parent notified before proceeding.

### Lines 777–938: Section 10 and Question 4

The parameter choice establishes the address budget with explicit inequalities. I can check |F|≥10^6D³ after D=4s⁴ is asserted, and can follow the O(a³) label budget. However, D=4s⁴ appears without deriving it from the arbitrary decoded degree-four polynomial and its power substitution. A short calculation would close the “somewhat larger degree” obligation retained from Section 6: each substituted variable has exponent at most (s−1)s³, and a degree-four monomial therefore has substituted degree at most 4(s−1)s³<4s⁴. The legitimate bound on the honest polynomial and the choice of base s must also be named at their introduction.

The zero-sampling workaround is unusually well explained: it changes rejection by a factor, not acceptance by that factor, and preserves a constant gap. The repetition proof is complete, including the same fixed certificate and independent-seed requirements. The enormous displayed γ is an asserted result; its value does not retrospectively provide the missing soundness derivation from Section 8.

First-use reduction gap at lines 886–899: enumerating fixed-arity forbidden assignments gives clauses of a fixed but possibly larger width. The next construction handles only a∨b∨c. The missing reduction from bounded-width clauses to three-literal clauses needs one explicit chain-of-auxiliary-variables sentence (or a precise accepted 3-CNF reduction input). The NAE and colouring gadget calculations themselves are sound and checkable. For (0,0,1), new colours (1,2,0) satisfy all three literal restrictions and the triangle edges.

First response to Question 4, before full answers: no. The exhaustive run would have 2^{√n} seeds, which is not bounded by any polynomial in n, so that proposed deterministic witness checker is no longer polynomial time. This does not prove the language is outside NP; it only removes the given converse argument. The outline preview revealed the answer's first words “The number of seeds would be”.

Current knowledge: the polynomial-size certificate and logarithmic randomness claims are reconstructible conditional on the unproved degree assertion and the stated implementation theorem. The amplification argument reaches 1/2 once a fixed gap is accepted. The argument producing that gap is still only qualitative.

### Lines 939–989: answers and reconstruction task

Full Answers 1–4 were opened only after saving the corresponding responses. They agree with those responses, including the nonzero-x exception and the distinction between failure of an NP proof and evidence of nonmembership. This agreement is limited by the preview contamination already recorded.

First response to the final reconstruction task, before long-record/source access: the special set (x,0) can occupy a tiny fraction of the full domain, so a received table can report zeros there while the nearby decoded M has nonzero values there. Direct reads would test the adversary's exceptional entries rather than M. Choose a random line through the desired point, use its encoded polynomial data, test that data and compare at a random nonzero line parameter with the primary table, then return the corrected origin observation if all checks pass. Treat refusal as rejection. If all data are honest, the output is the desired binary observation of M. For dishonest data, a quantitative correction theorem must make an incorrect returned observation rare when the relevant tests rarely reject and the primary table is close. Compare the actual ZERO test with the ideal test of M(x,0)=0 and the second identity. A false polynomial identity rejects at a random x with probability at least 1−degree/|F|, or half that after the random binary observation. If all correction/decoding errors together are smaller than that ideal rejection probability, the actual test still has a fixed rejection gap. The decoded M must be the one whose closeness the correction theorem uses and whose identities enter the grid-vanishing implication.

This reconstructs the qualitative mechanism but cannot give the correction inequality or establish its required margin from the exposition. That is a precise limit of the attempt, not a claim that the model or a human independently completed the soundness proof. The model's prior PCP knowledge also informs the reconstruction.

### Lines 990–1110: Section 12 and verification boundary

The old-test counterexample is a complete ordinary deduction. In characteristic two the fourth-power map gives (u+av)^4=u^4+a^4v^4, and summing the three order-three directions cancels the v term. The root bound proves disagreement from every quadratic over fields larger than four. The unbounded family distinguishes an actual converse failure from a small-field boundary issue. I accept the mechanism before checking the finite program. The notation F2[t]/(t⁴+t+1) at line 1028 exceeds the advertised prerequisites unless rewritten as arithmetic on four binary coordinates with t⁴=t+1; however this optional numerical comparison does not block the main proof.

The source/evidence section accurately distinguishes authored deduction, finite computation, Lean source, and independent human review. It also explicitly warns that the small examples do not instantiate the production field-size regime. I found no example-to-theorem scope mismatch in this first pass.

### Whole-paper first-pass judgment

The manuscript successfully teaches the source of redundancy, grid-vanishing certificates, weighted interpolation, random local correction, binary observations, and the need for one common decoded object. Its exercises cover indispensable hypotheses and distinguish a false conclusion from an inconclusive argument. It does not yet make the central constant-gap soundness deduction reconstructible: it states the ingredients but omits the quantitative bridge between them. This is the most consequential correction. A compact, actual error-budget calculation in Sections 8–9 should replace the qualitative assertions; it need not import all low-degree-test proofs or the final giant constant. Secondary repairs are defining a multiplicative generator, deriving the substituted degree bound, and bridging bounded-width clauses to 3-CNF. No human comprehension or learning gain was assessed.

End of sequential first pass. All 1110 source lines were read in order, in the blocks logged above. Source hash was rechecked unchanged. No long record, specialist paper, original source or example-checker source had yet been opened.

## Post-pass diagnosis and checks

The first-pass review file, through the preceding paragraph, was frozen before source checks at SHA-256 `313fc6f5797fd80ccd93a494bd954a5d77e08f097f8a39aba44348b4fb5a888f`. Everything below is later diagnosis or re-review and does not replace those observations.

### Long-record comparison

Read the relevant source account after the first pass: `papers/pcp/long/reasoning-record.md`, hash `f16eb27fb4fc5a641de3fd6661623e8dbf637e251dbcd539370f35eade050fa8`. Actual coverage: set-multilinear encoding (765–813); BLR, Hadamard soundness and row decoding (867–989); encoded-line testing, correction, ZERO and derived-oracle transfer (1076–1295); assembled soundness (1431–1518); bounded-arity Boolean reduction and the NAE transition (1745–1785). Other sections were searched for headings and source locators, not read as a full proof audit. No original Lean files or source paper were needed to diagnose these editorial omissions, and no new formal verification was performed here.

The long record confirms that the missing estimates exist and precisely identifies the repair:

1. The combined theorem has E(c)κ≤1/(4·10⁶) and Q≥10⁶D³ as hypotheses. One decoded polynomial has both full-label and homogeneous-label distances at most S(c)κ. The same witness is essential, and there is no assumed closeness of untrusted auxiliary rows. This resolves the missing code-test contract by presenting its combined consumer theorem; the exposition need not add the entire Hadamard proof.
2. Outer correction bounds the probability of either rejection or a wrong returned bit by C(c)R_a+δ+D/[2(Q−1)], averaged over a random homogeneous label. It does not guarantee every prescribed label or assume R_a small. If the enclosing ZERO test rarely rejects, each corrector's rejection event is contained in that event. This is the missing non-circular inference.
3. After fresh two-query derived reads, failed grid vanishing implies (1−5Dh/Q)/2 ≤ (1+2C_c)(κ+2ε)+2ε+5D/(Q−1), with ε=S_cκ. The factor 1+2C_c multiplies the derived-read error as well as κ. The exposition must preserve that factor.
4. The difference check gives ideal rejection at most κ+3ε, whereas distinct decoded polynomials would give at least (1−D/Q)/2. With Q≥100Dh and κ below a fixed minimum, the former is below 1/16 and the latter at least 3/8. The corresponding ZERO upper side is below 1/16+1/8=3/16, while its lower side is at least 3/8. These explicit margins establish the constant gap without needing the final giant numeral.
5. The arbitrary decoded degree bound is cb^c because a degree-c monomial has at most c variable occurrences and each substituted variable has degree below b^c. It differs from the honest degree bound <b^c. The production choice b=s,c=4 gives D=4s⁴.
6. The actual formal clause reduction uses prefix mismatch flags for each forbidden local pattern, then encodes each OR gate with three clauses. I withdrew my first generic “clause-splitting chain” remedy in favour of this source-faithful mechanism. The observed missing bridge remains the same.

These are omitted exposition contracts or calculations, not discovered mathematical errors in the underlying argument. The author accepted the main gap and planned a repair. Acceptance of that plan is not acceptance of a revised manuscript.

### Finite example verification

Read and executed both existing programs with ordinary `python3`; both exited 0:

- `papers/pcp/expository/check_examples.py`, hash `743563475ac1fb850d79537fb89291a03980a182d80115a94169988be30ee118`. Actual output: corrected GF16 nodes [2,4,8], weights [12,5,8]; X⁴ old-test acceptance 256/256, corrected acceptance 16/256, no quadratic representation; BLR acceptance 46/64; correction counts [8,6,6,6,6,6,6,6]/8; grid P(2,2)=4; GF4 residual matrix with ones precisely on its diagonal; repetition 27/64.
- `papers/pcp/expository/check_exposition_examples.py`, hash `93daee0c4077a7f2daf7196ce21e85b881a27c7f7688b43b85d7256a3a7372f3`. Checked all 81 K4 assignments; triangle dilution for t=0…11; all 125 mod-5 quadratics for the interpolation formula; both M identities at all 25 ambient points; all five digit substitutions; all 256 label-linearity pairs for the non-evaluation counterexample; all eight NAE Boolean cases and gadget extension equivalence.

The computations confirm the manuscript's concrete numerical examples. They do not establish the general PCP theorem, the large-field testing bounds, a Lean replay, or reader understanding.

### Method disposition

The relevant existing record-to-expository rule already requires the last established fact, next required conclusion and local quantitative inference to be visible. The missing soundness margin is an application failure of that rule, not evidence that a new global instruction is needed. Preserve the initial encounter separately from this diagnosis. The current question set covers structural prerequisites but needs one changed-budget task if the revised route is meant to assess the new quantitative inference. That request was sent to the author; no such attempt has yet occurred.

## Revised-edition review

Pending author notification and the successor source hash. No revised text or rendered edition has been accepted yet.

### Fresh changed-budget task, before author answer

The author sent a new task separately, after the source diagnosis: a false grid condition implies ideal rejection at least 3/8; actual rejection is at most κ; changing actual answers to ideal ones changes the verdict with probability at most 4κ+1/16. Determine whether κ≤1/32 and κ≤1/16 respectively rule out the false condition, and interpret the boundary. No answer to this new task had been seen. Prior assistance includes the long-record quantitative proof above, so this assesses application of that supplied mechanism, not discovery or an unassisted first reading.

First response: couple the two verdicts. Ideal rejection is at most κ+(4κ+1/16)=5κ+1/16. With κ≤1/32 this is at most 7/32, strictly below 3/8=12/32, a contradiction; the grid condition therefore cannot be false. With κ≤1/16 the bound is only 3/8, so equality is permitted and there is no contradiction at the boundary. The estimates alone do not certify grid vanishing in that case, but also do not establish a false grid condition or refute any PCP theorem. Any strict κ<1/16 would restore the strict comparison. This attempt uses both the actual rejection term and the verdict-change term; omitting the former would give the wrong boundary.

### Readback of the actual revisions

The author first supplied edition `d05bf328080e08bc04d9609acd65d10a978126a5438fe528eb939b313ed7df69`. I read its revised degree/generator passages and the complete Sections 8–9 route. Two subsequent narrow updates supplied the honest-capacity/field checks (`7dff5d7bd951077e66dea1d1112eea5a4916ff7d5ce758e84c8f34477b3af692`) and the certificate-degree derivation (`2e2333ca4727a5f8d510f5de8f184a4139f33122ae2d12ca3d29f2b9bec4d913`). The last hash is the accepted source edition for this bounded re-review.

Actual revised coverage: Section 5's quotient and certificate degree bound; Section 6's arbitrary decoded-degree calculation and multiplicative-generator definition; Section 8's combined decoding theorem, same-object distance guarantee and outer-correction inequality; Section 9 from perfect completeness through the full accumulated-error proof; Section 10's capacity, field inequalities and actual Boolean-clause mechanism; the separately posed Question 5 and later Answer 5; and the finite-field arithmetic explanation in Section 12. The initially reviewed source was read in full; this successor was read at the changed passages and their connected proof routes, not presented as a fresh blind whole-paper reading.

The original substantive objections are resolved in those passages:

- The accepted combined testing theorem now has explicit hypotheses and the same polynomial on full and homogeneous label spaces. It supplies exactly the distance bounds the seven-check argument consumes.
- The corrector inequality now includes refusal and wrong-return events, states the random-label averaging boundary, and explains why refusal probability is bounded by the enclosing test after averaging over requested targets. The alleged circularity is resolved rather than ignored.
- The difference check's replacement cost is 3ε. The ZERO inequality preserves `(1+2C)(κ+2ε)+2ε+5D/(Q−1)`. With the stated field conditions its false-case lower side is at least 3/8 while the upper side is below 3/16. Thus the proof now establishes a constant gap through an actual contradiction, rather than importing the desired conclusion in “controlled errors”.
- The decoded degree D=cb^c is derived for arbitrary degree-c polynomials. The honest capacity is separately checked: the interpolation and constraint degrees are at most 5m(h−1), grid certificates have degree no greater than their residual polynomials, and 5s(s−1)<s⁴ for s≥4. The same field satisfies both Q≥10⁶D³ and Q≥100Dh, so completeness and soundness use compatible parameters.
- The OR-gate equations make the bounded-arity-to-3-CNF transition reconstructible. The quotient-field explanation now supplies the actual arithmetic operation instead of requiring familiarity with quotient rings.
- New Answer 5 agrees with the saved first response. It explicitly distinguishes a strict contradiction from equality and an inconclusive estimate. This is a useful assessment of the repaired inference, with the assistance limitations already recorded.

For additional source verification, I read the long record's honest-capacity and parameter passages (1369–1430 and 1519–1567), generator definition (195–229), the inner correction and K(c) bound (1040–1076), and the quotient-degree argument (140–171). The expressions in the revision match those contracts.

### Updated example checker and path reconciliation

The author's new checker initially lived at workspace `work/pcp-examples/check_exposition_examples.py`, hash `b1c375fa0c8ab21ed9f415cbe375ac449252bdeefc074094539925e6e8016cfe`; the repository copy still had the older `93daee…` hash when first rechecked. This was a path/copy discrepancy, not a failed mathematical test. After the author identified the owned source path, I read and ran that exact new file. It exited 0 and verified all prior examples plus all eight OR-gate cases, all 64 pairs of three-bit actual/pattern inputs for prefix mismatch flags, and exact rational bounds 7/32<3/8 and equality 3/8. The mapper was separately asked to refresh the repository copy. This review does not silently treat the older canonical copy as the newly executed program.

### Final bounded judgment

At source hash `2e2333ca4727a5f8d510f5de8f184a4139f33122ae2d12ca3d29f2b9bec4d913`, all consequential source-level issues identified in this review are resolved. Given the explicitly stated deep testing theorems as accepted inputs, the exposition now supports reconstructing why constant-query local tests yield a fixed rejection gap: common decoded polynomials, a quantitative difference identity, two quantitative grid implications, and field/encoding parameters satisfying all those requirements together. The final repetition and NP reductions then recover the stated theorem. The finite examples agree with exact computation.

This is an AI mathematical/editorial review with prior subject knowledge and recorded assistance. It is not an independent human reading, an experimental learning result, a complete audit of all original mathematical sources, or a Lean replay. No delivered PDF or browser rendition was supplied to this reviewer, so typography, page breaks and final rendered link behaviour remain unassessed by this lane. The parent owns that delivery review. The optional extra F4 subtraction example remains a teaching preference, not an unresolved soundness defect.

