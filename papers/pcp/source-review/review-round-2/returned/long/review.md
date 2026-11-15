# Independent review of the full argument

## Judgment

The long record substantially succeeds at its stated task: it explains a coherent route from polynomial tests to a concrete PCP verifier, then connects that verifier to the two directions of the NP characterization. Its strongest feature is that it preserves the quantifiers and error events at the interfaces where a superficially simpler account would become false. The central PCP claim was not refuted in this review. The inspected formal statements and selected proof bodies support its stated endpoint. This is a source-level mathematical and correspondence assessment, not a fresh kernel replay or an audit of every imported machine proof.

Two localized corrections are established. The digit-encoding paragraph needs a formal left-inverse argument before it concludes injectivity; equality of evaluations over a finite field does not supply that implication by itself. The homogeneity paragraph misdescribes the corrected source as asserting a more general claim than the scalar case actually printed in v2. Neither issue is a counterexample to the PCP theorem. The appropriate next step is a bounded revision that fixes those sentences, makes two difficult transitions easier to reconstruct, and separates reader evidence states accurately. A wholesale rewrite, constant-optimization project, or additional reviewer gate is not justified.

This response assesses the 1,931-line long source and its 43-page PDF. The first-reading account was frozen before source checking; the source checks were frozen before consulting earlier audits. Three parallel model analyses supplied algebraic, binary/literature, and Lean-interface perspectives. These are not reports of three human readers, source-owner approval, or observed teaching outcomes. The companion papers were sampled for the same claims rather than independently reviewed in full. Exact scope and omissions are recorded in coverage.json.

## The recovered theorem and its boundary

For a language of finite binary strings in the concrete certificate class NP, choose one verifier, one polynomial-time implementation, constants a, b and ℓ, and a natural-coefficient polynomial p before choosing an input x. On an input of length n, the verifier uses exactly a⌈log₂(n+2)⌉+b independent fair bits, makes at most ℓ proof-bit queries on every answer branch, and uses addresses below p(n). A yes-input has one fixed proof accepted on every seed. On a no-input, every fixed proof has acceptance probability at most one half. An infinite Boolean oracle is a convenient representation; only the bounded prefix is observable. The reverse checker guesses that prefix and enumerates the polynomially many seeds. A separate pair of concrete simulations identifies this certificate class with the pinned Complexitylib nondeterministic-machine class. [L: intro-theorem, converse; F: Theorem.lean 25–33, Complexity/ReverseConcrete.lean 33–39, Complexity/ReferenceNPConverse.lean 20–36.]

These are strong, language-uniform statements. Constant query count is an upper bound on physical bit reads, not constant total runtime or a constant number of input reads. The proof is fixed before the seed, including during repetition. The address bound covers arbitrary answer histories. The graph reduction and verifier implementation carry actual program and cost witnesses; they are not free efficiency assumptions. The enormous explicit constants establish an asymptotic existence theorem, not a practical protocol.

The open boundary of this review is evidential. We did not rebuild the pinned project, extract its axiom closure, independently verify every compiler or simulation lemma, or observe an unfamiliar human learning the construction. The manuscript itself distinguishes explanatory reconstruction from formal source authority. That distinction should remain.

## Three audience perspectives

### Source-owner perspective

The manuscript adds real value beyond the original mathematical reading guide. That guide already introduces the endpoint, definitions and source route clearly; simply restating those interfaces would not be a substantial new explanation. The long record instead reconstructs the weighted-grid proof, the bivariate error locator and clean rectangle, the ruled-surface rigidity argument, the two simultaneous binary metrics, the actual ZERO failure event, and the parameter and machine compositions. These are useful objects for a source owner to check, teach, and refer readers to. [G: docs/pcp/reading-guide.md and README.md; L: algebra-weighted-plurality through algebra-ruled-surface; binary chapter; runtime through converse.]

The main source-owner concern is exact attribution of differences. A source comment can explain why a formal theorem was formulated, but it is not authoritative evidence about what a later paper edition says. The homogeneity sentence demonstrates that failure mode. A second concern is the reader's presentation of verification: source-read, statement-elaborated, proof-built and axiom-analyzed are distinct records. The manuscript should not acquire a stronger validation claim merely because a card displays a declaration or an empty axiom list.

This perspective does not speak for Troy Lee or the original authors. No one was contacted, and the original manuscript was not changed.

### Algebraic PCP researcher

The proof is credible because the text keeps the obstruction behind each construction visible. The full generator is needed for propagation through all nonzero field elements; arbitrary distinct interpolation nodes do not establish the same characterization. The fixed-center plurality argument upgrades an average test to a pointwise correction statement. The error locator organizes inconsistent rows into a common clean rectangle. The ruled surface connects one fixed target-line polynomial to every target point. Binary soundness retains one decoded object with two distance guarantees because the later tests sample a small, structured label set. ZERO corrects values on exceptional slices rather than assuming global proximity controls them.

The main cost for this reader is navigation through a long chain of local notation and constants. The answer is not to remove hard proofs. It is to state the four mixed-plane discrepancies explicitly, motivate the ruled surface before its table of errors, give a small constants table at final assembly, and bridge the changing uses of b, m, d and Q at chapter boundaries. These changes reduce reconstruction work while preserving the argument's actual difficulty.

### Lean-aware reader

The endpoint and selected support are substantially faithful. All 46 frozen reader associations were compared with source statements, section hypotheses, relevant definitions and selected local proof bodies: 40 are direct contextual supports, five are ingredients or subclaim supports, and one is a valid variant. None was unrelated or left unresolved. “Direct” does not mean that every sentence in a highlighted paragraph is literally asserted by one declaration.

The five ingredient selections concern the numerical field bound versus the complete rigidity budget; evaluation recovery versus injectivity; a query-length theorem beside completeness; a corrector guarantee beside its procedure; and a one-pair decoder used four times. The crossing variant uses nearest approximants everywhere in the selected signature, while the prose's valid proof only needs nearestness at the selected crossing. These distinctions belong in card titles, narrower selections, or supplemental links. Several were already deliberately recorded in the earlier canonical mapping audit. They are not six newly discovered mathematical failures. [claim_checks.json: LEAN-15, 17, 19, 28, 30, 37.]

The final reference-NP paragraph is correct but too compressed for this audience. A few sentences explaining the two simulations would complete the promise of a machine-level endpoint without reproducing compiler states.

## The proof spine

| Stage | Mathematical object and guarantee | Why the next stage needs it |
|---|---|---|
| Polynomial identities | Distance, interpolation and grid-vanishing certificates, with formal-polynomial degree bounds | Express assignments and constraints as low-degree objects |
| Corrected local test | Full-generator weighted relation; small rejection gives proximity to degree ≤ c | Test a constant-degree inner encoding |
| Bivariate agreement | Arbitrary approximating rows and columns yield one bivariate polynomial | Convert local line consistency into a shared algebraic object |
| Point-versus-line theorem | Small whole-field discrepancy gives one nearby total-degree-d polynomial | Decode the outer received table |
| Digit and Hadamard encodings | Lower degree by increasing dimension; expose field observations as single bits | Keep physical query count independent of graph size |
| Binary decoding | One decoded polynomial with the required full and homogeneous distances | Make later structured observations trustworthy |
| Local correction and ZERO | Bound rejection-or-wrong output at prescribed spatial targets, averaged over labels | Read certificate values on nonuniform slices |
| Seven-check assembly | Four fixed decoded polynomials satisfy difference and grid identities | Recover one proper colouring |
| Resources and machines | Exact finite sampling, fair bits, repetition, uniform graph reduction and concrete reverse | Establish the full NP characterization |

The central invariant is not merely “each table is close to a polynomial.” It is that the same chosen objects satisfy every estimate that later checks consume. The decisive rigidity step is likewise not just high agreement: one polynomial is chosen before varying the target parameter, and a positive-probability argument forces equality of fixed field elements.

## Reconstructing the difficult transitions

### Weighted local equations become global low degree

Subtract the univariate interpolant through the first c+1 powers of a generator. The weighted relation at zero determines the next value because the final weight is nonzero. Repeating this argument traverses the entire multiplicative group; restricting the same equations to each affine line gives the exact line characterization. This is why the orbit condition matters.

For robustness, two independently parameterized weighted predictions are embedded in a double grid. Nonzero nodes make the relevant affine maps uniform. The shared double sum couples the predictions, giving concentration at each fixed center, not merely on average. Under the strict rejection threshold, the combined failure probability is below one. Hence some sampled grid realizes all desired comparisons, and the resulting fixed values must agree. The manuscript's distinction between a strict proof threshold and a smaller closed downstream threshold is correct. [L: algebra-generator-test through algebra-generator-soundness; F: GeneratorLowDegreeTest.lean and WeightedLinearCorrection.lean, audited ranges in evidence/algebra_coverage.json.]

The old unit-weight test fails for an unbounded family: q=2^(2k), c=2 and f(x)=x₁⁴. Fourth powers are additive in characteristic two, so every old local equation passes. A degree-two polynomial agrees on at most four points in each first-coordinate fibre, giving distance at least 1−4/q. Increasing k defeats any proposed absolute constant in a cubic field-size condition. The conclusion concerns the old local lemma; it does not assert that this word defeats all seven checks of a PCP verifier. The independent GF(16) script illustrates the family with 0/256 old-test rejections and exact distance 12/16. The family proof, not this finite computation, supplies the quantified contradiction. [L: algebra-old-test-counterexample; evidence/counterexample_checks.py and .json.]

### Bivariate agreement needs a common rectangle

Most columns are good by Markov. Select enough of them, then use a polynomial linear system to construct an error locator that vanishes at inconsistent positions. The specialized system has a nonzero solution; a maximal-minor construction turns that information into polynomial coefficients with controlled degree. Root bounds remove exceptional rows, leaving a common clean rectangle. Interpolation through the same columns yields one candidate polynomial, first with a coarse error bound. A transverse comparison then improves that bound to 4ε.

The manuscript earns the length of this proof. “Apply bivariate agreement” would hide both the strengthened arbitrary-approximant hypothesis and the source's explicit constants. ALMSS Theorem 69 is an antecedent with nearest approximants and existential constants; the Arora–Safra construction supplies the locator/rectangle mechanism. The long account identifies its quantitative formulation separately. [L: algebra-bivariate-statement through algebra-agreement-boost; S3, S4; evidence/algebra_review.md.]

The candidate polynomial's individual degree bound and its evaluation agreement are not interchangeable facts. The text uses root bounds at the necessary transitions. This is a useful standard against which to judge the later injectivity sentence.

### Mixed planes and the ruled surface

The fixed-parameter estimate is a necessary intermediate step. Tied nearest line polynomials cannot simply be transported by a globally equivariant choice rule. On sufficiently good lines, separation supplies uniqueness; the remaining lines incur an explicit error cost. The manuscript correctly does this rather than assuming a compatible minimizer selection.

The mixed-plane paragraph then says it bounds “four errors,” but the reader must recover their exact definitions from the preceding crossing statement. This is the largest avoidable local reconstruction burden. Displaying those four probabilities, their averaging domains and their mean bounds would make (A27) auditable. A complete replacement appears in transition_audit.md and line_edits.md. This is an exposition repair, not a discovered invalid estimate.

The ruled surface answers a different question: how can every point of one target line be represented by one polynomial? Choose Q on that line once. Put g on the zero column of the sampled surface, and f elsewhere. Every nonzero column is an oriented line with the needed uniform distribution; fixing a row also gives an affine line. The five-error crossing lemma tolerates the modified zero column even when row candidates are no longer nearest. For each y₀, the union bound plus a separate pointwise correction comparison leaves positive probability that Q(y₀)=g(x+y₀h). The sampled surface may depend on y₀; Q does not. Therefore the equality holds on the entire line. [L: algebra-fixed-parameter through algebra-degree-zero.]

A tempting simplification would remove this second geometry and say that pointwise proximity already gives a low-degree line. That implication is false without a shared polynomial. A union bound over all target parameters would also introduce an unwanted field-size cost. Retain the existing rigidity mechanism and add its purpose before the accounting. The displayed constants satisfy B/ε+γ≤0.482025<1; d=0 receives a separate correct argument.

### Binary observations preserve one witness in two metrics

Digit encoding trades high univariate degree for a constant total degree in more variables. Hadamard encoding then turns a field observation into one bit. Testing arbitrary received words requires more than showing that honest encodings pass. The Hadamard analysis recovers a linear functional, proves it preserves the unit and products, and identifies it with evaluation at one point. At r=1 the product step is absent and unnecessary; say “For r≥2” before the product argument.

The full and homogeneous label distances must concern that same point. As a concrete illustration, when r=t=3 there are 256 full Boolean polynomial labels but only eight homogeneous linear labels. Corrupting exactly those eight gives full-label error 1/32 and homogeneous error one. Thus full-label proximity alone cannot supply a uniform restricted-label bound. The example is optional in the long record and especially suitable for the worked exposition. It supports, rather than replaces, the same-witness proof. [L: hadamard-labels through hadamard-row-decoding.]

The degree bound for an arbitrary decoded line is cb^c, whereas an honest line polynomial has degree strictly below b^c. Testing low degree does not certify the special set-multilinear monomial pattern, so this larger soundness degree is necessary. The source's 2r+4 Hadamard-query bound also belongs to a different tester from v2's eight-query variant: the formal tester retains lower product checks. At r=3 its count is ten. Preserve both distinctions.

### Correction, ZERO and final soundness

The outer corrector returns either a bit or rejection. Its bound is on the unconditional event “reject or return a wrong bit,” averaged over the requested homogeneous label and internal randomness at each fixed spatial target. It is not a guarantee conditioned on acceptance and is not a guarantee for every adversarially fixed label.

The proof's two copies each of e and R_a have distinct jobs. One replacement and rejection comparison control a decoded random point; homogeneous distance compares it with the true polynomial; a nonzero-polynomial root bound transfers this to the origin; a second replacement returns to the actual corrected bit; and the last rejection term accounts for the failure event itself. This yields C(c)=2+2(c+1)K(c). The existing prose already contains the accounting; a small displayed sum would aid memory but is optional. [L: outer-correction-soundness, (B16)–(B18).]

ZERO needs correction because the slices (x,0) and (x,Z_H(x)) can contain every corrupted certificate entry. Fresh full-label masks implement derived polynomial observations with an error bound in the actual joint experiment. Substituting an arbitrarily chosen “good mask” would change the algorithm and quantifiers. The replacement loss enters through ZERO rejection and is consequently multiplied by 1+2C(c). Preserve that coefficient and the outer polynomiality premise.

The final argument chooses P, Q*, M_A and M_B once. It first identifies Q* with the difference of P by a root-bound contradiction, then applies the two ZERO implications to those same certificate polynomials. The same physical line tables supply testing and correction. Degree inflation to 5D belongs to the residual constraints; the proof does not reapply the primary low-degree decoder at degree 5D. The explicit gap is consistent with these steps. [L: derived-oracle-transfer; decoding-contract through gap.]

At c=4, the intermediate constants are K=105408, E=1054138, S=1054166 and C=1054082. The resulting g₄ is 1/71115455156448. Whole-field fair-bit implementation loses at most a factor of sixteen, and the fixed repetition count is 1137847282503168. Seven component bounds sum to 187 before repetition; the amplified bound is 212777441828092416 bit queries. These numbers explain the theorem's existential scale. The supplied arithmetic receipt checks substitutions, not the truth of the general probability argument.

## Two repairs that change the mathematical reading

### Formal substitution before injectivity

At long line 795, the preceding displayed identity establishes equality of evaluations. Over a finite field, distinct formal polynomials can agree everywhere; Y^q−Y is the simplest warning when its degree fits the admitted range. No general b^c<q assumption is available here.

Move the definition of Dec before that inference and prove Dec(Enc(p))=p in F[Y]. Each digit monomial becomes the formal monomial Y^j; linearity gives the identity for degree strictly below b^c. Applying Dec to equal encodings gives injectivity. Evaluating the formal identity gives the displayed recovery equation. The existing source proves these separately as decode_encode, eval_encode and encode_injective_on. No new hypothesis is needed. [F: Algebraic/SetMultilinear.lean 67–107, 115–121; claim_checks.json: LEAN-19.]

This is a missing warrant for a true claim. It does not justify saying the encoding, formalization, or main theorem is false.

### Correct the homogeneity attribution

The sentence at long line 864 says the account does not need the paper's more general homogeneity assertion. Bundled v2 Claim 3.7 states exactly the needed restricted case P(Y)=ηY with homogeneous L. Bundled v1 has no final homogeneity clause. The nearby Lean comment discusses a broader false assertion, but it does not describe either supplied version accurately.

Replace the sentence with a precise acknowledgment of the scalar homogeneous case of corrected Claim 3.7, or delete it. If another historical draft is meant, identify it with an actual statement. Keep the general composition identity and the nonzero-scalar label permutation. [V2: technical_tools.tex 168–188, appendix-claim-consistency.tex; V1: main.tex 829–853; F: Algebraic/HadamardComposition.lean 20–24.]

## A concrete simplification attempt

There is a valid shorter route to the weighted robustness bound. In Kaufman–Sudan's terminology, use k=c+2 forms: the center u and the c+1 points u+a_i v. The accepted vectors form the linear subspace y₀=Σw_i y_i. The manuscript's preceding argument supplies exact characterization, and a_i≠0 gives the required 2-ary independence. Theorem 2.9 then gives the threshold with denominator (2k+1)(k−1)=2c²+7c+5, matching the direct proof. [S2: Definitions 2.3, 2.5, 2.8 and Theorem 2.9.]

This removes the double-grid derivation locally, but imports a general theorem and hides the mechanism of fixed-center concentration. Keep the direct proof in the long record; add the exact substitution as a concise source connection. The specialist account can refer to either route. This is reuse of an existing result, not a new theorem.

A second optional economy is a row-threshold lemma: choose the single witness supplied on low-rejection rows and any witness on other rows; bound every required metric by the larger of its local coefficient and the reciprocal threshold, then average. That abstraction captures both rowwise passages. It saves repetition only if the local thresholds and common-witness requirement remain explicit. Neither proposal requires replacing the overall architecture.

## Organization, notation and rendered form

The chapter order is defensible: algebraic guarantees, binary implementation of those guarantees, then assembly and machines. The most technical algebra should not be moved wholesale to an appendix in a document promising the complete argument. Its purpose should be made visible locally. The introduction already gives the theorem and a useful roadmap; it does not need another general PCP advertisement.

A small notation bridge at the final chapter would help: b is the digit base in the binary chapter and becomes m in the final parameter choice; d shifts from a degree bound to grid dimension; Q is also the field-size symbol after an earlier polynomial Q. The definitions are locally correct, so a global mechanical renaming is unnecessary. Change the function-arrow introduction of the decoded P to a formal-polynomial introduction with evaluation shorthand. Replace “valid local-correction generator” by a parameter satisfying GoodNodes, maintaining the explicit distinction between that parameter and the tester's full generator.

The PDF survey found a clear, legible mathematical layout and readable reference entries. Two modest refinements remain. The source frontmatter's explanatory byline and originator attribution do not appear on page 1, although the full credit appears on page 42. Render a compact byline from the supplied metadata without inventing endorsement. Keep the four-row primary-table comparison together if possible: it currently splits across pages 29–30, with a repeated header. This is a comparison-cost issue, not clipping or a broken table.

## Reader and provenance observations

The live reader loaded the full argument, opened the main theorem and NP certificate definitions, and exposed the full SetMultilinear source including the needed left inverse. The source-pane route was useful. The normal desktop viewport was 1900×990; mobile and accessibility behavior were not assessed.

Two attempts to click the specialist companion link remained on the full-argument route; a wait for the stated destination timed out. Direct navigation to the same href loaded the specialist paper. Treat this as a bounded session observation and reproduce the normal click/history interaction before assigning a cause. A section title beginning “A high-degree…” also produced the ambiguous label “Back to §A.” Neither observation is evidence that all navigation is broken.

The more consequential presentation issue is frozen metadata. Global text says signatures are source-read and no proof dependencies or axiom reports were extracted, while one endpoint retains statement-compiled provenance. Those facts can coexist if their scopes are stated. However, analytics.free_of_axioms lists declarations whose axiom arrays are empty despite unextracted reports. Missing data cannot establish axiom-freedom. Represent the states separately and show unknown/unextracted where no report exists. The review does not allege that the manuscript falsely claimed a completed proof build. [R: edition.json, lean.scope, declaration provenance and analytics.free_of_axioms; claim_checks.json and evidence/lean_review.md.]

The live deployment was not byte-compared with the frozen edition. These UI observations and the 46 frozen source associations therefore remain separate evidence classes.

## Prior audits and selected next questions

The earlier audits were read after the independent findings were frozen. They agree with the main invariants and record several repaired historical omissions. Those omissions should not be recycled as current defects. They also clarify why some reader cards intentionally select a supporting ingredient and why formula-only highlights were omitted. Our support-role recommendations incorporate that context. A prior successful PDF check is compatible with improving a split comparison table; earlier preservation acceptance does not settle the newly located injectivity or edition-attribution issues. Details are in evidence/prior_reconciliation.md.

Two useful questions remain, neither requiring a broad research programme. First, can a subsequent reader recover the four mixed-plane events and the fixed-Q rigidity argument from the revised text without consulting Lean? A short closed-text reconstruction of those exact objects would discriminate between explanatory repair and mere extra prose. Second, can the reader's data model express missing, retained statement, proof-build and axiom-report evidence without promoting one to another? A fixture containing an unextracted empty axiom array would test the important boundary.

Optimizing the huge constants, changing the tester, or claiming general AI or human learning conclusions would exceed the commissioned task. The repair plan keeps those out of scope. The review supplies proposed changes and original findings; it does not record them as incorporated.

## Evidence key

L: papers/long/reasoning-record.md; passage names above have the prefix pcp-long-. The frozen long source SHA-256 is 1d09db7bfda9d8f7cb2a4b8cf14421c8bf8b2edb7d0391655fb8715c1dce1588. F: formal/lean/PCP, pinned revision a0ce13ed0fa264f051c1278e039596ce65557fa4. G: formal/lean/docs/pcp. R: reader/edition.json. V1 and V2: literature/abssw-v1/tex and literature/abssw-v2/tex. Line ranges and hashes are further specified in claim_checks.json and coverage.json.

S1: [Official ECCC report and revision notice](https://eccc.weizmann.ac.il/report/2026/134/), revision 1 dated 22 October 2026; confirms the Lemma 3.3 correction. Exact v1/v2 statement comparisons use the supplied TeX editions.

S2: [Kaufman–Sudan, author-hosted STOC manuscript](https://people.csail.mit.edu/madhu/papers/2007/apt-conf.pdf), Definitions 2.3, 2.5, 2.8 and Theorem 2.9. Only the relevant definitions and theorem/proof opening were inspected.

S3: [ALMSS, author-hosted journal manuscript](https://people.seas.harvard.edu/~madhusudan/papers/1992/almss-journ.pdf), Theorem 69 and the surrounding crossing/point-line results. The historical statement is not an exact source for every displayed explicit constant.

S4: [Arora–Safra, journal-format copy](https://www.cs.umd.edu/~gasarch/TOPICS/pcp/AS.pdf), §5.2, particularly Lemmas 5.2.2 and 5.2.7 and Corollary 5.2.3. The reviewed mechanism is the locator and common-rectangle construction.

The original Friedl–Sudan corrected edition and Shoup theorem were not successfully verified here. Their precise original-source assertions remain outside this review; the manuscript's self-contained exact-line proof and source-level bounded-search composition were assessed separately.
