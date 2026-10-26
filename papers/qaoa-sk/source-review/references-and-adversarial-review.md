# References and adversarial review

The pinned manuscripts state full relative support for every admissible
zero-temperature SK minimizer and use scalar value identities to construct
QAOA words approaching the ground-state energy in the thermodynamic-first
limit. The citation ledger below separates imported results from historical
credit; the boundary checks identify what must survive any shorter account.
This is source correspondence and literature review, not a fresh Lean or
Comparator result or independent expert acceptance.

All OpenAI source links use commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. In the locators below, **P** is
`preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/build/`
and **Q** is
`preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/`.
Dates attached to arXiv versions are submission-history dates, separate from
journal years and manuscript title-page dates. Primary records were checked
on 23 October 2026.

## Primary citation ledger

| Manuscript key | Exact work and edition | Role in the inspected argument |
| --- | --- | --- |
| `AC2017` | Antonio Auffinger and Wei-Kuo Chen, **Parisi formula for the ground state energy in the mixed p-spin model**. [arXiv:1606.05335v2](https://arxiv.org/abs/1606.05335v2), 28 June 2016; v1, 16 June 2016. *Annals of Probability* **45**(6B) (2017), 4617–4631; [DOI](https://doi.org/10.1214/16-AOP1173). | **Imported:** the zero-temperature ground-state variational formula and attainment. Theorem 1 states the infimum formula; the proof of Lemma 3 constructs an admissible coefficient attaining it when combined with the upper bound. This is the precise import at [P/main.tex:94–107][p-existence] and [Q/sections/03-classical-optimization.tex:23–48][q-existence]. Neither selected formal theorem concludes that a minimizer exists. |
| `ACZ2017` in P; `ACZ2020` in Q | Antonio Auffinger, Wei-Kuo Chen and Qiang Zeng, **The SK model is infinite step replica symmetry breaking at zero temperature**. [arXiv:1703.06872v2](https://arxiv.org/abs/1703.06872v2), 17 June 2021; v1, 20 March 2017. *Communications on Pure and Applied Mathematics* **73**(5) (2020), 921–943; [DOI](https://doi.org/10.1002/cpa.21886). | **Historical distinction:** Theorem 1 proves infinitely many support points; Remark 1 explicitly distinguishes interval support. Infinite support does not exclude gaps. The keys refer to the same work, not to different support theorems. |
| `Chen2026` | Hong-Bin Chen, **FRSB in the SK spin glass: convergence to full-interval support at zero temperature**. [arXiv:2607.18032v1](https://arxiv.org/abs/2607.18032v1), 20 July 2026. | **Prior same conclusion and credited mechanism:** Theorem 1.3 states full support on `[0,1)`, smooth absolute continuity and no atom at zero. OpenAI explicitly acknowledges the same support conclusion and cites the regularity argument at [P/main.tex:133–147][p-credit]. Its separate coercive proof must not be presented as the first appearance of full support. The arXiv authorship disclosure credits ChatGPT 5.6 with proof arguments and prose while listing Chen as the responsible author; retain the bibliographic attribution and disclosure separately. |
| `FGGZ2022` | Edward Farhi, Jeffrey Goldstone, Sam Gutmann and Leo Zhou, **The Quantum Approximate Optimization Algorithm and the Sherrington-Kirkpatrick Model at Infinite Size**. [arXiv:1910.08187v4](https://arxiv.org/abs/1910.08187v4), 2 July 2022; v1, 17 October 2019. *Quantum* **6** (2022), 759; [DOI](https://doi.org/10.22331/q-2022-07-07-759). | **Imported:** fixed-depth, fixed-parameter infinite-size energy formula and concentration. Its finite-depth evaluations do not establish convergence as depth tends to infinity. Q's definition of `v_p` invokes this work at [Q/sections/01-introduction.tex:95–118][q-main]. |
| `BFMVZ2022` | Joao Basso, Edward Farhi, Kunal Marwaha, Benjamin Villalonga and Leo Zhou, **The Quantum Approximate Optimization Algorithm at High Depth for MaxCut on Large-Girth Regular Graphs and the Sherrington-Kirkpatrick Model**. [arXiv:2110.14206v3](https://arxiv.org/abs/2110.14206v3), 7 July 2022; v1, 27 October 2021. TQC 2022, *LIPIcs* **232**, 7:1–7:21; [DOI](https://doi.org/10.4230/LIPIcs.TQC.2022.7). | **Imported:** fixed-word tree-to-SK identification. Q cites Theorem 1 and equations (2.3), (2.6), (3.11), (6.1)–(6.3), and adjusts the tree-cost sign in [Q/sections/02-foundations.tex:17–45][q-transfer]. **Historical:** eventual Parisi attainment is a conjecture in this prior work, not its proved conclusion. |
| `EAMS2023` | Ahmed El Alaoui, Andrea Montanari and Mark Sellke, **Local algorithms for Maximum Cut and Minimum Bisection on locally treelike regular graphs of large degree**. [arXiv:2111.06813v2](https://arxiv.org/abs/2111.06813v2); *Random Structures & Algorithms* **63** (2023), 689–715. | **Imported in the separate positive-temperature route:** a finite-step message calculation, applied in [Q/sections/07-positive-temperature.tex:310–316, 369–444][q-positive-steps]. The exact v2 displays (2.21), (4.5) and (4.18) have the bounded factor and endpoint discrepancies described below; Q uses the corrected local form and supplies spatial Lipschitz regularity on its compact strip. This comparison does not certify the general theorem or the QAOA construction. |
| `BKL2026` | Sami Boulebnane, Abid Khan, Minzhao Liu, Jeffrey Larson, Dylan Herman, Ruslan Shaydulin and Marco Pistoia, **Spin-Boson Mapping of the Quantum Approximate Optimization Algorithm**. [arXiv:2505.07929v2](https://arxiv.org/abs/2505.07929v2), 22 April 2026; v1, 12 May 2025. Journal-accepted edition, *Physical Review Letters* (2026); [DOI](https://doi.org/10.1103/2w94-rymn). | **Related representation and historical credit:** fixed-depth spin–boson mapping. Q expressly proves its own occupation, insertion and surrounding-circuit estimates at [Q/sections/02-foundations.tex:47–63][q-boson]. Numerical depth/error evidence in the prior paper is not a proof of the QAOA endpoint or a complexity bound for Q's construction. |
| `Talagrand2006` | Michel Talagrand, **The Parisi formula**. Journal version, *Annals of Mathematics* **163**(1) (2006), 221–263; [publisher record and DOI](https://annals.math.princeton.edu/2006/163-1/p04). The publisher separately records online publication on 1 March 2009. | **Imported into the alternative route:** Theorem 1.1 gives positive-temperature free energy. Q then derives the zero-temperature value by the log-sum squeeze at [Q/sections/07-positive-temperature.tex:53–80][q-positive-value]. The full-support zero-temperature theorem is not an input to this alternative scalar route. |
| `Lopatto2026` | Patrick Lopatto, **Full replica symmetry breaking in the Sherrington-Kirkpatrick model**. [arXiv:2607.11756v3](https://arxiv.org/abs/2607.11756v3); arXiv history records v3 on 16 July 2026 and v1 on 13 July 2026. The [v3 manuscript](https://arxiv.org/html/2607.11756v3) displays 24 August 2026. These source-specific dates differ; no priority chronology is inferred from that discrepancy. | **Imported into the alternative route:** Theorem 1.1 supplies support `[0,q_beta]`, smooth density below `q_beta` and an endpoint atom for zero field and `beta > 1`. Q also cites Lemma 2.2, Proposition 2.4 and Lemma 2.5 for diffusion/regularity facts; [Q/sections/07-positive-temperature.tex:80–122][q-positive-inputs] specifies v3 and the field/Hamiltonian normalization. |
| `AC2015` in Q | Antonio Auffinger and Wei-Kuo Chen, **On properties of Parisi measures**. [arXiv:1303.3573v1](https://arxiv.org/abs/1303.3573v1), 14 March 2013. *Probability Theory and Related Fields* **161** (2015), 817–850; [DOI](https://doi.org/10.1007/s00440-014-0563-y). | **Alternative regularity citation:** Q invokes Propositions 1–2 and Appendix Proposition 5, equation (66), at [Q/sections/07-positive-temperature.tex:97–109][q-positive-inputs]. This is not a theorem that all overlap scales have positive mass. |
| `JT2017` | Aukosh Jagannath and Ian Tobasco, **Some Properties of the Phase Diagram for Mixed p-Spin Glasses**. [arXiv:1504.02731v2](https://arxiv.org/abs/1504.02731v2), 22 December 2015; v1, 10 April 2015. *Probability Theory and Related Fields* **167** (2017), 615–672; [DOI](https://doi.org/10.1007/s00440-015-0691-z). | **Alternative variational citation:** Proposition 1.1 and Corollary 3.10 give support-point self-consistency, cited at [Q/sections/07-positive-temperature.tex:107–109][q-positive-inputs]. Equality at support points alone does not show that the support fills an interval. |

The bibliographies are themselves pinned at [P/references.bib][p-bib] and
[Q/references.tex][q-bib]. Their keys are local identifiers: in particular,
`AC2015` in P instead denotes Auffinger–Chen, **The Parisi formula has a unique
minimizer**, [arXiv:1402.5132v3](https://arxiv.org/abs/1402.5132v3), 5 September
2014, published in *Communications in Mathematical Physics* **335** (2015),
1429–1444, [DOI](https://doi.org/10.1007/s00220-014-2254-z). A merged bibliography
must disambiguate these two works. Likewise the `ACZ2017` key is not the date
of the cited v2. The explicit same-conclusion credit to Chen rules out
attributing full support solely to the September OpenAI manuscript; this
review does not adjudicate a broader priority claim.

The EAMS v2 comparison is local. Its Proposition 2.1 and the proof of
Lemma 2.8 carry a $1/k$ factor absent from displayed (2.21). For the
constant first-step message rule, take the allowed Gaussian weights
$Y_o^0=g_o$ and $\widetilde Y_v^0=g_v$. The weighted left side is
$1/k$, while the printed right side is $1$. With both weights equal
to one, both sides vanish, so that unweighted example would not detect
the missing factor. Reindexing the adjacent-time sum from Proposition 2.1
through Lemma 4.3 gives $r=1,\ldots,L-1$, while displays (4.5) and
(4.18) print $2,\ldots,L$. A two-step coefficient changing sign between
the two sampled times makes those finite expressions differ. In particular,
$\delta=\varepsilon=1/4$, $L=2$ and spatially constant
$a_0=a_1=1$, $a_2=-1$ give a discrepancy
$4\delta\sqrt{k-1}$ in the printed Theorem 4.1, which cannot be
absorbed in its degree-independent constant. This refutes that literal
finite-step statement, without refuting the corrected continuum result. At fixed
positive temperature and on the bounded strip used by Q, the endpoint
difference is $O(\delta)$. These checks support Q's narrow correction;
they do not refute or repair EAMS's continuum theorem.

## Boundary checks for every downstream account

1. **Keep the two formal APIs separate.** `SKSupport` uses an order parameter
   on the subtype `[0,1)` with a zero extension, a `BrownianSystem`, and its
   own diffusion predicate. `SKValue` uses a function on all of `R`, a
   `BrownianSpace`, and a stopped-process formulation. Matching mathematical
   notation is not a checked conversion between those structures; the
   scalar proof does not import the support proof tree. Any claimed formal
   composition must exhibit the conversion, preservation of the control
   value and minimizer predicate, and correspondence of the chosen diffusion.
   See the [full-support interface](full-support-interface.md) and
   [scalar-value interface](scalar-value-interface.md).

2. **Do not erase the minimizer hypothesis.** Both selected interfaces
   quantify over a supplied minimizer. A constructed diffusion is not a
   constructed minimizer. The manuscript's nonvacuous application draws
   attainment from AC2017 at [P/main.tex:94–107][p-existence]; a formal
   endpoint with no minimizer hypothesis would require an additional
   existence statement and its correspondence to the selected API.

3. **Separate two curvature moments.** With
   `a(t,x) = partial_xx Phi_gamma(t,x)`, consistency gives
   `E[a(t,X_t)^2] = 1`, whereas the value is
   `P_* = integral_0^1 E[a(t,X_t)] dt`. The former does not say
   `E[a] = 1` or `a = 1` almost surely. Nonnegativity and Cauchy–Schwarz give
   `0 <= E[a] <= 1`, which supplies the terminal-loss estimate. The exact
   formulas are adjacent at [Q/sections/03-classical-optimization.tex:50–75][q-moments].
   Full support also does not by itself imply smooth density or strict
   positivity of that density; the [proof note](full-support-proof.md)
   identifies those further arguments.

4. **Fix one witness before each transfer.** The scalar coefficients
   `A_j`, `B_i` and normalizers must come from the same fixed minimizer,
   cutoff, mesh and rounded Gaussian function. An unrelated scalar
   approximant cannot replace the function whose rooted energy is used.
   Within seed compilation, all seed gates use the same Gaussian family,
   and the entire finite seeded word is fixed before its approximants.
   The controlling passages are [Q/sections/03-classical-optimization.tex:84–142][q-witness]
   and [Q/sections/05-seed-simulation.tex:10–30][q-seeds]. These are
   manuscript correspondence obligations beyond the scalar formal endpoint.

5. **Preserve every order of limits.** The scalar mesh tends to infinity
   at fixed `T < 1`, then `T` approaches one. The construction selects
   finite smoothing and circuit approximations in a nested order, then
   freezes a single finite ordinary word whose angles are independent of
   degree, `n` and disorder. Only that word enters the fixed-parameter
   thermodynamic limit. Thus Q's theorem has the stated
   `lim_{p -> infinity} sup_angles lim_{n -> infinity}` formulation, not an
   interchange with finite-size optimization or an arbitrary prescribed angle family
   at `p = p(n)`. A nonconstructive schedule of near-optimal words can
   nevertheless be padded to any prescribed integer depth allowance
   tending to infinity; long §11.3 proves this separately. The construction
   supplies no effective angle-search or accuracy-only finite-size rate. Long §11.5
   records a later source theorem for bounded-cost-angle families. [Q/sections/01-introduction.tex:95–133][q-main] and
   [Q/sections/06-assembly.tex:7–52][q-assembly] state the quantifiers and
   schedule. The positive-temperature route instead first fixes a finite
   inverse temperature and a cutoff below its support endpoint; it still
   needs the same subsequent synthesis and seed removal.

6. **Do not promote a correspondence into a verification result.**
   Full-support and scalar-value source theorems do not contain the rooted
   realization, controlled synthesis, seed removal or complete QAOA theorem.
   Those remaining links are described in the
   [QAOA dependency review](qaoa-dependency-chain.md). Bibliographic metadata,
   static source comparison, Lean checking, Comparator checking and reader
   or expert acceptance are different evidence classes. This review closes
   citation ambiguities; it does not certify those additional proof links.

[p-bib]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/build/references.bib#L1-L125
[q-bib]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/references.tex#L6-L118
[p-existence]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/build/main.tex#L94-L107
[p-credit]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/build/main.tex#L133-L147
[q-existence]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/03-classical-optimization.tex#L23-L48
[q-main]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/01-introduction.tex#L95-L133
[q-transfer]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/02-foundations.tex#L17-L45
[q-boson]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/02-foundations.tex#L47-L63
[q-positive-value]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/07-positive-temperature.tex#L53-L80
[q-positive-inputs]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/07-positive-temperature.tex#L80-L122
[q-moments]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/03-classical-optimization.tex#L50-L75
[q-witness]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/03-classical-optimization.tex#L84-L142
[q-seeds]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/05-seed-simulation.tex#L10-L30
[q-assembly]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/06-assembly.tex#L7-L52

[q-positive-steps]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/07-positive-temperature.tex#L310-L444

## Review-driven revision and method transfer

The 25 October revision draws on ten source-assisted model critiques of the
previous edition. Their common recommendations were checked against the actual
mathematical sources, rather than accepted by consensus. The contact argument,
diffuse-mass removal, origin and terminal cases, fixed-time density transfer,
and order of limits survived those sampled checks and remain in the papers.
These critiques were not human-reader studies or fresh formal acceptance.

| Decision | Revision and its boundary |
| --- | --- |
| Make the exposition's objects usable | The zero coefficient now gives an explicit heat response, moment curve and descending variation. Its admissibility is separated from minimality; the example does not inherit a minimizer theorem. |
| Complete the elementary proof before reopening its analytic input | The three geometric gap cases are exhausted before the strict-curvature mechanism is expanded. The later explanation explicitly resets to an arbitrary comparison coefficient. This ordering is a local choice, not a universal paper template. |
| Show where strictness matters | The calculus diagram has equal endpoint slopes, so the missing area comes from strict convexity. Its curve is an exact teaching example, not an asserted SK moment curve. |
| Retain the expert paper's distinctive argument | The quantitative estimate's two uses remain central. A compact rooted-energy identification explains the adjacent correlation sum; the complete circuit construction stays in the long record. |
| Supply the independent scalar lower bound | Long §10.2 now derives Gaussian-column splitting, adaptive selection, empirical orthogonalization and the corrected expectation limit, with separate proof destinations. The finite comparison is not an efficient algorithm or a formal-model transport. |
| Preserve application ingredients without retaining supplied premises as free | Three authored application records use the same witness at the theorem and supplier. Conditional arguments remain navigable; formal-interface and ordinary-manuscript premises remain distinct. Structural validation does not check the substitution's mathematical truth. |
| Reconcile recorded checking history | The graph now reaches the retained interruption summary alongside the older plans and failures. The dated observation has an unavailable terminal outcome; it supplies neither rejection nor acceptance. |

The changes refine the existing four [transition skills](../../../skills/README.md)
and their shared [maintenance loop](../../../docs/authoring.md#use-and-improve-the-transition-skills).
No external repository or installed home-directory skill is required to follow
that method. The following transfer checks explain the scope of the new guidance.

| General lesson and owner | Two distinct checks | Case the rule must reject |
| --- | --- | --- |
| A theorem application preserves a common witness and the suppliers' own premises; source-to-graph | A constructed diffusion supplies one premise while minimality remains free. Attainment supplies one manuscript minimizer before the separate classical algorithm applies full support. | A supplier that itself assumes the supposedly discharged premise cannot make the result unconditional; the regression fixture retains it. |
| A detailed account must explain the construction behind its promised endpoint; graph-to-long | The adaptive offset bound is distinct from its empirical expectation limit. The circuit's Gaussian-law matching is distinct from its energy identification. | A helper name, source inventory or checked finite example cannot stand in for either missing argument. |
| A short account retains the observable used by the next construction; long-to-short | The adjacent correlation sum needs its rooted-energy identity. The spatial moment inequality needs its fixed-time passage before it can force density. | Matching one number, or passing a time derivative without justification, does not supply the required transfer. |
| A teaching example isolates the hypothesis being taught; record-to-expository | For a nonconstant two-point variable and the function $x^2$, strict Jensen excludes equality. For a strictly increasing derivative, the secant inequalities differ from those of an affine function. | An affine function satisfies weak convexity and permits equality; it cannot illustrate a strict deficit. The SK diagram is a local use of this general choice. |

These are source and author checks of a method's scope, not measured learning
effects. A fresh reader attempt remains necessary to assess comprehension of
the revised exposition. Exact editions and passage bindings must be refreshed
after any subsequent change; the reviews of the previous edition remain history.

A subsequent layout review replaced eight prose-heavy tables in the long
record with full-width explanations, preserving their hypotheses, proof
destinations and passage identifiers. Three compact mathematical tables remain:
feasible measure changes, the rational coefficients and the gap cases. The
authoring guide now distinguishes a useful tabular comparison from paragraphs
compressed into columns; the latter failed at the actual reading size.

### Further chronological and source review, 25 October 2026

Ten further advisory returns examined edition `c0b43c1`. Four source-assisted
agent workstreams checked their proposals against the papers, retained originals
and formal definitions. A separate sequential reading scrutinised the revised
short accounts; neither that reading nor the earlier returns were blind or
human-reader studies.

Returns 01–04 supported the contact-and-area proof and its separate endpoint
cases. The exposition preserves both figures and the proof, states the inputs
needed before an optional stochastic calculation, explains the short-step
control comparison, and demonstrates continuous-mass removal on its existing
candidate. The initial zero-gap strict inequality now explicitly requires
positive time. The finite-spin consequence completes the opening question
before the optional analytic explanation. Additional proposed figures and a
longer prerequisite course were declined because existing examples supply
their jobs once the connections are explicit.

Returns 05–07 informed expert register, selection and credit. One spatial
expectation is now visible in both applications, with the fixed-time statement
made precise in the long record. The derivative correction's purpose precedes
its auxiliary quantities; an actual smooth model delimits pointwise positivity.
Local citations credit Chen's terminal estimate and classical consequence, and
Sellke's exact v4 finite-cutoff cancellation. The circuit target precedes its
finite construction, and the coefficient pairing identifies the energy
observable. The full synthesis remains in the long record.

Return 08 prompted a continuous route through support, terminal value, finite
Gaussian correlations and the ordinary circuit word. Independent contact and
Gaussian-comparison proofs now have their own mathematical section, separate
from formal-interface discussion. Seed initialization and the formula class
are defined before their estimates. The [heat-family lower bound](../long/reasoning-record.md#heat-lower-bound)
combines the exact example with the general predictable-correlation comparison;
it carries no novelty or formal-acceptance claim.

Returns 09–10 exposed correspondence and scope defects. The scalar endpoint
passage no longer reseeds a conditional helper's internally supplied premises;
its three clauses retain their actual caller hypotheses. The landscape
consequence records full support applied to the same attained minimizer.
Native scope queries distinguish these applications from the conditional
theorems selected alone. Ordinary Markdown companion links and PDF destinations
are checked separately; a captured archival bundle retains source bytes and
needs a consuming view to resolve relocated references.

Two mathematical scope refinements survived a separate source check. A finite
net gives a simultaneous overlap consequence at fixed positive tolerances,
without asserting exact continuum overlaps or shrinking-tolerance rates.
The [finite-size comparison](../long/reasoning-record.md#finite-size-comparison)
applies to each chosen finite word, with a threshold depending on that word;
no common angle bound is needed for this fixed-accuracy use. A uniform
growing-depth conclusion still requires uniform bounds. The record no longer
excludes the weaker valid combination.

The local method now tests statement and passage entry against the same caller
hypotheses, distinguishes fixed witnesses from varying families in negative
scope claims, and makes optional routes usable at their departure points.
The finite overlap net and fixed-word threshold exercise the quantifier rule;
a uniform rate is its counterexample. The stochastic calculation and deferred
analytic estimate exercise the route rule; a lemma needed by the next inference
cannot be postponed. Expert prose is calibrated against actual nearby source
passages, with audience-dependent choices rather than copied wording.

The inspected exact rational checker again gives zero polynomial residual,
22 positive remainder coefficients, the margin above $1/1000$, and the stated
Itô product identities. These finite checks do not validate the analytic
hypotheses. Draft review states and formal-check outcomes are retained;
source-assisted reading and exact bindings do not establish complete proof
acceptance or measured reader comprehension.

### Examples and alternate proofs, 26 October 2026

Ten further reviews examined edition `ba7025b6`. Their suggestions were
checked against actual arguments and exact source editions. Returns 01–04
and 06 informed an operation-first exposition: a Gaussian average, two ways
to count accumulated-weight area, and the elementary substitution giving
$q_0(1/2)=1/3$ precede their abstract uses. The same weights return in the
tail-cost calculation. A decision-before-noise example makes the control's
information restriction concrete. Optional stochastic derivations follow
the complete main argument. Additional examples and figures were not added
when an existing example could perform the same explanatory task.

Returns 05–06 supplied two useful proof choices. The
[global scaling argument](../long/reasoning-record.md#global-scaling-contact)
justifies contact by signed Fubini using
$\int\gamma|q-t|\le\int\gamma<\infty$, even for infinite total mass.
The [qualitative terminal proof](../long/reasoning-record.md#qualitative-terminal-gap)
uses finite convex chords, contact and $q\le1$, without a derivative at
one. The original local-removal proof and stronger quantitative terminal
estimate remain in the long record. The graph distinguishes the alternate
ordinary support argument from the original source and formal route.

Returns 07–10 sharpened the expert paper around a named fixed-time
spatial-moment proposition. The forward/backward heat cancellation explains
the integration law; a signed certificate term identifies the joint shape
comparison's role. The quantitative margin survives spatial approximation
and gives strict density positivity, beyond what qualitative crossing alone
supplies. The circuit discussion now displays the exact finite rooted-energy
observable: the correct limit alone cannot determine its adjacent index.
The prose uses the literature's conventions with original wording and precise
credit, without claiming priority for the source results.

Three checked consequences also have explicit destinations. The
[coefficient budget](../long/reasoning-record.md#coefficient-budget) proves
$\int_0^1\gamma\le1$ and $\gamma(t)\le(1-t)^{-1}$; the earlier blanket
absence-of-bounds claim is replaced by the missing derivative constants and
effective mesh threshold. The [spatial inequality at jumps](../long/reasoning-record.md#fixed-time-jump-extension)
is an ordinary extension, not a change to the retained Lean continuity
hypothesis, and is unnecessary for either principal application. The
[finite-instance sampling consequence](../long/reasoning-record.md#sampled-finite-instance)
uses a union bound for measured energy and the maximum under the same disorder.
It gives an asymptotic joint-probability statement, without an effective size
threshold, efficient angle search or every-instance guarantee.

Nineteen selected returned calculation programs were rerun on preserved
copies, including the elementary examples, rational certificate and finite
circuit checks. All passed at their stated finite or numerical scope.
Source-assisted mathematical review and subsequent sequential reading are
neither blind readings nor human comprehension studies. Formal targets,
historical receipts and unknown corrected-replay outcomes are unchanged.
The existing local transition skills incorporate the tested lessons about
operations, quantitative margins and finite observables; the workflow remains
self-contained.
