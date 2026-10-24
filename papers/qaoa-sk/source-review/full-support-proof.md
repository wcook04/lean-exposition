# Full support: proof mechanism and formal correspondence

For the pure zero-field SK model with covariance normalization
\(\xi(t)=t^2/2\), the source theorem states that **every admissible integrable
Parisi minimizer has full relative Stieltjes support on \([0,1)\)**. It also
gives strict increase of the order parameter and the identities
\(\mathbb E\Phi_x(t,X_t)^2=t\) and \(\mathbb E\Phi_{xx}(t,X_t)^2=1\).
The minimizer is an assumption; the associated diffusion is constructed.

This is a mathematical reading and correspondence review of the public TeX
and Lean source at `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
It is not a fresh Lean build, axiom audit, Comparator replay, or an independent
verification of every analytic lemma. All links below are immutable. Source
coordinates use these public repository-relative prefixes:

- **P**: `preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/build/`.
- **L**: `lean/OAI/Probability/SKSupport/`.

## Exact assumptions and conclusion

The admissible class consists of nonnegative, nondecreasing, right-continuous
\(\gamma:[0,1)\to\mathbb R\) with \(\int_0^1\gamma<\infty\). Its Stieltjes
measure satisfies \(\mu_\gamma([0,t])=\gamma(t)\), including an initially
permitted atom \(\mu_\gamma(\{0\})=\gamma(0)\). It is locally finite, without
probability normalization or an assumption of finite total mass. Full support
uses the **relative topology** of \([0,1)\).

The value function is the bounded-control supremum with terminal payoff
\(|x|\), equivalently the approximated solution of
\[
 \Phi_t=-\tfrac12(\Phi_{xx}+\gamma\Phi_x^2),\qquad
 \mathcal P(\gamma)=\Phi(0,0)-\tfrac12\int_0^1t\gamma(t)\,dt.
\]
The controls are progressively measurable for Brownian increments. The
diffusion has drift \(\gamma\Phi_x\) and initial value zero. The Lean model
makes these choices explicit through `OrderParameter`, `BrownianSystem`,
`Control`, `IsMinimizer` and `IsDiffusion`.
For a general admissible coefficient, which may jump, the spatial derivatives
are locally absolutely continuous in time and satisfy the differentiated
equation for almost every time; a classical time derivative at every jump is
not assumed. See [P/regularity.tex:26–31](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/build/regularity.tex#L26-L31).
See [P/main.tex:53–117](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/build/main.tex#L53-L117)
and [L/Model.lean:12–88](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKSupport/Model.lean#L12-L88).
Zero field supplies spatial symmetry and \(X_0=0\); constant \(\xi''=1\)
supplies the displayed curvature formulas. These are substantive restrictions,
not notation for general mixed-spin or nonzero-field models.

## Why the proof excludes every gap

**Analytic preparation.** Put \(u=\Phi_x\),
\(q(t)=\mathbb E u(t,X_t)^2\), and \(a(t)=\mathbb E\Phi_{xx}(t,X_t)^2\).
Finite monotone step coefficients and smooth terminal data
\(M^{-1}\log(2\cosh Mx)\) approximate the control value. Monotonicity bounds
\(\gamma\) on every strip ending at \(T<1\); heat smoothing gives uniform
bounds for every spatial derivative there. Uniform value convergence and
derivative interpolation give derivative convergence. A common Brownian
coupling and Gronwall give convergence of the diffusions. Consequently
\[
 u(t,X_t)=\int_0^t\Phi_{xx}(s,X_s)\,dB_s,\qquad q(0)=0,\quad q'=a.
\]
The integrable drift extends \(X\) continuously to time one, but derivative
estimates remain on compact strips below one.
[P/regularity.tex:16–44,107–237](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/build/regularity.tex#L16-L237)

**Variational contact, not unconstrained stationarity.** In each admissible
integrable direction \(\eta\),
\[
 D^+\mathcal P(\gamma)[\eta]=\tfrac12\int_0^1\eta(t)(q(t)-t)\,dt.
\]
Adding an atom at \(s\) gives
\(G(s):=\int_s^1(q(t)-t)\,dt\ge0\). Removing a fraction of the Stieltjes
mass on any compact set \(K\) gives \(\int_KG\,d\mu_\gamma\le0\).
Local finiteness justifies Fubini; continuity then gives \(G=0\) on the
support. At an interior support point, \(G'=t-q\) and \(G''=1-a\) imply
\(q(t)=t\), \(a(t)\le1\). If zero belongs to the support, the same upper
bound on \(a(0)\) follows from the one-sided expansion of \(G\), using
\(q(0)=0\). Removal of atoms alone would not establish this contact condition
for an arbitrary measure.
[P/variation.tex:12–127](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/build/variation.tex#L12-L127)

**The difficult sign estimate.** On a positive constant interval
\(\gamma=c>0\), write \(r=cu\), \(v=r_x\), \(w=r_{xx}\), \(z=r_{xxx}\).
Differentiating along the diffusion gives
\[
 q'''=c^{-2}\mathbb E(z^2-12vw^2+6v^4).
\]
Convexity of \(\Phi\) does not control the negative term pointwise. For fixed
positive nondecreasing step coefficients bounded by the terminal smoothing
parameter \(M\), factor the diffusion density as \(f=e^{c\Phi}g\) and set
\(s=-\partial_x\log g\). Backward comparison gives
\(v>0\), \(w\le0\), \(H=w/(2r)+v\le0\), \(H_x\ge0\) on \(x>0\).
Forward comparison gives \(s_x\ge1/t\), \(s_{xx}\le0\) on \(x>0\), and
\(j=s_x-(s/r)v\ge0\) everywhere. The jump rules preserve these signs; oddness and
\(v(0)>0\) justify the quotient extensions at zero.
[P/signs.tex:17–55,195–394](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/build/signs.tex#L17-L394)

The signs make
\(R=r^2,K=rs,v,B=-2H,j,L=-rs_{xx},S=2rH_x\) nonnegative. An explicit
rational polynomial \(F_2\) satisfies
\[
 f\mathcal W(F_2)=\partial_x(rfF_2),\qquad
 z^2-12vw^2+6v^4-\mathcal W(F_2)
 \ge\frac{1661507}{1521000000}v^4>\frac1{1000}v^4
\]
when \(v>0\). Differentiated Gaussian tails make the flux vanish and all
terms integrable. Thus the derivative correction has zero expectation,
yielding \(q'''>\!0\). This is an integrated coercivity argument, not a
claim that the original integrand is positive everywhere. Only the final
moments in spatial derivatives through order four pass to the general
integrable coefficient; one further derivative bound controls evaluation on
the coupled paths. No limiting density-score ratio is required.
[P/signs.tex:396–472](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/build/signs.tex#L396-L472),
[P/certificate.tex:117–199](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/build/certificate.tex#L117-L199),
[P/curvature.tex:9–52](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/build/curvature.tex#L9-L52)

**Interior and initial gaps.** A gap makes \(\gamma\) constant. For a
positive constant, strict convexity of \(a=q'\), together with endpoint
contact, gives \(a(t)<1\) inside the gap, contradicting
\(q(b)-q(a)=b-a\). For a zero constant, the separate heat identity
\(q''=\mathbb E\Phi_{xxx}^2>0\) gives the same contradiction. Strictness
uses full spatial support of the diffusion and the fact that \(\Phi_{xxx}\)
cannot vanish identically: an even quadratic cannot be one-Lipschitz and
differ from \(|x|\) by a bounded function. An initial gap with \(0\) outside
the support necessarily has \(\gamma=0\); \(q(0)=0\) replaces left contact.
[P/regularity.tex:298–308](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/build/regularity.tex#L298-L308),
[P/variation.tex:215–249](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/build/variation.tex#L215-L249)

**Terminal gaps.** An interval \((a,1)\) with finite constant coefficient
requires a different argument. Its tilted heat transition has a density
uniformly bounded below near zero at late times. On a spatial window of
width \(\sqrt{1-t}\), both signs of the terminal payoff have uniformly
positive tilted probability. Hence \(1-q(t)\ge C\sqrt{1-t}\), so
\(q(t)<t\) near one and \(G(s)<0\), contradicting contact positivity.
This covers \(c=0\) and empty support too. Full support now gives \(q=t\)
everywhere below one and, by differentiation including the right derivative
at zero, \(a=1\).
[P/variation.tex:130–249](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/build/variation.tex#L130-L249)

## Smooth density is a further argument

Full support alone does not imply absolute continuity or a positive density.
The manuscript obtains these from saturated consistency. With
\(f_k=\partial_x^k\Phi\), the Hessian identity and
\(\mathbb E f_2^2=1\) imply, first almost everywhere,
\[
 \gamma(t)=\frac{\mathbb E f_3(t,X_t)^2}
 {2\mathbb E f_2(t,X_t)^3}.
\]
The denominator is at least two, since \(f_2\ge0\) and
\(\mathbb E f_2^2=1\). Continuous moments and right continuity extend the
identity to every \(t<1\), giving continuity and \(\gamma(0)=0\).
The Itô equations for all polynomial moments bootstrap both the moments
and \(\gamma\) to smoothness. Finally, flattening \(\gamma\) around a fixed
\(t>0\) and passing the coercivity bound to the limit gives
\[
 2\gamma'(t)\mathbb E f_2^3
 \ge\frac{\gamma(t)^2}{1000}\mathbb E f_2^4>0.
\]
Thus \(\mu_\gamma=\gamma'(t)\,dt\) and \(\gamma'(t)>0\) on \((0,1)\).
The source asserts only \(\gamma'(0)\ge0\), and no smoothness at one.
[P/order-parameter-regularity.tex:15–152](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/build/order-parameter-regularity.tex#L15-L152)

## Lean lemma map

These are source correspondences, not an extracted complete dependency graph.

| Mathematical step | Public Lean source and declaration |
| --- | --- |
| Spatial smoothing and bounds | [L/Regularity/Regularity.lean:66–114](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKSupport/Regularity/Regularity.lean#L66-L114): `value_contDiff`, `value_uniform_derivative_bounds`; [L/Regularity/PositiveRegularity.lean:115–138](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKSupport/Regularity/PositiveRegularity.lean#L115-L138): `positiveValue_derivative_uniform` |
| \(q'=\mathbb E\Phi_{xx}^2\), including zero | [L/Moments/StripSquareMoment.lean:136–167](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKSupport/Moments/StripSquareMoment.lean#L136-L167): `squareMoment_eq_integral_curvatureMoment`, `squareMoment_hasDerivWithinAt` |
| Variation and contact | [L/Support/VariationIntegrals.lean:152–175](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKSupport/Support/VariationIntegrals.lean#L152-L175): `parisi_chord_derivative`, `minimizer_variational_inequality`; [L/Support/ContactPotential.lean:57–92](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKSupport/Support/ContactPotential.lean#L57-L92): compact mass removal and `minimizer_contact` |
| Exact algebra and pointwise coercivity | [L/Density/Certificate.lean:62–69,107–122](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKSupport/Density/Certificate.lean#L62-L122): `rational_identity`, `pointwise_coercivity`; the polynomial identity and the sign-based inequality are distinct stages |
| Actual integration and concrete finite-data providers | [L/Density/GaussianLogDensity.lean:106–162](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKSupport/Density/GaussianLogDensity.lean#L106-L162): `gaussian_shape_coercivity` proves integrability, zero flux on `(0,∞)` and reflection; [L/Density/FiniteDensity.lean:111–188](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKSupport/Density/FiniteDensity.lean#L111-L188): `finite_density_coercivity` constructs its premises and calls it at line 167; `finite_feedback_coercivity` converts density integrals into diffusion expectations |
| General whole-line helper, not the displayed integration call | [L/Density/Certificate.lean:165–194](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKSupport/Density/Certificate.lean#L165-L194): `integrated_coercivity_of_flux` assumes signs and the derivative identity at every real point, plus tails and integrability. Its name occurs only at its declaration in the retained support source tree; it must not be substituted for the preceding half-line call |
| Transfer and strict curvature | [L/Density/SampleJets.lean:90–143](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKSupport/Density/SampleJets.lean#L90-L143): `actual_coercivity`; [L/Moments/Curvature.lean:51–96](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKSupport/Moments/Curvature.lean#L51-L96): strict moments; [L/Support/GapCurvature.lean:48–71](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKSupport/Support/GapCurvature.lean#L48-L71): `positive_gap_curvature`, `zero_gap_curvature` |
| Terminal boundary layer | [L/Support/ContactPotential.lean:124–208](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKSupport/Support/ContactPotential.lean#L124-L208): `terminal_plateau_second_moment_defect`; [L/Support/NoTerminalPlateau.lean:15–78](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKSupport/Support/NoTerminalPlateau.lean#L15-L78): `minimizer_no_terminal_plateau` |
| Deterministic gap closure | [L/Support/Closure.lean:361–482](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKSupport/Support/Closure.lean#L361-L482): `full_support_of_contact_and_gap_curvature`, `derivative_eq_one_of_full_contact`; the contradiction uses the mean value theorem |
| Final statement and arbitrary associated diffusion | [L/Main.lean:19–59](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKSupport/Main.lean#L19-L59): `minimizer_full_support_actual`, `full_support`; diffusion uniqueness transfers the moments from the constructed solution |

The integration route matters at the origin. The manuscript extends
`b=-r″/r` smoothly there, whereas Lean's `certB` uses totalized division.
For the ordinary example `r=tanh x`, the extension has `b(0)=2`, while
the totalized definition has `b(0)=0`; with `v(0)=1`, the generic helper's
universal premise `b−2v≥0` fails at that point. The actual proof establishes
the signs only for `x>0`, proves continuity and zero value of the full flux
at zero, and reflects the resulting integral inequality. An isolated
point is irrelevant to the integral but relevant to a universally
quantified premise. This distinction concerns the source correspondence;
it is not a failure of `gaussian_shape_coercivity`. The exact premises and
concrete suppliers are recorded in
[the interface review](full-support-interface.md#intermediate-premises-and-their-concrete-providers).

## Corrections to make in a downstream account

1. **Match the formal claim to its type.** State the conditional minimizer
   hypothesis, relative support and interval \([0,1)\). Keep minimizer
   existence, the ground-state variational formula, smooth density and QAOA
   convergence separate. None is a conclusion of `FullSupportConclusion`.
   The manuscript explicitly cites existence externally at
   [P/main.tex:94–107](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/build/main.tex#L94-L107);
   the [public scope statement:14–16](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/docs/281.md#L14-L16)
   confirms the selected formal boundary.
2. **Do not identify every prose lemma with an identically stated Lean lemma.**
   `parisi_chord_derivative` is a limit along the specified shrinking chord
   sequence between two admissible order parameters, not the full
   real-parameter one-sided derivative asserted in the manuscript. It is
   sufficient for the variational inequality and contact proof. A claim of
   full lemma-by-lemma correspondence needs the additional derivative bridge.
3. **Explain the ratio coordinate change.** Lean's
   [L/Density/RatioJets.lean:13–14](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKSupport/Density/RatioJets.lean#L13-L14)
   defines the Wronskian \(rs_x-sr_x=rj\). Its nonnegativity on the positive
   half-line corresponds to the manuscript's ratio sign after using \(r>0\).
   It is not literally the same expression as \(j\).
4. **Preserve the transfer hypothesis and endpoint split.** The Lean
   `actual_coercivity` assumes \(t>0\) and continuity of \(\gamma\) at that
   time. Constancy supplies continuity during gap exclusion; the later
   regularity argument supplies it for a minimizer. Neither division by
   \(c\) at zero nor a uniform derivative estimate up to time one is justified.
5. **Keep the source comparison and replay claims separate.** The displayed
   Lean certificate ends in `ring`, and the final theorem visibly composes
   the stated ingredients; these are observations about source. A replay
   receipt and a transitive axiom/dependency audit are additional evidence,
   and neither would by itself verify the manuscript's broader prose claims.


## Reconstruction completed in the long record

The [long record](../long/reasoning-record.md) gives the compact-strip
approximation at §2.4 with two independent convergence conditions:
$\|\gamma_m-\gamma\|_{L^1}\to0$ and $M_m\to\infty$, together with
$M_m\ge\|\gamma_m\|_\infty$. The latter inequality alone does not make
the terminal data approach $|x|$. Positive-order spatial derivatives
are uniformly bounded on a fixed strip; the value itself grows with $|x|$.
The source owner is P/regularity.tex:107–186.

Long §3 gives the forward first-variation formula, its convex converse,
compact-measure removal, the right-hand argument at zero and the quantitative
terminal plateau contradiction. Long §4 includes every coefficient of the
certificate, all five squares, all 22 positive remainder coefficients, and
the density signs, jump rules and zero-flux justification needed before
integration. The exact finite check remains distinct from those analytic
arguments. Long §5 gives the exhaustive gap cases, the endpoint-slack area
identity and the weaker conditional-crossing deduction; curvature is applied
inside the constant interval, with only continuous endpoint values of $q'$.

The smooth-density conclusion is an additional ordinary result from
P/order-parameter-regularity.tex, Corollary 6.4, proved in long §5.1:
$\gamma\in C^\infty([0,1))$, $\gamma(0)=0$, and
$\mu_\gamma(dt)=\gamma'(t)dt$, with $\gamma'(t)>0$ for $0<t<1$.
It uses saturated consistency and the artificial shrinking-plateau comparison;
full support alone would not prove any density statement. These conclusions
are not added to the selected `FullSupportConclusion` type.

For example, full support can coexist with atoms: add any positive atom in
$(0,1)$ to Lebesgue measure. A purely atomic full-support example is a summable
series of positive weights over an enumeration of the rationals in $(0,1)$,
interpreted as the convergent series $\sum_{j\ge1}2^{-j}\delta_{r_j}$.
Neither is the minimizer established here; they delimit what support alone
means. Local finiteness also need not give finite total mass:
$\gamma(t)=(1-t)^{-1/2}-1$ is admissible, integrable, and has infinite
Stieltjes mass near one. Its endpoint behaviour is allowed by the definitions.
