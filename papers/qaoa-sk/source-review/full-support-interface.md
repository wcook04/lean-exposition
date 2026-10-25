# The full-support interface

The selected theorem states that every admissible integrable minimizer of the
zero-temperature Parisi functional for the pure, zero-field Sherrington–Kirkpatrick
model has full relative Stieltjes support on `[0,1)`. It also supplies a Stieltjes
measure and an associated diffusion, proves strict increase of the order
parameter, and gives two moment identities for every diffusion satisfying the
specified equation. The hypothesis that the order parameter is a minimizer is
essential to the statement; existence of such a minimizer is not a conclusion.

The source edition is
[`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a).
The [challenge statement][challenge], [definition owner][model], and
[implementing theorem][main] are retained under the
[source lock](../../../examples/qaoa-sk/source-lock.json). Line locators below
refer to those retained sources; their immutable public counterparts are the
[challenge](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SKFullSupport.lean#L12-L92),
[model](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKSupport/Model.lean#L12-L88),
and [implementation](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKSupport/Main.lean#L19-L59).
This is a source-level mathematical review;
it supplies no fresh Lean replay, extracted dependency graph, transitive axiom
audit, Comparator result, or independent expert acceptance.

## Exact domain and hypotheses

The challenge declares, in the namespace `OAI.ZeroTemperatureSK`,

```lean
theorem full_support (W : BrownianSystem Ω) (γ : OrderParameter)
    (hmin : IsMinimizer W γ) : FullSupportConclusion W γ
```

Here `Ω : Type*` and `[MeasurableSpace Ω]` are implicit surrounding parameters.
Thus the quantifiers range over an arbitrary measurable sample space, every
Brownian system on it, and every admissible order parameter on the interval.
There is no prescribed sample space, separately supplied Stieltjes measure, or
separately supplied diffusion in the hypotheses. See the
[challenge, lines 24–31 and 90–92][challenge].

The model definitions in [Model.lean, lines 1–88][model] are text-identical to
the corresponding first 88 lines of the challenge. Their mathematical content is:

| Lean object | Exact meaning and source |
| --- | --- |
| `Time` | The subtype `Set.Ico (0 : ℝ) 1`: the real interval `[0,1)`, including zero and excluding one. [Lines 12–15][model-domain]. |
| `extend γ.val` | Equal to `γ.val t` on `[0,1)` and zero everywhere else, including at `t = 1`. [Lines 14–15][model-domain]. |
| `OrderParameter` | A real-valued function on `Time`, nonnegative, monotone, right-continuous in the subtype, whose zero extension is Lebesgue integrable on `ℝ`. No boundedness at one, normalization of total Stieltjes mass, differentiability, or absolute continuity is required. [Lines 17–22][model-domain]. |
| `BrownianSystem Ω` | A measure `law`, a proof `IsProbabilityMeasure law`, a process `B : ℝ≥0 → Ω → ℝ`, measurability of each `B t`, and Mathlib's predicate `IsBrownianReal B law`. [Lines 24–29][model-brownian]. |
| `Control W t` | A real process, progressive for the natural filtration of `B(t+s) − B(t)`, bounded by one in absolute value for **every** time and sample point. The bound is pointwise, not merely almost sure. [Lines 33–41][model-control]. |
| `value W γ t x` | The real supremum of expected control payoffs, with the Brownian system fixed. It is a stochastic-control definition, rather than a PDE solution supplied as an assumption. [Lines 43–51][model-value]. |
| `gradient`, `curvature` | Respectively `deriv (value W γ t) x` and `deriv (gradient W γ t) x`; these are spatial derivatives. Their definitions alone are not regularity theorems. [Lines 53–57][model-value]. |
| `parisi W γ` | `value W γ 0 0 − (1/2) ∫₀¹ t γ(t) dt`, with the zero extension used in the integral. [Lines 59–60][model-minimum]. |
| `IsMinimizer W γ` | `∀ η : OrderParameter, parisi W γ ≤ parisi W η`: global minimality over the entire admissible class, not a stationary-point condition or minimization over a finite approximation. [Lines 62–63][model-minimum]. |

More explicitly, for `0 ≤ t ≤ 1`, the control formula is

\[
\Phi_\gamma(t,x)
=\sup_\alpha \mathbb E_W\!\left[
\left|x+B_1-B_t+\int_t^1\gamma(s)\alpha_{s-t}\,ds\right|
-\frac12\int_t^1\gamma(s)\alpha_{s-t}^{\,2}\,ds
\right].
\]

The control is indexed by elapsed time after `t`; this explains the
`Real.toNNReal (s - t)` argument in Lean. Writing the control as `a_s` instead
requires this reindexing. The absolute-value terminal payoff, standard Brownian
noise, and factors `1/2` implement the pure zero-field normalization
`ξ(t) = t²/2`; the selected interface has no external-field or general
mixed-spin covariance parameter. The manuscript gives the same control
formula and normalization in [main.tex, lines 65–87][paper-model], and explains
the zero-field restriction at [lines 149–152][paper-field].

## All five conclusions

[FullSupportConclusion, lines 81–88][model-conclusion] is a conjunction with the
following quantifier order.

1. **A Stieltjes measure exists.** There is a `μ : Measure Time` such that
   `μ (Set.Iic t) = ENNReal.ofReal (γ.val t)` for every `t : Time`.
   Since `Iic t` is formed inside `Time`, this says `μ([0,t]) = γ(t)`.
   In particular, the convention fixes `μ({0}) = γ(0)`.
2. **A diffusion exists on the given Brownian system.** There is a process
   `X : ℝ≥0 → Ω → ℝ` satisfying `IsDiffusion W γ X`.
3. **Every matching Stieltjes measure has full support.** For every `μ`,
   `IsStieltjesMeasure γ μ` implies `μ.support = Set.univ`.
   The ambient space is the subtype `[0,1)`, so this is full support in its
   relative topology. It is not a statement that the support is all of `ℝ`,
   nor does it assert mass or support at the excluded endpoint one.
4. **The order parameter increases strictly.** For every `a b : Time`,
   `a < b` implies `γ.val a < γ.val b`. Equivalently in real coordinates,
   `γ(a) < γ(b)` whenever `0 ≤ a < b < 1`.
5. **Every admissible diffusion satisfies both moment identities.** For every
   `X` with `IsDiffusion W γ X`, and every `t : Time`,
   \[
   \mathbb E_W\bigl[(\partial_x\Phi_\gamma(t,X_t))^2\bigr]=t,
   \qquad
   \mathbb E_W\bigl[(\partial_{xx}\Phi_\gamma(t,X_t))^2\bigr]=1.
   \]
   The first integral is named `squareMoment`; the second is written out in
   the conclusion. Both include `t = 0` and exclude `t = 1`.

The diffusion predicate requires progressiveness for the natural filtration
of `W.B`. Outside a single null set, the path is continuous on `[0,1]`, starts
at zero, and simultaneously for every `0 ≤ t ≤ 1` satisfies

\[
X_t=B_t+\int_0^t\gamma(s)\partial_x\Phi_\gamma(s,X_s)\,ds.
\]

This pathwise quantifier order is present in
[Model.lean, lines 68–75][model-diffusion]. The process is defined for all
nonnegative times, but this integral equation and the required path
continuity are imposed only through time one. Its terminal-time coverage
must not be transferred to the two moment identities.

## How the implementation supplies the interface

The implementing [Main.lean, lines 19–59][main] first proves the conclusion for
a constructed diffusion, then transfers the moment identities to every
admissible diffusion. The following is a reading of the displayed proof and
its named prerequisites, not an extracted transitive dependency report.

| Step in the displayed proof | Public source correspondence |
| --- | --- |
| Construct the Stieltjes measure. | `parameterMeasure` is the measure of the Stieltjes function **plus** `ENNReal.ofReal (γ.val ⊥) • Measure.dirac ⊥`. The additional atom enforces the convention at zero. `parameterMeasure_isStieltjes` has no minimizer hypothesis. [GapCurvature.lean, lines 96–119][measure-construction]. |
| Construct the diffusion. | `diffusion` is defined using the Brownian driver and the feedback drift. `diffusion_isDiffusion` proves the required predicate for every `W` and every `γ`, with no minimizer hypothesis. [CompactDrift.lean, lines 275–327][diffusion-construction]. |
| Establish contact and rule out gaps. | `minimizer_full_support_actual` applies the deterministic theorem `full_support_of_contact_and_gap_curvature`. It supplies continuity, `q(0)=0`, the derivative relation, contact on the support, exclusion of a terminal plateau, and separate inequalities for positive and zero constant intervals. [Main.lean, lines 19–33][main-actual]; [Closure.lean, lines 411–460][closure]. |
| Obtain the curvature identity, including at zero. | `derivative_eq_one_of_full_contact` differentiates `q(t)=t`, using a right derivative at zero. Here `q` is the squared-gradient moment and its derivative is the squared-curvature moment. [Closure.lean, lines 462–482][contact-derivative]; [StripSquareMoment.lean, lines 112–167][moment-owner]. |
| Transfer to arbitrary `X`. | `diffusion_uniqueness` identifies every process satisfying `IsDiffusion` with the constructed diffusion almost surely, simultaneously for all `t ≤ 1`. `Main.lean` then uses equality almost everywhere in both integrals. [Uniqueness.lean, lines 13–15][uniqueness]; [Main.lean, lines 44–59][main-transfer]. |

The gap argument has two genuinely different inputs. For a positive constant
coefficient on an interval, the implementation proves strict positivity of
the **second derivative of the curvature moment**. For a zero coefficient,
it proves strict positivity of the **first derivative of that moment**.
These are [positive_gap_curvature and zero_gap_curvature, lines 48–71][gap-inequalities].
The deterministic contradiction uses contact values `q(a)=a`, `q(b)=b` and
the endpoint derivative bounds to rule out such intervals; see
[Closure.lean, lines 382–405][gap-contradictions]. The separate no-terminal-plateau
input supplies support arbitrarily close to one. Neither contact at existing
support points alone nor an assertion of infinitely many support points would
fill all the gaps.

## Correspondence with the manuscript and scope limits

The manuscript's admissible class and left-endpoint measure convention appear
in [main.tex, lines 53–63][paper-domain]. Its functional, diffusion, and
full-support theorem appear in [lines 81–131][paper-theorem]. These match the
selected formal interface at the level of the definitions and conclusion
described above. The manuscript phrases the moments for the solution; the
Lean interface makes existence explicit and quantifies the moments over every
process satisfying the diffusion predicate.

The manuscript also invokes the established Parisi formula and attainment
result in [lines 93–107][paper-attainment]. That invocation must not be
mistaken for an existential conclusion of `full_support`. Likewise, the
manuscript discusses smooth absolute continuity, `γ(0)=0`, and strict
positivity of a density at [lines 133–147][paper-smoothness]; these are not
clauses of this selected interface. Strict increase by itself is not a
substitute for absolute continuity or a positive-density theorem.

The [upstream scope statement, lines 14–16][scope] identifies exactly this
conditional full-support result. Its [lines 10–12][scope] separately identify
the scalar-value results and state that the selected formal statements do not
assert convergence of QAOA circuit energies. The full-support interface has no
circuit depth, circuit angles, thermodynamic limit, or QAOA energy in its type.

## Axioms, dependencies, and review cautions

The challenge theorem ends with `sorry` at [line 92][challenge]. It specifies
the target to be compared; it is not the implementing proof. The implementation
has a proof body in [Main.lean, lines 35–59][main], imports its model through the
`SKSupport` proof tree, and does not import the challenge module.

The [Comparator configuration, lines 2–13][comparator] pairs
`ComparatorChallenges.SKFullSupport` with `OAI.Probability.SKSupport.Main` and
selects `OAI.ZeroTemperatureSK.full_support`. It permits `propext`, `Quot.sound`,
and `Classical.choice`; `definition_names` is empty and `enable_nanoda` is
`false`. These fields describe a configured check and its permitted axioms.
They do not establish that the check ran, that the implementing theorem's
transitive axioms were inspected, or that all its definitions are semantically
faithful to the manuscript.

The source imports `Mathlib` and multiple analytic, probabilistic, and
deterministic support modules; the immediate imports are visible at
[Main.lean, lines 1–8][main-imports]. The retained
[toolchain](../../../examples/qaoa-sk/upstream/lean/lean-toolchain#L1) is Lean
`v4.34.1`. The [derived Lake configuration, lines 10–20][lake] pins mathlib to
`d13f23b723b8a846827a245b89c10fc7d3f11612` and declares the two selected `Main`
modules as roots, with globs covering both proof trees. It is explicitly a
derived configuration, not an unchanged
copy of the full upstream package. A source reading of this interface does
not audit the complete imported proof closure or substitute for a build in
that environment.

Four details are particularly consequential when using this theorem in prose:

- Preserve `[0,1)` and the relative topology; do not silently include one.
- Preserve the left-endpoint atom and allow locally finite Stieltjes measures
  without probability normalization or finite total mass. The integrability
  assumption is on `γ`, not on the total mass of its Stieltjes measure.
- Preserve global minimality and distinguish it from existence. The measure
  and diffusion constructions already apply to every admissible `γ`; the
  support and self-consistency conclusions use minimality.
- Preserve “every diffusion” and both moments, while keeping smooth density
  claims, scalar ground-state value formulas, and QAOA convergence outside this
  interface unless separately supported.

[challenge]: ../../../examples/qaoa-sk/upstream/lean/ComparatorChallenges/SKFullSupport.lean#L12-L92
[model]: ../../../examples/qaoa-sk/upstream/lean/OAI/Probability/SKSupport/Model.lean#L1-L88
[model-domain]: ../../../examples/qaoa-sk/upstream/lean/OAI/Probability/SKSupport/Model.lean#L12-L22
[model-brownian]: ../../../examples/qaoa-sk/upstream/lean/OAI/Probability/SKSupport/Model.lean#L24-L29
[model-control]: ../../../examples/qaoa-sk/upstream/lean/OAI/Probability/SKSupport/Model.lean#L33-L41
[model-value]: ../../../examples/qaoa-sk/upstream/lean/OAI/Probability/SKSupport/Model.lean#L43-L57
[model-minimum]: ../../../examples/qaoa-sk/upstream/lean/OAI/Probability/SKSupport/Model.lean#L59-L63
[model-diffusion]: ../../../examples/qaoa-sk/upstream/lean/OAI/Probability/SKSupport/Model.lean#L68-L75
[model-conclusion]: ../../../examples/qaoa-sk/upstream/lean/OAI/Probability/SKSupport/Model.lean#L81-L88
[main]: ../../../examples/qaoa-sk/upstream/lean/OAI/Probability/SKSupport/Main.lean#L19-L59
[main-imports]: ../../../examples/qaoa-sk/upstream/lean/OAI/Probability/SKSupport/Main.lean#L1-L8
[main-actual]: ../../../examples/qaoa-sk/upstream/lean/OAI/Probability/SKSupport/Main.lean#L19-L33
[main-transfer]: ../../../examples/qaoa-sk/upstream/lean/OAI/Probability/SKSupport/Main.lean#L44-L59
[measure-construction]: ../../../examples/qaoa-sk/upstream/lean/OAI/Probability/SKSupport/Support/GapCurvature.lean#L96-L119
[diffusion-construction]: ../../../examples/qaoa-sk/upstream/lean/OAI/Probability/SKSupport/Diffusion/CompactDrift.lean#L275-L327
[closure]: ../../../examples/qaoa-sk/upstream/lean/OAI/Probability/SKSupport/Support/Closure.lean#L411-L460
[contact-derivative]: ../../../examples/qaoa-sk/upstream/lean/OAI/Probability/SKSupport/Support/Closure.lean#L462-L482
[moment-owner]: ../../../examples/qaoa-sk/upstream/lean/OAI/Probability/SKSupport/Moments/StripSquareMoment.lean#L112-L167
[uniqueness]: ../../../examples/qaoa-sk/upstream/lean/OAI/Probability/SKSupport/Diffusion/Uniqueness.lean#L13-L15
[gap-inequalities]: ../../../examples/qaoa-sk/upstream/lean/OAI/Probability/SKSupport/Support/GapCurvature.lean#L48-L71
[gap-contradictions]: ../../../examples/qaoa-sk/upstream/lean/OAI/Probability/SKSupport/Support/Closure.lean#L382-L405
[paper-domain]: ../../../examples/qaoa-sk/upstream/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/build/main.tex#L53-L63
[paper-model]: ../../../examples/qaoa-sk/upstream/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/build/main.tex#L65-L87
[paper-field]: ../../../examples/qaoa-sk/upstream/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/build/main.tex#L149-L152
[paper-theorem]: ../../../examples/qaoa-sk/upstream/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/build/main.tex#L81-L131
[paper-attainment]: ../../../examples/qaoa-sk/upstream/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/build/main.tex#L93-L107
[paper-smoothness]: ../../../examples/qaoa-sk/upstream/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/build/main.tex#L133-L147
[scope]: ../../../examples/qaoa-sk/upstream/lean/docs/281.md#L8-L16
[comparator]: ../../../examples/qaoa-sk/upstream/lean/ComparatorChallenges/SKFullSupport.json#L2-L13
[lake]: ../../../examples/qaoa-sk/upstream/lean/lakefile.lean#L1-L20

## Intermediate premises and their concrete providers

The rational identity, a general integral helper, and the particular
integration argument used by the implementation have different interfaces.
The algebraic
[`rational_identity`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKSupport/Density/Certificate.lean#L62-L69)
has no analytic hypotheses. The general helper
[`integrated_coercivity_of_flux`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKSupport/Density/Certificate.lean#L165-L194)
assumes signs and a flux derivative at **every** real point, vanishing flux
at both spatial infinities, and three integrability conditions. These are
explicit premises of that helper. They are not additional hypotheses of
`full_support`.

The displayed concrete supplier is a different theorem:
[`gaussian_shape_coercivity`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKSupport/Density/GaussianLogDensity.lean#L106-L162).
It integrates the certificate on the open positive half-line, proves that
the flux is zero at the origin and at positive infinity, and reflects the
result by evenness. In the retained support sources, the name
`integrated_coercivity_of_flux` occurs at its declaration only. In particular,
[`finite_density_coercivity`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKSupport/Density/FiniteDensity.lean#L111-L167)
ends with a direct application of `gaussian_shape_coercivity`, not the
whole-line helper. This is an observation about the retained text and
proof bodies, not a claim from an extracted dependency graph.

### Why the origin changes the interface

The distinction is mathematically consequential. The generic helper has
literally the hypothesis

```lean
(hB : ∀ x, 0 ≤ b x - 2*v x)
```

Its flux-derivative premise is also universal in `x`; neither premise is
merely almost everywhere. In contrast,
[`certB`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKSupport/Density/FiniteForwardRatio.lean#L143-L150)
is the totalized expression `-certW r x / r x`. The
[`BackwardShape` predicate](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKSupport/Backward/BackwardRescale.lean#L12-L17)
requires oddness of `r` and strict positivity of `deriv r` everywhere.
Consequently `r(0)=0` and `v(0)>0`. With Lean's totalized field division,
`certB r 0=0`, so `certB r 0 - 2*certV r 0 < 0`. The concrete certificate
variables therefore do **not** satisfy the generic helper's displayed
`hB` at the origin.

For an explicit ordinary calculation, take the example `r(x)=tanh x`
already used in [long §4.1](../long/reasoning-record.md#41-why-the-uncorrected-expression-has-no-pointwise-sign).
Then `r(0)=0`, `v(0)=1`, `w(0)=0`, and `z(0)=-2`. The totalized quotient
has `b(0)=0`, so `b(0)-2v(0)=-2`. For `x≠0`, however,
`-w(x)/r(x)=2 sech² x`, whose smooth extension has value `2` at zero.
The manuscript uses that smooth extension; the particular Lean definition
uses totalized division. A change at one spatial point does not change a
Lebesgue integral, but it does change a universal hypothesis.

The implementation handles exactly this difference. Its
[`cert_halfLine_signs` and `cert_halfLine_coercive`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKSupport/Density/FiniteForwardRatio.lean#L181-L231)
require `x>0`, where `r(x)>0` and division is valid. The separate
[`cert_flux_continuous`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKSupport/Density/GaussianTails.lean#L98-L115)
proves continuity of the **whole flux** through zero using smooth quotient
extensions and the factor `r(0)=0`. The
[half-line integral argument](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKSupport/Density/GaussianLogDensity.lean#L135-L160)
then uses this zero boundary value, the derivative identity only for
`x>0`, and the sign inequality almost everywhere on that open half-line.
Evenness supplies the full-line integral inequality. This explains the
source correspondence without replacing the actual proof by an
inapplicable direct instantiation of the generic helper. It does not
identify an error in the implemented half-line argument.

### From finite data to the gap inequalities

| Stage | Inputs that remain in its type | How the displayed source supplies the next stage |
| --- | --- | --- |
| [`gaussian_shape_coercivity`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKSupport/Density/GaussianLogDensity.lean#L106-L162) | A bounded smooth `r`, regular `s`, backward shape, oddness and forward signs for `s`, a nonnegative Wronskian on the nonnegative half-line, an even Lipschitz `U`, `d>0`, and `U′=r−s+2dx`. | Proves integrability and decay for the Gaussian-weighted expressions, integrates on `x>0`, and reflects. These premises are explicit at this local interface. |
| [`finite_density_coercivity`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKSupport/Density/FiniteDensity.lean#L111-L167) | Positive nondecreasing coefficients `c_i≤M`, a positive mesh, and a positive index `0<i≤N`. | Constructs the backward drift, forward score and Gaussian weight; obtains all the preceding shape, regularity and derivative premises from their finite-data providers; calls `gaussian_shape_coercivity` at line 167. |
| [`finite_feedback_coercivity`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKSupport/Density/FiniteDensity.lean#L173-L188) | The same finite data and an arbitrary supplied Brownian system. | Uses `finite_density_identity` twice to convert the density integrals into expectations along the finite feedback diffusion, then applies `finite_density_coercivity`. |
| [`sample_coercivity`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKSupport/Density/SampleJets.lean#L78-L88) | Any admissible `γ`, any supplied Brownian system, a time in `[0,1)`, and a positive sampled mesh index. | Supplies positivity, monotonicity, boundedness and positive mesh for the constructed approximants before applying `finite_feedback_coercivity`. |
| [`actual_coercivity`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKSupport/Density/SampleJets.lean#L90-L143) | Positive time `t>0` and continuity of `γ` at that time. **No minimizer or positive-coefficient hypothesis.** | Passes the integrated polynomial inequality through dominated convergence of spatial derivative moments. Positive time makes the sampled index eventually positive. No limiting score or score ratio is required. |
| [`stripThird_pos`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKSupport/Moments/Curvature.lean#L65-L90) | The previous time and continuity conditions, a compact-strip cutoff `t≤T<1`, and now `γ(t)>0`. | Combines the coercive lower bound with a strictly positive fourth moment and divides by `γ(t)²`. |
| [`positive_gap_curvature` and `zero_gap_curvature`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKSupport/Support/GapCurvature.lean#L48-L71) | Constancy on `(a,b)` with `0≤a<b<1`; the positive case additionally has `c>0`. Neither has a minimizer hypothesis. | Constancy supplies continuity for the positive case, giving the second derivative of the curvature moment strictly positive. The zero case instead uses `stripSecond_zero_pos` to obtain a strictly positive first derivative, without dividing by the coefficient. |

The local existence, regularity, shape and integrability obligations in this
table are discharged within the displayed source chain. A full replay and
an audit of its imported closure would be further checks; this source
review does not claim either. The term *density* in this chain refers to
the spatial law of a diffusion. It does not establish the separate smooth
Lebesgue density of the order parameter's Stieltjes measure discussed in
the manuscript.

Likewise, the scalar tree proves
[`sourceStripRegularity`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKValue/Control/Regularity.lean#L22-L42)
from its defined Brownian space and admissible coefficient. Its compact-strip
predicate allows zero as the cutoff, whereas the finite-Gaussian target
requires a strictly positive cutoff. These local requirements identify the
providers that a complete dependency audit would check; they are not extra
undischarged hypotheses on the selected endpoint. The long record's §§4, 5
and 12 preserve this distinction.
