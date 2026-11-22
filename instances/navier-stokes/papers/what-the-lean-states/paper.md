
<!-- passage:front -->
# Finite-time blow-up for Navier–Stokes: what the Lean states

**Navier–Stokes pages:** [the paper](../navier-stokes-paper/paper.pdf) · [index by number](../navier-stokes-index/paper.md) · [specialist digest](digest.md) · [full account, part I](../navier-stokes-part-1/paper.md) · [part II](../navier-stokes-part-2/paper.md) · [part III](../navier-stokes-appendix-b/paper.md) · **what the Lean states** · [statement files](../navier-stokes-statement-files/paper.md) · [proof routes](../navier-stokes-routes/paper.md) · [proof routes in detail](../navier-stokes-route-details/paper.md) · [library guide](../navier-stokes-library-01/paper.md) · [cell layer guide](../navier-stokes-cell-guide/paper.md) · [cell reference](../navier-stokes-cell-reference/paper.md) · [cell layer and Appendix B](cell-layer-fidelity.md) · [certificate checker](certificate-checker.md)

**20 November 2026, commit
[`ad53419`](https://github.com/tristanbuckmaster/navier-stokes/tree/ad53419de079eb8f95f60313473374624a348546).**
For the argument itself, read the [specialist digest](digest.md) first; this
page compares each Lean statement with the paper.

Levent Alpöge and Tristan Buckmaster's paper presents a construction of
finite-time blow-up for the three-dimensional **unforced** Navier–Stokes
equations, from smooth compactly supported divergence-free data on
$\mathbb R^3$ and smooth periodic data on $\mathbb T^3$. Its theorem gives a
blow-up rate $(T-t)^{-1/4}$ in $\dot H^1(\mathbb R^3)$, respectively
$H^1(\mathbb T^3)$, together with a description of the limiting profile. The
surrounding analysis gives stability after adjusting finitely many directions
in the initial data.

The public Lean sources supply **conditional reductions**: an appropriate
profile, or data satisfying a precise certificate condition, imply the
specified breakdown conclusions. The authors' repository does not contain the
concrete numerical certificate or the program reported to validate it with
128-bit Arb arithmetic. The paper supplies its SHA-256 and says it will be
released (§§1.1, 1.5). We have not independently verified that final premise.
The root README says the authors had not rebuilt the latest cell-layer
patch when they posted it. We rebuilt the patched package on GitHub Actions
and it compiles. Lean's Comparator, with four further checkers, accepts all
15 selected theorems and rejects a control with a deleted hypothesis (§5).

This page compares statements and records the limits of the available
evidence. It was prepared by AI agents under Will Cook's direction and has
not been reviewed by the authors. Source inspection, a successful proof
replay, and validation of numerical data are separate results, and §5 says
which of them have been obtained.
<!-- /passage:front -->

## 1. The equations and the Clay conclusions

<!-- passage:sec-1-the-equations-and-the-clay-conclusions -->

The statement file [`Challenge.lean`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Challenge.lean) uses Mathlib derivatives on
`EuclideanSpace ℝ (Fin 3)`. `IsSmoothSolution` asks for joint smoothness on
$[0,\infty)\times\mathbb R^3$, the prescribed initial value, and

$$
\partial_tu+(u\cdot\nabla)u=\nu\Delta u-\nabla p,\qquad
\operatorname{div}u=0
$$

at every positive time. The coordinate trace of the second Fréchet
derivative is the Laplacian. Smoothness on the positive-time interior
prevents the derivative operators' default values from supplying an
elementary loophole.

**`BreakdownOnSpace`.** For each $\nu>0$, there is a smooth compactly
supported divergence-free datum for which no global smooth solution has
$\int_{\mathbb R^3}|u(t,x)|^2\,dx$ bounded uniformly for $t\geq0$.
The nonnegative lower Lebesgue integral (`lintegral`) and finite real bound
give the intended energy restriction; an infinite integral cannot satisfy it.

**`BreakdownOnTorus`.** For each $\nu>0$, there is a smooth divergence-free
datum of period one in each coordinate for which no global smooth solution
has periodic velocity. The pressure may be any smooth pressure.

These propositions imply Fefferman's (C) and (D) by taking the force to be
zero. Smooth compactly supported data have all the required rapid-decay
bounds. Every solution in the official class satisfies the positive-time
equation used here. Excluding this larger candidate class is sufficient.
The official Clay PDF's **Errata explicitly adds pressure periodicity**;
the Lean torus conclusion excludes a larger pressure class and therefore
also excludes that corrected class. “Take $\nu>0$” in the official statement
already means arbitrary positive viscosity, so there is no additional
viscosity-quantifier advantage.

Sources: [`Challenge.lean:10–45`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Challenge.lean#L10-L45);
[official Clay statement, (4)–(11), (C), (D), and Errata](https://www.claymath.org/wp-content/uploads/2022/06/navierstokes.pdf).
This implication is a mathematical interpretation of the definitions, not
a newly checked Lean translation of Fefferman.
<!-- /passage:sec-1-the-equations-and-the-clay-conclusions -->

## 2. A profile gives breakdown

<!-- passage:sec-2-a-profile-gives-breakdown -->

`PeriodicSimilarityProfileExists` requires smooth $W(s,y)$ and $q(s,y)$,
a positive period $P$, a linear isometric equivalence $R$, and a finite
constant $C$, with

$$
\partial_sW+\tfrac12W+\tfrac12(y\cdot\nabla)W-\Delta W+
(W\cdot\nabla)W+\nabla q=0,\qquad \operatorname{div}W=0,
$$

$$
W(s+P,y)=R\,W(s,R^{-1}y),\qquad W\not\equiv0,
$$

and $|\nabla^jW|\leq C(1+|y|)^{-1-j}$ for $j=0,1,2$, together with
$|\nabla q|\leq C(1+|y|)^{-3}$. The equation and recurrence match (1.2).
The full Lean premise has additional written bounds relative to (1.3):
Remark 1.2 derives the higher velocity bound, and the README attributes the
pressure-gradient bound to standard analysis.

The definition explicitly excludes zero velocity and a zero or negative
period. Smoothness, an actual isometric equivalence and finite constants
also rule out the elementary derivative, singular-map and infinite-bound
degeneracies we looked for. This is not a construction of a
profile or an exhaustive proof that every possible modeling error is absent.

For $\nu=1$, the substitution
$u(t,x)=(T-t)^{-1/2}W(-\log(T-t),x/\sqrt{T-t})$ gives the displayed
similarity equation. A constant shift of similarity time accounts for the
paper's choice $\log(T/(T-t))$. A profile stationary in $s$ is continuously
self-similar; a profile recurrent in $s$ permits discrete self-similarity.
The classical stationary-profile exclusions do not automatically exclude
this latter possibility.

| Lean theorem | Comparison with the paper |
|---|---|
| `breakdown_on_space` | Coarser formal output than Theorem 1.1: no global smooth solution with uniformly bounded energy. It omits the trajectory, rate and convergence. Its written premise has the extra bounds above. |
| `breakdown_on_torus` | Coarser formal output than Theorem 1.1, but excludes arbitrary smooth pressure. Relating the paper's solution class to this endpoint needs pressure normalization as well as uniqueness. |
| `breakdown_on_space_of_weak` | A different explicit weak-profile theorem. No separate paper theorem has precisely its hypothesis; Proposition 7.11 and Theorem 1.1 provide a related regularization-and-breakdown route. |

Passing from an exhibited singular trajectory to a nonexistence endpoint
requires that any hypothetical global solution agree with it and have
bounded enstrophy through the proposed blow-up time. The authors' README
explains the finite-energy and generalized Galilean routes using
[Tao (2013)](https://msp.org/apde/2013/6-1/apde-v6-n1-p02-s.pdf).
It is too compressed to call this merely “uniqueness of smooth solutions.”
The table compares exported conclusion types. The paper's further analysis,
including Proposition 2.1, gives a finite-codimension family statement.
Internal formal proofs also contain a finite-dimensional correction
mechanism, as described below; its presence must be distinguished from the
quantifiers exposed by those conclusion types.

The weak profile requires a positive period and twisted recurrence, uniform
$L^6$ velocity and $L^2$ gradient bounds, square-integrable second derivatives
over a period, and the distributional equation against solenoidal tests.
It also requires that the field is **not almost everywhere zero** and that
each weak residual is integrable before its integral is set to zero.
The coefficients $-1$ and $-1/2$ in its weak drift terms follow by integration
by parts in three dimensions. A modification of zero on a null set is not
a witness.

Sources: [`Challenge.lean:47–108`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Challenge.lean#L47-L108); [`Solution.lean:17–24`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Solution.lean#L17-L24);
`README.md:23–53`; paper Theorem 1.1, Remark 1.2, Proposition 2.1,
Proposition 7.11.

### Quantitative content inside the formal proof

The exported nonexistence statements are coarser than the paper's theorem,
but they do not exhaust the mathematical content of `Breakdown/`.
[`Base/Framework.lean:66–73`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Base/Framework.lean#L66-L73) defines `TransferHolds`: an admissible nonzero
recurrent mild orbit, any dense data submodule and any positive approximation
tolerance give a mild solution on `[0,1)` whose initial datum belongs to that
submodule, with

$$
\|D_{1-t}u(t)-w(-\log(1-t))\|\le C(1-t)^\kappa,\qquad \kappa>0.
$$

[`Transfer/Exports.lean:53–55`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/Exports.lean#L53-L55) proves the transfer from the dichotomy, and
[`Weak/OrbitBreakdown.lean:13–28`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/OrbitBreakdown.lean#L13-L28) uses it in the actual breakdown route.
[`Uniqueness/Restrict.lean:53–63`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/Restrict.lean#L53-L63) also records the quantitative blow-up datum.
The realization, dilation, `RegEmbed` and `RegGlue` declarations connect the
abstract space to physical velocity and its homogeneous gradient norm.
`OrbitBoundStatement` and `OrbitNormStatement` give upper and positive lower
bounds on the recurrent orbit's norm.

The finite-dimensional correction appears in `StepDataStatement`
([`Transfer/StatementsFrame.lean:55–69`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StatementsFrame.lean#L55-L69)), the section construction
([`Transfer/Section.lean:31–59`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/Section.lean#L31-L59)), and the nonlinear fixed point
([`Transfer/Contraction.lean:123–132`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/Contraction.lean#L123-L132)). Thus there is formal support for
quantitative convergence and finite-dimensional correction ingredients.
We have not found a single exported, independently
replayed theorem carrying every clause of printed Theorem 1.1 and its
subsequent uniform family assertion. The exact torus convergence estimate
on `B₁/₁₆` remains an unmatched part of that full statement comparison.

### Lean we added: Theorem 1.1 on every compact time interval

We wrote new Lean that states the paper's conclusion in physical terms and
proves most of it from the authors' library. [`Theorem11Challenge`](https://github.com/wcook04/proof-reader/tree/claude/navier-stokes-20261120/lean-wrappers/navier-stokes/theorem11/Theorem11Challenge.lean)
states the target with Mathlib only, so it can be read without the authors'
definitions. [`Theorem11.theorem11SpaceSlabs`](https://github.com/wcook04/proof-reader/tree/claude/navier-stokes-20261120/lean-wrappers/navier-stokes/theorem11/Theorem11Solution.lean)
proves: for every profile satisfying the library's profile premise and every
$\varepsilon>0$ there are one smooth compactly supported divergence-free
datum $\phi$ with $\|\nabla(\phi-W(0))\|_2<\varepsilon$ and constants
$0<c\le C$, $0<\kappa<\tfrac14$ such that, for every $T<1$, a smooth
solution $u$ from $\phi$ on $[0,T)$ with bounded energy satisfies, for all
$0\le t<T$,

$$
c(1-t)^{-1/4}\le\|\nabla u(t)\|_2\le C(1-t)^{-1/4},\qquad
\|\nabla(D_{1-t}u(t)-W(-\log(1-t)))\|_2\le C(1-t)^{\kappa},
$$

where $D_{1-t}$ rescales to similarity variables. The datum and constants
are fixed once; the solution and its energy bound may depend on $T$. The full
statement also wants one solution on all of $[0,1)$ with one energy bound,
which needs the local pressures glued and an energy bound uniform up to time
one; both are stated in the file and not yet proved. The torus helpers (exact
agreement on $B_{1/16}$, the full $H^1$ comparison, the geometric rate) are
proved as conditional bridges. All 16 modules compile against the package,
and the theorems use only `propext`, `Classical.choice` and `Quot.sound`
([run 44837689921](https://github.com/wcook04/proof-reader/actions/runs/44837689921)).

### What a referee's reading of §§1–6 finds

A referee-style reading of §§1–6 and Appendix A found no blocking mathematical
defect in the conditional profile-to-blow-up proof. The essential-spectrum
bound comes from a genuinely compact perturbation on the actual
`Ḣ¹` space: local Rellich compactness at positive smoothing time, followed by
an integrable `(t₁−t′)⁻³/⁴` bound at the Duhamel endpoint. The finite-rank
spectral projection admits a compactly supported transversal `E`; the proof
does not require compactly supported eigenfunctions.

Compact initial data are compatible with the profile's slow tail because
the correction is small in `Ḣ¹`. At time zero it cancels the profile outside
a compact set and can itself have infinite `L²` norm. Classical `H¹` theory,
uniqueness and the energy identity then give a finite-energy solution from
the sum. The profile's `1/r` upper bound alone does not establish membership
or nonmembership in strong `L²` or `L³`.

On the torus, cutting off creates a residual. Lemma 6.3 transfers the
whole-space right inverse, including estimates for the nonlocal projected
heat flow. A Neumann series and a nonlinear correction eliminate the
residual, giving an unforced solution. Scaling the period-`L` torus to unit
period yields `T=L⁻²` and the exact comparison radius `1/16`.

The physical error bound `(T−t)^(κ−1/4)` must be interpreted after rescaling:
the rescaled error tends to zero, even when the physical error grows. The
lower blow-up bound comes from nonvanishing of the recurrent orbit,
compactness of one time period, and a small-error estimate.

The analytic bridge to the stronger-written formal pressure premise can
also be supplied by hand: construct the normalized pressure from `W⊗W`,
prove `|∇q|≲(1+|y|)⁻³` by a near/far kernel estimate, and remove the harmonic
ambiguity using a compactly supported test in similarity time. This does
not require an unproved bound on `∂sW`. It is an explanatory hand proof,
not a newly checked Lean declaration or a numerical certificate check.

The number of corrected directions is at least three. Spatial translation
gives linearized solutions $h_a=(a\cdot\nabla)u^*$, and the recurrence gives
$Mh_a(0)=e^{S/2}h_{R^{-1}a}(0)$. A nonzero $L^6$ field cannot be constant
along a whole line, so $a\mapsto h_a(0)$ is injective and these three
directions grow by the factor $e^{S/2}>1$ each period. So
$\dim E\ge3$. This is a consistency check on the spectral argument and a
lower bound only; the paper does not compute the codimension.
<!-- /passage:sec-2-a-profile-gives-breakdown -->

## 3. A certificate gives a profile

<!-- passage:sec-3-a-certificate-gives-a-profile -->

**`certificate_orbit` and `extended_certificate_orbit`.** Their stated
output is weaker than Theorem 7.1's output: they return abstract weak-profile
existence, without recording which parameter was chosen, the distance from
the approximate profile, or the prescribed period, identity isometry and
symmetries. A blanket verdict that the *whole theorem* is weaker would also
require an established comparison of the hypotheses. The earlier certificate
uses a parameter box and a slope inverse; the extended certificate uses the
paper's mixed box/ellipsoid and adjoint estimates. We have not proved
a complete implication between either predicate and the paper's definition.

The authors' README describes thirteen differences as a reading comparison.
The source confirms additional written requirements, including joint
continuous differentiability in the parameter, decay of a supplied weak
second derivative, invariance of the weight, and a uniform-in-time spatial
$L^2$ bound on each adjoint field. Other differences change the representation:
weighted orthonormal rows can represent the paper's orthogonal rows, and
`targetGap` is the prescribed total pin value minus the approximate
profile's pin value. These observations do not establish blanket equivalence
of the definitions.

### Two routes through the nonlinear problem

Both routes invert the bordered linearized equation: the perturbation is
solved together with auxiliary force coefficients, subject to pinning
constraints. Coercivity gives injectivity, and a compact perturbation argument
gives surjectivity (paper Proposition 7.8;
`Cert.extendedBorderedInvertibleHolds_of`). The frozen-form estimate then
controls the supremum of the perturbation's gradient norm over a period
(Proposition 7.9; `Cert.extendedSupBoundHolds_of`).

The paper chooses the parameter and quadratic forcing together by the
Schauder–Tychonoff theorem in a weak topology (Proposition 7.10). Lean first
uses a contraction to find a **unique correction within the prescribed error
bounds for each fixed parameter**, then proves the resulting multiplier map
continuous. Its contraction factor is $2c_Lc_wM<1$, exactly (7.25).
Condition **(7.26), explicitly unused in the paper's proof, controls the
supremum part of Lean's contraction distance**. It is used in
[`Breakdown/Cert/ExtendedHeldContracts.lean:97–128`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedHeldContracts.lean#L97-L128); the contraction and
uniqueness statements are `Cert.extendedHeldContractsHolds_of` and
`Cert.extendedHeldExistsUniqueHolds_of`.

The parameter step uses the coordinate and remaining-coordinate bounds in
(7.35) and (7.37). `Cert.extendedExistsZeroHeldHolds_of` applies
`Held.testSetZero` to the mixed box/ellipsoid; that theorem reduces a compact
convex set to the box fixed-point theorem in [`Cert/FixedPointBox.lean`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FixedPointBox.lean).
It finds a parameter where the approximate and correcting force coefficients
sum to **zero exactly**. `Cert.extendedHeldWeakEquationHolds_of` cancels their
auxiliary fields in the weak equation. Non-strict parameter inclusions are
sufficient; this step does not require the fixed point to lie in the interior.

### What the internal construction retains

`ExtendedCertificateData.IsHeldSolution` records the nonlinear equation,
exact pin constraints, the weighted bound $\leq2\varepsilon$, the gradient
supremum bound $\leq M$, and invariance. The zero-finding stage also retains
the chosen parameter. The proof in
[`Breakdown/Cert/ExtendedSigmaProfileOfHeld.lean:237–251`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedSigmaProfileOfHeld.lean#L237-L251) constructs the sum of
the approximate profile and this correction, with the chosen period.
[`Breakdown/Cert/Rescale.lean:85–115`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Rescale.lean#L85-L115) rescales time and explicitly chooses the
identity isometry. The subsequent existential statement hides those data.

The smoothing construction retains related information too:
`FarField.SmoothFieldOfOrbit` returns a smooth field with the same period and
isometry, representing the velocity of the given mild orbit almost everywhere
in space at every time. However, the earlier weak-to-orbit interface hides
its correspondence to the original weak-profile witness. Recovering the
complete same-witness conclusion (7.38)–(7.39) requires exposing those
relationships and transporting the bounds, pins and all prescribed
symmetries through regularization. No exported theorem we have read states
that complete bundle. It would be inaccurate to infer that the internal
proof lacks the error estimates or the smoothing argument.

### What the constants of Appendix B allow

The data format fixes few numbers. At the end of Appendix B the weight is
$w_*=39/50$, and the conditions force $c_1\ge50/3$, $c_0>81.64$ and
$c_2>129$, hence $c_L>98.3$, $M<0.01695$ and $\varepsilon<0.0075$. With
$c_w=1/(2\sqrt\pi\,w_*^{1/4})\approx0.30017$, the contraction condition
$2c_Lc_wM<1$ reads $c_LM<\sqrt\pi\,w_*^{1/4}\approx1.6657$. At $M=0.016$ it
needs $c_L<104.11$, which leaves a window above the floor of 98.3. Whether
the actual inverse estimate lands in it is what the certificate has to show.
An exact rational check with illustrative values ($c_L=100$, $M=0.016$,
$\varepsilon=10^{-4}$, the rest at or above their floors) satisfies the scalar
inequalities with contraction factor below 0.992. That rules out a
contradiction among the headline numbers and nothing more: no field, form or
bound has been constructed.

Three further consequences of the conditions are useful checks on a released
certificate.

- When there are pins, $c_2>0$ follows from the rest: solving the linear
  problem with zero forcing and a nonzero pin $\eta$ in (7.52) gives
  $0<(1-\vartheta)\|(v,\beta)\|\le c_2|\eta|$. So Lean's requirement
  $c_2\ge0$, which the paper does not state, costs nothing for a certificate
  that satisfies the paper's conditions.
- Putting $v=0$, $\beta=e_i$, $F=b_i$ in the coercive estimate gives
  $n\omega^2\le(c_1+c_0)^2b_*^2$, a lower bound on the forcing fields that
  the number of multipliers $n$ forces.
- With $k=c_1+c_0$, (7.21) and the contraction give $c_r<1/k-2c_wM$: the
  reference-profile error and the nonlinear margin cannot be chosen apart.

Three readings of the numbers need care. The distance "less than 0.017"
is measured from the chosen family member $W^a_\alpha$, not from the
computed field $\bar W$. The factor in the radius estimates is $m=2$, from
the half-period rotation, not the 19 of the spatial symmetry. And 128-bit
working precision says nothing by itself about the width of the final
enclosures; the margins do. At period $S\approx0.36$ the spatial dilation is
about 1.197 per period and 1.094 per half period with rotation; the
near-one exclusions of Chae–Wolf and Pineau–Vicol depend on amplitude and
rotation hypotheses, so the period alone gives no contradiction.

Sources: paper Appendix B (closing paragraph), (7.21)–(7.27), (7.52),
Remark 7.3.

### Lean we added: Theorem 7.1 with its chosen witness

The authors' exported certificate theorems say only that some weak profile
exists. [`Breakdown.theorem71_extended`](https://github.com/wcook04/proof-reader/tree/claude/navier-stokes-20261120/lean-wrappers/navier-stokes-theorem71/wrapper/Theorem71Solution.lean)
and `Breakdown.theorem71_cell` state and prove the conclusion of Theorem 7.1
in full: one chosen parameter $\alpha$, its period and approximate field, a
nonzero smooth exact profile, the bound (7.38) including the multiplier term
$\omega^2\sum_i\beta^a_i(\alpha)^2$, the gradient bound at every time, the
pins and every prescribed symmetry, for the extended certificate and for data
satisfying `CellSystemCondition`. Three existential lemmas in the authors'
files built these witnesses and then hid them; a short patch adds versions
that return them and keeps the originals, with their types unchanged, as
corollaries. The workflow applies it only after the three files' SHA-256
hashes match. The patched package and all 13 modules compile, and both
endpoints use only `propext`, `Classical.choice` and `Quot.sound`
([run 44844164476](https://github.com/wcook04/proof-reader/actions/runs/44844164476)).

### The conditional chain reaches both breakdown conclusions

From either formal certificate hypothesis, `certificate_orbit_proved` or
`extended_certificate_orbit_proved` supplies a weak profile. The subsequent
source-level chains are closed:

| Route from the weak profile | Library declarations | Result |
|---|---|---|
| Directly through a continuous mild orbit | `WeakProfile.weakOrbitOfParts_holds`, `WeakProfile.breakdownOnSpace_of_orbit`, `breakdownOnSpace_of_weak` | `BreakdownOnSpace` |
| Through a smooth decaying profile | `FarField.periodicLerayProfileExists_of_weak`, then `Periodic.breakdownOnTorus_of_profile`; composed as `FarField.breakdownOnTorus_of_weak` | `BreakdownOnTorus` |

The smooth-profile route supplies its regularity, integral-equation and decay
steps with `FarField.smoothFieldOfOrbit_holds`,
`FarField.integralEquationOfOrbit_holds` and `FarField.farFieldDecay_holds`.
It does not leave Proposition 7.11 as an external premise. The chain remains
conditional on a formal certificate; it supplies no numerical witness.
The chain was traced in the source; the build and axiom results are in §5.

Sources: [`Breakdown/Cert/ExtendedStatement.lean:96–225`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedStatement.lean#L96-L225);
[`Breakdown/Cert/ExtendedNodes.lean`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedNodes.lean):[68–75](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedNodes.lean#L68-L75), [209–265](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedNodes.lean#L209-L265);
[`Breakdown/Cert/ExtendedMain.lean:56–93`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedMain.lean#L56-L93);
[`Breakdown/Cert/ExtendedExistsZeroHeld.lean:102–118`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedExistsZeroHeld.lean#L102-L118);
[`Breakdown/Weak/Main.lean:31–40`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/Main.lean#L31-L40);
[`Breakdown/CertTorus/Defs.lean:62–67`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/Defs.lean#L62-L67);
[`Breakdown/CertTorus/TopStatements.lean:26–56`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/TopStatements.lean#L26-L56);
[`Breakdown/CertTorus/Main.lean:8–15`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/Main.lean#L8-L15); paper §7, especially
Propositions 7.8–7.11 and Theorem 7.1.

**The three `…_of_cell_system_condition` theorems.** Seven data/entry
arguments satisfying the fifteen fields of `CellSystemCondition` give
`BreakdownOnSpace`, `BreakdownOnTorus`, or their conjunction. Their paper
counterpart is the composite route through Appendix B, Proposition B.14,
Theorem 7.1 and Corollary 7.2. These theorem types supply an implication;
they do not supply concrete data satisfying the premise.

The expanded [cell-layer comparison](cell-layer-fidelity.md) records a
partial correspondence. Several earlier assertions needed correction:

- The cell instantiation forces `targetGap=0`. The generic extended
  certificate's allowance of a nonzero gap does not survive this specialization.
- The claimed local exclusion of an empty mesh was invalid. With no
  actuators, a negative existential support radius makes that coverage
  clause vacuous. This does not satisfy the remaining full certificate.
- The active-harmonic filter has three users: `group_link`, `groups_cover`
  and `rows_groups_cover`.
- Condition 14 has an inspectable route to the regularity and decay in
  (B.51), although the paper does not supply its complete coefficient format.
- Direction-dependent exterior radii carry explicit measurability,
  homogeneity and uniform lower/upper-bound obligations. An arbitrary
  implementable choice need not satisfy them.

The azimuthal weight $(|m|+1/2)^2$ matches the displayed paper estimate.
The README describes three changes in the 20 November patch: the azimuthal
weight, a cell constant that may now be zero, and coverage required only for
active model harmonics. The pre-patch sources are not public. The repository
has two commits, five minutes apart, and the second only moves the package
from `breakdown/` to `lean/`; every file keeps its Git blob identity. The
three changes match `AzimuthalBounded`, most likely
`IsLeafValues.curlHessFloor_nonneg` (whose use multiplies an inequality and
never divides by the constant, while `hessFloor_pos` stays strict), and
`Assembly.modelLabels`. Since
$(|m|+\tfrac12)^2=m^2+|m|+\tfrac14$, the new weight can only reduce each
term, to $5/9$ of the old one at $|m|=1$; the analytic estimate behind it is
correspondingly stronger, and the current proof chain carries it.

The comparator target [`CellLayerTheorems.lean`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CellLayerTheorems.lean) imports
`Breakdown.CertCell.StatementDefs`, rather than the standalone
[`CellLayerChallenge.lean`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CellLayerChallenge.lean) used for reading. A source comparison, which we
reran and which reproduces byte for byte, finds agreement for **all 787 non-theorem declaration commands**,
including complete bodies, embedded proofs and recorded scope. Across the
six readable statement modules, all **967 non-theorem commands** match
their library counterparts. The cell file also has three theorem stubs,
whose statements match the Comparator target. The import closure contains
626 additional declarations that are not repeated in those readable files;
they are inventoried separately. This establishes source agreement for the
displayed definitions, not an independent comparison of elaborated theorem
dependencies or their mathematical meaning.

Sources: [`CellLayerChallenge.lean`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CellLayerChallenge.lean):[3854](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CellLayerChallenge.lean#L3854), [4832–4839](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CellLayerChallenge.lean#L4832-L4839), [5193–5194](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CellLayerChallenge.lean#L5193-L5194), [5752–5760](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CellLayerChallenge.lean#L5752-L5760), [5814–5816](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CellLayerChallenge.lean#L5814-L5816), [5890–5891](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CellLayerChallenge.lean#L5890-L5891), [6042–6043](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CellLayerChallenge.lean#L6042-L6043), [7007–7046](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CellLayerChallenge.lean#L7007-L7046);
[`CellLayerTheorems.lean:1–29`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CellLayerTheorems.lean#L1-L29); paper Appendix B, especially (B.51)–(B.56)
and the closing qualification on omitted conditions.

### Trying to satisfy the hypotheses with cheap data

If any hypothesis of these implications could be met by trivial data, the
Lean would prove blow-up from that data, and the endpoints would say less than
they appear to. A systematic attempt recorded 101 routes against the two
endpoints, the two profile predicates, the extended certificate and the cell
condition: 90 are blocked by an identified clause and 11 remain open in the
sense that a cheap local choice is allowed but no complete witness exists.
None reached a complete hypothesis. The blocking clauses fall into ten
groups, among them joint regularity and a finite real energy bound in the
solution class ([`Breakdown/Defs.lean:26–45`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Defs.lean#L26-L45)), nontriviality almost everywhere
in the weak profile ([`Breakdown/Defs.lean:99`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Defs.lean#L99)), a strict lower bound on the
approximate profile's energy with positive weight, universal coercivity with a
positive multiplier weight, and coverage of every cell, every omitted mode and
the exterior.

One consequence is new (a deduction from the source, checked by hand). An empty mesh is not excluded by the per-cell
conditions, and earlier readings left it open. But if the full
`CellSystemCondition` holds with zero cells, the number of multipliers $k$ is
zero: every actuator then vanishes by the support theorem, and the coercive
estimate applied to the zero perturbation gives
$\omega^2\sum_i\kappa_i^2\le0$ for every multiplier vector, with
$\omega>0$. With $k=0$ the exterior still has to be covered by the
exterior conditions, so the empty mesh moves all the work to the exterior and
removes none of it. Whether a complete certificate with $k=0$ and no cells can
exist is open. These deductions are checked by hand; their Lean probes do
not all compile yet.
<!-- /passage:sec-3-a-certificate-gives-a-profile -->

## 4. The outstanding certificate bridge

<!-- passage:sec-4-the-outstanding-certificate-bridge -->

The required implication is

$$
\text{CheckerAccepts(bytes)}
\;\Longrightarrow\;
\text{CellSystemCondition(decode(bytes))}
\;\Longrightarrow\;
\text{BreakdownOnSpace}\land\text{BreakdownOnTorus}.
$$

Exact equality between paper and Lean descriptions is unnecessary: an
external checker may establish stronger conditions that imply the Lean
premise. Matching many formulas is insufficient if a required field,
decoding convention, domain or tail bound is missing.

| Item | Evidence at commit `ad53419` |
|---|---|
| Profile-to-breakdown and certificate-to-profile arguments | Paper exposition and Lean proof sources; narrower exported conclusions as described above. |
| Cell conditions imply the breakdown endpoints | Lean proof sources. Appendix B says Propositions B.1 and B.4 are proved in the formalization. |
| Concrete certificate satisfies the exact conditions | Authors' report of an external computation; neither certificate nor checker is public. |
| Build of the published package | Our Actions runs: `lake build` exits 0 (7,735 s, then 7,680 s); the authors' axiom script reports only `propext`, `Classical.choice` and `Quot.sound` for its 27 names. |
| Independent replay of the selected theorems by Comparator | Accepted: all 15 theorems by Lean's kernel and four further checkers; the control rejected (§5). |

The hash identifies the intended certificate bytes once obtained. It does
not establish the inequalities or their interpretation. The
[certificate-checker page](certificate-checker.md) sets out what a checker
has to establish for the implication above to hold: every field of
`CellSystemCondition` traced to its terminal comparisons, the places where a
natural implementation would check too little, a data schema that can be
written before release, and a plan for checking the certificate
independently of the authors' program.
<!-- /passage:sec-4-the-outstanding-certificate-bridge -->

## 5. Checking workflow and status

<!-- passage:sec-5-checking-workflow-and-status -->

Our [workflow](https://github.com/wcook04/proof-reader/blob/claude/navier-stokes-20261120/.github/workflows/navier-stokes-comparator.yml)
builds the authors' package at the pinned commit with Lean and Mathlib 4.33.1,
writes exports with `lean4export`, and judges them with Lake Comparator from
Lean 4.36.0. It uses the authors' three configurations, which select
**15 theorem statements**, and runs the external checkers Lean paranoid,
nanoda, con-leche and con-ron after Lean's own kernel. These are five checks,
not five independent implementations: Lean paranoid runs Lean's own kernel
code, and lean4lean, which `--paranoid` would add, is derived from it.

A run counts as a pass only if:

1. the build finishes;
2. a control, `breakdown_on_space` with its profile hypothesis deleted, is
   rejected with exit 1 and the statement-mismatch message for
   `Breakdown.breakdown_on_space`;
3. all three positive comparisons exit 0.

Building and judging are separate jobs. The judge job restores the build
job's compiled files by an exact cache key and checks every package `.olean`
against hashes the build job wrote; it records the hashes of the Mathlib files
it reads, which come from Mathlib's official cache. Two diagnostics sit
outside the gate. One runs Comparator with the readable `CellLayerChallenge`
file as the challenge, so that the definitions a reader sees are compared
with the ones `Solution` uses after elaboration. The other prints the axioms
of `FarField.periodicLerayProfileExists_of_weak` and
`FarField.breakdownOnTorus_of_weak`, which the authors' 27-name script does
not list. Comparator judges the exports it is given; as the
[Lake manual](https://lean-lang.org/doc/reference/4.36.0/Build-Tools-and-Distribution/Lake/)
says, it does not by itself tie them back to the source files.

**Source checks we reran.** A scan of all 2,259 `Breakdown` files (601,385
lines) finds no `axiom`, `sorry`, `admit`, `native_decide`, `implemented_by`,
`extern`, `unsafe`, `opaque`, `csimp`, `addDecl`, macro, elaborator or
`debug.*` option. The 89 `set_option` lines are 88 heartbeat limits and one
recursion-depth limit. The declaration-by-declaration comparison of §3 and
the scan both reproduce byte for byte from the published scripts. These are
statements about source text; they do not authenticate compiled files.

**Build ([Actions run 44774695098](https://github.com/wcook04/proof-reader/actions/runs/44774695098), 20 November 2026).**
The published package, with the 20 November patch, compiled on a
GitHub-hosted ubuntu-24.04 runner: `lake build` of every default target
exited 0 after 7,735 seconds, with Mathlib from its official cache. The
authors' script [`scripts/PrintAxioms.lean`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/scripts/PrintAxioms.lean) then reported only `propext`,
`Classical.choice` and `Quot.sound` for each of its 27 names. That is
diagnostic output for those names, not an enforcing audit of every theorem.
The run then failed at export, before Comparator.

**Comparator ([run 44819023135](https://github.com/wcook04/proof-reader/actions/runs/44819023135), 21 November 2026).** Accepted. Judged against
exports of the authors' compiled package, with only `propext`,
`Classical.choice` and `Quot.sound` permitted:

| Configuration | Theorems | Result |
|---|---|---|
| `comparator.json` (`Challenge.lean`) | `breakdown_on_space`, `breakdown_on_torus`, `breakdown_on_space_of_weak` | accepted by Lean paranoid, con-leche, con-ron, nanoda and Lean's kernel (38 minutes) |
| `comparator-certificate.json` (`ExtendedCoerciveChallenge.lean`) | `certificate_orbit`, `extended_certificate_orbit` and seven supporting theorems | accepted by all five (38 minutes) |
| `comparator-cell-layer.json` (`CellLayerTheorems.lean`) | the three `…_of_cell_system_condition` theorems | accepted by all five (38 minutes) |
| control: `breakdown_on_space` with its profile hypothesis deleted | 1 | rejected: "Challenge and solution theorem statement do not match" |

con-leche and con-ron each report 109,343 declarations accepted. The judge
job first checked that every compiled package file it restored matched the
hash the build job recorded. What this establishes: the conditional theorems
say what the statement files say, and their proofs pass five checks using only
the standard axioms. It does not check the certificate, which is not public,
and it is not five independent implementations (Lean paranoid runs Lean's
own kernel code).

The diagnostic outside the gate, Comparator with the readable
`CellLayerChallenge.lean` as the challenge, stopped at one constant:
"Const does not match between challenge and target
'Breakdown.AdjointDefect.transposeApply'". Its source text and surrounding
`open` and namespace lines are identical in the readable file and in the
library file `Breakdown/CertCell/StatementDefs.lean`; the two are elaborated
in different environments (the library file also imports the
fractional-certificate definitions), and the same text produces a different
constant there. We have not yet found which instance or definition differs.
So the readable file is a faithful copy of the library's text but not, for
this constant at least, of its elaborated terms; the accepted cell-layer
judgment above uses the library's definitions.

Earlier runs judged nothing: run 44774695098 failed at export, and run
[44796269901](https://github.com/wcook04/proof-reader/actions/runs/44796269901)
stopped every call with exit code 2 because the external checkers were not on
the runner's PATH while the job still showed green. The workflow now puts the
toolchain directory on PATH, stops if a checker is missing, and fails unless
the control is rejected and every positive comparison accepted.
<!-- /passage:sec-5-checking-workflow-and-status -->

## 6. Historical scope

<!-- passage:sec-6-historical-scope -->

This is an unforced smooth-data claim. The
[8 September 2026 announcement](https://openai.com/index/navier-stokes-solution/)
concerned forced Navier–Stokes; the
[11 September CMI statement](https://www.claymath.org/news/navier-stokes-announcement/)
does not validate this later construction. The distinction matters because
zero-force counterexamples would refute the unforced regularity alternatives
(A)/(B) as well as supply examples for (C)/(D).

[Bradshaw–Tsai's Open Problem 5.1](https://arxiv.org/html/1610.05680v1)
is a particularly direct antecedent for backward recurrent profiles.
[Pineau–Vicol's August 2026 version](https://arxiv.org/abs/2607.09619v2)
also belongs in the discussion: its exclusions concern specified parameter
regimes and do not constitute a blanket prohibition of these profiles.
Public announcement and reaction posts are not proof reviews.

On 20 November 2026 [Terence Tao](https://terrytao.wordpress.com/2026/11/20/unforced-euler-singularity-unforced-navier-stokes-singularity-and-the-generalized-riemann-hypothesis/)
listed this result with two others, ordered by how far each has been
digested. The first is a blow-up proof for the unforced incompressible Euler
equations by Alpöge, Buckmaster and Coiculescu, with a
[human-readable manuscript](https://cims.nyu.edu/~tristanb/cc.pdf) and a
[Lean formalization](https://github.com/mcoiculescu/EulerBlowupPublic).
He describes the Navier–Stokes paper as technically human-readable, with a
broadly clear strategy (a numerically built approximate discretely
self-similar solution, made exact by rigorous perturbation theory), and says
that a professionally written proof still needs more work. The third is
Alpöge's Lean-only proof of the Generalized Riemann Hypothesis.
<!-- /passage:sec-6-historical-scope -->

