
<!-- passage:front -->
# Annotations of the readable statements

**Navier–Stokes pages:** [the paper](../navier-stokes-paper/paper.pdf) · [index by number](../navier-stokes-index/paper.md) · [specialist digest](../navier-stokes/digest.md) · [full account, part I](../navier-stokes-part-1/paper.md) · [part II](../navier-stokes-part-2/paper.md) · [part III](../navier-stokes-appendix-b/paper.md) · [what the Lean states](../navier-stokes/paper.md) · **statement files** · [proof routes](../navier-stokes-routes/paper.md) · [proof routes in detail](../navier-stokes-route-details/paper.md) · [library guide](../navier-stokes-library-01/paper.md) · [cell layer guide](../navier-stokes-cell-guide/paper.md) · [cell reference](../navier-stokes-cell-reference/paper.md) · [cell layer and Appendix B](../navier-stokes/cell-layer-fidelity.md) · [certificate checker](../navier-stokes/certificate-checker.md)

Original annotations for the five statement modules at `ad53419de079eb8f95f60313473374624a348546`. Source reading and paper comparison are distinct from a proof replay.

Every source link is pinned. Pages in paper references are printed pages, equal to PDF pages in this edition.

Field paragraphs provide every structure-field gloss. Each opens the exact field lines. Other line-tie paragraphs isolate clauses or formulas inside a declaration.

<a id="001"></a>

### 001. Three-dimensional Euclidean space

`Breakdown.Space`: The paper’s physical and similarity spaces are represented by Euclidean three-vectors with the usual inner-product norm. This fixed dimension is used in the drift integration by parts as well as in the Navier–Stokes operators.

**Source.** [lean/Challenge.lean:10-10](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Challenge.lean#L10). Abbrev. **Paper.** Equation (1.1), p.1; profile space in (1.2), p.2.

**Library.** An identical source definition occurs at: [lean/Breakdown/Defs.lean:10-10](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Defs.lean#L10).

Encoding for `Breakdown.Space` (1): Fin 3 has exactly three coordinates; this is neither a variable-dimensional nor an empty ambient space.

Clause 1 of `Breakdown.Space`, lines 10-10: Fix the ambient physical space to R³. Paper: Equation (1.1), p.1. Source: [lean/Challenge.lean:10-10](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Challenge.lean#L10).

<a id="002"></a>

### 002. Coordinate unit vectors

`Breakdown.unitVector`: These are the three standard basis vectors used to write the divergence, Laplacian and gradient of (1.1). Coordinates are numbered 0, 1 and 2 in Lean.

**Source.** [lean/Challenge.lean:12-12](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Challenge.lean#L12). Def. **Paper.** Coordinate helper for equation (1.1), p.1; no separately numbered definition.

**Library.** An identical source definition occurs at: [lean/Breakdown/Defs.lean:12-12](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Defs.lean#L12).

Encoding for `Breakdown.unitVector` (1): Every basis vector has norm one, so these coordinate sums cannot collapse through an empty or zero basis.

Clause 1 of `Breakdown.unitVector`, lines 12-12: These are the three standard basis vectors used to write the divergence, Laplacian and gradient of (1.1). Paper: Coordinate helper for equation (1.1), p.1; no separately numbered definition. Source: [lean/Challenge.lean:12-12](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Challenge.lean#L12).

<a id="003"></a>

### 003. Divergence

`Breakdown.divergenceAt`: This is the trace of the spatial derivative, representing div u in (1.1) and div W in (1.2). The derivative is stored as a continuous linear map.

**Source.** [lean/Challenge.lean:14-15](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Challenge.lean#L14-L15). Def. **Paper.** Equations (1.1), p.1, and (1.2), p.2.

**Library.** An identical source definition occurs at: [lean/Breakdown/Defs.lean:14-15](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Defs.lean#L14-L15).

Encoding for `Breakdown.divergenceAt` (1): Mathlib’s fderiv is total and is zero when differentiability fails; the smooth-solution and smooth-profile hypotheses supply differentiability where this operator is used.

Clause 1 of `Breakdown.divergenceAt`, lines 14-15: This is the trace of the spatial derivative, representing div u in (1.1) and div W in (1.2). Paper: Equations (1.1), p.1, and (1.2), p.2. Source: [lean/Challenge.lean:14-15](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Challenge.lean#L14-L15).

<a id="004"></a>

### 004. Laplacian

`Breakdown.sumSecondPartialsAt`: The sum of the three diagonal second directional derivatives represents the vector Laplacian in (1.1). It uses the iterated Fréchet derivative rather than a componentwise array of scalar second derivatives.

**Source.** [lean/Challenge.lean:17-18](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Challenge.lean#L17-L18). Def. **Paper.** Equation (1.1), p.1; equation (1.2), p.2.

**Library.** An identical source definition occurs at: [lean/Breakdown/Defs.lean:17-18](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Defs.lean#L17-L18).

Encoding for `Breakdown.sumSecondPartialsAt` (1): The derivative expression is meaningful as the classical Laplacian under the surrounding smoothness hypotheses; it does not assert differentiability by itself.

Clause 1 of `Breakdown.sumSecondPartialsAt`, lines 17-18: The sum of the three diagonal second directional derivatives represents the vector Laplacian in (1.1). Paper: Equation (1.1), p.1; equation (1.2), p.2. Source: [lean/Challenge.lean:17-18](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Challenge.lean#L17-L18).

<a id="005"></a>

### 005. Pressure gradient

`Breakdown.gradientAt`: This reconstructs the vector ∇p from the three coordinate derivatives of the scalar pressure. Only the gradient enters the equation, so adding a function of time to p does not change this term.

**Source.** [lean/Challenge.lean:20-21](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Challenge.lean#L20-L21). Def. **Paper.** Equation (1.1), p.1; equation (1.2), p.2.

**Library.** An identical source definition occurs at: [lean/Breakdown/Defs.lean:20-21](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Defs.lean#L20-L21).

Encoding for `Breakdown.gradientAt` (1): The raw fderiv operation is total; smooth_pressure or the profile’s smooth-pressure clause supplies the needed regularity.

Clause 1 of `Breakdown.gradientAt`, lines 20-21: This reconstructs the vector ∇p from the three coordinate derivatives of the scalar pressure. Paper: Equation (1.1), p.1; equation (1.2), p.2. Source: [lean/Challenge.lean:20-21](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Challenge.lean#L20-L21).

<a id="006"></a>

### 006. Nonlinear transport

`Breakdown.advectionAt`: Applying the spatial derivative of v to v itself gives the paper’s (v·∇)v. This order of application fixes the convection convention used throughout the certificate files.

**Source.** [lean/Challenge.lean:23-24](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Challenge.lean#L23-L24). Def. **Paper.** Equation (1.1), p.1; equation (7.1), p.30.

**Library.** An identical source definition occurs at: [lean/Breakdown/Defs.lean:23-24](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Defs.lean#L23-L24).

Encoding for `Breakdown.advectionAt` (1): The operation does not carry a differentiability proof; the classical and weak interfaces provide separate regularity contracts.

Clause 1 of `Breakdown.advectionAt`, lines 23-24: Applying the spatial derivative of v to v itself gives the paper’s (v·∇)v. Paper: Equation (1.1), p.1; equation (7.1), p.30. Source: [lean/Challenge.lean:23-24](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Challenge.lean#L23-L24).

<a id="007"></a>

### 007. Global smooth solution

`Breakdown.IsSmoothSolution`: This is the global solution class used in the formal nonexistence conclusions, with viscosity ν and initial velocity u₀. Joint smoothness is required on the closed nonnegative-time half-space; the PDE and incompressibility are imposed at positive times.

**Source.** [lean/Challenge.lean:26-33](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Challenge.lean#L26-L33). Structure. **Paper.** Equation (1.1), p.1; definition of smooth solution in §1.1, p.2; formal endpoints in §1.5, pp.9-10.

**Library.** An identical source definition occurs at: [lean/Breakdown/Defs.lean:26-33](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Defs.lean#L26-L33).

Encoding for `Breakdown.IsSmoothSolution` (1): ContDiffOn controls the initial trace and prevents a jump at time zero.

Encoding for `Breakdown.IsSmoothSolution` (2): For t>0 the regularity domain contains a neighbourhood, so deriv, fderiv and iteratedFDeriv are actual derivatives there.

Encoding for `Breakdown.IsSmoothSolution` (3): Values at negative times are outside the regularity and PDE requirements.

Encoding for `Breakdown.IsSmoothSolution` (4): Periodicity and the energy restriction are added by the endpoint predicates, rather than by this structure.

Field `Breakdown.IsSmoothSolution.smooth_velocity`: The velocity is jointly smooth in time and space up to t=0. Paper: Definition of smooth solution, §1.1, p.2. Source: [lean/Challenge.lean:28-28](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Challenge.lean#L28).

Field `Breakdown.IsSmoothSolution.smooth_pressure`: The pressure is jointly smooth in time and space up to t=0. Paper: Definition of smooth solution, §1.1, p.2. Source: [lean/Challenge.lean:29-29](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Challenge.lean#L29).

Field `Breakdown.IsSmoothSolution.initial`: The velocity at t=0 equals the prescribed datum u₀ at every point. Paper: Definition of smooth solution, §1.1, p.2. Source: [lean/Challenge.lean:30-30](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Challenge.lean#L30).

Field `Breakdown.IsSmoothSolution.momentum`: The unforced momentum equation holds at every positive time, with viscosity ν. Paper: Equation (1.1) and viscosity scaling, p.1. Source: [lean/Challenge.lean:31-32](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Challenge.lean#L31-L32).

Field `Breakdown.IsSmoothSolution.incompressible`: The velocity has zero divergence at every positive time. Paper: Equation (1.1), p.1. Source: [lean/Challenge.lean:33-33](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Challenge.lean#L33).

<a id="008"></a>

### 008. Breakdown on the whole space

`Breakdown.BreakdownOnSpace`: For each positive viscosity, this asks for smooth compactly supported solenoidal data admitting no global smooth solution with uniformly bounded kinetic energy. It records a nonexistence endpoint and leaves the rate and profile convergence in Theorem 1.1 outside the conclusion.

**Source.** [lean/Challenge.lean:35-39](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Challenge.lean#L35-L39). Def. **Paper.** Theorem 1.1 and (1.6), p.3; finite-energy convention, p.2; formal endpoint, §1.5, pp.9-10.

**Library.** An identical source definition occurs at: [lean/Breakdown/Defs.lean:35-39](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Defs.lean#L35-L39).

Encoding for `Breakdown.BreakdownOnSpace` (1): The datum may depend on ν: the quantifier order is for every ν>0, there exists u₀.

Encoding for `Breakdown.BreakdownOnSpace` (2): The energy bound C is inside the forbidden solution existential; no fixed choice of a negative C can remove legitimate solutions.

Encoding for `Breakdown.BreakdownOnSpace` (3): The energy is an ENNReal lintegral bounded by finite ENNReal.ofReal C; no toReal conversion can turn infinite energy into zero.

Clause 1 of `Breakdown.BreakdownOnSpace`, lines 36-37: For each positive viscosity choose smooth compactly supported divergence-free initial data. Paper: Theorem 1.1, p.3. Source: [lean/Challenge.lean:36-37](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Challenge.lean#L36-L37).

Clause 2 of `Breakdown.BreakdownOnSpace`, lines 38-39: Exclude every global smooth solution for which one finite energy bound works at all nonnegative times. Paper: Finite-energy convention, §1.1, p.2; formal endpoint, §1.5, pp.9-10. Source: [lean/Challenge.lean:38-39](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Challenge.lean#L38-L39).

<a id="009"></a>

### 009. Breakdown on the torus

`Breakdown.BreakdownOnTorus`: For each positive viscosity, this asks for smooth solenoidal data of period one in each spatial coordinate admitting no global smooth solution with periodic velocity. The pressure remains unrestricted by periodicity, making the excluded class larger than the periodic-pressure class in the paper.

**Source.** [lean/Challenge.lean:41-45](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Challenge.lean#L41-L45). Def. **Paper.** Theorem 1.1 and (1.7), p.3; torus convention, §1.1, p.2; formal endpoint, §1.5, pp.9-10.

**Library.** An identical source definition occurs at: [lean/Breakdown/Defs.lean:41-45](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Defs.lean#L41-L45).

Encoding for `Breakdown.BreakdownOnTorus` (1): The torus is encoded by periodic functions on R³, rather than by a quotient type.

Encoding for `Breakdown.BreakdownOnTorus` (2): The existential pressure may be any smooth pressure; periodicity is imposed only on u₀ and u.

Encoding for `Breakdown.BreakdownOnTorus` (3): There is no whole-space energy condition here.

Clause 1 of `Breakdown.BreakdownOnTorus`, lines 42-43: For each positive viscosity choose smooth divergence-free data with period one along every coordinate. Paper: Theorem 1.1, p.3; torus convention, p.2. Source: [lean/Challenge.lean:42-43](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Challenge.lean#L42-L43).

Clause 2 of `Breakdown.BreakdownOnTorus`, lines 44-45: Exclude all global smooth solutions whose velocity retains the periods, regardless of pressure periodicity. Paper: Formal torus endpoint, §1.5, pp.9-10; compare the periodic-pressure convention on p.2. Source: [lean/Challenge.lean:44-45](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Challenge.lean#L44-L45).

<a id="010"></a>

### 010. Self-similar equation residual

`Breakdown.SimilarityResidual`: This is the left-hand side of the velocity equation in (1.2), before setting it to zero. Its time variable is the similarity time s, so it contains no reciprocal-period factor.

**Source.** [lean/Challenge.lean:47-49](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Challenge.lean#L47-L49). Def. **Paper.** Equation (1.2), p.2.

**Library.** An identical source definition occurs at: [lean/Breakdown/Defs.lean:47-49](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Defs.lean#L47-L49).

Encoding for `Breakdown.SimilarityResidual` (1): The classical derivative operations require the smoothness supplied by PeriodicSimilarityProfileExists.

Clause 1 of `Breakdown.SimilarityResidual`, lines 48-49: Assemble time differentiation, dilation drift, diffusion, convection and pressure gradient in similarity variables. Paper: Equation (1.2), p.2. Source: [lean/Challenge.lean:48-49](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Challenge.lean#L48-L49).

<a id="011"></a>

### 011. Smooth recurrent profile exists

`Breakdown.PeriodicSimilarityProfileExists`: A nonzero smooth pair (W,q) solves the self-similar equation and returns after a positive period P up to an orthogonal spatial transformation. The written premise includes second-derivative decay and pressure-gradient decay in addition to the two bounds displayed in (1.3).

**Source.** [lean/Challenge.lean:51-61](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Challenge.lean#L51-L61). Def. **Paper.** Equations (1.2)-(1.3), p.2; Theorem 1.1 and Remark 1.2, p.3.

**Library.** An identical source definition occurs at: [lean/Breakdown/Defs.lean:51-61](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Defs.lean#L51-L61).

Encoding for `Breakdown.PeriodicSimilarityProfileExists` (1): R is a linear isometric equivalence, so its inverse is genuine; reflections are allowed.

Encoding for `Breakdown.PeriodicSimilarityProfileExists` (2): The nonzero clause is pointwise, and smoothness prevents a null-set modification of zero from satisfying it.

Encoding for `Breakdown.PeriodicSimilarityProfileExists` (3): A single finite real C controls all times and all spatial points.

Encoding for `Breakdown.PeriodicSimilarityProfileExists` (4): Remark 1.2 supplies the higher velocity estimate by analysis; the pressure-gradient bound is an additional written formal requirement with no separate bound in (1.3).

Clause 1 of `Breakdown.PeriodicSimilarityProfileExists`, lines 52-55: Choose smooth velocity and pressure, an orthogonal transformation and a strictly positive period. Paper: Profile definition in §1.1, p.2. Source: [lean/Challenge.lean:52-55](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Challenge.lean#L52-L55).

Clause 2 of `Breakdown.PeriodicSimilarityProfileExists`, lines 56-57: Require the self-similar equation and incompressibility at every time and point. Paper: Equation (1.2), p.2. Source: [lean/Challenge.lean:56-57](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Challenge.lean#L56-L57).

Clause 3 of `Breakdown.PeriodicSimilarityProfileExists`, lines 58-58: Advance by one period and apply the spatial isometry to the field and its argument. Paper: Last relation in (1.2), p.2. Source: [lean/Challenge.lean:58-58](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Challenge.lean#L58).

Clause 4 of `Breakdown.PeriodicSimilarityProfileExists`, lines 59-59: Require a point at which the smooth velocity is nonzero. Paper: Nonzero-profile requirement, §1.1, p.2. Source: [lean/Challenge.lean:59-59](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Challenge.lean#L59).

Clause 5 of `Breakdown.PeriodicSimilarityProfileExists`, lines 60-60: Control spatial derivatives of orders zero, one and two by the corresponding inverse powers of 1+|y|. Paper: Equation (1.3), p.2, and Remark 1.2, p.3. Source: [lean/Challenge.lean:60-60](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Challenge.lean#L60).

Clause 6 of `Breakdown.PeriodicSimilarityProfileExists`, lines 61-61: Require inverse-cubic decay of the pressure gradient. Paper: Theorem 1.1, p.3; additional formal pressure bound with no separately numbered paper counterpart. Source: [lean/Challenge.lean:61-61](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Challenge.lean#L61).

<a id="012"></a>

### 012. Compactly supported scalar test

`Breakdown.IsTestFunction`: This supplies the scalar C∞ compactly supported test functions used to express weak spatial derivatives. Such tests make integration by parts local in the spatial variable.

**Source.** [lean/Challenge.lean:63-63](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Challenge.lean#L63). Def. **Paper.** Encoding helper for the distributional derivatives in §7.1, p.30; no separately numbered scalar-test definition.

**Library.** An identical source definition occurs at: [lean/Breakdown/Defs.lean:63-63](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Defs.lean#L63).

Encoding for `Breakdown.IsTestFunction` (1): A test is compactly supported in space; time is absent from this predicate.

Clause 1 of `Breakdown.IsTestFunction`, lines 63-63: This supplies the scalar C∞ compactly supported test functions used to express weak spatial derivatives. Paper: Encoding helper for the distributional derivatives in §7.1, p.30; no separately numbered scalar-test definition. Source: [lean/Challenge.lean:63-63](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Challenge.lean#L63).

<a id="013"></a>

### 013. Weak spatial gradient

`Breakdown.IsWeakGradient`: This represents G=∇f by coordinate integration by parts against every smooth compactly supported scalar test. Both f and G must be locally integrable, so the derivative identity is a distributional statement with meaningful local pairings.

**Source.** [lean/Challenge.lean:65-68](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Challenge.lean#L65-L68). Def. **Paper.** Distributional derivative convention in §7.1 and (7.4), p.30; space X in §2.1, p.10.

**Library.** An identical source definition occurs at: [lean/Breakdown/Defs.lean:65-68](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Defs.lean#L65-L68).

Encoding for `Breakdown.IsWeakGradient` (1): The derivative is supplied as data and constrained by the test identity; fderiv f is not used.

Encoding for `Breakdown.IsWeakGradient` (2): Mathlib’s Bochner integral is total, but local integrability and compact test support guard these particular integrals.

Clause 1 of `Breakdown.IsWeakGradient`, lines 66-66: Require local integrability of both the field and its supplied gradient. Paper: Distributional derivative convention, §7.1, p.30. Source: [lean/Challenge.lean:66-66](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Challenge.lean#L66).

Clause 2 of `Breakdown.IsWeakGradient`, lines 67-68: Test each coordinate derivative against every scalar smooth compactly supported function. Paper: Distributional derivatives used in (7.4), p.30. Source: [lean/Challenge.lean:67-68](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Challenge.lean#L67-L68).

<a id="014"></a>

### 014. Solenoidal space-time test

`Breakdown.IsSpaceTimeTestField`: These are the smooth compactly supported vector tests that remove pressure from the weak equation. Their divergence vanishes for every time and spatial point.

**Source.** [lean/Challenge.lean:70-72](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Challenge.lean#L70-L72). Def. **Paper.** Equation (7.2), p.30.

**Library.** An identical source definition occurs at: [lean/Breakdown/Defs.lean:70-72](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Defs.lean#L70-L72).

Encoding for `Breakdown.IsSpaceTimeTestField` (1): Support is compact in the joint time-space variable; these tests are not required to be time-periodic.

Clause 1 of `Breakdown.IsSpaceTimeTestField`, lines 71-72: Require joint smoothness, joint compact support and spatial divergence zero. Paper: Equation (7.2), p.30. Source: [lean/Challenge.lean:71-72](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Challenge.lean#L71-L72).

<a id="015"></a>

### 015. Weak self-similar equation

`Breakdown.weakSimilarityIntegrand`: This is the residual paired with a divergence-free test after moving time, drift, diffusion and convection derivatives onto that test. In three dimensions the half-velocity term and the integrated dilation drift combine to give the displayed negative unit coefficient on W·φ.

**Source.** [lean/Challenge.lean:74-80](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Challenge.lean#L74-L80). Def. **Paper.** Equation (1.2), p.2, tested as in (7.2), p.30.

**Library.** An identical source definition occurs at: [lean/Breakdown/Defs.lean:74-80](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Defs.lean#L74-L80).

Encoding for `Breakdown.weakSimilarityIntegrand` (1): The test’s derivatives are classical; W enters without a time derivative, and G supplies its weak spatial gradient.

Encoding for `Breakdown.weakSimilarityIntegrand` (2): The pressure term vanishes against the divergence-free tests.

Encoding for `Breakdown.weakSimilarityIntegrand` (3): WeakPeriodicSimilarityProfileExists separately requires this complete signed integrand to be Integrable before setting its integral to zero.

Clause 1 of `Breakdown.weakSimilarityIntegrand`, lines 76-78: Time integration by parts and the three-dimensional drift produce the negative time-test term, negative W·φ, and negative half radial-test term. Paper: Equation (1.2), p.2; weak testing in (7.2), p.30. Source: [lean/Challenge.lean:76-78](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Challenge.lean#L76-L78).

Clause 2 of `Breakdown.weakSimilarityIntegrand`, lines 79-79: Diffusion contributes the pairing of the weak gradient with the test gradient. Paper: Equation (1.2), p.2; weak testing in (7.2), p.30. Source: [lean/Challenge.lean:79-79](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Challenge.lean#L79).

Clause 3 of `Breakdown.weakSimilarityIntegrand`, lines 80-80: Incompressibility moves the nonlinear transport derivative onto the test. Paper: Equation (1.2), p.2; weak testing in (7.2), p.30. Source: [lean/Challenge.lean:80-80](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Challenge.lean#L80).

<a id="016"></a>

### 016. Weak recurrent profile exists

`Breakdown.WeakPeriodicSimilarityProfileExists`: This is the explicit weak-profile interface used between the certificate construction and breakdown: recurrent velocity, supplied weak derivatives, uniform L⁶ and gradient-L² bounds, and the pressure-free distributional equation. Its quantifiers are more detailed than the continuous-X hypothesis in Proposition 7.11.

**Source.** [lean/Challenge.lean:82-99](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Challenge.lean#L82-L99). Def. **Paper.** Related weak-to-smooth route: Proposition 7.11 and (7.62), p.44; equation (7.2), p.30; X in §2.1, p.10.

**Library.** An identical source definition occurs at: [lean/Breakdown/Defs.lean:82-99](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Defs.lean#L82-L99).

Encoding for `Breakdown.WeakPeriodicSimilarityProfileExists` (1): The same finite real C bounds the sixth-power velocity integral and squared operator-norm gradient integral for every time.

Encoding for `Breakdown.WeakPeriodicSimilarityProfileExists` (2): The gradient in this predicate uses the norm on continuous linear maps; the certificate’s matSq is the Frobenius square, an equivalent finite-dimensional norm.

Encoding for `Breakdown.WeakPeriodicSimilarityProfileExists` (3): The second weak derivative is required for almost every time, whereas the first weak gradient and its spatial-a.e. divergence statement are required for every time.

Encoding for `Breakdown.WeakPeriodicSimilarityProfileExists` (4): The final nontriviality clause is on product almost-everywhere equivalence classes and rejects null-set spikes.

Encoding for `Breakdown.WeakPeriodicSimilarityProfileExists` (5): The signed weak residual must be integrable; equality of a totalized integral to zero alone would not be the stated requirement.

Clause 1 of `Breakdown.WeakPeriodicSimilarityProfileExists`, lines 83-85: Choose the velocity, two supplied spatial derivative fields, a positive period and an isometry. Paper: Profile period in (1.2), p.2; related Proposition 7.11, p.44. Source: [lean/Challenge.lean:83-85](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Challenge.lean#L83-L85).

Clause 2 of `Breakdown.WeakPeriodicSimilarityProfileExists`, lines 86-88: Require joint almost-everywhere strong measurability for the velocity and both derivative fields. Paper: Measurability conventions for H and D_S, §7.1, p.30. Source: [lean/Challenge.lean:86-88](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Challenge.lean#L86-L88).

Clause 3 of `Breakdown.WeakPeriodicSimilarityProfileExists`, lines 89-89: Require the velocity recurrence pointwise in time and space. Paper: Last relation in (1.2), p.2. Source: [lean/Challenge.lean:89-89](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Challenge.lean#L89).

Clause 4 of `Breakdown.WeakPeriodicSimilarityProfileExists`, lines 90-92: The first derivative identity holds for every time; the second derivative identity holds for almost every time. Paper: Distributional derivative convention and (7.4), p.30. Source: [lean/Challenge.lean:90-92](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Challenge.lean#L90-L92).

Clause 5 of `Breakdown.WeakPeriodicSimilarityProfileExists`, lines 93-93: At every time the supplied gradient has trace zero almost everywhere in space. Paper: Incompressibility in (1.2), p.2. Source: [lean/Challenge.lean:93-93](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Challenge.lean#L93).

Clause 6 of `Breakdown.WeakPeriodicSimilarityProfileExists`, lines 94-95: One finite bound controls the velocity’s sixth-power integral and the gradient’s squared integral at every time. Paper: Space X in §2.1, p.10; related Proposition 7.11, p.44. Source: [lean/Challenge.lean:94-95](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Challenge.lean#L94-L95).

Clause 7 of `Breakdown.WeakPeriodicSimilarityProfileExists`, lines 96-96: Require a finite squared second-derivative integral over one positive period. Paper: Equation (7.4), p.30; related regularity route in Proposition 7.11, p.44. Source: [lean/Challenge.lean:96-96](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Challenge.lean#L96).

Clause 8 of `Breakdown.WeakPeriodicSimilarityProfileExists`, lines 97-98: For every solenoidal test, require the weak residual to be integrable and its integral to vanish. Paper: Equation (7.2), p.30, applied to the profile equation (1.2), p.2. Source: [lean/Challenge.lean:97-98](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Challenge.lean#L97-L98).

Clause 9 of `Breakdown.WeakPeriodicSimilarityProfileExists`, lines 99-99: Exclude velocity fields that vanish almost everywhere on space-time. Paper: Nonzero-profile requirement, §1.1, p.2; Proposition 7.11, p.44. Source: [lean/Challenge.lean:99-99](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Challenge.lean#L99).

<a id="017"></a>

### 017. Profile gives whole-space breakdown

`Breakdown.breakdown_on_space`: The exported implication sends a smooth recurrent profile to the whole-space nonexistence endpoint. The readable theorem contains a proof placeholder; Solution.lean supplies the implementation from the library.

**Source.** [lean/Challenge.lean:101-102](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Challenge.lean#L101-L102). Readable theorem stub. **Paper.** Theorem 1.1 and (1.6), p.3; formal endpoint in §1.5, pp.9-10.

**Library.** Implementation source: [lean/Solution.lean:17-18](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Solution.lean#L17-L18).

Encoding for `Breakdown.breakdown_on_space` (1): The profile remains an assumption; this theorem does not produce a numerical profile or validate a certificate.

Comparison for `Breakdown.breakdown_on_space`: The written profile premise includes extra decay bounds, and the conclusion retains nonexistence for every positive viscosity while omitting the constructed trajectory, rate and convergence in Theorem 1.1. Relating the paper and formal endpoints uses the analytic bridges described in the authors’ README.

Clause 1 of `Breakdown.breakdown_on_space`, lines 101-101: The readable implication has an explicit hypothesis and endpoint; its proof is supplied separately in Solution.lean. Paper: Theorem 1.1 and (1.6), p.3; formal endpoint in §1.5, pp.9-10. Source: [lean/Challenge.lean:101-101](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Challenge.lean#L101).

<a id="018"></a>

### 018. Profile gives torus breakdown

`Breakdown.breakdown_on_torus`: The exported implication sends a smooth recurrent profile to the periodic-velocity nonexistence endpoint. Its implementation also handles the pressure normalization needed to exclude global solutions whose pressure was not assumed periodic.

**Source.** [lean/Challenge.lean:104-105](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Challenge.lean#L104-L105). Readable theorem stub. **Paper.** Theorem 1.1 and (1.7), p.3; torus convention, p.2; formal endpoint in §1.5, pp.9-10.

**Library.** Implementation source: [lean/Solution.lean:20-21](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Solution.lean#L20-L21).

Encoding for `Breakdown.breakdown_on_torus` (1): The conclusion has neither an explicit blow-up time nor a rate or local convergence estimate.

Encoding for `Breakdown.breakdown_on_torus` (2): The theorem shown here is a stub, with the proof exposed separately by Solution.lean.

Comparison for `Breakdown.breakdown_on_torus`: The formal conclusion excludes a larger pressure class than the paper’s periodic-pressure formulation and omits the trajectory, rate and convergence of (1.7). The hypothesis also writes additional profile decay bounds, so a single unqualified stronger/weaker label would hide changes in both directions.

Clause 1 of `Breakdown.breakdown_on_torus`, lines 104-104: The readable implication has an explicit hypothesis and endpoint; its proof is supplied separately in Solution.lean. Paper: Theorem 1.1 and (1.7), p.3; torus convention, p.2; formal endpoint in §1.5, pp.9-10. Source: [lean/Challenge.lean:104-104](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Challenge.lean#L104).

<a id="019"></a>

### 019. Weak profile gives breakdown

`Breakdown.breakdown_on_space_of_weak`: This routes the explicit weak-profile interface directly to whole-space breakdown. The paper instead presents the related passage through a smooth profile in Proposition 7.11 before applying Theorem 1.1.

**Source.** [lean/Challenge.lean:107-108](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Challenge.lean#L107-L108). Readable theorem stub. **Paper.** Related route: Proposition 7.11, p.44, and Theorem 1.1, p.3; no separately stated paper theorem has this exact weak premise.

**Library.** Implementation source: [lean/Solution.lean:23-24](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Solution.lean#L23-L24).

Encoding for `Breakdown.breakdown_on_space_of_weak` (1): The weak hypothesis includes actual integrability and product-a.e. nontriviality; a pointwise spike in a zero equivalence class is excluded.

Encoding for `Breakdown.breakdown_on_space_of_weak` (2): This is a readable theorem stub, not a proof replay receipt.

Comparison for `Breakdown.breakdown_on_space_of_weak`: The paper has no theorem with precisely this explicit weak-profile hypothesis and direct whole-space endpoint. Its related route is regularization in Proposition 7.11 followed by Theorem 1.1.

Clause 1 of `Breakdown.breakdown_on_space_of_weak`, lines 107-107: The readable implication has an explicit hypothesis and endpoint; its proof is supplied separately in Solution.lean. Paper: Related route: Proposition 7.11, p.44, and Theorem 1.1, p.3; no separately stated paper theorem has this exact weak premise. Source: [lean/Challenge.lean:107-107](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Challenge.lean#L107).

<a id="020"></a>

### 020. Space-time symmetry

`Breakdown.Symmetry`: A symmetry pairs an orthogonal transformation R with a shift θ₀ in normalized period-one time. The set Γ may be empty and is not required to be supplied as a group.

**Source.** [lean/CertificateChallenge.lean:10-10](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L10). Abbrev. **Paper.** Equation (7.5), p.30.

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/Statement.lean:10-10](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Statement.lean#L10).

Encoding for `Breakdown.Symmetry` (1): The time shift is in normalized time θ; in the final profile it becomes θ₀S, as in (7.39), p.35.

Clause 1 of `Breakdown.Symmetry`, lines 10-10: A symmetry pairs an orthogonal transformation R with a shift θ₀ in normalized period-one time. Paper: Equation (7.5), p.30. Source: [lean/CertificateChallenge.lean:10-10](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L10).

<a id="021"></a>

### 021. Squared gradient matrix norm

`Breakdown.matSq`: Summing the squared lengths of the three coordinate directional derivatives gives the Frobenius square used for |∇v|² in Section 7. This differs from the operator-norm notation used by the weak-profile endpoint, although the two norms are equivalent in dimension three.

**Source.** [lean/CertificateChallenge.lean:12-12](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L12). Def. **Paper.** Matrix inner-product convention in §7.1, p.30; weighted norm (7.14), p.32.

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/Statement.lean:12-12](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Statement.lean#L12).

Encoding for `Breakdown.matSq` (1): The paper writes (∇v)ⱼₖ=∂ⱼvₖ; in Lean this component is (G(eⱼ))ₖ, giving the same scalar norm despite the different storage convention.

Clause 1 of `Breakdown.matSq`, lines 12-12: Summing the squared lengths of the three coordinate directional derivatives gives the Frobenius square used for |∇v|² in Section 7. Paper: Matrix inner-product convention in §7.1, p.30; weighted norm (7.14), p.32. Source: [lean/CertificateChallenge.lean:12-12](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L12).

<a id="022"></a>

### 022. Gradient matrix pairing

`Breakdown.matInner`: This is the Frobenius inner product of two derivative matrices written through their coordinate columns. It supplies the weak diffusion pairing and the pinning functional ℓᵢ.

**Source.** [lean/CertificateChallenge.lean:14-15](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L14-L15). Def. **Paper.** Matrix inner-product convention in §7.1, p.30; pinning (7.11), p.31.

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/Statement.lean:14-15](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Statement.lean#L14-L15).

Encoding for `Breakdown.matInner` (1): The paper writes (∇v)ⱼₖ=∂ⱼvₖ; applying G to eⱼ produces the vector with components indexed by k, so the pairing agrees after matching these indices.

Clause 1 of `Breakdown.matInner`, lines 14-15: This is the Frobenius inner product of two derivative matrices written through their coordinate columns. Paper: Matrix inner-product convention in §7.1, p.30; pinning (7.11), p.31. Source: [lean/CertificateChallenge.lean:14-15](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L14-L15).

<a id="023"></a>

### 023. Trace of the weak Hessian

`Breakdown.secondDerivTrace`: Tracing the two spatial input directions of H gives the vector Laplacian represented by the supplied weak Hessian. It is the quantity controlled by the graph condition defining D_S.

**Source.** [lean/CertificateChallenge.lean:17-18](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L17-L18). Def. **Paper.** Equation (7.4), p.30; weighted norm (7.14), p.32.

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/Statement.lean:17-18](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Statement.lean#L17-L18).

Encoding for `Breakdown.secondDerivTrace` (1): This is an algebraic trace of supplied data; IsPerturbation or IsProfileField connects H to actual weak derivatives.

Clause 1 of `Breakdown.secondDerivTrace`, lines 17-18: Tracing the two spatial input directions of H gives the vector Laplacian represented by the supplied weak Hessian. Paper: Equation (7.4), p.30; weighted norm (7.14), p.32. Source: [lean/CertificateChallenge.lean:17-18](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L17-L18).

<a id="024"></a>

### 024. Integral over one normalized period

`Breakdown.periodLIntegral`: This integrates a nonnegative density over θ∈[0,1] and all of R³, returning an extended nonnegative real. The period normalization matches the Hilbert-space convention of Section 7.

**Source.** [lean/CertificateChallenge.lean:20-21](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L20-L21). Def. **Paper.** Hilbert-space H and period-one convention, §7.1, p.30.

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/Statement.lean:20-21](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Statement.lean#L20-L21).

Encoding for `Breakdown.periodLIntegral` (1): ENNReal.ofReal truncates negative inputs to zero; arbitrary signed f therefore cannot be interpreted as a signed integral through this helper.

Encoding for `Breakdown.periodLIntegral` (2): The integral may be infinite, so finiteness must be supplied before using toReal.

Encoding for `Breakdown.periodLIntegral` (3): Replacing the paper’s (0,1) by [0,1] changes only time endpoints of Lebesgue measure zero.

Clause 1 of `Breakdown.periodLIntegral`, lines 20-21: This integrates a nonnegative density over θ∈[0,1] and all of R³, returning an extended nonnegative real. Paper: Hilbert-space H and period-one convention, §7.1, p.30. Source: [lean/CertificateChallenge.lean:20-21](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L20-L21).

<a id="025"></a>

### 025. Integral restricted to a spatial ball

`Breakdown.periodBallLIntegral`: The earlier certificate also measures squared forcing on a closed ball during one normalized period. This local-ball quantity has no finite-row counterpart in the paper’s definition of [F].

**Source.** [lean/CertificateChallenge.lean:23-24](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L23-L24). Def. **Paper.** Earlier formal alternative to the right-side seminorm (7.17), p.32; no identical printed condition.

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/Statement.lean:23-24](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Statement.lean#L23-L24).

Encoding for `Breakdown.periodBallLIntegral` (1): The radius is not required to be positive in CertificateData or IsCertificate; a nonpositive radius gives a null spatial domain for Lebesgue integration.

Encoding for `Breakdown.periodBallLIntegral` (2): ENNReal.ofReal clips negative inputs, and the value can be infinite.

Encoding for `Breakdown.periodBallLIntegral` (3): A local L² restriction is generally infinite-rank and must not be described as a finite list of row pairings.

Clause 1 of `Breakdown.periodBallLIntegral`, lines 23-24: Restrict the space integral to the closed ball while retaining the normalized time period. Paper: Compare (7.17), p.32; earlier local-ball seminorm has no identical printed counterpart. Source: [lean/CertificateChallenge.lean:23-24](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L23-L24).

<a id="026"></a>

### 026. Period-averaged L² norm

`Breakdown.periodNorm`: For a measurable field with finite squared integral, this is the H norm of Section 7. It first converts the extended nonnegative integral to a real number and then takes its square root.

**Source.** [lean/CertificateChallenge.lean:26-27](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L26-L27). Def. **Paper.** Hilbert-space H norm, §7.1, p.30.

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/Statement.lean:26-27](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Statement.lean#L26-L27).

Encoding for `Breakdown.periodNorm` (1): ENNReal.toReal sends infinity to zero, so this raw helper is not an L² norm on arbitrary fields.

Encoding for `Breakdown.periodNorm` (2): IsCertificate.coercive explicitly requires the right side’s squared integral to be finite; finite residual budgets provide the corresponding guard for residual fields.

Clause 1 of `Breakdown.periodNorm`, lines 26-27: For a measurable field with finite squared integral, this is the H norm of Section 7. Paper: Hilbert-space H norm, §7.1, p.30. Source: [lean/CertificateChallenge.lean:26-27](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L26-L27).

<a id="027"></a>

### 027. Local period-averaged L² norm

`Breakdown.periodBallNorm`: This is the earlier certificate’s L² norm over one period and a spatial ball. Its coefficient enters the older coercivity and residual-size estimates alongside the full H norm.

**Source.** [lean/CertificateChallenge.lean:29-30](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L29-L30). Def. **Paper.** Earlier formal alternative to [F] in (7.17)-(7.18), p.32, and (7.23)-(7.24), p.33.

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/Statement.lean:29-30](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Statement.lean#L29-L30).

Encoding for `Breakdown.periodBallNorm` (1): The same toReal-infinity default as periodNorm applies to arbitrary inputs.

Encoding for `Breakdown.periodBallNorm` (2): For an admissible right side the global L² hypothesis also makes the restricted integral finite.

Encoding for `Breakdown.periodBallNorm` (3): A zero or negative ball radius is allowed and makes this localized contribution vanish; it does not discharge the remaining certificate clauses.

Clause 1 of `Breakdown.periodBallNorm`, lines 29-30: Take the square root of the finite restricted integral when the L² guard is available. Paper: Compare (7.17)-(7.18), p.32; no identical local-ball condition in the current paper. Source: [lean/CertificateChallenge.lean:29-30](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L29-L30).

<a id="028"></a>

### 028. Euclidean norm of coefficients

`Breakdown.vecNorm`: This is the Euclidean norm of a finite multiplier or pin vector, used as |β| and |ℓ(v)| in Section 7. The index size is the certificate’s multiplier dimension.

**Source.** [lean/CertificateChallenge.lean:32-32](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L32). Def. **Paper.** Equations (7.14) and (7.18), p.32.

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/Statement.lean:32-32](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Statement.lean#L32).

Encoding for `Breakdown.vecNorm` (1): When k=0 the sum is empty and the norm is zero; the paper explicitly permits zero dimensions on p.35.

Clause 1 of `Breakdown.vecNorm`, lines 32-32: This is the Euclidean norm of a finite multiplier or pin vector, used as |β| and |ℓ(v)| in Section 7. Paper: Equations (7.14) and (7.18), p.32. Source: [lean/CertificateChallenge.lean:32-32](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L32).

<a id="029"></a>

### 029. Normalized time periodicity

`Breakdown.IsTimePeriodic`: This is period one in θ=s/S, the common convention for the approximate fields, perturbations and forcings in Section 7. It is independent of the separately supplied positive physical period.

**Source.** [lean/CertificateChallenge.lean:34-34](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L34). Def. **Paper.** Normalized-time convention and equation (7.1), p.30.

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/Statement.lean:34-34](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Statement.lean#L34).

Encoding for `Breakdown.IsTimePeriodic` (1): The recurrence is pointwise for every time and point, even when the surrounding field is used through an almost-everywhere class.

Clause 1 of `Breakdown.IsTimePeriodic`, lines 34-34: This is period one in θ=s/S, the common convention for the approximate fields, perturbations and forcings in Section 7. Paper: Normalized-time convention and equation (7.1), p.30. Source: [lean/CertificateChallenge.lean:34-34](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L34).

<a id="030"></a>

### 030. Unrestricted space-time test

`Breakdown.IsSpaceTimeTestVector`: These smooth compactly supported vector tests encode the weak transport derivative before pressure is removed. They have no divergence-free condition, unlike IsSpaceTimeTestField.

**Source.** [lean/CertificateChallenge.lean:36-38](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L36-L38). Def. **Paper.** Distributional derivative convention and equation (7.4), §7.1, p.30; no separately numbered unrestricted-test definition.

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/Statement.lean:36-38](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Statement.lean#L36-L38).

Encoding for `Breakdown.IsSpaceTimeTestVector` (1): Compact support is in the joint time-space variable; there is no periodicity requirement.

Clause 1 of `Breakdown.IsSpaceTimeTestVector`, lines 36-38: These smooth compactly supported vector tests encode the weak transport derivative before pressure is removed. Paper: Distributional derivative convention and equation (7.4), §7.1, p.30; no separately numbered unrestricted-test definition. Source: [lean/CertificateChallenge.lean:36-38](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L36-L38).

<a id="031"></a>

### 031. Admissible weak perturbation

`Breakdown.IsPerturbation`: This represents v∈D_S^Γ by velocity v, weak spatial derivatives G and H, and a separate field g for P⁻¹∂θv+½v+½y·∇v. The Laplacian is kept separate, so T_Pv is represented by g minus the trace of H.

**Source.** [lean/CertificateChallenge.lean:40-62](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L40-L62). Structure. **Paper.** Equation (7.4) and Γ-invariance (7.5), p.30; space X in §2.1, p.10.

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/Statement.lean:40-62](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Statement.lean#L40-L62).

Encoding for `Breakdown.IsPerturbation` (1): The structure has no standalone hypothesis P>0; certificate period_pos supplies it before this predicate is used in the main route.

Encoding for `Breakdown.IsPerturbation` (2): Only the combined time-and-dilation derivative g is required to lie in L², as in the discussion following (7.4).

Encoding for `Breakdown.IsPerturbation` (3): Weak derivative and L⁶ conditions hold for almost every time; the recurrence fields are pointwise.

Encoding for `Breakdown.IsPerturbation` (4): The Hessian’s trace has a finite period L² integral; this field does not itself assert a finite integral of every Hessian component.

Encoding for `Breakdown.IsPerturbation` (5): Raw transport pairings use totalized Bochner integrals; their analytic interpretation requires the local integrability derived from the surrounding Sobolev and graph conditions.

Field `Breakdown.IsPerturbation.measurable_velocity`: The perturbation velocity is jointly measurable up to a null set. Paper: D_S definition and (7.4), p.30. Source: [lean/CertificateChallenge.lean:43-43](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L43).

Field `Breakdown.IsPerturbation.measurable_gradient`: The supplied weak gradient is jointly measurable up to a null set. Paper: D_S definition and (7.4), p.30. Source: [lean/CertificateChallenge.lean:44-44](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L44).

Field `Breakdown.IsPerturbation.measurable_secondDeriv`: The supplied weak Hessian is jointly measurable up to a null set. Paper: Distributional derivatives in (7.4), p.30. Source: [lean/CertificateChallenge.lean:45-45](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L45).

Field `Breakdown.IsPerturbation.measurable_derivative`: The combined time-and-dilation derivative g is jointly measurable up to a null set. Paper: Discussion after (7.4), p.30. Source: [lean/CertificateChallenge.lean:46-46](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L46).

Field `Breakdown.IsPerturbation.periodic_velocity`: The velocity has period one in normalized time. Paper: Period-one convention before (7.4), p.30. Source: [lean/CertificateChallenge.lean:47-47](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L47).

Field `Breakdown.IsPerturbation.periodic_gradient`: The chosen gradient representative has period one. Paper: Period-one representation of D_S, §7.1, p.30. Source: [lean/CertificateChallenge.lean:48-48](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L48).

Field `Breakdown.IsPerturbation.periodic_secondDeriv`: The chosen Hessian representative has period one. Paper: Period-one representation of D_S, §7.1, p.30. Source: [lean/CertificateChallenge.lean:49-49](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L49).

Field `Breakdown.IsPerturbation.periodic_derivative`: The chosen combined derivative g has period one. Paper: Period-one representation of D_S, §7.1, p.30. Source: [lean/CertificateChallenge.lean:50-50](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L50).

Field `Breakdown.IsPerturbation.weak_gradient`: For almost every time, G is the distributional spatial derivative of v. Paper: Distributional derivatives in §7.1 and (7.4), p.30. Source: [lean/CertificateChallenge.lean:51-51](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L51).

Field `Breakdown.IsPerturbation.weak_secondDeriv`: For almost every time, each column of G has the weak spatial derivative supplied by H. Paper: Distributional derivatives in (7.4), p.30. Source: [lean/CertificateChallenge.lean:52-53](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L52-L53).

Field `Breakdown.IsPerturbation.divergence_free`: The trace of G vanishes for almost every time and almost every spatial point. Paper: Space X in §2.1, p.10; D_S in (7.4), p.30. Source: [lean/CertificateChallenge.lean:54-54](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L54).

Field `Breakdown.IsPerturbation.sixth_power`: The velocity lies in spatial L⁶ for almost every time. Paper: Space X in §2.1, p.10; D_S in (7.4), p.30. Source: [lean/CertificateChallenge.lean:55-55](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L55).

Field `Breakdown.IsPerturbation.gradient_finite`: The Frobenius square of G has finite integral over one period. Paper: D_S as a subspace of L²_loc(R;X), §7.1, p.30. Source: [lean/CertificateChallenge.lean:56-56](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L56).

Field `Breakdown.IsPerturbation.sumSecondPartials_finite`: The trace of H, representing Δv, has finite squared integral over one period. Paper: Equation (7.4), p.30. Source: [lean/CertificateChallenge.lean:57-57](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L57).

Field `Breakdown.IsPerturbation.derivative_finite`: The combined derivative g has finite squared integral over one period. Paper: Equation (7.4) and its following explanation, p.30. Source: [lean/CertificateChallenge.lean:58-58](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L58).

Field `Breakdown.IsPerturbation.transport`: Against every unrestricted compact vector test, g equals the weak time-and-dilation derivative of v. Paper: Equation (7.1) and discussion following (7.4), p.30. Source: [lean/CertificateChallenge.lean:59-61](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L59-L61).

Field `Breakdown.IsPerturbation.invariant`: For each prescribed symmetry, the velocity transforms equivariantly almost everywhere in space-time. Paper: Equation (7.5), p.30. Source: [lean/CertificateChallenge.lean:62-62](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L62).

<a id="032"></a>

### 032. Linear equation modulo pressure

`Breakdown.IsRightSide`: This states that F represents T_Pv+(W·∇)v+(v·∇)W plus the finite actuator force when paired with every solenoidal test. The Laplacian appears through the gradient pairing, and a pressure gradient is invisible to these tests.

**Source.** [lean/CertificateChallenge.lean:64-70](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L64-L70). Def. **Paper.** Equations (7.2), p.30, (7.13) and (7.18), p.32.

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/Statement.lean:64-70](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Statement.lean#L64-L70).

Encoding for `Breakdown.IsRightSide` (1): This predicate alone does not assert measurability or L² finiteness of F; IsCertificate.coercive supplies them separately.

Encoding for `Breakdown.IsRightSide` (2): The supplied g is the time-and-dilation part only; diffusion is recovered by integration by parts from G.

Encoding for `Breakdown.IsRightSide` (3): The universal quantifier includes right sides with a gradient component; F is not assumed divergence-free.

Clause 1 of `Breakdown.IsRightSide`, lines 67-68: Test the asserted right side against every solenoidal compact space-time test. Paper: Equality modulo gradients, (7.2), p.30. Source: [lean/CertificateChallenge.lean:67-68](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L67-L68).

Clause 2 of `Breakdown.IsRightSide`, lines 69-70: Pair the combined derivative, both linear convection terms, actuator force and weak diffusion with the test. Paper: Linear convection (7.13) and the premise of (7.18), p.32. Source: [lean/CertificateChallenge.lean:69-70](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L69-L70).

<a id="033"></a>

### 033. Squared weighted perturbation norm

`Breakdown.weightedEnergy`: This is ∥v∥²_w from (7.14), written using the supplied gradient and Hessian trace. The multiplier contribution is added separately in the coercive estimate.

**Source.** [lean/CertificateChallenge.lean:72-74](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L72-L74). Def. **Paper.** Equation (7.14), p.32.

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/Statement.lean:72-74](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Statement.lean#L72-L74).

Encoding for `Breakdown.weightedEnergy` (1): A bounded measurable positive weight and the perturbation’s finite derivative integrals are needed before treating the totalized real value as the intended energy.

Encoding for `Breakdown.weightedEnergy` (2): ENNReal.ofReal clips a negative density and toReal maps infinity to zero; IsCertificate’s weight and finiteness clauses prevent these defaults on admissible inputs.

Clause 1 of `Breakdown.weightedEnergy`, lines 72-74: This is ∥v∥²_w from (7.14), written using the supplied gradient and Hessian trace. Paper: Equation (7.14), p.32. Source: [lean/CertificateChallenge.lean:72-74](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L72-L74).

<a id="034"></a>

### 034. Linear pinning functional

`Breakdown.pinValue`: With χ=Ξᵢ and G=∇v, this is the pin ℓᵢ(v) used to remove the finite-dimensional defect in the linearized equation. It is the signed period pairing of the two derivative-matrix fields.

**Source.** [lean/CertificateChallenge.lean:76-77](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L76-L77). Def. **Paper.** Equation (7.11), p.31.

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/Statement.lean:76-77](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Statement.lean#L76-L77).

Encoding for `Breakdown.pinValue` (1): The Bochner integral is totalized; pin_finite together with gradient_finite provides the L² pairing control in certificate applications.

Encoding for `Breakdown.pinValue` (2): The pin matrix need not itself be a derivative, divergence-free, or periodic in this readable predicate.

Clause 1 of `Breakdown.pinValue`, lines 76-77: With χ=Ξᵢ and G=∇v, this is the pin ℓᵢ(v) used to remove the finite-dimensional defect in the linearized equation. Paper: Equation (7.11), p.31. Source: [lean/CertificateChallenge.lean:76-77](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L76-L77).

<a id="035"></a>

### 035. Stationary test field for the form

`Breakdown.IsProfileField`: This is the spatial test class used in the frozen quadratic-form estimate: u∈X with a weak Hessian and Δu∈L². Only Γ symmetries having zero time shift constrain this stationary field.

**Source.** [lean/CertificateChallenge.lean:79-88](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L79-L88). Structure. **Paper.** Equation (7.22), p.33; space X in §2.1, p.10.

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/Statement.lean:79-88](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Statement.lean#L79-L88).

Encoding for `Breakdown.IsProfileField` (1): The predicate is spatial and has no time variable.

Encoding for `Breakdown.IsProfileField` (2): Its L⁶ requirement selects the homogeneous Sobolev representative and rules out nonzero constant velocities.

Encoding for `Breakdown.IsProfileField` (3): Only the Hessian trace is explicitly square-integrable here; do not replace this clause by a full-Hessian norm without a bridge.

Field `Breakdown.IsProfileField.weak_gradient`: G is the weak spatial derivative of the stationary field. Paper: Test class for (7.22), p.33. Source: [lean/CertificateChallenge.lean:81-81](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L81).

Field `Breakdown.IsProfileField.weak_secondDeriv`: H supplies the weak derivative of every column of G. Paper: Test class for (7.22), p.33. Source: [lean/CertificateChallenge.lean:82-83](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L82-L83).

Field `Breakdown.IsProfileField.divergence_free`: The stationary field is divergence-free almost everywhere through the trace of G. Paper: Space X in §2.1, p.10; (7.22), p.33. Source: [lean/CertificateChallenge.lean:84-84](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L84).

Field `Breakdown.IsProfileField.sixth_power`: The stationary field belongs to L⁶(R³). Paper: Space X in §2.1, p.10; (7.22), p.33. Source: [lean/CertificateChallenge.lean:85-85](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L85).

Field `Breakdown.IsProfileField.gradient_finite`: The weak gradient has finite Frobenius L² norm. Paper: Space X in §2.1, p.10; (7.22), p.33. Source: [lean/CertificateChallenge.lean:86-86](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L86).

Field `Breakdown.IsProfileField.sumSecondPartials_finite`: The trace of H, representing the Laplacian, lies in L². Paper: Test class for (7.22), p.33. Source: [lean/CertificateChallenge.lean:87-87](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L87).

Field `Breakdown.IsProfileField.invariant`: The field is invariant under each spatial isometry paired with a zero time shift in Γ. Paper: Symmetry restriction after (7.22), p.33. Source: [lean/CertificateChallenge.lean:88-88](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L88).

<a id="036"></a>

### 036. Frozen quadratic form

`Breakdown.frozenForm`: This is the left-hand side of (7.22), evaluated at one time of the approximate profile. The convection term is paired with minus the Laplacian, so its displayed sign agrees with the paper after expanding that pairing.

**Source.** [lean/CertificateChallenge.lean:90-93](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L90-L93). Def. **Paper.** Equation (7.22), p.33.

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/Statement.lean:90-93](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Statement.lean#L90-L93).

Encoding for `Breakdown.frozenForm` (1): The input named w is the test velocity here, rather than the scalar weight.

Encoding for `Breakdown.frozenForm` (2): The signed Bochner integrals need the stationary field’s Sobolev regularity and the profile bounds in certificate applications.

Clause 1 of `Breakdown.frozenForm`, lines 92-93: Combine Laplacian energy, one quarter of the gradient energy and the two linear convection pairings. Paper: Equation (7.22), p.33. Source: [lean/CertificateChallenge.lean:92-93](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L92-L93).

<a id="037"></a>

### 037. Squared weighted spatial norm

`Breakdown.stationaryEnergy`: This is |u|²_w, the spatial weighted energy used on the right-hand side of (7.22). The trace of H represents Δu and matSq G represents the Frobenius square of ∇u.

**Source.** [lean/CertificateChallenge.lean:95-97](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L95-L97). Def. **Paper.** Equation (7.14), p.32, as used in (7.22), p.33.

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/Statement.lean:95-97](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Statement.lean#L95-L97).

Encoding for `Breakdown.stationaryEnergy` (1): The raw signed integrals are interpreted using the positive bounded measurable weight and the L² conditions supplied by the certificate and IsProfileField.

Clause 1 of `Breakdown.stationaryEnergy`, lines 95-97: This is |u|²_w, the spatial weighted energy used on the right-hand side of (7.22). Paper: Equation (7.14), p.32, as used in (7.22), p.33. Source: [lean/CertificateChallenge.lean:95-97](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L95-L97).

<a id="038"></a>

### 038. Approximate profile residual

`Breakdown.defectField`: This selects an explicit representative Fᵅ_a of the approximate equation’s residual, including its pressure gradient and the auxiliary actuator force. The reciprocal P occurs because the field is expressed in normalized time θ=s/P.

**Source.** [lean/CertificateChallenge.lean:99-102](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L99-L102). Def. **Paper.** Equations (7.1), p.30, and (7.10), p.31.

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/Statement.lean:99-102](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Statement.lean#L99-L102).

Encoding for `Breakdown.defectField` (1): The paper allows any residual representative modulo gradients; this earlier interface chooses one using a C¹ pressure.

Encoding for `Breakdown.defectField` (2): Division by zero is total in Lean, so period_pos is needed before reading 1/P as the intended time scaling.

Encoding for `Breakdown.defectField` (3): The approximate force need not vanish; its coefficients are cancelled after finding a parameter and nonlinear correction.

Clause 1 of `Breakdown.defectField`, lines 101-102: Assemble the rescaled self-similar residual with approximate force and pressure. Paper: Equations (7.1), p.30, and (7.10), p.31. Source: [lean/CertificateChallenge.lean:101-102](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L101-L102).

<a id="039"></a>

### 039. Weighted Sobolev constant

`Breakdown.supBoundFactor`: This is c_w=(4π√w_*)⁻¹ᐟ² in the paper’s bound from weighted energy to the spatial supremum norm. The expanded product inside the square root is algebraically the same constant.

**Source.** [lean/CertificateChallenge.lean:104-104](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L104). Def. **Paper.** Equation (7.15), p.32; Lemma 7.6, p.38.

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/Statement.lean:104-104](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Statement.lean#L104).

Encoding for `Breakdown.supBoundFactor` (1): Real.sqrt and division are total operations; the certificate’s weight_pos supplies w_*>0 and makes the intended constant positive.

Clause 1 of `Breakdown.supBoundFactor`, lines 104-104: This is c_w=(4π√w_*)⁻¹ᐟ² in the paper’s bound from weighted energy to the spatial supremum norm. Paper: Equation (7.15), p.32; Lemma 7.6, p.38. Source: [lean/CertificateChallenge.lean:104-104](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L104).

<a id="040"></a>

### 040. Data for the earlier certificate

`Breakdown.CertificateData`: This stores the approximate family, residual budgets, pinning data and constants for the earlier box-and-local-ball certificate. Several symbols agree with Section 7, while its local forcing norm and slope-inverse parameter test differ from the paper’s finite-row and adjoint formulation.

**Source.** [lean/CertificateChallenge.lean:106-137](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L106-L137). Structure. **Paper.** Related objects in §§7.2-7.3, pp.31-35; earlier certificate variant described in lean/README.md.

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/Statement.lean:106-137](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Statement.lean#L106-L137).

Encoding for `Breakdown.CertificateData` (1): The record contains data only; none of its signs, bounds or regularity claims holds until IsCertificate is supplied.

Encoding for `Breakdown.CertificateData` (2): The multiplier weight is fixed to one in this interface, and coercivity is assumed directly at the approximate profile.

Encoding for `Breakdown.CertificateData` (3): target is the total desired pin value; the perturbation target is target minus the pin of the approximate profile.

Encoding for `Breakdown.CertificateData` (4): The localized ball term is generally infinite-rank and is not literally the finite-row seminorm [F] of (7.17).

Encoding for `Breakdown.CertificateData` (5): The finite dimension k may be zero; radius_nonneg makes its parameter box nonempty even in degenerate dimensions.

Field `Breakdown.CertificateData.symmetries`: Γ is the prescribed set of orthogonal maps paired with normalized time shifts. Paper: Equation (7.5), p.30. Source: [lean/CertificateChallenge.lean:107-107](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L107).

Field `Breakdown.CertificateData.center`: The centre of the older rectangular parameter set is supplied explicitly. Paper: Related to K in §7.2, p.31, and (7.29), p.33; no identical centred-box field. Source: [lean/CertificateChallenge.lean:108-108](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L108).

Field `Breakdown.CertificateData.radius`: These are the coordinate half-widths of the older parameter box. Paper: Related to coordinate bounds in (7.29), p.33. Source: [lean/CertificateChallenge.lean:109-109](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L109).

Field `Breakdown.CertificateData.period`: P(p) is the similarity period S(α), as a function of the parameter. Paper: Period family in §7.2, p.31. Source: [lean/CertificateChallenge.lean:110-110](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L110).

Field `Breakdown.CertificateData.profile`: The parameterized field is the approximate profile Wᵅ_a in normalized time. Paper: Approximate family in §7.2 and (7.7)-(7.8), p.31. Source: [lean/CertificateChallenge.lean:111-111](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L111).

Field `Breakdown.CertificateData.pressure`: This chosen scalar pressure supplies the explicit residual’s gradient term. Paper: Residual modulo gradients in (7.10), p.31; explicit-pressure representation is additional. Source: [lean/CertificateChallenge.lean:112-112](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L112).

Field `Breakdown.CertificateData.multiplier`: The coefficient map supplies the approximate actuator force β_a(α). Paper: Equation (7.10), p.31. Source: [lean/CertificateChallenge.lean:113-113](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L113).

Field `Breakdown.CertificateData.target`: The total desired pin value becomes ℓ̄(α) after subtracting the approximate profile’s pin. Paper: Equations (7.11)-(7.12), p.31. Source: [lean/CertificateChallenge.lean:114-114](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L114).

Field `Breakdown.CertificateData.actuator`: The finite family bᵢ supplies the auxiliary forcing directions. Paper: Equation (7.9), p.31. Source: [lean/CertificateChallenge.lean:115-115](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L115).

Field `Breakdown.CertificateData.pin`: The matrix fields Ξᵢ define the linear pinning functionals on ∇v. Paper: Equation (7.11), p.31. Source: [lean/CertificateChallenge.lean:116-116](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L116).

Field `Breakdown.CertificateData.slope`: A square matrix approximates the variation of the force coefficients on the parameter box. Paper: Earlier alternative to the parameter map (7.30), p.34; no identical slope field. Source: [lean/CertificateChallenge.lean:117-117](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L117).

A proposed inverse matrix is supplied for the older zero-finding map. The complete certificate requires it to be a left inverse of the slope matrix. Paper: Earlier alternative to the parameter map (7.30), p.34; no identical inverse-slope field. Source: [lean/CertificateChallenge.lean:118-118](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L118).

Field `Breakdown.CertificateData.slopeOffset`: Coordinate error bounds enclose the force map around its affine slope model. Paper: Earlier alternative to enclosure conditions (7.34)-(7.37), p.34. Source: [lean/CertificateChallenge.lean:119-119](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L119).

Field `Breakdown.CertificateData.defectBound`: δ(p) bounds the full period L² norm of the residual. Paper: Equation (7.23), p.33. Source: [lean/CertificateChallenge.lean:120-120](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L120).

Field `Breakdown.CertificateData.defectBallBound`: This bounds the residual’s older local-ball norm before its coefficient is applied. Paper: Earlier alternative to δ₀ in (7.23), p.33. Source: [lean/CertificateChallenge.lean:121-121](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L121).

The real number w∗ is the proposed lower bound for the spatial energy weight; the certificate requires it to be positive. Paper: Equation (7.14), p.32. Source: [lean/CertificateChallenge.lean:122-122](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L122).

Field `Breakdown.CertificateData.weightFn`: w(y) is the spatial weight multiplying the squared gradient. Paper: Equation (7.14), p.32. Source: [lean/CertificateChallenge.lean:123-123](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L123).

Field `Breakdown.CertificateData.weightMax`: A real upper bound makes the spatial weight bounded. Paper: Bounded-weight assumption before (7.14), p.32. Source: [lean/CertificateChallenge.lean:124-124](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L124).

Field `Breakdown.CertificateData.coerciveL2`: c₁ is the coefficient of the full H norm in the coercive estimate. Paper: Equation (7.18), p.32. Source: [lean/CertificateChallenge.lean:125-125](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L125).

This coefficient multiplies the earlier local-ball forcing norm; the certificate requires it to be nonnegative. Paper: Earlier alternative to [F] in (7.17)-(7.18), p.32. Source: [lean/CertificateChallenge.lean:126-126](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L126).

Field `Breakdown.CertificateData.coercivePin`: c₂ multiplies the Euclidean size of the pin vector. Paper: Equation (7.18), p.32. Source: [lean/CertificateChallenge.lean:127-127](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L127).

Field `Breakdown.CertificateData.coerciveTotal`: c_L bounds the zero-pin inverse after combining full and localized forcing coefficients. Paper: Equation (7.21), p.33, with zero reference-transfer loss. Source: [lean/CertificateChallenge.lean:128-128](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L128).

Field `Breakdown.CertificateData.ballRadius`: The radius chooses the ball used in the earlier localized forcing estimate. Paper: Earlier alternative to (7.17), p.32; no identical radius parameter in the current certificate. Source: [lean/CertificateChallenge.lean:129-129](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L129).

Field `Breakdown.CertificateData.decay`: C_a bounds the approximate field and its first two spatial derivatives. Paper: Equation (7.8), p.31; second-derivative bound is an additional formal requirement. Source: [lean/CertificateChallenge.lean:130-130](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L130).

Field `Breakdown.CertificateData.periodMax`: S_max uniformly bounds all periods in the parameter set. Paper: Period family in §7.2, p.31. Source: [lean/CertificateChallenge.lean:131-131](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L131).

The natural number m is the proposed period divisor; the certificate restricts it to one or to two with the required half-period symmetry. Paper: Equation (7.6), p.30, and (7.26)-(7.27), p.33. Source: [lean/CertificateChallenge.lean:132-132](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L132).

Field `Breakdown.CertificateData.actuatorBound`: b_* bounds the combined H norms of the actuator fields. Paper: Equation (7.9), p.31. Source: [lean/CertificateChallenge.lean:133-133](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L133).

Field `Breakdown.CertificateData.formBound`: c₃ controls the negative part of the frozen quadratic form. Paper: Equation (7.22), p.33. Source: [lean/CertificateChallenge.lean:134-134](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L134).

Field `Breakdown.CertificateData.defectMax`: δ_max is a uniform upper bound for the full residual-norm budget. Paper: Equation (7.23), p.33. Source: [lean/CertificateChallenge.lean:135-135](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L135).

Field `Breakdown.CertificateData.sizeBound`: ε is half the admissible weighted correction radius. Paper: Equations (7.24)-(7.28), p.33. Source: [lean/CertificateChallenge.lean:136-136](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L136).

Field `Breakdown.CertificateData.supBound`: M bounds the spatial gradient norm uniformly in normalized time. Paper: Equations (7.25)-(7.27), p.33, and (7.38), p.35. Source: [lean/CertificateChallenge.lean:137-137](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L137).

<a id="041"></a>

### 041. Rectangular parameter set

`Breakdown.CertificateData.box`: The earlier certificate uses the coordinate interval between centre minus radius and centre plus radius. This replaces the paper’s mixed coordinate-box and ellipsoid geometry with a translated rectangle.

**Source.** [lean/CertificateChallenge.lean:139-140](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L139-L140). Def. **Paper.** Related to the parameter set (7.29), p.33; earlier rectangular alternative.

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/Statement.lean:139-140](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Statement.lean#L139-L140).

Encoding for `Breakdown.CertificateData.box` (1): Order on Fin k → R is pointwise, so Set.Icc means simultaneous coordinate bounds.

Encoding for `Breakdown.CertificateData.box` (2): radius_nonneg ensures that the centre belongs to the box; zero radii and k=0 remain allowed.

Clause 1 of `Breakdown.CertificateData.box`, lines 139-140: Specify the older parameter domain by coordinate lower and upper endpoints. Paper: Related to (7.29), p.33; no identical centred-box definition. Source: [lean/CertificateChallenge.lean:139-140](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L139-L140).

<a id="042"></a>

### 042. Conditions of the earlier certificate

`Breakdown.IsCertificate`: These are the full hypotheses for the older certificate-to-profile theorem, including analytic estimates for every admissible perturbation and finite arithmetic inequalities. They are an alternative to the final Section 7 certificate, with unit multiplier weight, direct approximate-profile coercivity, a local-ball forcing term and a slope-inverse box condition.

**Source.** [lean/CertificateChallenge.lean:142-215](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L142-L215). Structure. **Paper.** Related certificate conditions in §§7.2-7.3, pp.31-35; scalar comparisons (7.24)-(7.28), p.33.

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/Statement.lean:142-215](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Statement.lean#L142-L215).

Encoding for `Breakdown.IsCertificate` (1): The coercive estimate is universally quantified over perturbations, multiplier vectors and measurable finite-L² right sides; it cannot be checked by testing the approximate profile alone.

Encoding for `Breakdown.IsCertificate` (2): Joint C² regularity in parameter, time and space and a second-derivative decay bound are stronger written requirements than the family conditions on p.31.

Encoding for `Breakdown.IsCertificate` (3): The positive weight, positive periods, positive coerciveTotal and positive twist guard the divisions and square roots in the scalar bounds.

Encoding for `Breakdown.IsCertificate` (4): The strict nontriviality inequality forces the profile-gradient integral to have a positive finite toReal value: both zero and infinity give zero and fail.

Encoding for `Breakdown.IsCertificate` (5): No positivity is imposed on ballRadius; an inactive local term still leaves all global, coercive, nontriviality and parameter obligations.

Encoding for `Breakdown.IsCertificate` (6): A half-period symmetry permits twist=2; twist=1 is also allowed as a conservative choice even when that symmetry exists.

Encoding for `Breakdown.IsCertificate` (7): The pin coefficient is required nonnegative here, while the paper initially lists c₂ as real; comparing the full predicates requires more than matching that sign.

Field `Breakdown.IsCertificate.radius_nonneg`: Every coordinate radius is nonnegative, so the parameter box contains its centre. Paper: Parameter-domain sign convention in (7.29), p.33; older rectangular geometry. Source: [lean/CertificateChallenge.lean:143-143](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L143).

Field `Breakdown.IsCertificate.weight_pos`: The lower energy weight w_* is strictly positive. Paper: Weight assumption before (7.14), p.32. Source: [lean/CertificateChallenge.lean:144-144](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L144).

Field `Breakdown.IsCertificate.weightFn_measurable`: The spatial weight is measurable. Paper: Weight assumption before (7.14), p.32. Source: [lean/CertificateChallenge.lean:145-145](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L145).

Field `Breakdown.IsCertificate.weightFn_lower`: The spatial weight is everywhere at least w_*. Paper: Weight assumption before (7.14), p.32. Source: [lean/CertificateChallenge.lean:146-146](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L146).

Field `Breakdown.IsCertificate.weightFn_upper`: One finite real upper bound controls the spatial weight. Paper: Bounded-weight assumption before (7.14), p.32. Source: [lean/CertificateChallenge.lean:147-147](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L147).

Field `Breakdown.IsCertificate.weightFn_invariant`: The weight is unchanged under every spatial part of a prescribed symmetry. Paper: Γ-invariance in (7.5), p.30, and weighted norm (7.14), p.32; extra written weight-symmetry condition. Source: [lean/CertificateChallenge.lean:148-148](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L148).

Field `Breakdown.IsCertificate.coerciveL2_nonneg`: The coefficient c₁ of the full forcing norm is nonnegative. Paper: Sign assumption before (7.18), p.32. Source: [lean/CertificateChallenge.lean:149-149](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L149).

Field `Breakdown.IsCertificate.coerciveBall_nonneg`: The coefficient of the older local forcing norm is nonnegative. Paper: Earlier alternative to the seminorm bound in (7.17), p.32. Source: [lean/CertificateChallenge.lean:150-150](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L150).

Field `Breakdown.IsCertificate.coercivePin_nonneg`: The pin coefficient c₂ is nonnegative in this formal interface. Paper: Compare c₂∈R before (7.18), p.32; the formal predicate writes a sign condition. Source: [lean/CertificateChallenge.lean:151-151](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L151).

Field `Breakdown.IsCertificate.coerciveTotal_ge`: c_L dominates the sum of the full and local forcing coefficients. Paper: Equation (7.21), p.33, with zero reference-transfer loss and the older local coefficient. Source: [lean/CertificateChallenge.lean:152-152](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L152).

Field `Breakdown.IsCertificate.coerciveTotal_pos`: The inverse bound c_L is strictly positive. Paper: Sign assumption before (7.19), p.32. Source: [lean/CertificateChallenge.lean:153-153](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L153).

Field `Breakdown.IsCertificate.actuatorBound_nonneg`: The combined actuator bound b_* is nonnegative. Paper: Equation (7.9), p.31. Source: [lean/CertificateChallenge.lean:154-154](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L154).

Field `Breakdown.IsCertificate.formBound_nonneg`: The frozen-form loss c₃ is nonnegative. Paper: Assumption before (7.22), p.33. Source: [lean/CertificateChallenge.lean:155-155](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L155).

Field `Breakdown.IsCertificate.sizeBound_nonneg`: The correction-size parameter ε is nonnegative. Paper: Assumption before (7.23), p.33. Source: [lean/CertificateChallenge.lean:156-156](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L156).

Field `Breakdown.IsCertificate.supBound_pos`: The uniform gradient budget M is strictly positive. Paper: Assumption before (7.23), p.33. Source: [lean/CertificateChallenge.lean:157-157](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L157).

Field `Breakdown.IsCertificate.period_continuous`: The similarity period depends continuously on the parameter within the box. Paper: Period family in §7.2, p.31. Source: [lean/CertificateChallenge.lean:158-158](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L158).

Field `Breakdown.IsCertificate.period_pos`: Every parameter in the box has a strictly positive period. Paper: Period family in §7.2, p.31. Source: [lean/CertificateChallenge.lean:159-159](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L159).

Field `Breakdown.IsCertificate.period_le`: Every period is bounded above by S_max. Paper: Period family in §7.2, p.31. Source: [lean/CertificateChallenge.lean:160-160](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L160).

Field `Breakdown.IsCertificate.twist_pos`: The period-division factor m is positive. Paper: Equation (7.6), p.30; denominator in (7.26)-(7.27), p.33. Source: [lean/CertificateChallenge.lean:161-161](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L161).

Field `Breakdown.IsCertificate.twist_mem`: Use m=1, or use m=2 with an actual half-period symmetry witness. Paper: Equation (7.6), p.30; Lean permits the conservative choice m=1. Source: [lean/CertificateChallenge.lean:162-162](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L162).

Field `Breakdown.IsCertificate.multiplier_continuous`: The approximate force coefficient map β_a is continuous on the parameter box. Paper: Continuous multiplier family before (7.10), p.31. Source: [lean/CertificateChallenge.lean:163-163](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L163).

Field `Breakdown.IsCertificate.target_continuous`: The desired total pin value is continuous on the parameter box. Paper: Continuous perturbation target before (7.12), p.31; total-pin representation differs. Source: [lean/CertificateChallenge.lean:164-164](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L164).

Field `Breakdown.IsCertificate.profile_smooth`: The approximate family is jointly C² in parameter, normalized time and space. Paper: Family regularity in §7.2, p.31; this is a stronger written smoothness requirement. Source: [lean/CertificateChallenge.lean:165-165](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L165).

Field `Breakdown.IsCertificate.profile_periodic`: Every approximate field has period one in normalized time, including parameters outside the box. Paper: Periodicity of the approximate family, §7.2, p.31; global parameter extension is formal. Source: [lean/CertificateChallenge.lean:166-166](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L166).

Field `Breakdown.IsCertificate.profile_divergence`: For parameters in the box, the approximate velocity is pointwise divergence-free. Paper: Approximate family in §7.2, p.31. Source: [lean/CertificateChallenge.lean:167-167](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L167).

Field `Breakdown.IsCertificate.profile_decay`: On the box, the approximate field and its first two spatial derivatives satisfy uniform inverse-power decay. Paper: Equation (7.8), p.31; the second-derivative bound is extra. Source: [lean/CertificateChallenge.lean:168-169](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L168-L169).

Field `Breakdown.IsCertificate.profile_invariant`: Each approximate field on the box has every prescribed space-time symmetry. Paper: Equation (7.7), p.31. Source: [lean/CertificateChallenge.lean:170-171](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L170-L171).

Field `Breakdown.IsCertificate.pressure_smooth`: The chosen residual pressure is jointly C¹ in normalized time and space on each parameter slice. Paper: Explicit representative for (7.10), p.31; no separate smooth-pressure premise there. Source: [lean/CertificateChallenge.lean:172-172](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L172).

Field `Breakdown.IsCertificate.pressure_periodic`: The chosen residual pressure has period one in normalized time. Paper: Explicit representative for (7.10), p.31; no separate periodic-pressure premise there. Source: [lean/CertificateChallenge.lean:173-173](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L173).

Field `Breakdown.IsCertificate.actuator_measurable`: Each actuator is jointly measurable up to a null set. Paper: Forcing fields bᵢ∈H before (7.9), p.31. Source: [lean/CertificateChallenge.lean:174-174](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L174).

Field `Breakdown.IsCertificate.actuator_periodic`: Each actuator has period one in normalized time. Paper: H convention in §7.1, p.30; forcing fields before (7.9), p.31. Source: [lean/CertificateChallenge.lean:175-175](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L175).

Field `Breakdown.IsCertificate.actuator_invariant`: Each actuator is Γ-invariant almost everywhere in space-time. Paper: Forcing-field symmetry before (7.9), p.31. Source: [lean/CertificateChallenge.lean:176-177](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L176-L177).

Field `Breakdown.IsCertificate.actuator_norm`: The sum of the actuator squared H norms is at most b_*². Paper: Equation (7.9), p.31. Source: [lean/CertificateChallenge.lean:178-179](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L178-L179).

Field `Breakdown.IsCertificate.pin_measurable`: Each pin matrix field is jointly measurable up to a null set. Paper: Pin fields Ξᵢ∈H before (7.11), p.31. Source: [lean/CertificateChallenge.lean:180-180](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L180).

Field `Breakdown.IsCertificate.pin_finite`: Each pin matrix field has finite squared integral over one period. Paper: Pin fields Ξᵢ∈H before (7.11), p.31. Source: [lean/CertificateChallenge.lean:181-181](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L181).

Field `Breakdown.IsCertificate.coercive`: Every admissible linearized solution has weighted size bounded by full forcing, local-ball forcing and pin terms. Paper: Earlier analogue of (7.18), p.32, with ω=1, direct profile and a local-ball term. Source: [lean/CertificateChallenge.lean:182-189](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L182-L189).

Field `Breakdown.IsCertificate.frozen_form`: At every parameter and time, the stationary quadratic form is bounded below by minus c₃ times the weighted energy. Paper: Equation (7.22), p.33. Source: [lean/CertificateChallenge.lean:190-191](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L190-L191).

Field `Breakdown.IsCertificate.defect_nonneg`: The full and localized residual-norm budgets are nonnegative. Paper: Norm budgets in (7.23), p.33; localized budget belongs to the older variant. Source: [lean/CertificateChallenge.lean:192-192](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L192).

Field `Breakdown.IsCertificate.defect_l2`: The explicit residual has full squared period integral bounded by δ(p)². Paper: Equation (7.23), p.33. Source: [lean/CertificateChallenge.lean:193-195](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L193-L195).

Field `Breakdown.IsCertificate.defect_ball`: The residual’s squared integral on the chosen ball is bounded by the older localized budget squared. Paper: Earlier alternative to the seminorm residual bound in (7.23), p.33. Source: [lean/CertificateChallenge.lean:196-198](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L196-L198).

Field `Breakdown.IsCertificate.defect_le`: The parameter-dependent full residual bound is at most δ_max. Paper: Equation (7.23), p.33. Source: [lean/CertificateChallenge.lean:199-199](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L199).

Field `Breakdown.IsCertificate.size`: Full residual, localized residual and the discrepancy in the total pin target fit within ε. Paper: Equation (7.24), p.33, with zero transfer loss and the older local-ball residual term.; Equation (7.24), p.33. Source: [lean/CertificateChallenge.lean:200-202](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L200-L202).

Field `Breakdown.IsCertificate.small_first`: The weighted Sobolev factor and inverse bound give the strict smallness 2c_Lc_wM<1. Paper: Equation (7.25), p.33. Source: [lean/CertificateChallenge.lean:203-203](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L203).

Field `Breakdown.IsCertificate.small_second`: The second scalar inequality controls the uniform-gradient part of the older contraction metric. Paper: Equation (7.26), p.33, with ω=1. Source: [lean/CertificateChallenge.lean:204-206](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L204-L206).

Field `Breakdown.IsCertificate.small_third`: The third scalar inequality keeps the gradient budget M invariant under the nonlinear correction. Paper: Equation (7.27), p.33, with ω=1. Source: [lean/CertificateChallenge.lean:207-209](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L207-L209).

Field `Breakdown.IsCertificate.slope_inverse`: The supplied inverse multiplies the slope matrix to the identity. Paper: Earlier inverse-slope alternative to (7.30), p.34; no identical printed condition. Source: [lean/CertificateChallenge.lean:210-210](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L210).

Field `Breakdown.IsCertificate.slope_offset`: The approximate multiplier map stays within its coordinate error budget around the affine slope model. Paper: Earlier parameter enclosure alternative to (7.34)-(7.36), p.34. Source: [lean/CertificateChallenge.lean:211-212](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L211-L212).

Field `Breakdown.IsCertificate.inclusion`: The inverse-slope image of the correction and affine-error budgets lies inside every coordinate radius. Paper: Earlier map-to-self alternative to (7.35)-(7.37), p.34. Source: [lean/CertificateChallenge.lean:213-213](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L213).

Field `Breakdown.IsCertificate.nontrivial`: At every parameter, the approximate gradient energy is strictly larger than the greatest allowed cancellation energy. Paper: Equation (7.28), p.33, divided by the positive lower weight. Source: [lean/CertificateChallenge.lean:214-215](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L214-L215).

Clause 50 of `Breakdown.IsCertificate`, lines 182-186: The estimate ranges over every parameter, admissible perturbation, multiplier and finite-L² right side representing the linear equation. Paper: Universal premise of (7.18), p.32. Source: [lean/CertificateChallenge.lean:182-186](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L182-L186).

Clause 51 of `Breakdown.IsCertificate`, lines 187-189: The left side uses unit multiplier weight, and the right side includes the local-ball norm in place of a finite-row seminorm. Paper: Earlier analogue of (7.18), p.32. Source: [lean/CertificateChallenge.lean:187-189](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L187-L189).

<a id="043"></a>

### 043. An earlier certificate exists

`Breakdown.CertificateHypothesis`: This existentially packages a finite multiplier dimension, an older certificate data record and every clause of IsCertificate. It is the premise of certificate_orbit, with the dimension and data left to be supplied.

**Source.** [lean/CertificateChallenge.lean:217-217](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L217). Def. **Paper.** Related to the certificate hypothesis of Theorem 7.1, p.35; the older formal premise differs from §§7.2-7.3.

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/Statement.lean:217-217](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Statement.lean#L217).

Encoding for `Breakdown.CertificateHypothesis` (1): The existential does not restrict k to be positive; empty multiplier families remain possible and all remaining analytic conditions still apply.

Encoding for `Breakdown.CertificateHypothesis` (2): No concrete numerical certificate is constructed by this definition.

Clause 1 of `Breakdown.CertificateHypothesis`, lines 217-217: Require existence of data together with a proof of the entire older certificate predicate. Paper: Theorem 7.1, p.35; earlier formal certificate variant. Source: [lean/CertificateChallenge.lean:217-217](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L217).

<a id="044"></a>

### 044. Earlier certificate gives a profile

`Breakdown.certificate_orbit`: A witness of the earlier certificate predicate yields the explicit weak recurrent profile interface. The exported result hides the selected parameter, its period, the pin constraints and the quantitative closeness that the internal construction carries.

**Source.** [lean/CertificateChallenge.lean:219-220](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L219-L220). Readable theorem stub. **Paper.** Related to Theorem 7.1 and (7.38)-(7.39), p.35; weak regularization in Proposition 7.11, p.44.

**Library.** Implementation source: [lean/Solution.lean:39-40](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Solution.lean#L39-L40).

Encoding for `Breakdown.certificate_orbit` (1): This readable theorem is a proof stub; Solution.lean invokes certificate_orbit_proved in the library.

Encoding for `Breakdown.certificate_orbit` (2): The output does not state smoothness, identity isometry, the original Γ symmetries or a same-witness error bound.

Encoding for `Breakdown.certificate_orbit` (3): Its different certificate premise prevents a blanket comparison of the whole implication as simply weaker than Theorem 7.1.

Comparison for `Breakdown.certificate_orbit`: The input is the earlier box-and-local-ball certificate, whereas the paper uses a finite-row seminorm and a mixed box/ellipsoid with adjoint conditions. The exported output is coarser than Theorem 7.1, recording only weak-profile existence and hiding the selected witness and bounds.

Clause 1 of `Breakdown.certificate_orbit`, lines 219-219: The readable implication has an explicit hypothesis and endpoint; its proof is supplied separately in Solution.lean. Paper: Related to Theorem 7.1 and (7.38)-(7.39), p.35; weak regularization in Proposition 7.11, p.44. Source: [lean/CertificateChallenge.lean:219-219](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CertificateChallenge.lean#L219).

<a id="045"></a>

### 045. A priori perturbation estimate

`Breakdown.CoerciveClause`: This is the earlier certificate version of the estimate in (7.18): the perturbation energy and squared force coefficients are controlled by the right-hand side and the pins. It uses the approximate profile itself, unit weight on the force coefficients, and a ball-restricted L² term; the paper uses a reference profile, a separate multiplier weight and finitely many row pairings.

**Source.** [lean/CoerciveChallenge.lean:10-18](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L10-L18). Def. **Paper.** (7.17)-(7.18), p. 32; Lemma B.2 and (B.21)-(B.22), p. 56

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:10-18](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L10-L18).

Encoding for `Breakdown.CoerciveClause` (1): The quantifiers cover every parameter in the box, every admissible perturbation, every coefficient vector and every measurable periodic L² right-hand side satisfying the weak equation.

Encoding for `Breakdown.CoerciveClause` (2): This ball L² estimate is an earlier formulation, not a literal substitution of finitely many rows in (7.17).

Encoding for `Breakdown.CoerciveClause` (3): G and H are supplied weak spatial derivatives; g is the transport combination P⁻¹∂θv + v/2 + (y·∇)v/2, with the Laplacian supplied separately in IsRightSide.

Clause 1 of `Breakdown.CoerciveClause`, lines 11-15: Universal scope and the linearized equation modulo gradients. Paper: (7.18), p. 32; perturbation domain (7.4), p. 30 Source: [lean/CoerciveChallenge.lean:11-15](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L11-L15).

Clause 2 of `Breakdown.CoerciveClause`, lines 16-18: Energy estimate with unit force weight and a ball L² remainder. Paper: (7.14) and (7.18), p. 32 Source: [lean/CoerciveChallenge.lean:16-18](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L16-L18).

<a id="046"></a>

### 046. Extract the a priori estimate

`Breakdown.coerciveClause_of_isCertificate`: A certificate already contains the universally quantified a priori estimate. This theorem exposes that field for the multiplier argument leading back to (7.18).

**Source.** [lean/CoerciveChallenge.lean:20-22](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L20-L22). Theorem with a source proof body. **Paper.** (7.17)-(7.18), p. 32; Lemma B.2 and (B.21)-(B.22), p. 56

**Library.** Implementation source: [lean/Breakdown/Cert/CoerciveStatement.lean:20-22](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L20-L22).

Comparison for `Breakdown.coerciveClause_of_isCertificate`: This is a projection from the earlier certificate structure, with no separate theorem in the paper. Its target has the ball L² and unit-force-weight conventions of CoerciveClause.

Clause 1 of `Breakdown.coerciveClause_of_isCertificate`, lines 20-22: A certificate already contains the universally quantified a priori estimate. Paper: (7.17)-(7.18), p. 32; Lemma B.2 and (B.21)-(B.22), p. 56 Source: [lean/CoerciveChallenge.lean:20-22](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L20-L22).

<a id="047"></a>

### 047. Inner product over one period

`Breakdown.periodPairing`: This is the real H-pairing from §7.1, integrating first in space and then over the normalized time period. The definition accepts arbitrary fields; its Hilbert-space interpretation uses the measurability and finite L² assumptions of its callers.

**Source.** [lean/CoerciveChallenge.lean:24-25](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L24-L25). Def. **Paper.** §7.1, definition of the H inner product, p. 30; (B.14), p. 54

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:24-25](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L24-L25).

Encoding for `Breakdown.periodPairing` (1): Mathlib real Bochner integrals are total and equal zero on nonintegrable inputs. periodPairing_abs_le establishes integrability under its explicit L² hypotheses.

Encoding for `Breakdown.periodPairing` (2): The closed interval [0,1] differs from the paper’s open interval only on null endpoints for Lebesgue integration.

Clause 1 of `Breakdown.periodPairing`, lines 24-25: This is the real H-pairing from §7.1, integrating first in space and then over the normalized time period. Paper: §7.1, definition of the H inner product, p. 30; (B.14), p. 54 Source: [lean/CoerciveChallenge.lean:24-25](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L24-L25).

<a id="048"></a>

### 048. Multiplier estimate before division

`Breakdown.MultiplierInequality`: This packages the two estimates that Lemma B.2 combines: a bound on the multiplier and a coercive pairing bound. Lean keeps c, cμ, t, a and K abstract; the printed argument uses c = 3/50, t = 1000 and its row seminorm.

**Source.** [lean/CoerciveChallenge.lean:27-44](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L27-L44). Structure. **Paper.** Lemma B.2 and (B.21)-(B.22), p. 56

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:27-44](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L27-L44).

Encoding for `Breakdown.MultiplierInequality` (1): The existential multiplier and frequency norm occur after the perturbation, coefficients and right-hand side; one universal multiplier for all inputs is not required.

Encoding for `Breakdown.MultiplierInequality` (2): The K term measures F on a ball and the force coefficient weight is one; these differ from the extended certificate used in the printed paper.

Field `Breakdown.MultiplierInequality.c_pos`: The energy coefficient c is strictly positive, so the final division by √c is valid. Paper: Lemma B.2 and (B.21)-(B.22), p. 56 Source: [lean/CoerciveChallenge.lean:28-28](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L28).

Field `Breakdown.MultiplierInequality.cμ_nonneg`: The retained frequency energy has a nonnegative coefficient cμ. Paper: Proposition B.1 and (B.20), p. 55 Source: [lean/CoerciveChallenge.lean:29-29](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L29).

Field `Breakdown.MultiplierInequality.t_nonneg`: The coefficient of the squared pin norm is nonnegative. Paper: Lemma B.2 and (B.21)-(B.22), p. 56 Source: [lean/CoerciveChallenge.lean:30-30](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L30).

Field `Breakdown.MultiplierInequality.a_nonneg`: The multiplier norm bound uses a nonnegative constant a. Paper: Proposition B.1 and (B.20), p. 55 Source: [lean/CoerciveChallenge.lean:31-31](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L31).

Field `Breakdown.MultiplierInequality.K_nonneg`: The ball L² term uses a nonnegative constant K. Paper: (7.17)-(7.18), p. 32; Lemma B.2 and (B.21)-(B.22), p. 56 Source: [lean/CoerciveChallenge.lean:32-32](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L32).

Field `Breakdown.MultiplierInequality.bound`: For each admissible input, choose an L² multiplier and a nonnegative frequency norm satisfying both bounds. Paper: Proposition B.1, p. 55, and the combined inequality in the proof of Lemma B.2, p. 56 Source: [lean/CoerciveChallenge.lean:33-44](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L33-L44).

<a id="049"></a>

### 049. Cauchy-Schwarz over one period

`Breakdown.periodPairing_abs_le`: This supplies the Cauchy-Schwarz step in Lemma B.2. The proof first places the two fields and their pairing on the product measure and verifies integrability, which gives the real integrals and converted L² norms their intended values.

**Source.** [lean/CoerciveChallenge.lean:46-113](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L46-L113). Theorem with a source proof body. **Paper.** Lemma B.2 and (B.21)-(B.22), p. 56

**Library.** Implementation source: [lean/Breakdown/Cert/CoerciveStatement.lean:46-113](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L46-L113).

Encoding for `Breakdown.periodPairing_abs_le` (1): Both finite ENNReal square integrals and both almost-everywhere measurability assumptions are needed for this interpretation.

Encoding for `Breakdown.periodPairing_abs_le` (2): The source proof establishes integrability before applying the product-integral and L² inequalities.

Comparison for `Breakdown.periodPairing_abs_le`: The estimate used for the H-pairing in Lemma B.2 is proved on the period window for arbitrary measurable finite-L² fields. Periodicity, which is part of the paper’s space H, is not required for this estimate.

Clause 1 of `Breakdown.periodPairing_abs_le`, lines 46-51: L² hypotheses and the Cauchy-Schwarz conclusion. Paper: Lemma B.2 and (B.21)-(B.22), p. 56 Source: [lean/CoerciveChallenge.lean:46-51](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L46-L51).

<a id="050"></a>

### 050. Solve the quadratic bound

`Breakdown.le_add_of_sq_le`: This isolates the scalar step P² ≤ aP + Q² ⇒ P ≤ a + Q in the proof of Lemma B.2. All three scalar quantities are required to be nonnegative.

**Source.** [lean/CoerciveChallenge.lean:115-119](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L115-L119). Theorem with a source proof body. **Paper.** Lemma B.2 and (B.21)-(B.22), p. 56

**Library.** Implementation source: [lean/Breakdown/Cert/CoerciveStatement.lean:115-119](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L115-L119).

Comparison for `Breakdown.le_add_of_sq_le`: This is precisely the scalar implication used in Lemma B.2, with x and b standing for P and Q.

Clause 1 of `Breakdown.le_add_of_sq_le`, lines 115-116: Nonnegative scalar variables and the quadratic-to-linear implication. Paper: Lemma B.2 and (B.21)-(B.22), p. 56 Source: [lean/CoerciveChallenge.lean:115-116](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L115-L116).

<a id="051"></a>

### 051. Convert the multiplier estimate

`Breakdown.coercive_scalar_core`: This carries out the scalar algebra of Lemma B.2 with c > 0 and the stated sign conditions. It returns coefficients a/√c, K and √(t/c) for the global forcing, ball forcing and pin norms.

**Source.** [lean/CoerciveChallenge.lean:121-170](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L121-L170). Theorem with a source proof body. **Paper.** Lemma B.2 and (B.21)-(B.22), p. 56

**Library.** Implementation source: [lean/Breakdown/Cert/CoerciveStatement.lean:121-170](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L121-L170).

Encoding for `Breakdown.coercive_scalar_core` (1): The hypothesis c > 0 rules out totalized division by zero and makes √c positive.

Encoding for `Breakdown.coercive_scalar_core` (2): E and S encode the field energy and squared coefficient norm, while the retained frequency term has nonnegative coefficient cμ.

Comparison for `Breakdown.coercive_scalar_core`: This generalizes the algebraic step of Lemma B.2 from the printed constants to arbitrary constants satisfying the stated sign conditions. It is a scalar lemma, so the paper’s row seminorm and force weighting are not fixed by its statement.

Clause 1 of `Breakdown.coercive_scalar_core`, lines 121-125: Abstract norm and pairing bounds yield the divided estimate. Paper: Lemma B.2 and (B.21)-(B.22), p. 56 Source: [lean/CoerciveChallenge.lean:121-125](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L121-L125).

<a id="052"></a>

### 052. Obtain the a priori estimate

`Breakdown.coerciveClause_of_multiplierInequality`: The multiplier bound gives the earlier certificate estimate once its three output constants fit inside the declared certificate constants. This is the scalar assembly corresponding to Lemma B.2, retaining the older ball L² term.

**Source.** [lean/CoerciveChallenge.lean:172-189](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L172-L189). Theorem with a source proof body. **Paper.** Lemma B.2 and (B.21)-(B.22), p. 56

**Library.** Implementation source: [lean/Breakdown/Cert/CoerciveStatement.lean:172-189](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L172-L189).

Encoding for `Breakdown.coerciveClause_of_multiplierInequality` (1): The comparison hypotheses may enlarge the resulting constants because all norms multiplying them are nonnegative.

Encoding for `Breakdown.coerciveClause_of_multiplierInequality` (2): Integrability of the pairing is supplied by periodPairing_abs_le, rather than assumed from the bare definition.

Comparison for `Breakdown.coerciveClause_of_multiplierInequality`: The proof implements the conversion in Lemma B.2, but its target is the earlier ball L² certificate and its force weight is one. The paper’s finite-row and weighted-force estimate is handled in ExtendedCoerciveChallenge.

Clause 1 of `Breakdown.coerciveClause_of_multiplierInequality`, lines 172-175: Compare the divided multiplier constants with the certificate constants. Paper: (B.22) and Lemma B.2, p. 56 Source: [lean/CoerciveChallenge.lean:172-175](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L172-L175).

<a id="053"></a>

### 053. Rotation about the vertical axis

`Breakdown.axialRot`: This is the rotation Rφ about the third coordinate axis used in the mode average (B.12). Lean writes it in the Cartesian basis, so no cylindrical-coordinate choice is needed on the axis.

**Source.** [lean/CoerciveChallenge.lean:191-193](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L191-L193). Def. **Paper.** (B.12)-(B.13), p. 53, with harmonic convention (B.2), p. 50

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:191-193](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L191-L193).

Encoding for `Breakdown.axialRot` (1): Fin 3 uses coordinates 0, 1 and 2; the paper’s y₃ axis is coordinate 2.

Clause 1 of `Breakdown.axialRot`, lines 191-193: This is the rotation Rφ about the third coordinate axis used in the mode average (B.12). Paper: (B.12)-(B.13), p. 53, with harmonic convention (B.2), p. 50 Source: [lean/CoerciveChallenge.lean:191-193](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L191-L193).

<a id="054"></a>

### 054. Alternating symbol for curl

`Breakdown.alternatingSymbol`: This gives the three-dimensional alternating symbol used to form the curls in (B.14) and (B.18). It uses zero-based coordinate indices and is zero when two indices coincide.

**Source.** [lean/CoerciveChallenge.lean:195-196](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L195-L196). Def. **Paper.** Encoding helper for curls in (B.14), p. 54, and (B.18), p. 55; no separately numbered definition

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:195-196](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L195-L196).

Clause 1 of `Breakdown.alternatingSymbol`, lines 195-196: This gives the three-dimensional alternating symbol used to form the curls in (B.14) and (B.18). Paper: Encoding helper for curls in (B.14), p. 54, and (B.18), p. 55; no separately numbered definition Source: [lean/CoerciveChallenge.lean:195-196](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L195-L196).

<a id="055"></a>

### 055. Time and angle Fourier coefficient

`Breakdown.modeAverage`: This extracts a joint time-angle Fourier coefficient with normalization 1/(2π) and the conjugate exponential used in (B.12). Its index is the direct frequency pair (n,k), whereas the paper labels the same frequency as n = 2ι₂ − ι₁ and k = κι₁.

**Source.** [lean/CoerciveChallenge.lean:198-200](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L198-L200). Def. **Paper.** (B.12)-(B.13), p. 53, with harmonic convention (B.2), p. 50

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:198-200](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L198-L200).

Encoding for `Breakdown.modeAverage` (1): The real time interval has length one; the angle interval has length 2π.

Encoding for `Breakdown.modeAverage` (2): The complex interval integrals are total Bochner integrals; analytic callers establish the needed integrability.

Clause 1 of `Breakdown.modeAverage`, lines 198-200: This extracts a joint time-angle Fourier coefficient with normalization 1/(2π) and the conjugate exponential used in (B.12). Paper: (B.12)-(B.13), p. 53, with harmonic convention (B.2), p. 50 Source: [lean/CoerciveChallenge.lean:198-200](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L198-L200).

<a id="056"></a>

### 056. Velocity mode in the rotating frame

`Breakdown.modeVel`: This is the mode of v in (B.12), evaluated by rotating the point forward and the vector back before Fourier averaging. The generic index runs over all direct frequency pairs; the symmetry-adapted paper index enters through the harmonic embedding.

**Source.** [lean/CoerciveChallenge.lean:202-203](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L202-L203). Def. **Paper.** (B.12)-(B.13), p. 53, with harmonic convention (B.2), p. 50

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:202-203](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L202-L203).

Encoding for `Breakdown.modeVel` (1): Use (n,k) = (2ι₂−ι₁, κι₁) when comparing this generic mode with the paper’s Eι.

Encoding for `Breakdown.modeVel` (2): The components are complex Fourier coefficients even though v is a real vector field.

Clause 1 of `Breakdown.modeVel`, lines 202-203: This is the mode of v in (B.12), evaluated by rotating the point forward and the vector back before Fourier averaging. Paper: (B.12)-(B.13), p. 53, with harmonic convention (B.2), p. 50 Source: [lean/CoerciveChallenge.lean:202-203](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L202-L203).

<a id="057"></a>

### 057. Gradient mode in the rotating frame

`Breakdown.modeGrad`: This extends (B.12) to the gradient tensor by rotating its input and output indices. The output array stores the vector component first and the differentiation direction second, opposite to the derivative-first matrix convention stated near (7.11).

**Source.** [lean/CoerciveChallenge.lean:205-208](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L205-L208). Def. **Paper.** (B.12)-(B.13), p. 53; gradient modes in (B.16), p. 54; matrix convention near (7.11), p. 31

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:205-208](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L205-L208).

Encoding for `Breakdown.modeGrad` (1): The second index is the direction supplied to the continuous linear map G; the first is the resulting vector component.

Encoding for `Breakdown.modeGrad` (2): A pointwise arbitrary G need not be the gradient of v; IsPerturbation supplies the weak-gradient identity.

Clause 1 of `Breakdown.modeGrad`, lines 205-208: This extends (B.12) to the gradient tensor by rotating its input and output indices. Paper: (B.12)-(B.13), p. 53; gradient modes in (B.16), p. 54; matrix convention near (7.11), p. 31 Source: [lean/CoerciveChallenge.lean:205-208](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L205-L208).

<a id="058"></a>

### 058. Second derivative mode

`Breakdown.modeSecondDeriv`: This applies the rotating Fourier average to the second spatial derivative tensor appearing in (B.16). Its three indices are the output component and the two differentiation directions.

**Source.** [lean/CoerciveChallenge.lean:210-214](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L210-L214). Def. **Paper.** (B.16) and the unexpanded coefficient formulas described below it, p. 54

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:210-214](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L210-L214).

Encoding for `Breakdown.modeSecondDeriv` (1): The tensor is supplied as H, with weak-derivative compatibility imposed by IsPerturbation.

Encoding for `Breakdown.modeSecondDeriv` (2): The component norm used later is a finite sum of squared complex components, not the operator norm of H.

Clause 1 of `Breakdown.modeSecondDeriv`, lines 210-214: This applies the rotating Fourier average to the second spatial derivative tensor appearing in (B.16). Paper: (B.16) and the unexpanded coefficient formulas described below it, p. 54 Source: [lean/CoerciveChallenge.lean:210-214](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L210-L214).

<a id="059"></a>

### 059. Squared component norm

`Breakdown.cnormSq`: This sums the squared moduli of a finite complex array. It gives the Euclidean and Frobenius squared norms of the velocity, gradient and second derivative modes in (B.16).

**Source.** [lean/CoerciveChallenge.lean:216-216](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L216). Def. **Paper.** Norm encoding for (B.16), p. 54; no separately numbered definition

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:216-216](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L216).

Encoding for `Breakdown.cnormSq` (1): For a matrix or tensor this is the componentwise Frobenius norm; the conversion-weight Hessians use a different operator norm.

Encoding for `Breakdown.cnormSq` (2): The sum over an empty index type is zero; the active velocity and derivative arrays use nonempty Fin 3 products.

Clause 1 of `Breakdown.cnormSq`, lines 216-216: This sums the squared moduli of a finite complex array. Paper: Norm encoding for (B.16), p. 54; no separately numbered definition Source: [lean/CoerciveChallenge.lean:216-216](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L216).

<a id="060"></a>

### 060. Curl of a gradient mode

`Breakdown.curlOfGrad`: This contracts the Fourier gradient array with the alternating symbol to form the curl mode in (B.14) and (B.16). The component-first array convention explains the reversed pair of indices in the contraction.

**Source.** [lean/CoerciveChallenge.lean:218-219](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L218-L219). Def. **Paper.** (B.14) and (B.16), p. 54

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:218-219](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L218-L219).

Encoding for `Breakdown.curlOfGrad` (1): The array entry g(l,j) represents ∂j v_l; transposing the array without changing this contraction reverses its interpretation.

Clause 1 of `Breakdown.curlOfGrad`, lines 218-219: This contracts the Fourier gradient array with the alternating symbol to form the curl mode in (B.14) and (B.16). Paper: (B.14) and (B.16), p. 54 Source: [lean/CoerciveChallenge.lean:218-219](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L218-L219).

<a id="061"></a>

### 061. Gradient of a curl mode

`Breakdown.curlGradOfSecondDeriv`: This contracts the second derivative mode to obtain the derivative of the curl used in (B.16). Its output pair records the curl component and its differentiation direction.

**Source.** [lean/CoerciveChallenge.lean:221-222](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L221-L222). Def. **Paper.** (B.16) and the unexpanded coefficient formulas described below it, p. 54

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:221-222](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L221-L222).

Encoding for `Breakdown.curlGradOfSecondDeriv` (1): Weak derivative compatibility and symmetry of second derivatives are analytic facts supplied by the perturbation hypotheses, not by this algebraic contraction.

Clause 1 of `Breakdown.curlGradOfSecondDeriv`, lines 221-222: This contracts the second derivative mode to obtain the derivative of the curl used in (B.16). Paper: (B.16) and the unexpanded coefficient formulas described below it, p. 54 Source: [lean/CoerciveChallenge.lean:221-222](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L221-L222).

<a id="062"></a>

### 062. Distance from the rotation axis

`Breakdown.cylRadius`: This is r, the distance to the y₃ axis in Appendix B.3. It appears in the inverse-square angular-frequency gains of (B.35).

**Source.** [lean/CoerciveChallenge.lean:224-224](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L224). Def. **Paper.** Meridian coordinates in Appendix B.1, p. 50; (B.35), p. 60

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:224-224](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L224).

Encoding for `Breakdown.cylRadius` (1): The square-root argument is a sum of squares, so it is nonnegative.

Encoding for `Breakdown.cylRadius` (2): r is zero on the axis; the gain theorem is an almost-everywhere statement and the axis is a null set.

Clause 1 of `Breakdown.cylRadius`, lines 224-224: This is r, the distance to the y₃ axis in Appendix B.3. Paper: Meridian coordinates in Appendix B.1, p. 50; (B.35), p. 60 Source: [lean/CoerciveChallenge.lean:224-224](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L224).

<a id="063"></a>

### 063. Invariance under axial rotations

`Breakdown.IsAxisymmetric`: This states that a scalar coefficient is unchanged by every rotation about the y₃ axis. It expresses the rotational invariance required of the weights and auxiliary functions in Appendix B.2.

**Source.** [lean/CoerciveChallenge.lean:226-226](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L226). Def. **Paper.** Appendix B.2, weights paragraph, p. 53; mode coefficients (B.16), p. 54

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:226-226](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L226).

Encoding for `Breakdown.IsAxisymmetric` (1): The invariance is pointwise for every angle and point, rather than merely almost everywhere.

Clause 1 of `Breakdown.IsAxisymmetric`, lines 226-226: This states that a scalar coefficient is unchanged by every rotation about the y₃ axis. Paper: Appendix B.2, weights paragraph, p. 53; mode coefficients (B.16), p. 54 Source: [lean/CoerciveChallenge.lean:226-226](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L226).

<a id="064"></a>

### 064. Frequency in a rotating frame

`Breakdown.shiftedFrequency`: This is the frequency 2πn/P + kν(y), corresponding to Ωp in (B.15) after the paper’s harmonic reindexing. The earlier class-weight route permits a spatially varying rate; the printed piecewise multiplier uses a scalar rate for each piece and parameter.

**Source.** [lean/CoerciveChallenge.lean:228-229](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L228-L229). Def. **Paper.** (B.15) and the frequency seminorm immediately below it, p. 54

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:228-229](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L228-L229).

Encoding for `Breakdown.shiftedFrequency` (1): Division is total in Lean; the relevant admissibility predicate separately requires P > 0.

Encoding for `Breakdown.shiftedFrequency` (2): The paper’s κ is a spatial harmonic scale, while the generic second frequency coordinate here is already k = κι₁.

Clause 1 of `Breakdown.shiftedFrequency`, lines 228-229: This is the frequency 2πn/P + kν(y), corresponding to Ωp in (B.15) after the paper’s harmonic reindexing. Paper: (B.15) and the frequency seminorm immediately below it, p. 54 Source: [lean/CoerciveChallenge.lean:228-229](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L228-L229).

<a id="065"></a>

### 065. Mean time-angle mode

`Breakdown.meanField`: This reconstructs the real vector field in the zero time-angle mode. The earlier multiplier estimates separate this mean from the nonzero waves when bounding the coefficients related to (B.16).

**Source.** [lean/CoerciveChallenge.lean:231-232](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L231-L232). Def. **Paper.** Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:231-232](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L231-L232).

Encoding for `Breakdown.meanField` (1): Taking real parts returns a real vector field; mean-mode invariance is proved elsewhere.

Encoding for `Breakdown.meanField` (2): Evaluation at time zero is part of the mode reconstruction and does not restrict the original profile to its initial value.

Clause 1 of `Breakdown.meanField`, lines 231-232: This reconstructs the real vector field in the zero time-angle mode. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:231-232](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L231-L232).

<a id="066"></a>

### 066. Transport in a rotating frame

`Breakdown.relativeVelocity`: This is the mean field plus the similarity drift y/2, measured relative to a rotating frame. It supplies the earlier route’s mean transport bound corresponding to the full reference-profile transport bound described before (B.14).

**Source.** [lean/CoerciveChallenge.lean:234-235](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L234-L235). Def. **Paper.** Related to the transport bound in Appendix B.2, p. 53; earlier mean/wave split has no exact printed counterpart

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:234-235](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L234-L235).

Clause 1 of `Breakdown.relativeVelocity`, lines 234-235: This is the mean field plus the similarity drift y/2, measured relative to a rotating frame. Paper: Related to the transport bound in Appendix B.2, p. 53; earlier mean/wave split has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:234-235](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L234-L235).

<a id="067"></a>

### 067. Curl from a spatial derivative

`Breakdown.curlVec`: This turns a real derivative map into the curl vector used in (B.18). The derivative direction is the argument of G and the vector component is selected afterwards.

**Source.** [lean/CoerciveChallenge.lean:237-238](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L237-L238). Def. **Paper.** (B.18) and the positive/negative integral convention, p. 55

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:237-238](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L237-L238).

Encoding for `Breakdown.curlVec` (1): The expression is algebraic for any G; calling it the curl of a field requires G to be that field’s derivative.

Clause 1 of `Breakdown.curlVec`, lines 237-238: This turns a real derivative map into the curl vector used in (B.18). Paper: (B.18) and the positive/negative integral convention, p. 55 Source: [lean/CoerciveChallenge.lean:237-238](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L237-L238).

<a id="068"></a>

### 068. Derivative of vorticity

`Breakdown.vortGrad`: This contracts a second derivative tensor to obtain one component of ∇curl W in (B.18). The first explicit index selects the curl component and the second selects the differentiation direction.

**Source.** [lean/CoerciveChallenge.lean:240-241](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L240-L241). Def. **Paper.** (B.18) and the positive/negative integral convention, p. 55

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:240-241](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L240-L241).

Encoding for `Breakdown.vortGrad` (1): DDW is an iterated continuous-linear-map representation of the Hessian; the tensor contraction assumes its derivative meaning at analytic call sites.

Clause 1 of `Breakdown.vortGrad`, lines 240-241: This contracts a second derivative tensor to obtain one component of ∇curl W in (B.18). Paper: (B.18) and the positive/negative integral convention, p. 55 Source: [lean/CoerciveChallenge.lean:240-241](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L240-L241).

<a id="069"></a>

### 069. Stretching term in the energy identity

`Breakdown.stretchForm`: This is J from (B.18): the vorticity stretching term and the two terms involving derivatives of curl W. Lean expands the symmetric-gradient and cross-product contractions in Cartesian components.

**Source.** [lean/CoerciveChallenge.lean:243-251](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L243-L251). Def. **Paper.** (B.18) and the positive/negative integral convention, p. 55

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:243-251](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L243-L251).

Encoding for `Breakdown.stretchForm` (1): fderiv is total and returns a default derivative at points of nondifferentiability; the strong multiplier theorems require W to be C².

Encoding for `Breakdown.stretchForm` (2): The weak certificate route replaces the second derivative calls by a separately supplied weak Hessian in ExtendedCoerciveChallenge.

Clause 1 of `Breakdown.stretchForm`, lines 245-246: Negative symmetric-gradient quadratic form in curl v. Paper: (B.18), p. 55 Source: [lean/CoerciveChallenge.lean:245-246](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L245-L246).

Clause 2 of `Breakdown.stretchForm`, lines 247-248: Pair (v·∇)curl W with curl v. Paper: (B.18), p. 55 Source: [lean/CoerciveChallenge.lean:247-248](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L247-L248).

Clause 3 of `Breakdown.stretchForm`, lines 249-251: The half-weighted cross-product term written in components. Paper: (B.18), p. 55 Source: [lean/CoerciveChallenge.lean:249-251](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L249-L251).

<a id="070"></a>

### 070. Bounds for the mean and the waves

`Breakdown.FlowBounds`: These are numerical majorants for the earlier mean/wave decomposition of the reference profile. Their role corresponds to the profile bounds preceding (B.16), although the printed piecewise route packages those bounds differently.

**Source.** [lean/CoerciveChallenge.lean:253-264](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L253-L264). Structure. **Paper.** Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:253-264](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L253-L264).

Encoding for `Breakdown.FlowBounds` (1): The structure stores real numbers and functions without asserting they are valid bounds; FlowBounds.IsValid supplies those inequalities.

Field `Breakdown.FlowBounds.perpSpeed`: Bound for the mean similarity drift in the rotating frame of each class. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:254-254](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L254).

Field `Breakdown.FlowBounds.meanVort`: Bound for the vorticity of the zero Fourier mode. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:255-255](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L255).

Field `Breakdown.FlowBounds.meanVortGrad`: Bound for the spatial derivative of the mean vorticity. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:256-256](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L256).

Field `Breakdown.FlowBounds.meanStretch`: Upper quadratic-form bound for the symmetric derivative of the mean field. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:257-257](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L257).

Field `Breakdown.FlowBounds.meanGrad`: Operator-norm bound for the derivative of the mean field. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:258-258](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L258).

Field `Breakdown.FlowBounds.wave0`: Bound for the sum of the amplitudes of the nonzero velocity modes. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:259-259](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L259).

Field `Breakdown.FlowBounds.wave1`: Bound for the sum of the gradient-mode amplitudes of the nonzero waves. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:260-260](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L260).

Field `Breakdown.FlowBounds.waveVort`: Bound for the sum of the vorticity-mode amplitudes of the nonzero waves. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:261-261](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L261).

Field `Breakdown.FlowBounds.wave2`: Bound for the sum of the gradient-of-vorticity amplitudes of the nonzero waves. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:262-262](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L262).

Field `Breakdown.FlowBounds.waveStretch`: Absolute quadratic-form bound for the derivative of the oscillatory field. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:263-263](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L263).

Field `Breakdown.FlowBounds.waveVortGrad`: Bound for the derivative of the oscillatory vorticity. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:264-264](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L264).

<a id="071"></a>

### 071. Weights assigned to mode classes

`Breakdown.ModeWeights`: This is the earlier class-based multiplier data, related to the weights in Appendix B.2. It assigns signed curl and velocity weights directly to frequency classes, while the printed construction uses finite families of pieces with one-sided mode sets.

**Source.** [lean/CoerciveChallenge.lean:266-282](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L266-L282). Structure. **Paper.** Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:266-282](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L266-L282).

Encoding for `Breakdown.ModeWeights` (1): The raw structure imposes no finiteness, symmetry, sign, decay or denominator condition; ModeWeights.IsAdmissible supplies them.

Encoding for `Breakdown.ModeWeights` (2): The presence of classOf gives C an inhabitant even though Finite C alone would permit an empty type.

Field `Breakdown.ModeWeights.classOf`: Assign each direct time-angle frequency pair to a weight class. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:267-267](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L267).

This finite harmonic set is proposed for the oscillatory reference profile; admissibility excludes the zero harmonic. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:268-268](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L268).

Field `Breakdown.ModeWeights.rate`: Rotation rate for each class, allowed here to depend on position. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:269-269](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L269).

Field `Breakdown.ModeWeights.epsW`: Signed curl multiplier weight for each class. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:270-270](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L270).

Field `Breakdown.ModeWeights.muW`: Signed velocity multiplier weight for each class. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:271-271](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L271).

Field `Breakdown.ModeWeights.convD`: The conversion weight D that moves curl-gradient energy to Hessian energy. Paper: Appendix B.2, p. 53, and the conversion terms of (B.16), p. 54 Source: [lean/CoerciveChallenge.lean:272-272](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L272).

Field `Breakdown.ModeWeights.convZ`: The conversion weight Z that moves curl energy to gradient energy. Paper: Appendix B.2, p. 53, and the conversion terms of (B.16), p. 54 Source: [lean/CoerciveChallenge.lean:273-273](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L273).

Field `Breakdown.ModeWeights.share1`: Classwise share used to absorb transport and gradient-of-weight errors. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:274-274](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L274).

Field `Breakdown.ModeWeights.share2`: Share used to absorb couplings to velocity waves. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:275-275](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L275).

Field `Breakdown.ModeWeights.share4`: Share used to absorb the velocity multiplier’s wave couplings. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:276-276](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L276).

This is the balancing-length function for the oscillatory stretching estimate; admissibility requires it to be positive. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:277-277](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L277).

This is the balancing-length function for gradient-of-vorticity wave errors; admissibility requires it to be positive. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:278-278](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L278).

This is the classwise Young parameter for the velocity multiplier; admissibility requires a positive common lower bound. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:279-279](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L279).

This is the proposed common lower bound for the classwise Young parameters; admissibility requires it to be positive. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:280-280](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L280).

Field `Breakdown.ModeWeights.c`: Coefficient reserved for the weighted perturbation energy. Paper: Proposition B.1 and (B.20), p. 55 Source: [lean/CoerciveChallenge.lean:281-281](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L281).

Field `Breakdown.ModeWeights.cμ`: Coefficient reserved for the frequency seminorm. Paper: Proposition B.1 and (B.20), p. 55 Source: [lean/CoerciveChallenge.lean:282-282](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L282).

<a id="072"></a>

### 072. Magnitude of the curl weight

`Breakdown.ModeWeights.eps`: This is the absolute value of the signed curl weight for the class of a mode. It is the nonnegative magnitude entering the earlier coefficient estimates related to (B.16).

**Source.** [lean/CoerciveChallenge.lean:288-288](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L288). Def. **Paper.** Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:288-288](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L288).

Encoding for `Breakdown.ModeWeights.eps` (1): The signed weight still occurs in the multiplier pairing; replacing it there by its magnitude would lose the Fourier sign.

Clause 1 of `Breakdown.ModeWeights.eps`, lines 288-288: This is the absolute value of the signed curl weight for the class of a mode. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:288-288](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L288).

<a id="073"></a>

### 073. Magnitude of the velocity weight

`Breakdown.ModeWeights.mu`: This is the absolute value of the signed velocity weight for the class of a mode. It enters the frequency seminorm and the earlier coefficient estimates related to (B.16).

**Source.** [lean/CoerciveChallenge.lean:290-290](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L290). Def. **Paper.** Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:290-290](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L290).

Encoding for `Breakdown.ModeWeights.mu` (1): Its nonnegativity follows from the absolute value even before admissibility is imposed.

Clause 1 of `Breakdown.ModeWeights.mu`, lines 290-290: This is the absolute value of the signed velocity weight for the class of a mode. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:290-290](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L290).

<a id="074"></a>

### 074. Class frequency in its rotating frame

`Breakdown.ModeWeights.dop`: This applies the shifted frequency to the rotation rate assigned to a mode’s class. It corresponds to the frequency in (B.15), with direct frequency coordinates and the earlier spatially varying rate.

**Source.** [lean/CoerciveChallenge.lean:292-292](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L292). Def. **Paper.** (B.15) and the frequency seminorm immediately below it, p. 54

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:292-292](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L292).

Encoding for `Breakdown.ModeWeights.dop` (1): Positive P is a separate admissibility field; the raw function remains defined at P = 0.

Clause 1 of `Breakdown.ModeWeights.dop`, lines 292-292: This applies the shifted frequency to the rotation rate assigned to a mode’s class. Paper: (B.15) and the frequency seminorm immediately below it, p. 54 Source: [lean/CoerciveChallenge.lean:292-292](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L292).

<a id="075"></a>

### 075. Gradient size of the curl weight

`Breakdown.ModeWeights.epsGrad`: This measures the spatial derivative of the signed curl weight. It supplies the gradient-of-weight losses that enter the multiplier norm and the coefficients described after (B.16).

**Source.** [lean/CoerciveChallenge.lean:294-294](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L294). Def. **Paper.** Appendix B.2, coefficient discussion p. 54 and (B.19), p. 55; earlier class-weight encoding

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:294-294](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L294).

Encoding for `Breakdown.ModeWeights.epsGrad` (1): The weights are Lipschitz under admissibility, so their derivatives are meaningful almost everywhere even when they have spline knots.

Encoding for `Breakdown.ModeWeights.epsGrad` (2): The total fderiv value at a nondifferentiable point does not assert differentiability there.

Clause 1 of `Breakdown.ModeWeights.epsGrad`, lines 294-294: This measures the spatial derivative of the signed curl weight. Paper: Appendix B.2, coefficient discussion p. 54 and (B.19), p. 55; earlier class-weight encoding Source: [lean/CoerciveChallenge.lean:294-294](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L294).

<a id="076"></a>

### 076. Gradient size of the velocity weight

`Breakdown.ModeWeights.muGrad`: This measures the spatial derivative of the signed velocity weight. It enters the mixed derivative loss in the earlier version of the quadratic form associated with (B.16).

**Source.** [lean/CoerciveChallenge.lean:296-296](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L296). Def. **Paper.** Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:296-296](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L296).

Encoding for `Breakdown.ModeWeights.muGrad` (1): The derivative is used under the Lipschitz and decay conditions of ModeWeights.IsAdmissible; it is a total function outside those conditions.

Clause 1 of `Breakdown.ModeWeights.muGrad`, lines 296-296: This measures the spatial derivative of the signed velocity weight. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:296-296](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L296).

<a id="077"></a>

### 077. Neighbouring curl-weight bound

`Breakdown.ModeWeights.epsNb`: This takes the largest curl-weight magnitude among modes joined to the given mode by a listed reference-profile wave. It bounds the mode couplings discussed after (B.16).

**Source.** [lean/CoerciveChallenge.lean:298-299](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L298-L299). Def. **Paper.** Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:298-299](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L298-L299).

Encoding for `Breakdown.ModeWeights.epsNb` (1): The supremum is a finite supremum in nonnegative reals and is zero when the wave set is empty.

Encoding for `Breakdown.ModeWeights.epsNb` (2): It is not a conditionally complete real supremum over an unbounded set.

Clause 1 of `Breakdown.ModeWeights.epsNb`, lines 298-299: This takes the largest curl-weight magnitude among modes joined to the given mode by a listed reference-profile wave. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:298-299](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L298-L299).

<a id="078"></a>

### 078. Neighbouring velocity-weight bound

`Breakdown.ModeWeights.muNb`: This takes the largest velocity-weight magnitude among modes joined to the given mode by a listed reference-profile wave. It bounds the velocity multiplier’s off-mode losses in the earlier version of (B.16).

**Source.** [lean/CoerciveChallenge.lean:301-302](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L301-L302). Def. **Paper.** Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:301-302](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L301-L302).

Encoding for `Breakdown.ModeWeights.muNb` (1): The finite nonnegative supremum returns zero for an empty wave set, representing absence of those wave couplings.

Clause 1 of `Breakdown.ModeWeights.muNb`, lines 301-302: This takes the largest velocity-weight magnitude among modes joined to the given mode by a listed reference-profile wave. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:301-302](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L301-L302).

<a id="079"></a>

### 079. Indicator of a condition

`Breakdown.ModeWeights.ind`: This encodes a logical condition as the real number zero or one. The coefficient formulas use it to charge an error budget only when the corresponding weight or coupling is active.

**Source.** [lean/CoerciveChallenge.lean:305-305](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L305). Def. **Paper.** Encoding helper for the unexpanded coefficients of (B.16), p. 54; no separately numbered condition

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:305-305](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L305).

Encoding for `Breakdown.ModeWeights.ind` (1): Classical decidability is used for arbitrary propositions; the definition is mathematical and need not be an executable membership test.

Clause 1 of `Breakdown.ModeWeights.ind`, lines 305-305: This encodes a logical condition as the real number zero or one. Paper: Encoding helper for the unexpanded coefficients of (B.16), p. 54; no separately numbered condition Source: [lean/CoerciveChallenge.lean:305-305](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L305).

<a id="080"></a>

### 080. Curl-gradient energy already assigned

`Breakdown.ModeWeights.shareHat`: This adds the shares spent on the active curl weight and on its neighbouring modes. Subtracting it from one reduces the curl-gradient coefficient corresponding to I′₂ in (B.16).

**Source.** [lean/CoerciveChallenge.lean:307-308](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L307-L308). Def. **Paper.** Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:307-308](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L307-L308).

Encoding for `Breakdown.ModeWeights.shareHat` (1): The first share is active if the weight or its derivative is nonzero; the second is active if a neighbouring weight is positive.

Encoding for `Breakdown.ModeWeights.shareHat` (2): Admissibility requires D to lie below the remaining share.

Clause 1 of `Breakdown.ModeWeights.shareHat`, lines 307-308: This adds the shares spent on the active curl weight and on its neighbouring modes. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:307-308](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L307-L308).

<a id="081"></a>

### 081. Operator norm of a scalar Hessian

`Breakdown.ModeWeights.secondDerivNorm`: This is the operator norm of the second Fréchet derivative of a scalar conversion weight. It appears in the conversion losses for D and Z described explicitly below (B.16).

**Source.** [lean/CoerciveChallenge.lean:310-310](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L310). Def. **Paper.** (B.16) and the unexpanded coefficient formulas described below it, p. 54

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:310-310](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L310).

Encoding for `Breakdown.ModeWeights.secondDerivNorm` (1): This norm is an operator norm, unlike the Frobenius norms used for the Fourier derivative arrays.

Encoding for `Breakdown.ModeWeights.secondDerivNorm` (2): The conversion weights are required to be C² before their Hessian norms are used analytically.

Clause 1 of `Breakdown.ModeWeights.secondDerivNorm`, lines 310-310: This is the operator norm of the second Fréchet derivative of a scalar conversion weight. Paper: (B.16) and the unexpanded coefficient formulas described below it, p. 54 Source: [lean/CoerciveChallenge.lean:310-310](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L310).

<a id="082"></a>

### 082. Curl coefficient before conversion

`Breakdown.ModeWeights.coefA`: This is the earlier curl-energy coefficient before subtracting Z: it starts at 1/4, gains from the rotating-frame frequency, and pays for transport and wave couplings. Its role is the coefficient I′₁ in (B.16), whose full formulas the paper leaves to the formalization.

**Source.** [lean/CoerciveChallenge.lean:312-317](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L312-L317). Def. **Paper.** Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:312-317](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L312-L317).

Encoding for `Breakdown.ModeWeights.coefA` (1): All denominator guards come from ModeWeights.IsAdmissible, with share1 required positive where the curl weight or its gradient is active.

Encoding for `Breakdown.ModeWeights.coefA` (2): The whole formula belongs to the earlier class-weight route and should not be presented as the paper’s displayed piecewise formula.

Clause 1 of `Breakdown.ModeWeights.coefA`, lines 312-317: This is the earlier curl-energy coefficient before subtracting Z: it starts at 1/4, gains from the rotating-frame frequency, and pays for transport and wave couplings. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:312-317](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L312-L317).

<a id="083"></a>

### 083. Gradient coefficient after conversion

`Breakdown.ModeWeights.coefAA`: This is the earlier coefficient of the squared gradient mode after the Z conversion and subtraction of c times the energy weight. It also subtracts the D Hessian loss, vorticity losses and velocity-coupling share.

**Source.** [lean/CoerciveChallenge.lean:319-321](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L319-L321). Def. **Paper.** Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:319-321](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L319-L321).

Encoding for `Breakdown.ModeWeights.coefAA` (1): The coefficient may have either sign; pointwise positivity of the full density is a separate obligation.

Clause 1 of `Breakdown.ModeWeights.coefAA`, lines 319-321: This is the earlier coefficient of the squared gradient mode after the Z conversion and subtraction of c times the energy weight. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:319-321](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L319-L321).

<a id="084"></a>

### 084. Velocity-weight coupling penalty

`Breakdown.ModeWeights.penalty`: This records Young-inequality losses caused by the mean derivative and the nonzero waves in the earlier velocity multiplier. The activity tests depend on whether a signed weight is nonzero anywhere, rather than only at the current point.

**Source.** [lean/CoerciveChallenge.lean:323-326](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L323-L326). Def. **Paper.** Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:323-326](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L323-L326).

Encoding for `Breakdown.ModeWeights.penalty` (1): The existence tests are global in space; a locally zero weight can still activate a global-support penalty.

Encoding for `Breakdown.ModeWeights.penalty` (2): The eta and etaMin denominators are strictly positive under admissibility.

Clause 1 of `Breakdown.ModeWeights.penalty`, lines 323-326: This records Young-inequality losses caused by the mean derivative and the nonzero waves in the earlier velocity multiplier. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:323-326](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L323-L326).

<a id="085"></a>

### 085. Velocity coefficient after losses

`Breakdown.ModeWeights.coefB`: This is the earlier coefficient of the squared velocity mode in the quadratic lower bound. Its positive rotating-frame contribution is reduced by rotation, wave, Z-Hessian and Young-inequality losses.

**Source.** [lean/CoerciveChallenge.lean:328-331](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L328-L331). Def. **Paper.** Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:328-331](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L328-L331).

Encoding for `Breakdown.ModeWeights.coefB` (1): The coefficient need not be nonnegative by definition; later lower-bound arguments handle negative terms.

Clause 1 of `Breakdown.ModeWeights.coefB`, lines 328-331: This is the earlier coefficient of the squared velocity mode in the quadratic lower bound. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:328-331](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L328-L331).

<a id="086"></a>

### 086. Mixed gradient-velocity loss

`Breakdown.ModeWeights.coefC`: This is the coefficient of the mixed gradient-velocity term in the earlier class-weight density. The printed piecewise form (B.16) absorbs such products into its five squared-amplitude coefficients.

**Source.** [lean/CoerciveChallenge.lean:333-334](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L333-L334). Def. **Paper.** Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:333-334](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L333-L334).

Encoding for `Breakdown.ModeWeights.coefC` (1): The mixed term has an overall negative sign when modeDensity is assembled; its sign cannot be inferred from this name alone.

Clause 1 of `Breakdown.ModeWeights.coefC`, lines 333-334: This is the coefficient of the mixed gradient-velocity term in the earlier class-weight density. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:333-334](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L333-L334).

<a id="087"></a>

### 087. Earlier quadratic form for one mode

`Breakdown.ModeWeights.modeDensity`: This assembles the earlier mode lower bound from the Hessian, curl-gradient, gradient, curl and velocity amplitudes. It has an additional mixed gradient-velocity term compared with the five squared terms printed in (B.16).

**Source.** [lean/CoerciveChallenge.lean:336-339](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L336-L339). Def. **Paper.** Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:336-339](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L336-L339).

Encoding for `Breakdown.ModeWeights.modeDensity` (1): The input order is x2 = |∇²v̂|, xc = |∇curl v̂|, x1 = |∇v̂|, xo = |curl v̂| and x0 = |v̂|.

Encoding for `Breakdown.ModeWeights.modeDensity` (2): The displayed raw algebra does not assert any amplitude is nonnegative or comes from a field.

Clause 1 of `Breakdown.ModeWeights.modeDensity`, lines 337-337: Hessian and curl-gradient coefficients after assigning shares. Paper: (B.16) and the unexpanded coefficient formulas described below it, p. 54 Source: [lean/CoerciveChallenge.lean:337-337](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L337).

Clause 2 of `Breakdown.ModeWeights.modeDensity`, lines 338-339: Curl, gradient and velocity coefficients, with an additional mixed loss. Paper: (B.16) and the unexpanded coefficient formulas described below it, p. 54 Source: [lean/CoerciveChallenge.lean:338-339](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L338-L339).

<a id="088"></a>

### 088. Earlier density evaluated on a mode

`Breakdown.ModeWeights.modeTerm`: This substitutes the actual Fourier-mode amplitudes of v, G and H into the earlier quadratic form. It is the integrand corresponding to one Iι before the separate stretching term is added.

**Source.** [lean/CoerciveChallenge.lean:341-346](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L341-L346). Def. **Paper.** Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:341-346](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L341-L346).

Encoding for `Breakdown.ModeWeights.modeTerm` (1): The square roots of the finite sums of squared moduli are nonnegative.

Encoding for `Breakdown.ModeWeights.modeTerm` (2): The weak derivative relations between v, G and H are supplied by IsPerturbation.

Clause 1 of `Breakdown.ModeWeights.modeTerm`, lines 341-346: This substitutes the actual Fourier-mode amplitudes of v, G and H into the earlier quadratic form. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:341-346](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L341-L346).

<a id="089"></a>

### 089. Earlier frequency seminorm squared

`Breakdown.ModeWeights.frequencySeminormSq`: This integrates the squared velocity modes against the magnitude of the signed velocity weight and the rotating-frame frequency. It is the class-weight version of the seminorm defined immediately after (B.15).

**Source.** [lean/CoerciveChallenge.lean:348-350](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L348-L350). Def. **Paper.** (B.15) and the frequency seminorm immediately below it, p. 54

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:348-350](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L348-L350).

Encoding for `Breakdown.ModeWeights.frequencySeminormSq` (1): The ENNReal sum and nonnegative integral may take the value infinity; they do not silently default to zero.

Encoding for `Breakdown.ModeWeights.frequencySeminormSq` (2): multiplier_density explicitly proves finiteness before this quantity is used as a real norm.

Clause 1 of `Breakdown.ModeWeights.frequencySeminormSq`, lines 348-350: This integrates the squared velocity modes against the magnitude of the signed velocity weight and the rotating-frame frequency. Paper: (B.15) and the frequency seminorm immediately below it, p. 54 Source: [lean/CoerciveChallenge.lean:348-350](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L348-L350).

<a id="090"></a>

### 090. Admissible class-based weights

`Breakdown.ModeWeights.IsAdmissible`: This states the sign, symmetry, regularity, decay and budget conditions needed by the earlier multiplier route. It makes many analytic side conditions explicit; its signed class-weight parametrization differs from the piece families used in the printed Appendix B.2.

**Source.** [lean/CoerciveChallenge.lean:359-424](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L359-L424). Structure. **Paper.** Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:358-423](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L358-L423).

Encoding for `Breakdown.ModeWeights.IsAdmissible` (1): Derivative bounds use total fderiv, while global Lipschitz conditions supply almost-everywhere differentiability.

Encoding for `Breakdown.ModeWeights.IsAdmissible` (2): share1 may vanish only where both the curl weight and its derivative are inactive; every other displayed denominator has a separate strict-positivity guard.

Encoding for `Breakdown.ModeWeights.IsAdmissible` (3): The field conv_le controls the curl-gradient coefficient only; it does not assert that every coefficient or the complete density is nonnegative.

Encoding for `Breakdown.ModeWeights.IsAdmissible` (4): The wave list can be empty; the zero mode is handled separately by meanField and FlowBounds.IsValid.

Field `Breakdown.ModeWeights.IsAdmissible.finite_classes`: The collection of weight classes is finite. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:360-360](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L360).

Field `Breakdown.ModeWeights.IsAdmissible.c_pos`: The reserved weighted-energy coefficient c is positive. Paper: Proposition B.1 and (B.20), p. 55; constants abstracted in the earlier encoding Source: [lean/CoerciveChallenge.lean:361-361](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L361).

Field `Breakdown.ModeWeights.IsAdmissible.c_lt_one`: The reserved weighted-energy coefficient is less than one. Paper: Proposition B.1 and (B.20), p. 55; constants abstracted in the earlier encoding Source: [lean/CoerciveChallenge.lean:362-362](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L362).

Field `Breakdown.ModeWeights.IsAdmissible.cμ_pos`: The retained frequency-energy coefficient cμ is positive. Paper: Proposition B.1 and (B.20), p. 55; constants abstracted in the earlier encoding Source: [lean/CoerciveChallenge.lean:363-363](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L363).

Field `Breakdown.ModeWeights.IsAdmissible.cμ_lt_one`: The retained frequency-energy coefficient is less than one. Paper: Proposition B.1 and (B.20), p. 55; constants abstracted in the earlier encoding Source: [lean/CoerciveChallenge.lean:364-364](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L364).

Field `Breakdown.ModeWeights.IsAdmissible.period_pos`: The physical similarity period P is positive. Paper: §7.1 and (7.1), p. 30 Source: [lean/CoerciveChallenge.lean:365-365](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L365).

Field `Breakdown.ModeWeights.IsAdmissible.weight_pos`: The lower energy-weight bound w₀ is positive. Paper: (7.14) and its hypotheses, p. 32 Source: [lean/CoerciveChallenge.lean:366-366](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L366).

Field `Breakdown.ModeWeights.IsAdmissible.weight_lower`: The energy weight is at least w₀ at every spatial point. Paper: (7.14) and its hypotheses, p. 32 Source: [lean/CoerciveChallenge.lean:367-367](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L367).

Field `Breakdown.ModeWeights.IsAdmissible.weight_measurable`: The energy weight is measurable. Paper: (7.14) and its hypotheses, p. 32 Source: [lean/CoerciveChallenge.lean:368-368](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L368).

Field `Breakdown.ModeWeights.IsAdmissible.weight_axi`: The energy weight is invariant under axial rotations. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:369-369](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L369).

Field `Breakdown.ModeWeights.IsAdmissible.waves_neg`: Every listed nonzero wave is accompanied by its negative. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:370-370](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L370).

Field `Breakdown.ModeWeights.IsAdmissible.waves_ne_zero`: The zero mode is excluded from the oscillatory wave list. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:371-371](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L371).

Field `Breakdown.ModeWeights.IsAdmissible.epsW_odd`: The signed curl weight changes sign when the mode is negated. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:372-372](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L372).

Field `Breakdown.ModeWeights.IsAdmissible.muW_odd`: The signed velocity weight changes sign when the mode is negated. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:373-373](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L373).

Field `Breakdown.ModeWeights.IsAdmissible.rate_even`: Opposite modes have the same rotation rate. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:374-374](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L374).

Field `Breakdown.ModeWeights.IsAdmissible.convD_even`: Opposite modes have the same D conversion weight. Paper: Appendix B.2, p. 53, and the conversion terms of (B.16), p. 54 Source: [lean/CoerciveChallenge.lean:375-375](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L375).

Field `Breakdown.ModeWeights.IsAdmissible.convZ_even`: Opposite modes have the same Z conversion weight. Paper: Appendix B.2, p. 53, and the conversion terms of (B.16), p. 54 Source: [lean/CoerciveChallenge.lean:376-376](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L376).

Field `Breakdown.ModeWeights.IsAdmissible.share1_even`: Opposite modes have the same first error share. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:377-377](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L377).

Field `Breakdown.ModeWeights.IsAdmissible.eta_even`: Opposite modes have the same velocity Young parameter. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:378-378](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L378).

Field `Breakdown.ModeWeights.IsAdmissible.epsW_increment`: Each signed curl weight is globally Lipschitz, with its own constant. Paper: Appendix B.2, pp. 53 and 55; analytic regularity/decay made explicit in Lean; earlier class-weight form Source: [lean/CoerciveChallenge.lean:379-379](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L379).

Field `Breakdown.ModeWeights.IsAdmissible.muW_increment`: Each signed velocity weight is globally Lipschitz, with its own constant. Paper: Appendix B.2, pp. 53 and 55; analytic regularity/decay made explicit in Lean; earlier class-weight form Source: [lean/CoerciveChallenge.lean:380-380](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L380).

Field `Breakdown.ModeWeights.IsAdmissible.epsW_axi`: Every signed curl weight is invariant under axial rotations. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:381-381](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L381).

Field `Breakdown.ModeWeights.IsAdmissible.muW_axi`: Every signed velocity weight is invariant under axial rotations. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:382-382](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L382).

Field `Breakdown.ModeWeights.IsAdmissible.rate_axi`: Every classwise rotation-rate function is axisymmetric. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:383-383](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L383).

Field `Breakdown.ModeWeights.IsAdmissible.convD_axi`: Every D conversion weight is axisymmetric. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:384-384](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L384).

Field `Breakdown.ModeWeights.IsAdmissible.convZ_axi`: Every Z conversion weight is axisymmetric. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:385-385](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L385).

Field `Breakdown.ModeWeights.IsAdmissible.share1_axi`: Every first error-share function is axisymmetric. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:386-386](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L386).

Field `Breakdown.ModeWeights.IsAdmissible.share2_axi`: The second error-share function is axisymmetric. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:387-387](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L387).

Field `Breakdown.ModeWeights.IsAdmissible.share4_axi`: The fourth error-share function is axisymmetric. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:388-388](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L388).

Field `Breakdown.ModeWeights.IsAdmissible.len_axi`: The stretching balancing length is axisymmetric. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:389-389](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L389).

Field `Breakdown.ModeWeights.IsAdmissible.len2_axi`: The wave-error balancing length is axisymmetric. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:390-390](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L390).

Field `Breakdown.ModeWeights.IsAdmissible.rate_measurable`: Each classwise rotation-rate function is measurable. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:391-391](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L391).

Field `Breakdown.ModeWeights.IsAdmissible.share1_measurable`: Each first error-share function is measurable. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:392-392](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L392).

Field `Breakdown.ModeWeights.IsAdmissible.share2_measurable`: The second error-share function is measurable. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:393-393](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L393).

Field `Breakdown.ModeWeights.IsAdmissible.share4_measurable`: The fourth error-share function is measurable. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:394-394](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L394).

Field `Breakdown.ModeWeights.IsAdmissible.len_measurable`: The stretching balancing length is measurable. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:395-395](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L395).

Field `Breakdown.ModeWeights.IsAdmissible.len2_measurable`: The wave-error balancing length is measurable. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:396-396](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L396).

Field `Breakdown.ModeWeights.IsAdmissible.rate_bounded`: One finite bound controls all rotation-rate functions everywhere. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:397-397](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L397).

Field `Breakdown.ModeWeights.IsAdmissible.epsW_sign`: The signed curl weight agrees in sign with the rotating-frame frequency. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:398-398](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L398).

Field `Breakdown.ModeWeights.IsAdmissible.muW_sign`: The signed velocity weight agrees in sign with the rotating-frame frequency. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:399-399](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L399).

Field `Breakdown.ModeWeights.IsAdmissible.epsW_le`: Every curl-weight magnitude is at most epsSup. Paper: (B.19) and the admissibility paragraph, p. 55; earlier class-weight version Source: [lean/CoerciveChallenge.lean:400-400](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L400).

Field `Breakdown.ModeWeights.IsAdmissible.epsW_grad_le`: Every curl-weight derivative norm is at most epsGradSup. Paper: (B.19) and the admissibility paragraph, p. 55; earlier class-weight version Source: [lean/CoerciveChallenge.lean:401-401](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L401).

Field `Breakdown.ModeWeights.IsAdmissible.epsW_decay`: The curl weights have a uniform inverse-radius bound at infinity. Paper: Appendix B.2, pp. 53 and 55; analytic regularity/decay made explicit in Lean; earlier class-weight form Source: [lean/CoerciveChallenge.lean:402-402](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L402).

Field `Breakdown.ModeWeights.IsAdmissible.muW_decay`: Velocity weights and their derivatives satisfy the uniform bounds needed at infinity. Paper: Appendix B.2, pp. 53 and 55; analytic regularity/decay made explicit in Lean; earlier class-weight form Source: [lean/CoerciveChallenge.lean:403-404](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L403-L404).

Field `Breakdown.ModeWeights.IsAdmissible.mu_ratio`: The velocity-weight magnitude is bounded by ratio times the absolute frame frequency. Paper: (B.19) and the admissibility paragraph, p. 55; earlier class-weight version Source: [lean/CoerciveChallenge.lean:405-405](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L405).

Field `Breakdown.ModeWeights.IsAdmissible.ratio_nonneg`: The frequency-to-weight comparison constant is nonnegative. Paper: (B.19) and the admissibility paragraph, p. 55; earlier class-weight version Source: [lean/CoerciveChallenge.lean:406-406](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L406).

Field `Breakdown.ModeWeights.IsAdmissible.convD_smooth`: Each D conversion weight is C². Paper: Appendix B.2, p. 53, and the conversion terms of (B.16), p. 54 Source: [lean/CoerciveChallenge.lean:407-407](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L407).

Field `Breakdown.ModeWeights.IsAdmissible.convZ_smooth`: Each Z conversion weight is C². Paper: Appendix B.2, p. 53, and the conversion terms of (B.16), p. 54 Source: [lean/CoerciveChallenge.lean:408-408](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L408).

Field `Breakdown.ModeWeights.IsAdmissible.convD_nonneg`: Each D conversion weight is pointwise nonnegative. Paper: Appendix B.2, p. 53, and the conversion terms of (B.16), p. 54 Source: [lean/CoerciveChallenge.lean:409-409](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L409).

Field `Breakdown.ModeWeights.IsAdmissible.convD_decay`: D and its first two derivatives obey uniform radius-weighted bounds. Paper: Appendix B.2, pp. 53 and 55; analytic regularity/decay made explicit in Lean; earlier class-weight form Source: [lean/CoerciveChallenge.lean:410-410](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L410).

Field `Breakdown.ModeWeights.IsAdmissible.convZ_decay`: Z and its first two derivatives obey uniform bounds with powers of 1 + |y|. Paper: Appendix B.2, pp. 53 and 55; analytic regularity/decay made explicit in Lean; earlier class-weight form Source: [lean/CoerciveChallenge.lean:411-411](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L411).

Field `Breakdown.ModeWeights.IsAdmissible.share1_nonneg`: The first error share is nonnegative everywhere. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:412-412](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L412).

Field `Breakdown.ModeWeights.IsAdmissible.share1_pos`: The first error share is positive wherever the curl weight or its derivative is active. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:413-413](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L413).

Field `Breakdown.ModeWeights.IsAdmissible.share2_pos`: The second error share is strictly positive everywhere. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:414-414](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L414).

Field `Breakdown.ModeWeights.IsAdmissible.share4_pos`: The fourth error share is strictly positive everywhere. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:415-415](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L415).

Field `Breakdown.ModeWeights.IsAdmissible.len_pos`: The stretching balancing length is strictly positive. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:416-416](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L416).

Field `Breakdown.ModeWeights.IsAdmissible.len2_pos`: The wave-error balancing length is strictly positive. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:417-417](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L417).

Field `Breakdown.ModeWeights.IsAdmissible.share4_bounded`: The fourth error share has a common upper bound. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:418-418](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L418).

Field `Breakdown.ModeWeights.IsAdmissible.len_bounded`: Both reciprocal stretching-length combinations have a uniform finite bound. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:419-419](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L419).

Field `Breakdown.ModeWeights.IsAdmissible.len2_bounded`: Both reciprocal wave-length combinations have a uniform finite bound. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:420-420](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L420).

Field `Breakdown.ModeWeights.IsAdmissible.eta_pos`: Every classwise velocity Young parameter is positive. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:421-421](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L421).

Field `Breakdown.ModeWeights.IsAdmissible.etaMin_pos`: The common lower Young parameter is positive. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:422-422](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L422).

Field `Breakdown.ModeWeights.IsAdmissible.etaMin_le`: The common lower Young parameter is no larger than any classwise one. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:423-423](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L423).

Field `Breakdown.ModeWeights.IsAdmissible.conv_le`: The D conversion weight does not exceed the remaining curl-gradient share. Paper: Nonnegativity of I′₂ in the admissibility paragraph, p. 55, for the earlier coefficient formula Source: [lean/CoerciveChallenge.lean:424-424](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L424).

<a id="091"></a>

### 091. Spatial derivative of the profile

`Breakdown.gradField`: This provides the spatial derivative of W used in the Fourier gradient modes and the stretching form. The strong multiplier theorem requires W to be C², so this derivative has its ordinary analytic meaning there.

**Source.** [lean/CoerciveChallenge.lean:428-429](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L428-L429). Def. **Paper.** Derivative notation in (B.16), p. 54, and (B.18), p. 55

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:427-428](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L427-L428).

Encoding for `Breakdown.gradField` (1): At an arbitrary nonsmooth input, fderiv is a total operation and must not be read as a proof of differentiability.

Clause 1 of `Breakdown.gradField`, lines 428-429: This provides the spatial derivative of W used in the Fourier gradient modes and the stretching form. Paper: Derivative notation in (B.16), p. 54, and (B.18), p. 55 Source: [lean/CoerciveChallenge.lean:428-429](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L428-L429).

<a id="092"></a>

### 092. Spatial second derivative of the profile

`Breakdown.secondDerivField`: This supplies the iterated spatial derivative of W used in ∇curl W. It belongs to the strong C² route; the extended weak route keeps a separate weak Hessian for the piecewise-polynomial profile.

**Source.** [lean/CoerciveChallenge.lean:431-432](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L431-L432). Def. **Paper.** Derivative notation in (B.16), p. 54, and (B.18), p. 55; weak second derivatives in §7.2, p. 31

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:430-431](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L430-L431).

Encoding for `Breakdown.secondDerivField` (1): The nested fderiv calls are total outside the regularity hypotheses and do not themselves certify a Hessian.

Clause 1 of `Breakdown.secondDerivField`, lines 431-432: This supplies the iterated spatial derivative of W used in ∇curl W. Paper: Derivative notation in (B.16), p. 54, and (B.18), p. 55; weak second derivatives in §7.2, p. 31 Source: [lean/CoerciveChallenge.lean:431-432](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L431-L432).

<a id="093"></a>

### 093. Quadratic form of the symmetric part

`Breakdown.symPartForm`: This evaluates u·Gu, which equals the quadratic form of the symmetric part of G over the reals. The mean and wave bounds use it to control the stretching term J.

**Source.** [lean/CoerciveChallenge.lean:434-434](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L434). Def. **Paper.** (B.18) and the positive/negative integral convention, p. 55

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:433-433](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L433).

Encoding for `Breakdown.symPartForm` (1): No symmetric matrix is constructed: the antisymmetric part contributes zero to this scalar quadratic form.

Clause 1 of `Breakdown.symPartForm`, lines 434-434: This evaluates u·Gu, which equals the quadratic form of the symmetric part of G over the reals. Paper: (B.18) and the positive/negative integral convention, p. 55 Source: [lean/CoerciveChallenge.lean:434-434](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L434).

<a id="094"></a>

### 094. Validity of the mean and wave bounds

`Breakdown.FlowBounds.IsValid`: This attaches the stored majorants to the reference field by explicit pointwise inequalities and a finite Fourier reconstruction. It serves the same purpose as the profile bounds before (B.16), using the earlier mean/wave decomposition.

**Source.** [lean/CoerciveChallenge.lean:436-455](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L436-L455). Structure. **Paper.** Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:435-454](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L435-L454).

Encoding for `Breakdown.FlowBounds.IsValid` (1): A numerical table of majorants alone is insufficient; this predicate binds each bound to W.

Encoding for `Breakdown.FlowBounds.IsValid` (2): The harmonic reconstruction is pointwise for all times and spatial points.

Field `Breakdown.FlowBounds.IsValid.harmonics`: Reconstruct the reference field from its mean mode and the listed nonzero waves. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:438-439](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L438-L439).

Field `Breakdown.FlowBounds.IsValid.perpSpeed_ge`: Bound the mean-field transport velocity in every classwise rotating frame. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:440-440](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L440).

Field `Breakdown.FlowBounds.IsValid.meanVort_ge`: Bound the curl of the mean field. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:441-441](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L441).

Field `Breakdown.FlowBounds.IsValid.meanVortGrad_ge`: Bound the derivative of the curl of the mean field. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:442-442](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L442).

Field `Breakdown.FlowBounds.IsValid.meanStretch_ge`: Bound the mean symmetric-gradient quadratic form from above. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:443-443](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L443).

Field `Breakdown.FlowBounds.IsValid.meanGrad_ge`: Bound the operator norm of the mean-field derivative. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:444-444](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L444).

Field `Breakdown.FlowBounds.IsValid.wave0_ge`: Bound the sum of the velocity amplitudes of all listed waves. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:445-445](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L445).

Field `Breakdown.FlowBounds.IsValid.wave1_ge`: Bound the sum of the gradient amplitudes of all listed waves. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:446-446](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L446).

Field `Breakdown.FlowBounds.IsValid.waveVort_ge`: Bound the sum of the vorticity amplitudes of all listed waves. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:447-448](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L447-L448).

Field `Breakdown.FlowBounds.IsValid.wave2_ge`: Bound the sum of the gradient-of-vorticity amplitudes of all listed waves. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:449-450](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L449-L450).

Field `Breakdown.FlowBounds.IsValid.waveStretch_ge`: Bound the absolute stretching form of the oscillatory field at every rotated point. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:451-453](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L451-L453).

Field `Breakdown.FlowBounds.IsValid.waveVortGrad_ge`: Bound the difference between total and mean vorticity derivatives at every rotated point. Paper: Related to Appendix B.2, pp. 53-55; this earlier class-weight encoding has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:454-455](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L454-L455).

<a id="095"></a>

### 095. Periodic divergence-free test fields

`Breakdown.IsPeriodicTestField`: These are the smooth divergence-free test fields of period one with a common compact spatial support used in (B.14). The time variable remains periodic, so compactness is required only in space.

**Source.** [lean/CoerciveChallenge.lean:457-459](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L457-L459). Def. **Paper.** (B.14), p. 54

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:456-458](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L456-L458).

Encoding for `Breakdown.IsPeriodicTestField` (1): The support radius is chosen before all times and points, giving one radius uniform in time.

Encoding for `Breakdown.IsPeriodicTestField` (2): The divergence constraint is pointwise because the test field is smooth.

Clause 1 of `Breakdown.IsPeriodicTestField`, lines 458-459: Smoothness, period one, common spatial support and vanishing divergence. Paper: (B.14), p. 54 Source: [lean/CoerciveChallenge.lean:458-459](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L458-L459).

<a id="096"></a>

### 096. Periodic scalar test potentials

`Breakdown.IsPeriodicTestPotential`: These are smooth scalar potentials of period one with a common compact spatial support. Testing the multiplier against their gradients expresses the Hdiv condition that accompanies (B.14).

**Source.** [lean/CoerciveChallenge.lean:461-463](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L461-L463). Def. **Paper.** (B.14), p. 54

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:460-462](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L460-L462).

Encoding for `Breakdown.IsPeriodicTestPotential` (1): The predicate is an encoding of the divergence-free requirement on M, not an additional pressure field for the perturbation.

Encoding for `Breakdown.IsPeriodicTestPotential` (2): The support radius is uniform in time.

Clause 1 of `Breakdown.IsPeriodicTestPotential`, lines 461-463: These are smooth scalar potentials of period one with a common compact spatial support. Paper: (B.14), p. 54 Source: [lean/CoerciveChallenge.lean:461-463](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L461-L463).

<a id="097"></a>

### 097. Complex vector pairing

`Breakdown.cdot`: This is the Hermitian component pairing in the mode terms of (B.14), linear in the first argument and conjugate-linear in the second. The conjugation is essential when converting real field pairings to Fourier modes.

**Source.** [lean/CoerciveChallenge.lean:465-465](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L465). Def. **Paper.** (B.14), p. 54

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:464-464](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L464).

Encoding for `Breakdown.cdot` (1): This pairing is not the unconjugated complex bilinear dot product.

Clause 1 of `Breakdown.cdot`, lines 465-465: This is the Hermitian component pairing in the mode terms of (B.14), linear in the first argument and conjugate-linear in the second. Paper: (B.14), p. 54 Source: [lean/CoerciveChallenge.lean:465-465](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L465).

<a id="098"></a>

### 098. Complex matrix pairing

`Breakdown.cdotMat`: This extends the same Hermitian pairing to the nine components of a gradient mode. It is a componentwise encoding used in the multiplier analysis around (B.14).

**Source.** [lean/CoerciveChallenge.lean:467-467](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L467). Def. **Paper.** Encoding helper for the mode pairings of Appendix B.2, pp. 54-55; no separately numbered definition

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:466-466](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L466).

Encoding for `Breakdown.cdotMat` (1): The Frobenius pairing conjugates the second matrix componentwise.

Clause 1 of `Breakdown.cdotMat`, lines 467-467: This extends the same Hermitian pairing to the nine components of a gradient mode. Paper: Encoding helper for the mode pairings of Appendix B.2, pp. 54-55; no separately numbered definition Source: [lean/CoerciveChallenge.lean:467-467](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L467).

<a id="099"></a>

### 099. Multiplier for class-based weights

`Breakdown.ModeWeights.IsMultiplierField`: This identifies an L², period-one, divergence-free field by its pairings with smooth test fields, as in (B.14). The signed weights are attached directly to classes in this earlier version of the construction.

**Source.** [lean/CoerciveChallenge.lean:473-485](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L473-L485). Def. **Paper.** (B.14), p. 54

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:472-484](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L472-L484).

Encoding for `Breakdown.ModeWeights.IsMultiplierField` (1): The real Fourier series in the final identity is a total tsum, whose raw value need not represent a convergent series for arbitrary inputs.

Encoding for `Breakdown.ModeWeights.IsMultiplierField` (2): For admissible callers, Breakdown/Cert/CoerciveField.lean:495-514 supplies fieldModeTerm_summable; the raw definition does not carry this proof.

Encoding for `Breakdown.ModeWeights.IsMultiplierField` (3): Finite L² mass and smooth compactly supported tests make the pressure-orthogonality pairing an integrable pairing.

Clause 1 of `Breakdown.ModeWeights.IsMultiplierField`, lines 475-478: Periodicity, finite L² mass and orthogonality to gradients. Paper: (B.14), p. 54 Source: [lean/CoerciveChallenge.lean:475-478](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L475-L478).

Clause 2 of `Breakdown.ModeWeights.IsMultiplierField`, lines 479-485: Weak defining identity for the Laplacian and signed mode multipliers. Paper: (B.14), p. 54 Source: [lean/CoerciveChallenge.lean:479-485](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L479-L485).

<a id="100"></a>

### 100. Positive part of the earlier density

`Breakdown.ModeWeights.densityPos`: This sums the positive parts of the earlier mode terms and adds the positive part of J. Its integral is the earlier route’s version of I⁺ in the convention following (B.18).

**Source.** [lean/CoerciveChallenge.lean:487-490](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L487-L490). Def. **Paper.** (B.18) and the positive/negative integral convention, p. 55

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:486-489](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L486-L489).

Encoding for `Breakdown.ModeWeights.densityPos` (1): Each term is clipped separately by ENNReal.ofReal, before summation; this is not the positive part of a pre-summed signed series.

Encoding for `Breakdown.ModeWeights.densityPos` (2): The value may be infinity, and no real conversion is made here.

Clause 1 of `Breakdown.ModeWeights.densityPos`, lines 487-490: This sums the positive parts of the earlier mode terms and adds the positive part of J. Paper: (B.18) and the positive/negative integral convention, p. 55 Source: [lean/CoerciveChallenge.lean:487-490](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L487-L490).

<a id="101"></a>

### 101. Negative part of the earlier density

`Breakdown.ModeWeights.densityNeg`: This sums the negative parts of the earlier mode terms and adds the negative part of J. Finiteness of its integral is the essential assumption for combining the two signed bounds in Lemma B.2.

**Source.** [lean/CoerciveChallenge.lean:492-496](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L492-L496). Def. **Paper.** (B.18) and the positive/negative integral convention, p. 55

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:491-495](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L491-L495).

Encoding for `Breakdown.ModeWeights.densityNeg` (1): The ENNReal sum retains infinite negative mass as infinity.

Encoding for `Breakdown.ModeWeights.densityNeg` (2): Finite negative mass is required by the assembly theorem; it cannot be removed by a later toReal call.

Clause 1 of `Breakdown.ModeWeights.densityNeg`, lines 492-496: This sums the negative parts of the earlier mode terms and adds the negative part of J. Paper: (B.18) and the positive/negative integral convention, p. 55 Source: [lean/CoerciveChallenge.lean:492-496](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L492-L496).

<a id="102"></a>

### 102. Norm constant for the multiplier

`Breakdown.ModeWeights.multiplierConstant`: This is the square-root constant cM in Proposition B.1 with the energy share c left abstract. Setting c = 3/50 turns the first factor into the printed 50/3 coefficient.

**Source.** [lean/CoerciveChallenge.lean:498-499](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L498-L499). Def. **Paper.** Proposition B.1 and (B.20), p. 55

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:497-498](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L497-L498).

Encoding for `Breakdown.ModeWeights.multiplierConstant` (1): Positive c, cμ and w₀ are separate admissibility fields; the raw formula is total at zero denominators.

Encoding for `Breakdown.ModeWeights.multiplierConstant` (2): epsSup, epsGradSup and ratio correspond to nλ, n∇λ and nμ for the appropriate weight encoding.

Clause 1 of `Breakdown.ModeWeights.multiplierConstant`, lines 498-499: This is the square-root constant cM in Proposition B.1 with the energy share c left abstract. Paper: Proposition B.1 and (B.20), p. 55 Source: [lean/CoerciveChallenge.lean:498-499](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L498-L499).

<a id="103"></a>

### 103. Pairing remaining after energy costs

`Breakdown.ModeWeights.multiplierGap`: This is the left-hand side of the multiplier lower bound (B.20), with the earlier class-weight seminorm and an abstract coefficient c. The forcing-field pairings are subtracted so that they cancel against the lower-density estimate.

**Source.** [lean/CoerciveChallenge.lean:501-505](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L501-L505). Def. **Paper.** Proposition B.1 and (B.20), p. 55

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:500-504](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L500-L504).

Encoding for `Breakdown.ModeWeights.multiplierGap` (1): The frequency seminorm uses ENNReal.toReal; multiplier_density separately supplies its finiteness.

Encoding for `Breakdown.ModeWeights.multiplierGap` (2): The definition alone does not assert that the real converted energy is the intended finite integral.

Clause 1 of `Breakdown.ModeWeights.multiplierGap`, lines 501-505: This is the left-hand side of the multiplier lower bound (B.20), with the earlier class-weight seminorm and an abstract coefficient c. Paper: Proposition B.1 and (B.20), p. 55 Source: [lean/CoerciveChallenge.lean:501-505](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L501-L505).

<a id="104"></a>

### 104. Earlier multiplier lower bound

`Breakdown.ModeWeights.multiplier_density`: This provides the class-weight multiplier, finite frequency energy, its norm bound and the signed-density comparison underlying Proposition B.1. Its extended-real comparison remains meaningful before the negative density has been shown finite.

**Source.** [lean/CoerciveChallenge.lean:507-530](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L507-L530). Readable theorem stub. **Paper.** Proposition B.1 and (B.20), p. 55

**Library.** Implementation source: [lean/Solution.lean:53-76](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Solution.lean#L53-L76).

Encoding for `Breakdown.ModeWeights.multiplier_density` (1): This source file contains a proof stub; the implementation is re-exported from Solution.lean using multiplier_density_proved.

Encoding for `Breakdown.ModeWeights.multiplier_density` (2): The hypothesis W ∈ C² guards all classical derivatives; the active weak-Hessian route is a separate extension.

Encoding for `Breakdown.ModeWeights.multiplier_density` (3): The conclusion does not itself assert finite I⁻; the later rest estimate supplies that fact.

Comparison for `Breakdown.ModeWeights.multiplier_density`: This is the earlier class-weight form of the multiplier theorem, with a mixed density term and a C² reference field. Proposition B.1 uses piece families and the weak second derivatives of the certificate data; its direct active counterpart is the extended weak-piece theorem.

Clause 1 of `Breakdown.ModeWeights.multiplier_density`, lines 507-515: Admissible weights, valid profile bounds, profile regularity and forcing hypotheses. Paper: Proposition B.1 and (B.20), p. 55 Source: [lean/CoerciveChallenge.lean:507-515](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L507-L515).

Clause 2 of `Breakdown.ModeWeights.multiplier_density`, lines 516-522: Universal perturbation scope, existence of a multiplier and finite frequency seminorm. Paper: Proposition B.1 and (B.20), p. 55 Source: [lean/CoerciveChallenge.lean:516-522](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L516-L522).

Clause 3 of `Breakdown.ModeWeights.multiplier_density`, lines 523-524: Multiplier norm bound with an abstract energy coefficient. Paper: Proposition B.1 and (B.20), p. 55 Source: [lean/CoerciveChallenge.lean:523-524](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L523-L524).

Clause 4 of `Breakdown.ModeWeights.multiplier_density`, lines 525-529: Cross-added extended-real form of the density lower bound. Paper: (B.20) and the signed-integral convention, p. 55 Source: [lean/CoerciveChallenge.lean:525-529](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L525-L529).

<a id="105"></a>

### 105. Reduced quadratic lower bound

`Breakdown.ModeWeights.diagonalDensity`: This is a scalar quadratic form in Hessian, gradient and velocity amplitudes with one mixed term. It isolates the pointwise positivity algebra used in the region inequalities (B.29) and (B.36).

**Source.** [lean/CoerciveChallenge.lean:532-532](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L532). Def. **Paper.** Algebraic helper for (B.29), p. 59, and (B.36), p. 60; no exact printed definition

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:506-506](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L506).

Clause 1 of `Breakdown.ModeWeights.diagonalDensity`, lines 532-532: This is a scalar quadratic form in Hessian, gradient and velocity amplitudes with one mixed term. Paper: Algebraic helper for (B.29), p. 59, and (B.36), p. 60; no exact printed definition Source: [lean/CoerciveChallenge.lean:532-532](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L532).

<a id="106"></a>

### 106. Positivity from a discriminant bound

`Breakdown.ModeWeights.diagonalDensity_nonneg`: This proves nonnegativity of the reduced form from nonnegative diagonal coefficients and a discriminant bound on the mixed coefficient. It is the elementary algebra used in the pointwise condition (B.29).

**Source.** [lean/CoerciveChallenge.lean:534-548](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L534-L548). Theorem with a source proof body. **Paper.** (B.29), p. 59; positivity step in Lemma B.5, p. 60

**Library.** Implementation source: [lean/Breakdown/Cert/CoerciveStatement.lean:508-522](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L508-L522).

Comparison for `Breakdown.ModeWeights.diagonalDensity_nonneg`: This is a general scalar positivity lemma with no separately stated paper theorem. It extracts the discriminant argument used in the pointwise region conditions.

Clause 1 of `Breakdown.ModeWeights.diagonalDensity_nonneg`, lines 534-535: Nonnegative diagonal terms and the mixed-term discriminant imply a nonnegative quadratic form. Paper: (B.29), p. 59 Source: [lean/CoerciveChallenge.lean:534-535](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L534-L535).

<a id="107"></a>

### 107. Positivity using angular frequency

`Breakdown.ModeWeights.azimuthalDensity_nonneg`: This first transfers angular-frequency gains from Hessian to gradient and then from gradient to velocity before applying the discriminant test. It is a scalar model of the improvement behind (B.29) and (B.36).

**Source.** [lean/CoerciveChallenge.lean:550-572](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L550-L572). Theorem with a source proof body. **Paper.** (B.29), p. 59; (B.35)-(B.36) and Lemma B.5, p. 60

**Library.** Implementation source: [lean/Breakdown/Cert/CoerciveStatement.lean:524-546](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L524-L546).

Encoding for `Breakdown.ModeWeights.azimuthalDensity_nonneg` (1): The inequalities relating x0, x1 and x2 are hypotheses; the theorem does not derive them from Fourier symmetry.

Encoding for `Breakdown.ModeWeights.azimuthalDensity_nonneg` (2): The quotients are total at r = 0, but the analytic use of angular gains is almost everywhere away from the rotation axis.

Comparison for `Breakdown.ModeWeights.azimuthalDensity_nonneg`: This scalar lemma takes the two angular-gain inequalities as inputs and has no separately printed counterpart. The full Lemma B.5 also establishes geometric gains and handles the curl terms of the five-coefficient form.

Clause 1 of `Breakdown.ModeWeights.azimuthalDensity_nonneg`, lines 550-557: Distribute the angular gains and test the resulting quadratic form. Paper: (B.29), p. 59; (B.35)-(B.36), p. 60 Source: [lean/CoerciveChallenge.lean:550-557](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L550-L557).

<a id="108"></a>

### 108. Angular gains for two derivatives

`Breakdown.ModeWeights.mode_azimuthal_gain`: This gives the velocity-to-gradient and gradient-to-Hessian gains from (B.35) for a mode with |k| ≥ 2. The generic second mode coordinate is the actual azimuthal frequency k, which equals κι₁ in the paper.

**Source.** [lean/CoerciveChallenge.lean:574-582](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L574-L582). Readable theorem stub. **Paper.** Lemma B.5 and (B.35), p. 60

**Library.** Implementation source: [lean/Solution.lean:78-86](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Solution.lean#L78-L86).

Encoding for `Breakdown.ModeWeights.mode_azimuthal_gain` (1): The statement holds almost everywhere in space-time, so the zero cylindrical radius is confined to a null exceptional set.

Encoding for `Breakdown.ModeWeights.mode_azimuthal_gain` (2): Only two of the four inequalities displayed in (B.35) are included in this export.

Comparison for `Breakdown.ModeWeights.mode_azimuthal_gain`: The export supplies two of the four inequalities in (B.35) and assumes |k| ≥ 2, so it can omit positive-part notation. Lemma B.5 also includes the curl bound and the curl-to-curl-gradient gain.

Clause 1 of `Breakdown.ModeWeights.mode_azimuthal_gain`, lines 574-581: Two almost-everywhere angular gains under |k| ≥ 2. Paper: (B.35), p. 60 Source: [lean/CoerciveChallenge.lean:574-581](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L574-L581).

<a id="109"></a>

### 109. Cost of the earlier stretching bound

`Breakdown.ModeWeights.stretchCharge`: This is the modewise cost used to control the time-angle mean of the stretching term in the earlier mean/wave route. It separates mean and oscillatory vorticity-gradient contributions, with a balancing length for the latter.

**Source.** [lean/CoerciveChallenge.lean:584-590](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L584-L590). Def. **Paper.** Related to (B.18), p. 55, and the stretching lower bound (B.25), p. 57; earlier mean/wave estimate has no exact printed counterpart

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:548-554](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L548-L554).

Encoding for `Breakdown.ModeWeights.stretchCharge` (1): The coefficient √2 + 1/2 belongs to this earlier bound; the printed cell argument uses its own sharper constants and a different bound decomposition.

Encoding for `Breakdown.ModeWeights.stretchCharge` (2): Its denominator len is guarded by a strict-positivity assumption in stretch_mean_bound.

Clause 1 of `Breakdown.ModeWeights.stretchCharge`, lines 584-590: This is the modewise cost used to control the time-angle mean of the stretching term in the earlier mean/wave route. Paper: Related to (B.18), p. 55, and the stretching lower bound (B.25), p. 57; earlier mean/wave estimate has no exact printed counterpart Source: [lean/CoerciveChallenge.lean:584-590](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L584-L590).

<a id="110"></a>

### 110. Bound the mean stretching loss

`Breakdown.ModeWeights.stretch_mean_bound`: This bounds the negative part of the time-angle average of J by a sum of modewise costs in the earlier mean/wave route. It is a precursor to the cell-layer stretching estimate described around (B.25) and (B.32).

**Source.** [lean/CoerciveChallenge.lean:592-601](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L592-L601). Readable theorem stub. **Paper.** (B.18), p. 55; related stretching estimates (B.25), p. 57, and (B.32), p. 59

**Library.** Implementation source: [lean/Solution.lean:88-97](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Solution.lean#L88-L97).

Encoding for `Breakdown.ModeWeights.stretch_mean_bound` (1): The left side is ENNReal.ofReal of the negative mean, so a nonnegative mean contributes zero.

Encoding for `Breakdown.ModeWeights.stretch_mean_bound` (2): The conclusion is almost everywhere in space, and the right side is a nonnegative extended-real series.

Encoding for `Breakdown.ModeWeights.stretch_mean_bound` (3): The source is a stub here and has a proved implementation through Solution.lean.

Comparison for `Breakdown.ModeWeights.stretch_mean_bound`: The paper’s cell bound uses different coefficient data and constants from this earlier mean/wave estimate. This export controls the same stretching expression but should not be labelled an exact statement of Proposition B.4.

Clause 1 of `Breakdown.ModeWeights.stretch_mean_bound`, lines 592-595: Regularity, bound validity and a positive balancing length. Paper: (B.18), p. 55; related (B.25), p. 57 Source: [lean/CoerciveChallenge.lean:592-595](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L592-L595).

Clause 2 of `Breakdown.ModeWeights.stretch_mean_bound`, lines 596-600: Almost-everywhere mean stretching estimate with the earlier modewise charges. Paper: Related to (B.32), p. 59 Source: [lean/CoerciveChallenge.lean:596-600](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L596-L600).

<a id="111"></a>

### 111. Combine signed bounds safely

`Breakdown.ModeWeights.le_of_ennreal_bounds`: This turns two cross-added extended-real comparisons into a real inequality after assuming the negative mass is finite. It first derives finiteness of the positive mass, implementing the cancellation used in Lemma B.2 without subtracting infinity.

**Source.** [lean/CoerciveChallenge.lean:604-630](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L604-L630). Theorem with a source proof body. **Paper.** Signed-integral convention after (B.18), p. 55; cancellation in Lemma B.2, p. 56

**Library.** Implementation source: [lean/Breakdown/Cert/CoerciveStatement.lean:556-582](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L556-L582).

Encoding for `Breakdown.ModeWeights.le_of_ennreal_bounds` (1): The finite-Dn assumption is essential: with Dp = Dn = ∞, both premises hold for X = 0 and Y = 1, but the real conclusion fails.

Encoding for `Breakdown.ModeWeights.le_of_ennreal_bounds` (2): The proof establishes Dp < ∞ before converting either extended-real mass to a real number.

Comparison for `Breakdown.ModeWeights.le_of_ennreal_bounds`: This is an explicit extended-real bookkeeping lemma for the cancellation in Lemma B.2. The paper works directly with the finite signed integral and has no separately numbered version of this conversion.

Clause 1 of `Breakdown.ModeWeights.le_of_ennreal_bounds`, lines 604-606: Finite negative mass and the two comparisons that can safely be combined. Paper: Signed-integral convention after (B.18), p. 55; Lemma B.2, p. 56 Source: [lean/CoerciveChallenge.lean:604-606](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L604-L606).

<a id="112"></a>

### 112. Combine the earlier density bounds

`Breakdown.ModeWeights.multiplierInequality_of_density`: This combines the class-weight multiplier theorem with a separately supplied lower bound for its density to obtain MultiplierInequality. It corresponds to adding (B.20) and (B.21), while preserving the earlier ball L² formulation.

**Source.** [lean/CoerciveChallenge.lean:632-695](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L632-L695). Theorem with a source proof body. **Paper.** Lemma B.2 and (B.21)-(B.22), p. 56

**Library.** Implementation source: [lean/Solution.lean:99-135](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Solution.lean#L99-L135).

Encoding for `Breakdown.ModeWeights.multiplierInequality_of_density` (1): The rest hypothesis is required for every compatible multiplier, so the multiplier obtained from the existence theorem can be used without a new choice.

Encoding for `Breakdown.ModeWeights.multiplierInequality_of_density` (2): Finiteness of the negative density is part of the rest hypothesis and is passed to le_of_ennreal_bounds.

Encoding for `Breakdown.ModeWeights.multiplierInequality_of_density` (3): Nonnegative box radii supply an actual parameter at which positivity of the uniform coefficients c and cμ can be read.

Comparison for `Breakdown.ModeWeights.multiplierInequality_of_density`: This is the earlier class-weight and ball L² assembly. The printed argument uses the piecewise multiplier and finite-row seminorm, while the same cancellation and scalar conversion are retained.

Clause 1 of `Breakdown.ModeWeights.multiplierInequality_of_density`, lines 632-646: Uniform parameterwise profile, forcing and admissibility hypotheses. Paper: Proposition B.1 and (B.20), p. 55 Source: [lean/CoerciveChallenge.lean:632-646](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L632-L646).

Clause 2 of `Breakdown.ModeWeights.multiplierInequality_of_density`, lines 647-666: Assumed finite negative mass and the additional density lower bound. Paper: (B.21), p. 56; lower bound supplied by Proposition B.8, p. 63 Source: [lean/CoerciveChallenge.lean:647-666](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L647-L666).

Clause 3 of `Breakdown.ModeWeights.multiplierInequality_of_density`, lines 667-669: Combined multiplier inequality and its norm constant. Paper: Lemma B.2 and (B.21)-(B.22), p. 56 Source: [lean/CoerciveChallenge.lean:667-669](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L667-L669).

<a id="113"></a>

### 113. One curl-multiplier piece

`Breakdown.EpsPiece`: This is one index p in the paper’s family Pλ: a one-sided set of modes, a frame rate, a nonnegative weight and auxiliary positive functions. The structure stores the data; admissibility supplies their analytic and sign conditions.

**Source.** [lean/CoerciveChallenge.lean:700-712](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L700-L712). Structure. **Paper.** Appendix B.2, weight data p. 53; (B.14)-(B.16), p. 54

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:586-598](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L586-L598).

Encoding for `Breakdown.EpsPiece` (1): modes is an arbitrary mathematical Set and can be infinite.

Encoding for `Breakdown.EpsPiece` (2): The raw structure does not exclude overlap with its negative; the positive one-sided frequency condition later enforces disjointness.

The set Np selects the modes on which the curl multiplier acts; the positive one-sided frequency condition is imposed by admissibility. Paper: Appendix B.2, weight data p. 53; (B.14)-(B.16), p. 54 Source: [lean/CoerciveChallenge.lean:701-701](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L701).

Field `Breakdown.EpsPiece.frame`: The scalar frame rotation rate νp for the current certificate parameter. Paper: Appendix B.2, weight data p. 53; (B.14)-(B.16), p. 54 Source: [lean/CoerciveChallenge.lean:702-702](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L702).

Field `Breakdown.EpsPiece.wt`: The curl multiplier weight λp. Paper: Appendix B.2, weight data p. 53; (B.14)-(B.16), p. 54 Source: [lean/CoerciveChallenge.lean:703-703](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L703).

Field `Breakdown.EpsPiece.share1`: Young share for transport and gradient-of-weight errors. Paper: Auxiliary functions for the unexpanded coefficients of (B.16), p. 54; data described in Appendix B.2, p. 53 Source: [lean/CoerciveChallenge.lean:704-704](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L704).

Field `Breakdown.EpsPiece.share2`: Young share for mode couplings through the reference velocity. Paper: Auxiliary functions for the unexpanded coefficients of (B.16), p. 54; data described in Appendix B.2, p. 53 Source: [lean/CoerciveChallenge.lean:705-705](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L705).

This is the balancing-length function for the total vorticity-gradient loss; admissibility requires positivity. Paper: Auxiliary functions for the unexpanded coefficients of (B.16), p. 54; data described in Appendix B.2, p. 53 Source: [lean/CoerciveChallenge.lean:706-706](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L706).

Field `Breakdown.EpsPiece.t0`: Young parameter for the total vorticity coupling. Paper: Auxiliary functions for the unexpanded coefficients of (B.16), p. 54; data described in Appendix B.2, p. 53 Source: [lean/CoerciveChallenge.lean:707-707](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L707).

Field `Breakdown.EpsPiece.t1`: Young parameter for harmonic gradient-of-profile couplings. Paper: Auxiliary functions for the unexpanded coefficients of (B.16), p. 54; data described in Appendix B.2, p. 53 Source: [lean/CoerciveChallenge.lean:708-708](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L708).

Field `Breakdown.EpsPiece.t2`: Young parameter for harmonic gradient-of-vorticity couplings. Paper: Auxiliary functions for the unexpanded coefficients of (B.16), p. 54; data described in Appendix B.2, p. 53 Source: [lean/CoerciveChallenge.lean:709-709](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L709).

Field `Breakdown.EpsPiece.t3`: Young parameter for harmonic vorticity couplings. Paper: Auxiliary functions for the unexpanded coefficients of (B.16), p. 54; data described in Appendix B.2, p. 53 Source: [lean/CoerciveChallenge.lean:710-710](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L710).

This scale balances inward and outward velocity-mode couplings; admissibility requires it to be positive. Paper: Auxiliary functions for the unexpanded coefficients of (B.16), p. 54; data described in Appendix B.2, p. 53 Source: [lean/CoerciveChallenge.lean:711-711](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L711).

Field `Breakdown.EpsPiece.speed`: Pointwise bound for the full reference transport velocity in this frame. Paper: Appendix B.2, weight data p. 53; (B.14)-(B.16), p. 54 Source: [lean/CoerciveChallenge.lean:712-712](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L712).

<a id="114"></a>

### 114. One velocity-multiplier piece

These are the proposed data for one velocity piece p: a mode set, rotation rate, weight μp, Young parameter ηp and auxiliary functions. Admissibility supplies the one-sided frequency and positivity conditions.

**Source.** [lean/CoerciveChallenge.lean:714-721](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L714-L721). Structure. **Paper.** Appendix B.2, weight data p. 53; (B.14)-(B.16), p. 54

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:600-607](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L600-L607).

Encoding for `Breakdown.MuPiece` (1): The mode set can be infinite even though the number of pieces is finite.

Encoding for `Breakdown.MuPiece` (2): Zero piece counts are allowed by Fin nM; all remaining certificate requirements still have to hold.

The set Np selects the modes on which the velocity multiplier acts; admissibility imposes its positive one-sided frequency condition. Paper: Appendix B.2, weight data p. 53; (B.14)-(B.16), p. 54 Source: [lean/CoerciveChallenge.lean:715-715](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L715).

Field `Breakdown.MuPiece.frame`: The scalar frame rotation rate νp for the current parameter. Paper: Appendix B.2, weight data p. 53; (B.14)-(B.16), p. 54 Source: [lean/CoerciveChallenge.lean:716-716](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L716).

Field `Breakdown.MuPiece.wt`: The velocity multiplier weight µp. Paper: Appendix B.2, weight data p. 53; (B.14)-(B.16), p. 54 Source: [lean/CoerciveChallenge.lean:717-717](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L717).

Field `Breakdown.MuPiece.share`: Young share for transport and gradient-of-weight losses. Paper: Auxiliary data for the unexpanded coefficients of (B.16), p. 54; data described in Appendix B.2, p. 53 Source: [lean/CoerciveChallenge.lean:718-718](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L718).

Field `Breakdown.MuPiece.t4`: Young parameter for reference-velocity mode couplings. Paper: Auxiliary data for the unexpanded coefficients of (B.16), p. 54; data described in Appendix B.2, p. 53 Source: [lean/CoerciveChallenge.lean:719-719](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L719).

The scalar ηp is the Young parameter for derivative couplings; admissibility requires ηp>0. Paper: Auxiliary data for the unexpanded coefficients of (B.16), p. 54; data described in Appendix B.2, p. 53 Source: [lean/CoerciveChallenge.lean:720-720](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L720).

Field `Breakdown.MuPiece.speed`: Bound for the full reference transport velocity in this rotating frame. Paper: Appendix B.2, weight data p. 53; (B.14)-(B.16), p. 54 Source: [lean/CoerciveChallenge.lean:721-721](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L721).

<a id="115"></a>

### 115. Bounds for the reference harmonics

`Breakdown.HarmonicBounds`: This stores the finite harmonic enclosure of Wʳ described just before (B.16). It separates four mode-amplitude bounds from the two bounds on the full vorticity and its derivative.

**Source.** [lean/CoerciveChallenge.lean:723-730](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L723-L730). Structure. **Paper.** Appendix B.2, bounds paragraph immediately before (B.16), p. 54

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:609-616](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L609-L616).

Encoding for `Breakdown.HarmonicBounds` (1): These fields are proposed bounds until the associated admissibility inequalities bind them to the actual reference field.

Encoding for `Breakdown.HarmonicBounds` (2): Mode arrays use componentwise norms; supGradVort bounds the operator norm of the real derivative map.

This is the finite set proposed to contain the reference-profile harmonics; admissibility requires zero, closure under negation and the stated mode expansion. Paper: Appendix B.2, bounds paragraph immediately before (B.16), p. 54 Source: [lean/CoerciveChallenge.lean:724-724](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L724).

Field `Breakdown.HarmonicBounds.ampW`: Majorant for the amplitude of each velocity mode. Paper: Appendix B.2, bounds paragraph immediately before (B.16), p. 54 Source: [lean/CoerciveChallenge.lean:725-725](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L725).

Field `Breakdown.HarmonicBounds.ampGradW`: Majorant for the Frobenius amplitude of each gradient mode. Paper: Appendix B.2, bounds paragraph immediately before (B.16), p. 54 Source: [lean/CoerciveChallenge.lean:726-726](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L726).

Field `Breakdown.HarmonicBounds.ampVort`: Majorant for the amplitude of each vorticity mode. Paper: Appendix B.2, bounds paragraph immediately before (B.16), p. 54 Source: [lean/CoerciveChallenge.lean:727-727](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L727).

Field `Breakdown.HarmonicBounds.ampGradVort`: Majorant for the Frobenius amplitude of each vorticity-gradient mode. Paper: Appendix B.2, bounds paragraph immediately before (B.16), p. 54 Source: [lean/CoerciveChallenge.lean:728-728](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L728).

Field `Breakdown.HarmonicBounds.supVort`: Pointwise majorant for the full vorticity over time and axial rotations. Paper: Appendix B.2, bounds paragraph immediately before (B.16), p. 54 Source: [lean/CoerciveChallenge.lean:729-729](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L729).

Field `Breakdown.HarmonicBounds.supGradVort`: Pointwise operator-norm majorant for the full vorticity derivative. Paper: Appendix B.2, bounds paragraph immediately before (B.16), p. 54 Source: [lean/CoerciveChallenge.lean:730-730](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L730).

<a id="116"></a>

### 116. Finite families of multiplier pieces

`Breakdown.PieceWeights`: This is the multiplier data format used in the paper: finitely many curl and velocity pieces together with the classwise conversion weights D and Z. The energy coefficient c remains abstract here and is set to 3/50 by the cell certificate.

**Source.** [lean/CoerciveChallenge.lean:732-739](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L732-L739). Structure. **Paper.** Appendix B.2, pp. 53–55; (B.14)–(B.19), pp. 54–55

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:618-625](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L618-L625).

Encoding for `Breakdown.PieceWeights` (1): The piece families are finite, while each piece’s mode set can be infinite.

Encoding for `Breakdown.PieceWeights` (2): The raw structure is data only; PieceWeights.IsAdmissible carries the conditions.

Field `Breakdown.PieceWeights.classOf`: Assign each direct frequency pair to the class of its D and Z weights. Paper: Appendix B.2, finite classes paragraph, p. 53 Source: [lean/CoerciveChallenge.lean:733-733](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L733).

Field `Breakdown.PieceWeights.convD`: Classwise D weight converting curl-gradient to Hessian energy. Paper: Appendix B.2, p. 53, and the conversion terms of (B.16), p. 54 Source: [lean/CoerciveChallenge.lean:734-734](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L734).

Field `Breakdown.PieceWeights.convZ`: Classwise Z weight converting curl to gradient energy. Paper: Appendix B.2, p. 53, and the conversion terms of (B.16), p. 54 Source: [lean/CoerciveChallenge.lean:735-735](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L735).

Field `Breakdown.PieceWeights.epsP`: The finite indexed family of curl-multiplier pieces Pλ. Paper: (B.14), p. 54 Source: [lean/CoerciveChallenge.lean:736-736](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L736).

Field `Breakdown.PieceWeights.muP`: The finite indexed family of velocity-multiplier pieces Pµ. Paper: (B.14), p. 54 Source: [lean/CoerciveChallenge.lean:737-737](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L737).

The energy fraction c is an unrestricted real value in the data; admissibility requires c>0, and the cell construction specializes it to 3/50. Paper: Proposition B.1 and (B.20), p. 55 Source: [lean/CoerciveChallenge.lean:738-738](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L738).

Field `Breakdown.PieceWeights.cμ`: Fraction of the frequency seminorm retained in the multiplier estimate. Paper: Proposition B.1 and (B.20), p. 55 Source: [lean/CoerciveChallenge.lean:739-739](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L739).

<a id="117"></a>

### 117. Signed membership of a mode piece

`Breakdown.PieceWeights.sgn`: This is sgnp from the paragraph before (B.14): it assigns opposite signs to a mode set and its negative, and zero outside their union. The one-sided positive-frequency condition ensures those two sets are disjoint for admissible data.

**Source.** [lean/CoerciveChallenge.lean:744-744](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L744). Def. **Paper.** Definition of sgnp immediately before (B.14), p. 54

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:630-630](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L630).

Encoding for `Breakdown.PieceWeights.sgn` (1): For an arbitrary overlapping set the positive branch wins, so oddness is not a property of the raw definition alone.

Encoding for `Breakdown.PieceWeights.sgn` (2): Membership in an infinite Set is a mathematical predicate and need not have a finite executable decision procedure.

The sign is +1 on Np, −1 on −Np outside Np, and zero elsewhere; admissibility makes Np and −Np disjoint. Paper: Definition of sgnp immediately before (B.14), p. 54 Source: [lean/CoerciveChallenge.lean:744-744](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L744).

<a id="118"></a>

### 118. Membership up to mode negation

`Breakdown.PieceWeights.inPiece`: This tests whether a mode belongs to Np or to its negative. The coefficients in (B.16) use it to decide which modes receive a piece’s frequency gain and local losses.

**Source.** [lean/CoerciveChallenge.lean:746-746](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L746). Def. **Paper.** (B.16) and the unexpanded coefficient formulas described below it, p. 54

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:632-632](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L632).

Encoding for `Breakdown.PieceWeights.inPiece` (1): It records support without the sign; the signed multiplier itself uses sgn.

Clause 1 of `Breakdown.PieceWeights.inPiece`, lines 746-746: This tests whether a mode belongs to Np or to its negative. Paper: (B.16) and the unexpanded coefficient formulas described below it, p. 54 Source: [lean/CoerciveChallenge.lean:746-746](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L746).

<a id="119"></a>

### 119. Couplings entering a mode piece

`Breakdown.PieceWeights.fwdSum`: This sums the reference-mode majorants whose frequency shift carries the current mode into Np. It makes explicit one of the neighbour-coupling sums described after (B.16).

**Source.** [lean/CoerciveChallenge.lean:749-750](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L749-L750). Def. **Paper.** (B.16) and the unexpanded coefficient formulas described below it, p. 54

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:635-636](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L635-L636).

Encoding for `Breakdown.PieceWeights.fwdSum` (1): The sum is over the finite reference harmonic list, even if Np is infinite.

Encoding for `Breakdown.PieceWeights.fwdSum` (2): The bounds are indexed by the shifting reference harmonic, not by the destination perturbation mode.

Clause 1 of `Breakdown.PieceWeights.fwdSum`, lines 749-750: This sums the reference-mode majorants whose frequency shift carries the current mode into Np. Paper: (B.16) and the unexpanded coefficient formulas described below it, p. 54 Source: [lean/CoerciveChallenge.lean:749-750](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L749-L750).

<a id="120"></a>

### 120. Couplings leaving a mode piece

`Breakdown.PieceWeights.backSum`: For a chosen mode, this sums reference-mode majorants when subtracting the reference harmonic leaves Np. The piece coefficients use it to allocate losses at modes inside the piece.

**Source.** [lean/CoerciveChallenge.lean:753-754](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L753-L754). Def. **Paper.** (B.16) and the unexpanded coefficient formulas described below it, p. 54

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:639-640](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L639-L640).

Encoding for `Breakdown.PieceWeights.backSum` (1): Whether the current mode is in Np is checked by the caller inward; backSum by itself does not impose membership.

Clause 1 of `Breakdown.PieceWeights.backSum`, lines 753-754: For a chosen mode, this sums reference-mode majorants when subtracting the reference harmonic leaves Np. Paper: (B.16) and the unexpanded coefficient formulas described below it, p. 54 Source: [lean/CoerciveChallenge.lean:753-754](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L753-L754).

<a id="121"></a>

### 121. Internal share of piece couplings

`Breakdown.PieceWeights.inward`: This selects the complement-coupling sum at the representative of ±ι that lies in Np, and returns zero when neither representative lies there. It is part of the coefficient allocation behind (B.16).

**Source.** [lean/CoerciveChallenge.lean:757-758](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L757-L758). Def. **Paper.** (B.16) and the unexpanded coefficient formulas described below it, p. 54

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:643-644](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L643-L644).

Encoding for `Breakdown.PieceWeights.inward` (1): The first membership branch has priority for a malformed overlapping set; one-sided admissibility eliminates that overlap.

Clause 1 of `Breakdown.PieceWeights.inward`, lines 757-758: This selects the complement-coupling sum at the representative of ±ι that lies in Np, and returns zero when neither representative lies there. Paper: (B.16) and the unexpanded coefficient formulas described below it, p. 54 Source: [lean/CoerciveChallenge.lean:757-758](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L757-L758).

<a id="122"></a>

### 122. External share of piece couplings

`Breakdown.PieceWeights.outward`: This adds the forward coupling sums from each of ±ι that lies outside Np. It charges reference-harmonic interactions to the external modes in the error terms of (B.16).

**Source.** [lean/CoerciveChallenge.lean:761-762](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L761-L762). Def. **Paper.** (B.16) and the unexpanded coefficient formulas described below it, p. 54

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:647-648](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L647-L648).

Encoding for `Breakdown.PieceWeights.outward` (1): The positive and negative representatives are tested separately, so both can contribute when neither lies in Np.

Clause 1 of `Breakdown.PieceWeights.outward`, lines 761-762: This adds the forward coupling sums from each of ±ι that lies outside Np. Paper: (B.16) and the unexpanded coefficient formulas described below it, p. 54 Source: [lean/CoerciveChallenge.lean:761-762](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L761-L762).

<a id="123"></a>

### 123. Total reference-gradient majorant

`Breakdown.PieceWeights.harmonicSum`: This adds the majorants for all listed gradient modes of the reference profile. The velocity-piece coefficient uses this total when dividing derivative couplings into inward and outward losses.

**Source.** [lean/CoerciveChallenge.lean:764-764](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L764). Def. **Paper.** (B.16) and the unexpanded coefficient formulas described below it, p. 54

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:650-650](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L650).

Encoding for `Breakdown.PieceWeights.harmonicSum` (1): The finite list includes the zero mode under admissibility, unlike ModeWeights.waves in the earlier mean/wave route.

Clause 1 of `Breakdown.PieceWeights.harmonicSum`, lines 764-764: This adds the majorants for all listed gradient modes of the reference profile. Paper: (B.16) and the unexpanded coefficient formulas described below it, p. 54 Source: [lean/CoerciveChallenge.lean:764-764](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L764).

<a id="124"></a>

### 124. Frequency of a multiplier piece

`Breakdown.PieceWeights.frameFreq`: This is Ωp in (B.15) written for the direct frequency pair (n,k). Substituting n = 2ι₂ − ι₁, k = κι₁, P = S(α) and a = νp(α) gives the paper’s expression.

**Source.** [lean/CoerciveChallenge.lean:766-766](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L766). Def. **Paper.** (B.15) and the frequency seminorm immediately below it, p. 54

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:652-652](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L652).

Encoding for `Breakdown.PieceWeights.frameFreq` (1): The frame rate is a real scalar for a fixed piece and parameter; it has no spatial argument.

Encoding for `Breakdown.PieceWeights.frameFreq` (2): P > 0 is required by admissibility, although the raw expression is total at P = 0.

Clause 1 of `Breakdown.PieceWeights.frameFreq`, lines 766-766: This is Ωp in (B.15) written for the direct frequency pair (n,k). Paper: (B.15) and the frequency seminorm immediately below it, p. 54 Source: [lean/CoerciveChallenge.lean:766-766](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L766).

<a id="125"></a>

### 125. Derivative size of a piece weight

`Breakdown.PieceWeights.wtGrad`: This is the derivative norm of a scalar piece weight. It enters the gradient budget in (B.19) and the transport losses described below (B.16).

**Source.** [lean/CoerciveChallenge.lean:771-771](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L771). Def. **Paper.** (B.16), p. 54, and (B.19), p. 55

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:657-657](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L657).

Encoding for `Breakdown.PieceWeights.wtGrad` (1): Admissible piece weights are Lipschitz, giving ordinary derivatives almost everywhere.

Encoding for `Breakdown.PieceWeights.wtGrad` (2): The total fderiv value at spline knots is not a smoothness assertion and does not replace the Lipschitz hypothesis.

Clause 1 of `Breakdown.PieceWeights.wtGrad`, lines 771-771: This is the derivative norm of a scalar piece weight. Paper: (B.16), p. 54, and (B.19), p. 55 Source: [lean/CoerciveChallenge.lean:771-771](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L771).

<a id="126"></a>

### 126. Assigned curl-gradient energy

`Breakdown.PieceWeights.shareHat`: This adds the shares of curl-gradient energy used by every active curl piece and its couplings. The remainder 1 − shareHat − D is the coefficient I′₂ in (B.16), and admissibility requires it to be nonnegative.

**Source.** [lean/CoerciveChallenge.lean:774-778](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L774-L778). Def. **Paper.** (B.16) and the unexpanded coefficient formulas described below it, p. 54

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:660-664](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L660-L664).

Encoding for `Breakdown.PieceWeights.shareHat` (1): The share1 indicator sees both a nonzero weight and a nonzero derivative; the outward share sees a positive weight.

Encoding for `Breakdown.PieceWeights.shareHat` (2): The denominator scale is strictly positive in the piece admissibility conditions.

Clause 1 of `Breakdown.PieceWeights.shareHat`, lines 774-778: This adds the shares of curl-gradient energy used by every active curl piece and its couplings. Paper: (B.16) and the unexpanded coefficient formulas described below it, p. 54 Source: [lean/CoerciveChallenge.lean:774-778](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L774-L778).

<a id="127"></a>

### 127. Curl-mode coefficient before Z

`Breakdown.PieceWeights.coefA`: This gives I′₁ + Z in (B.16): the base 1/4 and curl-piece frequency gains after transport, rotation and reference-harmonic losses. The full expression fills in coefficients that the paper deliberately does not print.

**Source.** [lean/CoerciveChallenge.lean:781-792](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L781-L792). Def. **Paper.** (B.16) and the unexpanded coefficient formulas described below it, p. 54

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:667-678](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L667-L678).

Encoding for `Breakdown.PieceWeights.coefA` (1): The formula is summed over all pieces, so overlapping pieces contribute additively even though each individual one-sided set is disjoint from its negative.

Encoding for `Breakdown.PieceWeights.coefA` (2): Strict positivity of share1, share2, len, t0, t1, t2, t3 and scale comes from admissibility.

Clause 1 of `Breakdown.PieceWeights.coefA`, lines 781-792: This gives I′₁ + Z in (B.16): the base 1/4 and curl-piece frequency gains after transport, rotation and reference-harmonic losses. Paper: (B.16) and the unexpanded coefficient formulas described below it, p. 54 Source: [lean/CoerciveChallenge.lean:781-792](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L781-L792).

<a id="128"></a>

### 128. Gradient-mode coefficient

`Breakdown.PieceWeights.coefAA`: This is I₁ in (B.16), starting with Z − |∇²D|op − cw and subtracting the curl- and velocity-piece losses assigned to the gradient amplitude. The coefficient is allowed to be negative before the region and cell lower bounds are imposed.

**Source.** [lean/CoerciveChallenge.lean:795-801](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L795-L801). Def. **Paper.** (B.16) and the unexpanded coefficient formulas described below it, p. 54

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:681-687](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L681-L687).

Encoding for `Breakdown.PieceWeights.coefAA` (1): The Hessian norm is the operator norm of the scalar conversion weight, not the component norm of the perturbation Hessian.

Clause 1 of `Breakdown.PieceWeights.coefAA`, lines 795-801: This is I₁ in (B.16), starting with Z − |∇²D|op − cw and subtracting the curl- and velocity-piece losses assigned to the gradient amplitude. Paper: (B.16) and the unexpanded coefficient formulas described below it, p. 54 Source: [lean/CoerciveChallenge.lean:795-801](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L795-L801).

<a id="129"></a>

### 129. Velocity-mode coefficient

`Breakdown.PieceWeights.coefB`: This is I₀ in (B.16), combining the Z-Hessian loss with the retained velocity-frequency gains and all errors assigned to the velocity amplitude. The eta terms account for derivative couplings that were mixed terms in the earlier class-weight route.

**Source.** [lean/CoerciveChallenge.lean:804-815](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L804-L815). Def. **Paper.** (B.16) and the unexpanded coefficient formulas described below it, p. 54

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:690-701](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L690-L701).

Encoding for `Breakdown.PieceWeights.coefB` (1): Each eta is strictly positive under admissibility.

Encoding for `Breakdown.PieceWeights.coefB` (2): No sign is asserted by the definition; lower bounds for this coefficient belong to the later analytic and cell conditions.

Clause 1 of `Breakdown.PieceWeights.coefB`, lines 804-815: This is I₀ in (B.16), combining the Z-Hessian loss with the retained velocity-frequency gains and all errors assigned to the velocity amplitude. Paper: (B.16) and the unexpanded coefficient formulas described below it, p. 54 Source: [lean/CoerciveChallenge.lean:804-815](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L804-L815).

<a id="130"></a>

### 130. Five-term quadratic form for a mode

`Breakdown.PieceWeights.modeDensity`: This assembles exactly the five squared-amplitude slots of (B.16), with c left abstract in place of the paper’s 3/50. The curl coefficient is coefA − Z, while coefAA and coefB are the gradient and velocity coefficients.

**Source.** [lean/CoerciveChallenge.lean:817-820](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L817-L820). Def. **Paper.** (B.16) and the unexpanded coefficient formulas described below it, p. 54

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:703-706](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L703-L706).

Encoding for `Breakdown.PieceWeights.modeDensity` (1): The amplitude order is Hessian, gradient of curl, gradient, curl and velocity.

Encoding for `Breakdown.PieceWeights.modeDensity` (2): The conversion-weight conditions guarantee nonnegativity of I′₂, while the other coefficients still require the later lower-bound analysis.

Clause 1 of `Breakdown.PieceWeights.modeDensity`, lines 818-818: Hessian coefficient D − c and curl-gradient coefficient 1 − shareHat − D. Paper: (B.16), p. 54 Source: [lean/CoerciveChallenge.lean:818-818](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L818).

Clause 2 of `Breakdown.PieceWeights.modeDensity`, lines 819-820: Curl, gradient and velocity slots of the five-term form. Paper: (B.16), p. 54 Source: [lean/CoerciveChallenge.lean:819-820](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L819-L820).

<a id="131"></a>

### 131. Quadratic form on a Fourier mode

`Breakdown.PieceWeights.modeTerm`: This evaluates the five-term form Iι using the amplitudes of the Fourier modes of v and its supplied first and second derivatives. The separate stretching expression J is added only in densityPos and densityNeg.

**Source.** [lean/CoerciveChallenge.lean:822-827](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L822-L827). Def. **Paper.** (B.16) and the unexpanded coefficient formulas described below it, p. 54

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:708-713](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L708-L713).

Encoding for `Breakdown.PieceWeights.modeTerm` (1): The square roots of finite sums of squared complex moduli give nonnegative amplitudes.

Encoding for `Breakdown.PieceWeights.modeTerm` (2): IsPerturbation, rather than this substitution, states that G and H are the weak derivatives of v.

Clause 1 of `Breakdown.PieceWeights.modeTerm`, lines 822-827: This evaluates the five-term form Iι using the amplitudes of the Fourier modes of v and its supplied first and second derivatives. Paper: (B.16) and the unexpanded coefficient formulas described below it, p. 54 Source: [lean/CoerciveChallenge.lean:822-827](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L822-L827).

<a id="132"></a>

### 132. Frequency seminorm squared

`Breakdown.PieceWeights.seminormSq`: This is the nonnegative frequency seminorm defined after (B.15), summed over every velocity piece and every Fourier mode. The finite piece sum is outside the infinite mode sum, matching the paper’s piecewise weighting.

**Source.** [lean/CoerciveChallenge.lean:829-832](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L829-L832). Def. **Paper.** (B.15) and the frequency seminorm immediately below it, p. 54

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:715-718](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L715-L718).

Encoding for `Breakdown.PieceWeights.seminormSq` (1): ENNReal.ofReal clips negative raw inputs, so the condition that each µp is nonnegative is part of the intended interpretation.

Encoding for `Breakdown.PieceWeights.seminormSq` (2): The extended-real value may be infinity; piece_multiplier_density proves it finite for admissible perturbations before real conversion.

Clause 1 of `Breakdown.PieceWeights.seminormSq`, lines 829-832: This is the nonnegative frequency seminorm defined after (B.15), summed over every velocity piece and every Fourier mode. Paper: (B.15) and the frequency seminorm immediately below it, p. 54 Source: [lean/CoerciveChallenge.lean:829-832](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L829-L832).

<a id="133"></a>

### 133. Multiplier defined by test pairings

`Breakdown.PieceWeights.IsMultiplierField`: This is the field Mv of (B.14), characterized by its action on smooth periodic divergence-free test fields. Lean separately records its finite L² norm and orthogonality to gradients, expressing membership of Hdiv.

**Source.** [lean/CoerciveChallenge.lean:834-847](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L834-L847). Def. **Paper.** (B.14), p. 54

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:720-733](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L720-L733).

Encoding for `Breakdown.PieceWeights.IsMultiplierField` (1): The final sum over all modes is a real tsum; its interpretation needs the summability supplied for admissible callers.

Encoding for `Breakdown.PieceWeights.IsMultiplierField` (2): The summability witness is pieceIntegral_summable in Breakdown/Cert/CoercivePieceField.lean:830-853.

Encoding for `Breakdown.PieceWeights.IsMultiplierField` (3): There is one uniform spatial support radius for each test field, although the field is periodic rather than compactly supported in time.

Clause 1 of `Breakdown.PieceWeights.IsMultiplierField`, lines 836-839: Measurability, time periodicity, finite L² mass and divergence-free testing. Paper: (B.14), p. 54 Source: [lean/CoerciveChallenge.lean:836-839](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L836-L839).

Clause 2 of `Breakdown.PieceWeights.IsMultiplierField`, lines 840-842: Test-field pairing with the negative Laplacian contribution. Paper: (B.14), p. 54 Source: [lean/CoerciveChallenge.lean:840-842](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L840-L842).

Clause 3 of `Breakdown.PieceWeights.IsMultiplierField`, lines 843-847: Signed curl and velocity piece contributions, summed over Fourier modes. Paper: (B.14), p. 54 Source: [lean/CoerciveChallenge.lean:843-847](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L843-L847).

<a id="134"></a>

### 134. Positive mass of the mode density

`Breakdown.PieceWeights.densityPos`: This is the pointwise sum whose integral is I⁺ after (B.18). It adds the positive part of each Iι and the positive part of J, retaining the value infinity when needed.

**Source.** [lean/CoerciveChallenge.lean:849-852](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L849-L852). Def. **Paper.** (B.18) and the positive/negative integral convention, p. 55

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:735-738](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L735-L738).

Encoding for `Breakdown.PieceWeights.densityPos` (1): Positive parts are taken term by term before summation.

Encoding for `Breakdown.PieceWeights.densityPos` (2): This definition does not form a potentially undefined difference of two infinite signed sums.

Clause 1 of `Breakdown.PieceWeights.densityPos`, lines 849-852: This is the pointwise sum whose integral is I⁺ after (B.18). Paper: (B.18) and the positive/negative integral convention, p. 55 Source: [lean/CoerciveChallenge.lean:849-852](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L849-L852).

<a id="135"></a>

### 135. Negative mass of the mode density

`Breakdown.PieceWeights.densityNeg`: This is the pointwise sum whose integral is I⁻ after (B.18). Finiteness of its integral is the analytic condition that makes the signed lower bound and the cancellation in Lemma B.2 valid.

**Source.** [lean/CoerciveChallenge.lean:854-858](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L854-L858). Def. **Paper.** (B.18) and the positive/negative integral convention, p. 55

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:740-744](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L740-L744).

Encoding for `Breakdown.PieceWeights.densityNeg` (1): The value infinity remains visible in the nonnegative extended-real integral.

Encoding for `Breakdown.PieceWeights.densityNeg` (2): It is not sufficient to write the formal difference of the positive and negative densities without a finite-negative-mass proof.

Clause 1 of `Breakdown.PieceWeights.densityNeg`, lines 854-858: This is the pointwise sum whose integral is I⁻ after (B.18). Paper: (B.18) and the positive/negative integral convention, p. 55 Source: [lean/CoerciveChallenge.lean:854-858](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L854-L858).

<a id="136"></a>

### 136. Multiplier pairing after energy costs

`Breakdown.PieceWeights.multiplierGap`: This is the left side of (B.20), using the piecewise frequency seminorm and leaving c abstract. It separates the fixed energy costs and the forcing-field pairings from the quantity available to dominate the density.

**Source.** [lean/CoerciveChallenge.lean:860-864](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L860-L864). Def. **Paper.** Proposition B.1 and (B.20), p. 55

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:746-750](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L746-L750).

Encoding for `Breakdown.PieceWeights.multiplierGap` (1): The conversion of the frequency seminorm to a real number is justified by the finiteness conclusion of the multiplier theorem.

Encoding for `Breakdown.PieceWeights.multiplierGap` (2): The same multiplier is used in every pairing, which matters when the forcing-field terms cancel.

Clause 1 of `Breakdown.PieceWeights.multiplierGap`, lines 860-864: This is the left side of (B.20), using the piecewise frequency seminorm and leaving c abstract. Paper: Proposition B.1 and (B.20), p. 55 Source: [lean/CoerciveChallenge.lean:860-864](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L860-L864).

<a id="137"></a>

### 137. Admissible piecewise multiplier weights

`Breakdown.PieceWeights.IsAdmissible`: This spells out the admissibility conditions described before Proposition B.1, including the full profile enclosures and all three budgets of (B.19). The regularity and decay properties of the encoded weights are explicit analytic hypotheses; the reflection symmetry (B.17) and later cell bounds are separate conditions.

**Source.** [lean/CoerciveChallenge.lean:866-934](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L866-L934). Structure. **Paper.** Appendix B.2, pp. 53–55; (B.14)–(B.19), pp. 54–55

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/CoerciveStatement.lean:752-820](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L752-L820).

Encoding for `Breakdown.PieceWeights.IsAdmissible` (1): The frequency lower bound is chosen for each piece before quantifying over every mode in that piece; a merely pointwise positive frequency would be weaker.

Encoding for `Breakdown.PieceWeights.IsAdmissible` (2): Because the frame frequency changes sign under mode negation, the one-sided conditions imply that Np and −Np are disjoint and exclude the zero mode.

Encoding for `Breakdown.PieceWeights.IsAdmissible` (3): An empty piece set satisfies the one-sided condition vacuously; this removes that multiplier contribution but does not furnish a certificate.

Encoding for `Breakdown.PieceWeights.IsAdmissible` (4): These conditions concern real functions and infinite mode sets. Their presence in a finite-data encoding does not make them finite arithmetic checks without a reduction theorem.

Encoding for `Breakdown.PieceWeights.IsAdmissible` (5): The positive denominator conditions are global for every piece and point; no reciprocal here relies on a zero-denominator convention.

Field `Breakdown.PieceWeights.IsAdmissible.finite_classes`: The collection of D and Z weight classes is finite. Paper: Appendix B.2, weight data and auxiliary functions, p. 53 Source: [lean/CoerciveChallenge.lean:867-867](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L867).

Field `Breakdown.PieceWeights.IsAdmissible.c_pos`: The weighted-energy share c is strictly positive. Paper: Proposition B.1 and (B.20), p. 55; c is abstract here and equals 3/50 in the cell construction Source: [lean/CoerciveChallenge.lean:868-868](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L868).

Field `Breakdown.PieceWeights.IsAdmissible.c_lt_one`: The weighted-energy share c is less than one. Paper: Proposition B.1 and (B.20), p. 55; c is abstract here and equals 3/50 in the cell construction Source: [lean/CoerciveChallenge.lean:869-869](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L869).

Field `Breakdown.PieceWeights.IsAdmissible.cμ_pos`: The retained frequency share cμ is strictly positive. Paper: Proposition B.1 and (B.20), p. 55; c is abstract here and equals 3/50 in the cell construction Source: [lean/CoerciveChallenge.lean:870-870](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L870).

Field `Breakdown.PieceWeights.IsAdmissible.cμ_lt_one`: The retained frequency share cμ is less than one. Paper: Proposition B.1 and (B.20), p. 55; c is abstract here and equals 3/50 in the cell construction Source: [lean/CoerciveChallenge.lean:871-871](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L871).

Field `Breakdown.PieceWeights.IsAdmissible.period_pos`: The similarity period is strictly positive. Paper: §7.1 and (7.1), p. 30 Source: [lean/CoerciveChallenge.lean:872-872](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L872).

Field `Breakdown.PieceWeights.IsAdmissible.weight_pos`: The lower bound w₀ for the energy weight is positive. Paper: (7.14) and its weight hypotheses, p. 32 Source: [lean/CoerciveChallenge.lean:873-873](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L873).

Field `Breakdown.PieceWeights.IsAdmissible.weight_lower`: The energy weight is at least w₀ everywhere. Paper: (7.14) and its weight hypotheses, p. 32 Source: [lean/CoerciveChallenge.lean:874-874](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L874).

Field `Breakdown.PieceWeights.IsAdmissible.weight_measurable`: The energy weight is measurable. Paper: (7.14) and its weight hypotheses, p. 32 Source: [lean/CoerciveChallenge.lean:875-875](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L875).

Field `Breakdown.PieceWeights.IsAdmissible.weight_axi`: The energy weight is invariant under axial rotations. Paper: Axisymmetric coefficient form required in Appendix B.2, pp. 53-54 Source: [lean/CoerciveChallenge.lean:876-876](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L876).

Field `Breakdown.PieceWeights.IsAdmissible.harmonics_neg`: The reference harmonic list is closed under negation. Paper: Reference-profile bounds immediately before (B.16), p. 54; admissibility paragraph, p. 55 Source: [lean/CoerciveChallenge.lean:877-877](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L877).

Field `Breakdown.PieceWeights.IsAdmissible.harmonics_zero`: The reference harmonic list contains the zero mode. Paper: Reference-profile bounds immediately before (B.16), p. 54; admissibility paragraph, p. 55 Source: [lean/CoerciveChallenge.lean:878-878](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L878).

Field `Breakdown.PieceWeights.IsAdmissible.harmonics_span`: The listed real Fourier modes reconstruct the reference profile at every point and time. Paper: Reference-profile bounds immediately before (B.16), p. 54; admissibility paragraph, p. 55 Source: [lean/CoerciveChallenge.lean:879-879](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L879).

Field `Breakdown.PieceWeights.IsAdmissible.ampW_ge`: Each listed velocity-mode amplitude lies below its majorant. Paper: Reference-profile bounds immediately before (B.16), p. 54; admissibility paragraph, p. 55 Source: [lean/CoerciveChallenge.lean:880-880](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L880).

Field `Breakdown.PieceWeights.IsAdmissible.ampGradW_ge`: Each listed gradient-mode amplitude lies below its majorant. Paper: Reference-profile bounds immediately before (B.16), p. 54; admissibility paragraph, p. 55 Source: [lean/CoerciveChallenge.lean:881-882](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L881-L882).

Field `Breakdown.PieceWeights.IsAdmissible.ampVort_ge`: Each listed vorticity-mode amplitude lies below its majorant. Paper: Reference-profile bounds immediately before (B.16), p. 54; admissibility paragraph, p. 55 Source: [lean/CoerciveChallenge.lean:883-884](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L883-L884).

Field `Breakdown.PieceWeights.IsAdmissible.ampGradVort_ge`: Each listed vorticity-gradient amplitude lies below its majorant. Paper: Reference-profile bounds immediately before (B.16), p. 54; admissibility paragraph, p. 55 Source: [lean/CoerciveChallenge.lean:885-886](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L885-L886).

Field `Breakdown.PieceWeights.IsAdmissible.supVort_ge`: The full vorticity is bounded uniformly over all times and axial rotations. Paper: Reference-profile bounds immediately before (B.16), p. 54; admissibility paragraph, p. 55 Source: [lean/CoerciveChallenge.lean:887-887](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L887).

Field `Breakdown.PieceWeights.IsAdmissible.supGradVort_ge`: The full vorticity derivative is bounded uniformly over all times and rotations. Paper: Reference-profile bounds immediately before (B.16), p. 54; admissibility paragraph, p. 55 Source: [lean/CoerciveChallenge.lean:888-889](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L888-L889).

Field `Breakdown.PieceWeights.IsAdmissible.epsSpeed_ge`: Each curl piece bounds the full transport velocity in its rotating frame. Paper: Transport-bound data in Appendix B.2, p. 53; admissibility paragraph, p. 55 Source: [lean/CoerciveChallenge.lean:890-892](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L890-L892).

Field `Breakdown.PieceWeights.IsAdmissible.muSpeed_ge`: Each velocity piece bounds the full transport velocity in its rotating frame. Paper: Transport-bound data in Appendix B.2, p. 53; admissibility paragraph, p. 55 Source: [lean/CoerciveChallenge.lean:893-895](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L893-L895).

Field `Breakdown.PieceWeights.IsAdmissible.eps_oneSided`: Each curl piece has a strictly positive frequency lower bound uniform over its modes. Paper: (B.15), p. 54; positive frequency lower bounds in the admissibility paragraph, p. 55 Source: [lean/CoerciveChallenge.lean:896-896](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L896).

Field `Breakdown.PieceWeights.IsAdmissible.mu_oneSided`: Each velocity piece has a strictly positive frequency lower bound uniform over its modes. Paper: (B.15), p. 54; positive frequency lower bounds in the admissibility paragraph, p. 55 Source: [lean/CoerciveChallenge.lean:897-897](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L897).

Field `Breakdown.PieceWeights.IsAdmissible.mu_ratio`: The squared total velocity weight is controlled by the weighted frame-frequency sum. Paper: (B.19) and the admissibility paragraph, p. 55 Source: [lean/CoerciveChallenge.lean:898-899](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L898-L899).

Field `Breakdown.PieceWeights.IsAdmissible.ratio_nonneg`: The coefficient nµ in the frequency-weight inequality is nonnegative. Paper: (B.19) and the admissibility paragraph, p. 55 Source: [lean/CoerciveChallenge.lean:900-900](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L900).

Field `Breakdown.PieceWeights.IsAdmissible.eps_wt_nonneg`: Every curl-piece weight λp is pointwise nonnegative. Paper: Appendix B.2, weight data and auxiliary functions, p. 53 Source: [lean/CoerciveChallenge.lean:901-901](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L901).

Field `Breakdown.PieceWeights.IsAdmissible.mu_wt_nonneg`: Every velocity-piece weight µp is pointwise nonnegative. Paper: Appendix B.2, weight data and auxiliary functions, p. 53 Source: [lean/CoerciveChallenge.lean:902-902](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L902).

Field `Breakdown.PieceWeights.IsAdmissible.eps_increment`: Every curl-piece weight is globally Lipschitz. Paper: Appendix B.2, pp. 53 and 55; analytic regularity/decay made explicit in Lean Source: [lean/CoerciveChallenge.lean:903-903](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L903).

Field `Breakdown.PieceWeights.IsAdmissible.mu_increment`: Every velocity-piece weight is globally Lipschitz. Paper: Appendix B.2, pp. 53 and 55; analytic regularity/decay made explicit in Lean Source: [lean/CoerciveChallenge.lean:904-904](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L904).

Field `Breakdown.PieceWeights.IsAdmissible.eps_axi`: Every curl-piece weight is axisymmetric. Paper: Appendix B.2, weight data and auxiliary functions, p. 53 Source: [lean/CoerciveChallenge.lean:905-905](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L905).

Field `Breakdown.PieceWeights.IsAdmissible.mu_axi`: Every velocity-piece weight is axisymmetric. Paper: Appendix B.2, weight data and auxiliary functions, p. 53 Source: [lean/CoerciveChallenge.lean:906-906](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L906).

Field `Breakdown.PieceWeights.IsAdmissible.eps_sum_le`: The sum of all curl-piece weights is at most nλ at each point. Paper: (B.19) and the admissibility paragraph, p. 55 Source: [lean/CoerciveChallenge.lean:907-907](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L907).

Field `Breakdown.PieceWeights.IsAdmissible.eps_grad_sum_le`: The sum of all curl-weight derivative norms is at most n∇λ. Paper: (B.19) and the admissibility paragraph, p. 55 Source: [lean/CoerciveChallenge.lean:908-908](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L908).

Field `Breakdown.PieceWeights.IsAdmissible.eps_decay`: All curl weights obey one uniform inverse-radius bound at infinity. Paper: Appendix B.2, pp. 53 and 55; analytic regularity/decay made explicit in Lean Source: [lean/CoerciveChallenge.lean:909-909](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L909).

Field `Breakdown.PieceWeights.IsAdmissible.mu_decay`: All velocity weights and their derivatives obey the required uniform decay bounds. Paper: Appendix B.2, pp. 53 and 55; analytic regularity/decay made explicit in Lean Source: [lean/CoerciveChallenge.lean:910-911](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L910-L911).

Field `Breakdown.PieceWeights.IsAdmissible.eps_free_pos`: Every curl-piece Young share, length, coupling parameter and scale is strictly positive. Paper: Appendix B.2, weight data and auxiliary functions, p. 53 Source: [lean/CoerciveChallenge.lean:912-914](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L912-L914).

Field `Breakdown.PieceWeights.IsAdmissible.mu_free_pos`: Every velocity-piece share and coupling parameter is strictly positive. Paper: Appendix B.2, weight data and auxiliary functions, p. 53 Source: [lean/CoerciveChallenge.lean:915-915](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L915).

Field `Breakdown.PieceWeights.IsAdmissible.mu_eta_pos`: Every velocity-piece scalar eta is strictly positive. Paper: Appendix B.2, weight data and auxiliary functions, p. 53 Source: [lean/CoerciveChallenge.lean:916-916](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L916).

Field `Breakdown.PieceWeights.IsAdmissible.eps_free_measurable`: All curl-piece auxiliary functions are measurable. Paper: Appendix B.2, pp. 53 and 55; analytic regularity/decay made explicit in Lean Source: [lean/CoerciveChallenge.lean:917-919](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L917-L919).

Field `Breakdown.PieceWeights.IsAdmissible.mu_free_measurable`: All velocity-piece auxiliary functions are measurable. Paper: Appendix B.2, pp. 53 and 55; analytic regularity/decay made explicit in Lean Source: [lean/CoerciveChallenge.lean:920-920](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L920).

Field `Breakdown.PieceWeights.IsAdmissible.eps_free_axi`: All curl-piece auxiliary functions are invariant under axial rotations. Paper: Appendix B.2, weight data and auxiliary functions, p. 53 Source: [lean/CoerciveChallenge.lean:921-923](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L921-L923).

Field `Breakdown.PieceWeights.IsAdmissible.mu_free_axi`: All velocity-piece auxiliary functions are invariant under axial rotations. Paper: Appendix B.2, weight data and auxiliary functions, p. 53 Source: [lean/CoerciveChallenge.lean:924-924](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L924).

Field `Breakdown.PieceWeights.IsAdmissible.convD_even`: Opposite modes have the same D conversion weight. Paper: Appendix B.2, p. 53, and the conversion terms of (B.16), p. 54 Source: [lean/CoerciveChallenge.lean:925-925](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L925).

Field `Breakdown.PieceWeights.IsAdmissible.convZ_even`: Opposite modes have the same Z conversion weight. Paper: Appendix B.2, p. 53, and the conversion terms of (B.16), p. 54 Source: [lean/CoerciveChallenge.lean:926-926](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L926).

Field `Breakdown.PieceWeights.IsAdmissible.convD_smooth`: Every D conversion weight is C². Paper: Appendix B.2, p. 53, and the conversion terms of (B.16), p. 54 Source: [lean/CoerciveChallenge.lean:927-927](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L927).

Field `Breakdown.PieceWeights.IsAdmissible.convZ_smooth`: Every Z conversion weight is C². Paper: Appendix B.2, p. 53, and the conversion terms of (B.16), p. 54 Source: [lean/CoerciveChallenge.lean:928-928](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L928).

Field `Breakdown.PieceWeights.IsAdmissible.convD_nonneg`: Every D conversion weight is nonnegative. Paper: Appendix B.2, p. 53, and the conversion terms of (B.16), p. 54 Source: [lean/CoerciveChallenge.lean:929-929](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L929).

Field `Breakdown.PieceWeights.IsAdmissible.convD_axi`: Every D conversion weight is axisymmetric. Paper: Appendix B.2, p. 53, and the conversion terms of (B.16), p. 54 Source: [lean/CoerciveChallenge.lean:930-930](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L930).

Field `Breakdown.PieceWeights.IsAdmissible.convZ_axi`: Every Z conversion weight is axisymmetric. Paper: Appendix B.2, p. 53, and the conversion terms of (B.16), p. 54 Source: [lean/CoerciveChallenge.lean:931-931](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L931).

Field `Breakdown.PieceWeights.IsAdmissible.convD_decay`: D and its first two derivatives have uniform radius-weighted bounds. Paper: Appendix B.2, pp. 53 and 55; analytic regularity/decay made explicit in Lean Source: [lean/CoerciveChallenge.lean:932-932](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L932).

Field `Breakdown.PieceWeights.IsAdmissible.convZ_decay`: Z and its first two derivatives have uniform bounds with powers of 1 + |y|. Paper: Appendix B.2, pp. 53 and 55; analytic regularity/decay made explicit in Lean Source: [lean/CoerciveChallenge.lean:933-933](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L933).

Field `Breakdown.PieceWeights.IsAdmissible.conv_le`: The coefficient I′₂ = 1 − shareHat − D is nonnegative for every mode and point. Paper: Nonnegativity of I′₂ from (B.16), p. 54, required in the admissibility paragraph, p. 55 Source: [lean/CoerciveChallenge.lean:934-934](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L934).

<a id="138"></a>

### 138. Multiplier bound for piece weights

`Breakdown.PieceWeights.piece_multiplier_density`: This is the strong C²-reference-profile version of Proposition B.1 for the printed piecewise multiplier data. It provides the multiplier, finite frequency energy, the stated norm bound and an extended-real form of (B.20).

**Source.** [lean/CoerciveChallenge.lean:936-959](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L936-L959). Readable theorem stub. **Paper.** Proposition B.1 and (B.20), p. 55

**Library.** Implementation source: [lean/Solution.lean:144-167](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Solution.lean#L144-L167).

Encoding for `Breakdown.PieceWeights.piece_multiplier_density` (1): The file contains a statement stub here; Solution.lean re-exports a proved implementation.

Encoding for `Breakdown.PieceWeights.piece_multiplier_density` (2): The active certificate has a weak second derivative and uses the extension in ExtendedCoerciveChallenge rather than this C² version alone.

Encoding for `Breakdown.PieceWeights.piece_multiplier_density` (3): Finite I⁻ is not assumed here; the conclusion encodes the signed bound without first subtracting the two extended-real masses.

Comparison for `Breakdown.PieceWeights.piece_multiplier_density`: The five-term density and piece multiplier correspond to Proposition B.1, but this export requires a C² reference field and leaves c arbitrary. The printed certificate permits a C¹ reference field with a weak Hessian and specializes c to 3/50; its active counterpart is the extended weak-piece result.

Clause 1 of `Breakdown.PieceWeights.piece_multiplier_density`, lines 936-945: Admissible pieces, a C² reference field and L² forcing fields. Paper: Proposition B.1 and (B.20), p. 55 Source: [lean/CoerciveChallenge.lean:936-945](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L936-L945).

Clause 2 of `Breakdown.PieceWeights.piece_multiplier_density`, lines 946-952: Perturbation scope, existence of M and finite frequency energy. Paper: Proposition B.1 and (B.20), p. 55 Source: [lean/CoerciveChallenge.lean:946-952](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L946-L952).

Clause 3 of `Breakdown.PieceWeights.piece_multiplier_density`, lines 953-954: The multiplier norm bound with c kept abstract. Paper: Proposition B.1 and (B.20), p. 55 Source: [lean/CoerciveChallenge.lean:953-954](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L953-L954).

Clause 4 of `Breakdown.PieceWeights.piece_multiplier_density`, lines 955-958: Cross-added positive and negative density comparison. Paper: (B.20) and the signed-integral convention, p. 55 Source: [lean/CoerciveChallenge.lean:955-958](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L955-L958).

<a id="139"></a>

### 139. Assemble the piecewise estimate

`Breakdown.PieceWeights.multiplierInequality_of_pieceDensity`: This adds the piecewise multiplier bound to a supplied remainder-density bound and returns the abstract MultiplierInequality. It implements the cancellation of (B.20) with (B.21), while its target still uses the earlier ball L² certificate.

**Source.** [lean/CoerciveChallenge.lean:961-1021](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L961-L1021). Theorem with a source proof body. **Paper.** Lemma B.2 and (B.21)-(B.22), p. 56

**Library.** Implementation source: [lean/Solution.lean:169-206](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Solution.lean#L169-L206).

Encoding for `Breakdown.PieceWeights.multiplierInequality_of_pieceDensity` (1): The remainder-density hypothesis includes finite negative mass and is uniform over every compatible multiplier.

Encoding for `Breakdown.PieceWeights.multiplierInequality_of_pieceDensity` (2): The proof chooses one multiplier from piece_multiplier_density and uses exactly that multiplier in the supplied remainder bound.

Encoding for `Breakdown.PieceWeights.multiplierInequality_of_pieceDensity` (3): The parameter box contains its center because the radii are nonnegative, so positivity of the uniform constants is obtained from an actual admissible parameter.

Comparison for `Breakdown.PieceWeights.multiplierInequality_of_pieceDensity`: This combines the printed piecewise multiplier mechanism with the older ball L² and unit-force-weight estimate. The full row-based, weighted-force assembly for the paper is in ExtendedCoerciveChallenge.

Clause 1 of `Breakdown.PieceWeights.multiplierInequality_of_pieceDensity`, lines 961-977: Uniform smooth profiles, forcing bounds and admissible piece data. Paper: Proposition B.1 and (B.20), p. 55 Source: [lean/CoerciveChallenge.lean:961-977](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L961-L977).

Clause 2 of `Breakdown.PieceWeights.multiplierInequality_of_pieceDensity`, lines 978-995: A separate finite-negative-mass and remainder-density inequality. Paper: (B.21), p. 56; remainder supplied by Proposition B.8, p. 63 Source: [lean/CoerciveChallenge.lean:978-995](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L978-L995).

Clause 3 of `Breakdown.PieceWeights.multiplierInequality_of_pieceDensity`, lines 996-997: Combined multiplier inequality with the common norm constant. Paper: Lemma B.2 and (B.21)-(B.22), p. 56 Source: [lean/CoerciveChallenge.lean:996-997](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CoerciveChallenge.lean#L996-L997).

<a id="140"></a>

### 140. Finite row seminorm

`Breakdown.rowNorm`: This represents the finite-direction seminorm [F] in (7.17), with orthonormal row fields and separate squared-length weights. The paper absorbs each weight into its orthogonal field eₖ.

**Source.** [lean/ExtendedCertificateChallenge.lean:10-11](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L10-L11). Def. **Paper.** (7.17), p. 32; (B.11), p. 53

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/ExtendedStatement.lean:10-11](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedStatement.lean#L10-L11).

Encoding for `Breakdown.rowNorm` (1): The raw square root does not enforce nonnegative row weights or integrable pairings; IsExtendedCertificate supplies rowWeight_nonneg and finite L² rows.

Encoding for `Breakdown.rowNorm` (2): rowCount may be zero, giving the zero seminorm. This does not remove the other certificate obligations.

Clause 1 of `Breakdown.rowNorm`, lines 10-11: This represents the finite-direction seminorm [F] in (7.17), with orthonormal row fields and separate squared-length weights. Paper: (7.17), p. 32; (B.11), p. 53 Source: [lean/ExtendedCertificateChallenge.lean:10-11](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L10-L11).

<a id="141"></a>

### 141. Approximate-profile residual

`Breakdown.weakDefectField`: This builds the residual Fₐᵅ in (7.10), including the approximate force and a pressure-gradient representative. The Laplacian is the trace of a supplied weak Hessian, so the definition can represent the piecewise smooth profiles used by the certificate.

**Source.** [lean/ExtendedCertificateChallenge.lean:13-17](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L13-L17). Def. **Paper.** (7.1), p. 30; (7.10), p. 31

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/ExtendedStatement.lean:13-17](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedStatement.lean#L13-L17).

Encoding for `Breakdown.weakDefectField` (1): The time derivative and first spatial derivative are total Lean operations; the C¹ profile hypothesis supplies their intended meanings.

Encoding for `Breakdown.weakDefectField` (2): The supplied Hessian must satisfy profileSecondDeriv_weak; an arbitrary array is not a valid replacement for the second derivative.

Encoding for `Breakdown.weakDefectField` (3): pressureGrad is a measurable field orthogonal to solenoidal tests, rather than a scalar pressure function differentiated here.

Clause 1 of `Breakdown.weakDefectField`, lines 13-17: This builds the residual Fₐᵅ in (7.10), including the approximate force and a pressure-gradient representative. Paper: (7.1), p. 30; (7.10), p. 31 Source: [lean/ExtendedCertificateChallenge.lean:13-17](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L13-L17).

<a id="142"></a>

### 142. Data for the extended certificate

`Breakdown.ExtendedCertificateData`: This stores the approximate profiles, reference profiles, residual budgets, rows and parameter-enclosure data of §§7.2–7.3. It contains values only; IsExtendedCertificate imposes the analytic and scalar conditions, and the parameter q here is the paper’s α.

**Source.** [lean/ExtendedCertificateChallenge.lean:19-66](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L19-L66). Structure. **Paper.** §§7.2–7.3, pp. 31–35

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/ExtendedStatement.lean:19-66](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedStatement.lean#L19-L66).

Encoding for `Breakdown.ExtendedCertificateData` (1): The paper’s pressure q is unrelated to the parameter variable q used in these Lean definitions.

Encoding for `Breakdown.ExtendedCertificateData` (2): The raw structure allows arbitrary values; bounds, positivity, regularity and nontriviality belong to IsExtendedCertificate.

Field `Breakdown.ExtendedCertificateData.symmetries`: The set Γ of spatial isometries paired with normalised time shifts. Paper: (7.5), p. 30 Source: [lean/ExtendedCertificateChallenge.lean:20-20](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L20).

Field `Breakdown.ExtendedCertificateData.period`: The physical similarity period S(α) before time is normalised to one. Paper: §7.2, p. 31; (7.1), p. 30 Source: [lean/ExtendedCertificateChallenge.lean:21-21](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L21).

Field `Breakdown.ExtendedCertificateData.profile`: The approximate profile Wₐᵅ in normalised time. Paper: §7.2, p. 31; (7.7)–(7.10), p. 31 Source: [lean/ExtendedCertificateChallenge.lean:22-22](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L22).

Field `Breakdown.ExtendedCertificateData.profileSecondDeriv`: A specified weak spatial Hessian of Wₐᵅ, with its linkage imposed separately. Paper: §7.2, p. 31; representation for (7.10), p. 31 Source: [lean/ExtendedCertificateChallenge.lean:23-23](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L23).

Field `Breakdown.ExtendedCertificateData.pressureGrad`: A field representing the gradient term removed by solenoidal testing. Paper: (7.2), p. 30; (7.10), p. 31 Source: [lean/ExtendedCertificateChallenge.lean:24-24](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L24).

Field `Breakdown.ExtendedCertificateData.multiplier`: The approximate force coefficients βₐ(α), to be cancelled by the correction. Paper: (7.10), p. 31; (7.30), p. 34 Source: [lean/ExtendedCertificateChallenge.lean:25-25](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L25).

Field `Breakdown.ExtendedCertificateData.target`: The prescribed total-profile pin values; subtracting the approximate-profile pins gives the paper’s ℓ̄(α). Paper: (7.11)–(7.12), p. 31; encoding change Source: [lean/ExtendedCertificateChallenge.lean:26-26](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L26).

Field `Breakdown.ExtendedCertificateData.actuator`: The forcing fields bᵢ multiplying the auxiliary force coefficients. Paper: (7.9)–(7.10), p. 31 Source: [lean/ExtendedCertificateChallenge.lean:27-27](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L27).

Field `Breakdown.ExtendedCertificateData.pin`: The matrix fields Ξᵢ defining the gradient-pairing constraints ℓᵢ. Paper: (7.11), p. 31 Source: [lean/ExtendedCertificateChallenge.lean:28-28](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L28).

The coefficient ω weights the force-vector norm; the certificate requires ω>0. Paper: (7.14), p. 32 Source: [lean/ExtendedCertificateChallenge.lean:29-29](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L29).

Field `Breakdown.ExtendedCertificateData.model`: The reference profile Wᵣᵅ at which the initial coercive estimate is certified. Paper: (7.16), p. 32 Source: [lean/ExtendedCertificateChallenge.lean:30-30](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L30).

Field `Breakdown.ExtendedCertificateData.gapSize`: The comparison bound cᵣ for replacing the reference linearisation by the approximate one. Paper: (7.19), p. 32 Source: [lean/ExtendedCertificateChallenge.lean:31-31](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L31).

Field `Breakdown.ExtendedCertificateData.formShift`: The allowed loss in the frozen quadratic form when the reference profile is replaced. Paper: (7.22), p. 33; additional decomposition Source: [lean/ExtendedCertificateChallenge.lean:32-32](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L32).

Field `Breakdown.ExtendedCertificateData.rowCount`: The number N of directions measured separately in the residual seminorm. Paper: (7.17), p. 32 Source: [lean/ExtendedCertificateChallenge.lean:33-33](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L33).

These fields are the proposed residual directions; the certificate requires them to be orthonormal in H. Paper: (7.17), p. 32; (B.11), p. 53 Source: [lean/ExtendedCertificateChallenge.lean:34-34](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L34).

The real weights τₐ are attached to the residual directions; the certificate requires their nonnegativity and orthonormality of the direction fields. Paper: (7.17), p. 32; (B.11), p. 53 Source: [lean/ExtendedCertificateChallenge.lean:35-35](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L35).

Field `Breakdown.ExtendedCertificateData.rowBound`: The bound c₀ for the row seminorm as an operator on H. Paper: (7.17), p. 32 Source: [lean/ExtendedCertificateChallenge.lean:36-36](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L36).

The proposed lower bound w∗ for the energy weight is required to be positive by the certificate. Paper: (7.14)–(7.15), p. 32 Source: [lean/ExtendedCertificateChallenge.lean:37-37](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L37).

Field `Breakdown.ExtendedCertificateData.weightFn`: The spatial weight w multiplying the squared gradient in the correction energy. Paper: (7.14), p. 32 Source: [lean/ExtendedCertificateChallenge.lean:38-38](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L38).

Field `Breakdown.ExtendedCertificateData.weightMax`: A finite upper bound on the weight w, made explicit in Lean. Paper: §7.3 before (7.14), p. 32 Source: [lean/ExtendedCertificateChallenge.lean:39-39](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L39).

Field `Breakdown.ExtendedCertificateData.coerciveL2`: The coefficient c₁ of the full residual H norm. Paper: (7.18), p. 32 Source: [lean/ExtendedCertificateChallenge.lean:40-40](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L40).

Field `Breakdown.ExtendedCertificateData.coercivePin`: The coefficient c₂ of the Euclidean pin vector. Paper: (7.18), p. 32 Source: [lean/ExtendedCertificateChallenge.lean:41-41](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L41).

Field `Breakdown.ExtendedCertificateData.coerciveTotal`: The uniform inverse bound cL after the reference-profile loss is absorbed. Paper: (7.21), p. 33 Source: [lean/ExtendedCertificateChallenge.lean:42-42](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L42).

Field `Breakdown.ExtendedCertificateData.decay`: The common decay constant for the approximate field, gradient and supplied Hessian. Paper: (7.8), p. 31; extra Hessian representative bound Source: [lean/ExtendedCertificateChallenge.lean:43-43](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L43).

Field `Breakdown.ExtendedCertificateData.periodMax`: The uniform upper bound Smax for the selected periods. Paper: §7.2, p. 31; (7.26)–(7.27), p. 33 Source: [lean/ExtendedCertificateChallenge.lean:44-44](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L44).

The natural number m is the proposed period divisor; the certificate restricts it to one or to two with the specified half-period symmetry. Paper: (7.6), p. 30; (7.26)–(7.27), p. 33 Source: [lean/ExtendedCertificateChallenge.lean:45-45](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L45).

Field `Breakdown.ExtendedCertificateData.actuatorBound`: The bound b∗ for the combined L² size of all forcing fields. Paper: (7.9), p. 31 Source: [lean/ExtendedCertificateChallenge.lean:46-46](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L46).

Field `Breakdown.ExtendedCertificateData.modelFormBound`: The frozen-form lower-bound constant at the reference profile. Paper: (7.22), p. 33; reference-form decomposition Source: [lean/ExtendedCertificateChallenge.lean:47-47](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L47).

Field `Breakdown.ExtendedCertificateData.formBound`: The final constant c₃ controlling the frozen form at the approximate profile. Paper: (7.22), p. 33 Source: [lean/ExtendedCertificateChallenge.lean:48-48](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L48).

Field `Breakdown.ExtendedCertificateData.defectBound`: The parameterwise bound δ(α) for the residual H norm. Paper: (7.23), p. 33 Source: [lean/ExtendedCertificateChallenge.lean:49-49](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L49).

Field `Breakdown.ExtendedCertificateData.defectRowBound`: The parameterwise bound δ₀(α) for the finite row seminorm of the residual. Paper: (7.23), p. 33 Source: [lean/ExtendedCertificateChallenge.lean:50-50](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L50).

Field `Breakdown.ExtendedCertificateData.defectMax`: The uniform upper bound δmax for δ(α). Paper: (7.23), p. 33 Source: [lean/ExtendedCertificateChallenge.lean:51-51](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L51).

Field `Breakdown.ExtendedCertificateData.sizeBound`: The correction radius parameter ε; the held correction has norm at most 2ε. Paper: (7.24)–(7.28), p. 33 Source: [lean/ExtendedCertificateChallenge.lean:52-52](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L52).

Field `Breakdown.ExtendedCertificateData.supBound`: The bound M on the supremum over time of the correction's spatial L² gradient norm. Paper: (7.25)–(7.27), p. 33; (7.38), p. 35 Source: [lean/ExtendedCertificateChallenge.lean:53-53](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L53).

The columns of the proposed matrix V pair with the force vector in the parameter update; the certificate requires V to be invertible. Paper: (7.30), p. 34 Source: [lean/ExtendedCertificateChallenge.lean:54-54](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L54).

The coordinate scales dⱼ enter the mixed parameter set and parameter update; the certificate requires every dⱼ to be nonzero. Paper: (7.29)–(7.30), pp. 33–34 Source: [lean/ExtendedCertificateChallenge.lean:55-55](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L55).

Field `Breakdown.ExtendedCertificateData.radius`: The separate coordinate radii ϱⱼ on the adjoint-controlled set J. Paper: (7.29), p. 33 Source: [lean/ExtendedCertificateChallenge.lean:56-56](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L56).

Field `Breakdown.ExtendedCertificateData.stiffRadius`: The radius ϱ∗ for the scaled Euclidean ball in the remaining coordinates. Paper: (7.29), p. 33; (7.37), p. 34 Source: [lean/ExtendedCertificateChallenge.lean:57-57](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L57).

Field `Breakdown.ExtendedCertificateData.adjointSet`: The coordinate set J controlled separately by approximate adjoint fields. Paper: (7.29), p. 33; (7.31)–(7.35), p. 34 Source: [lean/ExtendedCertificateChallenge.lean:58-58](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L58).

Field `Breakdown.ExtendedCertificateData.adjoint`: The parameter-dependent fields ψα,ⱼ used to estimate the selected force coordinates. Paper: (7.31)–(7.35), p. 34 Source: [lean/ExtendedCertificateChallenge.lean:59-59](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L59).

Field `Breakdown.ExtendedCertificateData.coupling`: The matrix Y(α) coupling adjoint pairings to the pin constraints. Paper: (7.33)–(7.34), p. 34 Source: [lean/ExtendedCertificateChallenge.lean:60-60](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L60).

Field `Breakdown.ExtendedCertificateData.adjointDefect`: The linear adjoint-error bound aⱼ. Paper: (7.33), p. 34 Source: [lean/ExtendedCertificateChallenge.lean:61-61](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L61).

Field `Breakdown.ExtendedCertificateData.adjointL2`: A uniform-in-time spatial L² bound on ψα,ⱼ, beyond mere membership in H. Paper: §7.3 before (7.31), p. 34; stronger representative condition Source: [lean/ExtendedCertificateChallenge.lean:62-62](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L62).

Field `Breakdown.ExtendedCertificateData.adjointQuad`: The quadratic adjoint-error bound ãⱼ for the nonlinear convection term. Paper: (7.32), p. 34 Source: [lean/ExtendedCertificateChallenge.lean:63-63](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L63).

Field `Breakdown.ExtendedCertificateData.adjointOffset`: The offset bound oⱼ comparing the corrected force coordinate with dⱼαⱼ. Paper: (7.34), p. 34 Source: [lean/ExtendedCertificateChallenge.lean:64-64](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L64).

Field `Breakdown.ExtendedCertificateData.stiffNorm`: The bound a∗ for the frame columns outside J. Paper: (7.36), p. 34 Source: [lean/ExtendedCertificateChallenge.lean:65-65](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L65).

Field `Breakdown.ExtendedCertificateData.stiffOffset`: The joint offset bound o∗ for the complementary coordinates. Paper: (7.36), p. 34 Source: [lean/ExtendedCertificateChallenge.lean:66-66](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L66).

<a id="143"></a>

### 143. Mixed box and ellipsoid

`Breakdown.ExtendedCertificateData.params`: This is the set K in (7.29): coordinate intervals on J and a scaled Euclidean ball on its complement. It contains the zero vector when the coordinate radii are nonnegative, including when k is zero or some radii vanish.

**Source.** [lean/ExtendedCertificateChallenge.lean:72-74](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L72-L74). Def. **Paper.** (7.29), p. 33

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/ExtendedStatement.lean:72-74](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedStatement.lean#L72-L74).

Encoding for `Breakdown.ExtendedCertificateData.params` (1): Fin 0 → ℝ has one element, so a zero parameter dimension does not make the certificate conditions vacuous.

Encoding for `Breakdown.ExtendedCertificateData.params` (2): The raw set uses the square of stiffRadius; the certificate separately records its nonnegative sign and the nonzero scales.

Clause 1 of `Breakdown.ExtendedCertificateData.params`, lines 73-73: Separate interval bounds on the coordinates in J. Paper: (7.29), p. 33 Source: [lean/ExtendedCertificateChallenge.lean:73-73](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L73).

Clause 2 of `Breakdown.ExtendedCertificateData.params`, lines 74-74: The squared scaled-radius bound on the complementary coordinates. Paper: (7.29), p. 33 Source: [lean/ExtendedCertificateChallenge.lean:74-74](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L74).

<a id="144"></a>

### 144. Reference-profile loss

`Breakdown.ExtendedCertificateData.transferLoss`: This is ϑ in (7.20), the product of the full reference inverse bound c₁+c₀ and the profile-comparison error cᵣ. The strict bound ϑ<1 permits the comparison error to be absorbed.

**Source.** [lean/ExtendedCertificateChallenge.lean:76-76](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L76). Def. **Paper.** (7.20)–(7.21), p. 33

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/ExtendedStatement.lean:76-76](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedStatement.lean#L76).

Clause 1 of `Breakdown.ExtendedCertificateData.transferLoss`, lines 76-76: This is ϑ in (7.20), the product of the full reference inverse bound c₁+c₀ and the profile-comparison error cᵣ. Paper: (7.20)–(7.21), p. 33 Source: [lean/ExtendedCertificateChallenge.lean:76-76](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L76).

<a id="145"></a>

### 145. Residual row seminorm

`Breakdown.ExtendedCertificateData.rows`: This applies the certificate’s chosen finite row seminorm to F. The rows are stored as unit fields with weights, matching the weighted orthogonal rows of (7.17).

**Source.** [lean/ExtendedCertificateChallenge.lean:78-78](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L78). Def. **Paper.** (7.17), p. 32

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/ExtendedStatement.lean:78-78](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedStatement.lean#L78).

Encoding for `Breakdown.ExtendedCertificateData.rows` (1): Finite L² rows and nonnegative weights are supplied by IsExtendedCertificate; this abbreviation alone does not establish them.

Clause 1 of `Breakdown.ExtendedCertificateData.rows`, lines 78-78: This applies the certificate’s chosen finite row seminorm to F. Paper: (7.17), p. 32 Source: [lean/ExtendedCertificateChallenge.lean:78-78](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L78).

<a id="146"></a>

### 146. Chosen residual field

`Breakdown.ExtendedCertificateData.defect`: This evaluates the explicit residual Fₐᵅ at the parameter q, using the chosen weak Hessian, pressure representative and approximate force. Its finite H norm is an obligation in defect_l2.

**Source.** [lean/ExtendedCertificateChallenge.lean:80-82](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L80-L82). Def. **Paper.** (7.10), p. 31; (7.23), p. 33

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/ExtendedStatement.lean:80-82](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedStatement.lean#L80-L82).

Encoding for `Breakdown.ExtendedCertificateData.defect` (1): No continuity of the H-valued residual in the parameter is assumed here; the certificate only bounds it parameter by parameter.

Clause 1 of `Breakdown.ExtendedCertificateData.defect`, lines 80-82: This evaluates the explicit residual Fₐᵅ at the parameter q, using the chosen weak Hessian, pressure representative and approximate force. Paper: (7.10), p. 31; (7.23), p. 33 Source: [lean/ExtendedCertificateChallenge.lean:80-82](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L80-L82).

<a id="147"></a>

### 147. Required correction pins

`Breakdown.ExtendedCertificateData.targetGap`: This is the paper’s ℓ̄(α), expressed as the prescribed total-profile pins minus the pins already contributed by Wₐᵅ. It is the value required of the correction in (7.12).

**Source.** [lean/ExtendedCertificateChallenge.lean:84-85](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L84-L85). Def. **Paper.** (7.11)–(7.12), p. 31; (7.24), p. 33

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/ExtendedStatement.lean:84-85](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedStatement.lean#L84-L85).

Encoding for `Breakdown.ExtendedCertificateData.targetGap` (1): Do not identify target itself with ℓ̄; the derivative pairing must be subtracted.

Clause 1 of `Breakdown.ExtendedCertificateData.targetGap`, lines 84-85: This is the paper’s ℓ̄(α), expressed as the prescribed total-profile pins minus the pins already contributed by Wₐᵅ. Paper: (7.11)–(7.12), p. 31; (7.24), p. 33 Source: [lean/ExtendedCertificateChallenge.lean:84-85](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L84-L85).

<a id="148"></a>

### 148. Corrected force coordinate

`Breakdown.ExtendedCertificateData.adjustedMultiplier`: This forms the quantity inside the offset estimate (7.34) before subtracting dⱼαⱼ. The residual-adjoint pairing and the pin correction remove the predictable linear contributions to column j of the force map.

**Source.** [lean/ExtendedCertificateChallenge.lean:87-89](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L87-L89). Def. **Paper.** (7.34), p. 34

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/ExtendedStatement.lean:87-89](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedStatement.lean#L87-L89).

Encoding for `Breakdown.ExtendedCertificateData.adjustedMultiplier` (1): The sum uses frame i j, so j selects a column of V and the force coordinates are transformed by Vᵀ.

Encoding for `Breakdown.ExtendedCertificateData.adjustedMultiplier` (2): The adjoint field and coupling matrix need not depend continuously on the parameter; they enter estimates rather than the fixed-point map itself.

Clause 1 of `Breakdown.ExtendedCertificateData.adjustedMultiplier`, lines 87-89: This forms the quantity inside the offset estimate (7.34) before subtracting dⱼαⱼ. Paper: (7.34), p. 34 Source: [lean/ExtendedCertificateChallenge.lean:87-89](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L87-L89).

<a id="149"></a>

### 149. Adjoint pairing discrepancy

`Breakdown.ExtendedCertificateData.actuatorAdjointError`: This is the vector ⟨b,ψα,ⱼ⟩H−Vⱼ used in (7.35). It measures how accurately the selected adjoint field reads out the intended column of the force-coordinate matrix.

**Source.** [lean/ExtendedCertificateChallenge.lean:91-92](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L91-L92). Def. **Paper.** (7.31) and (7.35), p. 34

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/ExtendedStatement.lean:91-92](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedStatement.lean#L91-L92).

Encoding for `Breakdown.ExtendedCertificateData.actuatorAdjointError` (1): The field pairings need their L² hypotheses before the total Bochner integrals can be read as ordinary H inner products.

Clause 1 of `Breakdown.ExtendedCertificateData.actuatorAdjointError`, lines 91-92: This is the vector ⟨b,ψα,ⱼ⟩H−Vⱼ used in (7.35). Paper: (7.31) and (7.35), p. 34 Source: [lean/ExtendedCertificateChallenge.lean:91-92](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L91-L92).

<a id="150"></a>

### 150. Extended certificate conditions

`Breakdown.IsExtendedCertificate`: This is the parameterwise analytic contract corresponding to §§7.2–7.3, with explicit field representatives and extra regularity bounds. It retains the mixed parameter set, the weighted force norm and the finite row seminorm, while exposing the reference-profile transfer and all smallness inequalities.

**Source.** [lean/ExtendedCertificateChallenge.lean:96-225](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L96-L225). Structure. **Paper.** §§7.2–7.3, pp. 31–35; (7.7)–(7.37), pp. 31–34

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/ExtendedStatement.lean:96-225](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedStatement.lean#L96-L225).

Encoding for `Breakdown.IsExtendedCertificate` (1): The conjunction is essential: a bare total integral, derivative, square root or division is not independently an analytic assertion.

Encoding for `Breakdown.IsExtendedCertificate` (2): Joint global C¹ regularity in the parameter and the pointwise decaying weak Hessian are stronger written premises than §7.2.

Encoding for `Breakdown.IsExtendedCertificate` (3): The pressure pairing is justified from the finite residual and other locally integrable terms in Breakdown.Cert.Internal.ExtendedInvariance.defect_pairing; its total-integral definition is not an escape route.

Encoding for `Breakdown.IsExtendedCertificate` (4): The strict nontriviality test rejects both zero and infinite gradient energy, since both convert to zero under ENNReal.toReal.

Encoding for `Breakdown.IsExtendedCertificate` (5): The paper’s m may be replaced conservatively by one even if a half-period symmetry exists; m is never the spatial harmonic number κ.

Encoding for `Breakdown.IsExtendedCertificate` (6): small_second is (7.26), which the paper says is unused in its displayed proof; the source’s contraction route uses it to control the gradient part of the held-set metric.

Encoding for `Breakdown.IsExtendedCertificate` (7): adjoint_l2 imposes a uniform-in-time spatial L² bound, stronger than the paper’s space-time L² membership alone.

Encoding for `Breakdown.IsExtendedCertificate` (8): The row fields are unit and orthogonal before weights are applied. Normalising nonzero paper rows and deleting zero rows yields this representation.

Encoding for `Breakdown.IsExtendedCertificate` (9): The shape and dimension of K do not remove the universal obligations: zero belongs to K under radius_nonneg.

Field `Breakdown.IsExtendedCertificate.radius_nonneg`: The coordinate radii on J are nonnegative, making zero admissible there. Paper: (7.29), p. 33 Source: [lean/ExtendedCertificateChallenge.lean:97-97](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L97).

Field `Breakdown.IsExtendedCertificate.stiffRadius_nonneg`: The joint complementary-coordinate radius ϱ∗ is nonnegative. Paper: (7.29), p. 33 Source: [lean/ExtendedCertificateChallenge.lean:98-98](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L98).

Field `Breakdown.IsExtendedCertificate.scale_ne_zero`: Every scale dⱼ is nonzero, as required by the parameter update. Paper: (7.29)–(7.30), pp. 33–34 Source: [lean/ExtendedCertificateChallenge.lean:99-99](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L99).

Field `Breakdown.IsExtendedCertificate.weight_pos`: The lower energy-weight bound w∗ is strictly positive. Paper: §7.3 and (7.14)–(7.15), p. 32 Source: [lean/ExtendedCertificateChallenge.lean:100-100](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L100).

Field `Breakdown.IsExtendedCertificate.weightFn_measurable`: The spatial weight w is measurable. Paper: §7.3 before (7.14), p. 32 Source: [lean/ExtendedCertificateChallenge.lean:101-101](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L101).

Field `Breakdown.IsExtendedCertificate.weightFn_lower`: The weight w is bounded below by w∗ at every point. Paper: §7.3 before (7.14), p. 32 Source: [lean/ExtendedCertificateChallenge.lean:102-102](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L102).

Field `Breakdown.IsExtendedCertificate.weightFn_upper`: The weight w has the explicit finite upper bound weightMax. Paper: §7.3 before (7.14), p. 32 Source: [lean/ExtendedCertificateChallenge.lean:103-103](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L103).

Field `Breakdown.IsExtendedCertificate.weightFn_invariant`: The energy weight is invariant under the spatial part of each prescribed symmetry. Paper: Encoding refinement of (7.5) and (7.14), pp. 30, 32 Source: [lean/ExtendedCertificateChallenge.lean:104-104](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L104).

Field `Breakdown.IsExtendedCertificate.multiplierWeight_pos`: The force-vector weight ω is positive, so the force directions are measured nondegenerately. Paper: (7.14), p. 32 Source: [lean/ExtendedCertificateChallenge.lean:105-105](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L105).

Field `Breakdown.IsExtendedCertificate.coerciveL2_nonneg`: The full-residual coefficient c₁ is nonnegative. Paper: §7.3 before (7.18), p. 32 Source: [lean/ExtendedCertificateChallenge.lean:106-106](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L106).

Field `Breakdown.IsExtendedCertificate.coercivePin_nonneg`: The pin coefficient c₂ is nonnegative in this representation. Paper: (7.18), p. 32; explicit sign convention Source: [lean/ExtendedCertificateChallenge.lean:107-107](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L107).

Field `Breakdown.IsExtendedCertificate.rowBound_nonneg`: The row-seminorm bound c₀ is nonnegative. Paper: §7.3 before (7.17), p. 32 Source: [lean/ExtendedCertificateChallenge.lean:108-108](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L108).

Field `Breakdown.IsExtendedCertificate.gapSize_nonneg`: The profile-comparison error cᵣ is nonnegative. Paper: §7.3 before (7.19), p. 32 Source: [lean/ExtendedCertificateChallenge.lean:109-109](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L109).

Field `Breakdown.IsExtendedCertificate.formShift_nonneg`: The allowed frozen-form loss on changing reference profile is nonnegative. Paper: (7.22), p. 33; extra reference-form decomposition Source: [lean/ExtendedCertificateChallenge.lean:110-110](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L110).

Field `Breakdown.IsExtendedCertificate.transfer_lt`: The reference-profile loss ϑ is strictly below one. Paper: (7.21), p. 33 Source: [lean/ExtendedCertificateChallenge.lean:111-111](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L111).

Field `Breakdown.IsExtendedCertificate.coerciveTotal_ge`: The transferred zero-pin inverse bound fits below cL. Paper: (7.21), p. 33 Source: [lean/ExtendedCertificateChallenge.lean:112-112](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L112).

Field `Breakdown.IsExtendedCertificate.coerciveTotal_pos`: The uniform inverse constant cL is strictly positive. Paper: (7.21), p. 33 Source: [lean/ExtendedCertificateChallenge.lean:113-113](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L113).

Field `Breakdown.IsExtendedCertificate.actuatorBound_nonneg`: The aggregate forcing-field bound b∗ is nonnegative. Paper: (7.9), p. 31 Source: [lean/ExtendedCertificateChallenge.lean:114-114](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L114).

Field `Breakdown.IsExtendedCertificate.modelFormBound_nonneg`: The reference frozen-form bound has a nonnegative coefficient. Paper: (7.22), p. 33; reference-form decomposition Source: [lean/ExtendedCertificateChallenge.lean:115-115](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L115).

Field `Breakdown.IsExtendedCertificate.formBound_ge`: The reference form bound plus its transfer loss fits within c₃. Paper: (7.22), p. 33; reference-form decomposition Source: [lean/ExtendedCertificateChallenge.lean:116-116](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L116).

Field `Breakdown.IsExtendedCertificate.sizeBound_nonneg`: The correction-size parameter ε is nonnegative. Paper: §7.3 before (7.23), p. 33 Source: [lean/ExtendedCertificateChallenge.lean:117-117](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L117).

Field `Breakdown.IsExtendedCertificate.supBound_pos`: The allowance M for the supremum over time of the spatial L² gradient norm is strictly positive. Paper: §7.3 before (7.23), p. 33 Source: [lean/ExtendedCertificateChallenge.lean:118-118](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L118).

Field `Breakdown.IsExtendedCertificate.period_continuous`: The period S(α) is continuous on K. Paper: §7.2, p. 31 Source: [lean/ExtendedCertificateChallenge.lean:119-119](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L119).

Field `Breakdown.IsExtendedCertificate.period_pos`: Every admissible parameter has a positive period. Paper: §7.2, p. 31 Source: [lean/ExtendedCertificateChallenge.lean:120-120](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L120).

Field `Breakdown.IsExtendedCertificate.period_le`: The period is bounded by Smax throughout K. Paper: §7.2, p. 31 Source: [lean/ExtendedCertificateChallenge.lean:121-121](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L121).

Field `Breakdown.IsExtendedCertificate.twist_pos`: The effective period divisor m is positive. Paper: (7.6), p. 30 Source: [lean/ExtendedCertificateChallenge.lean:122-122](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L122).

Field `Breakdown.IsExtendedCertificate.twist_mem`: Either m is one, or it is two with a witnessed half-period twisted symmetry. Paper: (7.6), p. 30; conservative choice allowed Source: [lean/ExtendedCertificateChallenge.lean:123-123](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L123).

Field `Breakdown.IsExtendedCertificate.multiplier_continuous`: The approximate force vector βₐ(α) is continuous on K. Paper: §7.2 before (7.10), p. 31 Source: [lean/ExtendedCertificateChallenge.lean:124-124](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L124).

Field `Breakdown.IsExtendedCertificate.target_continuous`: The prescribed total-profile pin vector is continuous on K. Paper: §7.2 after (7.11), p. 31; target encoding Source: [lean/ExtendedCertificateChallenge.lean:125-125](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L125).

Field `Breakdown.IsExtendedCertificate.profile_smooth`: The approximate field is globally C¹ jointly in the parameter, time and space. Paper: §7.2, p. 31; stronger written premise Source: [lean/ExtendedCertificateChallenge.lean:126-126](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L126).

Field `Breakdown.IsExtendedCertificate.profile_periodic`: The approximate field has period one in normalised time, for every parameter. Paper: §7.2, p. 31 Source: [lean/ExtendedCertificateChallenge.lean:127-127](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L127).

Field `Breakdown.IsExtendedCertificate.profile_divergence`: The approximate field is divergence-free for parameters in K. Paper: §7.2, p. 31 Source: [lean/ExtendedCertificateChallenge.lean:128-128](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L128).

Field `Breakdown.IsExtendedCertificate.profile_decay`: The field, first derivative and supplied weak Hessian decay at orders one, two and three. Paper: (7.8), p. 31; additional second-derivative bound Source: [lean/ExtendedCertificateChallenge.lean:129-131](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L129-L131).

Field `Breakdown.IsExtendedCertificate.profileSecondDeriv_measurable`: The supplied weak Hessian is strongly measurable up to a null set in space-time. Paper: §7.2, p. 31; explicit weak-Hessian representation Source: [lean/ExtendedCertificateChallenge.lean:132-133](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L132-L133).

Field `Breakdown.IsExtendedCertificate.profileSecondDeriv_periodic`: The supplied weak Hessian has period one in normalised time. Paper: §7.2, p. 31; explicit weak-Hessian representation Source: [lean/ExtendedCertificateChallenge.lean:134-134](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L134).

Field `Breakdown.IsExtendedCertificate.profileSecondDeriv_weak`: At each time, the supplied Hessian differentiates every first spatial derivative weakly. Paper: §7.2, p. 31; explicit weak-Hessian representation Source: [lean/ExtendedCertificateChallenge.lean:135-137](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L135-L137).

Field `Breakdown.IsExtendedCertificate.profile_invariant`: The approximate field obeys each Γ symmetry pointwise. Paper: (7.7), p. 31 Source: [lean/ExtendedCertificateChallenge.lean:138-139](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L138-L139).

Field `Breakdown.IsExtendedCertificate.pressureGrad_measurable`: The chosen pressure-gradient representative is strongly measurable up to a null set. Paper: (7.2), p. 30; (7.10), p. 31; representation condition Source: [lean/ExtendedCertificateChallenge.lean:140-141](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L140-L141).

Field `Breakdown.IsExtendedCertificate.pressureGrad_periodic`: The chosen pressure-gradient representative is periodic in normalised time. Paper: (7.1)–(7.2), p. 30; representation condition Source: [lean/ExtendedCertificateChallenge.lean:142-142](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L142).

Field `Breakdown.IsExtendedCertificate.pressureGrad_orthogonal`: The chosen pressure field pairs to zero with every compact solenoidal space-time test field. Paper: (7.2), p. 30; (7.10), p. 31 Source: [lean/ExtendedCertificateChallenge.lean:143-144](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L143-L144).

Field `Breakdown.IsExtendedCertificate.actuator_measurable`: Every forcing field has a strongly measurable space-time representative. Paper: §7.2 before (7.9), p. 31 Source: [lean/ExtendedCertificateChallenge.lean:145-145](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L145).

Field `Breakdown.IsExtendedCertificate.actuator_periodic`: Every forcing field has period one in normalised time. Paper: §7.1, p. 30; (7.9), p. 31 Source: [lean/ExtendedCertificateChallenge.lean:146-146](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L146).

Field `Breakdown.IsExtendedCertificate.actuator_invariant`: Every forcing field has the required Γ symmetry almost everywhere in space-time. Paper: (7.5), p. 30; §7.2 before (7.9), p. 31 Source: [lean/ExtendedCertificateChallenge.lean:147-148](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L147-L148).

Field `Breakdown.IsExtendedCertificate.actuator_norm`: The sum of squared forcing-field L² norms is at most b∗², in ENNReal before conversion. Paper: (7.9), p. 31 Source: [lean/ExtendedCertificateChallenge.lean:149-150](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L149-L150).

Field `Breakdown.IsExtendedCertificate.pin_measurable`: Each pin matrix field Ξᵢ is strongly measurable up to a null set. Paper: (7.11), p. 31 Source: [lean/ExtendedCertificateChallenge.lean:151-151](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L151).

Field `Breakdown.IsExtendedCertificate.pin_finite`: Every pin matrix field has finite squared H norm. Paper: (7.11), p. 31 Source: [lean/ExtendedCertificateChallenge.lean:152-152](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L152).

Field `Breakdown.IsExtendedCertificate.model_smooth`: Each reference profile is C¹ in normalised time and space. Paper: §7.3 before (7.16), p. 32 Source: [lean/ExtendedCertificateChallenge.lean:153-153](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L153).

Field `Breakdown.IsExtendedCertificate.model_periodic`: Each reference profile has period one. Paper: §7.3 before (7.16), p. 32 Source: [lean/ExtendedCertificateChallenge.lean:154-154](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L154).

Field `Breakdown.IsExtendedCertificate.gap_transfer`: The difference of the two linearised convection operators is bounded by cᵣ times the correction energy norm. Paper: (7.19), p. 32 Source: [lean/ExtendedCertificateChallenge.lean:155-158](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L155-L158).

Field `Breakdown.IsExtendedCertificate.form_shift`: The approximate frozen form loses at most formShift times the stationary weighted energy relative to the reference form. Paper: (7.22), p. 33; extra reference-form decomposition Source: [lean/ExtendedCertificateChallenge.lean:159-161](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L159-L161).

Field `Breakdown.IsExtendedCertificate.rowField_measurable`: Every unit row field has a strongly measurable space-time representative. Paper: (7.17), p. 32; normalised-row representation Source: [lean/ExtendedCertificateChallenge.lean:162-162](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L162).

Field `Breakdown.IsExtendedCertificate.rowField_periodic`: Each row field has period one. Paper: (7.17), p. 32; normalised-row representation Source: [lean/ExtendedCertificateChallenge.lean:163-163](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L163).

Field `Breakdown.IsExtendedCertificate.rowField_finite`: Each row field has finite H norm before its weight is applied. Paper: (7.17), p. 32; normalised-row representation Source: [lean/ExtendedCertificateChallenge.lean:164-164](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L164).

Field `Breakdown.IsExtendedCertificate.rowField_orthonormal`: The unweighted row fields are orthonormal in the period pairing. Paper: (7.17), p. 32; (B.11), p. 53; normalised-row representation Source: [lean/ExtendedCertificateChallenge.lean:165-165](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L165).

Field `Breakdown.IsExtendedCertificate.rowWeight_nonneg`: Each squared row length is nonnegative. Paper: (7.17), p. 32; (B.11), p. 53 Source: [lean/ExtendedCertificateChallenge.lean:166-166](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L166).

Field `Breakdown.IsExtendedCertificate.rowWeight_le`: Every squared row length is at most c₀². Paper: (7.17), p. 32 Source: [lean/ExtendedCertificateChallenge.lean:167-167](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L167).

Field `Breakdown.IsExtendedCertificate.coercive`: Every admissible linearised equation at the reference profile obeys the weighted correction-and-force estimate, including the row seminorm and pins. Paper: (7.18), p. 32 Source: [lean/ExtendedCertificateChallenge.lean:168-174](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L168-L174).

Field `Breakdown.IsExtendedCertificate.frozen_form`: The reference frozen form has the stated lower bound for each stationary admissible field and time. Paper: (7.22), p. 33; reference-form decomposition Source: [lean/ExtendedCertificateChallenge.lean:175-176](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L175-L176).

Field `Breakdown.IsExtendedCertificate.defect_nonneg`: The parameterwise residual bounds δ and δ₀ are nonnegative. Paper: (7.23), p. 33; explicit sign conditions Source: [lean/ExtendedCertificateChallenge.lean:177-177](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L177).

Field `Breakdown.IsExtendedCertificate.defect_l2`: The explicit residual has squared H norm at most δ(α)², with finiteness retained in ENNReal. Paper: (7.23), p. 33 Source: [lean/ExtendedCertificateChallenge.lean:178-179](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L178-L179).

Field `Breakdown.IsExtendedCertificate.defect_rows`: The residual’s row seminorm is at most δ₀(α). Paper: (7.23), p. 33 Source: [lean/ExtendedCertificateChallenge.lean:180-180](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L180).

Field `Breakdown.IsExtendedCertificate.defect_le`: The full residual bound δ(α) is at most δmax. Paper: (7.23), p. 33 Source: [lean/ExtendedCertificateChallenge.lean:181-181](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L181).

Field `Breakdown.IsExtendedCertificate.size`: The residual and correction-pin costs fit into the absorbed radius allowance (1−ϑ)ε. Paper: (7.24), p. 33 Source: [lean/ExtendedCertificateChallenge.lean:182-183](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L182-L183).

Field `Breakdown.IsExtendedCertificate.small_first`: The nonlinear contraction factor 2cLcwM is strictly below one. Paper: (7.25), p. 33 Source: [lean/ExtendedCertificateChallenge.lean:184-184](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L184).

Field `Breakdown.IsExtendedCertificate.small_second`: The gradient part of the held-set metric is controlled by the same inverse bound. Paper: (7.26), p. 33 Source: [lean/ExtendedCertificateChallenge.lean:185-187](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L185-L187).

Field `Breakdown.IsExtendedCertificate.small_third`: The nonlinear solve preserves the gradient bound M. Paper: (7.27), p. 33 Source: [lean/ExtendedCertificateChallenge.lean:188-191](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L188-L191).

Field `Breakdown.IsExtendedCertificate.frame_unit`: The parameter-update matrix V is invertible. Paper: (7.30), p. 34 Source: [lean/ExtendedCertificateChallenge.lean:192-192](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L192).

Field `Breakdown.IsExtendedCertificate.adjoint_measurable`: Each selected adjoint field has a strongly measurable space-time representative at every admissible parameter. Paper: §7.3 before (7.31), p. 34 Source: [lean/ExtendedCertificateChallenge.lean:193-194](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L193-L194).

Field `Breakdown.IsExtendedCertificate.adjoint_periodic`: Each selected adjoint field is periodic in normalised time. Paper: §7.3 before (7.31), p. 34 Source: [lean/ExtendedCertificateChallenge.lean:195-195](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L195).

Field `Breakdown.IsExtendedCertificate.adjoint_l2`: Each selected adjoint has a uniform-in-time spatial L² bound, with ENNReal finiteness. Paper: §7.3 before (7.31), p. 34; stronger written bound Source: [lean/ExtendedCertificateChallenge.lean:196-197](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L196-L197).

Field `Breakdown.IsExtendedCertificate.adjointL2_nonneg`: The selected adjoint’s spatial L² upper-bound constant is nonnegative. Paper: §7.3 before (7.31), p. 34; representation constant Source: [lean/ExtendedCertificateChallenge.lean:198-198](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L198).

Field `Breakdown.IsExtendedCertificate.adjointDefect_nonneg`: The linear adjoint-error budget aⱼ is nonnegative. Paper: §7.3 before (7.32), p. 34 Source: [lean/ExtendedCertificateChallenge.lean:199-199](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L199).

Field `Breakdown.IsExtendedCertificate.adjointQuad_nonneg`: The nonlinear adjoint-error budget ãⱼ is nonnegative. Paper: §7.3 before (7.32), p. 34 Source: [lean/ExtendedCertificateChallenge.lean:200-200](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L200).

Field `Breakdown.IsExtendedCertificate.adjoint_quadratic`: The nonlinear convection pairing with each selected adjoint is bounded by ãⱼ times weighted energy. Paper: (7.32), p. 34 Source: [lean/ExtendedCertificateChallenge.lean:201-204](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L201-L204).

Field `Breakdown.IsExtendedCertificate.adjoint_defect`: The unforced linearised residual paired with an adjoint differs from its pin combination by at most aⱼ times the energy norm. Paper: (7.33), p. 34 Source: [lean/ExtendedCertificateChallenge.lean:205-211](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L205-L211).

Field `Breakdown.IsExtendedCertificate.adjoint_offset`: Each corrected force coordinate differs from dⱼαⱼ by at most oⱼ. Paper: (7.34), p. 34 Source: [lean/ExtendedCertificateChallenge.lean:212-213](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L212-L213).

Field `Breakdown.IsExtendedCertificate.adjoint_inclusion`: The quadratic, linear, force-reading and offset errors fit inside the separate parameter radius. Paper: (7.35), p. 34 Source: [lean/ExtendedCertificateChallenge.lean:214-217](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L214-L217).

Field `Breakdown.IsExtendedCertificate.stiffNorm_nonneg`: The joint complementary-column bound a∗ is nonnegative. Paper: §7.3 before (7.36), p. 34 Source: [lean/ExtendedCertificateChallenge.lean:218-218](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L218).

Field `Breakdown.IsExtendedCertificate.stiff_norm`: The frame columns outside J have Euclidean operator bound a∗. Paper: (7.36), first inequality, p. 34 Source: [lean/ExtendedCertificateChallenge.lean:219-220](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L219-L220).

Field `Breakdown.IsExtendedCertificate.stiff_offset`: The complementary approximate force coordinates have joint offset at most o∗. Paper: (7.36), second inequality, p. 34 Source: [lean/ExtendedCertificateChallenge.lean:221-222](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L221-L222).

Field `Breakdown.IsExtendedCertificate.stiff_inclusion`: The joint force and offset budgets fit inside the complementary radius ϱ∗. Paper: (7.37), p. 34 Source: [lean/ExtendedCertificateChallenge.lean:223-223](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L223).

Field `Breakdown.IsExtendedCertificate.nontrivial`: The approximate-profile gradient energy exceeds the maximum cancellation allowed to the correction. Paper: (7.28), p. 33 Source: [lean/ExtendedCertificateChallenge.lean:224-225](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L224-L225).

Clause 83 of `Breakdown.IsExtendedCertificate`, lines 129-129: The approximate velocity has first-order spatial decay. Paper: (7.8), first bound, p. 31 Source: [lean/ExtendedCertificateChallenge.lean:129-129](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L129).

Clause 84 of `Breakdown.IsExtendedCertificate`, lines 130-130: The first spatial derivative has second-order decay. Paper: (7.8), second bound, p. 31 Source: [lean/ExtendedCertificateChallenge.lean:130-130](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L130).

Clause 85 of `Breakdown.IsExtendedCertificate`, lines 131-131: The supplied weak Hessian has a pointwise third-order decay bound beyond the two printed estimates in (7.8). Paper: §7.2, p. 31; additional explicit Hessian-decay condition Source: [lean/ExtendedCertificateChallenge.lean:131-131](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L131).

<a id="151"></a>

### 151. An extended certificate exists

`Breakdown.ExtendedCertificateHypothesis`: This existentially packages a parameter dimension, a complete data record and all extended certificate conditions. It is the premise of extended_certificate_orbit; it does not supply the numerical data or discharge their inequalities.

**Source.** [lean/ExtendedCertificateChallenge.lean:227-228](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L227-L228). Def. **Paper.** Certificate definition at the end of §7.3, pp. 34–35; Theorem 7.1, p. 35

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/ExtendedStatement.lean:227-228](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedStatement.lean#L227-L228).

Encoding for `Breakdown.ExtendedCertificateHypothesis` (1): The existential quantifier does not claim that a witness has been computed or checked.

Clause 1 of `Breakdown.ExtendedCertificateHypothesis`, lines 227-228: This existentially packages a parameter dimension, a complete data record and all extended certificate conditions. Paper: Certificate definition at the end of §7.3, pp. 34–35; Theorem 7.1, p. 35 Source: [lean/ExtendedCertificateChallenge.lean:227-228](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L227-L228).

<a id="152"></a>

### 152. Normalise the force weight

For ω≠0, reciprocal rescaling of the forcing fields and force coefficients sets ω to one while preserving their product in the equation. The frame and complementary-column bound are rescaled as well; the certificate supplies ω>0.

**Source.** [lean/ExtendedCertificateChallenge.lean:234-241](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L234-L241). Def. **Paper.** (7.10), p. 31; (7.14), p. 32; (7.30)–(7.37), p. 34; normalisation helper

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/ExtendedStatement.lean:234-241](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedStatement.lean#L234-L241).

Encoding for `Breakdown.ExtendedCertificateData.withUnitWeight` (1): The transformation is total even at ω=0; its preservation theorem assumes a certificate, whose multiplierWeight_pos excludes that case.

For ω≠0, reciprocal rescaling of the forcing fields and force coefficients sets ω to one and preserves their product in the equation. Paper: (7.10), p. 31; (7.14), p. 32; (7.30)–(7.37), p. 34; normalisation helper Source: [lean/ExtendedCertificateChallenge.lean:234-241](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L234-L241).

<a id="153"></a>

### 153. Absorb the reference error

`Breakdown.ExtendedCertificateData.atProfile`: This replaces the reference profile by the approximate profile after absorbing the comparison loss ϑ. It divides c₁, c₂, c₀ and δ₀ by 1−ϑ and each squared row-length weight by (1−ϑ)²; the final inverse allowance c_L is unchanged.

**Source.** [lean/ExtendedCertificateChallenge.lean:243-253](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L243-L253). Def. **Paper.** (7.19)–(7.21), pp. 32–33; (7.22), p. 33; normalisation helper

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/ExtendedStatement.lean:243-253](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedStatement.lean#L243-L253).

Encoding for `Breakdown.ExtendedCertificateData.atProfile` (1): The preservation theorem uses transfer_lt, so every division by 1−ϑ has a positive denominator.

Clause 1 of `Breakdown.ExtendedCertificateData.atProfile`, lines 243-253: This replaces the reference profile by the approximate profile after absorbing the comparison loss ϑ. Paper: (7.19)–(7.21), pp. 32–33; (7.22), p. 33; normalisation helper Source: [lean/ExtendedCertificateChallenge.lean:243-253](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L243-L253).

<a id="154"></a>

### 154. Force rescaling preserves conditions

`Breakdown.isExtendedCertificate_withUnitWeight`: This states that a valid extended certificate remains valid after the force weight is normalised to one. It implements the coefficient change associated with the weighted norm in (7.14).

**Source.** [lean/ExtendedCertificateChallenge.lean:257-259](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L257-L259). Readable theorem stub. **Paper.** (7.10), p. 31; (7.14), p. 32; implementation normalisation, no separately numbered theorem

**Library.** Implementation source: [lean/Solution.lean:217-219](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Solution.lean#L217-L219).

Comparison for `Breakdown.isExtendedCertificate_withUnitWeight`: This is a certificate-preservation helper with no separately numbered paper statement. It keeps the same analytic problem under a change of force coordinates.

Clause 1 of `Breakdown.isExtendedCertificate_withUnitWeight`, lines 257-258: This states that a valid extended certificate remains valid after the force weight is normalised to one. Paper: (7.10), p. 31; (7.14), p. 32; implementation normalisation, no separately numbered theorem Source: [lean/ExtendedCertificateChallenge.lean:257-258](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L257-L258).

<a id="155"></a>

### 155. Reference transfer preserves conditions

`Breakdown.isExtendedCertificate_atProfile`: This states that the reference-profile error can be absorbed into the certificate constants. Its input includes ϑ<1, the condition needed to replace the reference linearisation by the approximate-profile linearisation.

**Source.** [lean/ExtendedCertificateChallenge.lean:261-263](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L261-L263). Readable theorem stub. **Paper.** Paragraph after (7.21), p. 33; implementation normalisation

**Library.** Implementation source: [lean/Solution.lean:221-223](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Solution.lean#L221-L223).

Comparison for `Breakdown.isExtendedCertificate_atProfile`: The paper explains this transfer after (7.21); Lean states preservation of its entire data-and-condition record. The formulations are at different levels of detail.

Clause 1 of `Breakdown.isExtendedCertificate_atProfile`, lines 261-262: This states that the reference-profile error can be absorbed into the certificate constants. Paper: Paragraph after (7.21), p. 33; implementation normalisation Source: [lean/ExtendedCertificateChallenge.lean:261-262](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L261-L262).

<a id="156"></a>

### 156. A certificate gives a weak profile

`Breakdown.extended_certificate_orbit`: This exports weak-profile existence from an extended certificate. The internal construction retains the chosen parameter and correction bounds, while this theorem’s conclusion hides the same-witness information displayed in (7.38)–(7.39).

**Source.** [lean/ExtendedCertificateChallenge.lean:265-267](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L265-L267). Readable theorem stub. **Paper.** Theorem 7.1 and (7.38)–(7.39), p. 35

**Library.** Implementation source: [lean/Solution.lean:225-227](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Solution.lean#L225-L227).

Encoding for `Breakdown.extended_certificate_orbit` (1): The premise has stronger written representative and regularity conditions than the paper’s certificate definition.

Encoding for `Breakdown.extended_certificate_orbit` (2): The public conclusion is WeakPeriodicSimilarityProfileExists, so this entry does not assert a separately retained parameter, prescribed Γ symmetry bundle, exact selected period or all quantitative bounds.

Encoding for `Breakdown.extended_certificate_orbit` (3): The readable theorem is a placeholder contract; Solution.lean:225–227 calls the implemented extended_certificate_orbit_proved.

Comparison for `Breakdown.extended_certificate_orbit`: The extended predicate adds representative and regularity conditions, and the exported conclusion records only weak-profile existence. The paper’s Theorem 7.1 retains α, its period, all prescribed symmetries and the bounds (7.38); these are not all exposed by this theorem type.

Clause 1 of `Breakdown.extended_certificate_orbit`, lines 265-266: This exports weak-profile existence from an extended certificate. Paper: Theorem 7.1 and (7.38)–(7.39), p. 35 Source: [lean/ExtendedCertificateChallenge.lean:265-266](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCertificateChallenge.lean#L265-L266).

<a id="157"></a>

### 157. Squared Hessian size

`Breakdown.Coercive.secondDerivSq`: This is the sum of squares of all spatial Hessian entries, used to measure convergence of the smooth approximations. It is a pointwise Hessian norm, whereas the correction energy in (7.14) uses the squared Laplacian.

**Source.** [lean/ExtendedCoerciveChallenge.lean:12-13](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L12-L13). Def. **Paper.** (B.16), p. 54; approximation step of Proposition B.1, pp. 55–56

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/ExtendedCoerciveDefs.lean:12-13](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L12-L13).

Encoding for `Breakdown.Coercive.secondDerivSq` (1): Equality of integrated Hessian and Laplacian energies requires the analytic identities in the proof; it is not a pointwise definition here.

Clause 1 of `Breakdown.Coercive.secondDerivSq`, lines 12-13: This is the sum of squares of all spatial Hessian entries, used to measure convergence of the smooth approximations. Paper: (B.16), p. 54; approximation step of Proposition B.1, pp. 55–56 Source: [lean/ExtendedCoerciveChallenge.lean:12-13](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L12-L13).

<a id="158"></a>

### 158. Base part of the mode density

`Breakdown.Coercive.baseDensity`: This is the part of Iι in (B.16) before the λ and μ corrections are added. It allows an arbitrary coercivity constant c; the paper displays c=3/50.

**Source.** [lean/ExtendedCoerciveChallenge.lean:15-19](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L15-L19). Def. **Paper.** (B.16), p. 54

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/ExtendedCoerciveDefs.lean:15-19](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L15-L19).

Encoding for `Breakdown.Coercive.baseDensity` (1): The inputs x₂, x꜀, x₁, xₒ, x₀ stand respectively for Hessian, vorticity-gradient, gradient, vorticity and velocity amplitudes.

Encoding for `Breakdown.Coercive.baseDensity` (2): The second derivatives of D and Z have their intended meanings under the C² fields of IsAdmissibleWeak.

Clause 1 of `Breakdown.Coercive.baseDensity`, lines 15-19: This is the part of Iι in (B.16) before the λ and μ corrections are added. Paper: (B.16), p. 54 Source: [lean/ExtendedCoerciveChallenge.lean:15-19](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L15-L19).

<a id="159"></a>

### 159. Velocity-mode amplitude

`Breakdown.Coercive.velAmp`: This is the Euclidean magnitude of the velocity mode v̂ι from (B.12). It supplies the order-zero argument in the mode quadratic form (B.16).

**Source.** [lean/ExtendedCoerciveChallenge.lean:21-22](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L21-L22). Def. **Paper.** (B.12), p. 53; (B.16), p. 54

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/ExtendedCoerciveDefs.lean:21-22](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L21-L22).

Encoding for `Breakdown.Coercive.velAmp` (1): The finite sum of squared complex component norms is nonnegative, so its square root has the intended Euclidean meaning.

Encoding for `Breakdown.Coercive.velAmp` (2): The underlying mode integrals still require the admissible-field integrability hypotheses; the definition alone is total on arbitrary input fields.

Clause 1 of `Breakdown.Coercive.velAmp`, lines 21-22: This is the Euclidean magnitude of the velocity mode v̂ι from (B.12). Paper: (B.12), p. 53; (B.16), p. 54 Source: [lean/ExtendedCoerciveChallenge.lean:21-22](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L21-L22).

<a id="160"></a>

### 160. Gradient-mode amplitude

`Breakdown.Coercive.gradAmp`: This is the Euclidean magnitude of the matrix mode representing ∇v̂ι. It is the order-one derivative amplitude used by (B.16) and the harmonic interaction bounds.

**Source.** [lean/ExtendedCoerciveChallenge.lean:24-25](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L24-L25). Def. **Paper.** (B.12), p. 53; (B.16), p. 54

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/ExtendedCoerciveDefs.lean:24-25](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L24-L25).

Encoding for `Breakdown.Coercive.gradAmp` (1): The finite sum of squared complex component norms is nonnegative, so its square root has the intended Euclidean meaning.

Encoding for `Breakdown.Coercive.gradAmp` (2): The underlying mode integrals still require the admissible-field integrability hypotheses; the definition alone is total on arbitrary input fields.

Clause 1 of `Breakdown.Coercive.gradAmp`, lines 24-25: This is the Euclidean magnitude of the matrix mode representing ∇v̂ι. Paper: (B.12), p. 53; (B.16), p. 54 Source: [lean/ExtendedCoerciveChallenge.lean:24-25](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L24-L25).

<a id="161"></a>

### 161. Vorticity-mode amplitude

`Breakdown.Coercive.vortAmp`: This contracts the gradient mode to its curl and takes its magnitude. It is the primed order-one amplitude in Iι and the main amplitude in the λ multiplier gains.

**Source.** [lean/ExtendedCoerciveChallenge.lean:27-28](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L27-L28). Def. **Paper.** (B.16), p. 54; (B.14)–(B.15), p. 54

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/ExtendedCoerciveDefs.lean:27-28](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L27-L28).

Encoding for `Breakdown.Coercive.vortAmp` (1): The finite sum of squared complex component norms is nonnegative, so its square root has the intended Euclidean meaning.

Encoding for `Breakdown.Coercive.vortAmp` (2): The underlying mode integrals still require the admissible-field integrability hypotheses; the definition alone is total on arbitrary input fields.

Clause 1 of `Breakdown.Coercive.vortAmp`, lines 27-28: This contracts the gradient mode to its curl and takes its magnitude. Paper: (B.16), p. 54; (B.14)–(B.15), p. 54 Source: [lean/ExtendedCoerciveChallenge.lean:27-28](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L27-L28).

<a id="162"></a>

### 162. Hessian-mode amplitude

`Breakdown.Coercive.secondDerivAmp`: This is the Euclidean magnitude of all entries of the second-derivative mode. It supplies the unprimed order-two term in Iι.

**Source.** [lean/ExtendedCoerciveChallenge.lean:30-31](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L30-L31). Def. **Paper.** (B.16), p. 54

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/ExtendedCoerciveDefs.lean:30-31](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L30-L31).

Encoding for `Breakdown.Coercive.secondDerivAmp` (1): The finite sum of squared complex component norms is nonnegative, so its square root has the intended Euclidean meaning.

Encoding for `Breakdown.Coercive.secondDerivAmp` (2): The underlying mode integrals still require the admissible-field integrability hypotheses; the definition alone is total on arbitrary input fields.

Clause 1 of `Breakdown.Coercive.secondDerivAmp`, lines 30-31: This is the Euclidean magnitude of all entries of the second-derivative mode. Paper: (B.16), p. 54 Source: [lean/ExtendedCoerciveChallenge.lean:30-31](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L30-L31).

<a id="163"></a>

### 163. Vorticity-gradient amplitude

`Breakdown.Coercive.vortGradAmp`: This takes the curl contraction of a second-derivative mode and measures all entries of the resulting gradient. It is the primed order-two amplitude in Iι.

**Source.** [lean/ExtendedCoerciveChallenge.lean:33-34](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L33-L34). Def. **Paper.** (B.16), p. 54

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/ExtendedCoerciveDefs.lean:33-34](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L33-L34).

Encoding for `Breakdown.Coercive.vortGradAmp` (1): The finite sum of squared complex component norms is nonnegative, so its square root has the intended Euclidean meaning.

Encoding for `Breakdown.Coercive.vortGradAmp` (2): The underlying mode integrals still require the admissible-field integrability hypotheses; the definition alone is total on arbitrary input fields.

Clause 1 of `Breakdown.Coercive.vortGradAmp`, lines 33-34: This takes the curl contraction of a second-derivative mode and measures all entries of the resulting gradient. Paper: (B.16), p. 54 Source: [lean/ExtendedCoerciveChallenge.lean:33-34](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L33-L34).

<a id="164"></a>

### 164. Insert the five mode amplitudes

`Breakdown.Coercive.modeVals`: This evaluates a scalar quadratic-form expression on the five derivative amplitudes used in (B.16). The argument order keeps the vorticity terms separate from the full gradient and Hessian terms.

**Source.** [lean/ExtendedCoerciveChallenge.lean:36-39](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L36-L39). Def. **Paper.** (B.16), p. 54; evaluation helper

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/ExtendedCoerciveDefs.lean:36-39](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L36-L39).

Clause 1 of `Breakdown.Coercive.modeVals`, lines 36-39: This evaluates a scalar quadratic-form expression on the five derivative amplitudes used in (B.16). Paper: (B.16), p. 54; evaluation helper Source: [lean/ExtendedCoerciveChallenge.lean:36-39](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L36-L39).

<a id="165"></a>

### 165. Signed split of the multiplier bound

`Breakdown.Coercive.IsSplitLowerBound`: This records a lower bound on the multiplier gap using nonnegative mode gains, mode remainders, block errors and the stretching term J. Positive and negative parts are retained separately in ENNReal so the proof can pass to a weak limit before establishing the final real-valued inequality.

**Source.** [lean/ExtendedCoerciveChallenge.lean:41-48](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L41-L48). Def. **Paper.** Proposition B.1, (B.18)–(B.20), p. 55; approximation step, p. 56

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/ExtendedCoerciveDefs.lean:41-48](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L41-L48).

Encoding for `Breakdown.Coercive.IsSplitLowerBound` (1): The first conjunct only makes the negative mode remainders and negative block contribution finite; finiteness of the full negative density is a separate later obligation.

Encoding for `Breakdown.Coercive.IsSplitLowerBound` (2): ENNReal.ofReal takes the positive part, and ENNReal.tsum preserves divergence as infinity. No subtraction of two infinite quantities occurs here.

Clause 1 of `Breakdown.Coercive.IsSplitLowerBound`, lines 42-43: The negative remainder and block errors have finite integral. Paper: Proposition B.1 approximation step, pp. 55–56 Source: [lean/ExtendedCoerciveChallenge.lean:42-43](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L42-L43).

The sum of the positive masses plus max(−X,0) is at most max(X,0) plus the negative masses. The negative mass of J may still be infinite at this stage. Paper: (B.20), p. 55; signed implementation form Source: [lean/ExtendedCoerciveChallenge.lean:44-48](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L44-L48).

<a id="166"></a>

### 166. Interactions across a mode set

`Breakdown.Coercive.edgeSum`: This sums harmonic interactions that leave a selected set Nₚ or its negative. These are the cross-mode errors in the λ and μ estimates described after (B.20).

**Source.** [lean/ExtendedCoerciveChallenge.lean:51-53](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L51-L53). Def. **Paper.** Proof of Proposition B.1 after (B.20), pp. 55–56; no separately printed formula

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/ExtendedCoerciveDefs.lean:51-53](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L51-L53).

Encoding for `Breakdown.Coercive.edgeSum` (1): The two branches select opposite frequency signs; the one-sided frequency condition is what makes Nₚ and −Nₚ disjoint in admissible data.

Encoding for `Breakdown.Coercive.edgeSum` (2): Only the supplied finite harmonic set is summed here; its coverage of the reference profile is imposed separately.

Clause 1 of `Breakdown.Coercive.edgeSum`, lines 51-53: This sums harmonic interactions that leave a selected set Nₚ or its negative. Paper: Proof of Proposition B.1 after (B.20), pp. 55–56; no separately printed formula Source: [lean/ExtendedCoerciveChallenge.lean:51-53](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L51-L53).

<a id="167"></a>

### 167. Mode-set square-sum norm

For a square-summable amplitude sequence on Np∪−Np, this formula is its ℓ² norm and is used in the block estimates for cross-mode errors. Outside that class the real series is assigned a default value, so the norm interpretation requires summability.

**Source.** [lean/ExtendedCoerciveChallenge.lean:55-56](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L55-L56). Def. **Paper.** Proof of Proposition B.1, pp. 55–56; block estimate helper

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/ExtendedCoerciveDefs.lean:55-56](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L55-L56).

Encoding for `Breakdown.Coercive.pieceNorm` (1): This is a real tsum, so the displayed expression alone does not assert square summability.

Encoding for `Breakdown.Coercive.pieceNorm` (2): At its proof uses, Fourier square-sum estimates supply summability before it is interpreted as an ℓ² norm.

For a square-summable amplitude sequence, the formula gives its ℓ² norm restricted to Np∪−Np. Paper: Proof of Proposition B.1, pp. 55–56; block estimate helper Source: [lean/ExtendedCoerciveChallenge.lean:55-56](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L55-L56).

<a id="168"></a>

### 168. Transport speed in a rotating frame

`Breakdown.Coercive.frameSpeedSup`: This is the time-and-angle supremum of the transport velocity Wᵣ+y/2−νₚe_z×y. It gives the transport bound entering the errors in (B.16).

**Source.** [lean/ExtendedCoerciveChallenge.lean:58-60](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L58-L60). Def. **Paper.** Transport bounds in §B.2, pp. 53–54; proof of Proposition B.1, pp. 55–56

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/ExtendedCoerciveDefs.lean:58-60](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L58-L60).

Encoding for `Breakdown.Coercive.frameSpeedSup` (1): The supremum is taken in ℝ; its usual upper-bound properties require boundedness.

Encoding for `Breakdown.Coercive.frameSpeedSup` (2): The admissibility speed bounds are pointwise in time and angle and provide the required finite majorant.

Clause 1 of `Breakdown.Coercive.frameSpeedSup`, lines 58-60: This is the time-and-angle supremum of the transport velocity Wᵣ+y/2−νₚe_z×y. Paper: Transport bounds in §B.2, pp. 53–54; proof of Proposition B.1, pp. 55–56 Source: [lean/ExtendedCoerciveChallenge.lean:58-60](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L58-L60).

<a id="169"></a>

### 169. Vorticity bound over time and angle

`Breakdown.Coercive.vortSup`: This is the real supremum of the vorticity of the reference profile over time and axial angle. It supplies a coefficient in the λ block errors.

**Source.** [lean/ExtendedCoerciveChallenge.lean:62-63](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L62-L63). Def. **Paper.** Reference-profile bounds before (B.16), p. 54; proof of Proposition B.1, pp. 55–56

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/ExtendedCoerciveDefs.lean:62-63](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L62-L63).

Encoding for `Breakdown.Coercive.vortSup` (1): The pointwise supVort_ge admissibility bound supplies boundedness for this real supremum.

Encoding for `Breakdown.Coercive.vortSup` (2): The derivative is meaningful under the reference-profile regularity hypotheses.

Clause 1 of `Breakdown.Coercive.vortSup`, lines 62-63: This is the real supremum of the vorticity of the reference profile over time and axial angle. Paper: Reference-profile bounds before (B.16), p. 54; proof of Proposition B.1, pp. 55–56 Source: [lean/ExtendedCoerciveChallenge.lean:62-63](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L62-L63).

<a id="170"></a>

### 170. Vorticity-gradient bound

`Breakdown.Coercive.vortGradSup`: This is the real supremum of the operator norm of ∇curl Wᵣ over time and axial angle. The weak-Hessian route replaces this classical derivative by vortGradSupWith.

**Source.** [lean/ExtendedCoerciveChallenge.lean:65-66](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L65-L66). Def. **Paper.** Reference-profile bounds before (B.16), p. 54; (B.18), p. 55

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/ExtendedCoerciveDefs.lean:65-66](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L65-L66).

Encoding for `Breakdown.Coercive.vortGradSup` (1): A raw fderiv is total; the classical-to-weak comparison theorem assumes C² regularity.

Encoding for `Breakdown.Coercive.vortGradSup` (2): The admissibility bound supplies the finite majorant needed for the real supremum.

Clause 1 of `Breakdown.Coercive.vortGradSup`, lines 65-66: This is the real supremum of the operator norm of ∇curl Wᵣ over time and axial angle. Paper: Reference-profile bounds before (B.16), p. 54; (B.18), p. 55 Source: [lean/ExtendedCoerciveChallenge.lean:65-66](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L65-L66).

<a id="171"></a>

### 171. Positive vorticity-mode gain

`Breakdown.Coercive.pieceEpsPos`: This is λₚ|Ωₚ(ι)| times the squared vorticity-mode amplitude on Nₚ∪−Nₚ. It is the positive contribution of a λ piece to the primed order-one coefficient in (B.16).

**Source.** [lean/ExtendedCoerciveChallenge.lean:69-72](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L69-L72). Def. **Paper.** (B.15)–(B.16), p. 54

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/ExtendedCoerciveDefs.lean:69-72](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L69-L72).

Encoding for `Breakdown.Coercive.pieceEpsPos` (1): The λ weights are nonnegative and the selected frequencies have a positive one-sided bound under admissibility.

Clause 1 of `Breakdown.Coercive.pieceEpsPos`, lines 69-72: This is λₚ|Ωₚ(ι)| times the squared vorticity-mode amplitude on Nₚ∪−Nₚ. Paper: (B.15)–(B.16), p. 54 Source: [lean/ExtendedCoerciveChallenge.lean:69-72](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L69-L72).

<a id="172"></a>

### 172. Vorticity cross-mode errors

`Breakdown.Coercive.pieceEpsRestMode`: This records the negative interaction terms from one λ piece when reference-profile harmonics connect its modes to modes outside the piece. The four summands use the reference velocity, gradient, vorticity gradient and vorticity bounds.

**Source.** [lean/ExtendedCoerciveChallenge.lean:74-81](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L74-L81). Def. **Paper.** Terms omitted from (B.16), p. 54; proof of Proposition B.1, pp. 55–56

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/ExtendedCoerciveDefs.lean:74-81](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L74-L81).

Clause 1 of `Breakdown.Coercive.pieceEpsRestMode`, lines 74-81: This records the negative interaction terms from one λ piece when reference-profile harmonics connect its modes to modes outside the piece. Paper: Terms omitted from (B.16), p. 54; proof of Proposition B.1, pp. 55–56 Source: [lean/ExtendedCoerciveChallenge.lean:74-81](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L74-L81).

<a id="173"></a>

### 173. Vorticity block errors

`Breakdown.Coercive.pieceEpsBlock`: This bounds the remaining λ-piece terms by products of square-sum norms over its modes. Transport, the weight gradient, frame rotation, reference vorticity and its gradient supply the error coefficients.

**Source.** [lean/ExtendedCoerciveChallenge.lean:83-94](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L83-L94). Def. **Paper.** Terms omitted from (B.16), p. 54; proof of Proposition B.1, pp. 55–56

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/ExtendedCoerciveDefs.lean:83-94](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L83-L94).

Encoding for `Breakdown.Coercive.pieceEpsBlock` (1): The real square sums and suprema acquire their analytic meaning from the summability and boundedness lemmas used before the estimate.

Clause 1 of `Breakdown.Coercive.pieceEpsBlock`, lines 83-94: This bounds the remaining λ-piece terms by products of square-sum norms over its modes. Paper: Terms omitted from (B.16), p. 54; proof of Proposition B.1, pp. 55–56 Source: [lean/ExtendedCoerciveChallenge.lean:83-94](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L83-L94).

<a id="174"></a>

### 174. Positive velocity-mode gain

`Breakdown.Coercive.pieceMuPos`: This is (1−cμ)μₚ|Ωₚ(ι)| times the squared velocity-mode amplitude. The fraction cμ of the same frequency seminorm is reserved on the left of (B.20).

**Source.** [lean/ExtendedCoerciveChallenge.lean:97-100](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L97-L100). Def. **Paper.** (B.15)–(B.16), p. 54; (B.20), p. 55

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/ExtendedCoerciveDefs.lean:97-100](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L97-L100).

Encoding for `Breakdown.Coercive.pieceMuPos` (1): Admissibility supplies 0<cμ<1 and nonnegative μ weights.

Clause 1 of `Breakdown.Coercive.pieceMuPos`, lines 97-100: This is (1−cμ)μₚ|Ωₚ(ι)| times the squared velocity-mode amplitude. Paper: (B.15)–(B.16), p. 54; (B.20), p. 55 Source: [lean/ExtendedCoerciveChallenge.lean:97-100](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L97-L100).

<a id="175"></a>

### 175. Velocity cross-mode errors

`Breakdown.Coercive.pieceMuRestMode`: This bounds the cross-mode transport and stretching terms for a μ piece. Its positive parameter ηₚ divides a Young-inequality split between the coupled gradient contribution and the weighted velocity contribution.

**Source.** [lean/ExtendedCoerciveChallenge.lean:103-110](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L103-L110). Def. **Paper.** Terms omitted from (B.16), p. 54; proof of Proposition B.1, pp. 55–56

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/ExtendedCoerciveDefs.lean:103-110](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L103-L110).

Encoding for `Breakdown.Coercive.pieceMuRestMode` (1): The division by ηₚ is justified by mu_eta_pos; the total raw definition is not a positivity certificate.

Clause 1 of `Breakdown.Coercive.pieceMuRestMode`, lines 103-110: This bounds the cross-mode transport and stretching terms for a μ piece. Paper: Terms omitted from (B.16), p. 54; proof of Proposition B.1, pp. 55–56 Source: [lean/ExtendedCoerciveChallenge.lean:103-110](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L103-L110).

<a id="176"></a>

### 176. Velocity block errors

`Breakdown.Coercive.pieceMuBlock`: This collects the μ-piece transport, weight-gradient and frame-rotation errors using the mode-set norms. It is an intermediate bound before Young’s inequality distributes errors among the coefficients of (B.16).

**Source.** [lean/ExtendedCoerciveChallenge.lean:112-117](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L112-L117). Def. **Paper.** Proof of Proposition B.1, pp. 55–56; no separately printed formula

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/ExtendedCoerciveDefs.lean:112-117](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L112-L117).

Encoding for `Breakdown.Coercive.pieceMuBlock` (1): The pieceNorm square sums require the Fourier summability estimates at the point of use.

Clause 1 of `Breakdown.Coercive.pieceMuBlock`, lines 112-117: This collects the μ-piece transport, weight-gradient and frame-rotation errors using the mode-set norms. Paper: Proof of Proposition B.1, pp. 55–56; no separately printed formula Source: [lean/ExtendedCoerciveChallenge.lean:112-117](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L112-L117).

<a id="177"></a>

### 177. Sum of the positive piece gains

`Breakdown.Coercive.piecePos`: This adds the λ and μ positive frequency gains for one mode. It is the nonnegative part kept separate while the remaining terms in (B.16) are estimated.

**Source.** [lean/ExtendedCoerciveChallenge.lean:119-121](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L119-L121). Def. **Paper.** (B.16), p. 54; proof of Proposition B.1, pp. 55–56

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/ExtendedCoerciveDefs.lean:119-121](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L119-L121).

Encoding for `Breakdown.Coercive.piecePos` (1): The two piece families are finite and may be empty; the base mode density is still present elsewhere.

Clause 1 of `Breakdown.Coercive.piecePos`, lines 119-121: This adds the λ and μ positive frequency gains for one mode. Paper: (B.16), p. 54; proof of Proposition B.1, pp. 55–56 Source: [lean/ExtendedCoerciveChallenge.lean:119-121](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L119-L121).

<a id="178"></a>

### 178. Base density and mode remainders

`Breakdown.Coercive.pieceRest`: This combines the base quadratic density with all λ and μ cross-mode remainders for one mode. The positive frequency gains and block errors are carried separately until the signed bound is assembled.

**Source.** [lean/ExtendedCoerciveChallenge.lean:123-127](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L123-L127). Def. **Paper.** (B.16), p. 54; proof of Proposition B.1, pp. 55–56

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/ExtendedCoerciveDefs.lean:123-127](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L123-L127).

Clause 1 of `Breakdown.Coercive.pieceRest`, lines 123-127: This combines the base quadratic density with all λ and μ cross-mode remainders for one mode. Paper: (B.16), p. 54; proof of Proposition B.1, pp. 55–56 Source: [lean/ExtendedCoerciveChallenge.lean:123-127](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L123-L127).

<a id="179"></a>

### 179. Sum of the block errors

`Breakdown.Coercive.pieceBlock`: This adds the block errors over the finite λ and μ piece families. It completes the intermediate split used to prove the density lower bound in Proposition B.1.

**Source.** [lean/ExtendedCoerciveChallenge.lean:129-132](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L129-L132). Def. **Paper.** Proof of Proposition B.1, pp. 55–56; no separately printed formula

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/ExtendedCoerciveDefs.lean:129-132](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L129-L132).

Clause 1 of `Breakdown.Coercive.pieceBlock`, lines 129-132: This adds the block errors over the finite λ and μ piece families. Paper: Proof of Proposition B.1, pp. 55–56; no separately printed formula Source: [lean/ExtendedCoerciveChallenge.lean:129-132](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L129-L132).

<a id="180"></a>

### 180. Time derivative and similarity drift

`Breakdown.Coercive.transportPart`: This is S⁻¹∂θv+v/2+(y·∇)v/2, the time-and-drift part of T_S. The Laplacian is handled separately, so this field corresponds to T_Sv+∆v.

**Source.** [lean/ExtendedCoerciveChallenge.lean:134-135](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L134-L135). Def. **Paper.** (7.1) and explanation after (7.4), p. 30

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/ExtendedCoerciveDefs.lean:134-135](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L134-L135).

Encoding for `Breakdown.Coercive.transportPart` (1): The source’s g denotes this combined time-and-drift term, not T_Sv alone.

Encoding for `Breakdown.Coercive.transportPart` (2): SmoothPerturbation provides genuine derivatives; at weak inputs g is independently linked through the perturbation contract.

Clause 1 of `Breakdown.Coercive.transportPart`, lines 134-135: This is S⁻¹∂θv+v/2+(y·∇)v/2, the time-and-drift part of T_S. Paper: (7.1) and explanation after (7.4), p. 30 Source: [lean/ExtendedCoerciveChallenge.lean:134-135](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L134-L135).

<a id="181"></a>

### 181. Smooth fields for approximation

`Breakdown.Coercive.IsSmoothPerturbation`: This is the smooth class used to prove the multiplier identities before taking limits to D_S. It asks for period-one, solenoidal fields with weighted velocity and time control and square-integrable derivatives of every positive spatial order.

**Source.** [lean/ExtendedCoerciveChallenge.lean:137-150](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L137-L150). Structure. **Paper.** (7.4), p. 30; smooth-approximation step in Proposition B.1, pp. 55–56

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/ExtendedCoerciveDefs.lean:137-150](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L137-L150).

Encoding for `Breakdown.Coercive.IsSmoothPerturbation` (1): The zeroth-order velocity need not be unweighted L²; the formal class uses a spatial weight and L⁶ slices.

Encoding for `Breakdown.Coercive.IsSmoothPerturbation` (2): This class does not itself impose the set Γ of symmetries.

Field `Breakdown.Coercive.IsSmoothPerturbation.smooth`: The field is jointly smooth in time and space. Paper: Proposition B.1 proof, pp. 55–56; approximation class Source: [lean/ExtendedCoerciveChallenge.lean:138-138](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L138).

Field `Breakdown.Coercive.IsSmoothPerturbation.periodic`: The field has period one in normalised time. Paper: (7.4), p. 30; approximation class Source: [lean/ExtendedCoerciveChallenge.lean:139-139](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L139).

Field `Breakdown.Coercive.IsSmoothPerturbation.divergence_free`: The spatial divergence vanishes at every time and point. Paper: (7.4), p. 30; approximation class Source: [lean/ExtendedCoerciveChallenge.lean:140-140](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L140).

Field `Breakdown.Coercive.IsSmoothPerturbation.sixth_power`: Each spatial slice has finite sixth-power integral. Paper: The space X used in (7.4), p. 30; approximation class Source: [lean/ExtendedCoerciveChallenge.lean:141-141](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L141).

Field `Breakdown.Coercive.IsSmoothPerturbation.weighted_finite`: The velocity is square integrable over one period with weight (1+the spatial norm)⁻². Paper: Proposition B.1 approximation step, pp. 55–56; explicit approximation norm Source: [lean/ExtendedCoerciveChallenge.lean:142-142](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L142).

Field `Breakdown.Coercive.IsSmoothPerturbation.derivatives_finite`: Every positive-order spatial derivative has finite squared period integral. Paper: Proposition B.1 approximation step, pp. 55–56; explicit approximation class Source: [lean/ExtendedCoerciveChallenge.lean:143-144](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L143-L144).

Field `Breakdown.Coercive.IsSmoothPerturbation.time_weighted_finite`: The time derivative has finite weighted squared period integral. Paper: Proposition B.1 approximation step, pp. 55–56; explicit approximation class Source: [lean/ExtendedCoerciveChallenge.lean:145-146](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L145-L146).

Field `Breakdown.Coercive.IsSmoothPerturbation.time_derivatives_finite`: Every positive-order spatial derivative of the time derivative is square integrable over a period. Paper: Proposition B.1 approximation step, pp. 55–56; explicit approximation class Source: [lean/ExtendedCoerciveChallenge.lean:147-148](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L147-L148).

Field `Breakdown.Coercive.IsSmoothPerturbation.transport_finite`: The combined time-and-drift term and all its spatial derivatives have finite squared period integral. Paper: (7.1), p. 30; Proposition B.1 approximation step, pp. 55–56 Source: [lean/ExtendedCoerciveChallenge.lean:149-150](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L149-L150).

<a id="182"></a>

### 182. Convergence of smooth approximations

`Breakdown.Coercive.IsSmoothApproximation`: This specifies the convergence used to pass the multiplier identities to a weak perturbation in D_S. The gradients, full Hessians, weighted velocities and combined time-and-drift terms converge in their squared period integrals.

**Source.** [lean/ExtendedCoerciveChallenge.lean:152-163](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L152-L163). Def. **Paper.** Approximation step of Proposition B.1, p. 56

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/ExtendedCoerciveDefs.lean:152-163](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L152-L163).

Encoding for `Breakdown.Coercive.IsSmoothApproximation` (1): The four convergence statements use ENNReal integrals tending to zero, retaining finiteness information instead of converting too early to real numbers.

Encoding for `Breakdown.Coercive.IsSmoothApproximation` (2): The source does not require the approximating sequence itself to carry Γ invariance.

Clause 1 of `Breakdown.Coercive.IsSmoothApproximation`, lines 155-155: Every member of the sequence lies in the smooth approximation class. Paper: Proposition B.1 approximation step, p. 56 Source: [lean/ExtendedCoerciveChallenge.lean:155-155](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L155).

Clause 2 of `Breakdown.Coercive.IsSmoothApproximation`, lines 156-157: The spatial gradients converge in period L². Paper: Proposition B.1 approximation step, p. 56 Source: [lean/ExtendedCoerciveChallenge.lean:156-157](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L156-L157).

Clause 3 of `Breakdown.Coercive.IsSmoothApproximation`, lines 158-159: The full spatial Hessians converge in period L². Paper: Proposition B.1 approximation step, p. 56 Source: [lean/ExtendedCoerciveChallenge.lean:158-159](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L158-L159).

Clause 4 of `Breakdown.Coercive.IsSmoothApproximation`, lines 160-161: The velocities converge in the weighted period L² norm. Paper: Proposition B.1 approximation step, p. 56 Source: [lean/ExtendedCoerciveChallenge.lean:160-161](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L160-L161).

Clause 5 of `Breakdown.Coercive.IsSmoothApproximation`, lines 162-163: The combined time-and-drift terms converge in period L². Paper: Proposition B.1 approximation step, p. 56 Source: [lean/ExtendedCoerciveChallenge.lean:162-163](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L162-L163).

<a id="183"></a>

### 183. Every perturbation can be approximated

`Breakdown.Coercive.SmoothApproximationHolds`: This is the proposition that every weak perturbation admits the smooth approximation just specified. It packages the density step invoked in the proof of Proposition B.1.

**Source.** [lean/ExtendedCoerciveChallenge.lean:165-167](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L165-L167). Def. **Paper.** Approximation step of Proposition B.1, p. 56

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/ExtendedCoerciveDefs.lean:165-167](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L165-L167).

Encoding for `Breakdown.Coercive.SmoothApproximationHolds` (1): A declaration ending in Holds here is a proposition definition, not an added axiom; its proof is supplied elsewhere in the library.

Clause 1 of `Breakdown.Coercive.SmoothApproximationHolds`, lines 165-167: This is the proposition that every weak perturbation admits the smooth approximation just specified. Paper: Approximation step of Proposition B.1, p. 56 Source: [lean/ExtendedCoerciveChallenge.lean:165-167](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L165-L167).

<a id="184"></a>

### 184. Reference field with a weak Hessian

`Breakdown.CoerciveWeak.IsWeakSecondDerivState`: This separates the C¹ reference field Wᵣ from a supplied measurable weak Hessian. It permits the vorticity-gradient terms in (B.16) and (B.18) to be interpreted without demanding a classical Hessian at every spline knot.

**Source.** [lean/ExtendedCoerciveChallenge.lean:175-185](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L175-L185). Structure. **Paper.** §7.2 weak second derivatives, p. 31; reference-profile bounds before (B.16), p. 54; (B.18), p. 55

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/ExtendedCoerciveDefs.lean:175-185](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L175-L185).

Encoding for `Breakdown.CoerciveWeak.IsWeakSecondDerivState` (1): The weak Hessian is linked to every first derivative at every time by integration against spatial tests.

Encoding for `Breakdown.CoerciveWeak.IsWeakSecondDerivState` (2): It has pointwise order-three decay in this representation, a stronger explicit bound than mere local integrability.

Encoding for `Breakdown.CoerciveWeak.IsWeakSecondDerivState` (3): A name containing smooth in this structure refers to ContDiff of order one.

Field `Breakdown.CoerciveWeak.IsWeakSecondDerivState.smooth`: The field is C¹ jointly in normalised time and space. Paper: §7.2, p. 31; weak-Hessian reference-field representation Source: [lean/ExtendedCoerciveChallenge.lean:177-177](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L177).

Field `Breakdown.CoerciveWeak.IsWeakSecondDerivState.periodic`: The field has period one in normalised time. Paper: §7.1, p. 30; reference-profile convention of (7.16), p. 32 Source: [lean/ExtendedCoerciveChallenge.lean:178-178](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L178).

Field `Breakdown.CoerciveWeak.IsWeakSecondDerivState.divergence_free`: The reference field is pointwise solenoidal. Paper: §B.1 reference profiles, pp. 50–52; Proposition B.1, p. 55 Source: [lean/ExtendedCoerciveChallenge.lean:179-179](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L179).

Field `Breakdown.CoerciveWeak.IsWeakSecondDerivState.secondDeriv_measurable`: The supplied Hessian is strongly measurable up to a null set in space-time. Paper: §7.2, p. 31; weak-Hessian representation Source: [lean/ExtendedCoerciveChallenge.lean:180-180](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L180).

Field `Breakdown.CoerciveWeak.IsWeakSecondDerivState.secondDeriv_periodic`: The supplied Hessian is periodic in normalised time. Paper: §7.1, p. 30; weak-Hessian representation Source: [lean/ExtendedCoerciveChallenge.lean:181-181](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L181).

Field `Breakdown.CoerciveWeak.IsWeakSecondDerivState.secondDeriv_weak`: For each time and coordinate direction, the Hessian differentiates the corresponding first derivative weakly. Paper: §7.2, p. 31; weak-Hessian representation Source: [lean/ExtendedCoerciveChallenge.lean:182-183](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L182-L183).

Field `Breakdown.CoerciveWeak.IsWeakSecondDerivState.decay`: The field, gradient and supplied Hessian obey uniform decay of orders one, two and three. Paper: (7.8), p. 31; additional Hessian bound for Proposition B.1 Source: [lean/ExtendedCoerciveChallenge.lean:184-185](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L184-L185).

<a id="185"></a>

### 185. Extract a weak-Hessian profile state

`Breakdown.CoerciveWeak.isWeakSecondDerivState_of_profile`: This fixes an admissible parameter and packages the approximate profile’s regularity, periodicity, divergence and weak-Hessian data. It passes from the family used in Section 7 to the single field required by the multiplier analysis.

**Source.** [lean/ExtendedCoerciveChallenge.lean:187-208](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L187-L208). Theorem with a source proof body. **Paper.** §7.2, p. 31; Proposition B.1, p. 55; packaging helper

**Library.** Implementation source: [lean/Breakdown/Cert/ExtendedCoerciveDefs.lean:187-208](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L187-L208).

Comparison for `Breakdown.CoerciveWeak.isWeakSecondDerivState_of_profile`: This is an implementation helper assembling already supplied hypotheses at one parameter. It has no separately numbered paper theorem.

Clause 1 of `Breakdown.CoerciveWeak.isWeakSecondDerivState_of_profile`, lines 187-201: This fixes an admissible parameter and packages the approximate profile’s regularity, periodicity, divergence and weak-Hessian data. Paper: §7.2, p. 31; Proposition B.1, p. 55; packaging helper Source: [lean/ExtendedCoerciveChallenge.lean:187-201](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L187-L201).

<a id="186"></a>

### 186. Weak Hessian symmetry

`Breakdown.CoerciveWeak.IsWeakSecondDerivState.secondDeriv_symm`: This states that the two spatial derivative slots of the supplied weak Hessian commute almost everywhere. The symmetry permits the integrations by parts behind the stretching and density identities.

**Source.** [lean/ExtendedCoerciveChallenge.lean:210-213](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L210-L213). Readable theorem stub. **Paper.** Weak second derivatives in §7.2, p. 31; proof of Proposition B.1, pp. 55–56; unnumbered analytic identity

**Library.** Implementation source: [lean/Solution.lean:241-244](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Solution.lean#L241-L244).

Encoding for `Breakdown.CoerciveWeak.IsWeakSecondDerivState.secondDeriv_symm` (1): The conclusion is for every fixed time, almost everywhere in space; it does not assert one spatial null set that works for every time.

Encoding for `Breakdown.CoerciveWeak.IsWeakSecondDerivState.secondDeriv_symm` (2): It proves symmetry of the linked weak derivative, not of an arbitrary supplied tensor.

Comparison for `Breakdown.CoerciveWeak.IsWeakSecondDerivState.secondDeriv_symm`: The paper uses the weak-derivative calculus within the multiplier argument without a separate numbered statement. Lean isolates the almost-everywhere symmetry needed for its tensor representation.

Clause 1 of `Breakdown.CoerciveWeak.IsWeakSecondDerivState.secondDeriv_symm`, lines 210-212: This states that the two spatial derivative slots of the supplied weak Hessian commute almost everywhere. Paper: Weak second derivatives in §7.2, p. 31; proof of Proposition B.1, pp. 55–56; unnumbered analytic identity Source: [lean/ExtendedCoerciveChallenge.lean:210-212](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L210-L212).

<a id="187"></a>

### 187. Vorticity gradient from a Hessian

`Breakdown.CoerciveWeak.vortGradMap`: This contracts a supplied Hessian into a linear map representing ∇curl Wᵣ. It provides the operator-norm input used in the weak version of the reference-profile bounds.

**Source.** [lean/ExtendedCoerciveChallenge.lean:215-216](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L215-L216). Def. **Paper.** Reference-profile bounds before (B.16), p. 54; (B.18), p. 55

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/ExtendedCoerciveDefs.lean:210-211](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L210-L211).

Encoding for `Breakdown.CoerciveWeak.vortGradMap` (1): The constructor is algebraic; its interpretation as a classical derivative is supplied by vortGradMap_secondDerivField under C² regularity.

Clause 1 of `Breakdown.CoerciveWeak.vortGradMap`, lines 215-216: This contracts a supplied Hessian into a linear map representing ∇curl Wᵣ. Paper: Reference-profile bounds before (B.16), p. 54; (B.18), p. 55 Source: [lean/ExtendedCoerciveChallenge.lean:215-216](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L215-L216).

<a id="188"></a>

### 188. Stretching with a weak Hessian

`Breakdown.CoerciveWeak.stretchFormWith`: This is the stretching term J of (B.18), using the reference field’s first derivative and the supplied weak Hessian for ∇curl Wᵣ. The three contributions retain the strain term and both vorticity-gradient interactions.

**Source.** [lean/ExtendedCoerciveChallenge.lean:218-224](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L218-L224). Def. **Paper.** (B.18), p. 55

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/ExtendedCoerciveDefs.lean:213-219](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L213-L219).

Encoding for `Breakdown.CoerciveWeak.stretchFormWith` (1): The physical meaning of HW comes from IsWeakSecondDerivState; this expression alone is only an algebraic tensor contraction.

Clause 1 of `Breakdown.CoerciveWeak.stretchFormWith`, lines 218-224: This is the stretching term J of (B.18), using the reference field’s first derivative and the supplied weak Hessian for ∇curl Wᵣ. Paper: (B.18), p. 55 Source: [lean/ExtendedCoerciveChallenge.lean:218-224](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L218-L224).

<a id="189"></a>

### 189. Recover the classical stretching term

`Breakdown.CoerciveWeak.stretchFormWith_secondDerivField`: This identifies the weak-Hessian stretching formula with the earlier formula when HW is chosen as the iterated derivative. The equality follows by unfolding the definitions.

**Source.** [lean/ExtendedCoerciveChallenge.lean:226-227](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L226-L227). Theorem with a source proof body. **Paper.** (B.18), p. 55; representation identity

**Library.** Implementation source: [lean/Breakdown/Cert/ExtendedCoerciveDefs.lean:221-222](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L221-L222).

Comparison for `Breakdown.CoerciveWeak.stretchFormWith_secondDerivField`: This is a definitional identity between two Lean representations of J. It is not a separate assertion made by the paper.

Clause 1 of `Breakdown.CoerciveWeak.stretchFormWith_secondDerivField`, lines 226-227: This identifies the weak-Hessian stretching formula with the earlier formula when HW is chosen as the iterated derivative. Paper: (B.18), p. 55; representation identity Source: [lean/ExtendedCoerciveChallenge.lean:226-227](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L226-L227).

<a id="190"></a>

### 190. Recover the classical curl derivative

`Breakdown.CoerciveWeak.vortGradMap_secondDerivField`: This identifies the tensor contraction with the actual derivative of curl Wᵣ for a C² field. It is the analytic bridge needed when replacing the classical supremum by the weak-Hessian one.

**Source.** [lean/ExtendedCoerciveChallenge.lean:229-232](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L229-L232). Readable theorem stub. **Paper.** Reference-profile bounds before (B.16), p. 54; (B.18), p. 55; derivative identity

**Library.** Implementation source: [lean/Solution.lean:246-249](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Solution.lean#L246-L249).

Encoding for `Breakdown.CoerciveWeak.vortGradMap_secondDerivField` (1): C² regularity is an explicit hypothesis, so the identity does not infer a genuine second derivative from a total fderiv value alone.

Comparison for `Breakdown.CoerciveWeak.vortGradMap_secondDerivField`: The paper writes ∇curl Wᵣ directly. Lean proves the coordinate-tensor identity that justifies that notation for its classical derivative representation.

Clause 1 of `Breakdown.CoerciveWeak.vortGradMap_secondDerivField`, lines 229-231: This identifies the tensor contraction with the actual derivative of curl Wᵣ for a C² field. Paper: Reference-profile bounds before (B.16), p. 54; (B.18), p. 55; derivative identity Source: [lean/ExtendedCoerciveChallenge.lean:229-231](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L229-L231).

<a id="191"></a>

### 191. Positive part of the weak density

`Breakdown.CoerciveWeak.densityPosWith`: This sums the positive parts of the whole mode densities Iι and of the stretching term J. It is the integrand defining I⁺ for the weak-Hessian multiplier theorem.

**Source.** [lean/ExtendedCoerciveChallenge.lean:235-240](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L235-L240). Def. **Paper.** (B.16), p. 54; definition of I⁺ after (B.18), p. 55

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/ExtendedCoerciveDefs.lean:224-229](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L224-L229).

Encoding for `Breakdown.CoerciveWeak.densityPosWith` (1): The sum and its integral take values in ENNReal, so divergence remains visible as infinity.

Encoding for `Breakdown.CoerciveWeak.densityPosWith` (2): The positive part is taken after each complete mode density is formed, rather than separately on each coefficient term.

Clause 1 of `Breakdown.CoerciveWeak.densityPosWith`, lines 235-240: This sums the positive parts of the whole mode densities Iι and of the stretching term J. Paper: (B.16), p. 54; definition of I⁺ after (B.18), p. 55 Source: [lean/ExtendedCoerciveChallenge.lean:235-240](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L235-L240).

<a id="192"></a>

### 192. Negative part of the weak density

`Breakdown.CoerciveWeak.densityNegWith`: This sums the negative parts of the whole mode densities Iι and of J. It is the integrand defining I⁻, whose finiteness is needed before the signed density becomes an ordinary real integral.

**Source.** [lean/ExtendedCoerciveChallenge.lean:242-247](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L242-L247). Def. **Paper.** Definition of I⁻ after (B.18), p. 55; (B.21), p. 56

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/ExtendedCoerciveDefs.lean:231-236](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L231-L236).

Encoding for `Breakdown.CoerciveWeak.densityNegWith` (1): ENNReal.ofReal of the negated real expression is its negative part; no cancellation of infinities is built into the definition.

Clause 1 of `Breakdown.CoerciveWeak.densityNegWith`, lines 242-247: This sums the negative parts of the whole mode densities Iι and of J. Paper: Definition of I⁻ after (B.18), p. 55; (B.21), p. 56 Source: [lean/ExtendedCoerciveChallenge.lean:242-247](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L242-L247).

<a id="193"></a>

### 193. Recover the classical positive density

`Breakdown.CoerciveWeak.densityPosWith_secondDerivField`: This identifies the pointwise integrand defining I⁺ with its earlier encoding when the supplied Hessian is the iterated derivative. It follows from the definition of the stretching term.

**Source.** [lean/ExtendedCoerciveChallenge.lean:249-252](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L249-L252). Theorem with a source proof body. **Paper.** Definition of I⁺ after (B.18), p. 55; representation identity

**Library.** Implementation source: [lean/Breakdown/Cert/ExtendedCoerciveDefs.lean:238-241](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L238-L241).

Comparison for `Breakdown.CoerciveWeak.densityPosWith_secondDerivField`: This is a definitional compatibility statement between two Lean encodings of the positive density, with no separately numbered paper theorem.

Clause 1 of `Breakdown.CoerciveWeak.densityPosWith_secondDerivField`, lines 249-251: This identifies the pointwise integrand defining I⁺ with its earlier encoding when the supplied Hessian is the iterated derivative. Paper: Definition of I⁺ after (B.18), p. 55; representation identity Source: [lean/ExtendedCoerciveChallenge.lean:249-251](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L249-L251).

<a id="194"></a>

### 194. Recover the classical negative density

`Breakdown.CoerciveWeak.densityNegWith_secondDerivField`: This identifies the pointwise integrand defining I⁻ with its earlier encoding when the supplied Hessian is the iterated derivative. The identity preserves the separate treatment of negative parts.

**Source.** [lean/ExtendedCoerciveChallenge.lean:254-257](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L254-L257). Theorem with a source proof body. **Paper.** Definition of I⁻ after (B.18), p. 55; representation identity

**Library.** Implementation source: [lean/Breakdown/Cert/ExtendedCoerciveDefs.lean:243-246](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L243-L246).

Comparison for `Breakdown.CoerciveWeak.densityNegWith_secondDerivField`: This is a definitional compatibility statement between two Lean encodings of the negative density, with no separately numbered paper theorem.

Clause 1 of `Breakdown.CoerciveWeak.densityNegWith_secondDerivField`, lines 254-256: This identifies the pointwise integrand defining I⁻ with its earlier encoding when the supplied Hessian is the iterated derivative. Paper: Definition of I⁻ after (B.18), p. 55; representation identity Source: [lean/ExtendedCoerciveChallenge.lean:254-256](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L254-L256).

<a id="195"></a>

### 195. Admissible multiplier weights

`Breakdown.CoerciveWeak.IsAdmissibleWeak`: This states the weight, harmonic and reference-profile bounds used for Proposition B.1 with a supplied weak Hessian. The coefficients are functions on all integer mode pairs, and the required weight signs, symmetries and decay are explicit.

**Source.** [lean/ExtendedCoerciveChallenge.lean:259-329](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L259-L329). Structure. **Paper.** §B.2, pp. 53–55; (B.15)–(B.19), pp. 54–55

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/ExtendedCoerciveDefs.lean:248-318](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L248-L318).

Encoding for `Breakdown.CoerciveWeak.IsAdmissibleWeak` (1): This contract does not by itself link HW to W; the multiplier theorem also requires IsWeakSecondDerivState.

Encoding for `Breakdown.CoerciveWeak.IsAdmissibleWeak` (2): The coercivity coefficient c is any number in (0,1) here; the printed choice is 3/50.

Encoding for `Breakdown.CoerciveWeak.IsAdmissibleWeak` (3): A finite class type cannot be empty once a PieceWeights record is supplied, because classOf maps every integer pair into it.

Encoding for `Breakdown.CoerciveWeak.IsAdmissibleWeak` (4): The harmonic set contains zero and is closed under negation; finite piece families may still be empty.

Encoding for `Breakdown.CoerciveWeak.IsAdmissibleWeak` (5): Each frequency lower bound is uniform over its selected set. Together with oddness of the frame frequency, it excludes overlap with the negative set.

Encoding for `Breakdown.CoerciveWeak.IsAdmissibleWeak` (6): Lipschitz weights have weak derivatives almost everywhere; the surrounding proof supplies the analytic interpretation of their total fderiv values.

Field `Breakdown.CoerciveWeak.IsAdmissibleWeak.finite_classes`: The class type used for Dι and Zι is finite. Paper: Finite harmonic classes in §B.2, p. 53; preceding (B.14), p. 54 Source: [lean/ExtendedCoerciveChallenge.lean:262-262](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L262).

Field `Breakdown.CoerciveWeak.IsAdmissibleWeak.c_pos`: The coercivity coefficient c is strictly positive. Paper: (B.16), p. 54; free version of the printed coefficient 3/50 Source: [lean/ExtendedCoerciveChallenge.lean:263-263](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L263).

Field `Breakdown.CoerciveWeak.IsAdmissibleWeak.c_lt_one`: The coercivity coefficient c is less than one. Paper: (B.16), p. 54; free version of the printed coefficient 3/50 Source: [lean/ExtendedCoerciveChallenge.lean:264-264](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L264).

Field `Breakdown.CoerciveWeak.IsAdmissibleWeak.cμ_pos`: The retained frequency-seminorm fraction cμ is positive. Paper: §B.2 weight setup, p. 53; preceding (B.14), p. 54 Source: [lean/ExtendedCoerciveChallenge.lean:265-265](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L265).

Field `Breakdown.CoerciveWeak.IsAdmissibleWeak.cμ_lt_one`: The retained fraction cμ is less than one. Paper: §B.2 weight setup, p. 53; preceding (B.14), p. 54 Source: [lean/ExtendedCoerciveChallenge.lean:266-266](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L266).

Field `Breakdown.CoerciveWeak.IsAdmissibleWeak.period_pos`: The period in the rotating-frame frequency is positive. Paper: (B.15), p. 54; §7.2, p. 31 Source: [lean/ExtendedCoerciveChallenge.lean:267-267](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L267).

Field `Breakdown.CoerciveWeak.IsAdmissibleWeak.weight_pos`: The energy-weight lower bound w∗ is positive. Paper: (7.14), p. 32; Proposition B.1, p. 55 Source: [lean/ExtendedCoerciveChallenge.lean:268-268](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L268).

Field `Breakdown.CoerciveWeak.IsAdmissibleWeak.weight_lower`: The energy weight is at least w∗ pointwise. Paper: (7.14), p. 32; Proposition B.1, p. 55 Source: [lean/ExtendedCoerciveChallenge.lean:269-269](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L269).

Field `Breakdown.CoerciveWeak.IsAdmissibleWeak.weight_measurable`: The energy weight is measurable. Paper: §7.3 before (7.14), p. 32 Source: [lean/ExtendedCoerciveChallenge.lean:270-270](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L270).

Field `Breakdown.CoerciveWeak.IsAdmissibleWeak.weight_axi`: The energy weight is invariant under rotations about the distinguished axis. Paper: Axisymmetric coefficient convention of §B.2, pp. 53–54 Source: [lean/ExtendedCoerciveChallenge.lean:271-271](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L271).

Field `Breakdown.CoerciveWeak.IsAdmissibleWeak.harmonics_neg`: Every retained reference harmonic has its negative in the same finite set. Paper: Reference-profile harmonic set before (B.16), p. 54 Source: [lean/ExtendedCoerciveChallenge.lean:272-272](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L272).

Field `Breakdown.CoerciveWeak.IsAdmissibleWeak.harmonics_zero`: The finite reference harmonic set contains the zero mode. Paper: Reference-profile harmonic set before (B.16), p. 54 Source: [lean/ExtendedCoerciveChallenge.lean:273-273](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L273).

Field `Breakdown.CoerciveWeak.IsAdmissibleWeak.harmonics_span`: The real parts of the retained velocity modes reconstruct Wᵣ exactly. Paper: Reference-profile harmonic set before (B.16), p. 54 Source: [lean/ExtendedCoerciveChallenge.lean:274-274](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L274).

Field `Breakdown.CoerciveWeak.IsAdmissibleWeak.ampW_ge`: The supplied velocity-mode amplitude majorant dominates every retained mode at every time and point. Paper: Reference-profile bounds before (B.16), p. 54 Source: [lean/ExtendedCoerciveChallenge.lean:275-275](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L275).

Field `Breakdown.CoerciveWeak.IsAdmissibleWeak.ampGradW_ge`: The gradient-mode amplitude majorant dominates the corresponding derivative mode. Paper: Reference-profile bounds before (B.16), p. 54 Source: [lean/ExtendedCoerciveChallenge.lean:276-277](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L276-L277).

Field `Breakdown.CoerciveWeak.IsAdmissibleWeak.ampVort_ge`: The vorticity-mode amplitude majorant dominates the curl of the gradient mode. Paper: Reference-profile bounds before (B.16), p. 54 Source: [lean/ExtendedCoerciveChallenge.lean:278-279](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L278-L279).

Field `Breakdown.CoerciveWeak.IsAdmissibleWeak.ampGradVort_ge`: The vorticity-gradient amplitude majorant dominates the curl contraction of each supplied Hessian mode. Paper: Reference-profile bounds before (B.16), p. 54; weak-Hessian representation Source: [lean/ExtendedCoerciveChallenge.lean:280-281](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L280-L281).

Field `Breakdown.CoerciveWeak.IsAdmissibleWeak.supVort_ge`: The vorticity magnitude is bounded for every time, angle and spatial point. Paper: Reference-profile bounds before (B.16), p. 54 Source: [lean/ExtendedCoerciveChallenge.lean:282-282](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L282).

Field `Breakdown.CoerciveWeak.IsAdmissibleWeak.supGradVort_ge`: The operator norm of the contracted weak Hessian is bounded for every time, angle and point. Paper: Reference-profile bounds before (B.16), p. 54; weak-Hessian representation Source: [lean/ExtendedCoerciveChallenge.lean:283-284](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L283-L284).

Field `Breakdown.CoerciveWeak.IsAdmissibleWeak.epsSpeed_ge`: Each λ piece bounds the reference transport speed in its rotating frame. Paper: Transport bounds of §B.2, p. 53 Source: [lean/ExtendedCoerciveChallenge.lean:285-287](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L285-L287).

Field `Breakdown.CoerciveWeak.IsAdmissibleWeak.muSpeed_ge`: Each μ piece bounds the reference transport speed in its rotating frame. Paper: Transport bounds of §B.2, p. 53 Source: [lean/ExtendedCoerciveChallenge.lean:288-290](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L288-L290).

Field `Breakdown.CoerciveWeak.IsAdmissibleWeak.eps_oneSided`: Every λ piece has one positive lower bound for its frame frequencies on Nₚ. Paper: Admissibility paragraph before (B.19), p. 55 Source: [lean/ExtendedCoerciveChallenge.lean:291-291](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L291).

Field `Breakdown.CoerciveWeak.IsAdmissibleWeak.mu_oneSided`: Every μ piece has one positive lower bound for its frame frequencies on Nₚ. Paper: Admissibility paragraph before (B.19), p. 55 Source: [lean/ExtendedCoerciveChallenge.lean:292-292](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L292).

Field `Breakdown.CoerciveWeak.IsAdmissibleWeak.mu_ratio`: The squared sum of μ weights is bounded by ratio times the weighted frequency sum. Paper: (B.19), third inequality, p. 55 Source: [lean/ExtendedCoerciveChallenge.lean:293-294](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L293-L294).

Field `Breakdown.CoerciveWeak.IsAdmissibleWeak.ratio_nonneg`: The common bound nμ is nonnegative. Paper: (B.19), p. 55 Source: [lean/ExtendedCoerciveChallenge.lean:295-295](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L295).

Field `Breakdown.CoerciveWeak.IsAdmissibleWeak.eps_wt_nonneg`: Every λ weight is nonnegative at every point. Paper: Weights of §B.2, p. 53 Source: [lean/ExtendedCoerciveChallenge.lean:296-296](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L296).

Field `Breakdown.CoerciveWeak.IsAdmissibleWeak.mu_wt_nonneg`: Every μ weight is nonnegative at every point. Paper: Weights of §B.2, p. 53 Source: [lean/ExtendedCoerciveChallenge.lean:297-297](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L297).

Field `Breakdown.CoerciveWeak.IsAdmissibleWeak.eps_increment`: Each λ weight has a finite Lipschitz constant. Paper: Regularity of the weights in §B.2, p. 53 Source: [lean/ExtendedCoerciveChallenge.lean:298-298](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L298).

Field `Breakdown.CoerciveWeak.IsAdmissibleWeak.mu_increment`: Each μ weight has a finite Lipschitz constant. Paper: Regularity of the weights in §B.2, p. 53 Source: [lean/ExtendedCoerciveChallenge.lean:299-299](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L299).

Field `Breakdown.CoerciveWeak.IsAdmissibleWeak.eps_axi`: Each λ weight is invariant under axial rotations. Paper: Axisymmetry of the weights in §B.2, p. 53 Source: [lean/ExtendedCoerciveChallenge.lean:300-300](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L300).

Field `Breakdown.CoerciveWeak.IsAdmissibleWeak.mu_axi`: Each μ weight is invariant under axial rotations. Paper: Axisymmetry of the weights in §B.2, p. 53 Source: [lean/ExtendedCoerciveChallenge.lean:301-301](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L301).

Field `Breakdown.CoerciveWeak.IsAdmissibleWeak.eps_sum_le`: The sum of λ weights is bounded by nλ. Paper: (B.19), first inequality, p. 55 Source: [lean/ExtendedCoerciveChallenge.lean:302-302](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L302).

Field `Breakdown.CoerciveWeak.IsAdmissibleWeak.eps_grad_sum_le`: The sum of norms of λ-weight gradients is bounded by n∇λ. Paper: (B.19), second inequality, p. 55 Source: [lean/ExtendedCoerciveChallenge.lean:303-303](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L303).

Field `Breakdown.CoerciveWeak.IsAdmissibleWeak.eps_decay`: The product of spatial radius and each λ weight has a common finite bound. Paper: Decay of the weights in §B.2, p. 53 Source: [lean/ExtendedCoerciveChallenge.lean:304-304](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L304).

Field `Breakdown.CoerciveWeak.IsAdmissibleWeak.mu_decay`: Each μ weight, its radius-squared multiple and its radius-weighted gradient have a common finite bound. Paper: Decay of the weights in §B.2, p. 53 Source: [lean/ExtendedCoerciveChallenge.lean:305-306](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L305-L306).

Field `Breakdown.CoerciveWeak.IsAdmissibleWeak.eps_free_pos`: All eight λ-piece allocation, length, splitting and scale functions are strictly positive. Paper: Positive auxiliary functions in §B.2, p. 53; Young-error allocation in the proof of Proposition B.1, p. 56; yielding (B.20), p. 55 Source: [lean/ExtendedCoerciveChallenge.lean:307-309](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L307-L309).

Field `Breakdown.CoerciveWeak.IsAdmissibleWeak.mu_free_pos`: The μ-piece share and splitting functions are strictly positive. Paper: Positive auxiliary functions in §B.2, p. 53; Young-error allocation in the proof of Proposition B.1, p. 56; yielding (B.20), p. 55 Source: [lean/ExtendedCoerciveChallenge.lean:310-310](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L310).

Field `Breakdown.CoerciveWeak.IsAdmissibleWeak.mu_eta_pos`: Each μ-piece Young-inequality parameter η is positive. Paper: Positive auxiliary number in §B.2, p. 53; Young-error allocation in the proof of Proposition B.1, p. 56; yielding (B.20), p. 55 Source: [lean/ExtendedCoerciveChallenge.lean:311-311](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L311).

Field `Breakdown.CoerciveWeak.IsAdmissibleWeak.eps_free_measurable`: Every λ-piece allocation function is measurable. Paper: Auxiliary-function form in §B.2, p. 53 Source: [lean/ExtendedCoerciveChallenge.lean:312-314](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L312-L314).

Field `Breakdown.CoerciveWeak.IsAdmissibleWeak.mu_free_measurable`: The μ-piece share and splitting functions are measurable. Paper: Auxiliary-function form in §B.2, p. 53 Source: [lean/ExtendedCoerciveChallenge.lean:315-315](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L315).

Field `Breakdown.CoerciveWeak.IsAdmissibleWeak.eps_free_axi`: All λ-piece allocation functions are invariant under axial rotations. Paper: Auxiliary-function axisymmetry in §B.2, p. 53 Source: [lean/ExtendedCoerciveChallenge.lean:316-318](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L316-L318).

Field `Breakdown.CoerciveWeak.IsAdmissibleWeak.mu_free_axi`: The μ-piece share and splitting functions are invariant under axial rotations. Paper: Auxiliary-function axisymmetry in §B.2, p. 53 Source: [lean/ExtendedCoerciveChallenge.lean:319-319](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L319).

Field `Breakdown.CoerciveWeak.IsAdmissibleWeak.convD_even`: The D coefficient is unchanged when a mode is replaced by its negative. Paper: Harmonic classes in §B.2, p. 53; preceding (B.14), p. 54 Source: [lean/ExtendedCoerciveChallenge.lean:320-320](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L320).

Field `Breakdown.CoerciveWeak.IsAdmissibleWeak.convZ_even`: The Z coefficient is unchanged when a mode is replaced by its negative. Paper: Harmonic classes in §B.2, p. 53; preceding (B.14), p. 54 Source: [lean/ExtendedCoerciveChallenge.lean:321-321](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L321).

Field `Breakdown.CoerciveWeak.IsAdmissibleWeak.convD_smooth`: Each class function D is C² in space. Paper: Regularity of D in §B.2, p. 53 Source: [lean/ExtendedCoerciveChallenge.lean:322-322](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L322).

Field `Breakdown.CoerciveWeak.IsAdmissibleWeak.convZ_smooth`: Each class function Z is C² in space. Paper: Regularity of Z in §B.2, p. 53 Source: [lean/ExtendedCoerciveChallenge.lean:323-323](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L323).

Field `Breakdown.CoerciveWeak.IsAdmissibleWeak.convD_nonneg`: Each D class function is nonnegative. Paper: Sign of D in §B.2, p. 53 Source: [lean/ExtendedCoerciveChallenge.lean:324-324](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L324).

Field `Breakdown.CoerciveWeak.IsAdmissibleWeak.convD_axi`: Each D class function is invariant under axial rotations. Paper: Axisymmetric class functions in §B.2, p. 53 Source: [lean/ExtendedCoerciveChallenge.lean:325-325](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L325).

Field `Breakdown.CoerciveWeak.IsAdmissibleWeak.convZ_axi`: Each Z class function is invariant under axial rotations. Paper: Axisymmetric class functions in §B.2, p. 53 Source: [lean/ExtendedCoerciveChallenge.lean:326-326](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L326).

Field `Breakdown.CoerciveWeak.IsAdmissibleWeak.convD_decay`: D and its first two derivatives have the stated radius-weighted finite bounds. Paper: Coefficient regularity and decay in §B.2, pp. 53–55 Source: [lean/ExtendedCoerciveChallenge.lean:327-327](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L327).

Field `Breakdown.CoerciveWeak.IsAdmissibleWeak.convZ_decay`: Z and its first two derivatives have finite bounds with powers of one plus radius. Paper: Coefficient regularity and decay in §B.2, pp. 53–55 Source: [lean/ExtendedCoerciveChallenge.lean:328-328](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L328).

Field `Breakdown.CoerciveWeak.IsAdmissibleWeak.conv_le`: D plus the allocated Hessian-error share stays below one, leaving a nonnegative vorticity-gradient coefficient. Paper: Nonnegativity of the primed order-two coefficient before (B.19), p. 55 Source: [lean/ExtendedCoerciveChallenge.lean:329-329](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L329).

<a id="196"></a>

### 196. Convert classical admissibility

`Breakdown.CoerciveWeak.isAdmissibleWeak_of_isAdmissible`: This converts the classical multiplier-weight conditions into the weak-Hessian conditions for a C² reference field. The vorticity-gradient operator bound is transported through the curl-derivative identity. Its library counterpart takes the curl-derivative identity as an explicit premise, which the library proves separately.

**Source.** [lean/ExtendedCoerciveChallenge.lean:332-340](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L332-L340). Theorem with a source proof body. **Paper.** Admissibility before (B.19), p. 55; representation conversion

**Library.** Implementation source: [lean/Breakdown/Cert/ExtendedCoerciveAssembly.lean:19-27](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveAssembly.lean#L19-L27). This helper has an extra derivative-identity premise; the proved dependency is recorded in `library_locations.json`.

Encoding for `Breakdown.CoerciveWeak.isAdmissibleWeak_of_isAdmissible` (1): The *Holds helper in Breakdown/Cert/ExtendedCoerciveAssembly.lean adds VortGradMapSecondDerivFieldHolds as a premise; Breakdown.CoerciveWeak.vortGradMapSecondDerivFieldHolds_proof supplies it in Breakdown/Cert/ExtendedCoerciveVortGradMap.lean:51–62. This is a conditional helper plus a proved bridge, rather than a simple rename.

Comparison for `Breakdown.CoerciveWeak.isAdmissibleWeak_of_isAdmissible`: The paper has one admissibility formulation. This Lean helper relates two representations and makes the C² condition for the classical derivative explicit.

Clause 1 of `Breakdown.CoerciveWeak.isAdmissibleWeak_of_isAdmissible`, lines 332-336: This converts the classical multiplier-weight conditions into the weak-Hessian conditions for a C² reference field. Paper: Admissibility before (B.19), p. 55; representation conversion Source: [lean/ExtendedCoerciveChallenge.lean:332-336](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L332-L336).

<a id="197"></a>

### 197. Weak multiplier-density statement

`Breakdown.CoerciveWeak.PieceMultiplierDensityWeakHolds`: This packages the weak-Hessian version of Proposition B.1: a multiplier exists, the perturbation has finite frequency seminorm, the multiplier has the stated H-norm bound, and its pairing satisfies the signed density inequality. The coercivity coefficient c remains a parameter in this formulation.

**Source.** [lean/ExtendedCoerciveChallenge.lean:342-365](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L342-L365). Def. **Paper.** Proposition B.1 and (B.20), p. 55

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/ExtendedCoerciveDefs.lean:321-344](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L321-L344).

Encoding for `Breakdown.CoerciveWeak.PieceMultiplierDensityWeakHolds` (1): The density inequality stays in ENNReal positive and negative parts; full negative-density finiteness is supplied later by RowRestClause.

Encoding for `Breakdown.CoerciveWeak.PieceMultiplierDensityWeakHolds` (2): The explicit seminorm finiteness clause is needed before its toReal value is read as an ordinary squared norm.

Encoding for `Breakdown.CoerciveWeak.PieceMultiplierDensityWeakHolds` (3): A Holds definition is a proposition, whose proof is supplied by pieceMultiplierDensityWeak.

Clause 1 of `Breakdown.CoerciveWeak.PieceMultiplierDensityWeakHolds`, lines 343-357: Admissible weights, a linked weak-Hessian reference field, finite forcing fields and an admissible linearised equation. Paper: Hypotheses of Proposition B.1, p. 55; low-regularity representation Source: [lean/ExtendedCoerciveChallenge.lean:343-357](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L343-L357).

Clause 2 of `Breakdown.CoerciveWeak.PieceMultiplierDensityWeakHolds`, lines 358-361: There is an L² multiplier, the perturbation has finite frequency seminorm, and the quantitative multiplier bound holds. Paper: Multiplier existence and norm bound in Proposition B.1, p. 55 Source: [lean/ExtendedCoerciveChallenge.lean:358-361](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L358-L361).

Clause 3 of `Breakdown.CoerciveWeak.PieceMultiplierDensityWeakHolds`, lines 362-365: The multiplier gap bounds the signed mode-and-stretching density without subtracting infinities. Paper: (B.20), p. 55; signed implementation form Source: [lean/ExtendedCoerciveChallenge.lean:362-365](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L362-L365).

<a id="198"></a>

### 198. Weak multiplier-density inequality

`Breakdown.CoerciveWeak.pieceMultiplierDensityWeak`: This states the assembled multiplier theorem for the weak-Hessian representation. It supplies the analytic Proposition B.1 step used by the subsequent coercivity conversion.

**Source.** [lean/ExtendedCoerciveChallenge.lean:367-368](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L367-L368). Readable theorem stub. **Paper.** Proposition B.1 and (B.20), p. 55

**Library.** Implementation source: [lean/Solution.lean:251-252](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Solution.lean#L251-L252).

Encoding for `Breakdown.CoerciveWeak.pieceMultiplierDensityWeak` (1): This proves a conditional analytic implication; it does not evaluate any numerical certificate or verify the remaining row-rest bound.

Comparison for `Breakdown.CoerciveWeak.pieceMultiplierDensityWeak`: The paper specialises the coefficient to 3/50 and describes particular harmonic and weight data. This theorem uses general admissible weights and explicit weak-Hessian representatives, with a signed ENNReal formulation of the density bound.

Clause 1 of `Breakdown.CoerciveWeak.pieceMultiplierDensityWeak`, lines 367-367: This states the assembled multiplier theorem for the weak-Hessian representation. Paper: Proposition B.1 and (B.20), p. 55 Source: [lean/ExtendedCoerciveChallenge.lean:367-367](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L367).

<a id="199"></a>

### 199. Weak vorticity-gradient bound

`Breakdown.CoerciveWeak.vortGradSupWith`: This takes the time-and-angle supremum of the operator norm obtained by contracting the supplied Hessian. It is the weak counterpart of the ∇curl Wᵣ bound entering the λ block errors.

**Source.** [lean/ExtendedCoerciveChallenge.lean:371-372](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L371-L372). Def. **Paper.** Reference-profile bounds before (B.16), p. 54; proof of Proposition B.1, pp. 55–56

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/ExtendedCoerciveDefs.lean:346-347](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L346-L347).

Encoding for `Breakdown.CoerciveWeak.vortGradSupWith` (1): The real supremum is justified by the pointwise supGradVort_ge admissibility bound.

Encoding for `Breakdown.CoerciveWeak.vortGradSupWith` (2): The link between this tensor and the derivative of the field is a separate IsWeakSecondDerivState condition.

Clause 1 of `Breakdown.CoerciveWeak.vortGradSupWith`, lines 371-372: This takes the time-and-angle supremum of the operator norm obtained by contracting the supplied Hessian. Paper: Reference-profile bounds before (B.16), p. 54; proof of Proposition B.1, pp. 55–56 Source: [lean/ExtendedCoerciveChallenge.lean:371-372](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L371-L372).

<a id="200"></a>

### 200. Recover the classical gradient bound

`Breakdown.CoerciveWeak.vortGradSupWith_secondDerivField`: This identifies the weak-Hessian vorticity-gradient supremum with the earlier classical supremum for a C² reference field. It transports the derivative identity through the real supremum. Its library counterpart takes the curl-derivative identity as an explicit premise, which the library proves separately.

**Source.** [lean/ExtendedCoerciveChallenge.lean:374-378](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L374-L378). Theorem with a source proof body. **Paper.** Reference-profile bounds before (B.16), p. 54; representation identity

**Library.** Implementation source: [lean/Breakdown/Cert/ExtendedCoerciveAssembly.lean:29-33](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveAssembly.lean#L29-L33). This helper has an extra derivative-identity premise; the proved dependency is recorded in `library_locations.json`.

Encoding for `Breakdown.CoerciveWeak.vortGradSupWith_secondDerivField` (1): The *Holds helper in Breakdown/Cert/ExtendedCoerciveAssembly.lean adds VortGradMapSecondDerivFieldHolds as a premise; Breakdown.CoerciveWeak.vortGradMapSecondDerivFieldHolds_proof supplies it in Breakdown/Cert/ExtendedCoerciveVortGradMap.lean:51–62. This is a conditional helper plus a proved bridge, rather than a simple rename.

Comparison for `Breakdown.CoerciveWeak.vortGradSupWith_secondDerivField`: This is compatibility between two formal representations of the same reference-profile bound, conditional on C² regularity. The paper does not state a separate theorem for this conversion.

Clause 1 of `Breakdown.CoerciveWeak.vortGradSupWith_secondDerivField`, lines 374-376: This identifies the weak-Hessian vorticity-gradient supremum with the earlier classical supremum for a C² reference field. Paper: Reference-profile bounds before (B.16), p. 54; representation identity Source: [lean/ExtendedCoerciveChallenge.lean:374-376](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L374-L376).

<a id="201"></a>

### 201. Weak vorticity cross-mode errors

`Breakdown.CoerciveWeak.pieceEpsRestModeWith`: This is the λ-piece cross-mode remainder with the supplied weak Hessian used for the vorticity-gradient mode. Its other three reference-field amplitudes are unchanged.

**Source.** [lean/ExtendedCoerciveChallenge.lean:380-392](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L380-L392). Def. **Paper.** Error terms in (B.16), p. 54; proof of Proposition B.1, pp. 55–56

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/ExtendedCoerciveDefs.lean:349-361](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L349-L361).

Clause 1 of `Breakdown.CoerciveWeak.pieceEpsRestModeWith`, lines 380-392: This is the λ-piece cross-mode remainder with the supplied weak Hessian used for the vorticity-gradient mode. Paper: Error terms in (B.16), p. 54; proof of Proposition B.1, pp. 55–56 Source: [lean/ExtendedCoerciveChallenge.lean:380-392](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L380-L392).

<a id="202"></a>

### 202. Recover classical cross-mode errors

`Breakdown.CoerciveWeak.pieceEpsRestModeWith_secondDerivField`: This identifies the weak λ-piece mode remainder with the earlier one when the supplied Hessian is the iterated derivative. The equality is definitional and has no additional smoothness hypothesis.

**Source.** [lean/ExtendedCoerciveChallenge.lean:394-396](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L394-L396). Theorem with a source proof body. **Paper.** Error terms in (B.16), p. 54; representation identity

**Library.** Implementation source: [lean/Breakdown/Cert/ExtendedCoerciveDefs.lean:363-365](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L363-L365).

Comparison for `Breakdown.CoerciveWeak.pieceEpsRestModeWith_secondDerivField`: This is an identity between two Lean formulas, not an additional analytic estimate in the paper. It substitutes the classical Hessian without changing the remainder.

Clause 1 of `Breakdown.CoerciveWeak.pieceEpsRestModeWith_secondDerivField`, lines 394-396: This identifies the weak λ-piece mode remainder with the earlier one when the supplied Hessian is the iterated derivative. Paper: Error terms in (B.16), p. 54; representation identity Source: [lean/ExtendedCoerciveChallenge.lean:394-396](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L394-L396).

<a id="203"></a>

### 203. Weak vorticity block errors

`Breakdown.CoerciveWeak.pieceEpsBlockWith`: This is the λ-piece block remainder with vortGradSupWith supplying the weak vorticity-gradient bound. The transport, rotation, weight-gradient and vorticity terms retain their previous form.

**Source.** [lean/ExtendedCoerciveChallenge.lean:398-412](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L398-L412). Def. **Paper.** Error terms in (B.16), p. 54; proof of Proposition B.1, pp. 55–56

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/ExtendedCoerciveDefs.lean:367-381](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L367-L381).

Encoding for `Breakdown.CoerciveWeak.pieceEpsBlockWith` (1): Fourier summability and the pointwise majorants justify the real piece norms and suprema at the estimate’s use.

Clause 1 of `Breakdown.CoerciveWeak.pieceEpsBlockWith`, lines 398-412: This is the λ-piece block remainder with vortGradSupWith supplying the weak vorticity-gradient bound. Paper: Error terms in (B.16), p. 54; proof of Proposition B.1, pp. 55–56 Source: [lean/ExtendedCoerciveChallenge.lean:398-412](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L398-L412).

<a id="204"></a>

### 204. Recover classical vorticity blocks

`Breakdown.CoerciveWeak.pieceEpsBlockWith_secondDerivField`: This identifies the weak λ-piece block formula with the earlier classical formula for a C² reference field. C² is used to identify the vorticity-gradient supremum. Its library counterpart takes the curl-derivative identity as an explicit premise, which the library proves separately.

**Source.** [lean/ExtendedCoerciveChallenge.lean:414-418](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L414-L418). Theorem with a source proof body. **Paper.** Error terms in (B.16), p. 54; representation identity

**Library.** Implementation source: [lean/Breakdown/Cert/ExtendedCoerciveAssembly.lean:35-39](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveAssembly.lean#L35-L39). This helper has an extra derivative-identity premise; the proved dependency is recorded in `library_locations.json`.

Encoding for `Breakdown.CoerciveWeak.pieceEpsBlockWith_secondDerivField` (1): The *Holds helper in Breakdown/Cert/ExtendedCoerciveAssembly.lean adds VortGradMapSecondDerivFieldHolds as a premise; Breakdown.CoerciveWeak.vortGradMapSecondDerivFieldHolds_proof supplies it in Breakdown/Cert/ExtendedCoerciveVortGradMap.lean:51–62. This is a conditional helper plus a proved bridge, rather than a simple rename.

Comparison for `Breakdown.CoerciveWeak.pieceEpsBlockWith_secondDerivField`: This is a representation-conversion lemma with an explicit C² hypothesis, rather than a separately printed paper estimate.

Clause 1 of `Breakdown.CoerciveWeak.pieceEpsBlockWith_secondDerivField`, lines 414-416: This identifies the weak λ-piece block formula with the earlier classical formula for a C² reference field. Paper: Error terms in (B.16), p. 54; representation identity Source: [lean/ExtendedCoerciveChallenge.lean:414-416](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L414-L416).

<a id="205"></a>

### 205. Weak base density and remainders

`Breakdown.CoerciveWeak.pieceRestWith`: This combines the base density with weak-Hessian λ mode errors and the unchanged μ mode errors. It is the per-mode remainder in the weak density-passage argument.

**Source.** [lean/ExtendedCoerciveChallenge.lean:420-426](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L420-L426). Def. **Paper.** (B.16), p. 54; approximation step of Proposition B.1, p. 56

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/ExtendedCoerciveDefs.lean:383-389](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L383-L389).

Clause 1 of `Breakdown.CoerciveWeak.pieceRestWith`, lines 420-426: This combines the base density with weak-Hessian λ mode errors and the unchanged μ mode errors. Paper: (B.16), p. 54; approximation step of Proposition B.1, p. 56 Source: [lean/ExtendedCoerciveChallenge.lean:420-426](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L420-L426).

<a id="206"></a>

### 206. Sum of the weak block errors

`Breakdown.CoerciveWeak.pieceBlockWith`: This sums all λ block errors with the supplied weak Hessian and all μ block errors. It is the block part of the signed split used after approximation.

**Source.** [lean/ExtendedCoerciveChallenge.lean:428-432](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L428-L432). Def. **Paper.** Approximation step of Proposition B.1, p. 56; error terms of (B.16), p. 54

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/ExtendedCoerciveDefs.lean:391-395](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L391-L395).

Clause 1 of `Breakdown.CoerciveWeak.pieceBlockWith`, lines 428-432: This sums all λ block errors with the supplied weak Hessian and all μ block errors. Paper: Approximation step of Proposition B.1, p. 56; error terms of (B.16), p. 54 Source: [lean/ExtendedCoerciveChallenge.lean:428-432](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L428-L432).

<a id="207"></a>

### 207. Recover classical mode remainders

`Breakdown.CoerciveWeak.pieceRestWith_secondDerivField`: This identifies the summed weak-Hessian mode remainder with the earlier remainder after substituting the iterated derivative. It follows by unfolding the component formulas.

**Source.** [lean/ExtendedCoerciveChallenge.lean:434-436](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L434-L436). Theorem with a source proof body. **Paper.** (B.16), p. 54; representation identity

**Library.** Implementation source: [lean/Breakdown/Cert/ExtendedCoerciveDefs.lean:397-399](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L397-L399).

Comparison for `Breakdown.CoerciveWeak.pieceRestWith_secondDerivField`: This is a definitional compatibility lemma for two Lean encodings of the mode remainder. It has no separately numbered paper statement.

Clause 1 of `Breakdown.CoerciveWeak.pieceRestWith_secondDerivField`, lines 434-436: This identifies the summed weak-Hessian mode remainder with the earlier remainder after substituting the iterated derivative. Paper: (B.16), p. 54; representation identity Source: [lean/ExtendedCoerciveChallenge.lean:434-436](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L434-L436).

<a id="208"></a>

### 208. Recover classical block remainders

`Breakdown.CoerciveWeak.pieceBlockWith_secondDerivField`: This identifies the total weak-Hessian block remainder with the earlier one for a C² reference field. It applies the λ-block conversion throughout the finite sum. Its library counterpart takes the curl-derivative identity as an explicit premise, which the library proves separately.

**Source.** [lean/ExtendedCoerciveChallenge.lean:438-442](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L438-L442). Theorem with a source proof body. **Paper.** (B.16), p. 54; representation identity

**Library.** Implementation source: [lean/Breakdown/Cert/ExtendedCoerciveAssembly.lean:41-45](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveAssembly.lean#L41-L45). This helper has an extra derivative-identity premise; the proved dependency is recorded in `library_locations.json`.

Encoding for `Breakdown.CoerciveWeak.pieceBlockWith_secondDerivField` (1): The *Holds helper in Breakdown/Cert/ExtendedCoerciveAssembly.lean adds VortGradMapSecondDerivFieldHolds as a premise; Breakdown.CoerciveWeak.vortGradMapSecondDerivFieldHolds_proof supplies it in Breakdown/Cert/ExtendedCoerciveVortGradMap.lean:51–62. This is a conditional helper plus a proved bridge, rather than a simple rename.

Comparison for `Breakdown.CoerciveWeak.pieceBlockWith_secondDerivField`: This is a compatibility lemma for the aggregate block remainder, with C² needed for its classical vorticity-gradient bound. It is not a separate paper theorem.

Clause 1 of `Breakdown.CoerciveWeak.pieceBlockWith_secondDerivField`, lines 438-440: This identifies the total weak-Hessian block remainder with the earlier one for a C² reference field. Paper: (B.16), p. 54; representation identity Source: [lean/ExtendedCoerciveChallenge.lean:438-440](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L438-L440).

<a id="209"></a>

### 209. Existence of the multiplier field

`Breakdown.CoerciveWeak.PieceFieldExistsWeakHolds`: This isolates the multiplier-existence and norm-bound part of Proposition B.1. It supplies a finite frequency seminorm and a field representing (B.14) for each admissible perturbation, before using the linearised equation.

**Source.** [lean/ExtendedCoerciveChallenge.lean:444-450](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L444-L450). Def. **Paper.** (B.14), p. 54; multiplier existence and norm bound in Proposition B.1, p. 55

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/ExtendedCoerciveDefs.lean:401-407](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L401-L407).

Encoding for `Breakdown.CoerciveWeak.PieceFieldExistsWeakHolds` (1): The residual equation, actuator family and weak-Hessian state are not premises of this node; it concerns the operator on the perturbation alone.

Encoding for `Breakdown.CoerciveWeak.PieceFieldExistsWeakHolds` (2): The D parameter is bookkeeping in this proposition and has no hypothesis attached to it.

Encoding for `Breakdown.CoerciveWeak.PieceFieldExistsWeakHolds` (3): This is a proposition definition, not an axiom declaration.

Clause 1 of `Breakdown.CoerciveWeak.PieceFieldExistsWeakHolds`, lines 445-447: Admissible weights and a weak perturbation are the inputs to the multiplier construction. Paper: (B.14), p. 54; Proposition B.1, p. 55 Source: [lean/ExtendedCoerciveChallenge.lean:445-447](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L445-L447).

Clause 2 of `Breakdown.CoerciveWeak.PieceFieldExistsWeakHolds`, lines 448-450: The frequency seminorm is finite and an L² multiplier with the required quantitative bound exists. Paper: Multiplier existence and norm bound in Proposition B.1, p. 55 Source: [lean/ExtendedCoerciveChallenge.lean:448-450](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L448-L450).

<a id="210"></a>

### 210. Pass the density bound to a limit

`Breakdown.CoerciveWeak.PieceDensityPassageWeakHolds`: This is the approximation step that carries the smooth multiplier estimate to a weak perturbation. Given a convergent smooth sequence and an admissible right-hand side, it produces the signed lower bound before Young’s inequality absorbs the remainder products.

**Source.** [lean/ExtendedCoerciveChallenge.lean:452-470](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L452-L470). Def. **Paper.** Approximation step in the proof of Proposition B.1, p. 56

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/ExtendedCoerciveDefs.lean:409-427](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L409-L427).

Encoding for `Breakdown.CoerciveWeak.PieceDensityPassageWeakHolds` (1): The approximation sequence is an explicit premise, so this node does not silently assume density of the smooth class.

Encoding for `Breakdown.CoerciveWeak.PieceDensityPassageWeakHolds` (2): The conclusion still records positive and negative parts separately in ENNReal.

Encoding for `Breakdown.CoerciveWeak.PieceDensityPassageWeakHolds` (3): This is a proposition definition; the library supplies its proof.

Clause 1 of `Breakdown.CoerciveWeak.PieceDensityPassageWeakHolds`, lines 452-470: This is the approximation step that carries the smooth multiplier estimate to a weak perturbation. Paper: Approximation step in the proof of Proposition B.1, p. 56 Source: [lean/ExtendedCoerciveChallenge.lean:452-470](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L452-L470).

<a id="211"></a>

### 211. Absorb the remainder products

`Breakdown.CoerciveWeak.PieceAbsorbStepWeakHolds`: This packages the Young-inequality step that distributes the cross-mode and block errors into the final coefficients Iι. It converts the intermediate signed split into the positive/negative density inequality of (B.20).

**Source.** [lean/ExtendedCoerciveChallenge.lean:472-482](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L472-L482). Def. **Paper.** Last step in the proof of Proposition B.1, p. 56; (B.20), p. 55

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/ExtendedCoerciveDefs.lean:429-439](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L429-L439).

Encoding for `Breakdown.CoerciveWeak.PieceAbsorbStepWeakHolds` (1): All positive allocation parameters and summability conditions enter through admissibility and the linked weak-Hessian state.

Encoding for `Breakdown.CoerciveWeak.PieceAbsorbStepWeakHolds` (2): This is a proposition definition, not evidence that a supplied set of numerical coefficients satisfies it.

Clause 1 of `Breakdown.CoerciveWeak.PieceAbsorbStepWeakHolds`, lines 472-482: This packages the Young-inequality step that distributes the cross-mode and block errors into the final coefficients Iι. Paper: Last step in the proof of Proposition B.1, p. 56; (B.20), p. 55 Source: [lean/ExtendedCoerciveChallenge.lean:472-482](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L472-L482).

<a id="212"></a>

### 212. Assemble the weak multiplier estimate

`Breakdown.CoerciveWeak.pieceMultiplierDensityWeak_of_nodes`: This combines multiplier existence, smooth approximation, passage to the limit and absorption of the error products. These four nodes supply the complete statement PieceMultiplierDensityWeakHolds.

**Source.** [lean/ExtendedCoerciveChallenge.lean:484-492](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L484-L492). Theorem with a source proof body. **Paper.** Proof of Proposition B.1, pp. 55–56; formal assembly

**Library.** Implementation source: [lean/Breakdown/Cert/ExtendedCoerciveDefs.lean:441-449](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L441-L449).

Encoding for `Breakdown.CoerciveWeak.pieceMultiplierDensityWeak_of_nodes` (1): The theorem is conditional on its four named proof nodes; the assembled public theorem supplies those nodes elsewhere.

Comparison for `Breakdown.CoerciveWeak.pieceMultiplierDensityWeak_of_nodes`: This theorem decomposes the proof of Proposition B.1 into four formal obligations. It is an assembly implication, rather than the paper’s final theorem statement alone.

Clause 1 of `Breakdown.CoerciveWeak.pieceMultiplierDensityWeak_of_nodes`, lines 484-486: This combines multiplier existence, smooth approximation, passage to the limit and absorption of the error products. Paper: Proof of Proposition B.1, pp. 55–56; formal assembly Source: [lean/ExtendedCoerciveChallenge.lean:484-486](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L484-L486).

<a id="213"></a>

### 213. Coercivity with residual rows

`Breakdown.CoerciveWeak.ExtendedCoerciveClause`: This isolates the extended certificate’s a priori estimate (7.18). At every admissible parameter it bounds the correction-and-force norm by the full residual norm, the finite row seminorm and the pin vector.

**Source.** [lean/ExtendedCoerciveChallenge.lean:498-505](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L498-L505). Def. **Paper.** (7.18), p. 32

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/ExtendedCoerciveDefs.lean:455-462](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L455-L462).

Encoding for `Breakdown.CoerciveWeak.ExtendedCoerciveClause` (1): F need not be divergence-free; the bound is for the chosen residual representative, as in the paper.

Encoding for `Breakdown.CoerciveWeak.ExtendedCoerciveClause` (2): The source supplies measurability, period-one recurrence and finite ENNReal squared norm before periodNorm F is used.

Encoding for `Breakdown.CoerciveWeak.ExtendedCoerciveClause` (3): The field g in the perturbation data is the combined time-and-drift term; IsRightSide inserts the Laplacian through weak testing.

Clause 1 of `Breakdown.CoerciveWeak.ExtendedCoerciveClause`, lines 499-503: The estimate is required for every parameter, admissible perturbation, force vector and finite residual representative of the reference linearised equation. Paper: Quantifiers and linearised equation for (7.18), p. 32 Source: [lean/ExtendedCoerciveChallenge.lean:499-503](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L499-L503).

Clause 2 of `Breakdown.CoerciveWeak.ExtendedCoerciveClause`, lines 504-505: The weighted correction-and-force norm is bounded by the full residual, finite rows and pin costs. Paper: (7.18), p. 32 Source: [lean/ExtendedCoerciveChallenge.lean:504-505](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L504-L505).

<a id="214"></a>

### 214. Extract the coercive estimate

`Breakdown.CoerciveWeak.extendedCoerciveClause_of_isExtendedCertificate`: This reads the coercive field from a complete extended certificate. It lets the multiplier argument use the isolated estimate (7.18) without passing the other certificate conditions.

**Source.** [lean/ExtendedCoerciveChallenge.lean:507-509](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L507-L509). Theorem with a source proof body. **Paper.** (7.18), p. 32; field-projection helper

**Library.** Implementation source: [lean/Breakdown/Cert/ExtendedCoerciveDefs.lean:464-466](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L464-L466).

Comparison for `Breakdown.CoerciveWeak.extendedCoerciveClause_of_isExtendedCertificate`: This is a projection of an already assumed certificate condition. It does not prove (7.18) from numerical data or from the other certificate conditions.

Clause 1 of `Breakdown.CoerciveWeak.extendedCoerciveClause_of_isExtendedCertificate`, lines 507-508: This reads the coercive field from a complete extended certificate. Paper: (7.18), p. 32; field-projection helper Source: [lean/ExtendedCoerciveChallenge.lean:507-508](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L507-L508).

<a id="215"></a>

### 215. The row expression is nonnegative

`Breakdown.CoerciveWeak.rows_nonneg`: This records nonnegativity of the square-root expression used for [F]. It is a scalar fact needed when comparing the coefficients in the final a priori estimate.

**Source.** [lean/ExtendedCoerciveChallenge.lean:511-512](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L511-L512). Theorem with a source proof body. **Paper.** (7.17)–(7.18), p. 32; scalar helper

**Library.** Implementation source: [lean/Breakdown/Cert/ExtendedCoerciveDefs.lean:468-469](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L468-L469).

Encoding for `Breakdown.CoerciveWeak.rows_nonneg` (1): Real.sqrt is nonnegative even on a negative input; this lemma alone does not establish that the expression is a seminorm.

Encoding for `Breakdown.CoerciveWeak.rows_nonneg` (2): The actual seminorm interpretation also uses nonnegative weights and finite row pairings.

Comparison for `Breakdown.CoerciveWeak.rows_nonneg`: The paper treats [F] as a seminorm. This lemma only establishes nonnegativity of its raw square-root expression and must not be used as a substitute for the row hypotheses.

Clause 1 of `Breakdown.CoerciveWeak.rows_nonneg`, lines 511-511: This records nonnegativity of the square-root expression used for [F]. Paper: (7.17)–(7.18), p. 32; scalar helper Source: [lean/ExtendedCoerciveChallenge.lean:511-511](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L511).

<a id="216"></a>

### 216. The parameter set contains zero

`Breakdown.CoerciveWeak.zero_mem_params`: This proves the origin belongs to the mixed set K when the separate coordinate radii are nonnegative. It is used to recover global scalar positivity from conditions that were written parameterwise.

**Source.** [lean/ExtendedCoerciveChallenge.lean:514-520](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L514-L520). Theorem with a source proof body. **Paper.** (7.29), p. 33; first sentence of p. 34

**Library.** Implementation source: [lean/Breakdown/Cert/ExtendedCoerciveDefs.lean:471-477](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L471-L477).

Encoding for `Breakdown.CoerciveWeak.zero_mem_params` (1): The complementary radius occurs squared, so this particular lemma does not require stiffRadius_nonneg or nonzero coordinate scales.

Encoding for `Breakdown.CoerciveWeak.zero_mem_params` (2): It also covers k=0, where the parameter-function type contains its unique zero vector.

Comparison for `Breakdown.CoerciveWeak.zero_mem_params`: The paper says the set K contains the origin. This lemma proves precisely that fact for its displayed mixed box-and-ball representation, using only the necessary coordinate-radius signs.

Clause 1 of `Breakdown.CoerciveWeak.zero_mem_params`, lines 514-515: This proves the origin belongs to the mixed set K when the separate coordinate radii are nonnegative. Paper: (7.29), p. 33; first sentence of p. 34 Source: [lean/ExtendedCoerciveChallenge.lean:514-515](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L514-L515).

<a id="217"></a>

### 217. Every forcing field has finite norm

`Breakdown.CoerciveWeak.actuator_finite`: This extracts finite period L² norm for each forcing field from the aggregate bound (7.9). The finite ENNReal upper bound prevents an infinite individual norm from being hidden by a later real conversion.

**Source.** [lean/ExtendedCoerciveChallenge.lean:522-527](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L522-L527). Theorem with a source proof body. **Paper.** (7.9), p. 31; finiteness helper

**Library.** Implementation source: [lean/Breakdown/Cert/ExtendedCoerciveDefs.lean:479-484](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L479-L484).

Comparison for `Breakdown.CoerciveWeak.actuator_finite`: This isolates a direct consequence of the aggregate norm bound and the paper’s bᵢ∈H assumption. It is an implementation finiteness lemma, with no separately numbered paper statement.

Clause 1 of `Breakdown.CoerciveWeak.actuator_finite`, lines 522-525: This extracts finite period L² norm for each forcing field from the aggregate bound (7.9). Paper: (7.9), p. 31; finiteness helper Source: [lean/ExtendedCoerciveChallenge.lean:522-525](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L522-L525).

<a id="218"></a>

### 218. Multiplier estimate with row terms

`Breakdown.CoerciveWeak.RowMultiplierInequality`: This is the quadratic inequality obtained by combining the multiplier lower bound with the row-rest estimate. It keeps the residual row term, the force-vector penalty and an auxiliary nonnegative frequency-seminorm value n explicit before the final scalar bound.

**Source.** [lean/ExtendedCoerciveChallenge.lean:529-544](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L529-L544). Structure. **Paper.** Proof of Lemma B.2, p. 56; (B.20)–(B.22), pp. 55–56

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/ExtendedCoerciveDefs.lean:486-501](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L486-L501).

Encoding for `Breakdown.CoerciveWeak.RowMultiplierInequality` (1): The variables c and t generalise the printed coefficients 3/50 and 1000.

Encoding for `Breakdown.CoerciveWeak.RowMultiplierInequality` (2): The symbol n here is an auxiliary real size, not the certificate dimension.

Encoding for `Breakdown.CoerciveWeak.RowMultiplierInequality` (3): Finite L² hypotheses are included for both F and the multiplier M before their period pairing is estimated.

Field `Breakdown.CoerciveWeak.RowMultiplierInequality.c_pos`: The correction-energy coefficient is positive, allowing division by its square root. Paper: Proof of Lemma B.2, p. 56; generalised coefficient c Source: [lean/ExtendedCoerciveChallenge.lean:530-530](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L530).

Field `Breakdown.CoerciveWeak.RowMultiplierInequality.cμ_nonneg`: The extra frequency-seminorm coefficient is nonnegative. Paper: Proof of Lemma B.2, p. 56 Source: [lean/ExtendedCoerciveChallenge.lean:531-531](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L531).

Field `Breakdown.CoerciveWeak.RowMultiplierInequality.t_nonneg`: The squared pin penalty has a nonnegative coefficient. Paper: (B.21), p. 56; generalised pin coefficient t Source: [lean/ExtendedCoerciveChallenge.lean:532-532](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L532).

Field `Breakdown.CoerciveWeak.RowMultiplierInequality.a_nonneg`: The multiplier-norm factor is nonnegative. Paper: Multiplier norm bound in Proposition B.1, p. 55 Source: [lean/ExtendedCoerciveChallenge.lean:533-533](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L533).

Field `Breakdown.CoerciveWeak.RowMultiplierInequality.bound`: For each admissible equation, an L² multiplier and nonnegative auxiliary size satisfy the norm bound and the quadratic estimate with rows and pins. Paper: Combined inequalities in the proof of Lemma B.2, p. 56 Source: [lean/ExtendedCoerciveChallenge.lean:534-544](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L534-L544).

<a id="219"></a>

### 219. Rows give the a priori estimate

`Breakdown.CoerciveWeak.extendedCoerciveClause_of_rowMultiplierInequality`: This converts the quadratic multiplier estimate into (7.18) by the period Cauchy–Schwarz inequality and the scalar argument of Lemma B.2. The coefficient comparisons require a/√c≤c₁ and √(t/c)≤c₂.

**Source.** [lean/ExtendedCoerciveChallenge.lean:546-566](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L546-L566). Theorem with a source proof body. **Paper.** Lemma B.2 and (B.22), p. 56; (7.18), p. 32

**Library.** Implementation source: [lean/Breakdown/Cert/ExtendedCoerciveDefs.lean:503-523](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L503-L523).

Comparison for `Breakdown.CoerciveWeak.extendedCoerciveClause_of_rowMultiplierInequality`: This is the parameter-uniform scalar implication behind Lemma B.2, allowing general c,t and weighted orthonormal rows. The paper displays the specialised constants c=3/50 and t=1000.

Clause 1 of `Breakdown.CoerciveWeak.extendedCoerciveClause_of_rowMultiplierInequality`, lines 546-548: This converts the quadratic multiplier estimate into (7.18) by the period Cauchy–Schwarz inequality and the scalar argument of Lemma B.2. Paper: Lemma B.2 and (B.22), p. 56; (7.18), p. 32 Source: [lean/ExtendedCoerciveChallenge.lean:546-548](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L546-L548).

<a id="220"></a>

### 220. The remaining density lower bound

`Breakdown.CoerciveWeak.RowRestClause`: This is the remaining lower bound (B.21), together with finiteness of I⁻, expressed with positive and negative ENNReal integrals. It is the analytic obligation that the cell and matrix estimates must establish before the coercivity theorem can be applied.

**Source.** [lean/ExtendedCoerciveChallenge.lean:568-588](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L568-L588). Def. **Paper.** (B.21), p. 56; Proposition B.8, pp. 63–64

**Library.** An identical source definition occurs at: [lean/Breakdown/Cert/ExtendedCoerciveDefs.lean:525-545](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L525-L545).

Encoding for `Breakdown.CoerciveWeak.RowRestClause` (1): This is universally quantified over admissible perturbations and right-hand sides; storing the predicate does not execute a numerical checker.

Encoding for `Breakdown.CoerciveWeak.RowRestClause` (2): The parameter c generalises 3/50 and t generalises 1000.

Encoding for `Breakdown.CoerciveWeak.RowRestClause` (3): Explicit negative-density finiteness is what permits cancellation with the multiplier-density inequality.

Clause 1 of `Breakdown.CoerciveWeak.RowRestClause`, lines 571-576: The rest bound applies to every admissible linearised equation and its multiplier. Paper: Quantifiers for (B.21), p. 56 Source: [lean/ExtendedCoerciveChallenge.lean:571-576](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L571-L576).

Clause 2 of `Breakdown.CoerciveWeak.RowRestClause`, lines 577-578: The integrated negative density I⁻ is finite. Paper: Finiteness requirement before (B.21), p. 56 Source: [lean/ExtendedCoerciveChallenge.lean:577-578](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L577-L578).

Clause 3 of `Breakdown.CoerciveWeak.RowRestClause`, lines 579-588: The weighted coefficient penalty cω²|κ|², minus the actuator pairing and quadratic row and pin penalties, lies below the signed density integral. Paper: (B.21), p. 56; signed implementation form Source: [lean/ExtendedCoerciveChallenge.lean:579-588](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L579-L588).

<a id="221"></a>

### 221. Combine the two density bounds

`Breakdown.CoerciveWeak.rowMultiplierInequality_of_pieceDensity`: This combines the weak multiplier theorem with RowRestClause and cancels their common signed densities. It gives the quadratic estimate used by Lemma B.2, with a multiplier-norm constant that is uniform in the parameter.

**Source.** [lean/ExtendedCoerciveChallenge.lean:590-627](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L590-L627). Theorem with a source proof body. **Paper.** (B.20)–(B.21), pp. 55–56; proof of Lemma B.2, p. 56

**Library.** Implementation source: [lean/Breakdown/Cert/ExtendedCoerciveDefs.lean:547-584](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L547-L584).

Encoding for `Breakdown.CoerciveWeak.rowMultiplierInequality_of_pieceDensity` (1): The proof uses zero_mem_params to obtain positivity of the common c and cμ from the parameterwise admissibility hypotheses.

Encoding for `Breakdown.CoerciveWeak.rowMultiplierInequality_of_pieceDensity` (2): The cancellation invokes the finite negative-density clause; it does not subtract infinities.

Comparison for `Breakdown.CoerciveWeak.rowMultiplierInequality_of_pieceDensity`: The paper combines the specialised density bounds inside the proof of Lemma B.2. This theorem isolates that combination for general coefficients, explicit weak-Hessian data and parameter-dependent weights.

Clause 1 of `Breakdown.CoerciveWeak.rowMultiplierInequality_of_pieceDensity`, lines 590-607: This combines the weak multiplier theorem with RowRestClause and cancels their common signed densities. Paper: (B.20)–(B.21), pp. 55–56; proof of Lemma B.2, p. 56 Source: [lean/ExtendedCoerciveChallenge.lean:590-607](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L590-L607).

<a id="222"></a>

### 222. Piece estimates give coercivity

`Breakdown.CoerciveWeak.extendedCoerciveClause_of_pieceData`: This is the completed passage from admissible multiplier pieces and the remaining density bound to the extended coercive estimate (7.18). It supplies the multiplier theorem internally and applies the two coefficient bounds from the scalar step.

**Source.** [lean/ExtendedCoerciveChallenge.lean:629-651](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L629-L651). Theorem with a source proof body. **Paper.** Proposition B.1, p. 55; Lemma B.2 and (B.21)–(B.22), p. 56

**Library.** Implementation source: [lean/Solution.lean:254-274](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Solution.lean#L254-L274).

Encoding for `Breakdown.CoerciveWeak.extendedCoerciveClause_of_pieceData` (1): The assumptions still include admissibility, the linked model Hessian, RowRestClause and both scalar coefficient inequalities.

Encoding for `Breakdown.CoerciveWeak.extendedCoerciveClause_of_pieceData` (2): This theorem is an implication from piece data satisfying those conditions, not an execution of the unreleased certificate checker.

Comparison for `Breakdown.CoerciveWeak.extendedCoerciveClause_of_pieceData`: This assembles the analytic route of Proposition B.1 and Lemma B.2 with general coefficients and explicit weak-Hessian representatives. It retains the row-rest and scalar hypotheses rather than verifying a particular finite certificate.

Clause 1 of `Breakdown.CoerciveWeak.extendedCoerciveClause_of_pieceData`, lines 629-648: This is the completed passage from admissible multiplier pieces and the remaining density bound to the extended coercive estimate (7.18). Paper: Proposition B.1, p. 55; Lemma B.2 and (B.21)–(B.22), p. 56 Source: [lean/ExtendedCoerciveChallenge.lean:629-648](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/ExtendedCoerciveChallenge.lean#L629-L648).
<!-- /passage:front -->

