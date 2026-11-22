
<!-- passage:front -->
# The authors’ paper, by its own numbering

**Navier–Stokes pages:** [the paper](../navier-stokes-paper/paper.pdf) · **index by number** · [specialist digest](../navier-stokes/digest.md) · [full account, part I](../navier-stokes-part-1/paper.md) · [part II](../navier-stokes-part-2/paper.md) · [part III](../navier-stokes-appendix-b/paper.md) · [what the Lean states](../navier-stokes/paper.md) · [statement files](../navier-stokes-statement-files/paper.md) · [proof routes](../navier-stokes-routes/paper.md) · [proof routes in detail](../navier-stokes-route-details/paper.md) · [library guide](../navier-stokes-library-01/paper.md) · [cell layer guide](../navier-stokes-cell-guide/paper.md) · [cell reference](../navier-stokes-cell-reference/paper.md) · [cell layer and Appendix B](../navier-stokes/cell-layer-fidelity.md) · [certificate checker](../navier-stokes/certificate-checker.md)

Original annotations for the paper of 20 November 2026, at source snapshot `ad53419de079eb8f95f60313473374624a348546`.

This index covers every numbered equation and named result in the PDF, plus its four figures. Each sentence below is an original summary. The page numbers refer to the printed labels; three internal PDF destinations point to an earlier page and have been corrected.

A comparison describes the listed correspondence at its stated scope. `same` concerns that statement or component; `stronger` and `weaker` identify the direction of a local change; `different` marks a changed formulation, premise, route or exposed conclusion. `no Lean` means no direct audited counterpart is assigned here, not a proof that none can exist. Definitions and certificate fields state requirements; their presence does not establish that released data satisfy them.

The uses and used-by links combine paper references and explicitly marked editorial dependencies. They are separate from a compiled Lean dependency graph.
<!-- /passage:front -->

<a id="1"></a>

## 1. Introduction

<!-- passage:sec-1 -->

### (1.1)

The velocity obeys the unforced viscosity-one Navier–Stokes momentum equation and has zero divergence.

[PDF page 1](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=1) · Section 1 · **same**.

**Comparison.** The momentum and incompressibility fields give these equations at viscosity one; the structure also packages regularity and initial data.

**Scope.** Momentum and incompressibility fields at ν=1.

**Lean correspondence.** [Smooth Navier–Stokes solution](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Defs.lean#L26) (`Breakdown.IsSmoothSolution`).

**Uses.** No item-level link recorded.

**Used by.** (1.2), (2.1), (3.14).

### (1.2)

A profile solves the Navier–Stokes equation in similarity variables and repeats after one positive period up to an orthogonal spatial twist.

[PDF page 2](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=2) · Section 1.1 · **same**.

**Comparison.** The residual, divergence and recurrence clauses reproduce this system; the additional decay clauses belong to the comparison with (1.3).

**Scope.** Similarity residual, divergence and twisted recurrence clauses.

**Lean correspondence.** [Residual in similarity variables](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Defs.lean#L47) (`Breakdown.SimilarityResidual`); [A nonzero recurrent profile](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Defs.lean#L51) (`Breakdown.PeriodicSimilarityProfileExists`).

**Uses.** (1.1).

**Used by.** (1.3), (1.4), (1.5), Remark 1.2, Proposition 4.1, (7.1), Theorem 7.1, Remark 7.3, (C.1).

### (1.3)

The profile velocity and its spatial gradient decay uniformly at orders one and two in the inverse distance.

[PDF page 2](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=2) · Section 1.1 · **stronger**.

**Comparison.** The formal premise includes these bounds and also assumes second-derivative and pressure-gradient decay; these are assumptions, not consequences proved by this declaration.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Smooth profile with decay](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/StatementsSlice.lean#L10) (`Breakdown.IsSimilarityProfile`); [A nonzero recurrent profile](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Defs.lean#L51) (`Breakdown.PeriodicSimilarityProfileExists`).

**Uses.** (1.2).

**Used by.** Remark 1.2, (4.1), (7.8), Theorem 7.1, Remark 7.3.

### (1.4)

The profile produces a physical velocity by the parabolic scaling and logarithmic time change associated with a final time T.

[PDF page 2](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=2) · Section 1.1 · **different**.

**Comparison.** The whole-space definitions use final time one and a similarity-time phase; the displayed formula permits arbitrary T.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Profile in physical variables](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/StatementsPhysical.lean#L14) (`Breakdown.physicalField`); [Physical curve of an orbit](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StatementsDefs.lean#L112) (`Breakdown.MildFramework.selfSimilar`).

**Uses.** (1.2).

**Used by.** (1.5), (1.6), (1.7), Remark 1.2, (2.5), (2.6), (4.1), Proposition 4.1, (7.40).

### (1.5)

Advancing physical time by one similarity period reproduces the velocity after the corresponding dilation and orthogonal twist.

[PDF page 2](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=2) · Section 1.1 · **different**.

**Comparison.** Lean encodes the twist on the similarity orbit and reconstructs physical pieces; this Eulerian identity is not the stated form of either declaration.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [A recurrent mild profile](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Base/Framework.lean#L55) (`Breakdown.MildFramework.IsOrbit`); [Physical curve of an orbit](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StatementsDefs.lean#L112) (`Breakdown.MildFramework.selfSimilar`).

**Uses.** (1.2), (1.4).

**Used by.** Proposition 4.1, (4.2), (7.66).

### Theorem 1.1

A nonzero smooth recurrent profile with the stated decay yields compact-data whole-space blow-up and smooth-data torus blow-up, both at the profile’s one-quarter rate with quantitative convergence to it.

[PDF page 3](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=3) · Section 1.1 · **different**. The embedded PDF destination points to page 2; the printed heading is on page 3.

**Comparison.** The pinned endpoints exclude global smooth solutions under a profile premise with additional decay; their statements do not bundle the constructed physical trajectories, common constants, rates and local torus comparison.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Proof in the paper.** Pages 11, 12.

**Lean correspondence.** [A profile excludes global smoothness](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/Space.lean#L24) (`Breakdown.breakdownOnSpace_of_profile`); [A profile gives torus breakdown](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Main.lean#L69) (`Breakdown.Periodic.breakdownOnTorus_of_profile`); [Compact data approaching the profile](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Base/Framework.lean#L66) (`Breakdown.TransferHolds`); [Keep the profile norm positive](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/Exports.lean#L41) (`Breakdown.orbitNorm`); [Bound the recurrent profile](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/OrbitNorm.lean#L60) (`Breakdown.orbitBound`).

**Uses.** Proposition 2.1, Proposition 2.2, Lemma 2.3.

**Used by.** Corollary 7.2.

### (1.6)

The whole-space solution has gradient norm comparable to (1−t)^(-1/4), while its gradient difference from the profile gains a positive power (1−t)^κ.

[PDF page 3](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=3) · Section 1.1 · **weaker**.

**Comparison.** The mapped interfaces retain mild rescaled convergence and positive profile norms; the exact two-sided physical estimate is not a bundled conclusion of these declarations.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Compact data approaching the profile](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Base/Framework.lean#L66) (`Breakdown.TransferHolds`); [Keep the profile norm positive](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/Exports.lean#L41) (`Breakdown.orbitNorm`); [Bound the recurrent profile](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/OrbitNorm.lean#L60) (`Breakdown.orbitBound`).

**Uses.** (1.4), Proposition 2.1.

**Used by.** No item-level link recorded.

### (1.7)

The torus solution has H1 norm comparable to (T−t)^(-1/4) and approaches the profile in local H1 on the ball of radius 1/16 at an improved power.

[PDF page 3](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=3) · Section 1.1 · **weaker**.

**Comparison.** The pinned torus interface exports norm unboundedness, without the printed local ball estimate or explicit rate.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [A torus mild solution is unbounded](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsSmooth.lean#L44) (`Breakdown.Periodic.TorusBlowup`); [Unbounded norm after gluing](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsSteps.lean#L110) (`Breakdown.Periodic.GlueUnbounded`).

**Uses.** (1.4), Proposition 2.2.

**Used by.** No item-level link recorded.

### Remark 1.2

The similarity equation and velocity decay alone imply the first and second spatial derivative decay through interior Navier–Stokes regularity.

[PDF page 3](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=3) · Section 1.1 · **no Lean**.

**Comparison.** The paper derives derivative decay from smooth Navier-Stokes evolution and velocity decay alone by a cited pressure-free interior estimate; Lean's nearby profile and far-field predicates carry additional derivative, tail, pressure and integral-equation hypotheses.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** No direct audited counterpart assigned.

**Uses.** (1.2), (1.3), (1.4).

**Used by.** Proposition 7.11.

### Figure 1

Two vorticity-magnitude surfaces of the computed approximate profile at similarity time zero, at levels 50 and 85, show its spatial shape with colour indicating height.

[PDF page 4](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=4) · Section 1.1 · **no Lean**.

**Comparison.** The figure displays vorticity level surfaces of one computed approximate profile; the pinned source supplies neither that field's numerical data nor a verified rendering.

**Scope.** The particular plotted numerical data, not the general analytical definitions used to describe them.

**Lean correspondence.** No direct audited counterpart assigned.

**Uses.** No item-level link recorded.

**Used by.** No item-level link recorded.
<!-- /passage:sec-1 -->

<a id="2"></a>

## 2. Outline of the proof

<!-- passage:sec-2 -->

### (2.1)

The heat evolution is Gaussian convolution at positive time and the identity at time zero.

[PDF page 10](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=10) · Section 2.1 · **different**.

**Comparison.** heatX is Fourier-defined on X, and source proofs identify its reconstructed L6 velocity with Gaussian convolution almost everywhere for positive time; the paper defines heat evolution on general Lp fields and includes time zero.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Heat flow on the Fourier space](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Basic.lean#L95) (`Breakdown.Freq.heatX`); [Heat multiplier](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Basic.lean#L90) (`Breakdown.Freq.heatFactor`); [Prove the heat semigroup properties](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Realization.lean#L52) (`Breakdown.Freq.heat_holds`); [Gaussian convolution](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/KernelStatementsIdentify.lean#L12) (`Breakdown.FarField.heatConv`); [Heat flow as Gaussian convolution](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/KernelStatementsIdentify.lean#L18) (`Breakdown.FarField.HeatVelocity`); [Identify the physical heat flow](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/HeatVelocity.lean#L114) (`Breakdown.FarField.heatVelocity_of_heatConvTest`).

**Uses.** (1.1).

**Used by.** (2.2), (2.4), (3.3), (7.65).

### (2.2)

Applying the Leray projection and heat evolution multiplies the Fourier transform by the solenoidal projection and the Gaussian frequency factor.

[PDF page 10](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=10) · Section 2.1 · **different**.

**Comparison.** heatDivFree realizes the projected heat operator on L2 forcing in the gradient-weighted Fourier representation; the paper defines it on L1+L2 fields.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Heat flow with solenoidal projection](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Statements.lean#L186) (`Breakdown.Freq.heatDivFree`).

**Uses.** (2.1).

**Used by.** (2.3), Lemma 3.1, (3.6), (3.8), (3.9), (3.10), Lemma 6.1.

### (2.3)

The symmetric bilinear term is minus one half of the projected heat evolution of the two transport interactions.

[PDF page 10](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=10) · Section 2.1 · **different**.

**Comparison.** Lean defines the bilinear map by duality and proves its transport formula with a compact test-field input; the display defines it for all pairs in X.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Symmetric Navier–Stokes bilinear term](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Basic.lean#L146) (`Breakdown.Freq.bilinX`); [Bilinear term against a test field](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Realization.lean#L142) (`Breakdown.Freq.bilinTestFormula_holds`).

**Uses.** (2.2).

**Used by.** (2.4), Lemma 3.1, (3.7), (3.8), (3.10), (3.17), (4.6), (6.9).

### (2.4)

A mild solution equals the heat evolution of its initial value plus the time integral of its quadratic bilinear term.

[PDF page 11](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=11) · Section 2.1 · **same**.

**Comparison.** The definition states this equation on the half-open interval and explicitly requires continuity and interval integrability.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [The mild integral equation](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Base/Framework.lean#L36) (`Breakdown.MildFramework.IsMildOn`).

**Uses.** (2.1), (2.3), Lemma 3.3.

**Used by.** Lemma 3.6, (4.7), (7.64).

### Proposition 2.1

Every sufficiently close whole-space datum can be corrected in one fixed finite-dimensional space of compact solenoidal fields to give a mild solution with the profile’s rate and improved error.

[PDF page 11](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=11) · Section 2.2 · **weaker**.

**Comparison.** The exported transfer statement selects one datum in a chosen dense subspace; finite-dimensional corrections exist internally, but the printed uniform family over every nearby datum is not retained by that interface.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Proof in the paper.** Pages 23, 24.

**Lean correspondence.** [Compact data approaching the profile](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Base/Framework.lean#L66) (`Breakdown.TransferHolds`); [Finite-dimensional correction data](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StatementsFrame.lean#L55) (`Breakdown.StepDataStatement`); [Quadratic correction on time pieces](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StatementsAbstract.lean#L44) (`Breakdown.ContractionStatement`); [Transfer from spectral splitting](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/Exports.lean#L54) (`Breakdown.transferHolds_of_dichotomy`).

**Uses.** Lemma 4.2, Proposition 4.3, Lemma 4.8, Lemma 5.1.

**Used by.** Theorem 1.1, (1.6).

### (2.5)

The corrected whole-space mild solution has a uniform two-sided one-quarter blow-up rate and an error smaller than the profile by a positive power.

[PDF page 11](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=11) · Section 2.2 · **weaker**.

**Comparison.** The mapped convergence and orbit-norm interfaces contain the ingredients, with no single statement exporting all the displayed constants and inequalities.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Compact data approaching the profile](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Base/Framework.lean#L66) (`Breakdown.TransferHolds`); [Keep the profile norm positive](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/Exports.lean#L41) (`Breakdown.orbitNorm`); [Bound the recurrent profile](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/OrbitNorm.lean#L60) (`Breakdown.orbitBound`).

**Uses.** (1.4), (4.4), (4.24).

**Used by.** No item-level link recorded.

### Proposition 2.2

A profile yields a smooth periodic initial datum whose mild solution blows up at a positive time at the profile’s rate and converges to it locally on the ball of radius 1/16.

[PDF page 11](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=11) · Section 2.2 · **weaker**.

**Comparison.** TorusBlowup supplies a smooth datum and an unbounded mild trajectory; its fields omit the two-sided rate and local profile convergence.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Proof in the paper.** Pages 28, 29.

**Lean correspondence.** [A torus mild solution is unbounded](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsSmooth.lean#L44) (`Breakdown.Periodic.TorusBlowup`); [Assemble the torus mild solution](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Assembly.lean#L188) (`Breakdown.Periodic.torusBlowup_of_parts`).

**Uses.** (3.21), Lemma 4.8, Lemma 6.2, Lemma 6.3.

**Used by.** Theorem 1.1, (1.7).

### (2.6)

The periodic mild solution obeys the same global H1 rate and local H1 profile-error bound that later appear in Theorem 1.1.

[PDF page 11](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=11) · Section 2.2 · **weaker**.

**Comparison.** The mapped torus conclusion states unboundedness of its Fourier-space norm, rather than these two quantified estimates.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [A torus mild solution is unbounded](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsSmooth.lean#L44) (`Breakdown.Periodic.TorusBlowup`); [Unbounded norm after gluing](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsSteps.lean#L110) (`Breakdown.Periodic.GlueUnbounded`).

**Uses.** (1.4), (3.16), (3.21), (6.18).

**Used by.** No item-level link recorded.

### Lemma 2.3

Mild solutions with compact smooth whole-space data or smooth mean-zero periodic data are classical on their lifespan, and the whole-space L2 norm does not increase.

[PDF page 11](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=11) · Section 2.3 · **weaker**.

**Comparison.** MildRegular gives smooth whole-space representatives on each compact interval and an interval energy bound; it does not state energy monotonicity or the periodic assertion.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Proof in the paper.** Pages 48, 49.

**Lean correspondence.** [Smooth representatives of mild flow](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/Basic.lean#L37) (`Breakdown.MildRegular`); [Smooth whole-space mild flow](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/Space.lean#L19) (`Breakdown.mildRegular_realization`); [Energy on a fixed time interval](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/Basic.lean#L19) (`Breakdown.EnergyBoundedOn`).

**Uses.** Lemma 3.3, Lemma 3.5, (3.16), Lemma 3.7.

**Used by.** Theorem 1.1.
<!-- /passage:sec-2 -->

<a id="3"></a>

## 3. Preliminaries

<!-- passage:sec-3 -->

### (3.1)

The L6 norm of a homogeneous H1 field is bounded by a constant times the L2 norm of its gradient.

[PDF page 12](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=12) · Section 3.1 · **different**.

**Comparison.** The explicit Sobolev theorem is for smooth decaying fields, while the bounded velocity map extends the construction to the abstract Fourier space.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Sobolev bound for decaying fields](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Statements.lean#L65) (`Breakdown.Freq.GradSixDecay`); [Prove the decaying-field Sobolev bound](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/GradSixDecay.lean#L289) (`Breakdown.Freq.gradSixDecay`); [Construct the L6 velocity map](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Realization.lean#L75) (`Breakdown.Freq.velocity_holds`).

**Uses.** No item-level link recorded.

**Used by.** (3.2), Lemma 3.1, (3.6), (3.7), Lemma 3.2, Lemma 3.6, (6.7), (6.8), Proposition 7.5, Lemma 7.7, (7.51), Proposition 7.8, (7.63), (B.45), Lemma B.11, (B.55).

### (3.2)

Fourier differentiation, the solenoidal constraint and Plancherel identify the homogeneous H1 norm with the frequency integral weighted by 4π²|ξ|².

[PDF page 12](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=12) · Section 3.1 · **different**.

**Comparison.** The formal space stores a gradient-weighted Fourier field; these declarations establish its solenoidal encoding and physical derivative norm rather than one literal transform identity for every u.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Real solenoidal Fourier fields](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Basic.lean#L76) (`Breakdown.Freq.Sig`); [Gradient norm and linear embedding](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Realization.lean#L63) (`Breakdown.Freq.embedNormLinear_holds`); [Read physical spatial derivatives](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Realization.lean#L83) (`Breakdown.Freq.partial_holds`).

**Uses.** (3.1).

**Used by.** (3.3), (3.5), Lemma 3.2, (3.15), (7.45), Lemma B.9.

### (3.3)

Heat flow is the Gaussian Fourier multiplier, a contraction semigroup on X, and is strongly continuous from time zero.

[PDF page 12](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=12) · Section 3.1 · **same**.

**Comparison.** HeatSemigroup records the multiplier realization, semigroup law, contraction and strong continuity, and heat_holds proves the package.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Heat semigroup properties](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Statements.lean#L14) (`Breakdown.Freq.HeatSemigroup`); [Prove the heat semigroup properties](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Realization.lean#L52) (`Breakdown.Freq.heat_holds`); [Heat multiplier](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Basic.lean#L90) (`Breakdown.Freq.heatFactor`).

**Uses.** (2.1), (3.2).

**Used by.** (3.5), Lemma 4.4, Proposition 7.5, (7.47).

### (3.4)

Dilation rescales both velocity and position by the square root of its parameter, while an orthogonal map acts by push-forward.

[PDF page 12](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=12) · Section 3.1 · **same**.

**Comparison.** The two physical-field definitions agree with the stated dilation and push-forward.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Navier–Stokes dilation](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Base/Realization.lean#L13) (`Breakdown.dilateField`); [Rotate a vector field](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Base/Realization.lean#L10) (`Breakdown.pushForward`).

**Uses.** No item-level link recorded.

**Used by.** (3.5), (3.8), (3.21), (4.2), (4.10), (4.13), (7.5), (7.40).

### (3.5)

Dilation multiplies the homogeneous H1 norm by μ^(1/4), composes multiplicatively and intertwines the corresponding heat evolutions.

[PDF page 12](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=12) · Section 3.1 · **same**.

**Comparison.** The formal dilation package has these norm, composition and heat-intertwining identities on the realized space.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Algebra of Navier–Stokes dilations](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Statements.lean#L22) (`Breakdown.Freq.DilationAlgebra`); [Prove the dilation identities](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Realization.lean#L54) (`Breakdown.Freq.dilation_holds`); [Continuity of dilations](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Realization.lean#L56) (`Breakdown.Freq.dilationCont_holds`).

**Uses.** (3.2), (3.3), (3.4).

**Used by.** (3.21), Lemma 4.2, (4.3), (4.4), Lemma 4.4, Lemma 4.6, (4.15), Proposition 7.5, (7.47).

### Lemma 3.1

Projected heat evolution sends L^(3/2) forcing into X with a τ^(-3/4) bound and gives a continuous symmetric bilinear map with the corresponding product estimate.

[PDF page 13](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=13) · Section 3.2 · **weaker**.

**Comparison.** The matched package proves the bilinear part and its time properties; no matching general L^(3/2)-forcing theorem for the full first assertion was identified.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Bilinear smoothing bound](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Statements.lean#L100) (`Breakdown.Freq.BilinBound`); [Construct and bound the bilinear term](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Realization.lean#L95) (`Breakdown.Freq.bilin_holds`); [Continuity of the bilinear term](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Realization.lean#L99) (`Breakdown.Freq.bilinCont_holds`); [Heat shift of the bilinear term](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Realization.lean#L97) (`Breakdown.Freq.bilinShift_holds`).

**Uses.** (2.2), (2.3), (3.1).

**Used by.** No item-level link recorded.

### (3.6)

The projected heat evolution of L^(3/2) forcing has homogeneous H1 norm at most a constant times τ^(-3/4) times the forcing norm.

[PDF page 13](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=13) · Section 3.2 · **no Lean**.

**Comparison.** No source declaration was located for projected heat flow on every L^(3/2) forcing field with this homogeneous H1 bound; the nearby heatDivFree domain is L2, and shell estimates restrict the input to transport products.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** No direct audited counterpart assigned.

**Uses.** (2.2), (3.1).

**Used by.** (3.7).

### (3.7)

The bilinear Navier–Stokes operator has norm bounded by Cτ^(-3/4) times the product of its two X-input norms.

[PDF page 13](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=13) · Section 3.2 · **same**.

**Comparison.** BilinBound has the same positive-time exponent and two input norms; bilin_holds proves existence and the bound.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Bilinear smoothing bound](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Statements.lean#L100) (`Breakdown.Freq.BilinBound`); [Construct and bound the bilinear term](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Realization.lean#L95) (`Breakdown.Freq.bilin_holds`).

**Uses.** (2.3), (3.1), (3.6).

**Used by.** Lemma 3.2, Lemma 4.4.

### (3.8)

The bilinear operator intertwines heat evolution, Navier–Stokes dilation and orthogonal push-forward.

[PDF page 13](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=13) · Section 3.2 · **same**.

**Comparison.** The three proved covariance statements correspond to the three identities, after reading the Fourier representation as a physical field.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Heat shift of the bilinear term](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Realization.lean#L97) (`Breakdown.Freq.bilinShift_holds`); [Dilation of the bilinear term](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Realization.lean#L109) (`Breakdown.Freq.bilinDilate_holds`); [Rotation of the bilinear term](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Realization.lean#L113) (`Breakdown.Freq.bilinRotate_holds`).

**Uses.** (2.2), (2.3), (3.4).

**Used by.** (3.21), Lemma 4.6.

### (3.9)

Every spatial derivative of the Oseen tensor decays at the parabolic rate (|x|+√τ)^(-3−l).

[PDF page 13](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=13) · Section 3.2 · **different**.

**Comparison.** Lean defines the Leray-divergence kernel and supplies a proof of its power-four parabolic decay; the paper states bounds for every derivative order of the Oseen tensor.

**Scope.** Matched: The divergence-kernel estimate with decay (norm(x) + sqrt(tau))^(-4). Remaining: The base Oseen tensor, an explicit identification as its derivative, and the entire family of bounds for every derivative order l >= 0.

**Lean correspondence.** [The Leray-divergence kernel](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/Defs.lean#L22) (`Breakdown.FarField.lerayKernel`); [Decay of the Leray kernel](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/KernelStatements.lean#L27) (`Breakdown.FarField.LerayKernelBound`); [Prove Leray kernel decay](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/IntegralEquationClosed.lean#L30) (`Breakdown.FarField.lerayKernelBound_holds`).

**Uses.** (2.2).

**Used by.** (3.10), Lemma 6.1, (6.2), (7.65).

### (3.10)

Projected heat evolution of a tensor divergence is convolution with the derivative of the Oseen tensor, which also gives the symmetric bilinear term.

[PDF page 13](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=13) · Section 3.2 · **different**.

**Comparison.** Lean supplies an almost-everywhere physical convolution formula for K(tau)(u,u), with a compact test-field version; the display also quantifies over arbitrary tensor divergences and distinct inputs u and v.

**Scope.** Matched: The diagonal bilinear term, as an equality of physical representatives almost everywhere; a separate compact test-field statement is exact in the abstract space. Remaining: The W^(1,1) tensor-divergence formula and the polarized two-input formula are not theorem conclusions of these declarations. Polarization was not written or compiled in this audit.

**Lean correspondence.** [Convolution for compact test fields](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/KernelStatementsIdentify.lean#L30) (`Breakdown.FarField.BilinTestKernel`); [Bilinear flow as convolution](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/KernelStatementsIdentify.lean#L39) (`Breakdown.FarField.BilinKernel`); [Extend the convolution formula](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/BilinKernel.lean#L152) (`Breakdown.FarField.bilinKernel_of_test_decay`).

**Uses.** (2.2), (2.3), (3.9).

**Used by.** Lemma 6.1, (6.2), (7.64).

### Lemma 3.2

Fixing a positive heat time and one velocity makes the bilinear operator compact in its other velocity argument.

[PDF page 14](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=14) · Section 3.3 · **weaker**.

**Comparison.** BilinCompact states compactness when the fixed input lies in the dense compact test span; the printed lemma quantifies over every element of X.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Proof in the paper.** Pages 14.

**Lean correspondence.** [Compactness with a test-field input](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Statements.lean#L115) (`Breakdown.Freq.BilinCompact`); [Prove test-input compactness](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Realization.lean#L116) (`Breakdown.Freq.bilinCompact_holds`).

**Uses.** (3.1), (3.2), (3.7).

**Used by.** Lemma 4.4.

### (3.11)

The abstract heat operators form a strongly continuous contraction semigroup on the Banach space.

[PDF page 14](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=14) · Section 3.4 · **same**.

**Comparison.** The G_zero, G_add, G_norm and G_cont fields carry exactly these abstract heat assumptions.

**Scope.** The heat-operator fields of HeatBilinear.

**Lean correspondence.** [Abstract heat and bilinear operators](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StatementsDefs.lean#L9) (`Breakdown.HeatBilinear`).

**Uses.** No item-level link recorded.

**Used by.** (3.12), Lemma 3.5, (3.13), Lemma 4.7, (4.20).

### (3.12)

The abstract bilinear kernel intertwines heat shifts and has a τ^(-3/4) product bound.

[PDF page 14](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=14) · Section 3.4 · **weaker**.

**Comparison.** K_shift is the stated covariance, while K_bound is assumed only for 0<τ≤1 instead of all positive τ.

**Scope.** K_shift and K_bound fields of HeatBilinear.

**Lean correspondence.** [Abstract heat and bilinear operators](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StatementsDefs.lean#L9) (`Breakdown.HeatBilinear`).

**Uses.** (3.11).

**Used by.** Lemma 3.3, Lemma 3.4, Lemma 3.5, (3.13), (4.18), Lemma 4.7, (4.19), (4.21).

### Lemma 3.3

The time-integrated bilinear kernel of two continuous curves is Bochner integrable and continuous up to both endpoints of a compact interval.

[PDF page 14](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=14) · Section 3.4 · **stronger**.

**Comparison.** The formal statement gives integrability and continuity on every compact interval [a,b]; only its additional explicit 4CK(t−a)^(1/4)MN estimate is restricted to t−a≤1. Continuous curves provide the finite M and N.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Proof in the paper.** Pages 47.

**Lean correspondence.** [Continuity of the Duhamel integral](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StatementsLocal.lean#L9) (`Breakdown.VarConstIntegralStatement`); [Integrate the bilinear term](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/VarConstIntegral.lean#L168) (`Breakdown.varConstIntegral`).

**Uses.** (3.12).

**Used by.** (2.4), Lemma 2.3, Lemma 3.4, Lemma 3.6, (4.6), Lemma 4.7, Lemma 6.2.

### Lemma 3.4

Linearization about any continuous background has a unique continuous solution for each continuous forcing, with a bounded linear solution operator.

[PDF page 14](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=14) · Section 3.4 · **different**.

**Comparison.** The matched formal route inverts linear operators on sufficiently short pieces and assembles them; it does not export this all-interval Volterra statement.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Proof in the paper.** Pages 47.

**Lean correspondence.** [Monodromy is a compact perturbation](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StatementsFrame.lean#L71) (`Breakdown.MonodromyStatement`); [Prove the monodromy decomposition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/Exports.lean#L47) (`Breakdown.monodromy`); [Prove the time-piece operator bounds](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/Exports.lean#L24) (`Breakdown.pieceOperator`).

**Uses.** (3.12), Lemma 3.3.

**Used by.** Lemma 3.5, (4.9), Lemma 4.6.

### Lemma 3.5

An integral solution can be restarted at any intermediate time, and two mild solutions with the same initial value coincide.

[PDF page 15](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=15) · Section 3.4 · **weaker**.

**Comparison.** The formal restart interface is specialized to the quadratic mild equation, while the displayed restart assertion permits separate input curves f and h; mild uniqueness is proved.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Proof in the paper.** Pages 47.

**Lean correspondence.** [Restart a mild solution](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StatementsLocal.lean#L27) (`Breakdown.RestrictStatement`); [Restart the integral equation](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/Restrict.lean#L28) (`Breakdown.restrict`); [Uniqueness of mild solutions](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StatementsLocal.lean#L41) (`Breakdown.UniqueStatement`); [Prove mild uniqueness](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/Exports.lean#L26) (`Breakdown.mildUnique`).

**Uses.** (3.11), (3.12), Lemma 3.4.

**Used by.** Lemma 2.3, Lemma 4.2, (4.4).

### (3.13)

Starting from an intermediate time gives the same Duhamel formula with the interval before that time absorbed into the heat-evolved value.

[PDF page 15](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=15) · Section 3.4 · **weaker**.

**Comparison.** RestrictStatement covers the nonlinear choice f=h=u; this display is written for arbitrary continuous forcing factors.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Restart a mild solution](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StatementsLocal.lean#L27) (`Breakdown.RestrictStatement`); [Restart the integral equation](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/Restrict.lean#L28) (`Breakdown.restrict`).

**Uses.** (3.11), (3.12).

**Used by.** Lemma 4.6.

### Lemma 3.6

A continuous X-valued curve satisfying the divergence-free weak test identity is a mild Navier–Stokes solution.

[PDF page 15](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=15) · Section 3.5 · **weaker**.

**Comparison.** The formal weak-to-mild bridge requires smooth decaying slices and L2-continuous differences in addition to the test identity.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Proof in the paper.** Pages 47, 48.

**Lean correspondence.** [The profile weak equation is mild](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Statements.lean#L151) (`Breakdown.Freq.MildOfWeak`); [Pass from weak to mild form](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Realization.lean#L125) (`Breakdown.Freq.mild_holds`); [Weak solution for the profile route](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Statements.lean#L127) (`Breakdown.Freq.IsWeakSolution`).

**Uses.** (2.4), (3.1), Lemma 3.3, (3.14).

**Used by.** Proposition 4.1, Proposition 7.11.

### (3.14)

Testing against a compact solenoidal field turns the time derivative of the velocity pairing into diffusion and quadratic transport pairings.

[PDF page 15](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=15) · Section 3.5 · **different**.

**Comparison.** The same weak momentum identity is written with gradient and advection pairings; the enclosing predicates carry extra decay and regularity conditions.

**Scope.** Test-derivative clause, with integration by parts identifying the displayed pairings.

**Lean correspondence.** [Weak solution for the profile route](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Statements.lean#L127) (`Breakdown.Freq.IsWeakSolution`); [Weak equation of the physical profile](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/StatementsPhysical.lean#L59) (`Breakdown.PhysicalWeak`).

**Uses.** (1.1).

**Used by.** Lemma 3.6.

### (3.15)

For mean-zero periodic solenoidal fields, the homogeneous H1 norm is both gradient energy over one cell and the corresponding Fourier-series sum.

[PDF page 15](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=15) · Section 3.6 · **different**.

**Comparison.** The formal unit-torus space uses the inhomogeneous weight 1+4π²|k|² and retains the zero mode; this is not the displayed homogeneous norm.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Periodic Fourier velocity space](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L91) (`Breakdown.Periodic.V`); [Inhomogeneous Fourier weight](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L19) (`Breakdown.Periodic.weight`).

**Uses.** (3.2).

**Used by.** (3.16), (3.17), (3.18), Lemma 3.7, (3.19), (6.1).

### (3.16)

On the unit torus, mean-zero homogeneous H1 and ordinary H1 norms are equivalent.

[PDF page 15](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=15) · Section 3.6 · **different**.

**Comparison.** The formal route works directly with its inhomogeneous Fourier norm and does not state this mean-zero norm-equivalence lemma.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Periodic Fourier velocity space](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L91) (`Breakdown.Periodic.V`); [Inhomogeneous Fourier weight](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L19) (`Breakdown.Periodic.weight`).

**Uses.** (3.15).

**Used by.** (2.6), Lemma 2.3, (3.18).

### (3.17)

The periodic symmetric bilinear term is defined by projected heat evolution of the two periodic transport interactions.

[PDF page 15](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=15) · Section 3.6 · **different**.

**Comparison.** The formal kernel uses Fourier coefficients on the unit torus with the inhomogeneous V norm; the paper defines it on variable-period homogeneous spaces.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Periodic bilinear term](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L608) (`Breakdown.Periodic.kernel`).

**Uses.** (2.3), (3.15).

**Used by.** Lemma 3.7, (3.20), (6.9).

### (3.18)

The periodic Sobolev inequality for mean-zero fields has a constant independent of the torus period.

[PDF page 16](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=16) · Section 3.6 · **different**.

**Comparison.** TrigHs controls finite Fourier polynomials on the unit cell with the inhomogeneous weight, rather than the printed uniform-in-period homogeneous inequality.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Sobolev bound for Fourier polynomials](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsCoeff.lean#L44) (`Breakdown.Periodic.TrigHs`); [Prove periodic Sobolev control](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TrigHs.lean#L333) (`Breakdown.Periodic.trigHs`).

**Uses.** (3.15), (3.16).

**Used by.** Lemma 3.7, (3.19), (3.20), (6.7).

### Lemma 3.7

Uniform projected-heat and bilinear smoothing estimates hold on every mean-zero periodic homogeneous H1 space, together with the heat-shift and continuity identities.

[PDF page 16](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=16) · Section 3.6 · **different**.

**Comparison.** Lean proves a unit-torus inhomogeneous kernel estimate for τ≤1 and packages rescaled time frames; the paper states the whole L^(3/2) forcing result for every spatial period.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Proof in the paper.** Pages 48.

**Lean correspondence.** [Periodic bilinear smoothing bound](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsAnalysis.lean#L9) (`Breakdown.Periodic.KernelSharpBound`); [Prove periodic bilinear smoothing](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/KernelBound.lean#L364) (`Breakdown.Periodic.kernelSharpBound`); [Rescaled heat flow on the torus](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsSteps.lean#L12) (`Breakdown.Periodic.stepFrame`).

**Uses.** (3.15), (3.17), (3.18).

**Used by.** Lemma 2.3, Lemma 6.2.

### (3.19)

Mean-zero periodic L^(3/2) forcing gains a τ^(-3/4) homogeneous H1 bound under projected heat evolution, uniformly in the period.

[PDF page 16](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=16) · Section 3.6 · **different**.

**Comparison.** Lean supplies the tau^(-3/4) L^(3/2) forcing bound for compactly supported L2 data transplanted to its inhomogeneous unit-torus space, with mu*tau <= 1; the paper allows every period and all positive times in the mean-zero homogeneous space.

**Scope.** Matched: The actual L^(3/2)-norm right-hand side is present, for supported L2 input and the rescaled unit-torus source operator. Remaining: All mean-zero L^(3/2) torus data, arbitrary torus period, all positive times, and the literal homogeneous output norm.

**Lean correspondence.** [Bound projected torus forcing](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellTorus.lean#L33) (`Breakdown.Periodic.ShellTorus.Internal.sourceOp_threeHalves`); [Projected heat for transplanted data](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L844) (`Breakdown.Periodic.sourceOp`); [Prove periodic Sobolev control](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TrigHs.lean#L333) (`Breakdown.Periodic.trigHs`).

**Uses.** (3.15), (3.18).

**Used by.** (3.20).

### (3.20)

The periodic bilinear term is bounded by CTτ^(-3/4) times the two homogeneous H1 norms, with CT independent of the period.

[PDF page 16](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=16) · Section 3.6 · **different**.

**Comparison.** The exponent matches, but the formal estimate concerns the inhomogeneous unit-period V norm for τ≤1 and its rescaled time frames.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Periodic bilinear smoothing bound](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsAnalysis.lean#L9) (`Breakdown.Periodic.KernelSharpBound`); [Prove periodic bilinear smoothing](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/KernelBound.lean#L364) (`Breakdown.Periodic.kernelSharpBound`); [Rescaled heat flow on the torus](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsSteps.lean#L12) (`Breakdown.Periodic.stepFrame`).

**Uses.** (3.17), (3.18), (3.19).

**Used by.** No item-level link recorded.

### (3.21)

Dilation changes the torus period and preserves the quarter-power norm scaling and covariance of both heat flow and the bilinear term.

[PDF page 16](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=16) · Section 3.6 · **different**.

**Comparison.** The formal construction rescales time on the unit torus and transfers compact fields with an additional L2 contribution to the norm; it does not state these variable-period identities.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Rescaled heat flow on the torus](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsSteps.lean#L12) (`Breakdown.Periodic.stepFrame`); [Norm of a transferred compact field](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsShell.lean#L39) (`Breakdown.Periodic.TransplantNorm`).

**Uses.** (3.4), (3.5), (3.8).

**Used by.** Proposition 2.2, (2.6).
<!-- /passage:sec-3 -->

<a id="4"></a>

## 4. The linearised equation

<!-- passage:sec-4 -->

### (4.1)

The physical profile and its gradient satisfy pointwise bounds by inverse powers of √(1−t)+|x|, and hence by inverse powers of |x|.

[PDF page 16](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=16) · Section 4.1 · **different**.

**Comparison.** The formal profile assumes spatial decay and the physical field is its dilation; the exact time-dependent pair of displayed estimates is not a separate matched declaration.

**Scope.** Decay premise together with the physical scaling definition; displayed estimate is an analytic reading.

**Lean correspondence.** [Profile in physical variables](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/StatementsPhysical.lean#L14) (`Breakdown.physicalField`); [Smooth profile with decay](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/StatementsSlice.lean#L10) (`Breakdown.IsSimilarityProfile`); [Velocity and gradient decay](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Base/Realization.lean#L16) (`Breakdown.IsDecayField`).

**Uses.** (1.3), (1.4).

**Used by.** Proposition 4.1, (5.1), Lemma 5.1, (5.2).

### Proposition 4.1

The velocity generated by a profile is a nonzero continuous X-valued mild solution before time one and obeys twisted discrete self-similarity.

[PDF page 17](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=17) · Section 4.1 · **different**.

**Comparison.** The proved package constructs an embedded similarity orbit and a physical mild curve under the formal profile’s additional decay bounds.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Proof in the paper.** Pages 17.

**Lean correspondence.** [Embed the given recurrent profile](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/StatementsEmbed.lean#L10) (`Breakdown.EmbeddedProfileOrbit`); [The embedded profile is an orbit](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/Orbit.lean#L35) (`Breakdown.embeddedProfileOrbit_holds`); [The physical profile is mild](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/StatementsPhysical.lean#L66) (`Breakdown.PhysicalMild`); [Build the physical mild profile](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/Orbit.lean#L22) (`Breakdown.physicalMild_unconditional`).

**Uses.** (1.2), (1.4), (1.5), Lemma 3.6, (4.1).

**Used by.** Lemma 4.2, (4.7).

### (4.2)

One advance by the profile period in similarity time equals the inverse-scale dilation followed by the orthogonal action.

[PDF page 17](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=17) · Section 4.1 · **different**.

**Comparison.** The recurrence is carried by IsOrbit and the matching of profile pieces; the paper writes it directly in physical time.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [A recurrent mild profile](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Base/Framework.lean#L55) (`Breakdown.MildFramework.IsOrbit`); [Physical curve of an orbit](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StatementsDefs.lean#L112) (`Breakdown.MildFramework.selfSimilar`); [Matching and bounds of profile pieces](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StatementsFrame.lean#L33) (`Breakdown.ProfilePieceStatement`).

**Uses.** (1.5), (3.4).

**Used by.** Lemma 4.2, (4.3).

### Lemma 4.2

Every physical period is a rotated dilation of the first, and the profile’s homogeneous H1 norm stays between positive multiples of (1−t)^(-1/4).

[PDF page 17](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=17) · Section 4.1 · **different**.

**Comparison.** Lean states recurrent rescaled pieces and positive upper and lower similarity-orbit norms; the printed physical-time rate is obtained by the dilation law.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Proof in the paper.** Pages 17.

**Lean correspondence.** [Matching and bounds of profile pieces](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StatementsFrame.lean#L33) (`Breakdown.ProfilePieceStatement`); [Build the recurrent profile pieces](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/Exports.lean#L43) (`Breakdown.profilePiece`); [Bound the recurrent profile](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/OrbitNorm.lean#L60) (`Breakdown.orbitBound`); [Keep the profile norm positive](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/Exports.lean#L41) (`Breakdown.orbitNorm`).

**Uses.** (3.5), Lemma 3.5, Proposition 4.1, (4.2).

**Used by.** Proposition 2.1.

### (4.3)

The velocity on the nth physical period is the first-period velocity dilated by λ^(-n) and acted on by the nth power of the twist.

[PDF page 17](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=17) · Section 4.1 · **different**.

**Comparison.** The formal route divides a period into k substeps and records piece matching and recurrence; this closed nth-period Eulerian identity is not its theorem type.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Matching and bounds of profile pieces](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StatementsFrame.lean#L33) (`Breakdown.ProfilePieceStatement`); [Build the recurrent profile pieces](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/Exports.lean#L43) (`Breakdown.profilePiece`); [Physical curve of an orbit](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StatementsDefs.lean#L112) (`Breakdown.MildFramework.selfSimilar`).

**Uses.** (3.5), (4.2).

**Used by.** (4.4), Lemma 4.6.

### (4.4)

The physical profile has a positive two-sided homogeneous H1 bound with the exact one-quarter blow-up exponent.

[PDF page 17](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=17) · Section 4.1 · **same**.

**Comparison.** The proved uniform similarity-orbit bounds and the dilation norm identity give this estimate under the physical scaling definition.

**Scope.** Combined consequence of the two orbit norm bounds and D_norm; no standalone printed-rate theorem is claimed.

**Lean correspondence.** [Bound the recurrent profile](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/OrbitNorm.lean#L60) (`Breakdown.orbitBound`); [Keep the profile norm positive](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/Exports.lean#L41) (`Breakdown.orbitNorm`); [Algebra of Navier–Stokes dilations](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Statements.lean#L22) (`Breakdown.Freq.DilationAlgebra`); [Physical curve of an orbit](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StatementsDefs.lean#L112) (`Breakdown.MildFramework.selfSimilar`).

**Uses.** (3.5), Lemma 3.5, (4.3).

**Used by.** (2.5), (4.5), Lemma 6.2, (6.5).

### (4.5)

The weighted norm multiplies a curve’s size by (1−t)^(1/4−κ) before taking its supremum up to blow-up.

[PDF page 17](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=17) · Section 4.2 · **different**.

**Comparison.** The formal route uses bounded sequences of rescaled continuous pieces and a separate gluing map; it has no matching declaration of the displayed global Cκ norm.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Continuous curves on one time piece](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StatementsDefs.lean#L36) (`Breakdown.Piece`); [Weighted discrete forced recurrence](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StatementsDefs.lean#L100) (`Breakdown.orbitSeq`); [Join the rescaled solution pieces](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StatementsDefs.lean#L136) (`Breakdown.MildFramework.gluePieces`).

**Uses.** (4.4).

**Used by.** (4.8), (4.15), (4.18), Lemma 4.7, (4.20).

### (4.6)

The bilinear Duhamel map integrates the heat-smoothed interaction of two curves from the initial time to the current time.

[PDF page 17](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=17) · Section 4.2 · **different**.

**Comparison.** pieceBil gives the same integral on one compact time piece; the paper defines B on the entire half-open lifespan.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Duhamel operator on one time piece](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StatementsDefs.lean#L80) (`Breakdown.HeatBilinear.pieceBil`); [Prove the time-piece operator bounds](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/Exports.lean#L24) (`Breakdown.pieceOperator`).

**Uses.** (2.3), Lemma 3.3.

**Used by.** (4.7), (4.8), (4.9), (4.12), (4.16).

### (4.7)

Adding a perturbation to the exact profile solves the nonlinear mild equation precisely when the perturbation satisfies its linearized equation plus the quadratic remainder.

[PDF page 18](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=18) · Section 4.2 · **weaker**.

**Comparison.** PiecePerturbationStatement records the forward implication on a compact piece and piecePerturbation proves it; the paper states an equivalence on the whole lifespan.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Correct one exact solution piece](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StatementsLocal.lean#L63) (`Breakdown.PiecePerturbationStatement`); [The corrected piece solves the equation](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/Exports.lean#L34) (`Breakdown.piecePerturbation`).

**Uses.** (2.4), Proposition 4.1, (4.6).

**Used by.** (4.17).

### Proposition 4.3

After allowing a finite-dimensional compactly supported correction to the initial datum, the linearized equation has a bounded right inverse in a suitable weighted space.

[PDF page 18](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=18) · Section 4.2 · **different**.

**Comparison.** The proved inverse is encoded on bounded sequences of short rescaled pieces, with a finite-dimensional correction and compact-data lift; the paper uses one global weighted curve space.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Proof in the paper.** Pages 20, 21.

**Lean correspondence.** [Finite-dimensional correction data](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StatementsFrame.lean#L55) (`Breakdown.StepDataStatement`); [Construct the correction data](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/Exports.lean#L51) (`Breakdown.stepData`); [A right inverse across repeated pieces](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StatementsAbstract.lean#L19) (`Breakdown.PeriodicInverseStatement`); [Assemble the periodic right inverse](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/Exports.lean#L49) (`Breakdown.periodicInverse`); [Lift the finite-dimensional correction](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StatementsAbstract.lean#L56) (`Breakdown.SectionStatement`); [Choose compactly supported lifts](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/Section.lean#L31) (`Breakdown.exists_section`).

**Uses.** Lemma 4.5, Lemma 4.6.

**Used by.** Proposition 2.1, (6.12), Lemma 6.3.

### (4.8)

The right inverse solves the linearized equation with an initial-data correction and bounds both the correction and the weighted trajectory by the source norm.

[PDF page 18](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=18) · Section 4.2 · **different**.

**Comparison.** StepDataStatement records the analogous bounded linear inverse with a finite-dimensional first component in the sequence formulation, and stepData proves it.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Finite-dimensional correction data](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StatementsFrame.lean#L55) (`Breakdown.StepDataStatement`); [Construct the correction data](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/Exports.lean#L51) (`Breakdown.stepData`).

**Uses.** (4.5), (4.6).

**Used by.** (6.14).

### (4.9)

The linearized flow from an initial vector is heat evolution plus twice its time-integrated interaction with the profile.

[PDF page 18](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=18) · Section 4.3 · **different**.

**Comparison.** The formal step map uses the inverse of the linearization on each sufficiently short subinterval, then composes those maps.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Linearization on one time piece](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StatementsDefs.lean#L117) (`Breakdown.MildFramework.stepOp`); [Linear flow across one time piece](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StatementsDefs.lean#L96) (`Breakdown.stepMap`); [Monodromy is a compact perturbation](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StatementsFrame.lean#L71) (`Breakdown.MonodromyStatement`).

**Uses.** Lemma 3.4, (4.6).

**Used by.** (4.10), Lemma 4.4, (4.13).

### (4.10)

The monodromy advances the linearized flow through one period, rescales it and removes the profile’s orthogonal twist.

[PDF page 18](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=18) · Section 4.3 · **different**.

**Comparison.** The monodromy expression is the untwisted product of k short-step maps in MonodromyStatement; the paper defines it through the one-period solution operator.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Linear flow across one time piece](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StatementsDefs.lean#L96) (`Breakdown.stepMap`); [Compose the linear time steps](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StatementsDefs.lean#L92) (`Breakdown.iterProd`); [Monodromy is a compact perturbation](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StatementsFrame.lean#L71) (`Breakdown.MonodromyStatement`).

**Uses.** (3.4), (4.9).

**Used by.** Lemma 4.4, Lemma 4.6, (4.14).

### Lemma 4.4

The monodromy differs from an operator of norm at most exp(−S/4) by a compact operator.

[PDF page 18](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=18) · Section 4.3 · **same**.

**Comparison.** MonodromyStatement records compactness of the difference from the untwisted free-step product and the same exp(−P/4) norm bound; monodromy proves it.

**Scope.** Last two clauses of MonodromyStatement after k short steps compose one period.

**Proof in the paper.** Pages 18, 19.

**Lean correspondence.** [Monodromy is a compact perturbation](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StatementsFrame.lean#L71) (`Breakdown.MonodromyStatement`); [Prove the monodromy decomposition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/Exports.lean#L47) (`Breakdown.monodromy`).

**Uses.** (3.3), (3.5), (3.7), Lemma 3.2, (4.9), (4.10).

**Used by.** Lemma 4.5.

### Lemma 4.5

A spectral circle between exp(−S/4) and one separates a finite-dimensional invertible component from the decaying component and makes their weighted power series summable.

[PDF page 19](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=19) · Section 4.3 · **stronger**.

**Comparison.** Set b=α=exp(−S/4) and β=1 in the abstract theorem, then choose Θ strictly between its radii r₁ and r₂. Its finite-rank commuting projection, surjectivity and inverse-power bounds give the paper’s invertibility and summability.

**Scope.** The geometric estimates are stronger than the displayed weighted summability after this explicit parameter specialization.

**Proof in the paper.** Pages 19.

**Lean correspondence.** [Finite-rank spectral splitting](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Base/Framework.lean#L75) (`Breakdown.DichotomyHolds`); [Prove the real spectral splitting](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/RealDichotomy.lean#L151) (`Breakdown.dichotomyHolds`).

**Uses.** Lemma 4.4.

**Used by.** Proposition 4.3.

### (4.11)

Stable forward powers and unstable inverse powers are summable after weighting by a separating spectral radius.

[PDF page 19](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=19) · Section 4.3 · **stronger**.

**Comparison.** The two-radius geometric estimates bound these series by convergent geometric sums once the weight is chosen strictly between the radii.

**Scope.** Geometric bounds imply the displayed summability; this last implication is an analytic comparison.

**Lean correspondence.** [Finite-rank spectral splitting](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Base/Framework.lean#L75) (`Breakdown.DichotomyHolds`); [Prove the real spectral splitting](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/RealDichotomy.lean#L151) (`Breakdown.dichotomyHolds`).

**Uses.** No item-level link recorded.

**Used by.** No item-level link recorded.

### Lemma 4.6

Rescaling the forced linearized equation period by period produces a monodromy recurrence whose forcing decays at the weighted geometric rate.

[PDF page 19](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=19) · Section 4.4 · **different**.

**Comparison.** Lean builds an equivalent kind of forced recurrence from k short pieces and bounded weighted forcing; it does not state the paper’s particular vn, gn, χn and fn formulas.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Proof in the paper.** Pages 19, 20.

**Lean correspondence.** [Weighted discrete forced recurrence](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StatementsDefs.lean#L100) (`Breakdown.orbitSeq`); [Matching and bounds of profile pieces](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StatementsFrame.lean#L33) (`Breakdown.ProfilePieceStatement`); [A right inverse across repeated pieces](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StatementsAbstract.lean#L19) (`Breakdown.PeriodicInverseStatement`); [Solve the weighted discrete recurrence](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StatementsAbstract.lean#L9) (`Breakdown.DiscreteDichotomyStatement`).

**Uses.** (3.5), (3.8), Lemma 3.4, (3.13), (4.3), (4.10).

**Used by.** Proposition 4.3.

### (4.12)

The forced linearized perturbation is the sum of heat-evolved initial data, twice the profile interaction and an added source.

[PDF page 19](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=19) · Section 4.4 · **different**.

**Comparison.** The formal inverse solves the normalized sequence of short-step equations, rather than this single equation on [0,1).

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Linearization on one time piece](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StatementsDefs.lean#L117) (`Breakdown.MildFramework.stepOp`); [A right inverse across repeated pieces](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StatementsAbstract.lean#L19) (`Breakdown.PeriodicInverseStatement`).

**Uses.** (4.6).

**Used by.** (4.13).

### (4.13)

Rotating and rescaling each period defines normalized perturbations, sources, initial values and the source contribution to the next period.

[PDF page 19](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=19) · Section 4.4 · **different**.

**Comparison.** The implementation uses rescaled pieces and orbitSeq; the particular four auxiliary objects in this display are not declarations in that route.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [One rescaled piece of the profile](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StatementsDefs.lean#L114) (`Breakdown.MildFramework.profilePiece`); [Weighted discrete forced recurrence](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StatementsDefs.lean#L100) (`Breakdown.orbitSeq`).

**Uses.** (3.4), (4.9), (4.12).

**Used by.** (4.14), (4.15).

### (4.14)

The normalized perturbation is its homogeneous linear evolution plus the source response, and its period-end data satisfy the forced monodromy recurrence.

[PDF page 19](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=19) · Section 4.4 · **different**.

**Comparison.** orbitSeq states a weight-normalized recurrence and the inverse is assembled on short pieces; the displayed unweighted two-part identity is not exported.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Weighted discrete forced recurrence](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StatementsDefs.lean#L100) (`Breakdown.orbitSeq`); [Solve the weighted discrete recurrence](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StatementsAbstract.lean#L9) (`Breakdown.DiscreteDichotomyStatement`); [A right inverse across repeated pieces](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StatementsAbstract.lean#L19) (`Breakdown.PeriodicInverseStatement`).

**Uses.** (4.10), (4.13).

**Used by.** No item-level link recorded.

### (4.15)

The rescaled source and the forcing of the discrete recurrence are uniformly bounded by Θ^n times the global weighted source norm.

[PDF page 19](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=19) · Section 4.4 · **no Lean**.

**Comparison.** No source declaration was located for the displayed conversion from the paper's global C_kappa norm to its particular g_n and f_n; the formal inverse instead takes bounded weighted sequences of short pieces as input.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** No direct audited counterpart assigned.

**Uses.** (3.5), (4.5), (4.13).

**Used by.** No item-level link recorded.

### (4.16)

An approximate curve determines its mild-equation residual and a linearized operator acting on a datum correction and a trajectory correction.

[PDF page 21](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=21) · Section 4.5 · **different**.

**Comparison.** The formal route records residuals on successive pieces and a linear sequence operator; the paper uses one residual and one operator on its global weighted curve space.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Linearized sequence operator on R3](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/InverseDefs.lean#L65) (`Breakdown.Periodic.r3Op`); [Linearized sequence operator on torus](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/InverseDefs.lean#L73) (`Breakdown.Periodic.torusOp`); [Small residual on every time piece](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsApproxSteps.lean#L24) (`Breakdown.Periodic.ApproxResidualSmall`).

**Uses.** (4.6).

**Used by.** (4.17), Lemma 4.8, (4.22), (4.23), (6.6).

### (4.17)

Correcting the approximate curve reduces to solving the linearized operator equation with heat-evolved datum error, negative residual and quadratic remainder.

[PDF page 21](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=21) · Section 4.5 · **different**.

**Comparison.** The sequence correction theorem has this residual-plus-quadratic structure after normalization on each piece; the unknowns and forcing are indexed by pieces.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Correct approximate solution pieces](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsSteps.lean#L91) (`Breakdown.Periodic.SeqPerturbation`); [Solve the periodic nonlinear correction](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SeqPerturbation.lean#L140) (`Breakdown.Periodic.seqPerturbation`).

**Uses.** (4.7), (4.16).

**Used by.** Lemma 4.8.

### (4.18)

A change of time variable bounds the convolution of the singular heat kernel with the blow-up weight whenever 0<κ<1/4.

[PDF page 21](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=21) · Section 4.5 · **no Lean**.

**Comparison.** No source declaration was located for this global weighted improper-integral calculation; the formal route bounds integrals on short compact pieces and treats the weight through a geometric sequence.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** No direct audited counterpart assigned.

**Uses.** (3.12), (4.5).

**Used by.** Lemma 4.7, (4.19), (4.21), (6.10).

### Lemma 4.7

The weighted Duhamel map is bilinearly bounded, the free heat evolution preserves the datum bound, and interaction with a bounded background is controlled in the stronger weighted norm.

[PDF page 22](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=22) · Section 4.5 · **different**. The embedded PDF destination points to page 21; the printed heading is on page 22.

**Comparison.** The formal route bounds compact-piece operators and handles the global time weight in sequence spaces; the three printed Cκ estimates are not one formal package.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Proof in the paper.** Pages 22.

**Lean correspondence.** [Bounds for operators on a time piece](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StatementsLocal.lean#L18) (`Breakdown.PieceOperatorStatement`); [Prove the time-piece operator bounds](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/Exports.lean#L24) (`Breakdown.pieceOperator`); [Abstract heat and bilinear operators](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StatementsDefs.lean#L9) (`Breakdown.HeatBilinear`).

**Uses.** (3.11), (3.12), Lemma 3.3, (4.5), (4.18).

**Used by.** Lemma 4.8.

### (4.19)

The Duhamel interaction of two Cκ curves is bounded in Cκ by the product of their weighted norms.

[PDF page 22](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=22) · Section 4.5 · **different**.

**Comparison.** The formal bilinear operator norm is on a compact time piece and has the factor T^(1/4); global weighting is supplied by the sequence construction.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Bounds for operators on a time piece](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StatementsLocal.lean#L18) (`Breakdown.PieceOperatorStatement`); [Prove the time-piece operator bounds](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/Exports.lean#L24) (`Breakdown.pieceOperator`).

**Uses.** (3.12), (4.18).

**Used by.** No item-level link recorded.

### (4.20)

The weighted norm of the free heat evolution is no greater than the initial X norm.

[PDF page 22](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=22) · Section 4.5 · **different**.

**Comparison.** The contraction and compact-piece free-evolution bounds are formal fields and theorems; the displayed Cκ weighting is a paper-level consequence of κ<1/4.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Abstract heat and bilinear operators](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StatementsDefs.lean#L9) (`Breakdown.HeatBilinear`); [Bounds for operators on a time piece](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StatementsLocal.lean#L18) (`Breakdown.PieceOperatorStatement`).

**Uses.** (3.11), (4.5).

**Used by.** Lemma 6.2.

### (4.21)

A bounded continuous background interacting with a C0 curve has Cκ norm bounded by the product of the background supremum and the C0 norm.

[PDF page 22](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=22) · Section 4.5 · **no Lean**.

**Comparison.** No source declaration was located for this mixed global C_kappa estimate using sup(f) and the C_0 norm of g; the matched formal bounds concern compact-piece bilinear operators and normalized sequences.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** No direct audited counterpart assigned.

**Uses.** (3.12), (4.18).

**Used by.** Lemma 6.2, Lemma 6.3.

### Lemma 4.8

A sufficiently small datum error and residual can be corrected to an exact solution once the linearized operator has a bounded right inverse.

[PDF page 22](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=22) · Section 4.5 · **different**.

**Comparison.** The formal fixed-point theorem acts on rescaled sequences and uses an explicit residual/data smallness condition; the paper formulates the same strategy in Cκ with different constants.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Proof in the paper.** Pages 22.

**Lean correspondence.** [Correct approximate solution pieces](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsSteps.lean#L91) (`Breakdown.Periodic.SeqPerturbation`); [Solve the periodic nonlinear correction](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SeqPerturbation.lean#L140) (`Breakdown.Periodic.seqPerturbation`); [Quadratic correction on time pieces](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StatementsAbstract.lean#L44) (`Breakdown.ContractionStatement`); [Solve the quadratic correction](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/Contraction.lean#L45) (`Breakdown.contraction`).

**Uses.** (4.16), (4.17), Lemma 4.7.

**Used by.** Proposition 2.1, Proposition 2.2, (6.16).

### (4.22)

The assumed right inverse solves each linearized source equation and controls the trajectory component by CR times the source norm.

[PDF page 22](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=22) · Section 4.5 · **different**.

**Comparison.** The formal right inverse is a continuous linear map into datum corrections and bounded sequences of pieces, with its equation expressed one piece at a time.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Finite-dimensional correction data](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StatementsFrame.lean#L55) (`Breakdown.StepDataStatement`); [A right inverse across repeated pieces](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StatementsAbstract.lean#L19) (`Breakdown.PeriodicInverseStatement`).

**Uses.** (4.16).

**Used by.** (4.23), (4.24).

### (4.23)

The norm of the heat-evolved datum error minus the residual must be small after multiplication by the squared inverse bound.

[PDF page 22](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=22) · Section 4.5 · **different**.

**Comparison.** SeqPerturbation uses 64‖R‖²CKL^(1/4)(ρ+‖ξ‖)≤1, which is a different normalized sufficient condition.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Correct approximate solution pieces](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsSteps.lean#L91) (`Breakdown.Periodic.SeqPerturbation`).

**Uses.** (4.16), (4.22).

**Used by.** (4.24).

### (4.24)

The nonlinear correction has weighted norm at most twice the inverse bound times the initial forcing error.

[PDF page 22](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=22) · Section 4.5 · **different**.

**Comparison.** The formal correction has the corresponding factor-two bound for each normalized piece and for its datum parameter; it is not stated in the displayed Cκ norm.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Correct approximate solution pieces](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsSteps.lean#L91) (`Breakdown.Periodic.SeqPerturbation`); [Solve the periodic nonlinear correction](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SeqPerturbation.lean#L140) (`Breakdown.Periodic.seqPerturbation`).

**Uses.** (4.22), (4.23).

**Used by.** (2.5), (6.17).
<!-- /passage:sec-4 -->

<a id="5"></a>

## 5. Blow-up on space

<!-- passage:sec-5 -->

### (5.1)

A radial homotopy potential is cut off and curled to produce a compactly supported divergence-free approximation to the profile velocity.

[PDF page 23](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=23) · Section 5.1 · **same**.

**Comparison.** The homotopy potential and cutoffField realize this construction; homotopyCurl and cutoffDivergenceFree prove the curl and solenoidal identities.

**Scope.** General-centre potential and product-rule form of curl(χA), specialized to centre zero and χ(x)=η(x/r).

**Lean correspondence.** [Vector potential for the cutoff](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsCutoff.lean#L18) (`Breakdown.Periodic.homotopyPotential`); [Divergence-free cutoff field](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsCutoff.lean#L25) (`Breakdown.Periodic.cutoffField`); [Recover the divergence-free field](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Cutoff.lean#L225) (`Breakdown.Periodic.homotopyCurl`); [Prove the cutoff is divergence-free](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Cutoff.lean#L254) (`Breakdown.Periodic.cutoffDivergenceFree`).

**Uses.** (4.1).

**Used by.** Lemma 5.1, (5.2).

### Lemma 5.1

The solenoidal cutoff agrees with the profile on the inner ball, vanishes outside the outer ball and has gradient error O(r^(-1/2)) and L2 size O(r^(1/2)), uniformly in time.

[PDF page 23](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=23) · Section 5.1 · **different**.

**Comparison.** Lean proves support, agreement, gradient closeness and mass bounds for a fixed physical cutoff around the unit-torus centre, with the scale encoded by T−t; its displayed estimates use different parameters.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Proof in the paper.** Pages 23.

**Lean correspondence.** [Support and agreement of the cutoff](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsApprox.lean#L51) (`Breakdown.Periodic.ApproxFieldProperties`); [Prove support and profile agreement](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Main.lean#L51) (`Breakdown.Periodic.approxFieldProperties_holds`); [Gradient error from the cutoff](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxSizes.lean#L902) (`Breakdown.Periodic.cutoffGradientClose`); [L2 mass of the cutoff](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxSizes.lean#L908) (`Breakdown.Periodic.cutoffMassBound`).

**Uses.** (4.1), (5.1).

**Used by.** Proposition 2.1, (6.4).

### (5.2)

The cutoff error in homogeneous H1 is O(r^(-1/2)), while the cutoff’s L2 norm is O(r^(1/2)).

[PDF page 23](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=23) · Section 5.1 · **different**.

**Comparison.** The formal gradient theorem is an arbitrary-ε closeness statement at small T−t, and the mass theorem is a squared L2 bound proportional to (T−t)^(-1/2).

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Gradient error from the cutoff](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxSizes.lean#L902) (`Breakdown.Periodic.cutoffGradientClose`); [L2 mass of the cutoff](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxSizes.lean#L908) (`Breakdown.Periodic.cutoffMassBound`).

**Uses.** (4.1), (5.1).

**Used by.** (6.4).
<!-- /passage:sec-5 -->

<a id="6"></a>

## 6. Blow-up on the torus

<!-- passage:sec-6 -->

### (6.1)

Periodizing a smooth solenoidal field supported in the small interior ball yields a mean-zero periodic field and preserves its homogeneous H1 norm.

[PDF page 24](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=24) · Section 6.1 · **different**.

**Comparison.** The formal transfer includes scaling to the unit torus and an inhomogeneous norm identity with an added μ times the L2 mass; it does not assert this homogeneous equality.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Norm of a transferred compact field](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsShell.lean#L39) (`Breakdown.Periodic.TransplantNorm`); [Prove the transferred norm identity](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Transplant.lean#L326) (`Breakdown.Periodic.transplantNorm`); [A smooth periodic transferred field](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsShell.lean#L45) (`Breakdown.Periodic.TransplantSmooth`).

**Uses.** (3.15).

**Used by.** Lemma 6.2, (6.5), (6.6).

### Lemma 6.1

The periodic and whole-space projected heat evolutions of a compact tensor divergence differ locally by at most CL^(-7/2) times the tensor’s L1 norm.

[PDF page 24](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=24) · Section 6.1 · **different**.

**Comparison.** HeatDivFreeComparison gives arbitrary-δ convergence at small scale on positive-time windows for compact L2 forcing, without this uniform all-time rate or tensor-divergence hypothesis.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Proof in the paper.** Pages 24, 25.

**Lean correspondence.** [Compare projected heat flows](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsShell.lean#L52) (`Breakdown.Periodic.HeatDivFreeComparison`); [Prove projected heat-flow convergence](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparison.lean#L18) (`Breakdown.Periodic.heatDivFreeComparison`).

**Uses.** (2.2), (3.9), (3.10).

**Used by.** Lemma 6.2.

### (6.2)

Both the local gradient-L2 error and the local L6 error between the two projected heat flows are bounded by CL^(-7/2) times the source tensor’s L1 norm.

[PDF page 24](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=24) · Section 6.1 · **different**.

**Comparison.** The formal comparison controls a shell norm by δ times an L^(3/2) forcing norm for sufficiently small scale; the printed L^(-7/2) estimate is not its statement.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Compare projected heat flows](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsShell.lean#L52) (`Breakdown.Periodic.HeatDivFreeComparison`); [Prove projected heat-flow convergence](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparison.lean#L18) (`Breakdown.Periodic.heatDivFreeComparison`).

**Uses.** (3.9), (3.10).

**Used by.** (6.3), (6.11).

### (6.3)

For compact solenoidal velocity data, the periodic and whole-space free heat flows differ locally by O(L^(-5/2)) times the datum’s L1 norm.

[PDF page 25](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=25) · Section 6.1 · **different**.

**Comparison.** FreeHeatComparison gives uniform small-scale convergence for each compact test field over a bounded time window; it does not export the displayed L-dependent rate.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Compare free heat flows](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsShell.lean#L58) (`Breakdown.Periodic.FreeHeatComparison`); [Prove free heat-flow convergence](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparison.lean#L24) (`Breakdown.Periodic.freeHeatComparison`).

**Uses.** (6.2).

**Used by.** Lemma 6.2, Lemma 6.3, (6.15).

### (6.4)

Cutting the profile at radius L/8 gives a homogeneous H1 error of order L^(-1/2) and an L2 norm of order L^(1/2).

[PDF page 25](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=25) · Section 6.2 · **different**.

**Comparison.** The formal cutoff estimates use the small physical scale T−t and a fixed cutoff, with gradient closeness stated qualitatively.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Gradient error from the cutoff](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxSizes.lean#L902) (`Breakdown.Periodic.cutoffGradientClose`); [L2 mass of the cutoff](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxSizes.lean#L908) (`Breakdown.Periodic.cutoffMassBound`).

**Uses.** Lemma 5.1, (5.2).

**Used by.** Lemma 6.2, (6.5), (6.11), Lemma 6.3, (6.15).

### Lemma 6.2

The periodized cutoff has the profile’s leading norm size and a Duhamel residual of order L^(-1/2) in the weighted space.

[PDF page 25](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=25) · Section 6.2 · **different**.

**Comparison.** The formal package bounds normalized approximate pieces above and below and makes their residual at most θ^nKT^(1/4); it uses the unit-torus sequence formulation.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Proof in the paper.** Pages 25, 26.

**Lean correspondence.** [Upper and lower approximate norms](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsApproxSteps.lean#L44) (`Breakdown.Periodic.ApproxSizes`); [Bound approximate-profile pieces](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxSizes.lean#L914) (`Breakdown.Periodic.approxSizes`); [Small residual on every time piece](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsApproxSteps.lean#L24) (`Breakdown.Periodic.ApproxResidualSmall`); [Bound the residual of each piece](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxResidual.lean#L373) (`Breakdown.Periodic.approxResidualSmall`).

**Uses.** Lemma 3.3, Lemma 3.7, (4.4), (4.20), (4.21), (6.1), Lemma 6.1, (6.3), (6.4).

**Used by.** Proposition 2.2, (6.16), (6.17).

### (6.5)

The approximate periodic velocity has the same gradient norm as its cutoff representative and stays between a perturbed positive lower profile rate and a uniform upper rate.

[PDF page 25](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=25) · Section 6.2 · **different**.

**Comparison.** ApproxSizes gives positive upper and lower bounds for normalized unit-torus pieces; TransplantNorm has an additional L2 term, so the displayed norm equality is not literal.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Upper and lower approximate norms](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsApproxSteps.lean#L44) (`Breakdown.Periodic.ApproxSizes`); [Bound approximate-profile pieces](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxSizes.lean#L914) (`Breakdown.Periodic.approxSizes`); [Norm of a transferred compact field](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsShell.lean#L39) (`Breakdown.Periodic.TransplantNorm`).

**Uses.** (4.4), (6.1), (6.4).

**Used by.** (6.8), (6.18).

### (6.6)

The periodic linearized operator subtracts twice the interaction with the approximate velocity and the heat evolution of a periodized datum correction.

[PDF page 26](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=26) · Section 6.3 · **different**.

**Comparison.** torusOp is the same linearization pattern after splitting into normalized time pieces, with a previous-piece shift and a separate initial seed.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Linearized sequence operator on torus](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/InverseDefs.lean#L73) (`Breakdown.Periodic.torusOp`).

**Uses.** (4.16), (6.1).

**Used by.** (6.13).

### (6.7)

Restriction to the interior ball is uniformly bounded from either the whole-space or periodic homogeneous H1 space into the local gradient-L2 plus L6 norm.

[PDF page 26](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=26) · Section 6.3 · **different**.

**Comparison.** The formal shell restriction uses L6 velocity and L2 derivative data with its product norm and a scaling map on the unit torus.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Restrict a whole-space field to a ball](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsShell.lean#L17) (`Breakdown.Periodic.RestrictR3Bound`); [Bound whole-space restriction](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellR3.lean#L342) (`Breakdown.Periodic.restrictR3Bound`); [Restrict and rescale a torus field](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L386) (`Breakdown.Periodic.restrictTorus`).

**Uses.** (3.1), (3.18).

**Used by.** Lemma 6.3, (6.15).

### (6.8)

The localized linearized transport source has L^(3/2) norm controlled by the profile’s blow-up rate times the local perturbation norm.

[PDF page 27](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=27) · Section 6.3 · **different**.

**Comparison.** AdvectShellBounds states the local transport product bound for a compact test field and shell data; the time-dependent profile factor is supplied separately in the formal construction.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Estimate local advection](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareStatements.lean#L183) (`Breakdown.Periodic.AdvectShellBounds`).

**Uses.** (3.1), (6.5).

**Used by.** (6.9), (6.10).

### (6.9)

The full linearized Duhamel interactions factor through restriction to the ball containing the cutoff.

[PDF page 27](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=27) · Section 6.3 · **different**.

**Comparison.** The formal factorization is proved first for compact test fields and rescaled shell operators, then assembled on sequences, rather than for the paper’s two global A operators.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Factor whole-space local interaction](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsShell.lean#L19) (`Breakdown.Periodic.R3Factor`); [Factor periodic local interaction](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsShell.lean#L28) (`Breakdown.Periodic.TorusFactor`); [Whole-space localized interaction](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/InverseDefs.lean#L33) (`Breakdown.Periodic.r3Lambda`); [Periodic localized interaction](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/InverseDefs.lean#L36) (`Breakdown.Periodic.torusLambda`).

**Uses.** (2.3), (3.17), (6.8).

**Used by.** (6.12), (6.13), (6.14).

### (6.10)

The whole-space and periodic localized interaction operators are uniformly bounded on the weighted local curve space.

[PDF page 27](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=27) · Section 6.3 · **different**.

**Comparison.** OperatorNormBounds controls the localized sequence maps in their ℓ∞ piece norms; the paper’s Cκ formulation and specific approximate background are different.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Bounds for localized sequence operators](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsInverse.lean#L47) (`Breakdown.Periodic.OperatorNormBounds`); [Prove the sequence operator bounds](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Main.lean#L64) (`Breakdown.Periodic.operatorNormBounds_holds`).

**Uses.** (4.18), (6.8).

**Used by.** Lemma 6.3, (6.15).

### (6.11)

After restricting back to the interior ball, the periodic and whole-space interaction operators differ by O(L^(-2)) in the weighted norm.

[PDF page 27](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=27) · Section 6.3 · **different**.

**Comparison.** The formal comparison becomes at most any prescribed δ for small scale and includes propagation through sequence shifts; it does not state the L^(-2) rate.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Compare the localized inverse data](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsInverse.lean#L76) (`Breakdown.Periodic.ComparisonSmall`); [Prove inverse data become close](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareFinal.lean#L32) (`Breakdown.Periodic.comparisonSmall`).

**Uses.** (6.2), (6.4).

**Used by.** Lemma 6.3, (6.15).

### (6.12)

Applying the whole-space right inverse to localized periodic forcing and reconstructing with the periodic interaction defines a candidate periodic right inverse.

[PDF page 27](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=27) · Section 6.3 · **different**.

**Comparison.** ShellInverseTransfer records a periodic right inverse through chain operators and localized comparison maps, and shellInverseTransfer constructs it; its candidate is not the displayed γ,v,ζ,z formula.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Transfer the localized right inverse](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsSeqOps.lean#L23) (`Breakdown.Periodic.ShellInverseTransfer`); [Construct the periodic right inverse](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/InverseAlgebra.lean#L69) (`Breakdown.Periodic.shellInverseTransfer`).

**Uses.** Proposition 4.3, (6.9).

**Used by.** (6.13), (6.14), (6.15).

### (6.13)

The defect of the candidate inverse is precisely the periodic interaction of the discrepancy between its chosen local field and the local restriction of its output.

[PDF page 27](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=27) · Section 6.3 · **different**.

**Comparison.** The formal inverse-transfer proof isolates localized feedback using chainOp; it does not expose the specific ζ−z restriction identity of this display.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Chain operator with localized feedback](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsSeqOps.lean#L17) (`Breakdown.Periodic.chainOp`); [Periodic chain identity](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsInverse.lean#L27) (`Breakdown.Periodic.TorusChainEq`); [Construct the periodic right inverse](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/InverseAlgebra.lean#L69) (`Breakdown.Periodic.shellInverseTransfer`).

**Uses.** (6.6), (6.9), (6.12).

**Used by.** Lemma 6.3.

### (6.14)

The whole-space corrected field equals localized interaction plus free datum evolution, with an error term caused by replacing the profile by its cutoff.

[PDF page 28](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=28) · Section 6.3 · **different**.

**Comparison.** The formal route identifies the whole-space chain operator with its sequence linearization; this particular cutoff-error identity is not a matched statement.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Linearized sequence operator on R3](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/InverseDefs.lean#L65) (`Breakdown.Periodic.r3Op`); [Whole-space chain identity](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsInverse.lean#L20) (`Breakdown.Periodic.R3ChainEq`).

**Uses.** (4.8), (6.9), (6.12).

**Used by.** Lemma 6.3.

### Lemma 6.3

The candidate periodic right inverse is uniformly bounded and its error has operator norm O(L^(-1/2)).

[PDF page 28](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=28) · Section 6.3 · **different**.

**Comparison.** Lean supplies qualitative small-scale operator comparisons and an exact right-inverse transfer theorem; the printed candidate and explicit L^(-1/2) defect bound are absent from these statement types.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Proof in the paper.** Pages 28.

**Lean correspondence.** [Compare the localized inverse data](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsInverse.lean#L76) (`Breakdown.Periodic.ComparisonSmall`); [Prove inverse data become close](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareFinal.lean#L32) (`Breakdown.Periodic.comparisonSmall`); [Transfer the localized right inverse](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsSeqOps.lean#L23) (`Breakdown.Periodic.ShellInverseTransfer`); [Construct the periodic right inverse](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/InverseAlgebra.lean#L69) (`Breakdown.Periodic.shellInverseTransfer`).

**Uses.** Proposition 4.3, (4.21), (6.3), (6.4), (6.7), (6.10), (6.11), (6.13), (6.14).

**Used by.** Proposition 2.2, (6.16).

### (6.15)

The candidate inverse bounds the datum and trajectory by the source norm while its linearized equation defect gains a factor L^(-1/2).

[PDF page 28](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=28) · Section 6.3 · **different**.

**Comparison.** The formal transfer hypothesis is an arbitrary δ comparison of localized operators and its conclusion gives a bounded exact inverse in sequence spaces.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Compare the localized inverse data](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsInverse.lean#L76) (`Breakdown.Periodic.ComparisonSmall`); [Transfer the localized right inverse](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsSeqOps.lean#L23) (`Breakdown.Periodic.ShellInverseTransfer`).

**Uses.** (6.3), (6.4), (6.7), (6.10), (6.11), (6.12).

**Used by.** No item-level link recorded.

### (6.16)

The torus period is chosen large enough to make the inverse defect contractive, the nonlinear forcing small and the corrected lower profile bound positive.

[PDF page 28](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=28) · Section 6.4 · **different**.

**Comparison.** The formal assembly chooses small T and separate tolerances for the same three purposes; it does not state these three inequalities in C1,C2,L and c*.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Perturb a bounded right inverse](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsSeqOps.lean#L10) (`Breakdown.Periodic.RightInversePerturb`); [Correct approximate solution pieces](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsSteps.lean#L91) (`Breakdown.Periodic.SeqPerturbation`); [Upper and lower approximate norms](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsApproxSteps.lean#L44) (`Breakdown.Periodic.ApproxSizes`).

**Uses.** Lemma 4.8, Lemma 6.2, Lemma 6.3.

**Used by.** (6.17), (6.18).

### (6.17)

The corrected periodic solution starts from the periodized cutoff plus a compact datum correction, and its weighted error is O(L^(-1/2)).

[PDF page 29](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=29) · Section 6.4 · **different**.

**Comparison.** The formal correction records a bounded sequence of errors and a transferred smooth datum; the global Cκ estimate with the printed L-power is not exported.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Correct approximate solution pieces](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsSteps.lean#L91) (`Breakdown.Periodic.SeqPerturbation`); [Solve the periodic nonlinear correction](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SeqPerturbation.lean#L140) (`Breakdown.Periodic.seqPerturbation`); [Assemble the torus mild solution](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Assembly.lean#L188) (`Breakdown.Periodic.torusBlowup_of_parts`).

**Uses.** (4.24), Lemma 6.2, (6.16).

**Used by.** (6.18).

### (6.18)

The resulting large-torus solution has homogeneous H1 norm between positive multiples of (1−t)^(-1/4).

[PDF page 29](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=29) · Section 6.4 · **weaker**.

**Comparison.** The formal pieces retain positive profile bounds and bounded corrections, but GlueUnbounded exports only norm unboundedness rather than this all-time two-sided rate.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Upper and lower approximate norms](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsApproxSteps.lean#L44) (`Breakdown.Periodic.ApproxSizes`); [Correct approximate solution pieces](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsSteps.lean#L91) (`Breakdown.Periodic.SeqPerturbation`); [Unbounded norm after gluing](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsSteps.lean#L110) (`Breakdown.Periodic.GlueUnbounded`); [Prove the glued norm is unbounded](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/GlueUnbounded.lean#L48) (`Breakdown.Periodic.glueUnbounded`).

**Uses.** (6.5), (6.16), (6.17).

**Used by.** (2.6).
<!-- /passage:sec-6 -->

<a id="7"></a>

## 7. From a certificate to a profile

<!-- passage:sec-7 -->

### (7.1)

Rescaling a profile period to one introduces the coefficient 1/S in the time derivative of the similarity equation.

[PDF page 30](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=30) · Section 7.1 · **different**.

**Comparison.** The formal normalized-time equation is encoded through a weak integrand and an explicit residual field, rather than this pressure-bearing strong display.

**Scope.** Local display and named formal counterpart; this does not identify the complete certificate definitions.

**Lean correspondence.** [Equation in unit-period time](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/StConclusion.lean#L10) (`Breakdown.sigmaSimilarityIntegrand`); [Explicit residual field](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedStatement.lean#L13) (`Breakdown.weakDefectField`).

**Uses.** (1.2).

**Used by.** (7.10), Proposition 7.11.

### (7.2)

Two locally integrable fields agree modulo gradients when their difference pairs to zero with every smooth compactly supported divergence-free space-time test.

[PDF page 30](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=30) · Section 7.1 · **same**.

**Comparison.** The test class and IsRightSide use this distributional notion, with the linear residual written after integration by parts.

**Scope.** Local display and named formal counterpart; this does not identify the complete certificate definitions.

**Lean correspondence.** [Equality modulo gradients](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Statement.lean#L64) (`Breakdown.IsRightSide`); [Divergence-free space-time tests](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Defs.lean#L70) (`Breakdown.IsSpaceTimeTestField`).

**Uses.** No item-level link recorded.

**Used by.** (7.3), (7.10), Proposition 7.11.

### (7.3)

Products of a smooth periodic time factor and a compactly supported solenoidal spatial field form a test family whose finite sums are dense in the solenoidal periodic space.

[PDF page 30](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=30) · Section 7.1 · **different**.

**Comparison.** Lean proves separation by periodised compact space-time tests; the displayed tensor family is a paper presentation of the density argument.

**Scope.** Local display and named formal counterpart; this does not identify the complete certificate definitions.

**Lean correspondence.** [Periodise a compact test field](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Basic.lean#L74) (`Breakdown.Cert.periodize`); [Periodic tests separate fields](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TestDense.lean#L357) (`Breakdown.Cert.testDenseHolds_proof`).

**Uses.** (7.2).

**Used by.** Proposition 7.5.

### (7.4)

A unit-period perturbation is admissible when both its Laplacian and its full drift-time-diffusion operator are square integrable over a period.

[PDF page 30](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=30) · Section 7.1 · **different**.

**Comparison.** The formal perturbation stores weak first and second derivatives and the combined time-drift field separately, and obtains them from a closed Fourier graph.

**Scope.** Local display and named formal counterpart; this does not identify the complete certificate definitions.

**Lean correspondence.** [Admissible perturbation](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Statement.lean#L40) (`Breakdown.IsPerturbation`); [Read graph elements as weak fields](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ReadingExists.lean#L214) (`Breakdown.Cert.readingExistsHolds_proof`).

**Uses.** No item-level link recorded.

**Used by.** Lemma 7.4, (7.42).

### (7.5)

A prescribed symmetry combines a time shift with the corresponding orthogonal action on the velocity field, almost everywhere.

[PDF page 30](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=30) · Section 7.1 · **same**.

**Comparison.** Replacing y by R y turns the paper’s R-inverse convention into the formal field equation.

**Scope.** Local display and named formal counterpart; this does not identify the complete certificate definitions.

**Lean correspondence.** [Prescribed space-time symmetries](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Statement.lean#L62) (`Breakdown.IsPerturbation.invariant`).

**Uses.** (3.4).

**Used by.** (7.7), (7.39).

### (7.6)

The paper sets m to two when the symmetry set contains a half-period shift and to one otherwise.

[PDF page 30](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=30) · Section 7.1 · **different**.

**Comparison.** The formal admissibility clause allows twist = 1 even when a half-period symmetry exists; twist = 2 still requires such a symmetry.

**Scope.** Local display and named formal counterpart; this does not identify the complete certificate definitions.

**Lean correspondence.** [Available half-period improvement](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedStatement.lean#L123) (`Breakdown.IsExtendedCertificate.twist_mem`).

**Uses.** No item-level link recorded.

**Used by.** (7.26), (7.27), Remark 7.3, Proposition 7.9, (7.55).

### (7.7)

Every approximate profile obeys each prescribed space-time symmetry at every point.

[PDF page 31](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=31) · Section 7.2 · **same**.

**Comparison.** The pointwise symmetry clause is equivalent after the spatial substitution y ↦ R y.

**Scope.** Local display and named formal counterpart; this does not identify the complete certificate definitions.

**Lean correspondence.** [Approximate-profile symmetries](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedStatement.lean#L138) (`Breakdown.IsExtendedCertificate.profile_invariant`).

**Uses.** (7.5).

**Used by.** (7.39), Lemma 7.7, (7.58).

### (7.8)

The approximate profile and its first spatial derivative have uniform inverse-radius decay of orders one and two.

[PDF page 31](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=31) · Section 7.2 · **stronger**.

**Comparison.** The formal clause additionally bounds a supplied weak second derivative by an inverse-radius term of order three.

**Scope.** Local display and named formal counterpart; this does not identify the complete certificate definitions.

**Lean correspondence.** [Approximate-profile decay](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedStatement.lean#L129) (`Breakdown.IsExtendedCertificate.profile_decay`).

**Uses.** (1.3).

**Used by.** Lemma 7.7, (7.50), Figure 4.

### (7.9)

The sum of squared period-space norms of the forcing fields is bounded by b_* squared.

[PDF page 31](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=31) · Section 7.2 · **same**.

**Comparison.** The formal condition uses the equivalent sum of nonnegative period integrals.

**Scope.** Local display and named formal counterpart; this does not identify the complete certificate definitions.

**Lean correspondence.** [Combined forcing-field norm](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedStatement.lean#L149) (`Breakdown.IsExtendedCertificate.actuator_norm`).

**Uses.** No item-level link recorded.

**Used by.** Proposition 7.9, (7.55), (7.56), Proposition B.14.

### (7.10)

The approximate profile solves the forced rescaled equation up to a square-integrable residual and a gradient.

[PDF page 31](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=31) · Section 7.2 · **different**.

**Comparison.** The formal residual is explicitly assembled from weak Hessian and pressure-gradient data; the paper allows any H field representing this residual modulo gradients.

**Scope.** Local display and named formal counterpart; this does not identify the complete certificate definitions.

**Lean correspondence.** [Residual of the approximate profile](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedStatement.lean#L80) (`Breakdown.ExtendedCertificateData.defect`); [Explicit residual field](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedStatement.lean#L13) (`Breakdown.weakDefectField`).

**Uses.** (7.1), (7.2).

**Used by.** (7.12), (7.23), (7.58), (B.57).

### (7.11)

Each linear constraint pairs the perturbation gradient with a fixed matrix field over one period.

[PDF page 31](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=31) · Section 7.2 · **same**.

**Comparison.** pinValue is the displayed pairing, while targetGap translates the stored full-profile target into the paper’s perturbation target.

**Scope.** Local display and named formal counterpart; this does not identify the complete certificate definitions.

**Lean correspondence.** [Linear gradient constraint](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Statement.lean#L76) (`Breakdown.pinValue`); [Constraint target for perturbation](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedStatement.lean#L84) (`Breakdown.ExtendedCertificateData.targetGap`).

**Uses.** No item-level link recorded.

**Used by.** (7.12), (7.18), (7.24), (7.33), Proposition 7.8, (7.53).

### (7.12)

The correction must solve the nonlinear forced perturbation equation and attain its prescribed linear constraints.

[PDF page 31](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=31) · Section 7.2 · **different**.

**Comparison.** The same equation and constraints are stored after Leray projection and free inversion, together with radius and essential-supremum bounds.

**Scope.** Local display and named formal counterpart; this does not identify the complete certificate definitions.

**Lean correspondence.** [Held nonlinear solution](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedNodes.lean#L68) (`Breakdown.ExtendedCertificateData.IsHeldSolution`).

**Uses.** (7.10), (7.11), (7.13).

**Used by.** (7.38), (7.57), Proposition 7.10.

### (7.13)

Linearised convection is the sum of advection of the perturbation by the approximate profile and advection of that profile by the perturbation.

[PDF page 32](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=32) · Section 7.2 · **same**.

**Comparison.** sliceConvection evaluates exactly the two terms through the physical velocity and its gradient.

**Scope.** Local display and named formal counterpart; this does not identify the complete certificate definitions.

**Lean correspondence.** [Linearised convection](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Basic.lean#L101) (`Breakdown.Cert.sliceConvection`).

**Uses.** No item-level link recorded.

**Used by.** (7.12), (7.16), (7.19), (7.22), (7.33), Lemma 7.7, (7.52), (7.53).

### (7.14)

The correction is measured by its weighted gradient-plus-Laplacian energy, and the forcing coefficients add an omega-weighted Euclidean term.

[PDF page 32](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=32) · Section 7.3 · **different**.

**Comparison.** The physical energies agree; the internal sizeZ norm uses omega = 1 after a proved rescaling of forcing fields and multipliers.

**Scope.** Local display and named formal counterpart; this does not identify the complete certificate definitions.

**Lean correspondence.** [Weighted energy over one period](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Statement.lean#L72) (`Breakdown.weightedEnergy`); [Weighted energy of one time slice](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Statement.lean#L95) (`Breakdown.stationaryEnergy`); [Correction and multiplier norm](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Basic.lean#L55) (`Breakdown.Cert.sizeZ`).

**Uses.** No item-level link recorded.

**Used by.** (7.15), (7.18), (7.19), (7.22), (7.26), (7.28), (7.32), (7.33), (7.38), Lemma 7.6, (7.49), (7.56), Lemma B.2.

### (7.15)

The pointwise velocity estimate uses the constant c_w determined solely by the positive lower bound of the weight.

[PDF page 32](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=32) · Section 7.3 · **same**.

**Comparison.** The formal reciprocal square root simplifies to the paper’s value.

**Scope.** Local display and named formal counterpart; this does not identify the complete certificate definitions.

**Lean correspondence.** [Weighted velocity-bound constant](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Statement.lean#L104) (`Breakdown.supBoundFactor`).

**Uses.** (7.14).

**Used by.** (7.25), (7.27), Lemma 7.6, (7.48).

### (7.16)

The reference-profile convection operator is obtained by linearising advection around the reference field.

[PDF page 32](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=32) · Section 7.3 · **same**.

**Comparison.** The same sliceConvection definition is applied to the formal model field.

**Scope.** Local display and named formal counterpart; this does not identify the complete certificate definitions.

**Lean correspondence.** [Linearised convection](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Basic.lean#L101) (`Breakdown.Cert.sliceConvection`).

**Uses.** (7.13).

**Used by.** (7.18), (7.19), (7.52).

### (7.17)

The residual seminorm collects finitely many orthogonal pairings and is bounded by c_0 times the full residual norm.

[PDF page 32](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=32) · Section 7.3 · **different**.

**Comparison.** Lean uses orthonormal rows with nonnegative weights and proves the corresponding seminorm bound; this is a different representation of the displayed orthogonal family.

**Scope.** Local display and named formal counterpart; this does not identify the complete certificate definitions.

**Lean correspondence.** [Finite-direction residual seminorm](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedStatement.lean#L10) (`Breakdown.rowNorm`); [Bounds for the row seminorm](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedRowNorm.lean#L141) (`Breakdown.Cert.rowNormHolds`).

**Uses.** No item-level link recorded.

**Used by.** (7.18), (7.23), (7.52), Proposition 7.10, Proposition B.14.

### (7.18)

The weighted correction and multiplier norm is controlled by the full reference residual norm, its finite-direction seminorm and the linear constraint values.

[PDF page 32](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=32) · Section 7.3 · **same**.

**Comparison.** The formal coercive field is this estimate under the explicit weak derivative encoding; it remains an input condition at this level.

**Scope.** Local display and named formal counterpart; this does not identify the complete certificate definitions.

**Lean correspondence.** [Reference-profile inverse estimate](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedStatement.lean#L168) (`Breakdown.IsExtendedCertificate.coercive`).

**Uses.** (7.11), (7.14), (7.16), (7.17).

**Used by.** (7.52).

### (7.19)

The convection error from replacing the reference field by the approximate profile is at most c_r times the weighted correction norm.

[PDF page 32](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=32) · Section 7.3 · **same**.

**Comparison.** The formal squared-integral inequality encodes this norm bound for admissible weak perturbations.

**Scope.** Local display and named formal counterpart; this does not identify the complete certificate definitions.

**Lean correspondence.** [Reference-to-profile convection error](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedStatement.lean#L155) (`Breakdown.IsExtendedCertificate.gap_transfer`).

**Uses.** (7.13), (7.14), (7.16).

**Used by.** (7.52).

### (7.20)

The transfer loss is the convection gap multiplied by the sum of the full-residual and finite-direction constants.

[PDF page 33](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=33) · Section 7.3 · **same**.

**Comparison.** transferLoss is exactly this product under the certificate’s field names.

**Scope.** Local display and named formal counterpart; this does not identify the complete certificate definitions.

**Lean correspondence.** [Loss in the profile transfer](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedStatement.lean#L76) (`Breakdown.ExtendedCertificateData.transferLoss`).

**Uses.** No item-level link recorded.

**Used by.** (7.21), (7.24), (7.52).

### (7.21)

The transfer loss is below one and leaves enough margin for the chosen zero-constraint inverse constant.

[PDF page 33](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=33) · Section 7.3 · **same**.

**Comparison.** The two formal fields reproduce both scalar inequalities.

**Scope.** Local display and named formal counterpart; this does not identify the complete certificate definitions.

**Lean correspondence.** [Transfer loss is below one](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedStatement.lean#L111) (`Breakdown.IsExtendedCertificate.transfer_lt`); [Zero-constraint inverse bound](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedStatement.lean#L112) (`Breakdown.IsExtendedCertificate.coerciveTotal_ge`).

**Uses.** (7.20).

**Used by.** Proposition 7.10, Proposition B.14.

### (7.22)

At every time the linearised quadratic form is bounded below by minus c_3 times the weighted perturbation energy on the spatially invariant class.

[PDF page 33](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=33) · Section 7.3 · **same**.

**Comparison.** The formal proof obtains this bound from the model bound plus the form-shift condition, then applies it to admissible weak slices.

**Scope.** Local display and named formal counterpart; this does not identify the complete certificate definitions.

**Lean correspondence.** [Frozen-time quadratic form](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Statement.lean#L90) (`Breakdown.frozenForm`); [Transfer the frozen-form bound](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedFrozenBridge.lean#L168) (`Breakdown.Cert.extendedFrozenBridgeHolds_of`).

**Uses.** (7.13), (7.14).

**Used by.** Proposition 7.9, (7.55), (7.56).

### (7.23)

The residual’s full norm and finite-direction seminorm have parameter-dependent bounds, with a common upper bound for the full norm.

[PDF page 33](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=33) · Section 7.3 · **same**.

**Comparison.** These three fields carry the displayed inequalities, with squared nonnegative integrals for the full norm.

**Scope.** Local display and named formal counterpart; this does not identify the complete certificate definitions.

**Lean correspondence.** [Residual norm bound](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedStatement.lean#L178) (`Breakdown.IsExtendedCertificate.defect_l2`); [Residual row bound](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedStatement.lean#L180) (`Breakdown.IsExtendedCertificate.defect_rows`); [Uniform residual bound](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedStatement.lean#L181) (`Breakdown.IsExtendedCertificate.defect_le`).

**Uses.** (7.10), (7.17).

**Used by.** (7.24), (7.27), Proposition 7.10, Proposition B.14.

### (7.24)

The combined residual and prescribed-constraint contribution fits within the transfer-adjusted radius epsilon.

[PDF page 33](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=33) · Section 7.3 · **same**.

**Comparison.** The formal targetGap is the paper’s prescribed correction constraint; the remaining constants give the same budget.

**Scope.** Local display and named formal counterpart; this does not identify the complete certificate definitions.

**Lean correspondence.** [Residual and constraint budget](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedStatement.lean#L182) (`Breakdown.IsExtendedCertificate.size`); [Constraint target for perturbation](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedStatement.lean#L84) (`Breakdown.ExtendedCertificateData.targetGap`).

**Uses.** (7.11), (7.20), (7.23).

**Used by.** Proposition 7.10, (7.59), Proposition B.14.

### (7.25)

The product 2 c_L c_w M is strictly below one.

[PDF page 33](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=33) · Section 7.3 · **same**.

**Comparison.** small_first states this exact scalar inequality.

**Scope.** Local display and named formal counterpart; this does not identify the complete certificate definitions.

**Lean correspondence.** [Nonlinear smallness condition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedStatement.lean#L184) (`Breakdown.IsExtendedCertificate.small_first`).

**Uses.** (7.15).

**Used by.** Proposition 7.10, (7.59), Proposition B.14.

### (7.26)

The second scalar budget bounds the energy-to-supremum amplification by M squared.

[PDF page 33](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=33) · Section 7.3 · **same**.

**Comparison.** small_second is algebraically identical; its use in the Lean difference estimate is an additional proof role, although the paper explicitly leaves it unused.

**Scope.** Local display and named formal counterpart; this does not identify the complete certificate definitions.

**Lean correspondence.** [Second supremum budget](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedStatement.lean#L185) (`Breakdown.IsExtendedCertificate.small_second`); [Contraction at a fixed parameter](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedHeldContracts.lean#L185) (`Breakdown.Cert.extendedHeldContractsHolds_of`).

**Uses.** (7.6), (7.14).

**Used by.** Proposition B.14.

### (7.27)

The residual, quadratic term and forcing contribution fit within the supremum budget for corrections of weighted size at most 2 epsilon.

[PDF page 33](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=33) · Section 7.3 · **same**.

**Comparison.** small_third records the same inequality and the held-step proof uses it to preserve the gradient supremum.

**Scope.** Local display and named formal counterpart; this does not identify the complete certificate definitions.

**Lean correspondence.** [Held-set supremum budget](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedStatement.lean#L188) (`Breakdown.IsExtendedCertificate.small_third`); [The nonlinear step keeps both bounds](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedHeldMapsTo.lean#L179) (`Breakdown.Cert.extendedHeldMapsToHolds_of`).

**Uses.** (7.6), (7.15), (7.23).

**Used by.** Proposition 7.10, (7.59), Proposition B.14.

### (7.28)

The approximate profile’s gradient energy is strictly too large for an admissible correction to cancel it.

[PDF page 33](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=33) · Section 7.3 · **same**.

**Comparison.** Dividing the paper inequality by the positive lower weight gives the formal nontrivial clause.

**Scope.** Local display and named formal counterpart; this does not identify the complete certificate definitions.

**Lean correspondence.** [Correction cannot cancel the profile](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedStatement.lean#L224) (`Breakdown.IsExtendedCertificate.nontrivial`); [The corrected profile is nonzero](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedHeldNonzero.lean#L15) (`Breakdown.Cert.extendedHeldNonzeroHolds_of`).

**Uses.** (7.14).

**Used by.** Theorem 7.1, Proposition B.14.

### (7.29)

The parameter set combines coordinate intervals on J with a diagonally scaled Euclidean ball on the complementary coordinates.

[PDF page 33](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=33) · Section 7.3 · **same**.

**Comparison.** params records the same mixed geometry; nonzero scales and nonnegative radii are separate certificate clauses.

**Scope.** Local display and named formal counterpart; this does not identify the complete certificate definitions.

**Lean correspondence.** [Admissible parameter set](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedStatement.lean#L72) (`Breakdown.ExtendedCertificateData.params`).

**Uses.** No item-level link recorded.

**Used by.** (7.30), (7.36), (7.60), (7.61), Lemma B.13, (B.59), Proposition B.14.

### (7.30)

The parameter update subtracts a diagonally scaled frame pairing with the total forcing multiplier.

[PDF page 34](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=34) · Section 7.3 · **same**.

**Comparison.** The local map T in testSetZero_of is the same update, written using the transpose frame matrix.

**Scope.** Local display and named formal counterpart; this does not identify the complete certificate definitions.

**Lean correspondence.** [Zero of the parameter multiplier](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Held/TestSetZero.lean#L92) (`Breakdown.Held.testSetZero_of`).

**Uses.** (7.29).

**Used by.** Proposition 7.10, (7.60), (7.61).

### (7.31)

Pairing every forcing field with an adjoint test produces the vector used to compare the frame with the forcing.

[PDF page 34](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=34) · Section 7.3 · **different**.

**Comparison.** The pairing is the same; the named formal vector stores this vector minus the frame column, which is the discrepancy used in the inclusion budget.

**Scope.** Local display and named formal counterpart; this does not identify the complete certificate definitions.

**Lean correspondence.** [Pairing over one period](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L24) (`Breakdown.periodPairing`); [Forcing-to-adjoint discrepancy](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedStatement.lean#L91) (`Breakdown.ExtendedCertificateData.actuatorAdjointError`).

**Uses.** No item-level link recorded.

**Used by.** (7.34), (7.35).

### (7.32)

The quadratic perturbation paired with each selected adjoint field is bounded by its assigned constant times the correction energy.

[PDF page 34](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=34) · Section 7.3 · **same**.

**Comparison.** adjoint_quadratic states the absolute pairing bound for the formal weak perturbation class.

**Scope.** Local display and named formal counterpart; this does not identify the complete certificate definitions.

**Lean correspondence.** [Quadratic adjoint error](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedStatement.lean#L201) (`Breakdown.IsExtendedCertificate.adjoint_quadratic`).

**Uses.** (7.14).

**Used by.** (7.35), (7.60), (7.61).

### (7.33)

Testing the linearised residual against an adjoint field differs from the coupled linear constraints by at most a constant times the correction norm.

[PDF page 34](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=34) · Section 7.3 · **same**.

**Comparison.** adjoint_defect retains the unprojected residual and the coupled constraint pairing.

**Scope.** Local display and named formal counterpart; this does not identify the complete certificate definitions.

**Lean correspondence.** [Linear adjoint error](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedStatement.lean#L205) (`Breakdown.IsExtendedCertificate.adjoint_defect`).

**Uses.** (7.11), (7.13), (7.14).

**Used by.** (7.34), (7.35), (7.60), (7.61).

### (7.34)

The adjusted approximate forcing multiplier stays within the assigned offset from the diagonal parameter term.

[PDF page 34](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=34) · Section 7.3 · **same**.

**Comparison.** adjustedMultiplier expands into the same frame, residual and constraint terms, and adjoint_offset supplies the bound.

**Scope.** Local display and named formal counterpart; this does not identify the complete certificate definitions.

**Lean correspondence.** [Approximate parameter offset](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedStatement.lean#L212) (`Breakdown.IsExtendedCertificate.adjoint_offset`); [Adjusted approximate multiplier](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedStatement.lean#L87) (`Breakdown.ExtendedCertificateData.adjustedMultiplier`).

**Uses.** (7.31), (7.33).

**Used by.** (7.35), (7.60), (7.61).

### (7.35)

The quadratic, linear-adjoint and frame-discrepancy errors together with the offset fit inside each selected parameter interval.

[PDF page 34](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=34) · Section 7.3 · **same**.

**Comparison.** The formal inclusion clause has the same square-root combination and non-strict inequality.

**Scope.** Local display and named formal counterpart; this does not identify the complete certificate definitions.

**Lean correspondence.** [Adjoint-coordinate inclusion](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedStatement.lean#L214) (`Breakdown.IsExtendedCertificate.adjoint_inclusion`).

**Uses.** (7.31), (7.32), (7.33), (7.34).

**Used by.** (7.60), (7.61), Proposition B.14.

### (7.36)

The complementary frame coordinates have a uniform operator bound and the approximate multiplier has a bounded complementary offset.

[PDF page 34](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=34) · Section 7.3 · **same**.

**Comparison.** stiff_norm and stiff_offset are the two displayed Euclidean bounds on the complement of adjointSet.

**Scope.** Local display and named formal counterpart; this does not identify the complete certificate definitions.

**Lean correspondence.** [Complementary frame norm](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedStatement.lean#L219) (`Breakdown.IsExtendedCertificate.stiff_norm`); [Complementary parameter offset](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedStatement.lean#L221) (`Breakdown.IsExtendedCertificate.stiff_offset`).

**Uses.** (7.29).

**Used by.** (7.37), (7.60), (7.61), Proposition B.14.

### (7.37)

The correction’s complementary forcing error plus the approximate offset fits inside the remaining parameter radius.

[PDF page 34](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=34) · Section 7.3 · **same**.

**Comparison.** stiff_inclusion is exactly this scalar budget.

**Scope.** Local display and named formal counterpart; this does not identify the complete certificate definitions.

**Lean correspondence.** [Complementary-coordinate inclusion](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedStatement.lean#L223) (`Breakdown.IsExtendedCertificate.stiff_inclusion`).

**Uses.** (7.36).

**Used by.** (7.60), (7.61), Proposition B.14.

### Theorem 7.1

A certificate yields a nonzero smooth periodic similarity profile at a selected parameter, with the same correction satisfying the quantitative bounds, constraints and all prescribed symmetries.

[PDF page 35](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=35) · Section 7.4 · **different**.

**Comparison.** The formal certificate has additional written requirements and the public theorem exposes a weaker existential weak profile; the separate smoothing result does not expose the full same-witness quantitative bundle.

**Scope.** The stated result and the exposed formal interface, including explicitly noted output omissions.

**Lean correspondence.** [Extended certificate gives weak profile](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedMain.lean#L56) (`Breakdown.extended_certificate_orbit_proved`); [Weak profile gives a smooth profile](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/Main.lean#L8) (`Breakdown.FarField.periodicLerayProfileExists_of_weak`); [Choose a force-free parameter](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedExistsZeroHeld.lean#L102) (`Breakdown.Cert.extendedExistsZeroHeldHolds_of`); [Construct the corrected weak profile](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedSigmaProfileOfHeld.lean#L232) (`Breakdown.Cert.extendedSigmaProfileOfHeldHolds_of`).

**Uses.** (1.2), (1.3), (7.28), (7.38), (7.39), Proposition 7.10, Proposition 7.11.

**Used by.** Corollary 7.2.

### (7.38)

The chosen smooth profile has a correction with the stated weighted energy, uniform gradient bound and prescribed constraints, using the same selected parameter.

[PDF page 35](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=35) · Section 7.4 · **weaker**.

**Comparison.** Internal held solutions carry these bounds before smoothing, after multiplier normalisation; the pinned endpoint does not expose their transport to the same final smooth profile.

**Scope.** Local display and named formal counterpart; this does not identify the complete certificate definitions.

**Lean correspondence.** [Held correction radius](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedNodes.lean#L74) (`Breakdown.ExtendedCertificateData.IsHeldSolution.size`); [Held gradient supremum](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedNodes.lean#L75) (`Breakdown.ExtendedCertificateData.IsHeldSolution.sup`); [Held gradient constraints](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedNodes.lean#L73) (`Breakdown.ExtendedCertificateData.IsHeldSolution.pins`); [Choose a force-free parameter](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedExistsZeroHeld.lean#L102) (`Breakdown.Cert.extendedExistsZeroHeldHolds_of`).

**Uses.** (7.12), (7.14).

**Used by.** Theorem 7.1.

### (7.39)

The final smooth profile inherits every prescribed space-time symmetry at every point.

[PDF page 35](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=35) · Section 7.4 · **weaker**.

**Comparison.** The approximate field and weak correction carry the symmetry data, but the existential IsSigmaProfile output drops the complete Gamma bundle and the public endpoint does not re-expose this conclusion.

**Scope.** Local display and named formal counterpart; this does not identify the complete certificate definitions.

**Lean correspondence.** [Prescribed space-time symmetries](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Statement.lean#L62) (`Breakdown.IsPerturbation.invariant`); [Approximate-profile symmetries](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedStatement.lean#L138) (`Breakdown.IsExtendedCertificate.profile_invariant`); [Construct the corrected weak profile](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedSigmaProfileOfHeld.lean#L232) (`Breakdown.Cert.extendedSigmaProfileOfHeldHolds_of`).

**Uses.** (7.5), (7.7).

**Used by.** Theorem 7.1, Remark 7.3.

### Corollary 7.2

Existence of a certificate gives the space and torus blow-up conclusions of Theorem 1.1 with the profile selected by Theorem 7.1.

[PDF page 35](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=35) · Section 7.4 · **different**.

**Comparison.** The public formal endpoints are conditional nonexistence of global smooth solutions; they do not expose the paper’s trajectory, rate, convergence and selected-profile data.

**Scope.** The stated result and the exposed formal interface, including explicitly noted output omissions.

**Lean correspondence.** [Extended certificate gives space blow-up](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Solution.lean#L298) (`Breakdown.extended_certificate_breakdown_on_space`); [Weak profile gives torus blow-up](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/Main.lean#L13) (`Breakdown.FarField.breakdownOnTorus_of_weak`); [Extended certificate gives weak profile](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedMain.lean#L56) (`Breakdown.extended_certificate_orbit_proved`).

**Uses.** Theorem 1.1, Theorem 7.1.

**Used by.** No item-level link recorded.

### Remark 7.3

Every prescribed symmetry with a positive time shift gives another valid profile period and isometry, including a half-period choice when available.

[PDF page 35](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=35) · Section 7.4 · **weaker**.

**Comparison.** The constituent symmetry equations are present, but no pinned public declaration exposes this alternative-period statement for the same final smooth profile.

**Scope.** The stated result and the exposed formal interface, including explicitly noted output omissions.

**Lean correspondence.** [Prescribed space-time symmetries](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Statement.lean#L62) (`Breakdown.IsPerturbation.invariant`); [Approximate-profile symmetries](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedStatement.lean#L138) (`Breakdown.IsExtendedCertificate.profile_invariant`).

**Uses.** (1.2), (1.3), (7.6), (7.39).

**Used by.** No item-level link recorded.

### (7.40)

The exponential change from normalized similarity time to physical time rescales space and velocity with opposite half-exponents.

[PDF page 36](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=36) · Section 7.5 · **same**.

**Comparison.** physicalCurve uses the equivalent inverse logarithmic time substitution and dilation, after replacing S theta by similarity time.

**Scope.** Local display and named formal counterpart; this does not identify the complete certificate definitions.

**Lean correspondence.** [Physical-time velocity curve](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/Basic.lean#L20) (`Breakdown.WeakProfile.physicalCurve`).

**Uses.** (1.4), (3.4).

**Used by.** (7.41), Lemma 7.4, (7.44), Proposition 7.5, (7.63).

### (7.41)

Under the exponential coordinate change, the free similarity operator becomes the heat operator and the Laplacian has the same cubic scaling factor.

[PDF page 36](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=36) · Section 7.5 · **different**.

**Comparison.** The formal counterpart establishes the transformed weak equation against tests; the two pointwise chain-rule identities are not its exposed statement.

**Scope.** Local display and named formal counterpart; this does not identify the complete certificate definitions.

**Lean correspondence.** [Weak equation in physical time](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/PhysicalIdentity.lean#L168) (`Breakdown.WeakProfile.physicalIdentity_of_parts`).

**Uses.** (7.40).

**Used by.** Lemma 7.4, (7.44), Proposition 7.5, (7.46).

### Lemma 7.4

An admissible perturbation has a solenoidal free residual, a continuous periodic energy-space representative and the local and averaged energy identities.

[PDF page 36](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=36) · Section 7.5 · **different**.

**Comparison.** These conclusions are implemented for the constructed free inverse and its physical representatives across several interfaces, rather than one theorem on the paper’s D_S space.

**Scope.** The stated result and the exposed formal interface, including explicitly noted output omissions.

**Lean correspondence.** [Local energy identity](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeEnergyLocal.lean#L625) (`Breakdown.Cert.freeEnergyLocalHolds_of`); [Continuous periodic energy-space curve](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeEnergyLocal.lean#L564) (`Breakdown.Cert.Internal.FreeEnergyLocal.exists_energyCurve`); [Free inverse and energy bound](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeInv.lean#L324) (`Breakdown.Cert.freeInvHolds_of`); [Choose bounded time representatives](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SliceReading.lean#L305) (`Breakdown.Cert.sliceReadingHolds_of`); [Read graph elements as weak fields](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ReadingExists.lean#L214) (`Breakdown.Cert.readingExistsHolds_proof`).

**Uses.** (7.4), (7.40), (7.41), (7.42), (7.43), (7.44), (7.45).

**Used by.** Lemma 7.6, (7.49), (7.54), Proposition 7.9, Lemma B.12, (B.54).

### (7.42)

The normalized-time derivative of the gradient energy balances Laplacian dissipation, the quarter-gradient term and the free residual pairing.

[PDF page 36](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=36) · Section 7.5 · **same**.

**Comparison.** The formal theorem gives an interval-integrated identity for a continuous energy representative of the constructed free inverse; its coefficients agree with the displayed differential identity after the physical-energy identification and the corresponding almost-everywhere reading.

**Scope.** The matching energy-identity component for the constructed free inverse, after physical-energy identification and the integrated-to-almost-everywhere differential passage; no unproved identification of the entire printed D_S domain is asserted.

**Lean correspondence.** [Local energy identity](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeEnergyLocal.lean#L625) (`Breakdown.Cert.freeEnergyLocalHolds_of`); [Physical and graph energies agree](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ReadingEnergy.lean#L293) (`Breakdown.Cert.readingEnergyHolds_of`).

**Uses.** (7.4).

**Used by.** Lemma 7.4, (7.43), Proposition 7.9, (7.55).

### (7.43)

Averaging the free energy identity over a period bounds the Laplacian energy plus one quarter of the gradient energy by the residual energy.

[PDF page 36](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=36) · Section 7.5 · **same**.

**Comparison.** freeInvHolds_of gives the displayed quadratic estimate for the constructed free inverse, and the local energy theorem supplies the pairing equality after integration over one period; physical energies are identified by the separate reading interface.

**Scope.** The free-inverse energy estimate and period-integrated identity; its numerical constants match after the physical-energy identification.

**Lean correspondence.** [Free inverse and energy bound](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeInv.lean#L324) (`Breakdown.Cert.freeInvHolds_of`); [Local energy identity](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeEnergyLocal.lean#L625) (`Breakdown.Cert.freeEnergyLocalHolds_of`).

**Uses.** (7.42).

**Used by.** Lemma 7.4, Proposition 7.5, Lemma 7.7, Proposition 7.8, Proposition B.1.

### (7.44)

The change of variables gives exponential scaling formulas for the gradient energy and the time-derivative–Laplacian pairing.

[PDF page 36](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=36) · Section 7.5 · **no Lean**.

**Comparison.** Dilation and weak-coordinate-change components are present, but no source declaration was located for this paired physical-coordinate energy and derivative-pairing formula at the paper's weak regularity.

**Scope.** Local display and named formal counterpart; this does not identify the complete certificate definitions.

**Lean correspondence.** No direct audited counterpart assigned.

**Uses.** (7.40), (7.41).

**Used by.** Lemma 7.4.

### (7.45)

The physical heat trajectory has a continuous gradient representative whose energy increment equals minus twice the time-integrated derivative–Laplacian pairing.

[PDF page 36](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=36) · Section 7.5 · **different**.

**Comparison.** Lean constructs a continuous periodic representative satisfying an integrated energy identity for freeInv in similarity time; the printed line is the physical-time identity obtained from a general Lions-Magenes argument.

**Scope.** Matched: A continuous representative, almost-everywhere agreement with the constructed free inverse, and its interval energy identity in similarity time. Remaining: The general physical-time identity for every field with the paper's weak regularity, its displayed physical derivative pairing, and the Lions-Magenes lemma as a reusable formal result.

**Lean correspondence.** [The similarity-time energy identity](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeEnergyLocal.lean#L17) (`Breakdown.Cert.Internal.FreeEnergyLocal.IsEnergyCurve`); [Continuous periodic energy-space curve](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeEnergyLocal.lean#L564) (`Breakdown.Cert.Internal.FreeEnergyLocal.exists_energyCurve`); [Local energy identity](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeEnergyLocal.lean#L625) (`Breakdown.Cert.freeEnergyLocalHolds_of`).

**Uses.** (3.2).

**Used by.** Lemma 7.4.

### Proposition 7.5

The free similarity operator is invertible on periodic solenoidal fields, respects the prescribed symmetries and has weak and local-strong continuity when the period varies.

[PDF page 37](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=37) · Section 7.5 · **different**.

**Comparison.** The Fourier graph inverse, symmetry, weak convergence and local compactness are proved separately; the statement is not exposed as a bijection of the paper’s D_S.

**Scope.** The stated result and the exposed formal interface, including explicitly noted output omissions.

**Lean correspondence.** [Build the free gradient inverse](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/GradInvSpec.lean#L374) (`Breakdown.Cert.exists_gradInvSpec`); [Free inverse and energy bound](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeInv.lean#L324) (`Breakdown.Cert.freeInvHolds_of`); [The free inverse preserves symmetry](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeEquivariant.lean#L168) (`Breakdown.Cert.freeEquivariantHolds_of`); [Weak continuity as the period varies](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/PeriodContinuity.lean#L266) (`Breakdown.Cert.periodContinuityHolds_of`); [Compactness on bounded cylinders](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/LocalCompactness.lean#L412) (`Breakdown.Cert.localCompactnessHolds_of`).

**Uses.** (3.1), (3.3), (3.5), (7.3), (7.40), (7.41), (7.43), (7.46), (7.47).

**Used by.** Lemma 7.7, Proposition 7.8.

### (7.46)

The dilated heat evolution solves the homogeneous free equation in similarity time.

[PDF page 37](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=37) · Section 7.5 · **same**.

**Comparison.** propagator_weak_derivative proves the same free evolution equation through test-function pairings.

**Scope.** Local display and named formal counterpart; this does not identify the complete certificate definitions.

**Lean correspondence.** [Free propagator equation](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportMild.lean#L471) (`Breakdown.Cert.Internal.FreePerturbation.propagator_weak_derivative`).

**Uses.** (7.41).

**Used by.** Proposition 7.5.

### (7.47)

The free evolution damps its gradient and Laplacian norms with exponential rates one quarter and three quarters.

[PDF page 37](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=37) · Section 7.5 · **weaker**.

**Comparison.** The cited formal operator estimate directly carries the gradient rate; it does not separately state the accompanying Laplacian rate of this display.

**Scope.** Local display and named formal counterpart; this does not identify the complete certificate definitions.

**Lean correspondence.** [Decay of the free gradient norm](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L223) (`Breakdown.Cert.Internal.DenseEnergyBand.norm_semigroupX_le`).

**Uses.** (3.3), (3.5).

**Used by.** Proposition 7.5.

### Lemma 7.6

A weighted two-derivative energy controls the velocity supremum and gives the stated quadratic convection estimate over a period.

[PDF page 38](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=38) · Section 7.6 · **same**.

**Comparison.** The formal slice bound and bilinear period-space estimate yield both displayed conclusions after the physical-energy identification.

**Scope.** The stated result and the exposed formal interface, including explicitly noted output omissions.

**Lean correspondence.** [Velocity bound from two derivatives](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SliceSupBound.lean#L10) (`Breakdown.Cert.sliceSupBoundHolds_of`); [Quadratic-term norm estimate](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProductBound.lean#L377) (`Breakdown.Cert.productBoundHolds_of`).

**Uses.** (7.14), (7.15), Lemma 7.4, (7.48), (7.49).

**Used by.** Proposition 7.10.

### (7.48)

The squared velocity supremum is bounded by c_w squared times the sum of the squared Laplacian L2 norm and w_* times the squared gradient L2 norm.

[PDF page 38](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=38) · Section 7.6 · **same**.

**Comparison.** The formal slice bound proves the product estimate from which this weighted version follows by the arithmetic–geometric mean inequality.

**Scope.** The derived weighted numerical inequality after the physical-energy identification; SliceSupBoundHolds itself states a product bound on the Fourier graph.

**Lean correspondence.** [Velocity bound from two derivatives](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SliceSupBound.lean#L10) (`Breakdown.Cert.sliceSupBoundHolds_of`); [Weighted velocity-bound constant](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Statement.lean#L104) (`Breakdown.supBoundFactor`).

**Uses.** (7.15).

**Used by.** Lemma 7.6, (7.49), (B.46).

### (7.49)

The quadratic convection norm is at most c_w times the weighted correction norm and its gradient supremum.

[PDF page 38](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=38) · Section 7.6 · **stronger**.

**Comparison.** The formal estimate treats two possibly distinct factors with an admissible weight and a finite gradient supremum; the displayed quadratic bound is its diagonal case after the physical-energy identification.

**Scope.** The bilinear product-estimate component with an admissible weight and finite gradient supremum; the paper’s displayed bound is its diagonal physical reading.

**Lean correspondence.** [Quadratic-term norm estimate](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProductBound.lean#L377) (`Breakdown.Cert.productBoundHolds_of`).

**Uses.** (7.14), Lemma 7.4, (7.48).

**Used by.** Lemma 7.6.

### Lemma 7.7

Linearised convection is bounded by the gradient norm, preserves symmetries and becomes compact after composition with the free inverse.

[PDF page 39](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=39) · Section 7.6 · **same**.

**Comparison.** The three assertions are supplied by separate proved interfaces using coefficient decay, invariant subspaces and local compactness with tail control.

**Scope.** The stated result and the exposed formal interface, including explicitly noted output omissions.

**Lean correspondence.** [Bounded linearised convection](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedConvection.lean#L272) (`Breakdown.Cert.extendedConvectionHolds_of`); [Symmetry of the projected data](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedInvariance.lean#L347) (`Breakdown.Cert.extendedInvarianceHolds_of`); [Compact convection after free inversion](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedConvectionCompact.lean#L383) (`Breakdown.Cert.extendedConvectionCompactHolds_of`).

**Uses.** (3.1), (7.7), (7.8), (7.13), (7.43), Proposition 7.5, (7.50), (7.51).

**Used by.** Proposition 7.8, Lemma B.12.

### (7.50)

The two convection terms are controlled pointwise by the profile decay factors multiplying the perturbation gradient and velocity.

[PDF page 39](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=39) · Section 7.6 · **different**.

**Comparison.** The corresponding formal lemmas prove norm estimates for the two terms using the same coefficient decay; the combined pointwise line is not their exposed conclusion.

**Scope.** Local display and named formal counterpart; this does not identify the complete certificate definitions.

**Lean correspondence.** [Approximate velocity times gradient](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedConvection.lean#L49) (`Breakdown.Cert.Internal.ConvectionFirstOrder.first_term`); [Perturbation times profile gradient](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedConvection.lean#L72) (`Breakdown.Cert.Internal.ConvectionFirstOrder.second_term`).

**Uses.** (7.8).

**Used by.** Lemma 7.7, (7.51).

### (7.51)

Outside a ball, the convection norm is bounded by a tail coefficient tending to zero times the perturbation gradient norm.

[PDF page 39](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=39) · Section 7.6 · **weaker**.

**Comparison.** The formal squared L2 tail bound decays as 1/(1+R), sufficient for compactness but coarser than the paper’s displayed L3-tail coefficient.

**Scope.** Local display and named formal counterpart; this does not identify the complete certificate definitions.

**Lean correspondence.** [Convection outside a large ball](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedConvectionCompact.lean#L141) (`Breakdown.Cert.Internal.ExtendedConvectionCompact.slice_tail_first`).

**Uses.** (3.1), (7.50).

**Used by.** Lemma 7.7.

### (7.52)

The reference coercive estimate transfers to the approximate profile with its left side multiplied by one minus the transfer loss.

[PDF page 39](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=39) · Section 7.7 · **same**.

**Comparison.** The proof absorbs the convection gap and rescales the residual, row and constraint constants by the positive transfer margin.

**Scope.** Local display and named formal counterpart; this does not identify the complete certificate definitions.

**Lean correspondence.** [Absorb the reference-profile error](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedAtProfile.lean#L448) (`Breakdown.Cert.extendedAtProfileHolds`).

**Uses.** (7.13), (7.16), (7.17), (7.18), (7.19), (7.20).

**Used by.** Proposition 7.8, Proposition 7.10, (7.59).

### Proposition 7.8

The linearised equation with forcing coefficients and matching linear constraints is uniquely solvable for every invariant projected right-hand side and constraint target.

[PDF page 40](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=40) · Section 7.7 · **same**. The embedded PDF destination points to page 39; the printed heading is on page 40.

**Comparison.** The formal operator uses f = T_S v as its unknown and proves invertibility by coercivity and a compact bordered perturbation, after normalising the certificate.

**Scope.** The stated result and the exposed formal interface, including explicitly noted output omissions.

**Lean correspondence.** [Invert the constrained linear problem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedBorderedInvertible.lean#L101) (`Breakdown.Cert.extendedBorderedInvertibleHolds_of`); [Convection with forcing and constraints](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Basic.lean#L172) (`Breakdown.Cert.bordered`).

**Uses.** (3.1), (7.11), (7.43), Proposition 7.5, Lemma 7.7, (7.52), (7.53), (7.54).

**Used by.** Proposition 7.10.

### (7.53)

The constrained linear map returns the projected linearised residual and the correction’s linear constraint vector.

[PDF page 40](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=40) · Section 7.7 · **different**.

**Comparison.** The formal bordered operator is this map after the substitution f = T_S v, so its domain is a pair of a free right-hand side and multipliers.

**Scope.** Local display and named formal counterpart; this does not identify the complete certificate definitions.

**Lean correspondence.** [Convection with forcing and constraints](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Basic.lean#L172) (`Breakdown.Cert.bordered`).

**Uses.** (7.11), (7.13).

**Used by.** Proposition 7.8, (7.54).

### (7.54)

Because the free part is solenoidal, projecting the full residual only projects convection and the forcing fields.

[PDF page 40](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=40) · Section 7.7 · **same**.

**Comparison.** The formal first component starts with f and adds already projected convection and actuator terms.

**Scope.** Local display and named formal counterpart; this does not identify the complete certificate definitions.

**Lean correspondence.** [Convection with forcing and constraints](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Basic.lean#L172) (`Breakdown.Cert.bordered`).

**Uses.** Lemma 7.4, (7.53).

**Used by.** Proposition 7.8.

### Proposition 7.9

A solution of the linearised constrained equation has a uniform-in-time gradient estimate determined by its weighted energy, residual size, forcing size and available half-period symmetry.

[PDF page 40](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=40) · Section 7.7 · **same**.

**Comparison.** The proved bound has the displayed constants in the Fourier representation, with the continuous energy identity recovering the pointwise supremum interpretation.

**Scope.** The stated result and the exposed formal interface, including explicitly noted output omissions.

**Lean correspondence.** [Uniform gradient bound](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedSupBound.lean#L15) (`Breakdown.Cert.extendedSupBoundHolds_of`).

**Uses.** (7.6), (7.9), (7.22), Lemma 7.4, (7.42), (7.55), (7.56).

**Used by.** Proposition 7.10.

### (7.55)

The gradient supremum is controlled by weighted mean energy and the residual-forcing contribution, with the half-period improvement when available.

[PDF page 40](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=40) · Section 7.7 · **same**.

**Comparison.** The formal bound has the same constants for the free-inverse representative and uses the essential supremum; the continuous energy representative supplies the pointwise reading.

**Scope.** Local display and named formal counterpart; this does not identify the complete certificate definitions.

**Lean correspondence.** [Uniform gradient bound](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedSupBound.lean#L15) (`Breakdown.Cert.extendedSupBoundHolds_of`).

**Uses.** (7.6), (7.9), (7.22), (7.42).

**Used by.** Proposition 7.9, (7.59).

### (7.56)

The mean upper bound for energy growth is at most the residual-plus-forcing norm times the correction norm, plus the frozen-form loss.

[PDF page 41](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=41) · Section 7.7 · **same**.

**Comparison.** This estimate occurs as the local bound hIG inside core_bound; the declaration then integrates it into the supremum estimate.

**Scope.** Local display and named formal counterpart; this does not identify the complete certificate definitions.

**Lean correspondence.** [Energy growth over a full period](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SupBound.lean#L265) (`Breakdown.Cert.Internal.SupBound.core_bound`).

**Uses.** (7.9), (7.14), (7.22).

**Used by.** Proposition 7.9.

### (7.57)

For fixed parameter and quadratic input, the linear problem has right side minus the approximate residual minus that input and keeps the prescribed constraints.

[PDF page 41](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=41) · Section 7.8 · **different**.

**Comparison.** heldRight substitutes the current correction’s quadratic term immediately, as required by the fixed-parameter contraction route.

**Scope.** Local display and named formal counterpart; this does not identify the complete certificate definitions.

**Lean correspondence.** [Right-hand side of the nonlinear step](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedNodes.lean#L61) (`Breakdown.ExtendedCertificateData.heldRight`); [Convection with forcing and constraints](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Basic.lean#L172) (`Breakdown.Cert.bordered`).

**Uses.** (7.12).

**Used by.** Proposition 7.10.

### (7.58)

The projected approximate residual is invariant under the certificate symmetries and depends continuously on the parameter when paired with divergence-free tests.

[PDF page 41](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=41) · Section 7.8 · **same**.

**Comparison.** The two formal interfaces prove projected invariance and testwise continuity without requiring continuity of the raw residual.

**Scope.** Local display and named formal counterpart; this does not identify the complete certificate definitions.

**Lean correspondence.** [Symmetry of the projected data](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedInvariance.lean#L347) (`Breakdown.Cert.extendedInvarianceHolds_of`); [Continuity of tested residual data](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedDataContinuity.lean#L436) (`Breakdown.Cert.extendedDataContinuityHolds_of`).

**Uses.** (7.7), (7.10).

**Used by.** Proposition 7.10.

### Proposition 7.10

Some admissible parameter has a nonlinear correction satisfying the two size bounds, the prescribed constraints and exact cancellation of the auxiliary force.

[PDF page 42](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=42) · Section 7.8 · **different**.

**Comparison.** The Lean route first proves a unique bounded correction for each fixed parameter by contraction, then finds a finite-dimensional multiplier zero; the paper uses a joint weak-topology Schauder map.

**Scope.** The stated result and the exposed formal interface, including explicitly noted output omissions.

**Lean correspondence.** [Choose a force-free parameter](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedExistsZeroHeld.lean#L102) (`Breakdown.Cert.extendedExistsZeroHeldHolds_of`); [Unique correction at each parameter](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedHeldExistsUnique.lean#L135) (`Breakdown.Cert.extendedHeldExistsUniqueHolds_of`); [Contraction at a fixed parameter](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedHeldContracts.lean#L185) (`Breakdown.Cert.extendedHeldContractsHolds_of`); [Continuous total forcing multiplier](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedMultiplierContinuity.lean#L55) (`Breakdown.Cert.extendedMultiplierContinuityHolds_of`).

**Uses.** (7.12), (7.17), (7.21), (7.23), (7.24), (7.25), (7.27), (7.30), Lemma 7.6, (7.52), Proposition 7.8, Proposition 7.9, (7.57), (7.58), (7.59), (7.60), (7.61).

**Used by.** Theorem 7.1.

### (7.59)

The selected nonlinear correction lies within the weighted radius 2 epsilon and gradient-supremum radius M.

[PDF page 42](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=42) · Section 7.8 · **same**.

**Comparison.** The held-solution fields encode these bounds; the nonlinear self-map proof establishes that iteration stays within them.

**Scope.** Local display and named formal counterpart; this does not identify the complete certificate definitions.

**Lean correspondence.** [Held correction radius](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedNodes.lean#L74) (`Breakdown.ExtendedCertificateData.IsHeldSolution.size`); [Held gradient supremum](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedNodes.lean#L75) (`Breakdown.ExtendedCertificateData.IsHeldSolution.sup`); [The nonlinear step keeps both bounds](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedHeldMapsTo.lean#L179) (`Breakdown.Cert.extendedHeldMapsToHolds_of`).

**Uses.** (7.24), (7.25), (7.27), (7.52), (7.55).

**Used by.** Proposition 7.10.

### (7.60)

At the selected parameter, the correction multiplier exactly cancels the approximate forcing multiplier.

[PDF page 42](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=42) · Section 7.8 · **same**.

**Comparison.** The formal conclusion includes the equality multiplier(q) + kappa = 0 for its selected held solution.

**Scope.** Local display and named formal counterpart; this does not identify the complete certificate definitions.

**Lean correspondence.** [Choose a force-free parameter](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedExistsZeroHeld.lean#L102) (`Breakdown.Cert.extendedExistsZeroHeldHolds_of`).

**Uses.** (7.29), (7.30), (7.32), (7.33), (7.34), (7.35), (7.36), (7.37).

**Used by.** Proposition 7.10.

### (7.61)

The corrected forcing multiplier satisfies the coordinate and complementary Euclidean enclosures that keep the parameter update inside K.

[PDF page 43](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=43) · Section 7.8 · **same**.

**Comparison.** The two formal lemmas prove these enclosures for the selected nonlinear held solution.

**Scope.** Local display and named formal counterpart; this does not identify the complete certificate definitions.

**Lean correspondence.** [Enclose adjoint coordinates](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedExistsZeroHeld.lean#L64) (`Breakdown.Cert.Internal.ExtendedExistsZeroHeld.box_part`); [Enclose complementary coordinates](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedExistsZeroHeld.lean#L87) (`Breakdown.Cert.Internal.ExtendedExistsZeroHeld.stiff_part`).

**Uses.** (7.29), (7.30), (7.32), (7.33), (7.34), (7.35), (7.36), (7.37).

**Used by.** Proposition 7.10.

### Proposition 7.11

A nonzero periodic energy-space field with locally integrable similarity-equation terms, solving that equation modulo gradients, has a smooth decaying profile representative equal to the rescaled input field at every time.

[PDF page 44](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=44) · Section 7.9 · **different**.

**Comparison.** The public theorem maps existential weak-profile data to existential smooth-profile data, with explicit weak-derivative and L2/L6 requirements in its input; it allows a general isometry and returns extra decay, but does not expose the identity with a specified input field in (7.62).

**Scope.** The stated result and the exposed formal interface, including explicitly noted output omissions.

**Lean correspondence.** [Weak profile gives a smooth profile](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/Main.lean#L8) (`Breakdown.FarField.periodicLerayProfileExists_of_weak`); [Smooth field for a specified orbit](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/SmoothFieldClosed.lean#L33) (`Breakdown.FarField.smoothFieldOfOrbit_holds`); [Turn a weak profile into a mild orbit](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/OrbitOfParts.lean#L164) (`Breakdown.WeakProfile.weakOrbitOfParts_holds`); [Spatial decay of the smooth profile](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/FarFieldDecayClosed.lean#L35) (`Breakdown.FarField.farFieldDecay_holds`).

**Uses.** Remark 1.2, Lemma 3.6, (7.1), (7.2), (7.62), (7.63), (7.64), (7.65), (7.66).

**Used by.** Theorem 7.1, (7.62).

### (7.62)

The smooth representative at similarity time s equals the original normalized-time field evaluated at s/S as an element of the homogeneous energy space.

[PDF page 44](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=44) · Section 7.9 · **weaker**.

**Comparison.** The smooth-orbit interface preserves a specified continuous orbit, but the preceding weak-to-orbit interface erases the link to the original weak field from its public type.

**Scope.** Local display and named formal counterpart; this does not identify the complete certificate definitions.

**Lean correspondence.** [Smooth field for a specified orbit](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/SmoothFieldClosed.lean#L33) (`Breakdown.FarField.smoothFieldOfOrbit_holds`); [Same velocity at every time](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/Defs.lean#L62) (`Breakdown.FarField.IsVelocityOf`); [Turn a weak profile into a mild orbit](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/OrbitOfParts.lean#L164) (`Breakdown.WeakProfile.weakOrbitOfParts_holds`).

**Uses.** Proposition 7.11.

**Used by.** Proposition 7.11.

### (7.63)

The physical solution’s L6 norm, multiplied by the quarter-power of the remaining time, is uniformly bounded by periodicity of the normalized profile.

[PDF page 45](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=45) · Section 7.10 · **different**.

**Comparison.** physicalCurve and velocity covariance give the rescaling at the level of Fourier states and almost-everywhere physical representatives; the displayed equality of physical-time suprema is not an exposed theorem conclusion.

**Scope.** Local display and named formal counterpart; this does not identify the complete certificate definitions.

**Lean correspondence.** [Physical-time velocity curve](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/Basic.lean#L20) (`Breakdown.WeakProfile.physicalCurve`); [Velocity rotation and dilation](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Statements.lean#L203) (`Breakdown.Freq.VelocityDilate`); [Velocity rotation and dilation](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Realization.lean#L103) (`Breakdown.Freq.velocityCov_holds`).

**Uses.** (3.1), (7.40).

**Used by.** Proposition 7.11, (7.65).

### (7.64)

The physical velocity satisfies the Duhamel formula with the Leray heat kernel and the quadratic velocity tensor.

[PDF page 45](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=45) · Section 7.10 · **same**.

**Comparison.** The formal mild equation gives the same heat-plus-bilinear integral formula in the Fourier realization, with the kernel identification proved downstream.

**Scope.** Local display and named formal counterpart; this does not identify the complete certificate definitions.

**Lean correspondence.** [Weak equations give a mild solution](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/MildFromGood.lean#L13) (`Breakdown.WeakProfile.mildFromGood_holds`); [Duhamel expression in physical time](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/Basic.lean#L34) (`Breakdown.WeakProfile.varConst`).

**Uses.** (2.4), (3.10).

**Used by.** Proposition 7.11, (7.65).

### (7.65)

Heat-kernel bootstrapping bounds the physical velocity supremum by a constant times the inverse square root of the time to blow-up.

[PDF page 46](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=46) · Section 7.10 · **different**.

**Comparison.** Lean obtains a smooth orbit with uniform derivative bounds by a Sobolev and Picard argument; it does not expose the paper’s L6-to-L12-to-L-infinity estimate as this numbered statement.

**Scope.** Local display and named formal counterpart; this does not identify the complete certificate definitions.

**Lean correspondence.** [Smooth field for a specified orbit](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/SmoothFieldClosed.lean#L33) (`Breakdown.FarField.smoothFieldOfOrbit_holds`).

**Uses.** (2.1), (3.9), (7.63), (7.64).

**Used by.** Proposition 7.11, (7.66).

### (7.66)

The physical solution decays like the reciprocal of the sum of the diffusion length and the distance from the origin.

[PDF page 46](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=46) · Section 7.10 · **different**.

**Comparison.** The decay theorem assumes IsRegularOrbitField, including an integral equation, uniform derivatives, a vanishing tail and square-integrable pressure gradient; its rescaled velocity estimate corresponds to the display without identifying those premises with the paper's weaker written input.

**Scope.** Comparison of the assumption-and-conclusion interface; the extra derivative bounds alone do not order the whole implication.

**Lean correspondence.** [Spatial decay of the smooth profile](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/FarFieldDecayClosed.lean#L35) (`Breakdown.FarField.farFieldDecay_holds`); [Profile and pressure decay bounds](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/Defs.lean#L74) (`Breakdown.FarField.DecayBounds`); [A smooth orbit with its integral law](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/Defs.lean#L58) (`Breakdown.FarField.IsRegularOrbitField`); [A smooth periodic similarity field](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/Defs.lean#L45) (`Breakdown.FarField.IsSmoothOrbitField`).

**Uses.** (1.5), (7.65).

**Used by.** Proposition 7.11.
<!-- /passage:sec-7 -->

<a id="appendix-b"></a>

## Appendix B. Certificate conditions

<!-- passage:sec-appendix-b -->

### (B.1)

The prescribed spatial and temporal symmetries are a rotation by π/κ paired with a half-period time shift and a half-turn about the first axis paired with no time shift.

[PDF page 50](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=50) · Section B.1. The form of the data of a certificate · **same**.

**Comparison.** IsModeClass names both generators, GeneratedByClassSymmetries restricts the remaining symmetries to their words modulo full periods, and CellHypothesis supplies κ≥3; the first structure alone is insufficient to recover all the surrounding prose.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Twist and reflection generators](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L1167) (`Breakdown.CertCell.Bridge.IsModeClass`); [Allowed symmetry words](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L1768) (`Breakdown.CertCell.Instance.GeneratedByClassSymmetries`); [Cell certificate hypotheses](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4378) (`Breakdown.CertCell.CellHypothesis`).

**Uses.** No item-level link recorded.

**Used by.** (B.2), (B.10), (B.11), (B.17), (B.24).

### (B.2)

A lattice label ι determines a complex harmonic with time frequency 2ι₂−ι₁ and azimuthal frequency κι₁.

[PDF page 50](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=50) · Section B.1. The form of the data of a certificate · **same**.

**Comparison.** The exponential and both integer frequency maps coincide after identifying the Lean azimuthal order with κ.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Lattice harmonic phase](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L937) (`Breakdown.CertCell.labelPhase`); [Label to Fourier frequencies](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L909) (`Breakdown.CertCell.labelHarmonic`).

**Uses.** (B.1).

**Used by.** (B.5), (B.10), (B.11), (B.12), (B.15).

### (B.3)

The radial variable is compactified as |y|/(|y|+L), while the polar variable records the third coordinate divided by |y|.

[PDF page 50](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=50) · Section B.1. The form of the data of a certificate · **same**.

**Comparison.** The two coordinate definitions are exact for nonzero y and positive chart length; Lean also assigns total values at the origin.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Compact radial coordinate](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2002) (`Breakdown.CertCell.GivenShape.chartCoord`); [Polar height coordinate](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L2495) (`Breakdown.CellCert.GivenFields.heightRatio`).

**Uses.** No item-level link recorded.

**Used by.** (B.4), (B.5), (B.9), (C.1).

### (B.4)

The weighted polar vector is η times the radial unit vector minus the vertical unit vector, and the weighted azimuthal vector is the cross product of the vertical and radial unit vectors.

[PDF page 50](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=50) · Section B.1. The form of the data of a certificate · **same**.

**Comparison.** polarVecQ and azimVecQ give the two displayed coordinate vectors, with the same convention for the radial direction.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Weighted polar frame vector](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L2514) (`Breakdown.CellCert.GivenFields.polarVecQ`); [Weighted azimuthal frame vector](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L2517) (`Breakdown.CellCert.GivenFields.azimVecQ`).

**Uses.** (B.3).

**Used by.** (B.6).

### (B.5)

Each harmonic receives an integer multiple of a radial phase, and the radial differential operator acquires the corresponding imaginary phase-derivative term.

[PDF page 50](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=50) · Section B.1. The form of the data of a certificate · **same**.

**Comparison.** keyPhase supplies the extra exponential, and shiftedScale combines σ(1−σ)∂σ with i times the phase index times phaseSlope.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Harmonic with radial phase](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2034) (`Breakdown.CertCell.GivenShape.keyPhase`); [Phase adjusted radial derivative](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2009) (`Breakdown.CertCell.GivenShape.shiftedScale`); [Radial phase derivative factor](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2006) (`Breakdown.CertCell.GivenShape.phaseSlope`).

**Uses.** (B.2), (B.3).

**Used by.** (B.6), (B.7), (B.8), (B.57), Lemma B.13.

### (B.6)

A represented vector field is a finite harmonic sum whose three scalar coefficients multiply the radial, weighted polar and weighted azimuthal vectors.

[PDF page 50](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=50) · Section B.1. The form of the data of a certificate · **same**.

**Comparison.** The formula is distributed between one-key synthesis and the finite sum; taking real parts is harmless for the valid conjugate-closed data, whose validity is a separate hypothesis.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Finite harmonic sum](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2053) (`Breakdown.CertCell.GivenShape.complexField`); [One vector harmonic](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2039) (`Breakdown.CertCell.GivenShape.keyVector`); [Real represented field](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2060) (`Breakdown.CertCell.GivenShape.shapeInfoField`); [Valid harmonic field data](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2072) (`Breakdown.CertCell.GivenShape.IsTimeFieldData`).

**Uses.** (B.4), (B.5).

**Used by.** (B.7), (B.8), (B.9), Proposition B.1, (B.51), (C.1).

### (B.7)

For nonzero azimuthal order, the radial and polar components contain prescribed origin, infinity and axis factors, and the azimuthal component is chosen to make the mode divergence free.

[PDF page 51](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=51) · Section B.1. The form of the data of a certificate · **same**.

**Comparison.** This is the nonzero-first-label branch of reducedComps, with lowOrder=h₀, highOrder=h and division by κι₁; spline regularity remains in IsTimeFieldData.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Solenoidal mode coefficients](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2019) (`Breakdown.CertCell.GivenShape.reducedComps`); [Phase adjusted radial derivative](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2009) (`Breakdown.CertCell.GivenShape.shiftedScale`); [Valid harmonic field data](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2072) (`Breakdown.CertCell.GivenShape.IsTimeFieldData`).

**Uses.** (B.5), (B.6).

**Used by.** Proposition B.1, (C.1).

### (B.8)

For zero azimuthal order, a stream coefficient consisting of an origin term plus a spline and an independent swirl coefficient determine the three divergence-free components.

[PDF page 51](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=51) · Section B.1. The form of the data of a certificate · **same**.

**Comparison.** This is the first-label-zero branch of reducedComps together with streamValue, including the σ(1−σ)^h weight and phase-adjusted radial derivative.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Solenoidal mode coefficients](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2019) (`Breakdown.CertCell.GivenShape.reducedComps`); [Axisymmetric stream coefficient](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2016) (`Breakdown.CertCell.GivenShape.streamValue`); [Valid harmonic field data](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2072) (`Breakdown.CertCell.GivenShape.IsTimeFieldData`).

**Uses.** (B.5), (B.6).

**Used by.** Proposition B.1, (C.1).

### (B.9)

The approximate profile is affine in the parameters through its mode coefficients, while its radial phase changes by a linear parameter rate times a cutoff logarithmic integral.

[PDF page 51](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=51) · Section B.1. The form of the data of a certificate · **same**.

**Comparison.** affineField, movedParams and stepPhase encode the displayed construction; IsProfileShapeEntry connects those definitions to the certificate profile and its central and tangent origin terms.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Affine profile in parameters](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2980) (`Breakdown.CellReduction.Instantiation.affineField`); [Parameter dependent radial phase](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2973) (`Breakdown.CellReduction.Instantiation.movedParams`); [Linear phase rate](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2976) (`Breakdown.CellReduction.Instantiation.phaseRate`); [Integrated phase cutoff](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L3008) (`Breakdown.CellReduction.Instantiation.stepPhase`); [Profile shape and certificate links](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L3039) (`Breakdown.CellReduction.Instantiation.IsProfileShapeEntry`).

**Uses.** (B.3), (B.6).

**Used by.** Lemma B.9, (B.47), (B.52), (B.56), (B.57), Lemma B.13.

### (B.10)

Each pinning functional pairs the perturbation gradient with a compactly supported tensor assembled from cell polynomials, harmonics and the reflection symmetry.

[PDF page 52](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=52) · Section B.1. The form of the data of a certificate · **same**.

**Comparison.** pinField constructs the tensor and pinValue is its gradient pairing; the output/input order of the linear-map encoding transposes the paper matrix convention.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Cell polynomial pinning tensor](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L1100) (`Breakdown.CertCell.CellLayerData.pinField`); [Reflected cell tensor field](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L1032) (`Breakdown.CertCell.CellMatField.field`); [Linear gradient constraint](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Statement.lean#L76) (`Breakdown.pinValue`).

**Uses.** (B.1), (B.2).

**Used by.** Proposition B.4.

### (B.11)

The row fields are obtained by applying the inverse square root of their Gram matrix to the generators and then scaling each field to squared norm τₖ.

[PDF page 53](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=53) · Section B.1. The form of the data of a certificate · **different**.

**Comparison.** The Gram normalisation is implemented, but rowFieldOf has unit norm and the factor τₖ is stored in rowWeightOf=testWeight/coercivity rather than in the field itself; the weighted row seminorm matches after this explicit translation.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Gram matrix of row generators](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L1487) (`Breakdown.CertCell.RowValues.fieldPairingMatrix`); [Inverse square root Gram mixing](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L1491) (`Breakdown.CertCell.RowValues.mix`); [Normalised row fields](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L1494) (`Breakdown.CertCell.RowValues.rowFieldOf`); [Separate row norm weights](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L1497) (`Breakdown.CertCell.RowValues.rowWeightOf`); [Rows linked to the certificate](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L1534) (`Breakdown.CertCell.Instance.IsRowInstance`); [Row orthonormality proof](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceOrthonormal.lean#L84) (`Breakdown.CertCell.Instance.rowFieldsOrthonormal`).

**Uses.** (B.1), (B.2).

**Used by.** (B.22), Proposition B.4.

### (B.12)

The ι-mode of a velocity field is its normalised time and azimuthal Fourier average after rotating the vector values back into a common frame.

[PDF page 53](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=53) · Section B.2. The multiplier inequality · **same**.

**Comparison.** modeVel uses the same conjugate phase, the inverse spatial rotation and normalisation by 2π; labelHarmonic translates the Appendix B labels.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Time and azimuthal projection](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L202) (`Breakdown.modeVel`); [Label to Fourier frequencies](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L909) (`Breakdown.CertCell.labelHarmonic`).

**Uses.** (B.2).

**Used by.** (B.13), (B.14), (B.16), (B.24), (B.31).

### (B.13)

A projected mode transforms under time translation and axial rotation by multiplication by its harmonic and rotation of its vector value.

[PDF page 53](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=53) · Section B.2. The multiplier inequality · **same**.

**Comparison.** The public theorem proves the displayed covariance under explicit periodicity and integrability hypotheses, which hold for the perturbations under discussion.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Mode shift and rotation covariance](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeShiftRotate.lean#L87) (`Breakdown.CertCell.Bridge.modeShiftRotate`).

**Uses.** (B.12).

**Used by.** Lemma B.3, Lemma B.5, (B.35).

### (B.14)

The multiplier is characterised by its test pairing as the negative Laplacian plus harmonic skew terms weighted by the curl and velocity weights.

[PDF page 54](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=54) · Section B.2. The multiplier inequality · **same**.

**Comparison.** The definition is the same weak characterisation and additionally records measurability, periodicity, finite L² norm and annihilation of pressure gradients; existence is supplied by Proposition B.1’s proof.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Weak multiplier characterisation](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L720) (`Breakdown.PieceWeights.IsMultiplierField`).

**Uses.** (B.12).

**Used by.** (B.16), Proposition B.1, (B.21).

### (B.15)

The frequency seen in a frame rotating at νₚ is the physical time frequency plus νₚ times the azimuthal frequency.

[PDF page 54](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=54) · Section B.2. The multiplier inequality · **same**.

**Comparison.** Substitution of labelHarmonic into frameFreq gives 2π(2ι₂−ι₁)/S+νₚκι₁.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Frequency in a rotating frame](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L652) (`Breakdown.PieceWeights.frameFreq`); [Label to Fourier frequencies](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L909) (`Breakdown.CertCell.labelHarmonic`).

**Uses.** (B.2).

**Used by.** (B.16), (B.19), Proposition B.1.

### (B.16)

The modal quadratic density is the sum of five coefficient-weighted squares of the Hessian, gradient of curl, curl, gradient and velocity.

[PDF page 54](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=54) · Section B.2. The multiplier inequality · **different**.

**Comparison.** The five-term structure matches exactly, but the paper explicitly omits most coefficient corrections; the Lean definitions choose complete formulas that cannot be checked against nonexistent printed expressions.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Five term mode density](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L703) (`Breakdown.PieceWeights.modeDensity`); [Density evaluated on derivatives](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L708) (`Breakdown.PieceWeights.modeTerm`); [Five explicit cell coefficients](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L1136) (`Breakdown.CertCell.ModeCoefficients.ofPieces`); [Curl coefficient with corrections](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L667) (`Breakdown.PieceWeights.coefA`); [Gradient coefficient with corrections](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L681) (`Breakdown.PieceWeights.coefAA`); [Velocity coefficient with corrections](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L690) (`Breakdown.PieceWeights.coefB`); [Curl Hessian error allocation](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L660) (`Breakdown.PieceWeights.shareHat`).

**Uses.** (B.12), (B.14), (B.15).

**Used by.** (B.17), Proposition B.1, (B.20), (B.21), Lemma B.3, (B.26), (B.27), (B.28), Proposition B.4, Lemma B.5.

### (B.17)

Reflecting the point and replacing ι by its reflected label preserves each coefficient of the modal density.

[PDF page 54](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=54) · Section B.2. The multiplier inequality · **weaker**.

**Comparison.** The explicit coefficient lemmas require y₃≠0, because auxiliary step data are compared away from the reflection plane; they establish the almost-everywhere symmetry needed for integration, rather than the literal unrestricted pointwise wording.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Reflected curl coefficient](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeTermFlip.lean#L178) (`Breakdown.CertCell.Bridge.Internal.ModeTermFlip.coefA_flip`); [Reflected gradient coefficient](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeTermFlip.lean#L208) (`Breakdown.CertCell.Bridge.Internal.ModeTermFlip.coefAA_flip`); [Reflected velocity coefficient](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeTermFlip.lean#L235) (`Breakdown.CertCell.Bridge.Internal.ModeTermFlip.coefB_flip`); [Reflected Hessian allocation](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeTermFlip.lean#L165) (`Breakdown.CertCell.Bridge.Internal.ModeTermFlip.shareHat_flip`); [Reflection compatible weights](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeStatements.lean#L17) (`Breakdown.CertCell.Bridge.IsFlipCompatible`); [Reflection of the full density](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeTermFlip.lean#L273) (`Breakdown.CertCell.Bridge.modeTermFlip`).

**Uses.** (B.1), (B.16).

**Used by.** Lemma B.3.

### (B.18)

The stretching contribution combines the symmetric gradient of the reference flow acting on curl v with two terms coupling its vorticity gradient to v and ∇v.

[PDF page 55](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=55) · Section B.2. The multiplier inequality · **same**.

**Comparison.** stretchForm has the same signs and index contractions; stretchFormWith replaces the reference Hessian by the supplied weak second-derivative representative.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Stretching quadratic expression](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L243) (`Breakdown.stretchForm`); [Stretching with weak second data](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L213) (`Breakdown.CoerciveWeak.stretchFormWith`).

**Uses.** No item-level link recorded.

**Used by.** Proposition B.1, (B.20), (B.21), Lemma B.3, (B.25), Proposition B.4, (B.32), (B.47).

### (B.19)

The admissibility numbers bound the total curl weight, the total magnitude of its gradients and the squared velocity-weight sum relative to its frequency-weighted sum.

[PDF page 55](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=55) · Section B.2. The multiplier inequality · **same**.

**Comparison.** These three inequalities are explicit fields of EnclosureAdmissibleClauses; they are assumptions on supplied data, not computed bounds.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Sum of curl weights](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2207) (`Breakdown.CertCell.InstanceSplit.EnclosureAdmissibleClauses.eps_sum_le`); [Sum of curl weight gradients](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2208) (`Breakdown.CertCell.InstanceSplit.EnclosureAdmissibleClauses.eps_grad_sum_le`); [Velocity weight frequency ratio](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2203) (`Breakdown.CertCell.InstanceSplit.EnclosureAdmissibleClauses.mu_ratio`); [Multiplier enclosure hypotheses](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2183) (`Breakdown.CertCell.InstanceSplit.EnclosureAdmissibleClauses`).

**Uses.** (B.15).

**Used by.** Proposition B.1.

### Proposition B.1

Admissible multiplier data give a finite μ-seminorm and an L² multiplier with the stated norm control, whose coercive pairing dominates the signed modal density whenever its negative part is finite.

[PDF page 55](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=55) · Section B.2. The multiplier inequality · **different**.

**Comparison.** The implemented weak-state theorem supplies multiplier existence, seminorm finiteness, the norm bound and an ENNReal density inequality; finite negative part then gives the printed real-integral statement, while full coefficient and regularity assumptions are more explicit than the abbreviated paper data.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Multiplier density proof](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveMain.lean#L51) (`Breakdown.CoerciveWeak.pieceMultiplierDensityWeakHolds_proof`); [Multiplier existence and density bound](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L321) (`Breakdown.CoerciveWeak.PieceMultiplierDensityWeakHolds`); [Admissible weak multiplier data](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L248) (`Breakdown.CoerciveWeak.IsAdmissibleWeak`); [Weak multiplier characterisation](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L720) (`Breakdown.PieceWeights.IsMultiplierField`).

**Uses.** (7.43), (B.6), (B.7), (B.8), (B.14), (B.15), (B.16), (B.18), (B.19).

**Used by.** (B.20), (B.22), Lemma B.2, Proposition B.14.

### (B.20)

After subtracting the coercive energy, μ-seminorm and actuator terms, the multiplier pairing is at least the signed integral of the modal density and stretching term.

[PDF page 55](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=55) · Section B.2. The multiplier inequality · **same**.

**Comparison.** multiplierGap is the displayed left side, and the proved positive/negative-integral inequality yields its comparison with the signed density once the stated negative-part finiteness is imposed.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Multiplier coercive difference](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L746) (`Breakdown.PieceWeights.multiplierGap`); [Multiplier existence and density bound](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L321) (`Breakdown.CoerciveWeak.PieceMultiplierDensityWeakHolds`); [Multiplier density proof](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveMain.lean#L51) (`Breakdown.CoerciveWeak.pieceMultiplierDensityWeakHolds_proof`).

**Uses.** (B.16), (B.18), Proposition B.1.

**Used by.** Lemma B.2.

### (B.21)

The integrated modal density is bounded below by 3/50 times ω²|β|², less the actuator pairing, 3/50 times the row seminorm squared and the pinning penalty 1000|ℓ(v)|².

[PDF page 56](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=56) · Section B.2. The multiplier inequality · **same**.

**Comparison.** RowRestClause gives this inequality with symbolic coercivity and pin weight, and CellHypothesis fixes them to 3/50 and 1000; the density is encoded through separate positive and negative integrals.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Density lower bound with rows](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L525) (`Breakdown.CoerciveWeak.RowRestClause`); [Cell data prove the row lower bound](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellLayerClosed.lean#L126) (`Breakdown.CertCell.rowRestClause_closed`); [Cell certificate hypotheses](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4378) (`Breakdown.CertCell.CellHypothesis`).

**Uses.** (B.14), (B.16), (B.18).

**Used by.** Lemma B.2, (B.43).

### (B.22)

The multiplier norm, pinning weight and row-weight cap determine sufficient lower bounds on the certificate constants c₁, c₂ and c₀.

[PDF page 56](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=56) · Section B.2. The multiplier inequality · **same**.

**Comparison.** The three bounds are explicit fields; substituting coercivity=3/50, pinWeight=1000 and rowWeightMax=400(1+2^−18) gives the printed constants.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Multiplier constant budget](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L6231) (`Breakdown.CellLayerSystem.CellSystemCondition.coerciveL2_ge`); [Pinning constant budget](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L6233) (`Breakdown.CellLayerSystem.CellSystemCondition.coercivePin_ge`); [Row norm constant budget](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L1541) (`Breakdown.CertCell.Instance.IsRowInstance.rowBound_ge`); [Cell certificate hypotheses](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4378) (`Breakdown.CertCell.CellHypothesis`).

**Uses.** (B.11), Proposition B.1.

**Used by.** Lemma B.2, Proposition B.14.

### Lemma B.2

The multiplier estimate and density lower bound imply the a priori certificate estimate for every admissible perturbation and right-hand side when c₁ and c₂ satisfy the stated budgets.

[PDF page 56](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=56) · Section B.2. The multiplier inequality · **same**.

**Comparison.** The first theorem combines the two signed density inequalities and the second completes the scalar estimate with the c₁ and c₂ budgets; the admissible perturbations are represented by weak gradients and second derivatives.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Combine both density inequalities](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L547) (`Breakdown.CoerciveWeak.rowMultiplierInequality_of_pieceDensity`); [Derive the coercive certificate bound](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveMain.lean#L76) (`Breakdown.CoerciveWeak.extendedCoerciveClause_of_pieceData_proved`).

**Uses.** (7.14), Proposition B.1, (B.20), (B.21), (B.22).

**Used by.** Proposition B.14.

### Lemma B.3

Reflection and rotation symmetries reduce the signed space-time density integral to 4π times its quarter-plane integral, with finiteness of positive and negative parts preserved.

[PDF page 56](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=56) · Section B.3. The cells, their complement and the tree · **same**.

**Comparison.** The formal bridge proves the positive and negative integral equalities separately, which gives both the signed identity and the finiteness statements without subtracting infinite quantities.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Density to quarter plane proof](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellLayerJunctions.lean#L165) (`Breakdown.CertCell.modeDensityBridge_closed`); [Separate positive and negative factors](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TopStatements.lean#L121) (`Breakdown.CertCell.DensityIdentity`); [Geometric half plane integration](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HalfPlaneReduction.lean#L170) (`Breakdown.CertCell.Bridge.halfPlaneReduction`); [Reflection of projected modes](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeFlip.lean#L373) (`Breakdown.CertCell.Bridge.modeFlip`).

**Uses.** (B.13), (B.16), (B.17), (B.18), (B.24).

**Used by.** (B.23), Proposition B.8.

### (B.23)

The space-time integral of the modal density and stretching term equals 4π times the corresponding weighted quarter-plane integral.

[PDF page 56](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=56) · Section B.3. The cells, their complement and the tree · **same**.

**Comparison.** The implementation proves the stronger bookkeeping form of two separate nonnegative integral equalities, so the signed formula follows whenever it is defined.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Separate positive and negative factors](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TopStatements.lean#L121) (`Breakdown.CertCell.DensityIdentity`); [Density to quarter plane proof](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellLayerJunctions.lean#L165) (`Breakdown.CertCell.modeDensityBridge_closed`).

**Uses.** Lemma B.3.

**Used by.** Proposition B.8, (B.44).

### (B.24)

Applying the reflection to a projected velocity mode is equivalent to projecting the reflected harmonic and reflecting its vector value.

[PDF page 57](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=57) · Section B.3. The cells, their complement and the tree · **same**.

**Comparison.** ModeFlipHolds supplies the velocity identity almost everywhere, as appropriate for the weak perturbation class, and also supplies first- and second-derivative versions.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Reflection of projected modes](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeFlip.lean#L373) (`Breakdown.CertCell.Bridge.modeFlip`).

**Uses.** (B.1), (B.12).

**Used by.** Lemma B.3, Proposition B.4.

### (B.25)

The stretching majorant charges curl energy, a gradient-velocity product and a split gradient/velocity square with the trace-free constant √(7/2).

[PDF page 57](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=57) · Section B.3. The cells, their complement and the tree · **same**.

**Comparison.** supremumLoss reproduces the three terms and traceFreeConst fixes their constant; its gradient and velocity norms are written as square roots of component-square sums.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Stretching loss majorant](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellDataDefs.lean#L239) (`Breakdown.CellCert.CellAnalysis.supremumLoss`); [Trace free contraction constant](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L259) (`Breakdown.CellCert.Exterior.traceFreeConst`).

**Uses.** (B.18).

**Used by.** (B.26), (B.28), Proposition B.4, (B.32).

### (B.26)

On compatible cell unknowns, the cell matrix minus its energy matrix is dominated by the retained potential and pairing forms, minus the top-degree form, plus eliminated-band and row contributions.

[PDF page 58](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=58) · Section B.3. The cells, their complement and the tree · **different**.

**Comparison.** The displayed comparison is the residual_value_le field, but the formal predicate is supplied as InRowRange; proving that this is the printed x=X_Qx_g representation also uses row completeness, pressure gauge invariance and transport conditions omitted from the paper.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Local residual matrix inequality](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4682) (`Breakdown.CertCell.Assembly.EliminationConditions.residual_value_le`); [Local elimination comparison](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4680) (`Breakdown.CertCell.Assembly.EliminationConditions`); [Compatible local row range](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5743) (`Breakdown.CertCell.Assembly.InRowRange`).

**Uses.** (B.16), (B.25).

**Used by.** Proposition B.4, (B.38).

### (B.27)

The high-degree gradient tail is absorbable up to I₂ times the sum of the cell’s radial factor times its minimum degree-(d+1) spectral eigenvalue and the angular gain (|κι₁|−2)₊²/r₂, with radial factor one on the axis.

[PDF page 58](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=58) · Section B.3. The cells, their complement and the tree · **same**.

**Comparison.** hessTailGain specialises tailGain with shift two, Q=d and innerRadius equal to r₁ off the axis or one on it; TailBudget.Holds contains the full charge comparison that uses this threshold.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Hessian tail gain](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2452) (`Breakdown.CertCell.TailBand.hessTailGain`); [Spectral and angular tail gain](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2449) (`Breakdown.CertCell.TailBand.tailGain`); [Axis adjusted radial factor](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L376) (`Breakdown.CellCert.CellAnalysis.CellBox.innerRadius`); [Complete tail absorption budget](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2478) (`Breakdown.CertCell.TailBand.TailBudget.Holds`).

**Uses.** (B.16).

**Used by.** Proposition B.4.

### (B.28)

The unresolved-mode density subtracts the stretching majorant with the chosen constant and the additional curl, gradient and velocity charges from the original density.

[PDF page 58](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=58) · Section B.3. The cells, their complement and the tree · **same**.

**Comparison.** offModeDensity applies exactly these coefficient subtractions through PointCoef.withStretch and then evaluates the resulting quadratic form.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Charged unresolved mode density](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailStatements.lean#L79) (`Breakdown.CertCell.TailBand.offModeDensity`); [Subtract stretching and local charges](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2519) (`Breakdown.CertCell.TailBand.PointCoef.withStretch`).

**Uses.** (B.16), (B.25).

**Used by.** (B.29), (B.30), Proposition B.4, (B.33), Lemma B.5, (B.36).

### (B.29)

The pointwise unresolved-mode test requires nonnegative Hessian weight, a permissible gradient split, nonnegative corrected velocity weight and a discriminant bound for the cross term.

[PDF page 59](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=59) · Section B.3. The cells, their complement and the tree · **same**.

**Comparison.** PassesTest is the conjunction of the four printed inequalities, using gradFloor and velWithShift for f₁* and f₀*.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Scalar positive quadratic test](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2503) (`Breakdown.CertCell.TailBand.PointCoef.PassesTest`); [Effective gradient coefficient](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2498) (`Breakdown.CertCell.TailBand.PointCoef.gradFloor`).

**Uses.** (B.28).

**Used by.** Lemma B.5.

### (B.30)

An exterior region passes the scalar test when its inverse-square velocity and cross-term costs fit within the gradient floor at an allowed positive Hardy constant.

[PDF page 59](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=59) · Section B.3. The cells, their complement and the tree · **different**.

**Comparison.** The numerical inequality and the alternatives Λ₀≤1/4+(k₀−1)₊² or Λ₀≤2 match, but a directional exterior is formalised with measurable homogeneous radius and uniform positive lower and finite upper bounds that the printed description does not state.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Exterior scalar budget](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2688) (`Breakdown.CertCell.TailBand.IsExteriorCondition.test`); [Exterior coefficient and Hardy tests](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2670) (`Breakdown.CertCell.TailBand.IsExteriorCondition`); [Admissible directional boundary](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2652) (`Breakdown.CertCell.TailBand.IsDirectionRadius`).

**Uses.** (B.28).

**Used by.** (B.31), Lemma B.6.

### (B.31)

On an admitted exterior region, the inverse-square weighted modal L² integral multiplied by Λ₀ is bounded by the modal gradient energy.

[PDF page 59](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=59) · Section B.3. The cells, their complement and the tree · **different**.

**Comparison.** The two geometric cases are proved, including the square-exterior constant two; the directional case is scoped by IsDirectionRadius rather than an unrestricted phrase allowing dependence on direction.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Hardy bound on directional exterior](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailRayModes.lean#L491) (`Breakdown.CertCell.TailBand.modeRayInverseSquare`); [Hardy bound outside a square](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareModes.lean#L462) (`Breakdown.CertCell.TailBand.modeSquareInverseSquare_of_smooth`); [Smooth square exterior bound](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmooth.lean#L610) (`Breakdown.CertCell.TailBand.squareExteriorSmoothStatement`); [Admissible directional boundary](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2652) (`Breakdown.CertCell.TailBand.IsDirectionRadius`).

**Uses.** (B.12), (B.30).

**Used by.** Lemma B.6.

### Proposition B.4

Valid cell data yield finite negative density, the exterior stretching bound, compatible physical unknowns with the local and global error comparisons, and the square-exterior Hardy estimate with constant two.

[PDF page 59](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=59) · Section B.3. The cells, their complement and the tree · **different**.

**Comparison.** The components are implemented across the closed cell, row, gauge, stretching and Hardy proofs; there is no single theorem with the four real error variables r_Q,0…r_Q,3 and the paper leaves part of the required data conditions unwritten.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Finiteness of the negative density](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/FormNegativeFinite.lean#L323) (`Breakdown.CertCell.formNegFinite`); [Exterior stretching bound by modes](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyExteriorStretch.lean#L321) (`Breakdown.CertCell.Assembly.exteriorPointBound_of_tripleSum`); [Mean stretching harmonic expansion](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyExteriorStretch.lean#L312) (`Breakdown.CertCell.Assembly.meanStretchTripleSum`); [Cell and global compatibility proof](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellLayerClosed.lean#L120) (`Breakdown.CertCell.cellJunctions_closed`); [Assemble the local integral bound](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellLayerPartProofs.lean#L55) (`Breakdown.CertCell.cellFormAssembly_closed`); [Assemble the row norm shares](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowSharesInstance.lean#L233) (`Breakdown.CertCell.rowSharesOfInstance`); [Assemble forcing and pinning shares](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSurrogateClosed.lean#L14) (`Breakdown.CertCell.InstancePair.pairSharesFromSurrogateProfiles_holds`); [Bound the plane credit leaves](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellLayerClosed.lean#L62) (`Breakdown.CertCell.creditLeavesBound_closed`); [Hardy bound outside a square](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareModes.lean#L462) (`Breakdown.CertCell.TailBand.modeSquareInverseSquare_of_smooth`); [Smooth square exterior bound](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmooth.lean#L610) (`Breakdown.CertCell.TailBand.squareExteriorSmoothStatement`).

**Uses.** (B.10), (B.11), (B.16), (B.18), (B.24), (B.25), (B.26), (B.27), (B.28).

**Used by.** (B.33), (B.34), Proposition B.8, Proposition B.14.

### (B.32)

Almost everywhere outside the cells, the mean stretching term is at least minus the sum of the modal stretching majorants.

[PDF page 59](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=59) · Section B.3. The cells, their complement and the tree · **same**.

**Comparison.** ExteriorPointBoundHolds is precisely this almost-everywhere inequality; exteriorPointBound_of_tripleSum proves it from the harmonic expansion discharged by meanStretchTripleSum.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Exterior stretching bound by modes](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyExteriorStretch.lean#L321) (`Breakdown.CertCell.Assembly.exteriorPointBound_of_tripleSum`); [Mean stretching harmonic expansion](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyExteriorStretch.lean#L312) (`Breakdown.CertCell.Assembly.meanStretchTripleSum`); [Stretching loss majorant](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellDataDefs.lean#L239) (`Breakdown.CellCert.CellAnalysis.supremumLoss`).

**Uses.** (B.18), (B.25).

**Used by.** Proposition B.8.

### (B.33)

Each cell’s matrix value and unresolved-mode integral, after its credit term, are bounded by its integrated density plus row, pairing and multiplier error allowances.

[PDF page 59](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=59) · Section B.3. The cells, their complement and the tree · **different**.

**Comparison.** The formal local comparison uses named rowShare, pairShare, strain-slack, credit and kappaCost expressions and separates signed integrals; it does not assert the printed existential four-number parametrisation directly.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Local cell integral comparison](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L851) (`Breakdown.CertCell.CellCalculus.IsCellFormBound`); [Bounds for every cell](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L886) (`Breakdown.CertCell.CellCalculus.CellFormBoundsHold`); [Assemble the local integral bound](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellLayerPartProofs.lean#L55) (`Breakdown.CertCell.cellFormAssembly_closed`); [Cell and global compatibility proof](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellLayerClosed.lean#L120) (`Breakdown.CertCell.cellJunctions_closed`).

**Uses.** (B.28), Proposition B.4.

**Used by.** Proposition B.8, (B.44).

### (B.34)

Summed cell errors and plane-credit matrices are controlled by the row seminorm, actuator and pinning pairings, and the global multiplier-error allowance.

[PDF page 59](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=59) · Section B.3. The cells, their complement and the tree · **different**.

**Comparison.** The same charges are bounded in separate row, pairing and credit proofs and assembled into InitialStateBound; the four paper error variables are replaced by explicit shares and their individual budgets.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Assemble the row norm shares](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowSharesInstance.lean#L233) (`Breakdown.CertCell.rowSharesOfInstance`); [Assemble forcing and pinning shares](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSurrogateClosed.lean#L14) (`Breakdown.CertCell.InstancePair.pairSharesFromSurrogateProfiles_holds`); [Bound the plane credit leaves](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellLayerClosed.lean#L62) (`Breakdown.CertCell.creditLeavesBound_closed`); [Initial global integral inequality](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellLayerPartStages.lean#L13) (`Breakdown.CertCell.initialState_closed`).

**Uses.** Proposition B.4.

**Used by.** (B.43), Proposition B.8, (B.44).

### Lemma B.5

A mode with azimuthal frequency k obeys the four angular derivative bounds, which reduce its charged density to a two-variable quadratic form that is nonnegative under the scalar test.

[PDF page 60](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=60) · Section B.3. The cells, their complement and the tree · **same**.

**Comparison.** The angular theorem proves the norm relations almost everywhere, quad_lower performs the reduction and pointwiseQuadraticTest proves nonnegativity from PassesTest.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Angular derivative mode bounds](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailAngularPlane.lean#L172) (`Breakdown.CertCell.TailBand.angularModeBounds`); [Prove the scalar quadratic test](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailPointwise.lean#L58) (`Breakdown.CertCell.TailBand.pointwiseQuadraticTest`); [Unresolved mode positivity proof](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyOffModes.lean#L107) (`Breakdown.CertCell.Assembly.offModeConditionSound_holds`); [Reduce to gradient and velocity terms](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailExteriorLinks.lean#L38) (`Breakdown.CertCell.TailBand.Internal.ExteriorLinks.quad_lower`).

**Uses.** (B.13), (B.16), (B.28), (B.29).

**Used by.** Proposition B.8.

### (B.35)

Curl is bounded by √2 times the gradient, while shifted angular frequencies control velocity, gradient and curl through the next derivative and the cylindrical radius.

[PDF page 60](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=60) · Section B.3. The cells, their complement and the tree · **same**.

**Comparison.** AngularRelations records the four inequalities in squared-norm variables, and angularModeBounds proves them for the weak projected modes almost everywhere.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Four angular derivative inequalities](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailStatements.lean#L52) (`Breakdown.CertCell.TailBand.AngularRelations`); [Angular derivative mode bounds](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailAngularPlane.lean#L172) (`Breakdown.CertCell.TailBand.angularModeBounds`).

**Uses.** (B.13).

**Used by.** (B.36), Lemma B.6.

### (B.36)

The charged density is bounded below by its effective gradient coefficient times |∇v̂|² plus its velocity coefficient times |v̂|² minus its cross coefficient times |∇v̂||v̂|.

[PDF page 60](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=60) · Section B.3. The cells, their complement and the tree · **same**.

**Comparison.** quad_lower is the algebraic inequality with the angular relations as hypotheses; gradFloor contains both the curl correction and the Hessian angular gain.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Reduce to gradient and velocity terms](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailExteriorLinks.lean#L38) (`Breakdown.CertCell.TailBand.Internal.ExteriorLinks.quad_lower`); [Effective gradient coefficient](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2498) (`Breakdown.CertCell.TailBand.PointCoef.gradFloor`).

**Uses.** (B.28), (B.35).

**Used by.** Lemma B.6.

### Lemma B.6

A radial exterior satisfies the Hardy estimate with constant 1/4+(|κι₁|−1)₊², and admissible exterior coefficient bounds then make the integrated unresolved-mode density nonnegative with finite negative part.

[PDF page 61](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=61) · Section B.3. The cells, their complement and the tree · **different**.

**Comparison.** The conclusion is proved for the formally admitted ray exteriors and the stated coefficient budgets; measurability and bounded homogeneous radius requirements make the geometric scope more explicit than the paper.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Hardy bound on directional exterior](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailRayModes.lean#L491) (`Breakdown.CertCell.TailBand.modeRayInverseSquare`); [Exterior density positivity proof](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellLayerPartProofs.lean#L73) (`Breakdown.CertCell.exteriorConditionSound_closed`); [Exterior coefficient and Hardy tests](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2670) (`Breakdown.CertCell.TailBand.IsExteriorCondition`); [Admissible directional boundary](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2652) (`Breakdown.CertCell.TailBand.IsDirectionRadius`).

**Uses.** (B.30), (B.31), (B.35), (B.36), (B.37).

**Used by.** Proposition B.8.

### (B.37)

Integration by parts on a radial tail, followed by Cauchy–Schwarz, bounds the unweighted square integral by four times the radius-squared derivative integral.

[PDF page 61](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=61) · Section B.3. The cells, their complement and the tree · **different**.

**Comparison.** rayLine proves the final one-dimensional estimate for compactly supported C¹ functions and radialRay extends it to the weak-field setting; the displayed intermediate boundary identity is used inside the proof rather than exported as the same general formula.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [One dimensional Hardy tail estimate](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RayLine.lean#L46) (`Breakdown.CellCert.Exterior.rayLine`); [Weak radial Hardy exterior estimate](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailRayBound.lean#L291) (`Breakdown.CertCell.TailBand.radialRay`).

**Uses.** No item-level link recorded.

**Used by.** Lemma B.6, Lemma B.11, (B.50).

### (B.38)

The global quadratic form is the sum of the global penalty, the embedded cell matrices and twice the embedded plane-credit matrices.

[PDF page 62](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=62) · Section B.3. The cells, their complement and the tree · **same**.

**Comparison.** The tree-sum theorem identifies the quadratic value of the leaf sum with precisely these components, including cancellation of paired null leaves and the factor two on credits.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Identify the assembled tree form](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTreeState.lean#L111) (`Breakdown.CertCell.Assembly.TreeStateInternal.quadValue_totalForm_eq`); [Sum of all leaf forms](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertificateStatements.lean#L31) (`Breakdown.CertCell.Certificate.SignedTree.totalForm`); [Physical global and credit leaves](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4285) (`Breakdown.CertCell.TreeEntry.leafForm`).

**Uses.** (B.26).

**Used by.** (B.39), Lemma B.7, Proposition B.8, (B.44).

### (B.39)

The node input is enclosed from below and its passed front from above by computed matrices with entrywise absolute-value error allowances.

[PDF page 62](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=62) · Section B.3. The cells, their complement and the tree · **same**.

**Comparison.** input_lower and front_upper are the two displayed comparisons, while the complex enclosure records the conjugate-pair realification mentioned in the accompanying text.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Input matrix lower enclosure](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L1392) (`Breakdown.CertCell.Certificate.PassesRealNodeEnclosure.input_lower`); [Front matrix upper enclosure](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L1403) (`Breakdown.CertCell.Certificate.PassesRealNodeEnclosure.front_upper`); [Complex node enclosure conditions](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L1409) (`Breakdown.CertCell.Certificate.PassesComplexNodeEnclosure`).

**Uses.** (B.38).

**Used by.** (B.40), Lemma B.7, (B.42).

### (B.40)

A weighted row sum of the absolute factorisation residual and both enclosure errors must fit within each node’s prescribed diagonal error radius.

[PDF page 62](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=62) · Section B.3. The cells, their complement and the tree · **same**.

**Comparison.** Both enclosure structures implement this test; real absolute values become complex norms in the complex-node variant.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Weighted row sum error test](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L1400) (`Breakdown.CertCell.Certificate.PassesRealNodeEnclosure.row_bound`); [Complex weighted row error test](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L1420) (`Breakdown.CertCell.Certificate.PassesComplexNodeEnclosure.row_bound`).

**Uses.** (B.39).

**Used by.** Lemma B.7, (B.42).

### Lemma B.7

The tree conditions give a global lower bound by positive pivot slack minus squared negative-column pairings, and hence strict positivity on the subspace orthogonal to those columns.

[PDF page 62](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=62) · Section B.3. The cells, their complement and the tree · **same**.

**Comparison.** signedTreeLowerBound telescopes the node bounds and pivotCountPositive uses the common column kernel and pivot coverage to prove positivity; the closed certificate theorem supplies the enclosure proofs.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Global signed tree lower bound](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertTreeLowerBound.lean#L34) (`Breakdown.CertCell.Certificate.signedTreeLowerBound`); [Positivity off the negative columns](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertPivotCount.lean#L36) (`Breakdown.CertCell.Certificate.pivotCountPositive`); [Closed tree nonnegativity theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellLayerConclusion.lean#L44) (`Breakdown.CertCell.stateEnclosureCertificateNonneg_holds`).

**Uses.** (B.38), (B.39), (B.40), (B.42).

**Used by.** (B.41), Proposition B.8, Proposition B.14.

### (B.41)

The assembled global matrix dominates the sum of pivot-slack squares minus the sum of the squared negative-column pairings.

[PDF page 62](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=62) · Section B.3. The cells, their complement and the tree · **same**.

**Comparison.** The formal lower bound includes a root-front term, whose required nonnegativity permits its removal and whose zero choice gives the printed display exactly.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Global signed tree lower bound](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertTreeLowerBound.lean#L34) (`Breakdown.CertCell.Certificate.signedTreeLowerBound`); [Sum of all leaf forms](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertificateStatements.lean#L31) (`Breakdown.CertCell.Certificate.SignedTree.totalForm`).

**Uses.** Lemma B.7.

**Used by.** No item-level link recorded.

### (B.42)

At each tree node, the passed front plus pivot slack minus negative-column loss is bounded by the local leaf input and the fronts received from its children.

[PDF page 63](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=63) · Section B.3. The cells, their complement and the tree · **same**.

**Comparison.** The node-bound conclusions are the displayed inequality after moving the node front to the appropriate side; the closed certificate result supplies the real and complex slack components.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Real node lower bound from enclosure](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertificateEnclosureStatements.lean#L166) (`Breakdown.CertCell.Certificate.realNodeEnclosureBound_of_slackBound`); [Complex node lower bound from enclosure](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertificateEnclosureStatements.lean#L252) (`Breakdown.CertCell.Certificate.complexNodeEnclosureBound_of_parts`); [Weighted row sums bound slack](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertSlackBound.lean#L85) (`Breakdown.CertCell.Certificate.signedSlackBound`); [Closed tree nonnegativity theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellLayerConclusion.lean#L44) (`Breakdown.CertCell.stateEnclosureCertificateNonneg_holds`).

**Uses.** (B.39), (B.40).

**Used by.** Lemma B.7.

### (B.43)

The global matrix is required to be no larger than the negative multiplier and pinning diagonal penalty, with the global error allowance added to the multiplier coefficient.

[PDF page 63](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=63) · Section B.3. The cells, their complement and the tree · **same**.

**Comparison.** globalForm is the exact scalar right side, with coercivity and pin weight later fixed by CellHypothesis, and TreeRowConditions.global_eq compares the global leaf against it despite the field name.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Global matrix penalty comparison](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5732) (`Breakdown.CertCell.Assembly.TreeRowConditions.global_eq`); [Global multiplier and pinning penalty](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4218) (`Breakdown.CertCell.globalForm`).

**Uses.** (B.21), (B.34).

**Used by.** Proposition B.8, (B.44).

### Proposition B.8

If all the Appendix B cell conditions hold, the negative modal density is finite and the density lower bound (B.21) holds uniformly over the parameter box for every admissible perturbation, multiplier vector and right-hand side.

[PDF page 63](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=63) · Section B.3. The cells, their complement and the tree · **different**.

**Comparison.** rowRestClause_closed is the correct endpoint for finiteness and (B.21), rather than merely the generic tree positivity theorem; its exact cell, shape and entry predicates include substantive omitted paper conditions.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Cell data prove the row lower bound](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellLayerClosed.lean#L126) (`Breakdown.CertCell.rowRestClause_closed`); [Density lower bound with rows](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L525) (`Breakdown.CoerciveWeak.RowRestClause`); [Closed tree nonnegativity theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellLayerConclusion.lean#L44) (`Breakdown.CertCell.stateEnclosureCertificateNonneg_holds`); [Cell and global compatibility proof](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellLayerClosed.lean#L120) (`Breakdown.CertCell.cellJunctions_closed`).

**Uses.** Lemma B.3, (B.23), Proposition B.4, (B.32), (B.33), (B.34), Lemma B.5, Lemma B.6, (B.38), Lemma B.7, (B.43), (B.44).

**Used by.** Proposition B.14.

### (B.44)

After summing the cell bounds and cancelling local errors, 4π times the global quadratic value is bounded by the total density minus the multiplier gap, plus forcing, row and affine pinning terms.

[PDF page 64](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=64) · Section B.3. The cells, their complement and the tree · **different**.

**Comparison.** InitialStateBound packages this comparison after replacing 2ζ·ℓ−|ζ|²/1000 by its completed-square upper bound; it also uses the formal reflected right-hand side and pressure representative, so it is not the unmodified intermediate display.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Initial global integral inequality](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellLayerPartStages.lean#L13) (`Breakdown.CertCell.initialState_closed`); [Global cell state value](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TopStatements.lean#L150) (`Breakdown.CertCell.initialStateValue`); [Initial state versus signed density](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TopStatements.lean#L188) (`Breakdown.CertCell.InitialStateBound`); [Identify the assembled tree form](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTreeState.lean#L111) (`Breakdown.CertCell.Assembly.TreeStateInternal.quadValue_totalForm_eq`).

**Uses.** (B.23), (B.33), (B.34), (B.38), (B.43).

**Used by.** Proposition B.8.

### (B.45)

Every field in the homogeneous energy space satisfies the L⁶ Sobolev inequality with constant 2/√3 multiplying its gradient L² norm.

[PDF page 64](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=64) · Section B.4. The other conditions and the statement · **same**.

**Comparison.** The proved statement is the squared equivalent with constant 4/3 for a weak gradient, finite sixth power and finite gradient energy; it does not require smooth compact support.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Sobolev inequality with fixed constant](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SixthPower.lean#L9) (`Breakdown.sixthPowerGradientBound_four_thirds`); [Weak sixth power gradient bound](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SixthPowerStatements.lean#L9) (`Breakdown.SixthPowerGradientBound`).

**Uses.** (3.1).

**Used by.** Lemma B.9, (B.49), Lemma B.10, Lemma B.12, (B.54).

### (B.46)

The weighted energy controls the gradient, Laplacian, their product and the supremum norm through the weight lower bound and the constant c_w.

[PDF page 64](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=64) · Section B.4. The other conditions and the statement · **different**.

**Comparison.** The cell reduction proves squared weak-field and period versions at constant weight and uses the same product estimate; it does not package all four displayed inequalities for an arbitrary variable weight into a single declaration.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Weighted energy and supremum bounds](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CellReduction/ReductionClosed.lean#L32) (`Breakdown.CertReduction.energyBoundsHolds_proof`); [Energy bound interfaces](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CellReduction/ReductionStatements.lean#L64) (`Breakdown.CertReduction.EnergyBoundsHolds`); [Energy product estimate](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CellReduction/EnergyBounds.lean#L21) (`Breakdown.CertReduction.Internal.product_le_scaleFactor_sq`).

**Uses.** (7.48).

**Used by.** Lemma B.9, (B.48), (B.49), Lemma B.10.

### Lemma B.9

Central and boxwise profile norm bounds satisfying the scalar budgets yield the gap-transfer estimate and a lower frozen-form bound with c₃ at least the sum of its reference and shift contributions.

[PDF page 64](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=64) · Section B.4. The other conditions and the statement · **same**.

**Comparison.** The gap, reference-form and form-shift implications are separated into three bridge theorems; the two profile pieces and the same constants are assembled by the cell-system composition.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Norm bounds imply gap transfer](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CellReduction/ReductionClosed.lean#L53) (`Breakdown.CertReduction.gapTransferBridgeHolds_proof`); [Norm bounds imply form shift](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CellReduction/ReductionClosed.lean#L56) (`Breakdown.CertReduction.formShiftBridgeHolds_proof`); [Reference frozen form lower bound](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CellReduction/ReductionClosed.lean#L63) (`Breakdown.CertReduction.frozenFormBridgeHolds_of_convection`); [Convection integration identity](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CellReduction/ConvectionIdentityClosed.lean#L8) (`Breakdown.CertReduction.convectionIdentity_holds`); [Central and box profile norm budgets](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L6177) (`Breakdown.CellLayerSystem.ShiftNumbersBounded`); [Reference strain and gradient budgets](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2920) (`Breakdown.CertReduction.FrozenFormBounded`).

**Uses.** (3.2), (B.9), (B.45), (B.46), (B.47), (B.48), (B.49).

**Used by.** Proposition B.14.

### (B.47)

Six finite bounds control central and parameter-box profile differences, the reference gradient and the lower symmetric-strain eigenvalue.

[PDF page 64](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=64) · Section B.4. The other conditions and the statement · **same**.

**Comparison.** ShiftNumbersBounded supplies the four difference norms and FrozenFormBounded supplies the reference L³ gradient norm and its quadratic strain lower bound; the integrals are encoded as squares or cubes.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Central and box profile norm budgets](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L6177) (`Breakdown.CellLayerSystem.ShiftNumbersBounded`); [Reference strain and gradient budgets](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2920) (`Breakdown.CertReduction.FrozenFormBounded`).

**Uses.** (B.9), (B.18).

**Used by.** Lemma B.9, (B.48), (B.49).

### (B.48)

The central and box errors are allocated to the gap and form-shift constants, while the reference strain and gradient costs are allocated to the reference form constant.

[PDF page 64](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=64) · Section B.4. The other conditions and the statement · **same**.

**Comparison.** The three scalar budgets coincide after expanding gapGradCoeff, shiftGradCoeff and the frozen-form coefficient.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Gap transfer scalar budget](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L6190) (`Breakdown.CellLayerSystem.ShiftNumbersBounded.gap_sum`); [Form shift scalar budget](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L6193) (`Breakdown.CellLayerSystem.ShiftNumbersBounded.shift_sum`); [Reference lower form budget](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2927) (`Breakdown.CertReduction.FrozenFormBounded.sum_le`).

**Uses.** (B.46), (B.47).

**Used by.** Lemma B.9.

### (B.49)

The transport error is bounded by a supremum norm for the advecting difference, an L² gradient norm times the velocity supremum for the central difference, and an L³ gradient norm times the velocity L⁶ norm for the box difference.

[PDF page 65](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=65) · Section B.4. The other conditions and the statement · **same**.

**Comparison.** The generic sup and gradient term proofs cover the three estimates, with the gradient proof choosing its L² or L³ branch and the cubic product supplying the 2/√3 factor.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Bound transport by profile supremum](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CellReduction/ReductionClosed.lean#L41) (`Breakdown.CertReduction.gapSupTermHolds_proof`); [Bound transport by profile gradient](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CellReduction/ReductionClosed.lean#L44) (`Breakdown.CertReduction.gapGradTermHolds_proof`); [Cubic multiplier Sobolev product](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CellReduction/ReductionClosed.lean#L35) (`Breakdown.CertReduction.cubicWeightProductHolds_proof`).

**Uses.** (B.45), (B.46), (B.47).

**Used by.** Lemma B.9.

### Lemma B.10

Either the stated L³ bound or the stated L² bound on an adjoint field implies the quadratic adjoint pairing estimate after applying its corresponding weight-dependent conversion factor.

[PDF page 65](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=65) · Section B.4. The other conditions and the statement · **same**.

**Comparison.** cubicForm selects the same two alternatives, adjointQuadCoeff contains the printed constants, and the bridge integrates the perturbation estimate over one period.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Quadratic adjoint bound from a norm](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CellReduction/AdjointQuadraticBridge.lean#L19) (`Breakdown.CertReduction.adjointQuadraticBridge_of`); [One period quadratic adjoint estimate](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CellReduction/AdjointQuadTerm.lean#L133) (`Breakdown.CertReduction.adjointQuadTerm_of`); [Adjoint L2 or L3 norm condition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2941) (`Breakdown.CertReduction.AdjointQuadraticBounded`); [Adjoint norm conversion constants](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2934) (`Breakdown.CertReduction.adjointQuadCoeff`).

**Uses.** (B.45), (B.46).

**Used by.** Proposition B.14.

### Lemma B.11

A field with the prescribed dual bound has an integrable pairing with every period-one field locally square-integrable in time with values in the energy space X, and the pairing is bounded by the dual number times its gradient norm.

[PDF page 66](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=66) · Section B.4. The other conditions and the statement · **same**.

**Comparison.** The implemented dual decomposition combines the plain weighted Hardy bound with the sharp azimuthal bound; it states both spatial and time integrability as well as the final absolute pairing estimate.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Dual data imply gradient pairing bound](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CellReduction/AdjointDualBounded.lean#L12) (`Breakdown.AdjointDefect.dualBoundedBound_of_parts`); [Plain remainder pairing proof](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CellReduction/AdjointRemainderPlain.lean#L41) (`Breakdown.AdjointDefect.remainderPlainHolds_proof`); [Azimuthal remainder pairing proof](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CellReduction/AdjointRemainderAzimuthal.lean#L198) (`Breakdown.AdjointDefect.remainderAzimuthalHolds_proof`); [Mixed adjoint remainder dual bound](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2783) (`Breakdown.AdjointDefect.DualBounded`); [Sharp azimuthal remainder bound](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2772) (`Breakdown.AdjointDefect.AzimuthalBounded`); [Plain weighted remainder bound](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2758) (`Breakdown.AdjointDefect.RemainderBounded`).

**Uses.** (3.1), (B.37), (B.50).

**Used by.** Lemma B.12, (B.53), Proposition B.14.

### (B.50)

An azimuthal scalar mode of order k satisfies the inverse-square Hardy bound with coefficient (|k|+1/2)².

[PDF page 66](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=66) · Section B.4. The other conditions and the statement · **same**.

**Comparison.** The smooth mode estimate uses the exact sharp coefficient, and the weak extension proves a sum over modes before the dual-pairing argument; remainderAzimuthalHolds_proof supplies its approximation and mode-sum components, and the residual certificate enforces distinct component, time-frequency and azimuthal labels.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Sharp smooth azimuthal Hardy bound](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CellReduction/AdjointRemainderAzimuthalSmooth.lean#L19) (`Breakdown.AdjointDefect.AzimuthalParts.smoothModeInverseSquare`); [Extend sharp Hardy to weak fields](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CellReduction/AdjointRemainderAzimuthalWeak.lean#L80) (`Breakdown.AdjointDefect.AzimuthalParts.modeInverseSquareWeak_of`); [Azimuthal remainder pairing proof](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CellReduction/AdjointRemainderAzimuthal.lean#L198) (`Breakdown.AdjointDefect.remainderAzimuthalHolds_proof`); [Sharp azimuthal remainder bound](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2772) (`Breakdown.AdjointDefect.AzimuthalBounded`).

**Uses.** (B.37).

**Used by.** Lemma B.11.

### (B.51)

The auxiliary potentials have the stated inverse-power value and gradient decay, while their weak Laplacians, flux divergence and pressure gradient satisfy a common bound of order |y|⁻¹(1+|y|)⁻².

[PDF page 67](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=67) · Section B.4. The other conditions and the statement · **stronger**.

**Comparison.** IsPotentialData gives bounded-near-origin Laplacian estimates decaying as (1+|y|)^−4 for G and (1+|y|)^−3 for U, plus a value bound for U; these imply the printed common estimate away from zero after changing the constant, while the full spline admissibility conditions are omitted in the paper.

**Scope.** The analytic decay bounds in IsPotentialData, after changing one existential constant; this does not compare the full omitted spline-admissibility hypotheses.

**Lean correspondence.** [Weak potential fields and decay](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CellReduction/AdjointEntryDefs.lean#L72) (`Breakdown.AdjointDefect.IsPotentialData`); [Potential series yield weak fields](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CellReduction/PotentialShape.lean#L96) (`Breakdown.PotentialShape.potentialData_of_series`); [Closed potential analysis components](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CellReduction/PotentialPartsClosed.lean#L34) (`Breakdown.PotentialShape.potentialParts_holds`); [Detailed spline potential conditions](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L6016) (`Breakdown.PotentialShape.IsPotentialSeries`).

**Uses.** (B.6).

**Used by.** (B.52), Lemma B.12.

### (B.52)

The adjoint remainder is the central-period formal adjoint applied to ψⱼ, corrected by the pin-generator Laplacians, pressure gradient, two potential Laplacians and the flux divergence.

[PDF page 67](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=67) · Section B.4. The other conditions and the statement · **same**.

**Comparison.** For the actual cell data, pins_eq and pins_valid identify the generators with valid compact B.6 fields, and shapeParts_closed.field_divergence makes their divergence zero; thus div(DΦ̃−DΦ̃*)=ΔΦ̃ distributionally, giving the displayed residual after theta=G, phi=U and the matrix transpose convention are applied.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Adjoint residual with potentials](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2735) (`Breakdown.AdjointDefect.remainderField`); [Formal adjoint transport operator](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2726) (`Breakdown.AdjointDefect.adjointTransport`); [Antisymmetric pin generator flux](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2818) (`Breakdown.AdjointDefect.AdjointDefectEntry.pinFlux`); [Adjoint residual at the centre period](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2822) (`Breakdown.AdjointDefect.AdjointDefectEntry.centreResidual`); [Link adjoint entries to profile data](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L3213) (`Breakdown.CellReduction.Instantiation.AdjointEntryLinks`); [Pin data match their shape entry](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L6209) (`Breakdown.CellLayerSystem.PotentialEntriesBounded.pins_eq`); [Valid pin shape entry](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L6207) (`Breakdown.CellLayerSystem.PotentialEntriesBounded.pins_valid`); [Valid compact pin generator fields](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L6085) (`Breakdown.PotentialShape.IsPinShapeEntry.generators_valid`); [Synthesis of pin and generator fields](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L6075) (`Breakdown.PotentialShape.PinShapeEntry.pinData`); [Shaped fields are divergence free](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeStatements.lean#L208) (`Breakdown.CertCell.GivenShape.ShapeParts.field_divergence`); [Closed analytic shape proofs](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellLayerJunctions.lean#L118) (`Breakdown.CertCell.GivenShape.shapeParts_closed`).

**Uses.** (B.9), (B.51).

**Used by.** Lemma B.12, (B.53), (B.56).

### Lemma B.12

The potential, parameter-variation, time-frequency and pin-approximation budgets in (B.53) imply the linear adjoint defect estimate uniformly on the parameter box.

[PDF page 67](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=67) · Section B.4. The other conditions and the statement · **same**.

**Comparison.** The generic bridge is specialised by AdjointEntryLinks.fitted_empty and the profile links; its three major contributions are the same potential defect, free/time shift and pin charge, with the named representation, potential, dual and charge proofs supplying the analytic components.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Assemble the linear adjoint bound](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CellReduction/AdjointAssembly.lean#L305) (`Breakdown.AdjointDefect.adjointDefectBridge_of_pieces`); [All adjoint defect norm budgets](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2859) (`Breakdown.AdjointDefect.AdjointDefectBounded`); [Link adjoint entries to profile data](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L3213) (`Breakdown.CellReduction.Instantiation.AdjointEntryLinks`); [Attach potential facts to cell data](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CellReduction/CellLayerBreakdownCompose.lean#L140) (`Breakdown.CellLayerSystem.adjointPotentialFacts_of_parts`); [Closed potential analysis components](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CellReduction/PotentialPartsClosed.lean#L34) (`Breakdown.PotentialShape.potentialParts_holds`); [Weak adjoint representation proof](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CellReduction/AdjointRepresentation.lean#L1382) (`Breakdown.AdjointDefect.representationHolds_of_density`); [Approximate the adjoint by tests](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CellReduction/AdjointTestDensity.lean#L17) (`Breakdown.AdjointDefect.testFieldDensityHolds_proof`); [Bound the potential contribution](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CellReduction/AdjointPotentialBound.lean#L135) (`Breakdown.AdjointDefect.potentialBoundHolds_proof`); [Dual data imply gradient pairing bound](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CellReduction/AdjointDualBounded.lean#L12) (`Breakdown.AdjointDefect.dualBoundedBound_of_parts`); [Plain remainder pairing proof](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CellReduction/AdjointRemainderPlain.lean#L41) (`Breakdown.AdjointDefect.remainderPlainHolds_proof`); [Azimuthal remainder pairing proof](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CellReduction/AdjointRemainderAzimuthal.lean#L198) (`Breakdown.AdjointDefect.remainderAzimuthalHolds_proof`); [Bound the pin approximation charge](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CellReduction/AdjointPinCharge.lean#L392) (`Breakdown.AdjointDefect.pinChargeHolds_proof`); [Bound the free parameter shift](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CellReduction/AdjointFreeShift.lean#L312) (`Breakdown.AdjointDefect.freeShiftBoundHolds_proof`).

**Uses.** Lemma 7.4, Lemma 7.7, (B.45), Lemma B.11, (B.51), (B.52), (B.53), (B.54), (B.55), (B.56).

**Used by.** Proposition B.14.

### (B.53)

The square-root potential defect, weighted parameter and time-frequency costs, and pin-approximation error must sum to at most the chosen linear adjoint error aⱼ.

[PDF page 67](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=67) · Section B.4. The other conditions and the statement · **same**.

**Comparison.** Expanding defectSum with fittedSet=∅ and adding pinCharge yields the printed scalar expression; without fitted_empty the generic definition contains additional fitted-direction terms.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Total linear adjoint error budget](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2889) (`Breakdown.AdjointDefect.AdjointDefectBounded.total`); [Potential and parameter error sum](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2828) (`Breakdown.AdjointDefect.AdjointDefectEntry.defectSum`); [Pin approximation error sum](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2835) (`Breakdown.AdjointDefect.AdjointDefectEntry.pinCharge`); [No fitted adjoint directions](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L3218) (`Breakdown.CellReduction.Instantiation.AdjointEntryLinks.fitted_empty`).

**Uses.** Lemma B.11, (B.52).

**Used by.** Lemma B.12.

### (B.54)

Pairing the self-similar linear operator with ψ transfers time differentiation and dilation to ψ and leaves the spatial diffusion term as a gradient pairing.

[PDF page 67](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=67) · Section B.4. The other conditions and the statement · **same**.

**Comparison.** RepresentationHolds with zero reference advection gives the displayed identity, including −ψ−(y·∇ψ)/2; the proof obtains it by test-field approximation with the required periodicity and decay.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Weak adjoint representation proof](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CellReduction/AdjointRepresentation.lean#L1382) (`Breakdown.AdjointDefect.representationHolds_of_density`); [Weak transport pairing identity](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CellReduction/AdjointStatements.lean#L37) (`Breakdown.AdjointDefect.RepresentationHolds`); [Approximate the adjoint by tests](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CellReduction/AdjointTestDensity.lean#L17) (`Breakdown.AdjointDefect.testFieldDensityHolds_proof`); [Formal adjoint transport operator](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2726) (`Breakdown.AdjointDefect.adjointTransport`).

**Uses.** Lemma 7.4, (B.45).

**Used by.** Lemma B.12, (B.56).

### (B.55)

A velocity with square-integrable weak gradient can be paired with a matrix divergence by moving the derivative onto the velocity and reversing the sign, under the stated integrability assumptions.

[PDF page 68](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=68) · Section B.4. The other conditions and the statement · **different**.

**Comparison.** The pairing identity is implemented, but weak_pairing assumes L² matrix columns and |y| times the divergence in L², whereas the paper states the general L²/L^(6/5) version; pair_flux verifies the needed special cases from potential decay.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Weak matrix integration by parts](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CellReduction/AdjointPotentialBoundPairing.lean#L477) (`Breakdown.AdjointDefect.Internal.PotentialBound.weak_pairing`); [Integrate the decaying flux by parts](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CellReduction/AdjointPotentialBoundSlice.lean#L56) (`Breakdown.AdjointDefect.Internal.PotentialBound.pair_flux`); [Distributional matrix divergence](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CellReduction/AdjointEntryDefs.lean#L13) (`Breakdown.AdjointDefect.IsWeakMatrixDivergence`).

**Uses.** (3.1).

**Used by.** Lemma B.12, (B.56).

### (B.56)

The linear adjoint defect splits into a potential-remainder pairing, parameter and period-variation pairings, and the two pin-approximation errors.

[PDF page 68](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=68) · Section B.4. The other conditions and the statement · **different**.

**Comparison.** The equality is assembled within adjointDefectBridge_of_parts using a generic fitted/free split and antisymmetric pin flux; its specialisation gives the same weak pairings, but no public declaration states the raw three-line printed identity as such.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Full adjoint decomposition and bound](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CellReduction/AdjointAssembly.lean#L111) (`Breakdown.AdjointDefect.adjointDefectBridge_of_parts`); [Potential remainder pairing identity](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CellReduction/AdjointPotentialBoundSlice.lean#L358) (`Breakdown.AdjointDefect.Internal.PotentialBound.slice_identity`); [Split parameter dependent adjoint](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CellReduction/AdjointAssemblyAlgebra.lean#L52) (`Breakdown.AdjointDefect.Internal.transport_split`); [No fitted adjoint directions](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L3218) (`Breakdown.CellReduction.Instantiation.AdjointEntryLinks.fitted_empty`).

**Uses.** (B.9), (B.52), (B.54), (B.55).

**Used by.** Lemma B.12.

### (B.57)

Inside the phase-matching ball, the approximate residual has explicitly defined constant, linear and symmetrised quadratic coefficients in the parameters.

[PDF page 68](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=68) · Section B.4. The other conditions and the statement · **same**.

**Comparison.** The three residual definitions include the same pressure-gradient corrections, and quadraticCoefficient uses one ordered term on the diagonal and the sum of both orders off it; offsetBallIdentity_holds proves the resulting expansion.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Constant residual coefficient](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L3123) (`Breakdown.CellReduction.Instantiation.centreDefect`); [Linear residual coefficient](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L3130) (`Breakdown.CellReduction.Instantiation.linearDefect`); [Ordered quadratic residual term](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L3137) (`Breakdown.CellReduction.Instantiation.quadraticDefect`); [Symmetrised quadratic coefficient](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L3173) (`Breakdown.CellReduction.Instantiation.OffsetExpansionEntry.quadraticCoefficient`); [Exact residual expansion inside ball](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CellReduction/InstOffsetIdentity.lean#L786) (`Breakdown.CellReduction.Instantiation.offsetBallIdentity_holds`).

**Uses.** (7.10), (B.5), (B.9).

**Used by.** Lemma B.13, (B.58).

### Lemma B.13

Absolute enclosures of the constant, linear and quadratic adjoint residual coefficients, together with the exterior residual-adjoint product bound, imply the uniform offset estimate with the budget (B.59).

[PDF page 69](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=69) · Section B.4. The other conditions and the statement · **same**.

**Comparison.** The offset theorem uses the exact local polynomial identity, the three absolute coefficient enclosures, coordinate radii and far-field Cauchy–Schwarz; the specialised profile route makes the target pinning term zero.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Coefficient bounds imply offset clause](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CellReduction/InstOffsetClause.lean#L297) (`Breakdown.CellReduction.Instantiation.offsetClause_holds_of`); [Exact residual expansion inside ball](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CellReduction/InstOffsetIdentity.lean#L786) (`Breakdown.CellReduction.Instantiation.offsetBallIdentity_holds`); [Offset coefficient enclosures](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L3187) (`Breakdown.CellReduction.Instantiation.IsOffsetExpansionEntry`); [Total adjoint offset error](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L3181) (`Breakdown.CellReduction.Instantiation.offsetSum`); [Zero target pinning values](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L3050) (`Breakdown.CellReduction.Instantiation.IsProfileShapeEntry.target_eq`).

**Uses.** (7.29), (B.5), (B.9), (B.57), (B.58), (B.59).

**Used by.** Proposition B.14.

### (B.58)

The supplied central, linear and quadratic coefficient approximations enclose the absolute error of the corresponding actuator-minus-local-residual adjoint pairings.

[PDF page 69](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=69) · Section B.4. The other conditions and the statement · **same**.

**Comparison.** All three fields have absolute values exactly as the printed PDF does; text extraction drops those bars, so reading the extracted inequalities alone would give an incorrect one-sided comparison.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Absolute constant coefficient error](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L3192) (`Breakdown.CellReduction.Instantiation.IsOffsetExpansionEntry.centre_close`); [Absolute linear coefficient error](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L3194) (`Breakdown.CellReduction.Instantiation.IsOffsetExpansionEntry.linear_close`); [Absolute quadratic coefficient error](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L3196) (`Breakdown.CellReduction.Instantiation.IsOffsetExpansionEntry.quad_close`).

**Uses.** (B.57).

**Used by.** Lemma B.13, (B.59).

### (B.59)

The offset budget sums the constant error, radius-weighted linear errors including the diagonal scale correction, upper-triangular quadratic errors weighted by both radii, and the far-field norm product.

[PDF page 69](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=69) · Section B.4. The other conditions and the statement · **same**.

**Comparison.** offsetSum uses the same upper-triangular indexing and diagonal correction; coordRadius uses |stiffRadius|/|scale|, equal to the printed radius under the certificate nonnegativity condition.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Total adjoint offset error](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L3181) (`Breakdown.CellReduction.Instantiation.offsetSum`); [Box and stiff coordinate radii](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L3178) (`Breakdown.CellReduction.Instantiation.coordRadius`).

**Uses.** (7.29), (B.58).

**Used by.** Lemma B.13.

### Proposition B.14

Data satisfying the Appendix B representation and validation conditions furnish a Section 7 certificate, with zero target pinning values and all of its required estimates.

[PDF page 69](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=69) · Section B.4. The other conditions and the statement · **different**.

**Comparison.** isExtendedCertificate_of_parts constructs an extended certificate after choosing a sufficient decay constant, and the closed cell-route theorem supplies its analytic component proofs; the exact CellSystemCondition includes representation, gauge, coefficient and error conditions the paper explicitly omits, and no concrete validating data are supplied here.

**Scope.** The item-specific correspondence described in the reason; no whole-library equivalence claim.

**Lean correspondence.** [Cell conditions yield a certificate](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CellReduction/CellLayerBreakdownCompose.lean#L171) (`Breakdown.CellLayerSystem.isExtendedCertificate_of_parts`); [Complete cell system condition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L6223) (`Breakdown.CellLayerSystem.CellSystemCondition`); [Closed cell route to space blowup](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CellReduction/CellLayerBreakdownClosed.lean#L42) (`Breakdown.CellLayerSystem.spaceBreakdown_of_cell_system_condition`); [Zero target pinning values](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L3050) (`Breakdown.CellReduction.Instantiation.IsProfileShapeEntry.target_eq`); [No fitted adjoint directions](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L3218) (`Breakdown.CellReduction.Instantiation.AdjointEntryLinks.fitted_empty`).

**Uses.** (7.9), (7.17), (7.21), (7.23), (7.24), (7.25), (7.26), (7.27), (7.28), (7.29), (7.35), (7.36), (7.37), Proposition B.1, (B.22), Lemma B.2, Proposition B.4, Lemma B.7, Proposition B.8, Lemma B.9, Lemma B.10, Lemma B.11, Lemma B.12, Lemma B.13.

**Used by.** No item-level link recorded.
<!-- /passage:sec-appendix-b -->

<a id="appendix-c"></a>

## Appendix C. Computation

<!-- passage:sec-appendix-c -->

### Figure 2

Meridional plots show the mean azimuthal vorticity and stream function, the mean azimuthal velocity, and the size of the first non-axisymmetric harmonic of the computed profile.

[PDF page 71](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=71) · Section C.1 · **no Lean**.

**Comparison.** The meridional plots concern the mean and first time harmonic of one computed candidate; formal harmonic representations provide no verified values or rendering of those particular plots.

**Scope.** The particular plotted numerical data, not the general analytical definitions used to describe them.

**Lean correspondence.** No direct audited counterpart assigned.

**Uses.** No item-level link recorded.

**Used by.** No item-level link recorded.

### Figure 3

A horizontal slice at height 6.5 depicts the vertical vorticity component of the computed approximate profile at similarity time zero.

[PDF page 72](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=72) · Section C.1 · **no Lean**.

**Comparison.** The horizontal vorticity slice at z = 6.5 concerns a particular computed candidate; its sampled field and plotting data are not supplied in the pinned source.

**Scope.** The particular plotted numerical data, not the general analytical definitions used to describe them.

**Lean correspondence.** No direct audited counterpart assigned.

**Uses.** No item-level link recorded.

**Used by.** No item-level link recorded.

### Figure 4

Radial plots compare the weighted suprema of the approximate velocity and its first two derivatives over angles and one period.

[PDF page 72](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=72) · Section C.1 · **no Lean**.

**Comparison.** The plotted weighted angular and time suprema concern one approximate candidate; abstract decay bounds on admitted data do not verify those plotted numerical values.

**Scope.** The particular plotted numerical data, not the general analytical definitions used to describe them.

**Lean correspondence.** No direct audited counterpart assigned.

**Uses.** (7.8).

**Used by.** No item-level link recorded.

### (C.1)

The computation uses the divergence-free self-similar equation in curl-cross form with the kinetic-energy contribution absorbed into the pressure.

[PDF page 73](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=73) · Section C.2. The discretization and Newton’s method · **different**.

**Comparison.** centreDefect encodes a continuum residual in derivative and pressure-adjusted advection form with extra period and actuator parameters; source proofs supply curl algebra, while the printed curl-cross PDE and the surrounding numerical computation are not one verified package.

**Scope.** Matched: The continuum residual's terms, pressure correction by half the squared speed, and source-read curl/advection and curl-curl algebra. Remaining: A standalone theorem equating this complete displayed PDE to centreDefect for the paper's exact notation and parameters; any verification of quadrature, least-squares fitted pressure, computed residuals or concrete candidate data.

**Lean correspondence.** [Define the constant residual term](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L3123) (`Breakdown.CellReduction.Instantiation.centreDefect`); [Relate curl and advection](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRemainderAnnihilates.lean#L33) (`Breakdown.CertCell.Assembly.Internal.RemainderAnnihilates.cross_identity`); [Relate curl-curl and the Laplacian](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityProof.lean#L494) (`Breakdown.Coercive.Internal.TestDensityProof.negSsp_curl_curl`).

**Uses.** (1.2), (B.3), (B.6), (B.7), (B.8).

**Used by.** (C.2).

### (C.2)

Newton corrections use the linearisation of the curl-cross self-similar operator at the current approximate field, applied to vectors without forming its full matrix.

[PDF page 73](https://raw.githubusercontent.com/tristanbuckmaster/navier-stokes/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf#page=73) · Section C.2. The discretization and Newton’s method · **different**.

**Comparison.** Lean defines the two curl-cross linear coupling terms and proves their weak-testing bridge with explicit derivative, pressure and actuator data; these continuum results do not verify the matrix-free Newton or flexible-GMRES procedure described around the displayed operator.

**Scope.** Matched: The exact two curl-cross coupling terms, their second-derivative and drift packaging, and an annihilator theorem connecting the strong remainder with solenoidal weak testing. Remaining: A standalone theorem for the complete displayed Newton Jacobian under the paper's conventions; the matrix-free solver, bordering, GMRES, preconditioner, nested dissection, stopping rule and computed values.

**Lean correspondence.** [The two linear curl couplings](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L692) (`Breakdown.CertCell.CellCalculus.couplingField`); [The strong continuum right side](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L781) (`Breakdown.CertCell.CellCalculus.IsStrongRightSide`); [Prove the remainder vanishes on tests](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRemainderAnnihilates.lean#L484) (`Breakdown.CertCell.Assembly.remainderAnnihilates_holds`); [Define the linear residual term](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L3130) (`Breakdown.CellReduction.Instantiation.linearDefect`).

**Uses.** (C.1).

**Used by.** No item-level link recorded.
<!-- /passage:sec-appendix-c -->

<a id="appendix-a"></a>

## Appendix A. Proofs attached to earlier numbers

<!-- passage:sec-appendix-a -->

Appendix A introduces no new numbered results or equations. Its proofs are attached to the existing lemma entries through their proof-page fields, so the same result is not counted twice.
<!-- /passage:sec-appendix-a -->

## Formal routes beyond the paper’s numbering

<!-- passage:sec-formal-routes-beyond-the-paper-s-numbering -->

These entries describe implementation steps or interfaces that need their own explanation even when there is no separate numbered statement. Their paper references identify where the route matters.

### The transfer interface keeps one chosen trajectory

A recurrent mild orbit can be approached by a solution whose initial point lies in any prescribed dense subspace. The public interface is more general in its abstract space and dense subspace, but forgets the printed family of all nearby data and its fixed correction space.

**Paper references.** Proposition 2.1, Proposition 4.3, (1.6).

**Lean route.** [Compact data approaching the profile](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Base/Framework.lean#L66) (`Breakdown.TransferHolds`); [Transfer from spectral splitting](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/Exports.lean#L54) (`Breakdown.transferHolds_of_dichotomy`).

### The analytic assumptions are instantiated separately

The abstract heat, bilinear, dilation and compactness package is connected to a concrete solenoidal Fourier space by a physical realization. These interfaces explain why following one declaration often leads first to a Prop definition and then to an assembly theorem in another module.

**Paper references.** (3.1), (3.3), (3.5), (3.7), Lemma 3.2.

**Lean route.** [Abstract blow-up transfer framework](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Base/Framework.lean#L9) (`Breakdown.MildFramework`); [Read abstract curves as velocity fields](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Base/Realization.lean#L32) (`Breakdown.Realization`); [The physical Fourier realization](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Realization.lean#L130) (`Breakdown.Freq.realization`).

### The whole-space state stores a weighted Fourier field

The formal whole-space Hilbert space stores a solenoidal Fourier object from which an L6 velocity and L2 derivatives are recovered. A value of X is not a raw pointwise velocity; embedX and velocity carry the relation to the paper’s physical fields.

**Paper references.** (3.1), (3.2).

**Lean route.** [The solenoidal Fourier space](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Basic.lean#L85) (`Breakdown.Freq.X`); [Real solenoidal Fourier fields](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Basic.lean#L76) (`Breakdown.Freq.Sig`); [Embed a physical velocity field](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Basic.lean#L122) (`Breakdown.Freq.embedX`); [Recover the velocity in L6](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Basic.lean#L130) (`Breakdown.Freq.velocity`).

### The profile premises include extra decay

The formal smooth-profile premise includes second spatial derivative decay and pressure-gradient decay. The source assumes these bounds explicitly; this index does not upgrade the paper’s weaker written hypothesis by claiming an unlocated Lean regularity bridge.

**Paper references.** (1.2), (1.3), Remark 1.2.

**Lean route.** [A nonzero recurrent profile](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Defs.lean#L51) (`Breakdown.PeriodicSimilarityProfileExists`); [Smooth profile with decay](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/StatementsSlice.lean#L10) (`Breakdown.IsSimilarityProfile`).

### Finite-dimensional data survive below the endpoint

The inverse construction retains a finite-dimensional correction subspace and a bounded lift whose values lie in a chosen dense subspace. A reader looking only at TransferHolds would miss this internal data; the period-piece encoding keeps it before the final existence statement is assembled.

**Paper references.** Proposition 4.3, Proposition 2.1.

**Lean route.** [Finite-dimensional correction data](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StatementsFrame.lean#L55) (`Breakdown.StepDataStatement`); [Construct the correction data](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/Exports.lean#L51) (`Breakdown.stepData`); [Lift the finite-dimensional correction](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StatementsAbstract.lean#L56) (`Breakdown.SectionStatement`); [Choose compactly supported lifts](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/Section.lean#L31) (`Breakdown.exists_section`).

### The unstable correction is chosen from future forcing

The discrete dichotomy chooses initial data that keep the forced recurrence bounded and builds the right inverse across recurrent pieces. This is the formal location of the backward-from-infinity step in the paper’s Lyapunov–Perron construction.

**Paper references.** Lemma 4.5, Lemma 4.6, Proposition 4.3.

**Lean route.** [Solve the weighted discrete recurrence](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StatementsAbstract.lean#L9) (`Breakdown.DiscreteDichotomyStatement`); [Choose the decaying recurrence data](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/DiscreteDichotomy.lean#L199) (`Breakdown.discreteDichotomy`); [A right inverse across repeated pieces](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StatementsAbstract.lean#L19) (`Breakdown.PeriodicInverseStatement`); [Assemble the periodic right inverse](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/Exports.lean#L49) (`Breakdown.periodicInverse`).

### The periodic representation keeps the zero mode

Periodic fields use a unit-cell Fourier H1 norm with weight 1+4π²|k|², and transferring a compact field adds a scaled L2 mass term. The printed proof instead uses mean-zero homogeneous H1 on a large torus before its final dilation; equality of these statement types must not be assumed.

**Paper references.** (3.15), (3.16), (6.1).

**Lean route.** [Periodic Fourier velocity space](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L91) (`Breakdown.Periodic.V`); [Inhomogeneous Fourier weight](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L19) (`Breakdown.Periodic.weight`); [Norm of a transferred compact field](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsShell.lean#L39) (`Breakdown.Periodic.TransplantNorm`).

### The heat comparison is qualitative in scale

For any prescribed error, small enough scale makes the localized periodic and whole-space evolution operators close. The formal route exposes δ-versus-scale convergence and finite-window/tail estimates rather than the printed all-time powers of the large spatial period.

**Paper references.** Lemma 6.1, (6.3), (6.11), Lemma 6.3.

**Lean route.** [Compare projected heat flows](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsShell.lean#L52) (`Breakdown.Periodic.HeatDivFreeComparison`); [Compare free heat flows](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsShell.lean#L58) (`Breakdown.Periodic.FreeHeatComparison`); [Compare the localized inverse data](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsInverse.lean#L76) (`Breakdown.Periodic.ComparisonSmall`).

### The global weighted curve is built from bounded pieces

A contraction corrects normalized time pieces and a gluing map reconstructs the curve before blow-up. The global Cκ norm used in the rewritten paper is replaced in the earlier formal route by an ℓ∞ sequence and a geometric weight.

**Paper references.** (4.5), Lemma 4.8, (6.17).

**Lean route.** [Correct approximate solution pieces](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsSteps.lean#L91) (`Breakdown.Periodic.SeqPerturbation`); [Solve the periodic nonlinear correction](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SeqPerturbation.lean#L140) (`Breakdown.Periodic.seqPerturbation`); [Join the rescaled solution pieces](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StatementsDefs.lean#L136) (`Breakdown.MildFramework.gluePieces`).

### Smoothness and physical reading are separate interfaces

A mild whole-space trajectory with compact smooth initial data has smooth physical representatives on each compact time interval. The interface gives EnergyBoundedOn for each interval; the paper’s uniform nonincreasing-energy statement is stronger than that field alone.

**Paper references.** Lemma 2.3, Theorem 1.1.

**Lean route.** [Smooth representatives of mild flow](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/Basic.lean#L37) (`Breakdown.MildRegular`); [Smooth whole-space mild flow](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/Space.lean#L19) (`Breakdown.mildRegular_realization`); [Identify abstract and physical fields](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/Basic.lean#L31) (`Breakdown.FieldReading`).

### The torus endpoint allows nonperiodic pressure

A time-dependent moving frame converts a global smooth solution with periodic velocity into one with periodic velocity and pressure. The endpoint excludes a broader pressure class than the paper’s initial definition of a periodic smooth solution, which requires both fields to be periodic.

**Paper references.** Theorem 1.1, Proposition 2.2.

**Lean route.** [Remove the pressure’s nonperiodic part](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsSmooth.lean#L38) (`Breakdown.Periodic.MovingFrameReduction`); [Choose a periodic pressure frame](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/MovingFrame.lean#L175) (`Breakdown.Periodic.movingFrameReduction`).

### The torus export forgets quantitative data

Positive lower norms of approximate pieces and bounded decaying corrections imply that the glued mild solution has unbounded norm. The endpoint retains unboundedness; reconstructing the printed all-time rate and local profile comparison needs additional witness-preserving statements.

**Paper references.** (1.7), (2.6), (6.18).

**Lean route.** [A torus mild solution is unbounded](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsSmooth.lean#L44) (`Breakdown.Periodic.TorusBlowup`); [Unbounded norm after gluing](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsSteps.lean#L110) (`Breakdown.Periodic.GlueUnbounded`); [Prove the glued norm is unbounded](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/GlueUnbounded.lean#L48) (`Breakdown.Periodic.glueUnbounded`).

### Normalise the multiplier weight

The forcing field and multiplier are rescaled inversely so their product is unchanged and the internal correction norm uses omega = 1.

**Paper references.** (7.14), (7.18).

**Lean route.** [Normalise the multiplier weight](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedUnitWeight.lean#L92) (`Breakdown.Cert.extendedUnitWeightHolds`).

### Replace the reference model by the approximate profile

The proof rescales the coercive and row constants by the positive transfer margin and removes the model gap before the fixed-point argument.

**Paper references.** (7.19), (7.20), (7.21), (7.52).

**Lean route.** [Absorb the reference-profile error](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedAtProfile.lean#L448) (`Breakdown.Cert.extendedAtProfileHolds`).

### A metric controlling energy and gradient supremum

The metric is the maximum of the correction-plus-multiplier norm and a scaled essential gradient supremum; it is why condition (7.26) is used by Lean.

**Paper references.** (7.25), (7.26), Proposition 7.10.

**Lean route.** [Distance between held corrections](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Basic.lean#L198) (`Breakdown.Cert.heldDist`).

### Unique correction at every parameter

The formal contraction proves local uniqueness within the held set, a conclusion not stated by Proposition 7.10; this is not a claim that the full formal theorem has weaker premises.

**Paper references.** Proposition 7.10.

**Lean route.** [Contraction at a fixed parameter](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedHeldContracts.lean#L185) (`Breakdown.Cert.extendedHeldContractsHolds_of`); [Unique correction at each parameter](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedHeldExistsUnique.lean#L135) (`Breakdown.Cert.extendedHeldExistsUniqueHolds_of`).

### Continuous total forcing multiplier

Uniqueness at fixed parameter identifies subsequential limits and makes the remaining finite-dimensional multiplier map continuous.

**Paper references.** Proposition 7.10.

**Lean route.** [Continuous total forcing multiplier](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedMultiplierContinuity.lean#L55) (`Breakdown.Cert.extendedMultiplierContinuityHolds_of`).

### A zero on a mixed box-and-ball parameter set

A compact convex fixed-point theorem is applied only after the nonlinear correction has been solved; it does not require the mixed parameter set to have interior.

**Paper references.** (7.29), (7.30), (7.61), Proposition 7.10.

**Lean route.** [Zero of the parameter multiplier](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Held/TestSetZero.lean#L92) (`Breakdown.Held.testSetZero_of`); [Choose a force-free parameter](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedExistsZeroHeld.lean#L102) (`Breakdown.Cert.extendedExistsZeroHeldHolds_of`).

### Where quantitative witness data leave the public type

The held record retains parameter, correction and bounds; later existential interfaces omit the links to this witness, so a smooth existence theorem cannot by itself certify the paper’s whole quantitative conclusion.

**Paper references.** Theorem 7.1, (7.38), (7.39), (7.62).

**Lean route.** [Held nonlinear solution](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedNodes.lean#L68) (`Breakdown.ExtendedCertificateData.IsHeldSolution`); [Construct the corrected weak profile](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedSigmaProfileOfHeld.lean#L232) (`Breakdown.Cert.extendedSigmaProfileOfHeldHolds_of`); [Return to similarity time](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Rescale.lean#L85) (`Breakdown.weakPeriodicSimilarityProfileExists_of_sigma`); [Weak profile gives a smooth profile](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/Main.lean#L8) (`Breakdown.FarField.periodicLerayProfileExists_of_weak`).

### Cancellation occurs in the physical weak equation

The formal proof cancels the actual forcing sum after the multiplier equality and establishes integrability before discarding the pressure-gradient pairing.

**Paper references.** (7.10), (7.12), (7.60).

**Lean route.** [Cancel the auxiliary forcing](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedHeldWeakEquation.lean#L530) (`Breakdown.Cert.extendedHeldWeakEquationHolds_of`).

### Strict separation from the zero field

The radius bound prevents the correction from cancelling the approximate profile; the weak embedding also proves that a zero gradient of an L6 field forces the field itself to vanish.

**Paper references.** (7.28), Theorem 7.1.

**Lean route.** [The corrected profile is nonzero](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedHeldNonzero.lean#L15) (`Breakdown.Cert.extendedHeldNonzeroHolds_of`); [Zero gradient forces zero velocity](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/ZeroGradient.lean#L164) (`Breakdown.WeakProfile.zeroGradientSix_holds`).

### The weak-to-smooth route is in the library

The library proves weak-to-mild conversion, smoothing and decay; these are not axioms imported from the external regularity references cited in the paper.

**Paper references.** Proposition 7.11, (7.66).

**Lean route.** [Turn a weak profile into a mild orbit](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/OrbitOfParts.lean#L164) (`Breakdown.WeakProfile.weakOrbitOfParts_holds`); [Smooth field for a specified orbit](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/SmoothFieldClosed.lean#L33) (`Breakdown.FarField.smoothFieldOfOrbit_holds`); [Weak profile gives a smooth profile](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/Main.lean#L8) (`Breakdown.FarField.periodicLerayProfileExists_of_weak`); [Spatial decay of the smooth profile](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/FarFieldDecayClosed.lean#L35) (`Breakdown.FarField.farFieldDecay_holds`).

### Complete multiplier coefficient formulas

The printed leading terms and five-term layout can be compared, but the inward/outward harmonic sums and auxiliary-charge choices require source inspection.

**Paper references.** (B.16), Proposition B.1.

**Lean route.** [Curl coefficient with corrections](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L667) (`Breakdown.PieceWeights.coefA`); [Gradient coefficient with corrections](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L681) (`Breakdown.PieceWeights.coefAA`); [Velocity coefficient with corrections](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L690) (`Breakdown.PieceWeights.coefB`); [Curl Hessian error allocation](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L660) (`Breakdown.PieceWeights.shareHat`); [Five explicit cell coefficients](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L1136) (`Breakdown.CertCell.ModeCoefficients.ofPieces`).

### Separate row fields and row weights

A plain name match to rowFieldOf misses the scaling needed to recover the paper field and seminorm.

**Paper references.** (B.11), (B.22).

**Lean route.** [Normalised row fields](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L1494) (`Breakdown.CertCell.RowValues.rowFieldOf`); [Separate row norm weights](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L1497) (`Breakdown.CertCell.RowValues.rowWeightOf`); [Rows linked to the certificate](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L1534) (`Breakdown.CertCell.Instance.IsRowInstance`); [Row orthonormality proof](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceOrthonormal.lean#L84) (`Breakdown.CertCell.Instance.rowFieldsOrthonormal`).

### Global rows and pressure gauge compatibility

The local elimination inequality only applies on an admitted range; the global state construction must place physical data in that range and transport pressure constants correctly.

**Paper references.** (B.26), Proposition B.4, Proposition B.8.

**Lean route.** [Compatible local row range](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5743) (`Breakdown.CertCell.Assembly.InRowRange`); [Global row and matrix conditions](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5726) (`Breakdown.CertCell.Assembly.TreeRowConditions`); [Cell and global compatibility proof](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellLayerClosed.lean#L120) (`Breakdown.CertCell.cellJunctions_closed`).

### Measurable bounded directional exterior

The exterior theorem is scoped by this predicate; its full hypotheses should not be replaced by the unqualified phrase “a radius depending on direction”.

**Paper references.** (B.30), (B.31), Lemma B.6.

**Lean route.** [Admissible directional boundary](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2652) (`Breakdown.CertCell.TailBand.IsDirectionRadius`); [Exterior coefficient and Hardy tests](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2670) (`Breakdown.CertCell.TailBand.IsExteriorCondition`).

### Potential spline joining and axis conditions

Jet orders, endpoint vanishing, axis powers and directional flux joins are needed to exclude unwanted distributional seam terms and obtain the advertised decay.

**Paper references.** (B.51), (B.52), Lemma B.12.

**Lean route.** [Detailed spline potential conditions](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L6016) (`Breakdown.PotentialShape.IsPotentialSeries`); [Potential series yield weak fields](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CellReduction/PotentialShape.lean#L96) (`Breakdown.PotentialShape.potentialData_of_series`); [Closed potential analysis components](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CellReduction/PotentialPartsClosed.lean#L34) (`Breakdown.PotentialShape.potentialParts_holds`).

### Distinct labels in the sharp dual bound

The certificate requires injective (component,time-frequency,azimuthal-order) triples and the denominator (|m|+1/2)^2; duplicate labels cannot be treated as orthogonal modes.

**Paper references.** Lemma B.11, (B.50).

**Lean route.** [Sharp azimuthal remainder bound](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2772) (`Breakdown.AdjointDefect.AzimuthalBounded`); [Sharp smooth azimuthal Hardy bound](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CellReduction/AdjointRemainderAzimuthalSmooth.lean#L19) (`Breakdown.AdjointDefect.AzimuthalParts.smoothModeInverseSquare`); [Extend sharp Hardy to weak fields](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CellReduction/AdjointRemainderAzimuthalWeak.lean#L80) (`Breakdown.AdjointDefect.AzimuthalParts.modeInverseSquareWeak_of`); [Azimuthal remainder pairing proof](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CellReduction/AdjointRemainderAzimuthal.lean#L198) (`Breakdown.AdjointDefect.remainderAzimuthalHolds_proof`).

### Zero target gap in the cell route

The generic targetGap field does not mean Appendix B permits nonzero target pinning; IsProfileShapeEntry.target_eq enforces zero.

**Paper references.** Lemma B.13, Proposition B.14.

**Lean route.** [Zero target pinning values](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L3050) (`Breakdown.CellReduction.Instantiation.IsProfileShapeEntry.target_eq`); [Profile shape and certificate links](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L3039) (`Breakdown.CellReduction.Instantiation.IsProfileShapeEntry`).

### Empty fitted set in the adjoint route

AdjointEntryLinks.fitted_empty removes the extra fitted-potential terms before comparing defectSum with B.53.

**Paper references.** (B.53), Lemma B.12.

**Lean route.** [No fitted adjoint directions](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L3218) (`Breakdown.CellReduction.Instantiation.AdjointEntryLinks.fitted_empty`); [Link adjoint entries to profile data](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L3213) (`Breakdown.CellReduction.Instantiation.AdjointEntryLinks`); [Potential and parameter error sum](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2828) (`Breakdown.AdjointDefect.AdjointDefectEntry.defectSum`).

### Weighted divergence integration by parts

It proves the identity needed for the constructed fields from their decay; it should not be advertised as a direct proof under exactly the printed L^(6/5) divergence hypothesis.

**Paper references.** (B.55), (B.56).

**Lean route.** [Weak matrix integration by parts](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CellReduction/AdjointPotentialBoundPairing.lean#L477) (`Breakdown.AdjointDefect.Internal.PotentialBound.weak_pairing`); [Integrate the decaying flux by parts](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CellReduction/AdjointPotentialBoundSlice.lean#L56) (`Breakdown.AdjointDefect.Internal.PotentialBound.pair_flux`); [Distributional matrix divergence](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CellReduction/AdjointEntryDefs.lean#L13) (`Breakdown.AdjointDefect.IsWeakMatrixDivergence`).

### No verified profile discovery computation

Analytical residual definitions and the conditional certificate theorem do not verify the approximate field discovery run or the numerical certificate values.

**Paper references.** (C.1), (C.2).

**Lean route.** .
<!-- /passage:sec-formal-routes-beyond-the-paper-s-numbering -->

