# Result comparison

## Result-by-result comparison

Each row opens the numbered statement in both editions. Each verdict compares mathematical scope. Some declarations address one part of a result, as specified in the notes. These are AI assessments. Proof and kernel-check status have their own records.

The adapted edition preserves the wording of all numbered statements.

A separate edition formalization supplies 28 proofs in their stated formal forms and 19 open propositions. Its [public verification run](https://github.com/wcook04/proof-reader/actions/runs/45023118802) records the axiom audit and the Comparator checks.

Comparator also checked [`NavierStokes.conditional_main`](https://github.com/wcook04/proof-reader/blob/5cf49623675e7fcb3ae59ffcc69d9f736fbaed0a/lean-wrappers/navier-stokes-edition/lean/MainTheorems.lean#L100), which gives both nonexistence conclusions under the formal profile or certificate premise. The certificate data are assumed to satisfy the stated conditions.

### Theorem 1.1

[Authors’ statement](../?l=b7477-8770) · [Adapted statement](../adapted/?l=b8114-9407)

**Proved and checked by Comparator.** [`NavierStokes.theorem_1_1_space`](https://github.com/wcook04/proof-reader/blob/5cf49623675e7fcb3ae59ffcc69d9f736fbaed0a/lean-wrappers/navier-stokes-edition/lean/MainTheorems.lean#L47). The whole-space statement gives the physical error (1.6) and two-sided rate for one solution, with uniqueness and noncontinuation. It assumes additional Hessian and pressure-gradient decay. The quantitative torus conclusion remains open.

**Different formulation.** The paper constructs a smooth finite-time trajectory with (1.6); the formal conclusion instead gives, for every positive viscosity, compact smooth solenoidal data admitting no global smooth solution with one uniform kinetic-energy bound. The premise includes second-derivative and pressure-gradient decay, and the trajectory and its rate are absent from this conclusion.

[`Breakdown.breakdownOnSpace_of_profile`](../lean/?m=Breakdown.Uniqueness.Space&d=Breakdown.breakdownOnSpace_of_profile)

**Different formulation.** The paper constructs the periodic trajectory and estimates (1.7); the formal conclusion gives, for every positive viscosity, smooth periodic solenoidal data admitting no global smooth solution with periodic velocity, with no periodicity restriction on its pressure. The premise includes additional profile decay, while the rate and the local comparison on B₁/₁₆ are absent from this conclusion.

[`Breakdown.Periodic.breakdownOnTorus_of_profile`](../lean/?m=Breakdown.Torus.Main&d=Breakdown.Periodic.breakdownOnTorus_of_profile)

### Remark 1.2

[Authors’ statement](../?l=b10202-10975) · [Adapted statement](../adapted/?l=b11967-12740)

**Comparison unresolved.** The paper derives first and second derivative decay from the velocity bound and the smooth equations by local parabolic estimates. The library’s pinned Lean profile predicate assumes derivative decay. The comparison has no checked declaration deriving these bounds from the paper’s weaker premise.

### Proposition 2.1

[Authors’ statement](../?l=b44471-45221) · [Adapted statement](../adapted/?l=b50479-51229)

**Open Lean proposition.** [`NavierStokes.proposition_2_1_target`](https://github.com/wcook04/proof-reader/blob/5cf49623675e7fcb3ae59ffcc69d9f736fbaed0a/lean-wrappers/navier-stokes-edition/lean/OpenTargets.lean#L72). The target requires a single finite-dimensional correction space that works for each prescribed nearby datum.

**Lean is weaker.** For every prescribed dense class of initial data and every ε>0, the formal conclusion chooses one mild solution whose datum is within ε of W(0) and whose dilated error is at most C(1−t)^κ for some κ>0. Proposition 2.1 also chooses a fixed finite-dimensional correction space and treats every sufficiently close datum; that whole family is absent from this conclusion.

[`Breakdown.TransferHolds`](../lean/?m=Breakdown.Base.Framework&d=Breakdown.TransferHolds) · [`Breakdown.transferHolds_of_dichotomy`](../lean/?m=Breakdown.Transfer.Exports&d=Breakdown.transferHolds_of_dichotomy)

### Proposition 2.2

[Authors’ statement](../?l=b45429-45951) · [Adapted statement](../adapted/?l=b51670-52192)

**Open Lean proposition.** [`NavierStokes.proposition_2_2_target`](https://github.com/wcook04/proof-reader/blob/5cf49623675e7fcb3ae59ffcc69d9f736fbaed0a/lean-wrappers/navier-stokes-edition/lean/OpenTargets.lean#L95). The target keeps the finite time, both rate bounds and the local profile comparison on the unit torus.

**Lean is weaker.** The conclusion supplies a smooth periodic solenoidal datum and a mild trajectory whose inhomogeneous H¹ norm is unbounded on [0,T), for some T>0. Proposition 2.2 additionally gives T≤1, the two-sided rate, and local convergence to the profile.

[`Breakdown.Periodic.TorusBlowup`](../lean/?m=Breakdown.Torus.StatementsSmooth&d=Breakdown.Periodic.TorusBlowup) · [`Breakdown.Periodic.torusBlowup_of_parts`](../lean/?m=Breakdown.Torus.Assembly&d=Breakdown.Periodic.torusBlowup_of_parts)

### Lemma 2.3

[Authors’ statement](../?l=b46358-46766) · [Adapted statement](../adapted/?l=b53033-53441)

**Open Lean proposition.** [`NavierStokes.lemma_2_3_target`](https://github.com/wcook04/proof-reader/blob/5cf49623675e7fcb3ae59ffcc69d9f736fbaed0a/lean-wrappers/navier-stokes-edition/lean/OpenTargets.lean#L121). The target covers both domains and requires energy nonincrease and one smooth representative on the whole interval.

**Lean is weaker.** From compact smooth solenoidal initial data, a mild curve on [0,T] has smooth velocity and pressure representatives, with bounded kinetic energy and gradient norm on that interval. Lemma 2.3 additionally states energy nonincrease throughout the lifespan and a periodic assertion.

[`Breakdown.MildRegular`](../lean/?m=Breakdown.Uniqueness.Basic&d=Breakdown.MildRegular) · [`Breakdown.mildRegular_realization`](../lean/?m=Breakdown.Uniqueness.Space&d=Breakdown.mildRegular_realization)

### Lemma 3.1

[Authors’ statement](../?l=b50925-51654) · [Adapted statement](../adapted/?l=b58790-59519)

**Open Lean proposition.** [`NavierStokes.lemma_3_1_target`](https://github.com/wcook04/proof-reader/blob/5cf49623675e7fcb3ae59ffcc69d9f736fbaed0a/lean-wrappers/navier-stokes-edition/lean/OpenTargets.lean#L149). The target includes the projected heat response to general forcing in $L^{3/2}$.

**Lean is weaker.** For all τ>0 and u,v∈X, the symmetric bilinear term is bounded by Cτ⁻³⁄⁴‖u‖X‖v‖X. This is (3.7), while Lemma 3.1 also states a projected-heat estimate for arbitrary L³⁄² forcing.

[`Breakdown.Freq.BilinBound`](../lean/?m=Breakdown.FreqTr.Statements&d=Breakdown.Freq.BilinBound)

**Lean is weaker.** The symmetric bilinear term exists for every positive heat time and satisfies Cτ⁻³⁄⁴‖u‖X‖v‖X. This gives the bilinear conclusion of Lemma 3.1 and the full inequality (3.7).

[`Breakdown.Freq.bilin_holds`](../lean/?m=Breakdown.FreqTr.Realization&d=Breakdown.Freq.bilin_holds)

### Lemma 3.2

[Authors’ statement](../?l=b55230-55343) · [Adapted statement](../adapted/?l=b63568-63681)

**Proved in the stated formal form.** [`NavierStokes.lemma_3_2`](https://github.com/wcook04/proof-reader/blob/5cf49623675e7fcb3ae59ffcc69d9f736fbaed0a/lean-wrappers/navier-stokes-edition/lean/SectionsTwoSix.lean#L33). Compactness is proved for the represented bilinear operator.

**Different formulation.** For positive heat time, the operator in the second input is compact when its first input is a compact smooth solenoidal field in the dense test class. Lemma 3.2 allows every first input in X; extending to that class uses density and continuity in operator norm.

[`Breakdown.Freq.BilinCompact`](../lean/?m=Breakdown.FreqTr.Statements&d=Breakdown.Freq.BilinCompact)

**Lean is weaker.** For positive heat time, the operator in the second input is compact when its first input is a compact smooth solenoidal field in the dense test class. Lemma 3.2 allows every first input in X; extending to that class uses density and continuity in operator norm.

[`Breakdown.Freq.bilinCompact_holds`](../lean/?m=Breakdown.FreqTr.Realization&d=Breakdown.Freq.bilinCompact_holds)

### Lemma 3.3

[Authors’ statement](../?l=b58232-58490) · [Adapted statement](../adapted/?l=b66965-67223)

**Proved in the stated formal form.** [`NavierStokes.lemma_3_3`](https://github.com/wcook04/proof-reader/blob/5cf49623675e7fcb3ae59ffcc69d9f736fbaed0a/lean-wrappers/navier-stokes-edition/lean/SectionsTwoSix.lean#L50). The proof obtains the required suprema from the abstract heat and bilinear hypotheses.

**Lean is stronger.** For two continuous curves on any compact interval, the Duhamel integral exists and is continuous up to both endpoints. The formal statement adds the estimate 4C_K(t−a)¹⁄⁴MN when t−a≤1, with M and N bounds for the input curves.

[`Breakdown.VarConstIntegralStatement`](../lean/?m=Breakdown.Transfer.StatementsLocal&d=Breakdown.VarConstIntegralStatement) · [`Breakdown.varConstIntegral`](../lean/?m=Breakdown.Transfer.VarConstIntegral&d=Breakdown.varConstIntegral)

### Lemma 3.4

[Authors’ statement](../?l=b58650-58974) · [Adapted statement](../adapted/?l=b67383-67707)

**Open Lean proposition.** [`NavierStokes.lemma_3_4_target`](https://github.com/wcook04/proof-reader/blob/5cf49623675e7fcb3ae59ffcc69d9f736fbaed0a/lean-wrappers/navier-stokes-edition/lean/OpenTargets.lean#L168). The target asks for inversion over every finite interval, without a smallness hypothesis on the operator norm.

**Different formulation.** After sufficiently short intervals are composed and the twist removed, the period map differs compactly from the free product, whose norm is at most exp(−P/4). The same statement also provides inverses of the short-interval operators with norm at most 4/3.

[`Breakdown.MonodromyStatement`](../lean/?m=Breakdown.Transfer.StatementsFrame&d=Breakdown.MonodromyStatement) · [`Breakdown.monodromy`](../lean/?m=Breakdown.Transfer.Exports&d=Breakdown.monodromy)

### Lemma 3.5

[Authors’ statement](../?l=b59112-59482) · [Adapted statement](../adapted/?l=b67845-68215)

**Proved in the stated formal form.** [`NavierStokes.lemma_3_5`](https://github.com/wcook04/proof-reader/blob/5cf49623675e7fcb3ae59ffcc69d9f736fbaed0a/lean-wrappers/navier-stokes-edition/lean/SectionsTwoSix.lean#L65). The proof gives the restriction identity with independent inputs and uniqueness for the quadratic mild problem.

**Different formulation.** The quadratic mild equation can be restarted from any intermediate time by the heat semigroup law and adjacent-interval integration. Lemma 3.5 and (3.13) allow independent continuous factors f and h in the forcing, a larger class than the quadratic choice f=h=u.

[`Breakdown.RestrictStatement`](../lean/?m=Breakdown.Transfer.StatementsLocal&d=Breakdown.RestrictStatement) · [`Breakdown.restrict`](../lean/?m=Breakdown.Transfer.Restrict&d=Breakdown.restrict)

**Lean is weaker.** Two mild solutions with the same initial value agree on their entire common interval, whether that interval is closed or half-open. This is the uniqueness part of Lemma 3.5; restarting is proved separately.

[`Breakdown.UniqueStatement`](../lean/?m=Breakdown.Transfer.StatementsLocal&d=Breakdown.UniqueStatement) · [`Breakdown.mildUnique`](../lean/?m=Breakdown.Transfer.Exports&d=Breakdown.mildUnique)

### Lemma 3.6

[Authors’ statement](../?l=b60231-60819) · [Adapted statement](../adapted/?l=b69373-69961)

**Open Lean proposition.** [`NavierStokes.lemma_3_6_target`](https://github.com/wcook04/proof-reader/blob/5cf49623675e7fcb3ae59ffcc69d9f736fbaed0a/lean-wrappers/navier-stokes-edition/lean/OpenTargets.lean#L185). The target uses the paper’s continuous homogeneous $H^1$ weak-solution class.

**Different formulation.** The formal weak-to-mild implication assumes smooth decaying slices, continuity in X, and L²-continuous slice differences in addition to the weak test identity. Lemma 3.6 assumes only a continuous X-valued curve and the stated differentiability of its test pairings.

[`Breakdown.Freq.MildOfWeak`](../lean/?m=Breakdown.FreqTr.Statements&d=Breakdown.Freq.MildOfWeak) · [`Breakdown.Freq.mild_holds`](../lean/?m=Breakdown.FreqTr.Realization&d=Breakdown.Freq.mild_holds)

### Lemma 3.7

[Authors’ statement](../?l=b64066-65454) · [Adapted statement](../adapted/?l=b74064-75452)

**Open Lean proposition.** [`NavierStokes.lemma_3_7_target`](https://github.com/wcook04/proof-reader/blob/5cf49623675e7fcb3ae59ffcc69d9f736fbaed0a/lean-wrappers/navier-stokes-edition/lean/OpenTargets.lean#L204). The target includes all periods and lags, using the mean-zero homogeneous norm.

**Different formulation.** The bilinear smoothing bound is Cτ⁻³⁄⁴ in the inhomogeneous unit-torus norm, for 0<τ≤1. Lemma 3.7 and (3.20) use mean-zero homogeneous spaces at every spatial period and all positive times.

[`Breakdown.Periodic.KernelSharpBound`](../lean/?m=Breakdown.Torus.StatementsAnalysis&d=Breakdown.Periodic.KernelSharpBound) · [`Breakdown.Periodic.kernelSharpBound`](../lean/?m=Breakdown.Torus.KernelBound&d=Breakdown.Periodic.kernelSharpBound)

### Proposition 4.1

[Authors’ statement](../?l=b67560-67961) · [Adapted statement](../adapted/?l=b78362-78763)

**Open Lean proposition.** [`NavierStokes.proposition_4_1_target`](https://github.com/wcook04/proof-reader/blob/5cf49623675e7fcb3ae59ffcc69d9f736fbaed0a/lean-wrappers/navier-stokes-edition/lean/OpenTargets.lean#L234). The target asks for the velocity with the recurrence specified by the printed profile.

**Different formulation.** A smooth nonzero twisted-periodic profile, with the additional second-derivative and pressure-gradient decay, determines a continuous nonzero recurrent orbit in the energy space. Proposition 4.1 states the resulting properties directly for the physical velocity on [0,1).

[`Breakdown.EmbeddedProfileOrbit`](../lean/?m=Breakdown.Profile.StatementsEmbed&d=Breakdown.EmbeddedProfileOrbit) · [`Breakdown.embeddedProfileOrbit_holds`](../lean/?m=Breakdown.Profile.Orbit&d=Breakdown.embeddedProfileOrbit_holds)

**Different formulation.** A smooth profile with the additional derivative and pressure-gradient decay and continuous energy-space slices gives a mild physical curve on each compact interval [0,T], 0<T<1. Proposition 4.1 also bundles nonvanishing and discrete self-similarity on [0,1).

[`Breakdown.PhysicalMild`](../lean/?m=Breakdown.Profile.StatementsPhysical&d=Breakdown.PhysicalMild) · [`Breakdown.physicalMild_unconditional`](../lean/?m=Breakdown.Profile.Orbit&d=Breakdown.physicalMild_unconditional)

### Lemma 4.2

[Authors’ statement](../?l=b69363-69689) · [Adapted statement](../adapted/?l=b80176-80502)

**Open Lean proposition.** [`NavierStokes.lemma_4_2_target`](https://github.com/wcook04/proof-reader/blob/5cf49623675e7fcb3ae59ffcc69d9f736fbaed0a/lean-wrappers/navier-stokes-edition/lean/OpenTargets.lean#L248). The target keeps the physical recurrence and both sides of the physical norm estimate.

**Different formulation.** The rescaled profile intervals are mild, have matching dilated endpoints, recur under the twist every k intervals, and have a uniform upper bound inherited from the similarity orbit. The two-sided physical rate in Lemma 4.2 also uses the lower orbit bound and dilation law.

[`Breakdown.ProfilePieceStatement`](../lean/?m=Breakdown.Transfer.StatementsFrame&d=Breakdown.ProfilePieceStatement) · [`Breakdown.profilePiece`](../lean/?m=Breakdown.Transfer.Exports&d=Breakdown.profilePiece)

### Proposition 4.3

[Authors’ statement](../?l=b72658-73144) · [Adapted statement](../adapted/?l=b84530-85016)

**Open Lean proposition.** [`NavierStokes.proposition_4_3_target`](https://github.com/wcook04/proof-reader/blob/5cf49623675e7fcb3ae59ffcc69d9f736fbaed0a/lean-wrappers/navier-stokes-edition/lean/OpenTargets.lean#L264). The target is a bounded inverse on a single weighted time trajectory.

**Different formulation.** The right inverse acts on bounded sequences of short rescaled time intervals, returns an exceptional coordinate in a fixed finite-dimensional space, and lifts its initial correction into the chosen dense class. Proposition 4.3 writes the corresponding problem as one trajectory in Cκ([0,1);X).

[`Breakdown.StepDataStatement`](../lean/?m=Breakdown.Transfer.StatementsFrame&d=Breakdown.StepDataStatement) · [`Breakdown.stepData`](../lean/?m=Breakdown.Transfer.Exports&d=Breakdown.stepData)

**Different formulation.** Under a finite-dimensional spectral splitting, invertibility of each short-interval operator, and a lift preserving the exceptional projection, a bounded right inverse solves the weighted sequence equations. Proposition 4.3 presents the result on the global Cκ trajectory space.

[`Breakdown.PeriodicInverseStatement`](../lean/?m=Breakdown.Transfer.StatementsAbstract&d=Breakdown.PeriodicInverseStatement) · [`Breakdown.periodicInverse`](../lean/?m=Breakdown.Transfer.Exports&d=Breakdown.periodicInverse)

**Different formulation.** For a finite-rank projection and a dense linear class, there is a bounded lift J into that class with PᵤJ=Pᵤ. Restricting J to the exceptional range gives the compact-data correction space used in Proposition 4.3.

[`Breakdown.SectionStatement`](../lean/?m=Breakdown.Transfer.StatementsAbstract&d=Breakdown.SectionStatement) · [`Breakdown.exists_section`](../lean/?m=Breakdown.Transfer.Section&d=Breakdown.exists_section)

### Lemma 4.4

[Authors’ statement](../?l=b74267-74437) · [Adapted statement](../adapted/?l=b86525-86695)

**Open Lean proposition.** [`NavierStokes.lemma_4_4_target`](https://github.com/wcook04/proof-reader/blob/5cf49623675e7fcb3ae59ffcc69d9f736fbaed0a/lean-wrappers/navier-stokes-edition/lean/OpenTargets.lean#L286). The open statement uses the paper’s Volterra operator over one full period.

**Different formulation.** After sufficiently short intervals are composed and the twist removed, the period map differs compactly from the free product, whose norm is at most exp(−P/4). The same statement also provides inverses of the short-interval operators with norm at most 4/3.

[`Breakdown.MonodromyStatement`](../lean/?m=Breakdown.Transfer.StatementsFrame&d=Breakdown.MonodromyStatement) · [`Breakdown.monodromy`](../lean/?m=Breakdown.Transfer.Exports&d=Breakdown.monodromy)

### Lemma 4.5

[Authors’ statement](../?l=b75594-76095) · [Adapted statement](../adapted/?l=b87871-88372)

**Proved in the stated formal form.** [`NavierStokes.lemma_4_5`](https://github.com/wcook04/proof-reader/blob/5cf49623675e7fcb3ae59ffcc69d9f736fbaed0a/lean-wrappers/navier-stokes-edition/lean/SectionsTwoSix.lean#L193). The formal conclusion gives geometric bounds for the split operator. The paper expresses them as convergence of two series at an intermediate weight.

**Lean is stronger.** For a compact perturbation of an operator of norm at most b≤α<β, the spectral conclusion gives a commuting finite-rank projection and geometric bounds with α<r₁<r₂<β, together with surjectivity on the exceptional range. Taking α=b=exp(−S/4), β=1 and r₁<Θ<r₂ gives the two convergent series in (4.11).

[`Breakdown.DichotomyHolds`](../lean/?m=Breakdown.Base.Framework&d=Breakdown.DichotomyHolds) · [`Breakdown.dichotomyHolds`](../lean/?m=Breakdown.Spectral.RealDichotomy&d=Breakdown.dichotomyHolds)

### Lemma 4.6

[Authors’ statement](../?l=b78181-79181) · [Adapted statement](../adapted/?l=b91150-92150)

**Open Lean proposition.** [`NavierStokes.lemma_4_6_target`](https://github.com/wcook04/proof-reader/blob/5cf49623675e7fcb3ae59ffcc69d9f736fbaed0a/lean-wrappers/navier-stokes-edition/lean/OpenTargets.lean#L304). The target includes the passage to discrete time, forcing linearity and the weighted estimate.

**Different formulation.** The weighted recurrence is xₙ₊₁=θ⁻¹(Mxₙ+cₙ). Display (4.14) writes the corresponding unweighted recurrence and also identifies its continuous-time trajectory and forcing.

[`Breakdown.orbitSeq`](../lean/?m=Breakdown.Transfer.StatementsDefs&d=Breakdown.orbitSeq)

### Lemma 4.7

[Authors’ statement](../?l=b86966-87679) · [Adapted statement](../adapted/?l=b100168-100881)

**Open Lean proposition.** [`NavierStokes.lemma_4_7_target`](https://github.com/wcook04/proof-reader/blob/5cf49623675e7fcb3ae59ffcc69d9f736fbaed0a/lean-wrappers/navier-stokes-edition/lean/OpenTargets.lean#L340). The target keeps all three weighted estimates with the constant uniform in the underlying space and operators.

**Different formulation.** On [0,T], the bilinear Duhamel operator is bounded by 4C_K T¹⁄⁴ for T≤1, and the free heat-evolution operator has norm at most one. Lemma 4.7 expresses different, global Cκ estimates on [0,1).

[`Breakdown.PieceOperatorStatement`](../lean/?m=Breakdown.Transfer.StatementsLocal&d=Breakdown.PieceOperatorStatement) · [`Breakdown.pieceOperator`](../lean/?m=Breakdown.Transfer.Exports&d=Breakdown.pieceOperator)

### Lemma 4.8

[Authors’ statement](../?l=b88323-89559) · [Adapted statement](../adapted/?l=b101525-102761)

**Open Lean proposition.** [`NavierStokes.lemma_4_8_target`](https://github.com/wcook04/proof-reader/blob/5cf49623675e7fcb3ae59ffcc69d9f736fbaed0a/lean-wrappers/navier-stokes-edition/lean/OpenTargets.lean#L361). The target is for a general small weighted residual on the full time interval.

**Different formulation.** For normalized time intervals, a right inverse and 64‖R‖²C_K L¹⁄⁴(ρ+‖ξ‖)≤1 give exact mild intervals with matching endpoints. Both the datum correction and each normalized error are bounded by 2‖R‖(ρ+‖ξ‖), while Lemma 4.8 uses the Cκ norm of the combined forcing e^{tΔ}χ−Fᵃ.

[`Breakdown.Periodic.SeqPerturbation`](../lean/?m=Breakdown.Torus.StatementsSteps&d=Breakdown.Periodic.SeqPerturbation) · [`Breakdown.Periodic.seqPerturbation`](../lean/?m=Breakdown.Torus.SeqPerturbation&d=Breakdown.Periodic.seqPerturbation)

### Lemma 5.1

[Authors’ statement](../?l=b91525-91956) · [Adapted statement](../adapted/?l=b105440-105871)

**Open Lean proposition.** [`NavierStokes.lemma_5_1_target`](https://github.com/wcook04/proof-reader/blob/5cf49623675e7fcb3ae59ffcc69d9f736fbaed0a/lean-wrappers/navier-stokes-edition/lean/OpenTargets.lean#L391). The target varies the cutoff radius and keeps the constants uniform in radius and time.

**Different formulation.** The smooth solenoidal cutoff has fixed support around the centre of the unit torus and agrees exactly with the physical profile on a fixed inner ball. Lemma 5.1 uses an arbitrary radius r and additionally gives explicit gradient-error and mass estimates.

[`Breakdown.Periodic.ApproxFieldProperties`](../lean/?m=Breakdown.Torus.StatementsApprox&d=Breakdown.Periodic.ApproxFieldProperties) · [`Breakdown.Periodic.approxFieldProperties_holds`](../lean/?m=Breakdown.Torus.Main&d=Breakdown.Periodic.approxFieldProperties_holds)

### Lemma 6.1

[Authors’ statement](../?l=b98078-98512) · [Adapted statement](../adapted/?l=b114314-114748)

**Open Lean proposition.** [`NavierStokes.lemma_6_1_target`](https://github.com/wcook04/proof-reader/blob/5cf49623675e7fcb3ae59ffcc69d9f736fbaed0a/lean-wrappers/navier-stokes-edition/lean/OpenTargets.lean#L442). The target gives the explicit large-period rate for compactly supported tensor forcing and every positive lag.

**Different formulation.** Compactly supported L² forcing has arbitrarily small local projected-heat discrepancy, measured by δ times its L³⁄² norm, at sufficiently small scale and on a compact positive-time window. Lemma 6.1 gives an all-time CL⁻⁷⁄² estimate for the divergence of a W¹,¹ tensor, in terms of that tensor’s L¹ norm.

[`Breakdown.Periodic.HeatDivFreeComparison`](../lean/?m=Breakdown.Torus.StatementsShell&d=Breakdown.Periodic.HeatDivFreeComparison) · [`Breakdown.Periodic.heatDivFreeComparison`](../lean/?m=Breakdown.Torus.HeatComparison&d=Breakdown.Periodic.heatDivFreeComparison)

### Lemma 6.2

[Authors’ statement](../?l=b102327-102772) · [Adapted statement](../adapted/?l=b119002-119447)

**Open Lean proposition.** [`NavierStokes.lemma_6_2_target`](https://github.com/wcook04/proof-reader/blob/5cf49623675e7fcb3ae59ffcc69d9f736fbaed0a/lean-wrappers/navier-stokes-edition/lean/OpenTargets.lean#L414). The target keeps the physical norms and the explicit large-period residual rate.

**Different formulation.** For sufficiently small positive final time, the normalized approximate intervals have a uniform upper bound and pointwise lower norm bound c/2. This does not itself assert a norm identity under periodization or a rate for the corrected trajectory.

[`Breakdown.Periodic.ApproxSizes`](../lean/?m=Breakdown.Torus.StatementsApproxSteps&d=Breakdown.Periodic.ApproxSizes) · [`Breakdown.Periodic.approxSizes`](../lean/?m=Breakdown.Torus.ApproxSizes&d=Breakdown.Periodic.approxSizes)

**Different formulation.** For the normalized nth approximate interval, the residual is bounded by θⁿKT¹⁄⁴, assuming the profile bounds and λ¹⁄⁴<θ. Lemma 6.2 instead states a global Cκ residual bound of order L⁻¹⁄² on the large torus.

[`Breakdown.Periodic.ApproxResidualSmall`](../lean/?m=Breakdown.Torus.StatementsApproxSteps&d=Breakdown.Periodic.ApproxResidualSmall) · [`Breakdown.Periodic.approxResidualSmall`](../lean/?m=Breakdown.Torus.ApproxResidual&d=Breakdown.Periodic.approxResidualSmall)

### Lemma 6.3

[Authors’ statement](../?l=b111914-112410) · [Adapted statement](../adapted/?l=b128547-129043)

**Open Lean proposition.** [`NavierStokes.lemma_6_3_target`](https://github.com/wcook04/proof-reader/blob/5cf49623675e7fcb3ae59ffcc69d9f736fbaed0a/lean-wrappers/navier-stokes-edition/lean/OpenTargets.lean#L468). The target retains the prescribed approximate inverse and the explicit large-period defect bound.

**Different formulation.** For any δ>0, the localized interaction and initial-data maps on the unit torus are within δ of their whole-space counterparts when the scale is sufficiently small. The statement gives no explicit power of the large period L in (6.11) or (6.15).

[`Breakdown.Periodic.ComparisonSmall`](../lean/?m=Breakdown.Torus.StatementsInverse&d=Breakdown.Periodic.ComparisonSmall) · [`Breakdown.Periodic.comparisonSmall`](../lean/?m=Breakdown.Torus.CompareFinal&d=Breakdown.Periodic.comparisonSmall)

**Different formulation.** Two localized comparisons within δ and an explicit smallness inequality transfer a bounded whole-space right inverse to an exact periodic right inverse. Lemma 6.3 first constructs a particular approximate inverse with a defect of order L⁻¹⁄².

[`Breakdown.Periodic.ShellInverseTransfer`](../lean/?m=Breakdown.Torus.StatementsSeqOps&d=Breakdown.Periodic.ShellInverseTransfer) · [`Breakdown.Periodic.shellInverseTransfer`](../lean/?m=Breakdown.Torus.InverseAlgebra&d=Breakdown.Periodic.shellInverseTransfer)

### Theorem 7.1

[Authors’ statement](../?l=b143264-143973) · [Adapted statement](../adapted/?l=b162871-163580)

**Proved in the stated formal form.** [`NavierStokes.theorem_7_1`](https://github.com/wcook04/proof-reader/blob/5cf49623675e7fcb3ae59ffcc69d9f736fbaed0a/lean-wrappers/navier-stokes-edition/lean/SectionSeven.lean#L29). The output keeps the chosen parameter, profile, correction, bounds and symmetries. It assumes a formal extended certificate and concludes extra Hessian and pressure-gradient decay.

**Different formulation.** Theorem 7.1 returns α, its period, a smooth profile and the bounds and symmetries of that same profile. This implication assumes the more restrictive certificate conditions and concludes only existence of a weak recurrent profile; its conclusion does not retain α or the bounds (7.38).

[`Breakdown.extended_certificate_orbit_proved`](../lean/?m=Breakdown.Cert.ExtendedMain&d=Breakdown.extended_certificate_orbit_proved)

### Corollary 7.2

[Authors’ statement](../?l=b143974-144191) · [Adapted statement](../adapted/?l=b164513-164730)

**Proved in the stated formal form.** [`NavierStokes.corollary_7_2`](https://github.com/wcook04/proof-reader/blob/5cf49623675e7fcb3ae59ffcc69d9f736fbaed0a/lean-wrappers/navier-stokes-edition/lean/SectionSeven.lean#L45). The construction retains the certificate profile, proves quantitative whole-space blow-up and gives both nonexistence conclusions. The quantitative torus trajectory remains open.

**Different formulation.** The conclusion excludes a global smooth bounded-energy whole-space solution for suitable compactly supported data at every positive viscosity. Corollary 7.2 also asserts the torus conclusion and retains the constructed trajectories, rates and chosen profile from Theorems 1.1 and 7.1.

[`Breakdown.extended_certificate_breakdown_on_space`](../lean/?m=Solution&d=Breakdown.extended_certificate_breakdown_on_space)

### Remark 7.3

[Authors’ statement](../?l=b144192-144664) · [Adapted statement](../adapted/?l=b166428-166900)

**Paper only.** This is a consequence in the paper of the chosen profile’s twist identity. Replacing the period by the positive shift in that identity leaves the profile equations and decay bounds in force. The pinned Lean library has a separate result for half-periodicity of a gradient-energy representative.

### Lemma 7.4

[Authors’ statement](../?l=b149507-150290) · [Adapted statement](../adapted/?l=b171642-172425)

**Proved in the stated formal form.** [`NavierStokes.lemma_7_4`](https://github.com/wcook04/proof-reader/blob/5cf49623675e7fcb3ae59ffcc69d9f736fbaed0a/lean-wrappers/navier-stokes-edition/lean/SectionSeven.lean#L75). The estimate concerns the constructed inverse. It gives the integrated energy identity, with the differentiated identity and period pairing outside the stated conclusion.

**Different formulation.** For the constructed free solution, the result supplies a continuous periodic scalar representative of the gradient energy and an interval-integrated identity. Equation (7.42) is the almost-everywhere differential identity for arbitrary v ∈ D_S; (7.45) is its physical-time counterpart.

[`Breakdown.Cert.freeEnergyLocalHolds_of`](../lean/?m=Breakdown.Cert.FreeEnergyLocal&d=Breakdown.Cert.freeEnergyLocalHolds_of)

### Proposition 7.5

[Authors’ statement](../?l=b153443-153939) · [Adapted statement](../adapted/?l=b176235-176731)

**Proved in the stated formal form.** [`NavierStokes.proposition_7_5`](https://github.com/wcook04/proof-reader/blob/5cf49623675e7fcb3ae59ffcc69d9f736fbaed0a/lean-wrappers/navier-stokes-edition/lean/SectionSeven.lean#L94). The proof gives a symmetry-preserving inverse and weak graph convergence. The statement leaves open the full domain identification and local strong convergence of the full sequence.

**Different formulation.** This result constructs the time-integral operator giving the gradient part of the free solution. Proposition 7.5 additionally states bijectivity on D_S, symmetry preservation and weak and local strong convergence; those conclusions require separate results.

[`Breakdown.Cert.exists_gradInvSpec`](../lean/?m=Breakdown.Cert.GradInvSpec&d=Breakdown.Cert.exists_gradInvSpec)

### Lemma 7.6

[Authors’ statement](../?l=b158955-159435) · [Adapted statement](../adapted/?l=b181862-182342)

**Proved in the stated formal form.** [`NavierStokes.lemma_7_6`](https://github.com/wcook04/proof-reader/blob/5cf49623675e7fcb3ae59ffcc69d9f736fbaed0a/lean-wrappers/navier-stokes-edition/lean/SectionSeven.lean#L115). The estimate uses graph norms and an essential gradient supremum. The time-dependent bound accommodates two fields.

**Lean is weaker.** Lemma 7.6 includes a spatial supremum bound and a quadratic estimate over a period. This theorem proves the spatial product inequality, which implies the weighted bound; the period estimate is a separate theorem.

[`Breakdown.Cert.sliceSupBoundHolds_of`](../lean/?m=Breakdown.Cert.SliceSupBound&d=Breakdown.Cert.sliceSupBoundHolds_of)

### Lemma 7.7

[Authors’ statement](../?l=b160680-161205) · [Adapted statement](../adapted/?l=b183909-184434)

**Proved in the stated formal form.** [`NavierStokes.lemma_7_7`](https://github.com/wcook04/proof-reader/blob/5cf49623675e7fcb3ae59ffcc69d9f736fbaed0a/lean-wrappers/navier-stokes-edition/lean/SectionSeven.lean#L141). Compactness is proved after applying the solenoidal projection, on the graph domain.

**Lean is weaker.** The conclusion gives a bounded projected convection operator and identifies its pairing with the physical convection terms. The symmetry and compactness conclusions of Lemma 7.7 are supplied by other results.

[`Breakdown.Cert.extendedConvectionHolds_of`](../lean/?m=Breakdown.Cert.ExtendedConvection&d=Breakdown.Cert.extendedConvectionHolds_of)

### Proposition 7.8

[Authors’ statement](../?l=b164640-165325) · [Adapted statement](../adapted/?l=b188098-188783)

**Proved in the stated formal form.** [`NavierStokes.proposition_7_8`](https://github.com/wcook04/proof-reader/blob/5cf49623675e7fcb3ae59ffcc69d9f736fbaed0a/lean-wrappers/navier-stokes-edition/lean/SectionSeven.lean#L158). Existence and uniqueness are expressed in forcing coordinates for the constructed inverse, with the four normalization equations explicit.

**Same mathematical strength.** For a certificate reduced to unit forcing weight and coincident reference and approximate profiles, the constrained linear problem has an inverse and is injective on the invariant subspace. This is the unique solve of Proposition 7.8 in the variable f = T_S v, with the compactness and coercivity results supplied as hypotheses.

[`Breakdown.Cert.extendedBorderedInvertibleHolds_of`](../lean/?m=Breakdown.Cert.ExtendedBorderedInvertible&d=Breakdown.Cert.extendedBorderedInvertibleHolds_of)

### Proposition 7.9

[Authors’ statement](../?l=b167536-167983) · [Adapted statement](../adapted/?l=b191450-191897)

**Proved in the stated formal form.** [`NavierStokes.proposition_7_9`](https://github.com/wcook04/proof-reader/blob/5cf49623675e7fcb3ae59ffcc69d9f736fbaed0a/lean-wrappers/navier-stokes-edition/lean/SectionSeven.lean#L181). The bound concerns the constructed inverse and the projected residual, with an essential gradient supremum.

**Same mathematical strength.** The estimate has the coefficients 1/w_* + 2S c₃/m and 2S/m of (7.55), initially for the essential supremum of the gradient norm of the constructed free solution. A continuous energy representative gives the pointwise supremum used in the paper.

[`Breakdown.Cert.extendedSupBoundHolds_of`](../lean/?m=Breakdown.Cert.ExtendedSupBound&d=Breakdown.Cert.extendedSupBoundHolds_of)

### Proposition 7.10

[Authors’ statement](../?l=b173785-174199) · [Adapted statement](../adapted/?l=b198278-198692)

**Proved in the stated formal form.** [`NavierStokes.proposition_7_10`](https://github.com/wcook04/proof-reader/blob/5cf49623675e7fcb3ae59ffcc69d9f736fbaed0a/lean-wrappers/navier-stokes-edition/lean/SectionSeven.lean#L198). The solution is given after the certificate's reductions, with the relation between reduced and original multipliers explicit.

**Different formulation.** Proposition 7.10 selects a parameter and a bounded correction with zero total force by a joint weak-topology fixed point. This result reaches that conclusion for a reduced certificate by a unique solve at each parameter followed by a finite-dimensional zero.

[`Breakdown.Cert.extendedExistsZeroHeldHolds_of`](../lean/?m=Breakdown.Cert.ExtendedExistsZeroHeld&d=Breakdown.Cert.extendedExistsZeroHeldHolds_of)

### Proposition 7.11

[Authors’ statement](../?l=b185393-186259) · [Adapted statement](../adapted/?l=b208954-209820)

**Proved in the stated formal form.** [`NavierStokes.proposition_7_11`](https://github.com/wcook04/proof-reader/blob/5cf49623675e7fcb3ae59ffcc69d9f736fbaed0a/lean-wrappers/navier-stokes-edition/lean/SectionSeven.lean#L215). The proof retains the same input profile at every time. It assumes a square-integrable weak Hessian and a specified continuous representative, and concludes extra decay.

**Different formulation.** Proposition 7.11 preserves a specified weak field at every time while producing a smooth profile. This implication only asserts that existence of a weak recurrent field gives existence of a smooth recurrent profile; it permits an orthogonal twist and does not identify the output with the original field.

[`Breakdown.FarField.periodicLerayProfileExists_of_weak`](../lean/?m=Breakdown.CertTorus.Main&d=Breakdown.FarField.periodicLerayProfileExists_of_weak)

### Proposition B.1

[Authors’ statement](../?l=b235285-236313) · [Adapted statement](../adapted/?l=b262843-263871)

**Proved in the stated formal form.** [`NavierStokes.proposition_B_1`](https://github.com/wcook04/proof-reader/blob/5cf49623675e7fcb3ae59ffcc69d9f736fbaed0a/lean-wrappers/navier-stokes-edition/lean/AppendixB.lean#L26). The weak-form estimate permits general admissible weights and states the density inequality through positive and negative integrals.

**Different formulation.** The multiplier theorem gives existence, finite μ-seminorm, the stated norm bound and a comparison of positive and negative density integrals under explicit weak derivative and coefficient assumptions. Finite negative density converts that comparison into (B.20); the paper leaves some admissibility conditions implicit.

[`Breakdown.CoerciveWeak.pieceMultiplierDensityWeakHolds_proof`](../lean/?m=Breakdown.Cert.ExtendedCoerciveMain&d=Breakdown.CoerciveWeak.pieceMultiplierDensityWeakHolds_proof)

**Different formulation.** This is the full multiplier assertion for weak perturbations, with positive and negative density integrals kept separate. It yields the real signed inequality of Proposition B.1 once the negative part is finite and the full coefficient assumptions hold.

[`Breakdown.CoerciveWeak.PieceMultiplierDensityWeakHolds`](../lean/?m=Breakdown.Cert.ExtendedCoerciveDefs&d=Breakdown.CoerciveWeak.PieceMultiplierDensityWeakHolds)

### Lemma B.2

[Authors’ statement](../?l=b239970-240188) · [Adapted statement](../adapted/?l=b268415-268633)

**Proved in the stated formal form.** [`NavierStokes.lemma_B_2`](https://github.com/wcook04/proof-reader/blob/5cf49623675e7fcb3ae59ffcc69d9f736fbaed0a/lean-wrappers/navier-stokes-edition/lean/AppendixB.lean#L57). The statement makes analytic hypotheses explicit and assumes the parameter-wise row lower bound. The constants are symbolic.

**Same mathematical strength.** The two density inequalities and the bounds c_M/√c≤c₁ and √(t/c)≤c₂ imply the a priori certificate estimate. With c=3/50 and t=1000, this is Lemma B.2 for the admitted weak perturbations.

[`Breakdown.CoerciveWeak.extendedCoerciveClause_of_pieceData_proved`](../lean/?m=Breakdown.Cert.ExtendedCoerciveMain&d=Breakdown.CoerciveWeak.extendedCoerciveClause_of_pieceData_proved)

**Lean is weaker.** This combines the two density comparisons into the intermediate quadratic multiplier inequality. The final estimate (7.18) also uses the scalar bounds for c₁ and c₂ in (B.22), supplied in the subsequent coercive estimate.

[`Breakdown.CoerciveWeak.rowMultiplierInequality_of_pieceDensity`](../lean/?m=Breakdown.Cert.ExtendedCoerciveDefs&d=Breakdown.CoerciveWeak.rowMultiplierInequality_of_pieceDensity)

### Lemma B.3

[Authors’ statement](../?l=b242329-242796) · [Adapted statement](../adapted/?l=b271528-271995)

**Proved in the stated formal form.** [`NavierStokes.lemma_B_3`](https://github.com/wcook04/proof-reader/blob/5cf49623675e7fcb3ae59ffcc69d9f736fbaed0a/lean-wrappers/navier-stokes-edition/lean/AppendixB.lean#L90). The two nonnegative identities are proved separately, including infinite values. The printed signed identity uses a finiteness assumption.

**Lean is stronger.** The proof gives the positive- and negative-part identities separately, each with factor 4π. They imply (B.23) when its signed integral is defined and remain meaningful even before either part is known to be finite.

[`Breakdown.CertCell.modeDensityBridge_closed`](../lean/?m=Breakdown.CertCell.CellLayerJunctions&d=Breakdown.CertCell.modeDensityBridge_closed)

**Lean is stronger.** The assertion equates each nonnegative part of the space-time density integral to 4π times its quarter-plane counterpart. Subtracting when the negative part is finite recovers (B.23).

[`Breakdown.CertCell.DensityIdentity`](../lean/?m=Breakdown.CertCell.TopStatements&d=Breakdown.CertCell.DensityIdentity)

### Proposition B.4

[Authors’ statement](../?l=b255480-257482) · [Adapted statement](../adapted/?l=b285656-287658)

**Proved in the stated formal form.** [`NavierStokes.proposition_B_4`](https://github.com/wcook04/proof-reader/blob/5cf49623675e7fcb3ae59ffcc69d9f736fbaed0a/lean-wrappers/navier-stokes-edition/lean/AppendixB.lean#L115). The proof uses the full formal cell conditions and their separate positive and negative density accounts. The printed remainder numbers are outside the conclusion.

**Different formulation.** The result assembles compatible local and global unknowns and the cell estimates from the full finite-data conditions. The paper's four existential error numbers are replaced by explicit row, pairing, slack and credit contributions.

[`Breakdown.CertCell.cellJunctions_closed`](../lean/?m=Breakdown.CertCell.CellLayerClosed&d=Breakdown.CertCell.cellJunctions_closed)

**Different formulation.** The theorem combines the resolved-mode energy estimate with an assumed residual-form bound to obtain the local cell inequality. Its conclusion uses explicit error contributions and signed parts, rather than the four existential numbers of (B.33).

[`Breakdown.CertCell.cellFormAssembly_closed`](../lean/?m=Breakdown.CertCell.CellLayerPartProofs&d=Breakdown.CertCell.cellFormAssembly_closed)

**Different formulation.** The conclusion is finiteness of the negative quarter-plane density for weak perturbations under coefficient lower bounds and reference-field regularity, without requiring the forcing equation. The 4π identity transfers it to I⁻; the remaining conclusions of Proposition B.4 are separate.

[`Breakdown.CertCell.formNegFinite`](../lean/?m=Breakdown.CertCell.FormNegativeFinite&d=Breakdown.CertCell.formNegFinite)

### Lemma B.5

[Authors’ statement](../?l=b261621-262589) · [Adapted statement](../adapted/?l=b292503-293471)

**Proved in the stated formal form.** [`NavierStokes.lemma_B_5`](https://github.com/wcook04/proof-reader/blob/5cf49623675e7fcb3ae59ffcc69d9f736fbaed0a/lean-wrappers/navier-stokes-edition/lean/AppendixB.lean#L142). The result gives the angular bounds and final nonnegativity. Equation (B.36) is absent as a separate conclusion.

**Same mathematical strength.** All four inequalities in (B.35) are proved almost everywhere for weak projected modes: the curl bound and the three angular gains. The paper already includes the curl and curl-gradient inequalities.

[`Breakdown.CertCell.TailBand.angularModeBounds`](../lean/?m=Breakdown.CertCell.TailAngularPlane&d=Breakdown.CertCell.TailBand.angularModeBounds)

**Different formulation.** This is the scalar positivity argument for five nonnegative derivative sizes satisfying the four angular inequalities and the coefficient test. Substituting the actual mode norms gives the last conclusion of Lemma B.5.

[`Breakdown.CertCell.TailBand.pointwiseQuadraticTest`](../lean/?m=Breakdown.CertCell.TailPointwise&d=Breakdown.CertCell.TailBand.pointwiseQuadraticTest)

**Same mathematical strength.** Under the admissible coefficient and scalar tests, the unresolved-mode density is nonnegative almost everywhere on its region. This is the final assertion of Lemma B.5; the four angular inequalities are separate inputs to its proof.

[`Breakdown.CertCell.Assembly.offModeConditionSound_holds`](../lean/?m=Breakdown.CertCell.AssemblyOffModes&d=Breakdown.CertCell.Assembly.offModeConditionSound_holds)

### Lemma B.6

[Authors’ statement](../?l=b264858-265365) · [Adapted statement](../adapted/?l=b295912-296419)

**Proved in the stated formal form.** [`NavierStokes.lemma_B_6`](https://github.com/wcook04/proof-reader/blob/5cf49623675e7fcb3ae59ffcc69d9f736fbaed0a/lean-wrappers/navier-stokes-edition/lean/AppendixBTail.lean#L165). The formal ray geometry adds explicit regularity and bounds. The conclusion includes finiteness of the negative part.

**Different formulation.** The ray-exterior inequality uses the constant 1/4+(|κι₁|−1)₊² and the admitted weak modes. Its radius must be measurable, homogeneous, bounded above and bounded away from zero, assumptions absent from the printed geometric description.

[`Breakdown.CertCell.TailBand.modeRayInverseSquare`](../lean/?m=Breakdown.CertCell.TailRayModes&d=Breakdown.CertCell.TailBand.modeRayInverseSquare)

**Different formulation.** The theorem proves integrability of the negative exterior density and nonnegativity of its integral under the full exterior conditions. These include the bounded positive directional radius or the zero-mode square exterior, together with their coefficient budgets.

[`Breakdown.CertCell.exteriorConditionSound_closed`](../lean/?m=Breakdown.CertCell.CellLayerPartProofs&d=Breakdown.CertCell.exteriorConditionSound_closed)

### Lemma B.7

[Authors’ statement](../?l=b272644-273109) · [Adapted statement](../adapted/?l=b304575-305040)

**Proved in the stated formal form.** [`NavierStokes.lemma_B_7`](https://github.com/wcook04/proof-reader/blob/5cf49623675e7fcb3ae59ffcc69d9f736fbaed0a/lean-wrappers/navier-stokes-edition/lean/AppendixB.lean#L205). The lower bound keeps the nonnegative root contribution and the result makes strict positivity explicit.

**Lean is stronger.** The lower bound retains the quadratic form passed by the root, as well as the pivot gains and negative-column losses. The paper's (B.41) follows after dropping that nonnegative root contribution.

[`Breakdown.CertCell.Certificate.signedTreeLowerBound`](../lean/?m=Breakdown.CertCell.CertTreeLowerBound&d=Breakdown.CertCell.Certificate.signedTreeLowerBound)

**Different formulation.** The conclusion gives a positive subspace of the root form with dimension at least the number of physical coordinates. The proof chooses the common kernel of negative-column pairings, while the printed lemma states positivity of the total form explicitly on that kernel.

[`Breakdown.CertCell.Certificate.pivotCountPositive`](../lean/?m=Breakdown.CertCell.CertPivotCount&d=Breakdown.CertCell.Certificate.pivotCountPositive)

### Proposition B.8

[Authors’ statement](../?l=b275971-276185) · [Adapted statement](../adapted/?l=b308084-308298)

**Proved in the stated formal form.** [`NavierStokes.proposition_B_8`](https://github.com/wcook04/proof-reader/blob/5cf49623675e7fcb3ae59ffcc69d9f736fbaed0a/lean-wrappers/navier-stokes-edition/lean/AppendixB.lean#L253). The estimate is stated as a comparison of nonnegative extended integrals for periodic weak perturbations under all formal cell conditions.

**Different formulation.** The theorem derives the lower bound (B.21) and negative-part finiteness from the complete cell, shape and matrix conditions. Its assumptions include coefficient, gauge and error requirements that the paper explicitly leaves unwritten.

[`Breakdown.CertCell.rowRestClause_closed`](../lean/?m=Breakdown.CertCell.CellLayerClosed&d=Breakdown.CertCell.rowRestClause_closed)

**Same mathematical strength.** The condition states finiteness of negative density and the lower bound (B.21), with c and the pinning weight as parameters. Taking c=3/50 and the pinning weight 1000 gives the printed constants, after subtracting the finite negative integral.

[`Breakdown.CoerciveWeak.RowRestClause`](../lean/?m=Breakdown.Cert.ExtendedCoerciveDefs&d=Breakdown.CoerciveWeak.RowRestClause)

### Lemma B.9

[Authors’ statement](../?l=b280764-282654) · [Adapted statement](../adapted/?l=b313898-315788)

**Proved in the stated formal form.** [`NavierStokes.lemma_B_9`](https://github.com/wcook04/proof-reader/blob/5cf49623675e7fcb3ae59ffcc69d9f736fbaed0a/lean-wrappers/navier-stokes-edition/lean/AppendixB.lean#L273). The proof uses an arbitrary finite decomposition with explicit hypotheses for derivative identification.

**Same mathematical strength.** The central and parameter-shift bounds imply the operator difference estimate (7.19), using the first scalar budget in (B.48). This is the first conclusion of Lemma B.9.

[`Breakdown.CertReduction.gapTransferBridgeHolds_proof`](../lean/?m=Breakdown.CellReduction.ReductionClosed&d=Breakdown.CertReduction.gapTransferBridgeHolds_proof)

**Same mathematical strength.** The central and parameter-shift norms control the change in the quadratic convection form by c₃″‖u‖w². This supplies the second profile contribution to the lower bound in Lemma B.9.

[`Breakdown.CertReduction.formShiftBridgeHolds_proof`](../lean/?m=Breakdown.CellReduction.ReductionClosed&d=Breakdown.CertReduction.formShiftBridgeHolds_proof)

**Same mathematical strength.** The reference strain lower bound and L³ gradient norm give the reference quadratic-form lower bound with c₃′ from (B.48). Combining it with the profile-shift estimate gives (7.22).

[`Breakdown.CertReduction.frozenFormBridgeHolds_of_convection`](../lean/?m=Breakdown.CellReduction.ReductionClosed&d=Breakdown.CertReduction.frozenFormBridgeHolds_of_convection)

### Lemma B.10

[Authors’ statement](../?l=b286225-286624) · [Adapted statement](../adapted/?l=b319638-320037)

**Proved in the stated formal form.** [`NavierStokes.lemma_B_10`](https://github.com/wcook04/proof-reader/blob/5cf49623675e7fcb3ae59ffcc69d9f736fbaed0a/lean-wrappers/navier-stokes-edition/lean/AppendixB.lean#L303). The bound on the integral of the product of norms implies the printed pairing estimate.

**Same mathematical strength.** Integrating the quadratic adjoint slice estimate over one period gives (7.32) with either norm choice of Lemma B.10. The formulation also permits the adjoint to depend on the parameter.

[`Breakdown.CertReduction.adjointQuadraticBridge_of`](../lean/?m=Breakdown.CellReduction.AdjointQuadraticBridge&d=Breakdown.CertReduction.adjointQuadraticBridge_of)

**Lean is weaker.** The theorem gives the almost-everywhere time-slice estimate for (v·∇)v paired with ψ, using either its L² or L³ norm. The period-integrated conclusion of Lemma B.10 is supplied by a separate integration step.

[`Breakdown.CertReduction.adjointQuadTerm_of`](../lean/?m=Breakdown.CellReduction.AdjointQuadTerm&d=Breakdown.CertReduction.adjointQuadTerm_of)

### Lemma B.11

[Authors’ statement](../?l=b288370-288657) · [Adapted statement](../adapted/?l=b321900-322187)

**Open Lean proposition.** [`NavierStokes.lemma_B_11`](https://github.com/wcook04/proof-reader/blob/5cf49623675e7fcb3ae59ffcc69d9f736fbaed0a/lean-wrappers/navier-stokes-edition/lean/OpenTargets.lean#L598). Joint absolute integrability remains open. A companion theorem gives slice integrability and a time-integrable signed spatial pairing.

**Different formulation.** The two parts of the dual decomposition imply the absolute pairing bound and spatial integrability at almost every time, with integrability of the time integral. The statement permits tests without time periodicity and does not itself assert the joint absolute integrability printed in Lemma B.11.

[`Breakdown.AdjointDefect.dualBoundedBound_of_parts`](../lean/?m=Breakdown.CellReduction.AdjointDualBounded&d=Breakdown.AdjointDefect.dualBoundedBound_of_parts)

**Lean is weaker.** The weighted Hardy bound 2‖|y|R′‖H≤n′ gives the dual estimate for the plain remainder. The finite harmonic remainder and their sum are separate parts of Lemma B.11.

[`Breakdown.AdjointDefect.remainderPlainHolds_proof`](../lean/?m=Breakdown.CellReduction.AdjointRemainderPlain&d=Breakdown.AdjointDefect.remainderPlainHolds_proof)

**Lean is weaker.** This proves the dual estimate for the finite harmonic remainder with coefficient (|k|+1/2)⁻² and the component weights 1/2,1/2,1. The plain remainder is combined with it in the full estimate of Lemma B.11.

[`Breakdown.AdjointDefect.remainderAzimuthalHolds_proof`](../lean/?m=Breakdown.CellReduction.AdjointRemainderAzimuthal&d=Breakdown.AdjointDefect.remainderAzimuthalHolds_proof)

### Lemma B.12

[Authors’ statement](../?l=b296453-297231) · [Adapted statement](../adapted/?l=b330620-331398)

**Proved in the stated formal form.** [`NavierStokes.lemma_B_12`](https://github.com/wcook04/proof-reader/blob/5cf49623675e7fcb3ae59ffcc69d9f736fbaed0a/lean-wrappers/navier-stokes-edition/lean/AppendixB.lean#L344). The formal statement exposes regularity and decomposition premises and records the coefficient budget through its data fields.

**Different formulation.** The linear adjoint estimate follows from the representation, potential, dual, pin-error and parameter-shift estimates, under explicit potential and curl-potential hypotheses. For the cell construction these are supplied by the finite shape conditions, and the empty fitted set recovers Lemma B.12.

[`Breakdown.AdjointDefect.adjointDefectBridge_of_pieces`](../lean/?m=Breakdown.CellReduction.AdjointAssembly&d=Breakdown.AdjointDefect.adjointDefectBridge_of_pieces)

### Lemma B.13

[Authors’ statement](../?l=b303479-304912) · [Adapted statement](../adapted/?l=b338014-339447)

**Proved in the stated formal form.** [`NavierStokes.lemma_B_13`](https://github.com/wcook04/proof-reader/blob/5cf49623675e7fcb3ae59ffcc69d9f736fbaed0a/lean-wrappers/navier-stokes-edition/lean/AppendixB.lean#L372). The statement assumes the cell and pressure representation explicitly and records the error budget in the offset data.

**Same mathematical strength.** The local quadratic expansion, absolute coefficient enclosures and exterior Cauchy–Schwarz bound imply the offset estimate (7.34). The specified profile construction makes the target pinning gap zero, as in Lemma B.13.

[`Breakdown.CellReduction.Instantiation.offsetClause_holds_of`](../lean/?m=Breakdown.CellReduction.InstOffsetClause&d=Breakdown.CellReduction.Instantiation.offsetClause_holds_of)

**Same mathematical strength.** Inside the matching ball, the residual is the central coefficient plus the linear and upper-triangular quadratic parameter sums, almost everywhere. This is the local expansion used in the proof of Lemma B.13.

[`Breakdown.CellReduction.Instantiation.offsetBallIdentity_holds`](../lean/?m=Breakdown.CellReduction.InstOffsetIdentity&d=Breakdown.CellReduction.Instantiation.offsetBallIdentity_holds)

### Proposition B.14

[Authors’ statement](../?l=b307737-308320) · [Adapted statement](../adapted/?l=b342291-342874)

**Proved in the stated formal form.** [`NavierStokes.proposition_B_14`](https://github.com/wcook04/proof-reader/blob/5cf49623675e7fcb3ae59ffcc69d9f736fbaed0a/lean-wrappers/navier-stokes-edition/lean/AppendixB.lean#L394). The proof produces an extended certificate after choosing a decay constant. It retains the full formal cell hypotheses.

**Different formulation.** The construction produces a certificate after choosing a sufficiently large decay constant, from the full fifteen groups of cell assumptions and the analytic estimates. The paper omits some finite-data hypotheses, so equivalence of the complete condition lists cannot be checked from Proposition B.14 alone.

[`Breakdown.CellLayerSystem.isExtendedCertificate_of_parts`](../lean/?m=Breakdown.CellReduction.CellLayerBreakdownCompose&d=Breakdown.CellLayerSystem.isExtendedCertificate_of_parts)
