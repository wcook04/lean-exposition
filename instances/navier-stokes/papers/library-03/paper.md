
<!-- passage:front -->
# Library guide 3: Breakdown/Cert

**Navier–Stokes pages:** [the paper](../navier-stokes-paper/paper.pdf) · [proof routes](../navier-stokes-routes/paper.md) · [routes in detail](../navier-stokes-route-details/paper.md) · library guide: [1](../navier-stokes-library-01/paper.md) [2](../navier-stokes-library-02/paper.md) **3** [4](../navier-stokes-library-04/paper.md) [5](../navier-stokes-library-05/paper.md) [6](../navier-stokes-library-06/paper.md) [7](../navier-stokes-library-07/paper.md) [8](../navier-stokes-library-08/paper.md) [9](../navier-stokes-library-09/paper.md) [10](../navier-stokes-library-10/paper.md) [11](../navier-stokes-library-11/paper.md) [12](../navier-stokes-library-12/paper.md) [13](../navier-stokes-library-13/paper.md) [14](../navier-stokes-library-14/paper.md) [15](../navier-stokes-library-15/paper.md) [16](../navier-stokes-library-16/paper.md) [17](../navier-stokes-library-17/paper.md) [18](../navier-stokes-library-18/paper.md) [19](../navier-stokes-library-19/paper.md) [20](../navier-stokes-library-20/paper.md) [21](../navier-stokes-library-21/paper.md) [22](../navier-stokes-library-22/paper.md) [23](../navier-stokes-library-23/paper.md) [24](../navier-stokes-library-24/paper.md) [25](../navier-stokes-library-25/paper.md) [26](../navier-stokes-library-26/paper.md) [27](../navier-stokes-library-27/paper.md) [28](../navier-stokes-library-28/paper.md) [29](../navier-stokes-library-29/paper.md) [30](../navier-stokes-library-30/paper.md)

*A plain title and a sentence for each declaration in `Breakdown.Cert.Basic` to `Breakdown.Cert.CoercivePerturbationFactsProof` of Alpöge and Buckmaster's Lean at `ad53419de079eb8f95f60313473374624a348546`, in the authors' file order. Prepared with AI assistance. The authors have not reviewed it.*

Each paragraph names one declaration and says whether it is a definition, a proposition that the library defines (its name usually ends in `Holds` or `Statement`) or a proved result, then what it states. Click a paragraph to open its Lean on the right.

### Breakdown.Cert.Basic

The certificate's analytic objects live in periodic L² spaces over a closed half-order graph; this file defines their projections, weighted energy, free inverse, convection, actuators, pins, and bordered operator, with explicit specifications for the operators chosen by existence.

**Paper context:** §7 certificate construction: functional spaces, linear operators, and the bordered correction problem.

**Instance: Zero is less than one.** The real inequality zero less than one is registered as a type-class fact. Source: `Breakdown.Cert.factZeroLtOneReal` (`Breakdown/Cert/Basic.lean:15`).

**Definition: Time in the unit interval.** Choose the representative of a circle time in the half-open interval from zero to one. Source: `Breakdown.Cert.circleRep` (`Breakdown/Cert/Basic.lean:19`).

**Definition: Read a field on the time circle.** Evaluate a real-time field at the chosen representative of a circle time. Source: `Breakdown.Cert.onCircle` (`Breakdown/Cert/Basic.lean:21`).

**Definition: Embed a square-integrable circle field.** Use the field's L² class when it is square integrable, and use zero otherwise. Source: `Breakdown.Cert.circleLpOrZero` (`Breakdown/Cert/Basic.lean:23`).

**Definition: The solenoidal energy space.** Use the Fourier energy space as the underlying Hilbert space of the certificate construction. Source: `Breakdown.Cert.HBar` (`Breakdown/Cert/Basic.lean:27`).

**Instance: Completeness of the closed graph.** The closed half-order graph is a complete metric space. Source: `anonymous instance` (`Breakdown/Cert/Basic.lean:32`). [Open this instance in the source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Basic.lean#L32).

**Definition: First component of the graph.** Project a member of the closed half-order graph onto its first Fourier-space component. Source: `Breakdown.Cert.gradPart` (`Breakdown/Cert/Basic.lean:37`).

**Definition: Second component of the graph.** Project a member of the closed half-order graph onto its second Fourier-space component. Source: `Breakdown.Cert.secondPart` (`Breakdown/Cert/Basic.lean:39`).

**Definition: First graph component over time.** Apply the first graph projection to an L² field on the time circle. Source: `Breakdown.Cert.gradCLM` (`Breakdown/Cert/Basic.lean:45`).

**Definition: Second graph component over time.** Apply the second graph projection to an L² field on the time circle. Source: `Breakdown.Cert.secondCLM` (`Breakdown/Cert/Basic.lean:47`).

**Definition: Weighted gradient energy of a slice.** Integrate the weight times the sum of the squared spatial derivatives on one time slice. Source: `Breakdown.Cert.sliceWeightedGrad` (`Breakdown/Cert/Basic.lean:49`).

**Definition: The weighted graph energy.** Add the squared L² norm of the second graph component to the time integral of the weighted gradient energy. Source: `Breakdown.Cert.energyW` (`Breakdown/Cert/Basic.lean:52`).

**Definition: Read an energy element in space.** Turn a solenoidal Fourier element into its real L² representative in physical space. Source: `Breakdown.Cert.toPhysH` (`Breakdown/Cert/Basic.lean:60`).

**Definition: The transverse Fourier projection.** Subtract the longitudinal Fourier projection from the identity. Source: `Breakdown.Cert.solenoidalSymbol` (`Breakdown/Cert/Basic.lean:62`).

**Definition: Specification of the Leray projection.** Require the proposed operator to agree with the transverse Fourier projection of each real L² field. Source: `Breakdown.Cert.ProjSpec` (`Breakdown/Cert/Basic.lean:65`).

**Definition: Project a physical field.** Embed the physical field in L² when possible and apply the chosen solenoidal projection. Source: `Breakdown.Cert.solField` (`Breakdown/Cert/Basic.lean:70`).

**Definition: Periodise a test field in Hilbert space.** Periodise a space-time test field and read it in the Hilbert space over the time circle. Source: `Breakdown.Cert.testInHH` (`Breakdown/Cert/Basic.lean:76`).

**Definition: Fourier smoothing on the energy space.** Apply the scalar smoothing symbol to a solenoidal Fourier element. Source: `Breakdown.Cert.smoothH` (`Breakdown/Cert/Basic.lean:78`).

**Definition: Smoothing followed by dilation.** Combine smoothing at time one minus exp(-τ) with dilation by exp(-τ). Source: `Breakdown.Cert.slicePropagator` (`Breakdown/Cert/Basic.lean:81`).

**Definition: Translate a field around the circle.** Use the measure-preserving time translation to define a continuous linear map on L² circle fields. Source: `Breakdown.Cert.shiftLp` (`Breakdown/Cert/Basic.lean:84`).

**Definition: Integrand for the free inverse.** Shift the source backwards by τ/P and apply the slice propagator at τ. Source: `Breakdown.Cert.propagatorIntegrand` (`Breakdown/Cert/Basic.lean:89`).

**Definition: Specification of the gradient inverse.** Require the proposed inverse to equal the integral of the propagator over positive τ. Source: `Breakdown.Cert.GradInvSpec` (`Breakdown/Cert/Basic.lean:92`).

**Definition: Choose the gradient inverse.** Choose a bounded linear operator satisfying the propagator-integral specification when one exists, and use zero otherwise. Source: `Breakdown.Cert.gradInv` (`Breakdown/Cert/Basic.lean:95`).

**Definition: Specification of the free inverse.** Require the first graph component of the proposed free inverse to equal the gradient inverse. Source: `Breakdown.Cert.FreeInvSpec` (`Breakdown/Cert/Basic.lean:97`).

**Definition: Specification of linear convection.** Require the proposed operator to agree almost everywhere with the solenoidal projection of linear convection about the profile. Source: `Breakdown.Cert.ConvectionSpec` (`Breakdown/Cert/Basic.lean:104`).

**Definition: Choose the convection operator.** Choose an operator satisfying the linear-convection specification when one exists, and use zero otherwise. Source: `Breakdown.Cert.convection` (`Breakdown/Cert/Basic.lean:108`).

**Definition: One forcing field in Hilbert space.** Read one actuator field in the Hilbert space over the time circle. Source: `Breakdown.Cert.actuatorSlice` (`Breakdown/Cert/Basic.lean:111`).

**Definition: Combine the forcing fields.** Form the bounded linear combination of actuator fields with the supplied finite coefficient vector. Source: `Breakdown.Cert.actuatorH` (`Breakdown/Cert/Basic.lean:113`).

**Definition: Pin pairing on one time slice.** Integrate the componentwise pairing of the perturbation gradient with a pin field. Source: `Breakdown.Cert.pinSlice` (`Breakdown/Cert/Basic.lean:116`).

**Definition: Specification of the pin map.** Require each output coordinate to equal the time integral of its pin pairing. Source: `Breakdown.Cert.PinSpec` (`Breakdown/Cert/Basic.lean:119`).

**Definition: Choose the pin map.** Choose a bounded linear map satisfying the pin-pairing specification when one exists, and use zero otherwise. Source: `Breakdown.Cert.pinMap` (`Breakdown/Cert/Basic.lean:122`).

**Definition: The quadratic convection field.** Form the directional derivative of the second velocity along the first velocity. Source: `Breakdown.Cert.productSlice` (`Breakdown/Cert/Basic.lean:125`).

**Definition: Quadratic convection in Hilbert space.** Project the quadratic convection field onto the solenoidal Hilbert space on each circle time. Source: `Breakdown.Cert.productH` (`Breakdown/Cert/Basic.lean:128`).

**Definition: The profile defect in Hilbert space.** Read the profile's equation defect, including its pressure and actuator terms, in the periodic Hilbert space. Source: `Breakdown.Cert.defectH` (`Breakdown/Cert/Basic.lean:132`).

**Definition: The remaining pin displacement.** Subtract the profile's current pin values from the target pin values. Source: `Breakdown.Cert.targetGap` (`Breakdown/Cert/Basic.lean:135`).

**Definition: A time-dependent velocity field.** Use a function of real time and physical position with vector values as the velocity-field type. Source: `Breakdown.Cert.VelField` (`Breakdown/Cert/Basic.lean:138`).

**Definition: A time-dependent gradient field.** Use a function of time and position taking values in linear maps as the gradient-field type. Source: `Breakdown.Cert.GradField` (`Breakdown/Cert/Basic.lean:140`).

**Definition: A time-dependent second derivative.** Use a function of time and position taking values in bilinear maps as the second-derivative type. Source: `Breakdown.Cert.SecondField` (`Breakdown/Cert/Basic.lean:142`).

**Definition: Physical representatives of graph data.** Require periodic measurable velocity and derivative fields to represent the graph element and satisfy its weak-gradient and trace identities. Source: `Breakdown.Cert.IsReadingOf` (`Breakdown/Cert/Basic.lean:144`).

**Definition: Choose physical representatives.** Choose physical representatives satisfying the reading conditions when they exist, and use three zero fields otherwise. Source: `Breakdown.Cert.readingOf` (`Breakdown/Cert/Basic.lean:159`).

**Definition: Convection of chosen representatives.** Apply the second representative's gradient to the first representative's velocity. Source: `Breakdown.Cert.productField` (`Breakdown/Cert/Basic.lean:163`).

**Definition: Rotate a periodic Hilbert field.** Apply the spatial Fourier rotation to each value of the field on the time circle. Source: `Breakdown.Cert.rotHH` (`Breakdown/Cert/Basic.lean:166`).

**Definition: Specification of the bordered inverse.** Require a proposed right inverse to preserve the prescribed symmetry subspace and solve the bordered equation there. Source: `Breakdown.Cert.BorderedInvSpec` (`Breakdown/Cert/Basic.lean:179`).

**Definition: Choose the bordered right inverse.** Choose a bounded operator satisfying the bordered-inverse specification when one exists, and use zero otherwise. Source: `Breakdown.Cert.borderedInv` (`Breakdown/Cert/Basic.lean:184`).

**Definition: The held equation's forcing data.** Pair the negative profile defect and quadratic correction with the remaining pin displacement. Source: `Breakdown.Cert.heldRight` (`Breakdown/Cert/Basic.lean:188`).

**Definition: One step of the held iteration.** Apply the bordered inverse to the held right side and then recover the graph correction with the free inverse. Source: `Breakdown.Cert.heldStep` (`Breakdown/Cert/Basic.lean:191`).

**Definition: The bounded set for held iteration.** Restrict corrections by symmetry, the combined energy-size bound, and the supremum bound on the first graph component. Source: `Breakdown.Cert.heldSet` (`Breakdown/Cert/Basic.lean:195`).

**Definition: Conditions for a held solution.** Require the invariant field and multiplier to satisfy the nonlinear equation, pin equations, and the stated size bounds. Source: `Breakdown.Cert.IsHeldSolution` (`Breakdown/Cert/Basic.lean:202`).

**Definition: The corrected total multiplier.** Add the selected held-solution multiplier to the profile's original multiplier, using zero correction if no held solution exists. Source: `Breakdown.Cert.multiplierOf` (`Breakdown/Cert/Basic.lean:211`).

### Breakdown.Cert.BorderedInvertible

This file turns the coercive zero-kernel argument into an inverse on the symmetry subspace by combining a closed invariant space, its projection, and the compact-perturbation inverse theorem.

**Paper context:** §7 certificate construction: invertibility of the bordered correction operator.

**Theorem: The symmetry subspace is closed.** The common kernel of the symmetry constraints is closed. Source: `Breakdown.Cert.isClosed_invariantHH` (`Breakdown/Cert/BorderedInvertible.lean:13`).

**Theorem: The symmetry subspace is complete.** The invariant Hilbert subspace is complete. Source: `Breakdown.Cert.completeSpace_invariantHH` (`Breakdown/Cert/BorderedInvertible.lean:17`).

**Theorem: Project onto invariant fields.** There is a continuous linear projection onto the symmetry subspace that fixes each invariant field. Source: `Breakdown.Cert.exists_projection_invariantHH` (`Breakdown/Cert/BorderedInvertible.lean:20`).

**Theorem: The second graph component is faithful.** A closed-graph element with zero second component is zero. Source: `Breakdown.Cert.Internal.BorderedInvertible.eq_zero_of_secondPart_eq_zero` (`Breakdown/Cert/BorderedInvertible.lean:28`).

**Theorem: The second time projection is faithful.** A periodic graph element with zero second-component field is zero. Source: `Breakdown.Cert.Internal.BorderedInvertible.eq_zero_of_secondCLM_eq_zero` (`Breakdown/Cert/BorderedInvertible.lean:52`).

**Theorem: The bordered operator has zero kernel.** Under the certificate and coercivity assumptions, an invariant vector in the kernel of the bordered operator is zero. Source: `Breakdown.Cert.Internal.BorderedInvertible.eq_zero_of_bordered_eq_zero` (`Breakdown/Cert/BorderedInvertible.lean:63`).

**Theorem: An invariant bordered right inverse.** Compactness, invariance, injectivity, and an invariant projection give a right inverse on the symmetry subspace. Source: `Breakdown.Cert.Internal.BorderedInvertible.exists_borderedInvSpec` (`Breakdown/Cert/BorderedInvertible.lean:156`).

**Theorem: Invert the bordered operator.** The compactness, coercivity, equivariance, data, and free-inverse interfaces imply the bordered-invertibility interface. Source: `Breakdown.Cert.borderedInvertibleHolds_of` (`Breakdown/Cert/BorderedInvertible.lean:185`).

### Breakdown.Cert.BoxZero

A coordinatewise error enclosure makes a preconditioned map preserve a finite parameter box, so the fixed-point theorem supplies a zero inside that box.

**Paper context:** §7, Proposition 7.10: the finite-dimensional parameter-zero step.

**Theorem: Coordinate bound for matrix action.** The absolute value of a matrix-vector product coordinate is at most the corresponding row sum of absolute products. Source: `Breakdown.BoxZeroInternal.abs_mulVec_apply_le` (`Breakdown/Cert/BoxZero.lean:10`).

**Theorem: A zero inside the parameter box.** A continuous map sufficiently close to an invertible linear map has a zero in the closed parameter box when the stated coordinatewise enclosure fits inside it. Source: `Breakdown.exists_zero_of_inclusion` (`Breakdown/Cert/BoxZero.lean:19`).

### Breakdown.Cert.CoerciveAbsorb

The mode-density comparison is closed by allocating harmonic interaction costs to incoming and outgoing square terms, cancelling their sums, and integrating the resulting signed inequality.

**Paper context:** Appendix B, Proposition B.1: absorption and summation of the ordinary mode-weight density estimate.

**Theorem: Absorb a product into squares.** For positive K, the product uv is at most Ku²/4 plus v²/K. Source: `Breakdown.Coercive.Internal.Absorb.mul_le_absorb` (`Breakdown/Cert/CoerciveAbsorb.lean:17`).

**Theorem: Young's inequality with a free weight.** For positive t, the product uv is at most half of tu² plus v²/t. Source: `Breakdown.Coercive.Internal.Absorb.mul_le_half` (`Breakdown/Cert/CoerciveAbsorb.lean:24`).

**Theorem: Proposition indicators are nonnegative.** The real-valued indicator of a proposition is nonnegative. Source: `Breakdown.Coercive.Internal.Absorb.ind_nonneg` (`Breakdown/Cert/CoerciveAbsorb.lean:30`).

**Theorem: An indicator is at most one.** The real-valued indicator of a proposition is at most one. Source: `Breakdown.Coercive.Internal.Absorb.ind_le_one` (`Breakdown/Cert/CoerciveAbsorb.lean:34`).

**Theorem: Indicators respect implication.** If one proposition implies another, its real-valued indicator is no larger. Source: `Breakdown.Coercive.Internal.Absorb.ind_mono` (`Breakdown/Cert/CoerciveAbsorb.lean:38`).

**Theorem: A true proposition has indicator one.** The indicator of a proposition supplied with a proof equals one. Source: `Breakdown.Coercive.Internal.Absorb.ind_of` (`Breakdown/Cert/CoerciveAbsorb.lean:44`).

**Theorem: Absorb one harmonic interaction.** The weighted harmonic product is bounded by the stated square cost at the source and the shared square cost at the destination. Source: `Breakdown.Coercive.Internal.Absorb.wave_absorb` (`Breakdown/Cert/CoerciveAbsorb.lean:48`).

**Theorem: A squared difference bound.** The squared norm of a difference is at most twice the sum of the two squared norms. Source: `Breakdown.Coercive.Internal.Absorb.sq_norm_sub_le` (`Breakdown/Cert/CoerciveAbsorb.lean:79`).

**Theorem: Squared complex norm is nonnegative.** The squared complex norm is nonnegative for the stated data. Source: `Breakdown.Coercive.Internal.Absorb.cnormSq_nonneg'` (`Breakdown/Cert/CoerciveAbsorb.lean:85`).

**Theorem: Curl square is controlled by gradient.** The squared curl contraction is at most twice the squared norm of the gradient array. Source: `Breakdown.Coercive.Internal.Absorb.cnormSq_curlOfGrad_le` (`Breakdown/Cert/CoerciveAbsorb.lean:88`).

**Theorem: Curl amplitude is controlled by gradient.** The vorticity amplitude is at most √2 times the gradient amplitude. Source: `Breakdown.Coercive.Internal.Absorb.vortAmp_le` (`Breakdown/Cert/CoerciveAbsorb.lean:99`).

**Theorem: Each nonnegative summand is bounded.** A nonnegative summand belonging to a finite sum is bounded by every upper bound for that sum. Source: `Breakdown.Coercive.Internal.Absorb.single_le_of_sum_le` (`Breakdown/Cert/CoerciveAbsorb.lean:105`).

**Theorem: Allocate the curl interaction costs.** Under the stated positivity and amplitude bounds, the curl-density lower expression plus its incoming cost is bounded by the positive curl term, remainder, and outgoing costs. Source: `Breakdown.Coercive.Internal.Absorb.eps_core` (`Breakdown/Cert/CoerciveAbsorb.lean:109`).

**Theorem: Weighted Cauchy-Schwarz inequality.** The square of a finite weighted sum is bounded by the sum of its nonnegative weights times the weighted sum of squares. Source: `Breakdown.Coercive.Internal.Absorb.sum_sq_le_weighted` (`Breakdown/Cert/CoerciveAbsorb.lean:201`).

**Theorem: Allocate the velocity interaction costs.** Under the stated positivity and amplitude bounds, the velocity-density lower expression plus its incoming cost is bounded by the positive velocity term, remainder, and outgoing costs. Source: `Breakdown.Coercive.Internal.Absorb.mu_core` (`Breakdown/Cert/CoerciveAbsorb.lean:206`).

**Theorem: Discard the negative part in ENNReal.** Converting a real number to a nonnegative extended real gives the same result as first taking its maximum with zero. Source: `Breakdown.Coercive.Internal.Absorb.ofReal_eq_max` (`Breakdown/Cert/CoerciveAbsorb.lean:257`).

**Theorem: Separate positive and negative parts.** The positive part of a real number equals that number plus its negative part. Source: `Breakdown.Coercive.Internal.Absorb.max_split` (`Breakdown/Cert/CoerciveAbsorb.lean:262`).

**Theorem: Cancel summed interaction costs.** The hypotheses on the shifted costs allow their cancellation in the signed inequality between the total mode density and remainder. Source: `Breakdown.Coercive.Internal.Absorb.tsum_cancel` (`Breakdown/Cert/CoerciveAbsorb.lean:269`).

**Theorem: Additivity of the period integral.** Under the measurability hypothesis, the iterated nonnegative integral of a sum equals the sum of the two iterated integrals. Source: `Breakdown.Coercive.Internal.Absorb.lintegral_add_left_iter` (`Breakdown/Cert/CoerciveAbsorb.lean:314`).

**Theorem: Integrate a signed density bound.** The pointwise density comparison and the finite integral identity imply the signed inequality for the integrated densities. Source: `Breakdown.Coercive.Internal.Absorb.integrate_step` (`Breakdown/Cert/CoerciveAbsorb.lean:326`).

**Definition: Curl cost at a shifted mode.** Collect the curl-weight interaction costs assigned to the mode shifted by one profile harmonic. Source: `Breakdown.Coercive.Internal.Absorb.epsShift` (`Breakdown/Cert/CoerciveAbsorb.lean:369`).

**Definition: Velocity cost at a shifted mode.** Collect the velocity-weight interaction costs assigned to the mode shifted by one profile harmonic. Source: `Breakdown.Coercive.Internal.Absorb.muShift` (`Breakdown/Cert/CoerciveAbsorb.lean:375`).

**Definition: Incoming curl interaction cost.** Collect the curl interaction cost available at the receiving mode from its neighbouring weights. Source: `Breakdown.Coercive.Internal.Absorb.epsDebt` (`Breakdown/Cert/CoerciveAbsorb.lean:380`).

**Definition: Incoming velocity interaction cost.** Collect the velocity interaction cost available at the receiving mode from its neighbouring weights. Source: `Breakdown.Coercive.Internal.Absorb.muDebt` (`Breakdown/Cert/CoerciveAbsorb.lean:385`).

**Theorem: Split the total mode density.** The mode density equals its base, curl-weight, and velocity-weight contributions. Source: `Breakdown.Coercive.Internal.Absorb.density_split` (`Breakdown/Cert/CoerciveAbsorb.lean:392`).

**Theorem: Curl density and shifted costs.** The curl density together with its incoming cost is bounded by the positive curl term, its remainder, and the shifted interaction costs. Source: `Breakdown.Coercive.Internal.Absorb.eps_mode` (`Breakdown/Cert/CoerciveAbsorb.lean:403`).

**Theorem: Velocity density and shifted costs.** The velocity density together with its incoming cost is bounded by the positive velocity term, its remainder, and the shifted interaction costs. Source: `Breakdown.Coercive.Internal.Absorb.mu_mode` (`Breakdown/Cert/CoerciveAbsorb.lean:431`).

**Theorem: Combine the two absorption estimates.** The full mode term and incoming costs are bounded by its positive contribution, remainder, and shifted costs. Source: `Breakdown.Coercive.Internal.Absorb.mode_step` (`Breakdown/Cert/CoerciveAbsorb.lean:451`).

**Theorem: Neighbouring curl weight bound.** The curl weight at an allowed shifted mode is bounded by the receiving mode's neighbouring curl weight. Source: `Breakdown.Coercive.Internal.Absorb.eps_le_epsNb` (`Breakdown/Cert/CoerciveAbsorb.lean:465`).

**Theorem: Neighbouring velocity weight bound.** The velocity weight at an allowed shifted mode is bounded by the receiving mode's neighbouring velocity weight. Source: `Breakdown.Coercive.Internal.Absorb.mu_le_muNb` (`Breakdown/Cert/CoerciveAbsorb.lean:471`).

**Theorem: Incoming costs cover shifted charges.** The sum of the allowed shifted curl and velocity charges is bounded by the receiving mode's combined incoming cost. Source: `Breakdown.Coercive.Internal.Absorb.shift_le_debt` (`Breakdown/Cert/CoerciveAbsorb.lean:477`).

**Theorem: Combined shifted costs are nonnegative.** The sum of the shifted curl and velocity costs is nonnegative under the coefficient and amplitude hypotheses. Source: `Breakdown.Coercive.Internal.Absorb.shift_nonneg` (`Breakdown/Cert/CoerciveAbsorb.lean:540`).

**Theorem: Combined incoming costs are nonnegative.** The sum of the incoming curl and velocity costs is nonnegative under the coefficient and amplitude hypotheses. Source: `Breakdown.Coercive.Internal.Absorb.debt_nonneg` (`Breakdown/Cert/CoerciveAbsorb.lean:553`).

**Theorem: Positive mode contribution nonnegativity.** The positive mode contribution is nonnegative for the stated data. Source: `Breakdown.Coercive.Internal.Absorb.modePos_nonneg` (`Breakdown/Cert/CoerciveAbsorb.lean:567`).

**Theorem: Bound the neighbouring curl weight.** The neighbouring curl weight is bounded by the supplied uniform curl-weight bound. Source: `Breakdown.Coercive.Internal.Absorb.epsNb_le` (`Breakdown/Cert/CoerciveAbsorb.lean:575`).

**Theorem: The combined incoming-cost sum is finite.** The nonnegative extended-real sum of the combined incoming curl and velocity costs is finite. Source: `Breakdown.Coercive.Internal.Absorb.debt_tsum_ne_top` (`Breakdown/Cert/CoerciveAbsorb.lean:586`).

**Theorem: Curl-gradient square bound.** The squared curl-gradient contraction is at most twice the squared norm of the second-derivative array. Source: `Breakdown.Coercive.Internal.Absorb.cnormSq_curlGradOfSecondDeriv_le` (`Breakdown/Cert/CoerciveAbsorb.lean:638`).

**Theorem: The period slab ignores null sets.** The product measure on one period and space is absolutely continuous with respect to full space-time volume. Source: `Breakdown.Coercive.Internal.Absorb.ac_slab` (`Breakdown/Cert/CoerciveAbsorb.lean:647`).

**Theorem: Squared complex norm is measurable.** Under the stated hypotheses, the squared complex norm is strongly measurable up to a null set. Source: `Breakdown.Coercive.Internal.Absorb.aesm_cnormSq` (`Breakdown/Cert/CoerciveAbsorb.lean:653`).

**Theorem: Squared complex norm is measurable.** Under the stated hypotheses, the squared complex norm is measurable up to a null set. Source: `Breakdown.Coercive.Internal.Absorb.aem_ofReal_cnormSq` (`Breakdown/Cert/CoerciveAbsorb.lean:658`).

**Theorem: Second-derivative mode is measurable.** Under the stated hypotheses, the second-derivative mode is strongly measurable up to a null set. Source: `Breakdown.Coercive.Internal.Absorb.aesm_modeSecondDeriv` (`Breakdown/Cert/CoerciveAbsorb.lean:664`).

**Theorem: Finite series on almost every slice.** Finiteness of the summed integrals implies that the pointwise nonnegative series is finite almost everywhere on the period slab. Source: `Breakdown.Coercive.Internal.Absorb.ae_of_tsum_lintegral` (`Breakdown/Cert/CoerciveAbsorb.lean:677`).

**Theorem: Almost-everywhere finite mode energies.** The sum of the velocity, gradient, and curl-gradient mode squares is finite for almost every time and spatial point. Source: `Breakdown.Coercive.Internal.Absorb.ae_amp_summable` (`Breakdown/Cert/CoerciveAbsorb.lean:688`).

**Theorem: Pointwise signed density comparison.** The source's positive and negative parts give the stated pointwise signed comparison after the harmonic costs have been absorbed. Source: `Breakdown.Coercive.Internal.Absorb.pointwise` (`Breakdown/Cert/CoerciveAbsorb.lean:748`).

**Theorem: Velocity amplitude is measurable.** Under the stated hypotheses, the velocity amplitude is measurable up to a null set. Source: `Breakdown.Coercive.Internal.Absorb.aem_velAmp'` (`Breakdown/Cert/CoerciveAbsorb.lean:775`).

**Theorem: Gradient amplitude is measurable.** Under the stated hypotheses, the gradient amplitude is measurable up to a null set. Source: `Breakdown.Coercive.Internal.Absorb.aem_gradAmp'` (`Breakdown/Cert/CoerciveAbsorb.lean:779`).

**Theorem: Vorticity amplitude is measurable.** Under the stated hypotheses, the vorticity amplitude is measurable up to a null set. Source: `Breakdown.Coercive.Internal.Absorb.aem_vortAmp'` (`Breakdown/Cert/CoerciveAbsorb.lean:784`).

**Theorem: Measurability of Hessian amplitudes.** Under the stated hypotheses, the second-derivative amplitude is measurable up to a null set. Source: `Breakdown.Coercive.Internal.Absorb.aem_secondDerivAmp'` (`Breakdown/Cert/CoerciveAbsorb.lean:792`).

**Theorem: Curl-gradient amplitude is measurable.** Under the stated hypotheses, the vorticity-gradient amplitude is measurable up to a null set. Source: `Breakdown.Coercive.Internal.Absorb.aem_vortGradAmp'` (`Breakdown/Cert/CoerciveAbsorb.lean:797`).

**Theorem: The background gradient is C¹.** The background spatial derivative is continuously differentiable as a joint space-time function. Source: `Breakdown.Coercive.Internal.Absorb.cont_gradField` (`Breakdown/Cert/CoerciveAbsorb.lean:805`).

**Theorem: The background Hessian is continuous.** The background second spatial derivative is jointly continuous in time and space. Source: `Breakdown.Coercive.Internal.Absorb.cont_secondDerivField` (`Breakdown/Cert/CoerciveAbsorb.lean:810`).

**Theorem: Velocity mode is continuous.** Under the stated hypotheses, the velocity mode is continuous. Source: `Breakdown.Coercive.Internal.Absorb.cont_modeVel_zero` (`Breakdown/Cert/CoerciveAbsorb.lean:816`).

**Theorem: The averaged field is measurable.** The time-angle mean field is measurable under the stated field regularity hypotheses. Source: `Breakdown.Coercive.Internal.Absorb.measurable_meanField` (`Breakdown/Cert/CoerciveAbsorb.lean:847`).

**Theorem: Absolute values preserve measurability.** The absolute value of the stated real measurable function is measurable up to a null set. Source: `Breakdown.Coercive.Internal.Absorb.abs_aem` (`Breakdown/Cert/CoerciveAbsorb.lean:853`).

**Theorem: Total mode remainder is measurable.** Under the stated hypotheses, the total mode remainder is measurable up to a null set. Source: `Breakdown.Coercive.Internal.Absorb.rest_aem` (`Breakdown/Cert/CoerciveAbsorb.lean:856`).

**Theorem: Positive mode contribution is measurable.** Under the stated hypotheses, the positive mode contribution is measurable up to a null set. Source: `Breakdown.Coercive.Internal.Absorb.pos_aem` (`Breakdown/Cert/CoerciveAbsorb.lean:917`).

**Theorem: Stretching form is measurable.** Under the stated hypotheses, the stretching form is measurable up to a null set. Source: `Breakdown.Coercive.Internal.Absorb.stretch_aem` (`Breakdown/Cert/CoerciveAbsorb.lean:929`).

**Theorem: Measurable parts of the signed bound.** The positive-side and negative-side sums in the density comparison are measurable up to null sets on the period slab. Source: `Breakdown.Coercive.Internal.Absorb.aemeasurable_parts` (`Breakdown/Cert/CoerciveAbsorb.lean:941`).

**Theorem: Absorb the mode interaction costs.** The supplied hypotheses establish conversion of a split remainder bound into the signed total mode-density inequality. Source: `Breakdown.Coercive.modeAbsorbStepHolds_of` (`Breakdown/Cert/CoerciveAbsorb.lean:1036`).

### Breakdown.Cert.CoerciveAssembly

The file assembles the ordinary mode-weight and piece-weight routes from named analytic specifications, showing how field existence, smooth approximation, density passage, and absorption yield the final multiplier-density interfaces.

**Paper context:** Appendix B, Proposition B.1: assembly of the two multiplier-density arguments used by the certificate.

**Theorem: A multiplier with a density bound.** The supplied hypotheses establish existence of a multiplier with the stated norm bound and signed mode-density inequality. Source: `Breakdown.Coercive.multiplierDensity_of_field` (`Breakdown/Cert/CoerciveAssembly.lean:13`).

**Theorem: A piece multiplier with a density bound.** The supplied hypotheses establish existence of a piece multiplier with the stated norm bound and signed piece-density inequality. Source: `Breakdown.Coercive.pieceMultiplierDensity_of_field` (`Breakdown/Cert/CoerciveAssembly.lean:21`).

**Theorem: Split the total mode density.** The mode density equals its base, curl-weight, and velocity-weight contributions. Source: `Breakdown.Coercive.modeDensity_eq_split` (`Breakdown/Cert/CoerciveAssembly.lean:29`).

**Theorem: Split the total piece density.** The piece density equals its base density plus all curl-piece and velocity-piece contributions. Source: `Breakdown.Coercive.pieceDensity_eq_split` (`Breakdown/Cert/CoerciveAssembly.lean:37`).

**Theorem: The weak mode-density bound.** The supplied hypotheses establish the split lower bound for the multiplier gap of a weak perturbation with its given multiplier. Source: `Breakdown.Coercive.modeDensityOfField_of_passage` (`Breakdown/Cert/CoerciveAssembly.lean:48`).

**Theorem: The weak piece-density bound.** The supplied hypotheses establish the split lower bound for the piece-multiplier gap of a weak perturbation with its given multiplier. Source: `Breakdown.Coercive.pieceDensityOfField_of_passage` (`Breakdown/Cert/CoerciveAssembly.lean:56`).

**Theorem: A multiplier with a density bound.** The supplied hypotheses establish existence of a multiplier with the stated norm bound and signed mode-density inequality. Source: `Breakdown.Coercive.multiplierDensityHolds_of_nodes` (`Breakdown/Cert/CoerciveAssembly.lean:64`).

**Theorem: A piece multiplier with a density bound.** The supplied hypotheses establish existence of a piece multiplier with the stated norm bound and signed piece-density inequality. Source: `Breakdown.Coercive.pieceMultiplierDensityHolds_of_nodes` (`Breakdown/Cert/CoerciveAssembly.lean:99`).

**Theorem: Angular frequency controls derivatives.** The supplied hypotheses establish the two inverse-radius lower bounds from angular frequencies at least two. Source: `Breakdown.Coercive.modeAzimuthalGainHolds_of_nodes` (`Breakdown/Cert/CoerciveAssembly.lean:134`).

**Theorem: Bound the mean stretching term.** The supplied hypotheses establish control of the averaged negative stretching form by the summed stretching charges. Source: `Breakdown.Coercive.stretchMeanBoundHolds_of_nodes` (`Breakdown/Cert/CoerciveAssembly.lean:140`).

**Theorem: Density gives the multiplier inequality.** The multiplier-density, angular-gain, and stretching interfaces imply the certificate's multiplier inequality with its explicit square-root constant. Source: `Breakdown.Coercive.multiplierInequality_of_densityHolds` (`Breakdown/Cert/CoerciveAssembly.lean:145`).

**Theorem: Piece density gives the multiplier bound.** The piece-density, angular-gain, and stretching interfaces imply the certificate's multiplier inequality with its explicit square-root constant. Source: `Breakdown.Coercive.multiplierInequality_of_pieceDensityHolds` (`Breakdown/Cert/CoerciveAssembly.lean:211`).

### Breakdown.Cert.CoerciveBase

The base energy density is expanded into positive energy terms and coefficient remainders; continuity, mode averaging, and period-integral identities prepare this algebra for integration.

**Paper context:** Appendix B, Proposition B.1: the base quadratic-density component of coercivity.

**Definition: Squared velocity mode.** Take the squared complex norm of the velocity mode. Source: `Breakdown.Coercive.BaseDensityInternal.velSq` (`Breakdown/Cert/CoerciveBase.lean:14`).

**Definition: Squared gradient mode.** Take the squared complex norm of the gradient mode. Source: `Breakdown.Coercive.BaseDensityInternal.gradSq` (`Breakdown/Cert/CoerciveBase.lean:17`).

**Definition: Squared vorticity mode.** Take the squared complex norm of the curl of the gradient mode. Source: `Breakdown.Coercive.BaseDensityInternal.vortSq` (`Breakdown/Cert/CoerciveBase.lean:20`).

**Definition: Squared second-derivative mode.** Take the squared complex norm of the second-derivative mode. Source: `Breakdown.Coercive.BaseDensityInternal.secondDerivModeSq` (`Breakdown/Cert/CoerciveBase.lean:23`).

**Definition: Squared vorticity-gradient mode.** Take the squared complex norm of the curl-gradient extracted from the second-derivative mode. Source: `Breakdown.Coercive.BaseDensityInternal.vortGradSq` (`Breakdown/Cert/CoerciveBase.lean:26`).

**Definition: Integrate and sum a mode density.** Sum the nonnegative mode-density integrals over space, one time period, and all integer frequency pairs. Source: `Breakdown.Coercive.BaseDensityInternal.modeSum` (`Breakdown/Cert/CoerciveBase.lean:29`).

**Definition: Vorticity energy minus weighted energy.** Subtract the weighted second-derivative and gradient energy from the vorticity-gradient energy plus one quarter of the vorticity energy. Source: `Breakdown.Coercive.BaseDensityInternal.baseMain` (`Breakdown/Cert/CoerciveBase.lean:32`).

**Definition: Weighted second-derivative defect.** Record the difference between the weighted second-derivative and curl-gradient squares, less the Hessian-of-weight correction. Source: `Breakdown.Coercive.BaseDensityInternal.secondDerivDefect` (`Breakdown/Cert/CoerciveBase.lean:35`).

**Definition: Weighted gradient defect.** Record the difference between the weighted gradient and curl squares, less the Hessian-of-weight correction. Source: `Breakdown.Coercive.BaseDensityInternal.gradDefect` (`Breakdown/Cert/CoerciveBase.lean:38`).

**Definition: The five base-density terms.** Expand the base density into its second-derivative, curl-gradient, curl, gradient, and velocity square terms. Source: `Breakdown.Coercive.BaseDensityInternal.expanded` (`Breakdown/Cert/CoerciveBase.lean:41`).

**Theorem: Squared complex norm is nonnegative.** The squared complex norm is nonnegative for the stated data. Source: `Breakdown.Coercive.BaseDensityInternal.cnormSq_nonneg` (`Breakdown/Cert/CoerciveBase.lean:48`).

**Theorem: The complex square sum is continuous.** The sum of the squared norms of a finite complex array depends continuously on the array. Source: `Breakdown.Coercive.BaseDensityInternal.continuous_cnormSq` (`Breakdown/Cert/CoerciveBase.lean:51`).

**Theorem: The curl contraction is continuous.** The complex curl contraction depends continuously on its gradient array. Source: `Breakdown.Coercive.BaseDensityInternal.continuous_curlOfGrad` (`Breakdown/Cert/CoerciveBase.lean:55`).

**Theorem: Continuity of curl-gradient contraction.** The curl-gradient contraction depends continuously on the complex second-derivative array. Source: `Breakdown.Coercive.BaseDensityInternal.continuous_curlGradOfSecondDeriv` (`Breakdown/Cert/CoerciveBase.lean:60`).

**Theorem: Evaluate the base density.** Evaluating the base density on the mode amplitudes gives its five-term square expansion. Source: `Breakdown.Coercive.BaseDensityInternal.modeValues_baseDensity` (`Breakdown/Cert/CoerciveBase.lean:66`).

**Theorem: The first rotated coordinate.** The first coordinate after axial rotation is cos(φ)y₀ − sin(φ)y₁. Source: `Breakdown.Coercive.BaseDensityInternal.axialRot_coord_zero` (`Breakdown/Cert/CoerciveBase.lean:73`).

**Theorem: The second rotated coordinate.** The second coordinate after axial rotation is sin(φ)y₀ + cos(φ)y₁. Source: `Breakdown.Coercive.BaseDensityInternal.axialRot_coord_one` (`Breakdown/Cert/CoerciveBase.lean:77`).

**Theorem: Rotation fixes the axial coordinate.** Axial rotation leaves the third coordinate unchanged. Source: `Breakdown.Coercive.BaseDensityInternal.axialRot_coord_two` (`Breakdown/Cert/CoerciveBase.lean:81`).

**Theorem: Axial rotation preserves length.** Axial rotation preserves the Euclidean norm. Source: `Breakdown.Coercive.BaseDensityInternal.norm_axialRot` (`Breakdown/Cert/CoerciveBase.lean:84`).

**Theorem: Axial rotation fixes zero.** Every axial rotation sends the zero vector to zero. Source: `Breakdown.Coercive.BaseDensityInternal.axialRot_zero_vec` (`Breakdown/Cert/CoerciveBase.lean:91`).

**Theorem: Axial rotation is continuous.** Under the stated hypotheses, the axial rotation is continuous. Source: `Breakdown.Coercive.BaseDensityInternal.continuous_axialRot_of` (`Breakdown/Cert/CoerciveBase.lean:94`).

**Theorem: The average of a zero component is zero.** A component that vanishes on every averaging parameter has zero Fourier mode average. Source: `Breakdown.Coercive.BaseDensityInternal.modeAverage_eq_zero` (`Breakdown/Cert/CoerciveBase.lean:99`).

**Theorem: A finite order lies below infinity.** A finite differentiability order plus one lies below the infinite order. Source: `Breakdown.Coercive.BaseDensityInternal.top_add_le` (`Breakdown/Cert/CoerciveBase.lean:103`).

**Theorem: Common support for field derivatives.** A compact periodic test field and its first two spatial derivatives vanish beyond one common radius. Source: `Breakdown.Coercive.BaseDensityInternal.modes_support_aux` (`Breakdown/Cert/CoerciveBase.lean:106`).

**Theorem: A common support radius for all modes.** All velocity, gradient, and second-derivative modes of a compact periodic test field vanish beyond one common radius. Source: `Breakdown.Coercive.BaseDensityInternal.modes_support` (`Breakdown/Cert/CoerciveBase.lean:122`).

**Theorem: Fourier mode average is continuous.** Under the stated hypotheses, the Fourier mode average is continuous. Source: `Breakdown.Coercive.BaseDensityInternal.continuous_modeAverage` (`Breakdown/Cert/CoerciveBase.lean:137`).

**Theorem: Continuity of field and derivatives.** A periodic test field, its gradient, and its second derivative are jointly continuous in time and space. Source: `Breakdown.Coercive.BaseDensityInternal.fields_continuous` (`Breakdown/Cert/CoerciveBase.lean:157`).

**Theorem: Continuity of the derivative modes.** The velocity, gradient, and second-derivative modes of a periodic test field are jointly continuous. Source: `Breakdown.Coercive.BaseDensityInternal.modes_continuous` (`Breakdown/Cert/CoerciveBase.lean:170`).

**Definition: The weight's Hessian quadratic form.** Pair the Hessian of the scalar weight with the real part of the complex vector outer product. Source: `Breakdown.Coercive.BaseDensityInternal.secondDerivQuad` (`Breakdown/Cert/CoerciveBase.lean:206`).

**Theorem: Norm square from coordinates.** The squared norm of a vector assembled from the coordinate basis equals the sum of its coordinate squares. Source: `Breakdown.Coercive.BaseDensityInternal.norm_coordVec` (`Breakdown/Cert/CoerciveBase.lean:210`).

**Theorem: Bound the weight's Hessian form.** The Hessian quadratic form is bounded above by the Hessian norm of the weight times the complex vector norm square. Source: `Breakdown.Coercive.BaseDensityInternal.secondDerivQuad_le` (`Breakdown/Cert/CoerciveBase.lean:214`).

**Theorem: Continuity of the five mode squares.** The velocity, gradient, curl, second-derivative, and curl-gradient mode squares are jointly continuous. Source: `Breakdown.Coercive.BaseDensityInternal.squares_continuous` (`Breakdown/Cert/CoerciveBase.lean:240`).

**Theorem: Common support of the five mode squares.** All five mode squares vanish outside one common spatial ball. Source: `Breakdown.Coercive.BaseDensityInternal.squares_support` (`Breakdown/Cert/CoerciveBase.lean:250`).

**Theorem: Function m is integrable.** Under the stated hypotheses, the function m is integrable. Source: `Breakdown.Coercive.BaseDensityInternal.integrable_of_vanish` (`Breakdown/Cert/CoerciveBase.lean:258`).

**Theorem: Move a signed bound to nonnegative terms.** An integral inequality with nonnegative positive and negative terms gives the corresponding inequality of nonnegative extended integrals. Source: `Breakdown.Coercive.BaseDensityInternal.ennreal_le_of_integral_le` (`Breakdown/Cert/CoerciveBase.lean:263`).

**Theorem: Interchange integration and mode sums.** The nonnegative period integral of the mode sum equals the sum of the mode integrals. Source: `Breakdown.Coercive.BaseDensityInternal.lintegral_tsum_swap` (`Breakdown/Cert/CoerciveBase.lean:279`).

**Theorem: Add the integrated mode sums.** Under the stated hypotheses, the integrated sum over modes commutes with addition. Source: `Breakdown.Coercive.BaseDensityInternal.modeSum_add` (`Breakdown/Cert/CoerciveBase.lean:292`).

**Theorem: Scale the integrated mode sum.** Under the stated hypotheses, the integrated sum over modes commutes with multiplication by a constant. Source: `Breakdown.Coercive.BaseDensityInternal.modeSum_const_mul` (`Breakdown/Cert/CoerciveBase.lean:311`).

**Theorem: Cancel finite signed energy terms.** Finite auxiliary terms can be removed from the extended-real inequality using their given real difference. Source: `Breakdown.Coercive.BaseDensityInternal.final_algebra` (`Breakdown/Cert/CoerciveBase.lean:325`).

**Definition: Positive part of the base energy.** Collect the vorticity energy and the contribution from the negative part of the coefficient c. Source: `Breakdown.Coercive.BaseDensityInternal.mainPos` (`Breakdown/Cert/CoerciveBase.lean:346`).

**Definition: Negative part of the base energy.** Multiply the weighted derivative energy by the positive part of c. Source: `Breakdown.Coercive.BaseDensityInternal.mainNeg` (`Breakdown/Cert/CoerciveBase.lean:350`).

**Theorem: Measurability of the five mode squares.** The velocity, gradient, curl, second-derivative, and curl-gradient mode squares are measurable. Source: `Breakdown.Coercive.BaseDensityInternal.squares_measurable` (`Breakdown/Cert/CoerciveBase.lean:353`).

**Theorem: The five mode squares are nonnegative.** Each of the velocity, gradient, curl, second-derivative, and curl-gradient mode squares is nonnegative. Source: `Breakdown.Coercive.BaseDensityInternal.squares_nonneg` (`Breakdown/Cert/CoerciveBase.lean:362`).

**Theorem: The weight Hessian norm is continuous.** For a twice continuously differentiable scalar weight, the norm of its second derivative is a continuous spatial function. Source: `Breakdown.Coercive.BaseDensityInternal.continuous_secondDerivNorm` (`Breakdown/Cert/CoerciveBase.lean:367`).

**Theorem: Integral is measurable.** Under the stated hypotheses, the integral is measurable. Source: `Breakdown.Coercive.BaseDensityInternal.measurable_inner` (`Breakdown/Cert/CoerciveBase.lean:371`).

**Theorem: Expanded base density is measurable.** Under the stated hypotheses, the expanded base density is measurable. Source: `Breakdown.Coercive.BaseDensityInternal.measurable_expanded` (`Breakdown/Cert/CoerciveBase.lean:375`).

**Theorem: Positive base energy is measurable.** Under the stated hypotheses, the positive base-energy contribution is measurable. Source: `Breakdown.Coercive.BaseDensityInternal.measurable_mainPos` (`Breakdown/Cert/CoerciveBase.lean:391`).

**Definition: Curl as a linear map.** Package the alternating contraction of a gradient matrix as a linear map. Source: `Breakdown.Coercive.BaseDensityInternal.curlLinear` (`Breakdown/Cert/CoerciveBase.lean:399`).

**Theorem: Read the linear curl map.** Applying the linear curl map returns the usual curl contraction of the gradient matrix. Source: `Breakdown.Coercive.BaseDensityInternal.curlLinear_apply` (`Breakdown/Cert/CoerciveBase.lean:413`).

**Theorem: Squared matrix norm is continuous.** Under the stated hypotheses, the squared matrix norm is continuous. Source: `Breakdown.Coercive.BaseDensityInternal.continuous_matSq` (`Breakdown/Cert/CoerciveBase.lean:415`).

**Theorem: Continuity of the energy integrands.** The curl-gradient, curl, second-derivative trace, and gradient energy integrands are jointly continuous. Source: `Breakdown.Coercive.BaseDensityInternal.energy_fields_continuous` (`Breakdown/Cert/CoerciveBase.lean:419`).

**Theorem: Common support of energy integrands.** The curl-gradient, curl, trace, and gradient energy integrands vanish outside one common spatial ball. Source: `Breakdown.Coercive.BaseDensityInternal.energy_fields_support` (`Breakdown/Cert/CoerciveBase.lean:439`).

**Theorem: One bound for all slice integrals.** A continuous integrand with common compact spatial support has a finite uniform bound on its spatial integrals over one time period. Source: `Breakdown.Coercive.BaseDensityInternal.lintegral_slice_le` (`Breakdown/Cert/CoerciveBase.lean:457`).

**Theorem: Period integral is finite.** Under the stated hypotheses, the nonnegative period integral is finite. Source: `Breakdown.Coercive.BaseDensityInternal.periodLIntegral_lt_top` (`Breakdown/Cert/CoerciveBase.lean:473`).

**Theorem: Period integral preserves addition.** Under the stated hypotheses, the nonnegative period integral commutes with addition. Source: `Breakdown.Coercive.BaseDensityInternal.periodLIntegral_add` (`Breakdown/Cert/CoerciveBase.lean:482`).

**Theorem: Read the nonnegative period integral.** For the stated nonnegative compactly supported integrand, the ordinary period integral equals the real value of its nonnegative extended integral. Source: `Breakdown.Coercive.BaseDensityInternal.integral_eq_periodLIntegral` (`Breakdown/Cert/CoerciveBase.lean:496`).

**Theorem: Finiteness of the derivative energies.** The curl-gradient, curl, trace, and weighted-gradient energies are finite under the stated weight and test-field hypotheses. Source: `Breakdown.Coercive.BaseDensityInternal.fields_finite` (`Breakdown/Cert/CoerciveBase.lean:508`).

**Theorem: Split the vorticity energy.** The vorticity energy equals the curl-gradient energy plus one quarter of the curl energy. Source: `Breakdown.Coercive.BaseDensityInternal.vorticityEnergy_eq` (`Breakdown/Cert/CoerciveBase.lean:526`).

**Theorem: Split the weighted derivative energy.** The weighted energy equals the trace energy plus the weighted-gradient energy. Source: `Breakdown.Coercive.BaseDensityInternal.weightedEnergy_eq` (`Breakdown/Cert/CoerciveBase.lean:554`).

**Theorem: Coordinates determine a vector.** Two three-dimensional vectors are equal when their three coordinates agree. Source: `Breakdown.Coercive.BaseDensityInternal.space_eq_of_coords` (`Breakdown/Cert/CoerciveBase.lean:567`).

**Theorem: Rotation commutes with scaling.** Axial rotation commutes with real scalar multiplication. Source: `Breakdown.Coercive.BaseDensityInternal.axialRot_smul_vec` (`Breakdown/Cert/CoerciveBase.lean:574`).

**Theorem: Fourier mode average preserves scaling.** Under the stated hypotheses, the Fourier mode average commutes with multiplication by a constant. Source: `Breakdown.Coercive.BaseDensityInternal.modeAverage_const_mul` (`Breakdown/Cert/CoerciveBase.lean:580`).

**Theorem: Parseval for weighted gradient energy.** The sum of the weighted gradient-mode energies equals the physical weighted-gradient energy under the mode square-sum and axisymmetric-weight hypotheses. Source: `Breakdown.Coercive.BaseDensityInternal.squareSum_weighted_grad` (`Breakdown/Cert/CoerciveBase.lean:593`).

**Theorem: Average a finite linear combination.** The Fourier mode average of a finite linear combination equals the same combination of the mode averages. Source: `Breakdown.Coercive.BaseDensityInternal.modeAverage_finset_sum` (`Breakdown/Cert/CoerciveBase.lean:630`).

**Theorem: Rotate the first basis vector.** Axial rotation sends the first basis vector to cos(φ)e₀ + sin(φ)e₁. Source: `Breakdown.Coercive.BaseDensityInternal.axialRot_unit_zero` (`Breakdown/Cert/CoerciveBase.lean:662`).

**Theorem: Rotate the second basis vector.** Axial rotation sends the second basis vector to −sin(φ)e₀ + cos(φ)e₁. Source: `Breakdown.Coercive.BaseDensityInternal.axialRot_unit_one` (`Breakdown/Cert/CoerciveBase.lean:666`).

**Theorem: Rotation fixes the axial basis vector.** Axial rotation fixes the third coordinate basis vector. Source: `Breakdown.Coercive.BaseDensityInternal.axialRot_unit_two` (`Breakdown/Cert/CoerciveBase.lean:670`).

**Theorem: A coordinate formula for curl.** A curl coordinate equals the alternating contraction of the gradient-matrix coordinates. Source: `Breakdown.Coercive.BaseDensityInternal.curlVec_coord` (`Breakdown/Cert/CoerciveBase.lean:673`).

**Theorem: Curl rotates with the coordinate frame.** The three coordinate identities identify the curl of the rotated gradient with the rotated curl. Source: `Breakdown.Coercive.BaseDensityInternal.curl_covariant_aux` (`Breakdown/Cert/CoerciveBase.lean:678`).

**Theorem: Curl rotates with the coordinate frame.** The alternating contraction of a rotated gradient equals the corresponding coordinate of the rotated curl. Source: `Breakdown.Coercive.BaseDensityInternal.curl_covariant` (`Breakdown/Cert/CoerciveBase.lean:693`).

**Theorem: Parseval for vorticity energy.** The sum of the vorticity-mode energies equals the physical curl energy over one period. Source: `Breakdown.Coercive.BaseDensityInternal.squareSum_vort` (`Breakdown/Cert/CoerciveBase.lean:702`).

**Theorem: Differentiate the curl field.** The directional derivative of the curl equals the curl contraction of the second derivative in that direction. Source: `Breakdown.Coercive.BaseDensityInternal.fderiv_curl_apply` (`Breakdown/Cert/CoerciveBase.lean:745`).

**Theorem: Parseval for curl-gradient energy.** The sum of the curl-gradient mode energies equals the physical curl-gradient energy over one period. Source: `Breakdown.Coercive.BaseDensityInternal.squareSum_vortGrad` (`Breakdown/Cert/CoerciveBase.lean:755`).

**Theorem: Smooth slices have symmetric derivatives.** A periodic test field has smooth spatial slices and symmetric second spatial derivatives. Source: `Breakdown.Coercive.BaseDensityInternal.slice_smooth` (`Breakdown/Cert/CoerciveBase.lean:809`).

**Theorem: Differentiate a gradient column.** Differentiating a fixed gradient column amounts to evaluating the second derivative in that column direction. Source: `Breakdown.Coercive.BaseDensityInternal.column_fderiv` (`Breakdown/Cert/CoerciveBase.lean:817`).

**Theorem: The derivative of divergence vanishes.** Differentiating the divergence-free condition gives zero for the corresponding contraction of the second derivative. Source: `Breakdown.Coercive.BaseDensityInternal.divergence_deriv_zero` (`Breakdown/Cert/CoerciveBase.lean:823`).

**Theorem: Full Hessian and trace energies agree.** For the stated divergence-free test slice, the integrated full second-derivative square equals the integrated squared trace. Source: `Breakdown.Coercive.BaseDensityInternal.slice_secondDerivSq_eq` (`Breakdown/Cert/CoerciveBase.lean:841`).

**Theorem: Parseval for second-derivative energy.** The sum of second-derivative mode energies equals the physical squared-trace energy under the square-sum and div-curl interfaces. Source: `Breakdown.Coercive.BaseDensityInternal.squareSum_secondDeriv` (`Breakdown/Cert/CoerciveBase.lean:948`).

**Theorem: Integrability of base-density components.** At each mode and time, the base energy, derivative defects, and positive and negative energy parts are integrable in space. Source: `Breakdown.Coercive.BaseDensityInternal.per_mode_integrable` (`Breakdown/Cert/CoerciveBase.lean:972`).

**Theorem: Integrability of weighted defects.** The weighted square differences and Hessian-of-weight corrections in both derivative defects are integrable. Source: `Breakdown.Coercive.BaseDensityInternal.defect_parts_integrable` (`Breakdown/Cert/CoerciveBase.lean:1028`).

**Theorem: Integrals preserve pointwise order.** An almost-everywhere comparison of integrable functions gives the corresponding comparison of their integrals. Source: `Breakdown.Coercive.BaseDensityInternal.integral_le_of_pointwise` (`Breakdown/Cert/CoerciveBase.lean:1055`).

**Theorem: Sum the positive base-energy terms.** The summed positive mode contribution equals the physical curl energies plus the weighted derivative energy multiplied by the negative part of c. Source: `Breakdown.Coercive.BaseDensityInternal.modeSum_mainPos` (`Breakdown/Cert/CoerciveBase.lean:1062`).

**Theorem: Sum the negative base-energy terms.** The summed negative mode contribution equals the weighted derivative energy multiplied by the positive part of c. Source: `Breakdown.Coercive.BaseDensityInternal.modeSum_mainNeg` (`Breakdown/Cert/CoerciveBase.lean:1093`).

### Breakdown.Cert.CoerciveBordered

The abstract periodic graph equation is translated into the weak physical perturbation equation and its actuator terms, allowing the coercive estimate to force a bordered-kernel vector to vanish.

**Paper context:** §7 certificate construction: applying the Appendix B coercive estimate to the bordered operator's kernel.

**Theorem: Shift the window of a periodic integral.** A nonnegative one-periodic function has the same integral over every translated unit interval. Source: `Breakdown.Cert.Internal.CoerciveBordered.lintegral_Ioc_periodic` (`Breakdown/Cert/CoerciveBordered.lean:14`).

**Theorem: Period L² gives local integrability.** A periodic field with finite squared energy over a period is locally integrable on space-time. Source: `Breakdown.Cert.Internal.CoerciveBordered.locallyIntegrable_of_periodic_sq` (`Breakdown/Cert/CoerciveBordered.lean:21`).

**Theorem: Local mass from the energy-space norm.** The velocity's L¹ mass on a unit ball is bounded by its energy-space norm times the stated L⁶ embedding and volume factor. Source: `Breakdown.Cert.Internal.CoerciveBordered.lintegral_ball_velocity_le` (`Breakdown/Cert/CoerciveBordered.lean:57`).

**Theorem: Local mass from the graph norm.** The physical velocity's L¹ mass on a unit ball is bounded by the graph norm times the projection, embedding, and volume factors. Source: `Breakdown.Cert.Internal.CoerciveBordered.ball_bound` (`Breakdown/Cert/CoerciveBordered.lean:74`).

**Theorem: Velocity norm is integrable.** Under the stated hypotheses, the velocity norm is locally integrable. Source: `Breakdown.Cert.Internal.CoerciveBordered.locallyIntegrable_norm_velocity` (`Breakdown/Cert/CoerciveBordered.lean:91`).

**Theorem: Function f is integrable.** Under the stated hypotheses, the function f is integrable. Source: `Breakdown.Cert.Internal.CoerciveBordered.integrable_of_le` (`Breakdown/Cert/CoerciveBordered.lean:129`).

**Theorem: Period integration preserves order.** An almost-everywhere pointwise bound implies the same bound between the nonnegative period integrals. Source: `Breakdown.Cert.Internal.CoerciveBordered.periodLIntegral_mono` (`Breakdown/Cert/CoerciveBordered.lean:136`).

**Theorem: Periodic test fields are continuous.** The stated periodic test field is jointly continuous in time and space. Source: `Breakdown.Cert.Internal.CoerciveBordered.continuous_test` (`Breakdown/Cert/CoerciveBordered.lean:140`).

**Theorem: Spatial derivative is continuous.** Under the stated hypotheses, the spatial derivative is continuous. Source: `Breakdown.Cert.Internal.CoerciveBordered.continuous_fderiv_test` (`Breakdown/Cert/CoerciveBordered.lean:143`).

**Theorem: Spatial derivative has compact support.** Under the stated hypotheses, the spatial derivative has compact support. Source: `Breakdown.Cert.Internal.CoerciveBordered.hasCompactSupport_fderiv_test` (`Breakdown/Cert/CoerciveBordered.lean:150`).

**Theorem: Continuous test-field partials.** Under the stated hypotheses, the test-field derivative in a coordinate direction is continuous. Source: `Breakdown.Cert.Internal.CoerciveBordered.continuous_fderiv_test_apply` (`Breakdown/Cert/CoerciveBordered.lean:164`).

**Theorem: Test partials have compact support.** Under the stated hypotheses, the test-field derivative in a coordinate direction has compact support. Source: `Breakdown.Cert.Internal.CoerciveBordered.hasCompactSupport_fderiv_test_apply` (`Breakdown/Cert/CoerciveBordered.lean:168`).

**Theorem: Bound a linear map by its columns.** The norm of a linear map applied to a vector is at most the vector norm times the sum of the column norms. Source: `Breakdown.Cert.Internal.CoerciveBordered.norm_apply_le_sum` (`Breakdown/Cert/CoerciveBordered.lean:173`).

**Theorem: Field pairing is integrable.** Under the stated hypotheses, the field pairing is integrable. Source: `Breakdown.Cert.Internal.CoerciveBordered.integrable_inner_of_periodic` (`Breakdown/Cert/CoerciveBordered.lean:189`).

**Theorem: Measurability of weak-gradient columns.** Under the stated hypotheses, the selected weak-gradient column is strongly measurable up to a null set. Source: `Breakdown.Cert.Internal.CoerciveBordered.column_measurable` (`Breakdown/Cert/CoerciveBordered.lean:200`).

**Theorem: Selected weak-gradient column formula.** Under the stated hypotheses, the selected weak-gradient column has time period one. Source: `Breakdown.Cert.Internal.CoerciveBordered.column_periodic` (`Breakdown/Cert/CoerciveBordered.lean:205`).

**Theorem: Finite energy of gradient columns.** Under the stated hypotheses, the period energy of the selected weak-gradient column is finite. Source: `Breakdown.Cert.Internal.CoerciveBordered.column_finite` (`Breakdown/Cert/CoerciveBordered.lean:208`).

**Theorem: Gradient columns are locally integrable.** Under the stated hypotheses, the norm of the selected weak-gradient column is locally integrable. Source: `Breakdown.Cert.Internal.CoerciveBordered.column_locallyIntegrable` (`Breakdown/Cert/CoerciveBordered.lean:215`).

**Theorem: Integrability of the gradient pairing.** Under the stated hypotheses, the matrix pairing of weak and test gradients is integrable. Source: `Breakdown.Cert.Internal.CoerciveBordered.integrable_matNorm` (`Breakdown/Cert/CoerciveBordered.lean:222`).

**Theorem: The profile is jointly continuous.** The profile at the selected parameter is jointly continuous in time and space. Source: `Breakdown.Cert.Internal.CoerciveBordered.continuous_profile` (`Breakdown/Cert/CoerciveBordered.lean:232`).

**Theorem: Spatial derivative is continuous.** Under the stated hypotheses, the spatial derivative is continuous. Source: `Breakdown.Cert.Internal.CoerciveBordered.continuous_fderiv_profile` (`Breakdown/Cert/CoerciveBordered.lean:236`).

**Theorem: The tested convection is integrable.** Under the stated hypotheses, the convection pairing with the test field is integrable. Source: `Breakdown.Cert.Internal.CoerciveBordered.integrable_convection` (`Breakdown/Cert/CoerciveBordered.lean:242`).

**Theorem: The tested actuator sum is integrable.** Under the stated hypotheses, the actuator combination paired with the test field is integrable. Source: `Breakdown.Cert.Internal.CoerciveBordered.integrable_actuator` (`Breakdown/Cert/CoerciveBordered.lean:284`).

**Theorem: The field equation in the bordered map.** The first component of the bordered map is the original field plus linear convection and the actuator combination. Source: `Breakdown.Cert.Internal.CoerciveBordered.bordered_fst` (`Breakdown/Cert/CoerciveBordered.lean:300`).

**Theorem: Combine the source pairings.** The separate source pairings add to the pairing against the sum of the sources, with the scalar term unchanged. Source: `Breakdown.Cert.Internal.CoerciveBordered.integrand_eq` (`Breakdown/Cert/CoerciveBordered.lean:305`).

**Theorem: Recover the weak right-side equation.** The operator and physical-representation hypotheses identify the supplied field as the weak equation's right side. Source: `Breakdown.Cert.Internal.CoerciveBordered.isRightSide_of` (`Breakdown/Cert/CoerciveBordered.lean:310`).

**Theorem: Bound the correction and multiplier.** The combined correction size is bounded by A plus c times the finite-dimensional data norm under the stated energy estimates. Source: `Breakdown.Cert.Internal.CoerciveBordered.size_bound_of` (`Breakdown/Cert/CoerciveBordered.lean:355`).

**Theorem: Coercivity controls the bordered solve.** The physical coercivity, free-inverse, and representation interfaces establish the bordered coercive estimate. Source: `Breakdown.Cert.coerciveBorderedHolds_of` (`Breakdown/Cert/CoerciveBordered.lean:366`).

### Breakdown.Cert.CoerciveCurlEnergy

Coordinate curl identities identify gradient energy with curl energy under the stated solenoidal and integrability assumptions.

**Paper context:** Appendix B, Proposition B.1: curl-versus-gradient energy identities in the multiplier estimate.

**Definition: A coordinate cross-product map.** Contract one coordinate direction with the alternating symbol to obtain a continuous linear cross-product map. Source: `Breakdown.Coercive.Internal.CurlEnergy.crossMap` (`Breakdown/Cert/CoerciveCurlEnergy.lean:21`).

**Theorem: Read a coordinate cross-product map.** The continuous cross-product map has the displayed alternating-symbol coordinate formula. Source: `Breakdown.Coercive.Internal.CurlEnergy.crossMap_apply` (`Breakdown/Cert/CoerciveCurlEnergy.lean:25`).

**Theorem: Build curl from coordinate derivatives.** The curl vector is the sum of coordinate cross-product maps applied to the columns of the gradient. Source: `Breakdown.Coercive.Internal.CurlEnergy.curlVec_eq_sum` (`Breakdown/Cert/CoerciveCurlEnergy.lean:29`).

**Theorem: Curl vector is continuous.** Under the stated hypotheses, the curl vector is continuous. Source: `Breakdown.Coercive.Internal.CurlEnergy.continuous_curlVec` (`Breakdown/Cert/CoerciveCurlEnergy.lean:34`).

**Definition: Curl on the Fourier energy space.** Sum the coordinate cross-product maps applied to the spatial derivative operators. Source: `Breakdown.Coercive.Internal.CurlEnergy.curlX` (`Breakdown/Cert/CoerciveCurlEnergy.lean:39`).

**Theorem: Physical representative of Fourier curl.** The Fourier-space curl agrees almost everywhere with the sum of coordinate cross products of its physical derivative representatives. Source: `Breakdown.Coercive.Internal.CurlEnergy.curlX_ae` (`Breakdown/Cert/CoerciveCurlEnergy.lean:42`).

**Theorem: The L² norm as an integral.** The squared L² norm equals the ordinary integral of the squared pointwise norm. Source: `Breakdown.Coercive.Internal.CurlEnergy.sq_norm_eq_integral` (`Breakdown/Cert/CoerciveCurlEnergy.lean:55`).

**Theorem: The L² norm as a nonnegative integral.** The squared L² norm, converted to a nonnegative extended real, equals the nonnegative integral of the squared pointwise norm. Source: `Breakdown.Coercive.Internal.CurlEnergy.sq_norm_eq_lintegral` (`Breakdown/Cert/CoerciveCurlEnergy.lean:61`).

**Theorem: Curl and gradient energy for a test.** For an embedded solenoidal test field, the squared curl norm equals the sum of the squared derivative norms. Source: `Breakdown.Coercive.Internal.CurlEnergy.sq_norm_curlX_embed` (`Breakdown/Cert/CoerciveCurlEnergy.lean:66`).

**Theorem: Curl and gradient energy agree.** For every Fourier energy-space element, the squared curl norm equals the sum of the squared derivative norms. Source: `Breakdown.Coercive.Internal.CurlEnergy.sq_norm_curlX` (`Breakdown/Cert/CoerciveCurlEnergy.lean:96`).

**Theorem: Curl commutes with frame rotation.** The alternating contraction of the conjugated gradient equals the rotated curl coordinate. Source: `Breakdown.Coercive.Internal.CurlEnergy.curlVec_axialRot` (`Breakdown/Cert/CoerciveCurlEnergy.lean:108`).

**Theorem: Curl commutes with mode extraction.** Taking the curl of a gradient mode gives the velocity mode of the physical curl at the stated point. Source: `Breakdown.Coercive.Internal.CurlEnergy.curlOfGrad_modeGrad_eq` (`Breakdown/Cert/CoerciveCurlEnergy.lean:118`).

**Theorem: Integrated curl and gradient squares.** Under the weak-gradient and solenoidal hypotheses, the curl and gradient squares have the same spatial integral. Source: `Breakdown.Coercive.lintegral_curlVec_sq_eq_matSq` (`Breakdown/Cert/CoerciveCurlEnergy.lean:151`).

**Theorem: Period curl and gradient energies.** Under the perturbation hypotheses, the curl and gradient squares have the same integral over one period. Source: `Breakdown.Coercive.periodLIntegral_curlVec_sq_eq` (`Breakdown/Cert/CoerciveCurlEnergy.lean:195`).

**Theorem: Modes preserve curl almost everywhere.** The curl of the gradient mode equals the mode of the physical curl almost everywhere in space-time. Source: `Breakdown.Coercive.ae_curlOfGrad_modeGrad` (`Breakdown/Cert/CoerciveCurlEnergy.lean:205`).

### Breakdown.Cert.CoerciveCurlWeight

Weighted curl testing is reduced to coordinate integration by parts and the decay and compact-support conditions that justify those integrals.

**Paper context:** Appendix B, Proposition B.1: the weighted curl contribution to the coercive multiplier.

**Definition: A coordinate projection.** Read one coordinate as a continuous linear functional on physical space. Source: `Breakdown.Coercive.CurlWeight.Internal.coordMap` (`Breakdown/Cert/CoerciveCurlWeight.lean:14`).

**Theorem: Read a coordinate projection.** The coordinate projection returns the selected vector coordinate. Source: `Breakdown.Coercive.CurlWeight.Internal.coordMap_apply` (`Breakdown/Cert/CoerciveCurlWeight.lean:16`).

**Theorem: Read a coordinate-basis expansion.** The k-th coordinate of the sum of cᵢeᵢ equals cₖ. Source: `Breakdown.Coercive.CurlWeight.Internal.coord_sum_smul` (`Breakdown/Cert/CoerciveCurlWeight.lean:18`).

**Theorem: Expand the curl square.** The curl norm square equals the matrix norm square minus the transposed-coordinate contraction. Source: `Breakdown.Coercive.CurlWeight.Internal.curl_norm_sq` (`Breakdown/Cert/CoerciveCurlWeight.lean:22`).

**Theorem: Function g has compact support.** Under the stated hypotheses, the function g has compact support. Source: `Breakdown.Coercive.CurlWeight.Internal.hasCompactSupport_of_vanish` (`Breakdown/Cert/CoerciveCurlWeight.lean:30`).

**Theorem: Derivative outside the support.** The derivative of a function vanishes at a point outside its topological support. Source: `Breakdown.Coercive.CurlWeight.Internal.fderiv_eq_zero_of_not_mem` (`Breakdown/Cert/CoerciveCurlWeight.lean:36`).

**Theorem: A compact derivative integrates to zero.** The directional derivative of the stated compactly supported smooth function is integrable and has integral zero. Source: `Breakdown.Coercive.CurlWeight.Internal.integral_fderiv_eq_zero` (`Breakdown/Cert/CoerciveCurlWeight.lean:40`).

**Definition: Flux for weighted div-curl identity.** Form the coordinate flux whose divergence supplies the weighted div-curl integration by parts. Source: `Breakdown.Coercive.CurlWeight.Internal.fluxField` (`Breakdown/Cert/CoerciveCurlWeight.lean:56`).

**Theorem: The weighted div-curl identity.** The supplied hypotheses establish the weighted curl-gradient identity with the Hessian-of-weight correction for compactly supported divergence-free fields. Source: `Breakdown.Coercive.curlWeightIdentityHolds_proof` (`Breakdown/Cert/CoerciveCurlWeight.lean:64`).

### Breakdown.Cert.CoerciveDensityPassage

The ordinary mode-weight estimate passes from smooth approximations to a weak perturbation by proving convergence of multipliers, sources, energies, and pairings and controlling both signed density sides.

**Paper context:** Appendix B, Proposition B.1: weak-limit passage for ordinary mode weights.

**Theorem: Frequency energies pass to the limit.** The frequency-seminorm square of the approximation error tends to zero, and the approximating frequency energies converge to the weak-field frequency energy. Source: `Breakdown.Coercive.Internal.DensityPassage.difference_frequency_converges` (`Breakdown/Cert/CoerciveDensityPassage.lean:51`).

**Theorem: A multiplier discrepancy tests to zero.** The difference between the approximating multiplier, limiting multiplier, and multiplier of the difference pairs to zero with every stated solenoidal test. Source: `Breakdown.Coercive.Internal.DensityPassage.multiplier_difference_test` (`Breakdown/Cert/CoerciveDensityPassage.lean:62`).

**Theorem: A multiplier discrepancy is orthogonal.** The multiplier discrepancy pairs to zero with both gradient tests and solenoidal tests. Source: `Breakdown.Coercive.Internal.DensityPassage.multiplier_difference_orthogonal` (`Breakdown/Cert/CoerciveDensityPassage.lean:72`).

**Theorem: Linearity of the multiplier in the limit.** The approximating multiplier minus the limiting multiplier equals the multiplier of the difference almost everywhere. Source: `Breakdown.Coercive.Internal.DensityPassage.multiplier_difference_ae` (`Breakdown/Cert/CoerciveDensityPassage.lean:106`).

**Theorem: Multipliers converge in period L².** The squared period L² distance from each approximating multiplier to the limiting multiplier tends to zero. Source: `Breakdown.Coercive.Internal.DensityPassage.field_converges` (`Breakdown/Cert/CoerciveDensityPassage.lean:133`).

**Theorem: The smooth source has finite L² norm.** The smooth equation source plus the actuator combination is strongly measurable up to a null set and has finite period L² norm. Source: `Breakdown.Coercive.Internal.DensityPassage.smooth_right_square_integrable` (`Breakdown/Cert/CoerciveDensityPassage.lean:187`).

**Theorem: The limiting source has finite L² norm.** The weak equation's limiting source is strongly measurable up to a null set and has finite period L² norm. Source: `Breakdown.Coercive.Internal.DensityPassage.right_model_square_integrable` (`Breakdown/Cert/CoerciveDensityPassage.lean:193`).

**Theorem: Equation sources converge in period L².** The squared period L² distance between the smooth source with actuators and the explicit limiting source tends to zero. Source: `Breakdown.Coercive.Internal.DensityPassage.smooth_right_converges` (`Breakdown/Cert/CoerciveDensityPassage.lean:198`).

**Theorem: Replace the source in a multiplier test.** The given right side and its explicit limiting-source formula have the same pairing with the multiplier. Source: `Breakdown.Coercive.Internal.DensityPassage.pairing_right_model` (`Breakdown/Cert/CoerciveDensityPassage.lean:204`).

**Theorem: Source-multiplier pairings converge.** The smooth source-multiplier pairings converge to the pairing of the limiting source and multiplier. Source: `Breakdown.Coercive.Internal.DensityPassage.right_pairing_converges` (`Breakdown/Cert/CoerciveDensityPassage.lean:209`).

**Theorem: Actuator pairings converge.** The pairing of each fixed actuator with the approximating multipliers converges to its pairing with the limiting multiplier. Source: `Breakdown.Coercive.Internal.DensityPassage.action_pairing_converges` (`Breakdown/Cert/CoerciveDensityPassage.lean:229`).

**Theorem: Weighted energies converge.** The weighted energies of the approximating gradients and Hessians converge to the weighted energy of the weak derivative fields. Source: `Breakdown.Coercive.Internal.DensityPassage.energy_converges` (`Breakdown/Cert/CoerciveDensityPassage.lean:236`).

**Theorem: Frequency-seminorm energies converge.** The real values of the approximating squared frequency seminorms converge to the corresponding weak-field value. Source: `Breakdown.Coercive.Internal.DensityPassage.frequency_converges` (`Breakdown/Cert/CoerciveDensityPassage.lean:246`).

**Theorem: Multiplier gaps converge.** The multiplier gaps of the smooth approximations, their sources, and their multipliers converge to the weak-field multiplier gap. Source: `Breakdown.Coercive.Internal.DensityPassage.gap_converges` (`Breakdown/Cert/CoerciveDensityPassage.lean:254`).

**Theorem: The mode remainder converges in L¹.** The remainder differences are measurable, the limiting absolute remainder is integrable, and the total L¹ remainder error tends to zero. Source: `Breakdown.Coercive.Internal.DensityPassage.rest_abs_converges` (`Breakdown/Cert/CoerciveDensityPassage.lean:276`).

**Theorem: Convergence of the negative remainder.** The integrated negative remainder is finite and the approximating negative remainder integrals converge to it. Source: `Breakdown.Coercive.Internal.DensityPassage.rest_negative_converge` (`Breakdown/Cert/CoerciveDensityPassage.lean:287`).

**Theorem: Stretching converges in L¹.** The limiting stretching form is integrable and the period integral of the absolute stretching error tends to zero. Source: `Breakdown.Coercive.Internal.DensityPassage.stretch_l1_converges` (`Breakdown/Cert/CoerciveDensityPassage.lean:298`).

**Theorem: Convergence of the negative density side.** The integrated negative side of the split density is finite and its smooth approximations converge to it. Source: `Breakdown.Coercive.Internal.DensityPassage.negative_parts_converge` (`Breakdown/Cert/CoerciveDensityPassage.lean:305`).

**Theorem: Measurable positive density side.** The positive split density is measurable on almost every spatial slice and its spatial integral is measurable in time. Source: `Breakdown.Coercive.Internal.DensityPassage.left_densities_measurable` (`Breakdown/Cert/CoerciveDensityPassage.lean:326`).

**Theorem: Choose one subsequence for all modes.** There is a strictly increasing subsequence along which every positive mode term, every remainder mode, and the stretching form converge almost everywhere. Source: `Breakdown.Coercive.Internal.DensityPassage.modes_converge_ae` (`Breakdown/Cert/CoerciveDensityPassage.lean:336`).

**Theorem: Lower semicontinuity of positive density.** Along a strictly increasing subsequence, the weak positive density is at most the lower limit of its smooth approximations almost everywhere. Source: `Breakdown.Coercive.Internal.DensityPassage.left_density_liminf` (`Breakdown/Cert/CoerciveDensityPassage.lean:347`).

**Theorem: Pass mode density to weak fields.** The supplied hypotheses establish transfer of the split mode-density inequality along a smooth approximation to the weak perturbation. Source: `Breakdown.Coercive.modeDensityPassageHolds_of` (`Breakdown/Cert/CoerciveDensityPassage.lean:374`).

### Breakdown.Cert.CoerciveDensityPassageCutoff

A smooth time cutoff converts periodwise weak testing into compact time-space testing, identifying the explicit limiting equation source with the source.

**Paper context:** Appendix B, Proposition B.1: time localization in the weak density passage.

**Definition: A smooth cutoff for one period.** Build a smooth time cutoff from translated transition functions to localise periodic testing. Source: `Breakdown.Coercive.Internal.DensityPassage.timeCutoff` (`Breakdown/Cert/CoerciveDensityPassageCutoff.lean:16`).

**Theorem: Smooth period cutoff is smooth.** Under the stated hypotheses, the smooth period cutoff is smooth. Source: `Breakdown.Coercive.Internal.DensityPassage.contDiff_timeCutoff` (`Breakdown/Cert/CoerciveDensityPassageCutoff.lean:18`).

**Theorem: The time cutoff vanishes off its window.** The time cutoff vanishes outside the interval specified in the hypothesis. Source: `Breakdown.Coercive.Internal.DensityPassage.timeCutoff_eq_zero` (`Breakdown/Cert/CoerciveDensityPassageCutoff.lean:23`).

**Theorem: Two shifted cutoffs sum to one.** The period cutoff and its unit backward shift sum to one on the stated interval. Source: `Breakdown.Coercive.Internal.DensityPassage.timeCutoff_add` (`Breakdown/Cert/CoerciveDensityPassageCutoff.lean:30`).

**Theorem: Turn a periodic test into a local test.** Multiplying a periodic solenoidal test by the time cutoff gives a compact space-time solenoidal test. Source: `Breakdown.Coercive.Internal.DensityPassage.cutoff_isSpaceTimeTestField` (`Breakdown/Cert/CoerciveDensityPassageCutoff.lean:37`).

**Theorem: Weak integration by parts for the trace.** The gradient pairing and trace pairing are integrable and differ by the sign prescribed by weak integration by parts. Source: `Breakdown.Coercive.Internal.DensityPassage.matInner_integral_eq` (`Breakdown/Cert/CoerciveDensityPassageCutoff.lean:56`).

**Theorem: A cutoff recovers the period pairing.** The full-time pairing against the cutoff test equals the original pairing over one period. Source: `Breakdown.Coercive.Internal.DensityPassage.integral_cutoff_eq` (`Breakdown/Cert/CoerciveDensityPassageCutoff.lean:99`).

**Theorem: Limiting equation source formula.** Under the stated hypotheses, the limiting equation source has time period one. Source: `Breakdown.Coercive.Internal.DensityPassage.rightSideLimit_periodic` (`Breakdown/Cert/CoerciveDensityPassageCutoff.lean:141`).

**Theorem: The explicit source has the same tests.** The difference between the right side and its explicit limiting formula is integrable against the test and has zero pairing. Source: `Breakdown.Coercive.Internal.DensityPassage.rightSide_spaceTime` (`Breakdown/Cert/CoerciveDensityPassageCutoff.lean:152`).

**Theorem: The source discrepancy tests to zero.** The right side minus its limiting formula has zero pairing with a periodic solenoidal test. Source: `Breakdown.Coercive.Internal.DensityPassage.rightSide_orthogonal_periodic` (`Breakdown/Cert/CoerciveDensityPassageCutoff.lean:203`).

### Breakdown.Cert.CoerciveDensityPassageEnergy

Quadratic trace and gradient estimates turn convergence of weak derivative fields into convergence of the weighted perturbation energy.

**Paper context:** Appendix B, Proposition B.1: energy continuity under smooth approximation.

**Theorem: Perturb the norm square.** For positive ε, the norm square of a sum is bounded by (1+ε) times the first square plus (1+1/ε) times the second. Source: `Breakdown.Coercive.Internal.DensityPassageEnergy.norm_add_sq_le` (`Breakdown/Cert/CoerciveDensityPassageEnergy.lean:14`).

**Theorem: Second-derivative square is continuous.** Under the stated hypotheses, the squared second-derivative norm is continuous. Source: `Breakdown.Coercive.Internal.DensityPassageEnergy.continuous_secondDerivSq` (`Breakdown/Cert/CoerciveDensityPassageEnergy.lean:26`).

**Theorem: Second-derivative error is symmetric.** Reversing the order of subtraction leaves the squared second-derivative discrepancy unchanged. Source: `Breakdown.Coercive.Internal.DensityPassageEnergy.secondDerivSq_sub_comm` (`Breakdown/Cert/CoerciveDensityPassageEnergy.lean:30`).

**Theorem: Gradient error is symmetric.** Reversing the order of subtraction leaves the squared matrix discrepancy unchanged. Source: `Breakdown.Coercive.Internal.DensityPassageEnergy.matSq_sub_comm` (`Breakdown/Cert/CoerciveDensityPassageEnergy.lean:36`).

**Theorem: Continuity of squared trace norm.** The squared norm of the second-derivative trace depends continuously on the second-derivative tensor. Source: `Breakdown.Coercive.Internal.DensityPassageEnergy.continuous_traceSq` (`Breakdown/Cert/CoerciveDensityPassageEnergy.lean:42`).

**Theorem: Squared matrix norm is continuous.** Under the stated hypotheses, the squared matrix norm is continuous. Source: `Breakdown.Coercive.Internal.DensityPassageEnergy.continuous_matNorm` (`Breakdown/Cert/CoerciveDensityPassageEnergy.lean:47`).

**Theorem: The period slab as a restricted measure.** Restricting space-time volume to the unit time slab equals the product of restricted time volume and spatial volume. Source: `Breakdown.Coercive.Internal.DensityPassageEnergy.restrict_prod_eq` (`Breakdown/Cert/CoerciveDensityPassageEnergy.lean:51`).

**Theorem: Integrate directly over the period slab.** The iterated nonnegative period integral equals the integral over the period product measure. Source: `Breakdown.Coercive.Internal.DensityPassageEnergy.periodLIntegral_eq_prod_measure` (`Breakdown/Cert/CoerciveDensityPassageEnergy.lean:55`).

**Theorem: Squared matrix norm is nonnegative.** The squared matrix norm is nonnegative for the stated data. Source: `Breakdown.Coercive.Internal.DensityPassageEnergy.matSq_nonneg` (`Breakdown/Cert/CoerciveDensityPassageEnergy.lean:61`).

**Theorem: Second-derivative square is nonnegative.** The squared second-derivative norm is nonnegative for the stated data. Source: `Breakdown.Coercive.Internal.DensityPassageEnergy.secondDerivSq_nonneg` (`Breakdown/Cert/CoerciveDensityPassageEnergy.lean:65`).

**Theorem: Control the trace by all second partials.** The squared norm of the trace is at most three times the full second-derivative norm square. Source: `Breakdown.Coercive.Internal.DensityPassageEnergy.trace_sq_le` (`Breakdown/Cert/CoerciveDensityPassageEnergy.lean:69`).

**Theorem: Split a trace into reference and error.** The second-derivative trace equals the reference trace plus the trace of the second-derivative difference. Source: `Breakdown.Coercive.Internal.DensityPassageEnergy.secondDerivTrace_add_sub` (`Breakdown/Cert/CoerciveDensityPassageEnergy.lean:85`).

**Theorem: Perturb the matrix norm square.** The matrix norm square after perturbation is bounded by its original square and the difference square with the displayed ε weights. Source: `Breakdown.Coercive.Internal.DensityPassageEnergy.matSq_le` (`Breakdown/Cert/CoerciveDensityPassageEnergy.lean:92`).

**Theorem: Perturb the weighted energy density.** The perturbed trace and weighted-gradient density is bounded by the original density and the derivative discrepancies with the stated ε factors. Source: `Breakdown.Coercive.Internal.DensityPassageEnergy.energy_point_le` (`Breakdown/Cert/CoerciveDensityPassageEnergy.lean:100`).

**Theorem: Period integral preserves scaling.** Under the stated hypotheses, the nonnegative period integral commutes with multiplication by a constant. Source: `Breakdown.Coercive.Internal.DensityPassageEnergy.periodLIntegral_const_mul` (`Breakdown/Cert/CoerciveDensityPassageEnergy.lean:117`).

**Theorem: Period integration preserves order.** An almost-everywhere pointwise bound implies the same bound between the nonnegative period integrals. Source: `Breakdown.Coercive.Internal.DensityPassageEnergy.periodLIntegral_mono` (`Breakdown/Cert/CoerciveDensityPassageEnergy.lean:127`).

**Theorem: Measurable nonnegative conversion.** Converting a real function to a nonnegative extended-real function preserves its measurability up to a null set. Source: `Breakdown.Coercive.Internal.DensityPassageEnergy.aem_ofReal` (`Breakdown/Cert/CoerciveDensityPassageEnergy.lean:132`).

**Theorem: Subadditivity of the period integral.** The nonnegative period integral of a sum is at most the sum of the two period integrals. Source: `Breakdown.Coercive.Internal.DensityPassageEnergy.periodLIntegral_add_le'` (`Breakdown/Cert/CoerciveDensityPassageEnergy.lean:136`).

**Theorem: Adjustable bounds force convergence.** The stated bounds for every positive tolerance imply that the real sequence converges to the specified real limit. Source: `Breakdown.Coercive.Internal.DensityPassageEnergy.tendsto_of_eps_bounds` (`Breakdown/Cert/CoerciveDensityPassageEnergy.lean:146`).

**Theorem: Weighted energies pass to the limit.** The weighted energies of the approximating derivative fields converge to the weighted energy of the limiting gradient and Hessian. Source: `Breakdown.Coercive.weightedEnergy_tendsto` (`Breakdown/Cert/CoerciveDensityPassageEnergy.lean:195`).

### Breakdown.Cert.CoerciveDensityPassageLiminf

The positive side of the signed density inequality is bounded by a pointwise lower limit, then Fatou-type integration passes that lower bound to the limit.

**Paper context:** Appendix B, Proposition B.1: lower semicontinuity of the positive density contribution.

**Theorem: A sum lies below its lower limit.** The limiting nonnegative series plus its convergent extra term is at most the lower limit of the corresponding approximating sums. Source: `Breakdown.Coercive.Internal.DensityPassage.tsum_add_le_liminf` (`Breakdown/Cert/CoerciveDensityPassageLiminf.lean:14`).

**Theorem: Combine positive density sums.** When the block term is zero, the positive split density equals one sum of paired positive mode and remainder terms plus the positive stretching term. Source: `Breakdown.Coercive.Internal.DensityPassage.splitLeft_eq` (`Breakdown/Cert/CoerciveDensityPassageLiminf.lean:24`).

**Theorem: The positive density has a lower limit.** The limiting positive split density is at most the lower limit of its approximations under the given modewise convergence assumptions. Source: `Breakdown.Coercive.Internal.DensityPassage.splitLeft_le_liminf` (`Breakdown/Cert/CoerciveDensityPassageLiminf.lean:30`).

### Breakdown.Cert.CoerciveDensityPassageLinear

Linearity of mode extraction, curl contraction, and variational pairings shows that differences of multiplier fields represent differences of perturbations.

**Paper context:** Appendix B, Proposition B.1: linearity needed for multiplier convergence.

**Theorem: Axial rotation preserves subtraction.** Under the stated hypotheses, the axial rotation commutes with subtraction. Source: `Breakdown.Coercive.Internal.DensityPassageLinear.axialRot_sub` (`Breakdown/Cert/CoerciveDensityPassageLinear.lean:19`).

**Theorem: Subtract inside a Fourier-mode average.** Under the stated hypotheses, the Fourier mode average commutes with subtraction. Source: `Breakdown.Coercive.Internal.DensityPassageLinear.modeAverage_sub` (`Breakdown/Cert/CoerciveDensityPassageLinear.lean:23`).

**Theorem: Velocity mode preserves subtraction.** Under the stated hypotheses, the velocity mode commutes with subtraction. Source: `Breakdown.Coercive.Internal.DensityPassageLinear.modeVel_sub` (`Breakdown/Cert/CoerciveDensityPassageLinear.lean:46`).

**Theorem: Gradient mode preserves subtraction.** Under the stated hypotheses, the gradient mode commutes with subtraction. Source: `Breakdown.Coercive.Internal.DensityPassageLinear.modeGrad_sub` (`Breakdown/Cert/CoerciveDensityPassageLinear.lean:58`).

**Theorem: Curl mode preserves subtraction.** Under the stated hypotheses, the curl extracted from a gradient commutes with subtraction. Source: `Breakdown.Coercive.Internal.DensityPassageLinear.curlOfGrad_sub` (`Breakdown/Cert/CoerciveDensityPassageLinear.lean:70`).

**Theorem: Subtract the first complex argument.** The complex coordinate pairing distributes over subtraction in its first argument. Source: `Breakdown.Coercive.Internal.DensityPassageLinear.cdot_sub_left` (`Breakdown/Cert/CoerciveDensityPassageLinear.lean:75`).

**Theorem: Modes subtract almost everywhere.** Almost everywhere, taking velocity or gradient modes commutes with subtraction of the corresponding input fields. Source: `Breakdown.Coercive.Internal.DensityPassageLinear.ae_mode_sub` (`Breakdown/Cert/CoerciveDensityPassageLinear.lean:78`).

**Theorem: Restrict an almost-everywhere statement.** A statement holding almost everywhere in space-time also holds almost everywhere on the period slab. Source: `Breakdown.Coercive.Internal.DensityPassageLinear.ae_period` (`Breakdown/Cert/CoerciveDensityPassageLinear.lean:91`).

**Theorem: Subtract the combined multiplier term.** Almost everywhere, the combined curl and velocity multiplier term for the field differences equals the difference of the two combined terms. Source: `Breakdown.Coercive.Internal.DensityPassageLinear.modeTerm_sub` (`Breakdown/Cert/CoerciveDensityPassageLinear.lean:96`).

**Theorem: Subtract multiplier mode sums.** Under the stated hypotheses, the sum of multiplier mode pairings commutes with subtraction. Source: `Breakdown.Coercive.Internal.DensityPassageLinear.fieldModeSum_sub` (`Breakdown/Cert/CoerciveDensityPassageLinear.lean:112`).

**Theorem: Subtract in the Laplacian pairing.** The period pairing of the negative trace of a Hessian difference equals the difference of the corresponding negative-trace pairings. Source: `Breakdown.Coercive.Internal.DensityPassageLinear.secondDerivPart_sub` (`Breakdown/Cert/CoerciveDensityPassageLinear.lean:142`).

**Theorem: Test the multiplier difference.** The difference between the first multiplier and the sum of the other two pairs to zero with every stated periodic test field. Source: `Breakdown.Coercive.Internal.DensityPassageLinear.multiplier_difference_pairing` (`Breakdown/Cert/CoerciveDensityPassageLinear.lean:169`).

### Breakdown.Cert.CoerciveDensityPassageMeasurable

The positive and negative density expressions are made measurable on the period slab and on almost every spatial slice, supplying the measure-theoretic hypotheses for the limit argument.

**Paper context:** Appendix B, Proposition B.1: measurability in the ordinary mode-density passage.

**Theorem: The positive density side is measurable.** The positive split density is measurable on almost every spatial slice and its spatial integral is measurable in time. Source: `Breakdown.Coercive.Internal.DensityPassage.splitLeft_aemeasurable` (`Breakdown/Cert/CoerciveDensityPassageMeasurable.lean:18`).

### Breakdown.Cert.CoerciveDensityPassageModes

Integrated mode errors are controlled by physical approximation errors, and a common subsequence gives the mode and stretching limits needed by the density argument.

**Paper context:** Appendix B, Proposition B.1: convergence of ordinary Fourier-mode densities.

**Theorem: Axial rotation preserves subtraction.** Under the stated hypotheses, the axial rotation commutes with subtraction. Source: `Breakdown.Coercive.Internal.DensityPassageModes.axialRot_sub` (`Breakdown/Cert/CoerciveDensityPassageModes.lean:20`).

**Theorem: Integrability with the Fourier phase.** Under the stated hypotheses, the Fourier-phase weighted integrand is integrable. Source: `Breakdown.Coercive.Internal.DensityPassageModes.integrable_exp_mul` (`Breakdown/Cert/CoerciveDensityPassageModes.lean:24`).

**Theorem: Integrable Hessian orbit coordinates.** Under the stated hypotheses, the rotated Hessian-coordinate orbit is integrable. Source: `Breakdown.Coercive.Internal.DensityPassageModes.integrable_secondDerivComponent` (`Breakdown/Cert/CoerciveDensityPassageModes.lean:30`).

**Theorem: Velocity mode preserves subtraction.** Under the stated hypotheses, the velocity mode commutes with subtraction. Source: `Breakdown.Coercive.Internal.DensityPassageModes.modeVel_sub_of` (`Breakdown/Cert/CoerciveDensityPassageModes.lean:49`).

**Theorem: Gradient mode preserves subtraction.** Under the stated hypotheses, the gradient mode commutes with subtraction. Source: `Breakdown.Coercive.Internal.DensityPassageModes.modeGrad_sub_of` (`Breakdown/Cert/CoerciveDensityPassageModes.lean:66`).

**Theorem: Subtract second-derivative modes.** Under the stated hypotheses, the second-derivative mode commutes with subtraction. Source: `Breakdown.Coercive.Internal.DensityPassageModes.modeSecondDeriv_sub_of` (`Breakdown/Cert/CoerciveDensityPassageModes.lean:87`).

**Definition: Velocity difference with radial decay.** Multiply the difference of two velocity fields by the reciprocal of one plus the spatial radius. Source: `Breakdown.Coercive.Internal.DensityPassageModes.weightedDiff` (`Breakdown/Cert/CoerciveDensityPassageModes.lean:109`).

**Theorem: Radial weights pass through modes.** Taking the velocity mode of the radially weighted field difference equals multiplying the difference mode by (1 + ‖y‖)⁻¹. Source: `Breakdown.Coercive.Internal.DensityPassageModes.modeVel_weightedDiff` (`Breakdown/Cert/CoerciveDensityPassageModes.lean:111`).

**Theorem: Scale complex square norms.** Multiplying a finite complex array by c multiplies its squared norm by ‖c‖². Source: `Breakdown.Coercive.Internal.DensityPassageModes.cnormSq_const_mul` (`Breakdown/Cert/CoerciveDensityPassageModes.lean:122`).

**Theorem: Square-norm errors determine convergence.** Vanishing squared complex-array discrepancy implies convergence of the complex-array sequence to the specified array. Source: `Breakdown.Coercive.Internal.DensityPassageModes.tendsto_of_cnormSq` (`Breakdown/Cert/CoerciveDensityPassageModes.lean:126`).

**Definition: Remainder as a function of amplitudes.** Evaluate the base, curl, and velocity remainder terms on the supplied mode amplitudes. Source: `Breakdown.Coercive.Internal.DensityPassageModes.restOfAmps` (`Breakdown/Cert/CoerciveDensityPassageModes.lean:139`).

**Theorem: Express the remainder in amplitudes.** The mode remainder equals the amplitude-variable remainder evaluated on the velocity, gradient, curl, Hessian, and curl-gradient amplitudes. Source: `Breakdown.Coercive.Internal.DensityPassageModes.modeRest_eq` (`Breakdown/Cert/CoerciveDensityPassageModes.lean:158`).

**Theorem: The amplitude remainder is continuous.** For fixed coefficients and space-time point, the remainder depends continuously on its five amplitude functions in their product topology. Source: `Breakdown.Coercive.Internal.DensityPassageModes.continuous_restOfAmps` (`Breakdown/Cert/CoerciveDensityPassageModes.lean:164`).

**Definition: Stretching at fixed field values.** Evaluate the stretching form on constant velocity and gradient values at the chosen point. Source: `Breakdown.Coercive.Internal.DensityPassageModes.stretchOf` (`Breakdown/Cert/CoerciveDensityPassageModes.lean:171`).

**Theorem: Stretching through pointwise data.** The stretching form equals its fixed-data expression evaluated at the actual velocity and gradient. Source: `Breakdown.Coercive.Internal.DensityPassageModes.stretchForm_eq_of` (`Breakdown/Cert/CoerciveDensityPassageModes.lean:174`).

**Theorem: Continuous stretching in field data.** Under the stated hypotheses, the stretching form in its field and gradient arguments is continuous. Source: `Breakdown.Coercive.Internal.DensityPassageModes.continuous_stretchForm` (`Breakdown/Cert/CoerciveDensityPassageModes.lean:179`).

**Theorem: Mode convergence passes to the densities.** Convergence of the velocity and derivative modes gives convergence of each positive density term, each remainder term, and the stretching form. Source: `Breakdown.Coercive.Internal.DensityPassageModes.limits_of_modes` (`Breakdown/Cert/CoerciveDensityPassageModes.lean:184`).

**Definition: One squared mode discrepancy.** Select the squared discrepancy of a weighted velocity mode, gradient mode, or second-derivative mode. Source: `Breakdown.Coercive.Internal.DensityPassageModes.modeDiff` (`Breakdown/Cert/CoerciveDensityPassageModes.lean:236`).

**Definition: Enumerate the frequency lattice.** Choose a bijection between the natural numbers and the integer frequency pairs. Source: `Breakdown.Coercive.Internal.DensityPassageModes.modeIndex` (`Breakdown/Cert/CoerciveDensityPassageModes.lean:243`).

**Definition: Enumerate all mode discrepancies.** Use pairing of natural numbers to enumerate derivative orders together with the frequency lattice. Source: `Breakdown.Coercive.Internal.DensityPassageModes.diffModes` (`Breakdown/Cert/CoerciveDensityPassageModes.lean:245`).

**Theorem: Decode an enumerated mode discrepancy.** The paired natural-number index recovers the specified derivative order and frequency-pair discrepancy. Source: `Breakdown.Coercive.Internal.DensityPassageModes.diffModes_pair` (`Breakdown/Cert/CoerciveDensityPassageModes.lean:249`).

**Theorem: Weighted velocity error is measurable.** Under the stated hypotheses, the radially weighted velocity difference is strongly measurable up to a null set. Source: `Breakdown.Coercive.Internal.DensityPassageModes.weightedDiff_measurable` (`Breakdown/Cert/CoerciveDensityPassageModes.lean:260`).

**Theorem: Squared mode discrepancy is measurable.** Under the stated hypotheses, the squared mode discrepancy is measurable up to a null set. Source: `Breakdown.Coercive.Internal.DensityPassageModes.modeDiff_aemeasurable` (`Breakdown/Cert/CoerciveDensityPassageModes.lean:268`).

**Theorem: Weighted velocity-mode errors vanish.** The integrated square of each radially weighted velocity-mode discrepancy tends to zero. Source: `Breakdown.Coercive.Internal.DensityPassageModes.vel_diff_tendsto` (`Breakdown/Cert/CoerciveDensityPassageModes.lean:286`).

**Theorem: Gradient-mode errors vanish in L².** The integrated square of each gradient-mode discrepancy tends to zero. Source: `Breakdown.Coercive.Internal.DensityPassageModes.grad_diff_tendsto` (`Breakdown/Cert/CoerciveDensityPassageModes.lean:309`).

**Theorem: Hessian-mode errors vanish in L².** The integrated square of each second-derivative-mode discrepancy tends to zero. Source: `Breakdown.Coercive.Internal.DensityPassageModes.secondDeriv_diff_tendsto` (`Breakdown/Cert/CoerciveDensityPassageModes.lean:326`).

**Theorem: Each selected mode error vanishes.** The period integral of each indexed mode-discrepancy square tends to zero. Source: `Breakdown.Coercive.Internal.DensityPassageModes.modeDiff_tendsto` (`Breakdown/Cert/CoerciveDensityPassageModes.lean:343`).

**Theorem: The zeroth discrepancy is velocity error.** The zeroth discrepancy is the squared radially weighted velocity-mode error. Source: `Breakdown.Coercive.Internal.DensityPassageModes.modeDiff_zero` (`Breakdown/Cert/CoerciveDensityPassageModes.lean:356`).

**Theorem: The first discrepancy is gradient error.** The first discrepancy is the squared gradient-mode error. Source: `Breakdown.Coercive.Internal.DensityPassageModes.modeDiff_one` (`Breakdown/Cert/CoerciveDensityPassageModes.lean:362`).

**Theorem: The second discrepancy is Hessian error.** The second discrepancy is the squared second-derivative-mode error. Source: `Breakdown.Coercive.Internal.DensityPassageModes.modeDiff_two` (`Breakdown/Cert/CoerciveDensityPassageModes.lean:369`).

**Theorem: All derivative modes subtract a.e..** On one common full-measure set, taking velocity, gradient, or Hessian modes commutes with every approximation-minus-limit difference. Source: `Breakdown.Coercive.Internal.DensityPassageModes.ae_modes_sub` (`Breakdown/Cert/CoerciveDensityPassageModes.lean:376`).

**Theorem: Choose one subsequence for all modes.** There is a strictly increasing subsequence along which every positive mode term, every remainder mode, and the stretching form converge almost everywhere. Source: `Breakdown.Coercive.Internal.DensityPassageModes.modes_converge_ae` (`Breakdown/Cert/CoerciveDensityPassageModes.lean:396`).

### Breakdown.Cert.CoerciveDensityPassageNegative

The negative density side is treated through absolute discrepancy bounds and a sandwich argument for its nonnegative integrals.

**Paper context:** Appendix B, Proposition B.1: convergence of the negative density contribution.

**Theorem: Additivity of the period integral.** Under the measurability hypothesis, the iterated nonnegative integral of a sum equals the sum of its two iterated integrals. Source: `Breakdown.Coercive.Internal.DensityPassage.iterated_lintegral_add_right` (`Breakdown/Cert/CoerciveDensityPassageNegative.lean:18`).

**Theorem: Negative parts converge under L¹ control.** The negative part of the limit is integrable and its integrals converge under the stated L¹ difference control. Source: `Breakdown.Coercive.Internal.DensityPassage.negPart_tendsto` (`Breakdown/Cert/CoerciveDensityPassageNegative.lean:32`).

**Theorem: Integrate the negative density split.** With zero block contribution, the integrated negative split equals the negative remainder integral plus the negative stretching integral. Source: `Breakdown.Coercive.Internal.DensityPassage.splitRight_integral_eq` (`Breakdown/Cert/CoerciveDensityPassageNegative.lean:69`).

**Theorem: An integral sandwich gives convergence.** The stated upper and lower integral controls force the nonnegative period integrals to converge to the limiting integrand's period integral. Source: `Breakdown.Coercive.Internal.DensityPassage.lintegral_tendsto_of_sandwich` (`Breakdown/Cert/CoerciveDensityPassageNegative.lean:77`).

**Theorem: Summed negative parts converge in L¹.** The limiting sum of negative mode parts is integrable and its approximating integrals converge under the stated summed L¹ control. Source: `Breakdown.Coercive.Internal.DensityPassage.tsum_negPart_tendsto` (`Breakdown/Cert/CoerciveDensityPassageNegative.lean:98`).

**Theorem: Differences retain period L² energy.** The difference of the two fields with finite period squared energies also has finite period squared energy. Source: `Breakdown.Coercive.Internal.DensityPassage.periodL2_sub_of` (`Breakdown/Cert/CoerciveDensityPassageNegative.lean:118`).

### Breakdown.Cert.CoerciveDensityPassagePairing

Orthogonality to periodic solenoidal tests is extended to the multiplier, identifying its pairing with the source and with the explicit limiting equation source.

**Paper context:** Appendix B, Proposition B.1: convergence of the multiplier pairings.

**Theorem: Orthogonal data pair to zero.** The two fields have zero period pairing when the stated orthogonality and multiplier representation hypotheses hold. Source: `Breakdown.Coercive.Internal.DensityPassage.pairing_eq_zero_of_orthogonal` (`Breakdown/Cert/CoerciveDensityPassagePairing.lean:18`).

**Theorem: Replace the source in a multiplier test.** The given right side and its explicit limiting-source formula have the same pairing with the multiplier. Source: `Breakdown.Coercive.Internal.DensityPassage.pairing_rightSideLimit_eq` (`Breakdown/Cert/CoerciveDensityPassagePairing.lean:59`).

### Breakdown.Cert.CoerciveDensityPassageRest

A common mode-amplitude energy controls the remainder and its approximation discrepancy; the file proves measurability, finite integrated energy, and vanishing total discrepancy.

**Paper context:** Appendix B, Proposition B.1: summable remainder control for ordinary modes.

**Definition: Combined squared mode amplitudes.** Add the second-derivative, curl-gradient, gradient, curl, and radially weighted velocity squares at one mode. Source: `Breakdown.Coercive.Internal.DensityPassageRest.ampSq` (`Breakdown/Cert/CoerciveDensityPassageRest.lean:25`).

**Definition: Sum of squared mode amplitudes.** Sum the nonnegative combined amplitude squares over all frequency pairs. Source: `Breakdown.Coercive.Internal.DensityPassageRest.ampTot` (`Breakdown/Cert/CoerciveDensityPassageRest.lean:30`).

**Definition: Combined squared mode discrepancies.** Add the corresponding squared differences of derivative, curl, and radially weighted velocity modes. Source: `Breakdown.Coercive.Internal.DensityPassageRest.diffSq` (`Breakdown/Cert/CoerciveDensityPassageRest.lean:34`).

**Definition: Sum of squared mode discrepancies.** Sum the nonnegative combined mode discrepancies over all frequency pairs. Source: `Breakdown.Coercive.Internal.DensityPassageRest.diffTot` (`Breakdown/Cert/CoerciveDensityPassageRest.lean:44`).

**Theorem: One quadratic bound for all remainders.** There is a uniform nonnegative constant controlling the absolute mode remainder and its changes by the amplitude and discrepancy square sums. Source: `Breakdown.Coercive.Internal.DensityPassageRest.rest_pointwise_bound` (`Breakdown/Cert/CoerciveDensityPassageRest.lean:50`).

**Theorem: Continuity of curl-gradient contraction.** The curl-gradient contraction depends continuously on the complex second-derivative array. Source: `Breakdown.Coercive.Internal.DensityPassageRest.continuous_curlGradOfSecondDeriv` (`Breakdown/Cert/CoerciveDensityPassageRest.lean:68`).

**Theorem: The curl contraction is continuous.** The complex curl contraction depends continuously on its gradient array. Source: `Breakdown.Coercive.Internal.DensityPassageRest.continuous_curlOfGrad` (`Breakdown/Cert/CoerciveDensityPassageRest.lean:74`).

**Theorem: Measurability of the amplitude energy.** Under the stated hypotheses, the combined amplitude-square sum is measurable up to a null set. Source: `Breakdown.Coercive.Internal.DensityPassageRest.aem_terms` (`Breakdown/Cert/CoerciveDensityPassageRest.lean:79`).

**Theorem: Measurable amplitude-discrepancy energy.** Under the stated hypotheses, the combined amplitude-discrepancy square sum is measurable up to a null set. Source: `Breakdown.Coercive.Internal.DensityPassageRest.aem_diff_terms` (`Breakdown/Cert/CoerciveDensityPassageRest.lean:94`).

**Theorem: Total mode energy is measurable.** Under the stated hypotheses, the sum of mode amplitude squares is measurable up to a null set. Source: `Breakdown.Coercive.Internal.DensityPassageRest.ampTot_aemeasurable` (`Breakdown/Cert/CoerciveDensityPassageRest.lean:115`).

**Theorem: Total mode error is measurable.** Under the stated hypotheses, the sum of mode discrepancy squares is measurable up to a null set. Source: `Breakdown.Coercive.Internal.DensityPassageRest.diffTot_aemeasurable` (`Breakdown/Cert/CoerciveDensityPassageRest.lean:126`).

**Theorem: Measurable remainder discrepancies.** Under the stated hypotheses, the sum of absolute mode-remainder discrepancies is measurable up to a null set. Source: `Breakdown.Coercive.Internal.DensityPassageRest.restDiff_aemeasurable` (`Breakdown/Cert/CoerciveDensityPassageRest.lean:142`).

**Theorem: A radial weight factors out of a mode.** The squared mode of radially weighted velocity equals the unweighted mode square divided by the squared radial weight denominator. Source: `Breakdown.Coercive.Internal.DensityPassageRest.cnormSq_modeVel_weight` (`Breakdown/Cert/CoerciveDensityPassageRest.lean:155`).

**Theorem: Parseval with inverse-radius weighting.** The sum of the radially weighted velocity-mode energies equals the physical velocity energy with the same radial weight. Source: `Breakdown.Coercive.Internal.DensityPassageRest.weighted_squareSum` (`Breakdown/Cert/CoerciveDensityPassageRest.lean:171`).

**Theorem: Bound the combined amplitude energy.** The integrated amplitude sum is bounded by 730 times the second-derivative mode energy, 244 times the gradient mode energy, and the weighted velocity-mode energy. Source: `Breakdown.Coercive.Internal.DensityPassageRest.ampTot_le` (`Breakdown/Cert/CoerciveDensityPassageRest.lean:196`).

**Theorem: Total amplitude energy is integrable.** The period integral of the total combined mode-amplitude energy is finite. Source: `Breakdown.Coercive.Internal.DensityPassageRest.ampTot_finite` (`Breakdown/Cert/CoerciveDensityPassageRest.lean:253`).

**Theorem: Subtract inside the curl-gradient map.** Under the stated hypotheses, the curl-gradient contraction commutes with subtraction. Source: `Breakdown.Coercive.Internal.DensityPassageRest.curlGradOfSecondDeriv_sub` (`Breakdown/Cert/CoerciveDensityPassageRest.lean:269`).

**Theorem: Curl mode preserves subtraction.** Under the stated hypotheses, the curl extracted from a gradient commutes with subtraction. Source: `Breakdown.Coercive.Internal.DensityPassageRest.curlOfGrad_sub` (`Breakdown/Cert/CoerciveDensityPassageRest.lean:274`).

**Theorem: Total mode discrepancy tends to zero.** The period integral of the total combined mode discrepancy tends to zero along the smooth approximation. Source: `Breakdown.Coercive.Internal.DensityPassageRest.diffTot_tendsto` (`Breakdown/Cert/CoerciveDensityPassageRest.lean:279`).

**Theorem: The mode remainder converges in L¹.** The remainder differences are measurable, the limiting absolute remainder is integrable, and the total L¹ remainder error tends to zero. Source: `Breakdown.Coercive.Internal.DensityPassageRest.rest_abs_converges_of` (`Breakdown/Cert/CoerciveDensityPassageRest.lean:349`).

### Breakdown.Cert.CoerciveDensityPassageRestBound

The remainder-bound specification packages a uniform amplitude estimate and an adjustable quadratic difference estimate; closure under sums, signs, and products proves the bounds for the base density.

**Paper context:** Appendix B, Proposition B.1: reusable quantitative bounds for density remainders.

**Definition: Sum of squared mode amplitudes.** Sum the second-derivative, curl-gradient, gradient, curl, and radially weighted velocity squares over the frequency lattice. Source: `Breakdown.Coercive.Internal.DensityPassageRestBound.ampTotal` (`Breakdown/Cert/CoerciveDensityPassageRestBound.lean:15`).

**Definition: Sum of squared mode discrepancies.** Sum the corresponding derivative, curl, and radially weighted velocity discrepancies over the frequency lattice. Source: `Breakdown.Coercive.Internal.DensityPassageRestBound.diffTotal` (`Breakdown/Cert/CoerciveDensityPassageRestBound.lean:21`).

**Definition: Uniform bound for a remainder.** Require both a quadratic amplitude bound for the remainder and an adjustable quadratic bound for differences of remainders. Source: `Breakdown.Coercive.Internal.DensityPassageRestBound.IsRestBound` (`Breakdown/Cert/CoerciveDensityPassageRestBound.lean:31`).

**Theorem: Remainder bounds are closed under sums.** The sum of two remainders satisfying the uniform amplitude and quadratic difference bounds satisfies those bounds as well. Source: `Breakdown.Coercive.Internal.DensityPassageRestBound.IsRestBound.add` (`Breakdown/Cert/CoerciveDensityPassageRestBound.lean:43`).

**Theorem: A reverse triangle inequality for modes.** The difference between the two complex-vector amplitudes is bounded by the amplitude of their difference. Source: `Breakdown.Coercive.Internal.DensityPassageRestBound.sqrt_cnormSq_sub_le` (`Breakdown/Cert/CoerciveDensityPassageRestBound.lean:87`).

**Theorem: Control a difference of products.** The product discrepancy is bounded by discrepancy squares and original-factor squares with the stated adjustable weight. Source: `Breakdown.Coercive.Internal.DensityPassageRestBound.prod_diff_le` (`Breakdown/Cert/CoerciveDensityPassageRestBound.lean:95`).

**Theorem: Control a weighted square discrepancy.** A bounded coefficient times a difference of squares is controlled by the square discrepancy and the original square with the stated adjustable weight. Source: `Breakdown.Coercive.Internal.DensityPassageRestBound.sq_term_le` (`Breakdown/Cert/CoerciveDensityPassageRestBound.lean:125`).

**Theorem: Bound a weighted square.** The absolute value of a bounded coefficient times a square is at most the coefficient bound times that square. Source: `Breakdown.Coercive.Internal.DensityPassageRestBound.sq_term_abs_le` (`Breakdown/Cert/CoerciveDensityPassageRestBound.lean:136`).

**Theorem: Squaring the amplitude recovers energy.** The square of the complex-vector amplitude equals its squared complex norm. Source: `Breakdown.Coercive.Internal.DensityPassageRestBound.sqrt_cnormSq_sq` (`Breakdown/Cert/CoerciveDensityPassageRestBound.lean:140`).

**Theorem: Convert a quadratic bound to ENNReal.** The real quadratic estimate gives the corresponding bound between nonnegative extended-real quantities. Source: `Breakdown.Coercive.Internal.DensityPassageRestBound.ennreal_step` (`Breakdown/Cert/CoerciveDensityPassageRestBound.lean:143`).

**Theorem: Sum a two-term nonnegative bound.** A termwise nonnegative upper bound sums to the corresponding weighted sums of its two controlling series. Source: `Breakdown.Coercive.Internal.DensityPassageRestBound.tsum_step` (`Breakdown/Cert/CoerciveDensityPassageRestBound.lean:150`).

**Theorem: A reverse triangle inequality for modes.** The difference between the two complex-vector amplitudes is bounded by the amplitude of their difference. Source: `Breakdown.Coercive.Internal.DensityPassageRestBound.amp_sub_le` (`Breakdown/Cert/CoerciveDensityPassageRestBound.lean:156`).

**Theorem: A weighted reverse triangle inequality.** Dividing by the positive radial factor preserves the reverse triangle bound for the two complex-vector amplitudes. Source: `Breakdown.Coercive.Internal.DensityPassageRestBound.amp_sub_div_le` (`Breakdown/Cert/CoerciveDensityPassageRestBound.lean:160`).

**Theorem: Split a five-square discrepancy.** The difference of the two five-term quadratic expressions equals the sum of their individual weighted square differences. Source: `Breakdown.Coercive.Internal.DensityPassageRestBound.five_split` (`Breakdown/Cert/CoerciveDensityPassageRestBound.lean:165`).

**Theorem: Uniform bounds for the base coefficients.** One nonnegative constant bounds all five base-density coefficients, including the radially weighted velocity coefficient. Source: `Breakdown.Coercive.Internal.DensityPassageRestBound.base_coeff_bounds` (`Breakdown/Cert/CoerciveDensityPassageRestBound.lean:171`).

**Theorem: Base density remainder bound.** The base density has the common uniform amplitude bound and adjustable quadratic difference bound. Source: `Breakdown.Coercive.Internal.DensityPassageRestBound.base_bound` (`Breakdown/Cert/CoerciveDensityPassageRestBound.lean:217`).

**Definition: Combined squares at one mode.** Add the derivative, curl, and radially weighted velocity squares at one mode and point. Source: `Breakdown.Coercive.Internal.DensityPassageRestBound.ampSqAt` (`Breakdown/Cert/CoerciveDensityPassageRestBound.lean:304`).

**Definition: Combined discrepancy at one mode.** Add the corresponding derivative, curl, and weighted-velocity discrepancy squares at one mode and point. Source: `Breakdown.Coercive.Internal.DensityPassageRestBound.diffSqAt` (`Breakdown/Cert/CoerciveDensityPassageRestBound.lean:310`).

**Theorem: Expand the total amplitude sum.** The total amplitude energy equals the series of the combined amplitude square at each mode. Source: `Breakdown.Coercive.Internal.DensityPassageRestBound.ampTotal_eq` (`Breakdown/Cert/CoerciveDensityPassageRestBound.lean:320`).

**Theorem: Expand the total discrepancy sum.** The total discrepancy energy equals the series of the combined discrepancy square at each mode. Source: `Breakdown.Coercive.Internal.DensityPassageRestBound.diffTotal_eq` (`Breakdown/Cert/CoerciveDensityPassageRestBound.lean:324`).

**Definition: Amplitude and difference bounds.** Require a nonnegative amplitude whose square and squared increments are bounded by the combined mode energies. Source: `Breakdown.Coercive.Internal.DensityPassageRestBound.IsAmp` (`Breakdown/Cert/CoerciveDensityPassageRestBound.lean:330`).

**Theorem: Bound the squared amplitude difference.** The squared difference of two complex-vector amplitudes is at most the squared norm of their vector difference. Source: `Breakdown.Coercive.Internal.DensityPassageRestBound.amp_sq_sub_le` (`Breakdown/Cert/CoerciveDensityPassageRestBound.lean:335`).

**Theorem: Amplitude-square terms are nonnegative.** Each of the five terms in the combined mode-amplitude square is nonnegative. Source: `Breakdown.Coercive.Internal.DensityPassageRestBound.ampSqAt_parts` (`Breakdown/Cert/CoerciveDensityPassageRestBound.lean:340`).

**Theorem: Each discrepancy term is nonnegative.** Each of the five terms in the combined mode-discrepancy square is nonnegative. Source: `Breakdown.Coercive.Internal.DensityPassageRestBound.diffSqAt_parts` (`Breakdown/Cert/CoerciveDensityPassageRestBound.lean:349`).

**Theorem: Hessian amplitude energy bounds.** The Hessian amplitude is nonnegative, and its square and squared increments are controlled by the specified combined mode energies. Source: `Breakdown.Coercive.Internal.DensityPassageRestBound.isAmp_secondDeriv` (`Breakdown/Cert/CoerciveDensityPassageRestBound.lean:362`).

**Theorem: Curl-gradient amplitude energy bounds.** The curl-gradient amplitude is nonnegative, and its square and squared increments are controlled by the specified combined mode energies. Source: `Breakdown.Coercive.Internal.DensityPassageRestBound.isAmp_vortGrad` (`Breakdown/Cert/CoerciveDensityPassageRestBound.lean:370`).

**Theorem: Gradient amplitudes obey energy bounds.** The gradient amplitude is nonnegative, and its square and squared increments are controlled by the specified combined mode energies. Source: `Breakdown.Coercive.Internal.DensityPassageRestBound.isAmp_grad` (`Breakdown/Cert/CoerciveDensityPassageRestBound.lean:378`).

**Theorem: Curl amplitude energy bounds.** The curl amplitude is nonnegative, and its square and squared increments are controlled by the specified combined mode energies. Source: `Breakdown.Coercive.Internal.DensityPassageRestBound.isAmp_vort` (`Breakdown/Cert/CoerciveDensityPassageRestBound.lean:386`).

**Theorem: Weighted velocity amplitude bounds.** The radially damped velocity amplitude is nonnegative, and its square and squared increments are controlled by the specified combined mode energies. Source: `Breakdown.Coercive.Internal.DensityPassageRestBound.isAmp_vel` (`Breakdown/Cert/CoerciveDensityPassageRestBound.lean:394`).

**Theorem: Reindex two shifted frequency sums.** The equally weighted sum of two translated frequency series is twice the weight times the original series. Source: `Breakdown.Coercive.Internal.DensityPassageRestBound.tsum_shift_two` (`Breakdown/Cert/CoerciveDensityPassageRestBound.lean:407`).

**Theorem: Products satisfy the remainder bounds.** The stated bounded coefficient times two shifted amplitude factors satisfies the uniform amplitude and adjustable quadratic difference bounds. Source: `Breakdown.Coercive.Internal.DensityPassageRestBound.isRestBound_prod` (`Breakdown/Cert/CoerciveDensityPassageRestBound.lean:414`).

**Theorem: Zero satisfies the remainder bounds.** The identically zero remainder satisfies the uniform amplitude and quadratic difference specification. Source: `Breakdown.Coercive.Internal.DensityPassageRestBound.restBound_of_zero` (`Breakdown/Cert/CoerciveDensityPassageRestBound.lean:477`).

**Theorem: Negation preserves remainder bounds.** Negating a remainder preserves its uniform amplitude and adjustable quadratic difference bounds. Source: `Breakdown.Coercive.Internal.DensityPassageRestBound.IsRestBound.neg` (`Breakdown/Cert/CoerciveDensityPassageRestBound.lean:482`).

**Theorem: Finite sums retain remainder bounds.** A finite sum of remainders satisfying the uniform amplitude and quadratic difference bounds satisfies those bounds as well. Source: `Breakdown.Coercive.Internal.DensityPassageRestBound.isRestBound_finsetSum` (`Breakdown/Cert/CoerciveDensityPassageRestBound.lean:495`).

### Breakdown.Cert.CoerciveDensityPassageRestBoundAll

The separate base, curl, and velocity remainder bounds are combined into the ordinary full-mode remainder bound.

**Paper context:** Appendix B, Proposition B.1: assembling the remainder estimates used in weak passage.

**Theorem: One quadratic bound for all remainders.** There is a uniform nonnegative constant controlling the absolute mode remainder and its changes by the amplitude and discrepancy square sums. Source: `Breakdown.Coercive.Internal.DensityPassageRestBound.rest_pointwise_bound` (`Breakdown/Cert/CoerciveDensityPassageRestBoundAll.lean:15`).

### Breakdown.Cert.CoerciveDensityPassageRestBoundEps

Uniform bounds on the curl coefficients and their shifted amplitude products establish the curl-mode remainder's amplitude and difference estimates.

**Paper context:** Appendix B, Proposition B.1: curl-weight remainders in the weak passage.

**Theorem: Absolute bound for a nonnegative value.** A nonnegative real number bounded above by M has absolute value at most M. Source: `Breakdown.Coercive.Internal.DensityPassageRestBound.abs_le_of_nonneg_le` (`Breakdown/Cert/CoerciveDensityPassageRestBoundEps.lean:15`).

**Theorem: Uniform curl-remainder coefficients.** One nonnegative constant bounds the curl-remainder coefficients, including the radially weighted derivative and harmonic terms. Source: `Breakdown.Coercive.Internal.DensityPassageRestBound.eps_coeff_bounded` (`Breakdown/Cert/CoerciveDensityPassageRestBoundEps.lean:19`).

**Theorem: Curl-mode remainder remainder bound.** The curl-mode remainder has the common uniform amplitude bound and adjustable quadratic difference bound. Source: `Breakdown.Coercive.Internal.DensityPassageRestBound.epsRest_bound` (`Breakdown/Cert/CoerciveDensityPassageRestBoundEps.lean:122`).

### Breakdown.Cert.CoerciveDensityPassageRestBoundMu

The velocity-mode remainder is decomposed into bounded coefficient products and transferred through equal expressions to obtain its common remainder estimate.

**Paper context:** Appendix B, Proposition B.1: velocity-weight remainders in the weak passage.

**Theorem: Uniform velocity-remainder coefficients.** One nonnegative constant bounds all the radially weighted coefficients appearing in the velocity remainder. Source: `Breakdown.Coercive.Internal.DensityPassageRestBound.mu_coeff_bounds` (`Breakdown/Cert/CoerciveDensityPassageRestBoundMu.lean:15`).

**Theorem: Equal remainders share their bounds.** The stated equality of remainders transfers the uniform amplitude and adjustable quadratic difference bounds to the second remainder. Source: `Breakdown.Coercive.Internal.DensityPassageRestBound.restBound_congr` (`Breakdown/Cert/CoerciveDensityPassageRestBoundMu.lean:219`).

**Theorem: Velocity-mode remainder remainder bound.** The velocity-mode remainder has the common uniform amplitude bound and adjustable quadratic difference bound. Source: `Breakdown.Coercive.Internal.DensityPassageRestBound.muRest_bound` (`Breakdown/Cert/CoerciveDensityPassageRestBoundMu.lean:225`).

### Breakdown.Cert.CoerciveDensityPassageRestMeasurable

Measurability of each base, curl, and velocity remainder is lifted to the full mode remainder and the sum of its absolute approximation discrepancies.

**Paper context:** Appendix B, Proposition B.1: measurable ordinary-mode remainder sums.

**Theorem: Base density is measurable.** Under the stated hypotheses, the base density is measurable up to a null set. Source: `Breakdown.Coercive.Internal.DensityPassageRestMeasurable.aem_base_of` (`Breakdown/Cert/CoerciveDensityPassageRestMeasurable.lean:21`).

**Theorem: Curl-mode remainder is measurable.** Under the stated hypotheses, the curl-mode remainder is measurable up to a null set. Source: `Breakdown.Coercive.Internal.DensityPassageRestMeasurable.aem_epsRest_of` (`Breakdown/Cert/CoerciveDensityPassageRestMeasurable.lean:44`).

**Theorem: Velocity-mode remainder is measurable.** Under the stated hypotheses, the velocity-mode remainder is measurable up to a null set. Source: `Breakdown.Coercive.Internal.DensityPassageRestMeasurable.aem_muRest_of` (`Breakdown/Cert/CoerciveDensityPassageRestMeasurable.lean:80`).

**Theorem: Total mode remainder is measurable.** Under the stated hypotheses, the total mode remainder is measurable up to a null set. Source: `Breakdown.Coercive.Internal.DensityPassageRestMeasurable.aem_modeRest_of` (`Breakdown/Cert/CoerciveDensityPassageRestMeasurable.lean:110`).

**Theorem: Measurable remainder discrepancies.** Under the stated hypotheses, the sum of absolute mode-remainder discrepancies is measurable up to a null set. Source: `Breakdown.Coercive.Internal.DensityPassageRestMeasurable.rest_difference_aemeasurable` (`Breakdown/Cert/CoerciveDensityPassageRestMeasurable.lean:119`).

### Breakdown.Cert.CoerciveEnergyIdentityStretch

The stretching contribution is expanded into curl coordinates and integrated by parts, separating the background-gradient and background-Hessian terms.

**Paper context:** Appendix B, Proposition B.1: the stretching term in the smooth energy identity.

**Theorem: A coordinate formula for curl.** A curl coordinate equals the alternating contraction of the gradient-matrix coordinates. Source: `Breakdown.Coercive.EnergyIdentityInternal.curlVec_apply` (`Breakdown/Cert/CoerciveEnergyIdentityStretch.lean:14`).

**Theorem: Differentiate a scalar product.** The directional derivative of a product equals the sum of the two product-rule terms. Source: `Breakdown.Coercive.EnergyIdentityInternal.mul_deriv` (`Breakdown/Cert/CoerciveEnergyIdentityStretch.lean:18`).

**Theorem: Curl as a linear contraction.** Each curl coordinate is the corresponding coordinate projection composed with the continuous linear curl contraction of the gradient. Source: `Breakdown.Coercive.EnergyIdentityInternal.curl_comp_eq` (`Breakdown/Cert/CoerciveEnergyIdentityStretch.lean:25`).

**Theorem: The curl coordinate has Cⁿ regularity.** The selected curl coordinate has n continuous derivatives under the stated regularity hypothesis on the original vector field. Source: `Breakdown.Coercive.EnergyIdentityInternal.curl_contDiff` (`Breakdown/Cert/CoerciveEnergyIdentityStretch.lean:29`).

**Theorem: Curl vector has compact support.** Under the stated hypotheses, the curl vector has compact support. Source: `Breakdown.Coercive.EnergyIdentityInternal.curl_support` (`Breakdown/Cert/CoerciveEnergyIdentityStretch.lean:34`).

**Theorem: Differentiate the curl contraction.** The derivative of a curl coordinate is the alternating-symbol contraction of the corresponding second derivatives. Source: `Breakdown.Coercive.EnergyIdentityInternal.curl_deriv` (`Breakdown/Cert/CoerciveEnergyIdentityStretch.lean:39`).

**Theorem: Second derivatives are symmetric.** Under the stated smoothness hypothesis, the second derivative is unchanged when its two directions are interchanged. Source: `Breakdown.Coercive.EnergyIdentityInternal.d2_symm_two` (`Breakdown/Cert/CoerciveEnergyIdentityStretch.lean:49`).

**Theorem: Integrate a finite sum by parts.** The integral of the finite sum of products with derivatives equals the negative integral with each derivative transferred to the first factor. Source: `Breakdown.Coercive.EnergyIdentityInternal.ibp_sum` (`Breakdown/Cert/CoerciveEnergyIdentityStretch.lean:53`).

**Theorem: Alternating symbol at (0, 0, 0).** The alternating symbol at (0, 0, 0) equals 0. Source: `Breakdown.Coercive.EnergyIdentityInternal.eps_000` (`Breakdown/Cert/CoerciveEnergyIdentityStretch.lean:72`).

**Theorem: Alternating symbol at (0, 0, 1).** The alternating symbol at (0, 0, 1) equals 0. Source: `Breakdown.Coercive.EnergyIdentityInternal.eps_001` (`Breakdown/Cert/CoerciveEnergyIdentityStretch.lean:73`).

**Theorem: Alternating symbol at (0, 0, 2).** The alternating symbol at (0, 0, 2) equals 0. Source: `Breakdown.Coercive.EnergyIdentityInternal.eps_002` (`Breakdown/Cert/CoerciveEnergyIdentityStretch.lean:74`).

**Theorem: Alternating symbol at (0, 1, 0).** The alternating symbol at (0, 1, 0) equals 0. Source: `Breakdown.Coercive.EnergyIdentityInternal.eps_010` (`Breakdown/Cert/CoerciveEnergyIdentityStretch.lean:75`).

**Theorem: Alternating symbol at (0, 1, 1).** The alternating symbol at (0, 1, 1) equals 0. Source: `Breakdown.Coercive.EnergyIdentityInternal.eps_011` (`Breakdown/Cert/CoerciveEnergyIdentityStretch.lean:76`).

**Theorem: Alternating symbol at (0, 1, 2).** The alternating symbol at (0, 1, 2) equals 1. Source: `Breakdown.Coercive.EnergyIdentityInternal.eps_012` (`Breakdown/Cert/CoerciveEnergyIdentityStretch.lean:77`).

**Theorem: Alternating symbol at (0, 2, 0).** The alternating symbol at (0, 2, 0) equals 0. Source: `Breakdown.Coercive.EnergyIdentityInternal.eps_020` (`Breakdown/Cert/CoerciveEnergyIdentityStretch.lean:78`).

**Theorem: Alternating symbol at (0, 2, 1).** The alternating symbol at (0, 2, 1) equals -1. Source: `Breakdown.Coercive.EnergyIdentityInternal.eps_021` (`Breakdown/Cert/CoerciveEnergyIdentityStretch.lean:79`).

**Theorem: Alternating symbol at (0, 2, 2).** The alternating symbol at (0, 2, 2) equals 0. Source: `Breakdown.Coercive.EnergyIdentityInternal.eps_022` (`Breakdown/Cert/CoerciveEnergyIdentityStretch.lean:80`).

**Theorem: Alternating symbol at (1, 0, 0).** The alternating symbol at (1, 0, 0) equals 0. Source: `Breakdown.Coercive.EnergyIdentityInternal.eps_100` (`Breakdown/Cert/CoerciveEnergyIdentityStretch.lean:81`).

**Theorem: Alternating symbol at (1, 0, 1).** The alternating symbol at (1, 0, 1) equals 0. Source: `Breakdown.Coercive.EnergyIdentityInternal.eps_101` (`Breakdown/Cert/CoerciveEnergyIdentityStretch.lean:82`).

**Theorem: Alternating symbol at (1, 0, 2).** The alternating symbol at (1, 0, 2) equals -1. Source: `Breakdown.Coercive.EnergyIdentityInternal.eps_102` (`Breakdown/Cert/CoerciveEnergyIdentityStretch.lean:83`).

**Theorem: Alternating symbol at (1, 1, 0).** The alternating symbol at (1, 1, 0) equals 0. Source: `Breakdown.Coercive.EnergyIdentityInternal.eps_110` (`Breakdown/Cert/CoerciveEnergyIdentityStretch.lean:84`).

**Theorem: Alternating symbol at (1, 1, 1).** The alternating symbol at (1, 1, 1) equals 0. Source: `Breakdown.Coercive.EnergyIdentityInternal.eps_111` (`Breakdown/Cert/CoerciveEnergyIdentityStretch.lean:85`).

**Theorem: Alternating symbol at (1, 1, 2).** The alternating symbol at (1, 1, 2) equals 0. Source: `Breakdown.Coercive.EnergyIdentityInternal.eps_112` (`Breakdown/Cert/CoerciveEnergyIdentityStretch.lean:86`).

**Theorem: Alternating symbol at (1, 2, 0).** The alternating symbol at (1, 2, 0) equals 1. Source: `Breakdown.Coercive.EnergyIdentityInternal.eps_120` (`Breakdown/Cert/CoerciveEnergyIdentityStretch.lean:87`).

**Theorem: Alternating symbol at (1, 2, 1).** The alternating symbol at (1, 2, 1) equals 0. Source: `Breakdown.Coercive.EnergyIdentityInternal.eps_121` (`Breakdown/Cert/CoerciveEnergyIdentityStretch.lean:88`).

**Theorem: Alternating symbol at (1, 2, 2).** The alternating symbol at (1, 2, 2) equals 0. Source: `Breakdown.Coercive.EnergyIdentityInternal.eps_122` (`Breakdown/Cert/CoerciveEnergyIdentityStretch.lean:89`).

**Theorem: Alternating symbol at (2, 0, 0).** The alternating symbol at (2, 0, 0) equals 0. Source: `Breakdown.Coercive.EnergyIdentityInternal.eps_200` (`Breakdown/Cert/CoerciveEnergyIdentityStretch.lean:90`).

**Theorem: Alternating symbol at (2, 0, 1).** The alternating symbol at (2, 0, 1) equals 1. Source: `Breakdown.Coercive.EnergyIdentityInternal.eps_201` (`Breakdown/Cert/CoerciveEnergyIdentityStretch.lean:91`).

**Theorem: Alternating symbol at (2, 0, 2).** The alternating symbol at (2, 0, 2) equals 0. Source: `Breakdown.Coercive.EnergyIdentityInternal.eps_202` (`Breakdown/Cert/CoerciveEnergyIdentityStretch.lean:92`).

**Theorem: Alternating symbol at (2, 1, 0).** The alternating symbol at (2, 1, 0) equals -1. Source: `Breakdown.Coercive.EnergyIdentityInternal.eps_210` (`Breakdown/Cert/CoerciveEnergyIdentityStretch.lean:93`).

**Theorem: Alternating symbol at (2, 1, 1).** The alternating symbol at (2, 1, 1) equals 0. Source: `Breakdown.Coercive.EnergyIdentityInternal.eps_211` (`Breakdown/Cert/CoerciveEnergyIdentityStretch.lean:94`).

**Theorem: Alternating symbol at (2, 1, 2).** The alternating symbol at (2, 1, 2) equals 0. Source: `Breakdown.Coercive.EnergyIdentityInternal.eps_212` (`Breakdown/Cert/CoerciveEnergyIdentityStretch.lean:95`).

**Theorem: Alternating symbol at (2, 2, 0).** The alternating symbol at (2, 2, 0) equals 0. Source: `Breakdown.Coercive.EnergyIdentityInternal.eps_220` (`Breakdown/Cert/CoerciveEnergyIdentityStretch.lean:96`).

**Theorem: Alternating symbol at (2, 2, 1).** The alternating symbol at (2, 2, 1) equals 0. Source: `Breakdown.Coercive.EnergyIdentityInternal.eps_221` (`Breakdown/Cert/CoerciveEnergyIdentityStretch.lean:97`).

**Theorem: Alternating symbol at (2, 2, 2).** The alternating symbol at (2, 2, 2) equals 0. Source: `Breakdown.Coercive.EnergyIdentityInternal.eps_222` (`Breakdown/Cert/CoerciveEnergyIdentityStretch.lean:98`).

**Theorem: Differentiate the divergence constraint.** The coordinate contraction obtained by differentiating the zero divergence is zero. Source: `Breakdown.Coercive.EnergyIdentityInternal.div_deriv_zero_two` (`Breakdown/Cert/CoerciveEnergyIdentityStretch.lean:100`).

**Theorem: The negative Laplacian is curl of curl.** For the stated divergence-free smooth field, each negative Laplacian coordinate equals the corresponding curl-of-curl contraction. Source: `Breakdown.Coercive.EnergyIdentityInternal.ssp_curl` (`Breakdown/Cert/CoerciveEnergyIdentityStretch.lean:123`).

**Theorem: Differentiate linear convection.** The derivative of the two linear-convection terms expands by the product rule into four first- and second-derivative terms. Source: `Breakdown.Coercive.EnergyIdentityInternal.A_deriv` (`Breakdown/Cert/CoerciveEnergyIdentityStretch.lean:142`).

**Theorem: Convection derivative in coordinates.** Each coordinate derivative of linear convection equals the displayed finite sum of profile and perturbation jets. Source: `Breakdown.Coercive.EnergyIdentityInternal.A_deriv_jets` (`Breakdown/Cert/CoerciveEnergyIdentityStretch.lean:157`).

**Theorem: Expand the convection curl pairing.** The alternating coordinate contraction of the convection derivative expands into the displayed vorticity-gradient and strain terms. Source: `Breakdown.Coercive.EnergyIdentityInternal.curl_grad_point` (`Breakdown/Cert/CoerciveEnergyIdentityStretch.lean:174`).

**Theorem: Compact support gives a vanishing radius.** There is a radius outside which the compactly supported field vanishes. Source: `Breakdown.Coercive.EnergyIdentityInternal.vanish_radius` (`Breakdown/Cert/CoerciveEnergyIdentityStretch.lean:208`).

**Theorem: Differentiate a constant multiple.** The directional derivative of a constant multiple is the same constant times the directional derivative. Source: `Breakdown.Coercive.EnergyIdentityInternal.const_mul_deriv` (`Breakdown/Cert/CoerciveEnergyIdentityStretch.lean:217`).

**Theorem: Differentiate a scaled product.** The directional derivative of a constant times a product is the constant times the two product-rule terms. Source: `Breakdown.Coercive.EnergyIdentityInternal.cmul_deriv` (`Breakdown/Cert/CoerciveEnergyIdentityStretch.lean:222`).

**Theorem: Expand the vorticity interaction.** The vorticity-gradient contraction is rewritten as a sum over four coordinate indices using the alternating symbol. Source: `Breakdown.Coercive.EnergyIdentityInternal.x_split` (`Breakdown/Cert/CoerciveEnergyIdentityStretch.lean:231`).

**Theorem: Expand the differentiated interaction.** The differentiated four-index vorticity expression expands into its first- and second-derivative product terms. Source: `Breakdown.Coercive.EnergyIdentityInternal.x_expand` (`Breakdown/Cert/CoerciveEnergyIdentityStretch.lean:242`).

**Theorem: Rearrange the second interaction term.** The four-index derivative expression rearranges into the displayed vorticity and perturbation-gradient contractions. Source: `Breakdown.Coercive.EnergyIdentityInternal.y_point` (`Breakdown/Cert/CoerciveEnergyIdentityStretch.lean:266`).

**Theorem: A compact factor gives compact support.** A constant times the product of the stated functions has compact support when the supplied factor does. Source: `Breakdown.Coercive.EnergyIdentityInternal.cmul_support_right` (`Breakdown/Cert/CoerciveEnergyIdentityStretch.lean:289`).

**Theorem: Compact support of constant multiples.** Multiplying a compactly supported function by a real constant preserves compact support. Source: `Breakdown.Coercive.EnergyIdentityInternal.cmul_support_one` (`Breakdown/Cert/CoerciveEnergyIdentityStretch.lean:294`).

**Theorem: The weighted product is C¹.** A constant times the product of the stated continuously differentiable functions is continuously differentiable. Source: `Breakdown.Coercive.EnergyIdentityInternal.cmul_contDiff` (`Breakdown/Cert/CoerciveEnergyIdentityStretch.lean:299`).

**Theorem: A constant multiple is C¹.** Multiplying the stated continuously differentiable function by a real constant preserves continuous differentiability. Source: `Breakdown.Coercive.EnergyIdentityInternal.cmul_contDiff_one` (`Breakdown/Cert/CoerciveEnergyIdentityStretch.lean:303`).

**Theorem: Integrate the mixed stretching term.** Integration by parts identifies the mixed vorticity interaction with the stated half-weighted second-derivative contraction. Source: `Breakdown.Coercive.EnergyIdentityInternal.x_term` (`Breakdown/Cert/CoerciveEnergyIdentityStretch.lean:306`).

**Theorem: The convection field is C¹.** The sum of the perturbation derivative acting on the background and the background derivative acting on the perturbation is continuously differentiable. Source: `Breakdown.Coercive.EnergyIdentityInternal.A_contDiff` (`Breakdown/Cert/CoerciveEnergyIdentityStretch.lean:391`).

**Theorem: The convection field has compact support.** The sum of the perturbation derivative acting on the background and the background derivative acting on the perturbation has compact support. Source: `Breakdown.Coercive.EnergyIdentityInternal.A_support` (`Breakdown/Cert/CoerciveEnergyIdentityStretch.lean:396`).

**Theorem: Convection paired with the Laplacian.** Pairing linear convection with the negative Laplacian gives the integrated strain and vorticity-gradient stretching expression. Source: `Breakdown.Coercive.EnergyIdentityInternal.stretch_identity` (`Breakdown/Cert/CoerciveEnergyIdentityStretch.lean:406`).

**Theorem: The stretching identity on one slice.** The linear-convection pairing with the negative second-derivative trace equals the integral of the stretching form on that time slice. Source: `Breakdown.Coercive.EnergyIdentityInternal.slice_stretch` (`Breakdown/Cert/CoerciveEnergyIdentityStretch.lean:524`).

### Breakdown.Cert.CoerciveEnergyIdentityTools

Smooth compact tests, coordinate derivative identities, and period integration justify the scalar transport, zero-divergence cancellation, and Laplacian-versus-curl energy calculations.

**Paper context:** Appendix B, Proposition B.1: analytic identities underlying the smooth energy calculation.

**Theorem: Smooth fields have smooth spatial slices.** Every spatial slice of the stated smooth space-time field is smooth. Source: `Breakdown.Coercive.EnergyIdentityInternal.slice_smooth` (`Breakdown/Cert/CoerciveEnergyIdentityTools.lean:14`).

**Theorem: One vanishing radius for all times.** The periodic test field vanishes outside a common spatial radius at every time. Source: `Breakdown.Coercive.EnergyIdentityInternal.slice_vanish` (`Breakdown/Cert/CoerciveEnergyIdentityTools.lean:18`).

**Theorem: Function f has compact support.** Under the stated hypotheses, the function f has compact support. Source: `Breakdown.Coercive.EnergyIdentityInternal.compact_of_vanish` (`Breakdown/Cert/CoerciveEnergyIdentityTools.lean:22`).

**Theorem: Vanish locally outside the support.** The field is identically zero on a neighbourhood of the given point outside its support. Source: `Breakdown.Coercive.EnergyIdentityInternal.vanish_open` (`Breakdown/Cert/CoerciveEnergyIdentityTools.lean:28`).

**Theorem: Derivative outside a common support ball.** The derivative vanishes beyond every radius outside which the original function vanishes. Source: `Breakdown.Coercive.EnergyIdentityInternal.fderiv_vanish` (`Breakdown/Cert/CoerciveEnergyIdentityTools.lean:33`).

**Theorem: Differentiate through a linear map.** Differentiation of a fixed continuous linear map applied to a function composes that map with the function's derivative. Source: `Breakdown.Coercive.EnergyIdentityInternal.fderiv_clm_left` (`Breakdown/Cert/CoerciveEnergyIdentityTools.lean:39`).

**Theorem: Differentiate a vector coordinate.** The derivative of a vector coordinate is the corresponding coordinate of the vector derivative. Source: `Breakdown.Coercive.EnergyIdentityInternal.fderiv_component` (`Breakdown/Cert/CoerciveEnergyIdentityTools.lean:44`).

**Theorem: Read a second derivative by coordinates.** Differentiating a scalar first-derivative coordinate gives the matching coordinate of the second vector derivative. Source: `Breakdown.Coercive.EnergyIdentityInternal.fderiv_second_component` (`Breakdown/Cert/CoerciveEnergyIdentityTools.lean:51`).

**Theorem: Transfer a coordinate derivative.** The integral of a product with a coordinate derivative equals the negative integral with the derivative on the other factor. Source: `Breakdown.Coercive.EnergyIdentityInternal.ibp` (`Breakdown/Cert/CoerciveEnergyIdentityTools.lean:66`).

**Theorem: Curl vector preserves addition.** Under the stated hypotheses, the curl vector commutes with addition. Source: `Breakdown.Coercive.EnergyIdentityInternal.curlVec_add` (`Breakdown/Cert/CoerciveEnergyIdentityTools.lean:82`).

**Theorem: Curl vector preserves scaling.** Under the stated hypotheses, the curl vector commutes with scalar multiplication. Source: `Breakdown.Coercive.EnergyIdentityInternal.curlVec_smul` (`Breakdown/Cert/CoerciveEnergyIdentityTools.lean:86`).

**Definition: Curl as a linear map.** Package the alternating contraction of a gradient matrix as a linear map. Source: `Breakdown.Coercive.EnergyIdentityInternal.curlLinear` (`Breakdown/Cert/CoerciveEnergyIdentityTools.lean:91`).

**Definition: Curl as a continuous linear map.** Equip the linear curl contraction with its continuous-linear-map structure. Source: `Breakdown.Coercive.EnergyIdentityInternal.curlCLM` (`Breakdown/Cert/CoerciveEnergyIdentityTools.lean:96`).

**Theorem: Read the continuous curl map.** Applying the continuous linear curl map returns the usual curl contraction of the gradient matrix. Source: `Breakdown.Coercive.EnergyIdentityInternal.curlCLM_apply` (`Breakdown/Cert/CoerciveEnergyIdentityTools.lean:98`).

**Theorem: Common support for derivative fields.** The test field and the listed first, second, and curl derivatives vanish beyond the same support radius. Source: `Breakdown.Coercive.EnergyIdentityInternal.slice_facts_of` (`Breakdown/Cert/CoerciveEnergyIdentityTools.lean:100`).

**Theorem: Continuous spatial derivatives.** The stated test slice and its listed spatial derivative and curl fields are continuous. Source: `Breakdown.Coercive.EnergyIdentityInternal.slice_continuous` (`Breakdown/Cert/CoerciveEnergyIdentityTools.lean:109`).

**Theorem: Integral is integrable.** Under the stated hypotheses, the integral is integrable on the stated set. Source: `Breakdown.Coercive.EnergyIdentityInternal.sigma_integrable` (`Breakdown/Cert/CoerciveEnergyIdentityTools.lean:119`).

**Theorem: Extract the joint spatial derivative.** The spatial derivative is the joint space-time derivative composed with the spatial inclusion. Source: `Breakdown.Coercive.EnergyIdentityInternal.space_fderiv_eq` (`Breakdown/Cert/CoerciveEnergyIdentityTools.lean:144`).

**Theorem: The spatial derivative has Cⁿ regularity.** The spatial derivative field has n continuous derivatives as a joint space-time function under the stated extra regularity hypothesis. Source: `Breakdown.Coercive.EnergyIdentityInternal.joint_partial` (`Breakdown/Cert/CoerciveEnergyIdentityTools.lean:150`).

**Theorem: Extract the joint time derivative.** The time derivative equals the joint space-time derivative applied to the time unit direction. Source: `Breakdown.Coercive.EnergyIdentityInternal.time_deriv_eq` (`Breakdown/Cert/CoerciveEnergyIdentityTools.lean:161`).

**Theorem: Continuity of the space-time derivatives.** The field and its listed temporal, spatial, and curl derivatives are jointly continuous. Source: `Breakdown.Coercive.EnergyIdentityInternal.joint_continuous` (`Breakdown/Cert/CoerciveEnergyIdentityTools.lean:169`).

**Theorem: Continuity of profile derivatives.** The profile and its first two spatial derivatives are jointly continuous. Source: `Breakdown.Coercive.EnergyIdentityInternal.joint_continuous_weight` (`Breakdown/Cert/CoerciveEnergyIdentityTools.lean:191`).

**Theorem: Smooth coordinate partial derivatives.** Under the stated hypotheses, the coordinate partial derivative of the field is smooth. Source: `Breakdown.Coercive.EnergyIdentityInternal.d1_smooth` (`Breakdown/Cert/CoerciveEnergyIdentityTools.lean:202`).

**Theorem: Compact support of coordinate partials.** Under the stated hypotheses, the coordinate partial derivative of the field has compact support. Source: `Breakdown.Coercive.EnergyIdentityInternal.d1_support` (`Breakdown/Cert/CoerciveEnergyIdentityTools.lean:208`).

**Theorem: Smooth coordinates of vector fields.** Every coordinate of the stated smooth vector field is smooth. Source: `Breakdown.Coercive.EnergyIdentityInternal.comp_smooth` (`Breakdown/Cert/CoerciveEnergyIdentityTools.lean:213`).

**Theorem: Coordinates retain compact support.** Each coordinate of the stated compactly supported vector field has compact support. Source: `Breakdown.Coercive.EnergyIdentityInternal.comp_support` (`Breakdown/Cert/CoerciveEnergyIdentityTools.lean:218`).

**Theorem: Read a second derivative by coordinates.** Differentiating a scalar first-derivative coordinate gives the matching coordinate of the second vector derivative. Source: `Breakdown.Coercive.EnergyIdentityInternal.d2_eq` (`Breakdown/Cert/CoerciveEnergyIdentityTools.lean:223`).

**Theorem: Second derivatives are symmetric.** Under the stated smoothness hypothesis, the second derivative is unchanged when its two directions are interchanged. Source: `Breakdown.Coercive.EnergyIdentityInternal.d2_symm` (`Breakdown/Cert/CoerciveEnergyIdentityTools.lean:235`).

**Theorem: Differentiate the divergence constraint.** The coordinate contraction obtained by differentiating the zero divergence is zero. Source: `Breakdown.Coercive.EnergyIdentityInternal.div_deriv_zero` (`Breakdown/Cert/CoerciveEnergyIdentityTools.lean:239`).

**Theorem: Function f is integrable.** Under the stated hypotheses, the function f is integrable. Source: `Breakdown.Coercive.EnergyIdentityInternal.cont_intg` (`Breakdown/Cert/CoerciveEnergyIdentityTools.lean:258`).

**Theorem: Order one lies below infinity.** The differentiability order one lies below the infinite order. Source: `Breakdown.Coercive.EnergyIdentityInternal.one_le_inf` (`Breakdown/Cert/CoerciveEnergyIdentityTools.lean:261`).

**Theorem: The integrated cross term vanishes.** The integral of the transposed gradient contraction is zero for the stated compact divergence-free field. Source: `Breakdown.Coercive.EnergyIdentityInternal.cross_zero` (`Breakdown/Cert/CoerciveEnergyIdentityTools.lean:263`).

**Theorem: Smooth scalar coordinate partials.** Under the stated hypotheses, the coordinate partial derivative of the scalar function is smooth. Source: `Breakdown.Coercive.EnergyIdentityInternal.sd1_smooth` (`Breakdown/Cert/CoerciveEnergyIdentityTools.lean:296`).

**Theorem: Mixed scalar partials commute.** The two mixed scalar coordinate derivatives agree under the stated smoothness hypothesis. Source: `Breakdown.Coercive.EnergyIdentityInternal.s_symm` (`Breakdown/Cert/CoerciveEnergyIdentityTools.lean:300`).

**Theorem: Differentiate a coordinate product.** The derivative of a coordinate times a scalar function is the coordinate product rule. Source: `Breakdown.Coercive.EnergyIdentityInternal.coord_mul_deriv` (`Breakdown/Cert/CoerciveEnergyIdentityTools.lean:313`).

**Theorem: Integrate radial transport by parts.** The integral of a coordinate times a function times its derivative is minus one half of the function's square integral. Source: `Breakdown.Coercive.EnergyIdentityInternal.radial_term` (`Breakdown/Cert/CoerciveEnergyIdentityTools.lean:324`).

**Theorem: Transport gives negative quarter energy.** Pairing scalar similarity transport with a second coordinate derivative gives minus one quarter of the corresponding derivative-square integral. Source: `Breakdown.Coercive.EnergyIdentityInternal.scalar_transport` (`Breakdown/Cert/CoerciveEnergyIdentityTools.lean:347`).

**Theorem: The curl square in coordinates.** The curl norm square is the sum of all gradient-coordinate squares minus the transposed-coordinate contraction. Source: `Breakdown.Coercive.EnergyIdentityInternal.curl_sq` (`Breakdown/Cert/CoerciveEnergyIdentityTools.lean:422`).

**Theorem: The inner product in coordinates.** The Euclidean inner product equals the sum of the coordinatewise products. Source: `Breakdown.Coercive.EnergyIdentityInternal.inner_coord` (`Breakdown/Cert/CoerciveEnergyIdentityTools.lean:429`).

**Theorem: Evaluate a linear map by coordinates.** A coordinate of a linear map applied to a vector is the coordinate-weighted sum of its columns. Source: `Breakdown.Coercive.EnergyIdentityInternal.apply_self` (`Breakdown/Cert/CoerciveEnergyIdentityTools.lean:432`).

**Theorem: Swap two derivatives under the integral.** The two mixed products of coordinate derivatives have equal integrals under the stated support and smoothness hypotheses. Source: `Breakdown.Coercive.EnergyIdentityInternal.swap_ibp` (`Breakdown/Cert/CoerciveEnergyIdentityTools.lean:437`).

**Theorem: Laplacian square equals Hessian energy.** The integrated square of the scalar Laplacian equals the sum of the integrated squared second partials. Source: `Breakdown.Coercive.EnergyIdentityInternal.sumSecondPartials_scalar` (`Breakdown/Cert/CoerciveEnergyIdentityTools.lean:454`).

**Theorem: Differentiate time through the joint map.** The time slice has derivative given by the joint derivative applied to the time unit direction. Source: `Breakdown.Coercive.EnergyIdentityInternal.time_hasDeriv` (`Breakdown/Cert/CoerciveEnergyIdentityTools.lean:481`).

**Theorem: Time and space differentiation commute.** The spatial derivative of the time derivative equals the time derivative of the spatial derivative under the stated regularity. Source: `Breakdown.Coercive.EnergyIdentityInternal.mixed_partial` (`Breakdown/Cert/CoerciveEnergyIdentityTools.lean:488`).

**Theorem: Function f is integrable.** Under the stated hypotheses, the function f is integrable. Source: `Breakdown.Coercive.EnergyIdentityInternal.prod_integrable` (`Breakdown/Cert/CoerciveEnergyIdentityTools.lean:520`).

**Theorem: Periodic time derivatives integrate to 0.** The period integral of a scalar field times its time derivative vanishes. Source: `Breakdown.Coercive.EnergyIdentityInternal.period_term` (`Breakdown/Cert/CoerciveEnergyIdentityTools.lean:543`).

**Theorem: Zero divergence cancels transport.** The integral of a scalar field times its derivative along the divergence-free background field is zero. Source: `Breakdown.Coercive.EnergyIdentityInternal.transport_zero` (`Breakdown/Cert/CoerciveEnergyIdentityTools.lean:573`).

**Theorem: Similarity transport gives curl energy.** Pairing the half-velocity and half-radial-derivative terms with the negative Laplacian gives one quarter of the curl energy. Source: `Breakdown.Coercive.EnergyIdentityInternal.slice_transport` (`Breakdown/Cert/CoerciveEnergyIdentityTools.lean:618`).

**Theorem: Laplacian and curl-gradient energies.** The squared Laplacian pairing equals the integral of the curl-gradient square for the stated divergence-free smooth slice. Source: `Breakdown.Coercive.EnergyIdentityInternal.slice_sumSecondPartials` (`Breakdown/Cert/CoerciveEnergyIdentityTools.lean:680`).

### Breakdown.Cert.CoerciveField

The ordinary mode pairing is shown to be a bounded linear functional on periodic solenoidal tests, giving a multiplier field with an explicit norm bound.

**Paper context:** Appendix B, Proposition B.1: existence and norm control of the ordinary multiplier field.

**Definition: Mode contribution to the multiplier.** Sum the time-space integrals of the signed curl and velocity mode pairings. Source: `Breakdown.Coercive.Internal.Field.fieldModeSum` (`Breakdown/Cert/CoerciveField.lean:19`).

**Definition: The variational multiplier pairing.** Add the negative second-derivative trace pairing to the sum of curl and velocity mode contributions. Source: `Breakdown.Coercive.Internal.Field.fieldPairing` (`Breakdown/Cert/CoerciveField.lean:26`).

**Definition: Volume over one time period.** Use the product of volume on the closed unit time interval and spatial volume. Source: `Breakdown.Coercive.Internal.Field.periodMeasure` (`Breakdown/Cert/CoerciveField.lean:31`).

**Definition: The period gradient norm.** Take the square root of the period integral of the squared gradient-matrix norm. Source: `Breakdown.Coercive.Internal.Field.fieldGradNorm` (`Breakdown/Cert/CoerciveField.lean:34`).

**Theorem: Add periodic test fields.** The sum of two periodic solenoidal test fields is again a periodic solenoidal test field. Source: `Breakdown.Coercive.Internal.Field.testField_add` (`Breakdown/Cert/CoerciveField.lean:37`).

**Theorem: Scale a periodic test field.** A real scalar multiple of a periodic solenoidal test field remains a periodic solenoidal test field. Source: `Breakdown.Coercive.Internal.Field.testField_smul` (`Breakdown/Cert/CoerciveField.lean:63`).

**Theorem: Perturbations have finite frequency norm.** The squared frequency seminorm of the stated weak perturbation is finite. Source: `Breakdown.Coercive.Internal.Field.frequencySeminormSq_lt_top_of_perturbation` (`Breakdown/Cert/CoerciveField.lean:85`).

**Theorem: Axial rotation is continuous.** Under the stated hypotheses, the axial rotation is continuous. Source: `Breakdown.Coercive.Internal.Field.axialRot_comp_continuous` (`Breakdown/Cert/CoerciveField.lean:159`).

**Theorem: Axial rotation preserves addition.** Under the stated hypotheses, the axial rotation commutes with addition. Source: `Breakdown.Coercive.Internal.Field.axialRot_add` (`Breakdown/Cert/CoerciveField.lean:164`).

**Theorem: Fourier mode average preserves addition.** Under the stated hypotheses, the Fourier mode average commutes with addition. Source: `Breakdown.Coercive.Internal.Field.modeAverage_add` (`Breakdown/Cert/CoerciveField.lean:168`).

**Theorem: Velocity orbit coordinate is continuous.** Under the stated hypotheses, the velocity orbit coordinate is continuous. Source: `Breakdown.Coercive.Internal.Field.mode_integrand_continuous` (`Breakdown/Cert/CoerciveField.lean:199`).

**Theorem: Velocity mode preserves addition.** Under the stated hypotheses, the velocity mode commutes with addition. Source: `Breakdown.Coercive.Internal.Field.modeVel_add` (`Breakdown/Cert/CoerciveField.lean:210`).

**Theorem: Gradient field is continuous.** Under the stated hypotheses, the gradient field is continuous. Source: `Breakdown.Coercive.Internal.Field.gradField_continuous` (`Breakdown/Cert/CoerciveField.lean:221`).

**Theorem: Gradient field preserves addition.** Under the stated hypotheses, the gradient field commutes with addition. Source: `Breakdown.Coercive.Internal.Field.gradField_add` (`Breakdown/Cert/CoerciveField.lean:241`).

**Theorem: Gradient mode preserves addition.** Under the stated hypotheses, the gradient mode commutes with addition. Source: `Breakdown.Coercive.Internal.Field.modeGrad_add` (`Breakdown/Cert/CoerciveField.lean:249`).

**Theorem: Curl mode preserves addition.** Under the stated hypotheses, the curl extracted from a gradient commutes with addition. Source: `Breakdown.Coercive.Internal.Field.curlOfGrad_add` (`Breakdown/Cert/CoerciveField.lean:271`).

**Theorem: Add in the second complex pairing slot.** The complex coordinate pairing distributes over addition in its second argument. Source: `Breakdown.Coercive.Internal.Field.cdot_add_right` (`Breakdown/Cert/CoerciveField.lean:276`).

**Definition: A signed curl pairing.** Take the real part of i times the signed curl weight times the complex curl-mode pairing. Source: `Breakdown.Coercive.Internal.Field.termEps` (`Breakdown/Cert/CoerciveField.lean:279`).

**Definition: A signed velocity pairing.** Take the real part of i times the signed velocity weight times the complex velocity-mode pairing. Source: `Breakdown.Coercive.Internal.Field.termMu` (`Breakdown/Cert/CoerciveField.lean:284`).

**Theorem: Expand the multiplier mode sum.** The multiplier mode sum equals the series of integrated curl and velocity pairing terms. Source: `Breakdown.Coercive.Internal.Field.fieldModeSum_eq` (`Breakdown/Cert/CoerciveField.lean:288`).

**Theorem: Curl pairing term preserves addition.** Under the stated hypotheses, the curl pairing term commutes with addition. Source: `Breakdown.Coercive.Internal.Field.termEps_add` (`Breakdown/Cert/CoerciveField.lean:293`).

**Theorem: Velocity pairing term preserves addition.** Under the stated hypotheses, the velocity pairing term commutes with addition. Source: `Breakdown.Coercive.Internal.Field.termMu_add` (`Breakdown/Cert/CoerciveField.lean:301`).

**Theorem: Signed curl weight is continuous.** Under the stated hypotheses, the signed curl weight is continuous. Source: `Breakdown.Coercive.Internal.Field.epsW_continuous` (`Breakdown/Cert/CoerciveField.lean:308`).

**Theorem: Signed velocity weight is continuous.** Under the stated hypotheses, the signed velocity weight is continuous. Source: `Breakdown.Coercive.Internal.Field.muW_continuous` (`Breakdown/Cert/CoerciveField.lean:314`).

**Theorem: A test sees only a bounded region.** The velocity pairing against the stated compact test is unchanged when the velocity is truncated to the supporting ball. Source: `Breakdown.Coercive.Internal.Field.termMu_ballPart` (`Breakdown/Cert/CoerciveField.lean:320`).

**Theorem: Test gradients have finite period energy.** The period integral of the squared coordinate-column norm of the test-field gradient is finite. Source: `Breakdown.Coercive.Internal.Field.gradField_matSq_lt_top` (`Breakdown/Cert/CoerciveField.lean:329`).

**Theorem: Curl pairing term is measurable.** Under the stated hypotheses, the curl pairing term is strongly measurable up to a null set. Source: `Breakdown.Coercive.Internal.Field.termEps_aestronglyMeasurable` (`Breakdown/Cert/CoerciveField.lean:340`).

**Theorem: Curl pairing term is integrable.** Under the stated hypotheses, the curl pairing term is integrable. Source: `Breakdown.Coercive.Internal.Field.termEps_integrable` (`Breakdown/Cert/CoerciveField.lean:357`).

**Theorem: Velocity pairing term is measurable.** Under the stated hypotheses, the velocity pairing term is strongly measurable up to a null set. Source: `Breakdown.Coercive.Internal.Field.termMu_aestronglyMeasurable` (`Breakdown/Cert/CoerciveField.lean:376`).

**Theorem: Velocity pairing term is integrable.** Under the stated hypotheses, the velocity pairing term is integrable. Source: `Breakdown.Coercive.Internal.Field.termMu_integrable` (`Breakdown/Cert/CoerciveField.lean:393`).

**Theorem: The combined mode term is integrable.** The sum of the curl and velocity multiplier terms is integrable over the period slab. Source: `Breakdown.Coercive.Internal.Field.fieldModeTerm_integrable` (`Breakdown/Cert/CoerciveField.lean:419`).

**Theorem: Curl pairing term is summable.** Under the stated hypotheses, the curl pairing term is summable over its index set. Source: `Breakdown.Coercive.Internal.Field.termEps_summable` (`Breakdown/Cert/CoerciveField.lean:431`).

**Theorem: Velocity pairing term is summable.** Under the stated hypotheses, the velocity pairing term is summable over its index set. Source: `Breakdown.Coercive.Internal.Field.termMu_summable` (`Breakdown/Cert/CoerciveField.lean:464`).

**Theorem: Summable integrated multiplier terms.** The integrals of the combined curl and velocity multiplier terms form a summable family over integer modes. Source: `Breakdown.Coercive.Internal.Field.fieldModeTerm_summable` (`Breakdown/Cert/CoerciveField.lean:495`).

**Theorem: Multiplier mode sum preserves addition.** Under the stated hypotheses, the sum of multiplier mode pairings commutes with addition. Source: `Breakdown.Coercive.Internal.Field.fieldModeSum_add` (`Breakdown/Cert/CoerciveField.lean:516`).

**Theorem: Axial rotation preserves scaling.** Under the stated hypotheses, the axial rotation commutes with scalar multiplication. Source: `Breakdown.Coercive.Internal.Field.axialRot_smul` (`Breakdown/Cert/CoerciveField.lean:559`).

**Theorem: Fourier mode average preserves scaling.** Under the stated hypotheses, the Fourier mode average commutes with multiplication by a constant. Source: `Breakdown.Coercive.Internal.Field.modeAverage_const_mul` (`Breakdown/Cert/CoerciveField.lean:563`).

**Theorem: Velocity mode preserves scaling.** Under the stated hypotheses, the velocity mode commutes with scalar multiplication. Source: `Breakdown.Coercive.Internal.Field.modeVel_smul` (`Breakdown/Cert/CoerciveField.lean:569`).

**Theorem: Gradient mode preserves scaling.** Under the stated hypotheses, the gradient mode commutes with scalar multiplication. Source: `Breakdown.Coercive.Internal.Field.modeGrad_smul` (`Breakdown/Cert/CoerciveField.lean:578`).

**Theorem: Gradient field preserves scaling.** Under the stated hypotheses, the gradient field commutes with scalar multiplication. Source: `Breakdown.Coercive.Internal.Field.gradField_smul` (`Breakdown/Cert/CoerciveField.lean:587`).

**Theorem: Curl respects scalar multiplication.** Multiplying every gradient coordinate by a real scalar multiplies its complex curl contraction by that scalar. Source: `Breakdown.Coercive.Internal.Field.curlOfGrad_smul` (`Breakdown/Cert/CoerciveField.lean:595`).

**Theorem: Scale the second complex pairing slot.** A real scalar factor in the second argument factors out of the complex coordinate pairing. Source: `Breakdown.Coercive.Internal.Field.cdot_smul_right` (`Breakdown/Cert/CoerciveField.lean:602`).

**Theorem: Multiplier mode sum preserves scaling.** Under the stated hypotheses, the sum of multiplier mode pairings commutes with scalar multiplication. Source: `Breakdown.Coercive.Internal.Field.fieldModeSum_smul` (`Breakdown/Cert/CoerciveField.lean:608`).

**Theorem: Strong measurability of test fields.** The joint space-time test field is strongly measurable up to a null set. Source: `Breakdown.Coercive.Internal.Field.testField_aestronglyMeasurable` (`Breakdown/Cert/CoerciveField.lean:635`).

**Theorem: Finite period L² for compact fields.** The stated continuous periodic field with uniform compact spatial support has finite squared energy over one time period. Source: `Breakdown.Coercive.Internal.Field.sq_lt_top_of_support` (`Breakdown/Cert/CoerciveField.lean:639`).

**Theorem: Test fields have finite period L² energy.** The squared norm of the stated periodic test field has finite integral over one period. Source: `Breakdown.Coercive.Internal.Field.testField_sq_lt_top` (`Breakdown/Cert/CoerciveField.lean:669`).

**Theorem: The period slab as a restricted measure.** The period product measure equals space-time volume restricted to the unit time slab. Source: `Breakdown.Coercive.Internal.Field.period_measure_eq` (`Breakdown/Cert/CoerciveField.lean:674`).

**Theorem: Integrate directly over the period slab.** The iterated nonnegative period integral equals the integral over the period product measure. Source: `Breakdown.Coercive.Internal.Field.periodLIntegral_eq_prod` (`Breakdown/Cert/CoerciveField.lean:679`).

**Theorem: Second-derivative trace is continuous.** Under the stated hypotheses, the second-derivative trace is continuous. Source: `Breakdown.Coercive.Internal.Field.secondDerivTrace_continuous` (`Breakdown/Cert/CoerciveField.lean:686`).

**Theorem: Squared matrix norm is continuous.** Under the stated hypotheses, the squared matrix norm is continuous. Source: `Breakdown.Coercive.Internal.Field.matSq_continuous` (`Breakdown/Cert/CoerciveField.lean:693`).

**Theorem: Squared matrix norm is nonnegative.** The squared matrix norm is nonnegative for the stated data. Source: `Breakdown.Coercive.Internal.Field.matSq_nonneg` (`Breakdown/Cert/CoerciveField.lean:698`).

**Theorem: Field pairing is integrable.** Under the stated hypotheses, the field pairing is integrable. Source: `Breakdown.Coercive.Internal.Field.pairing_integrable` (`Breakdown/Cert/CoerciveField.lean:701`).

**Theorem: The zero periodic test field.** The zero field is a periodic solenoidal test field. Source: `Breakdown.Coercive.Internal.Field.testField_zero` (`Breakdown/Cert/CoerciveField.lean:727`).

**Theorem: Period square energy gives L² membership.** The field with finite period squared energy belongs to L² for the period-slab measure. Source: `Breakdown.Coercive.Internal.Field.memLp_of_period` (`Breakdown/Cert/CoerciveField.lean:734`).

**Theorem: L² membership gives finite period energy.** The field's L² membership for the period-slab measure implies finite squared energy over one period. Source: `Breakdown.Coercive.Internal.Field.period_lt_top_of_memLp` (`Breakdown/Cert/CoerciveField.lean:746`).

**Theorem: Read the L² inner product pointwise.** The inner product of the L² classes equals the integral of their pointwise inner product. Source: `Breakdown.Coercive.Internal.Field.inner_toLp` (`Breakdown/Cert/CoerciveField.lean:752`).

**Theorem: Two L² fields have an integrable pairing.** The pointwise inner product of the two stated L² fields is integrable over the period slab. Source: `Breakdown.Coercive.Internal.Field.integrable_inner_of_memLp` (`Breakdown/Cert/CoerciveField.lean:760`).

**Theorem: The L² norm equals the period norm.** The norm of the period L² class equals the field's period norm. Source: `Breakdown.Coercive.Internal.Field.norm_toLp_eq_periodNorm` (`Breakdown/Cert/CoerciveField.lean:767`).

**Theorem: Test-potential gradients lie in L².** The spatial gradient of the stated test potential belongs to L² on the period slab. Source: `Breakdown.Coercive.Internal.Field.potential_gradient_memLp` (`Breakdown/Cert/CoerciveField.lean:779`).

**Theorem: Gradients annihilate solenoidal tests.** The gradient of a periodic test potential has zero period pairing with a solenoidal test field. Source: `Breakdown.Coercive.Internal.Field.gradient_inner_testField` (`Breakdown/Cert/CoerciveField.lean:816`).

**Theorem: Represent a bounded variational pairing.** The stated bounded linear pairing is represented by a periodic solenoidal L² field with the required norm bound. Source: `Breakdown.Coercive.Internal.Field.exists_field_of_bounded` (`Breakdown/Cert/CoerciveField.lean:888`).

**Theorem: Derivative control by weighted energy.** The square root of weighted energy bounds the Laplacian period norm and, after division by the weight lower bound's square root, the gradient period norm. Source: `Breakdown.Coercive.Internal.Field.weightedEnergy_bounds` (`Breakdown/Cert/CoerciveField.lean:1015`).

**Theorem: Combine the multiplier norm estimates.** The separate derivative and frequency contributions are bounded by the explicit multiplier constant times the combined energy square root. Source: `Breakdown.Coercive.Internal.Field.scalar_bound` (`Breakdown/Cert/CoerciveField.lean:1085`).

**Theorem: Bound the negative-Laplacian pairing.** The absolute negative-Laplacian pairing is at most the product of the two period L² norms. Source: `Breakdown.Coercive.Internal.Field.secondDerivPairing_abs_le` (`Breakdown/Cert/CoerciveField.lean:1110`).

**Theorem: Add tests in the Laplacian pairing.** The negative-Laplacian period pairing distributes over addition of its test-field argument. Source: `Breakdown.Coercive.Internal.Field.secondDerivPairing_add` (`Breakdown/Cert/CoerciveField.lean:1127`).

**Theorem: Scale a test in the Laplacian pairing.** Multiplying the test field by a real scalar multiplies the negative-Laplacian period pairing by the same scalar. Source: `Breakdown.Coercive.Internal.Field.secondDerivPairing_smul` (`Breakdown/Cert/CoerciveField.lean:1156`).

**Theorem: Separate curl and velocity mode sums.** The full multiplier mode sum equals the curl contribution plus the velocity contribution. Source: `Breakdown.Coercive.Internal.Field.fieldModeSum_split` (`Breakdown/Cert/CoerciveField.lean:1162`).

**Theorem: Cauchy-Schwarz for square-root integrals.** The product of the two square roots is integrable and its integral is bounded by the square root of each factor's integral multiplied together. Source: `Breakdown.Coercive.Internal.Field.integral_sqrt_mul_le` (`Breakdown/Cert/CoerciveField.lean:1178`).

**Theorem: Bound one integrated curl-mode term.** The absolute curl-mode pairing is bounded by the stated second-derivative and curl-energy factor times the test-mode L² norm. Source: `Breakdown.Coercive.Internal.Field.epsModeTerm_abs_le` (`Breakdown/Cert/CoerciveField.lean:1199`).

**Theorem: Summed curl energy is controlled.** The sum of the integrated curl-mode squares is bounded by the squared period gradient norm. Source: `Breakdown.Coercive.Internal.Field.curlMode_tsum_le` (`Breakdown/Cert/CoerciveField.lean:1279`).

**Theorem: The curl contraction is continuous.** The complex curl contraction depends continuously on its gradient array. Source: `Breakdown.Coercive.Internal.Field.continuous_curlOfGrad` (`Breakdown/Cert/CoerciveField.lean:1306`).

**Theorem: Bound the summed curl contribution.** The absolute sum of the curl-weight pairings is controlled by the stated trace and gradient energy factors times the test-field period norm. Source: `Breakdown.Coercive.Internal.Field.epsModeSum_abs_le` (`Breakdown/Cert/CoerciveField.lean:1310`).

**Theorem: Complex Cauchy-Schwarz inequality.** The norm of the complex coordinate pairing is at most the product of the two complex-vector amplitudes. Source: `Breakdown.Coercive.Internal.Field.norm_cdot_le_sqrt` (`Breakdown/Cert/CoerciveField.lean:1395`).

**Theorem: Young bound for a velocity-mode term.** For a positive splitting parameter, the absolute velocity-mode pairing is bounded by the weighted velocity square and reciprocal-weight test square. Source: `Breakdown.Coercive.Internal.Field.termMu_abs_le_of_pos` (`Breakdown/Cert/CoerciveField.lean:1404`).

**Theorem: Bound the summed velocity contribution.** The absolute sum of velocity-weight pairings is controlled by the frequency or piece seminorm factor and the test-field period norm. Source: `Breakdown.Coercive.Internal.Field.muModeSum_abs_le` (`Breakdown/Cert/CoerciveField.lean:1428`).

**Theorem: Bound the full multiplier mode sum.** The full multiplier mode pairing is bounded by the combined trace, gradient, and frequency factors times the test-field period norm. Source: `Breakdown.Coercive.Internal.Field.fieldModeSum_abs_le` (`Breakdown/Cert/CoerciveField.lean:1534`).

**Theorem: Existence of the mode multiplier.** The supplied hypotheses establish finiteness of the frequency seminorm and existence of a variational multiplier with its norm bound. Source: `Breakdown.Coercive.modeFieldExistsHolds_of` (`Breakdown/Cert/CoerciveField.lean:1557`).

### Breakdown.Cert.CoerciveFieldModes

Orbit measurability, mode-square integrability, and summability estimates justify the infinite mode sums used to construct the multiplier functional.

**Paper context:** Appendix B, Proposition B.1: measure and summation support for multiplier-field existence.

**Definition: Volume over one time period.** Use the product of volume on the closed unit time interval and spatial volume. Source: `Breakdown.Coercive.Internal.FieldModes.slab` (`Breakdown/Cert/CoerciveFieldModes.lean:17`).

**Definition: A periodic L² field.** Require almost-everywhere strong measurability, time periodicity, and finite squared norm over one period. Source: `Breakdown.Coercive.Internal.FieldModes.IsSquareField` (`Breakdown/Cert/CoerciveFieldModes.lean:19`).

**Definition: Measure for averaging field orbits.** Use space-time volume together with one time period and one full angular turn for orbit averaging. Source: `Breakdown.Coercive.Internal.FieldModes.orbitDomain` (`Breakdown/Cert/CoerciveFieldModes.lean:23`).

**Theorem: Measurability along time-rotation orbits.** Under the stated hypotheses, the field composed with its time-rotation orbit is strongly measurable up to a null set. Source: `Breakdown.Coercive.Internal.FieldModes.aestronglyMeasurable_orbit` (`Breakdown/Cert/CoerciveFieldModes.lean:27`).

**Theorem: Fourier mode average is measurable.** Under the stated hypotheses, the Fourier mode average is strongly measurable up to a null set. Source: `Breakdown.Coercive.Internal.FieldModes.aestronglyMeasurable_modeAverage` (`Breakdown/Cert/CoerciveFieldModes.lean:45`).

**Theorem: Fourier mode average is measurable.** Under the stated hypotheses, the Fourier mode average is strongly measurable up to a null set. Source: `Breakdown.Coercive.Internal.FieldModes.aestronglyMeasurable_modeAverage_comp` (`Breakdown/Cert/CoerciveFieldModes.lean:62`).

**Theorem: Velocity mode is measurable.** Under the stated hypotheses, the velocity mode is strongly measurable up to a null set. Source: `Breakdown.Coercive.Internal.FieldModes.aestronglyMeasurable_modeVel` (`Breakdown/Cert/CoerciveFieldModes.lean:74`).

**Theorem: Gradient mode is measurable.** Under the stated hypotheses, the gradient mode is strongly measurable up to a null set. Source: `Breakdown.Coercive.Internal.FieldModes.aestronglyMeasurable_modeGrad` (`Breakdown/Cert/CoerciveFieldModes.lean:82`).

**Theorem: Squared complex norm is nonnegative.** The squared complex norm is nonnegative for the stated data. Source: `Breakdown.Coercive.Internal.FieldModes.cnormSq_nonneg` (`Breakdown/Cert/CoerciveFieldModes.lean:94`).

**Theorem: The complex square sum is continuous.** The sum of the squared norms of a finite complex array depends continuously on the array. Source: `Breakdown.Coercive.Internal.FieldModes.continuous_cnormSq` (`Breakdown/Cert/CoerciveFieldModes.lean:97`).

**Theorem: The period measure is a slab restriction.** The period product measure is space-time volume restricted to the unit time slab. Source: `Breakdown.Coercive.Internal.FieldModes.slab_eq` (`Breakdown/Cert/CoerciveFieldModes.lean:101`).

**Theorem: Gradient mode is measurable.** Under the stated hypotheses, the gradient mode is measurable up to a null set. Source: `Breakdown.Coercive.Internal.FieldModes.aemeasurable_modeGrad` (`Breakdown/Cert/CoerciveFieldModes.lean:105`).

**Theorem: Velocity mode is measurable.** Under the stated hypotheses, the velocity mode is measurable up to a null set. Source: `Breakdown.Coercive.Internal.FieldModes.aemeasurable_modeVel` (`Breakdown/Cert/CoerciveFieldModes.lean:111`).

**Theorem: Period integral is finite.** Under the stated hypotheses, the nonnegative period integral is finite. Source: `Breakdown.Coercive.Internal.FieldModes.periodLIntegral_lt_top_of_support` (`Breakdown/Cert/CoerciveFieldModes.lean:117`).

**Theorem: Integrable gradient-mode squares.** Under the stated hypotheses, the squared norm of the gradient mode is integrable. Source: `Breakdown.Coercive.Internal.FieldModes.integrable_cnormSq_modeGrad` (`Breakdown/Cert/CoerciveFieldModes.lean:147`).

**Theorem: Summable integrated gradient squares.** Under the stated hypotheses, the family of integrated gradient-mode squares is summable over its index set. Source: `Breakdown.Coercive.Internal.FieldModes.summable_integral_cnormSq_modeGrad` (`Breakdown/Cert/CoerciveFieldModes.lean:164`).

**Theorem: Integrable velocity-mode squares.** Under the stated hypotheses, the squared norm of the velocity mode is integrable. Source: `Breakdown.Coercive.Internal.FieldModes.integrable_cnormSq_modeVel` (`Breakdown/Cert/CoerciveFieldModes.lean:179`).

**Theorem: Summable integrated velocity squares.** Under the stated hypotheses, the family of integrated velocity-mode squares is summable over its index set. Source: `Breakdown.Coercive.Internal.FieldModes.summable_integral_cnormSq_modeVel` (`Breakdown/Cert/CoerciveFieldModes.lean:196`).

**Theorem: Parseval in ordinary integrals.** The sum of integrated velocity-mode squares equals the real value of the physical period L² energy. Source: `Breakdown.Coercive.Internal.FieldModes.tsum_integral_cnormSq_modeVel` (`Breakdown/Cert/CoerciveFieldModes.lean:209`).

**Theorem: Recover a product of square roots.** The stated square estimate implies the bound by the product of the two nonnegative square roots. Source: `Breakdown.Coercive.Internal.FieldModes.sq_sqrt_bound` (`Breakdown/Cert/CoerciveFieldModes.lean:229`).

**Theorem: Young bound for two square roots.** For positive t, the product of two nonnegative square roots is at most half of ta plus c/t. Source: `Breakdown.Coercive.Internal.FieldModes.sqrt_mul_sqrt_le_of_pos` (`Breakdown/Cert/CoerciveFieldModes.lean:261`).

**Theorem: Cauchy-Schwarz for an infinite series.** The square-root product series is summable and its sum is at most the product of the square roots of the two sums. Source: `Breakdown.Coercive.Internal.FieldModes.tsum_sqrt_mul_le` (`Breakdown/Cert/CoerciveFieldModes.lean:274`).

**Theorem: A compact continuous field lies in L².** A continuous periodic field with the stated compact spatial support satisfies the periodic L² field conditions. Source: `Breakdown.Coercive.Internal.FieldModes.isSquareField_of_continuous` (`Breakdown/Cert/CoerciveFieldModes.lean:292`).

**Theorem: Bound a complex pairing by two squares.** The norm of the complex coordinate pairing is at most half the sum of the two complex-vector norm squares. Source: `Breakdown.Coercive.Internal.FieldModes.norm_cdot_le` (`Breakdown/Cert/CoerciveFieldModes.lean:299`).

**Theorem: The three curl coordinates.** The curl contraction has the usual three differences of off-diagonal gradient entries. Source: `Breakdown.Coercive.Internal.FieldModes.curlOfGrad_apply` (`Breakdown/Cert/CoerciveFieldModes.lean:307`).

**Theorem: A squared difference bound.** The squared norm of a difference is at most twice the sum of the two squared norms. Source: `Breakdown.Coercive.Internal.FieldModes.norm_sub_sq_le` (`Breakdown/Cert/CoerciveFieldModes.lean:312`).

**Theorem: Curl square is controlled by gradient.** The squared curl contraction is at most twice the squared norm of the gradient array. Source: `Breakdown.Coercive.Internal.FieldModes.cnormSq_curlOfGrad_le` (`Breakdown/Cert/CoerciveFieldModes.lean:317`).

**Theorem: Bound a rotated complex real part.** The absolute real part of i times a real coefficient times a complex number is at most the coefficient's absolute value times the complex norm. Source: `Breakdown.Coercive.Internal.FieldModes.abs_re_I_mul_le` (`Breakdown/Cert/CoerciveFieldModes.lean:326`).

**Theorem: Bound a signed curl contraction.** The signed curl contraction is bounded by the coefficient's absolute value times the sum of the two gradient norm squares. Source: `Breakdown.Coercive.Internal.FieldModes.abs_curlTerm_le` (`Breakdown/Cert/CoerciveFieldModes.lean:330`).

**Theorem: Bound a signed velocity contraction.** The signed velocity contraction is bounded by half the coefficient's absolute value times the sum of the two velocity norm squares. Source: `Breakdown.Coercive.Internal.FieldModes.abs_velTerm_le` (`Breakdown/Cert/CoerciveFieldModes.lean:336`).

**Theorem: Gradient field formula.** Under the stated hypotheses, the gradient field has time period one. Source: `Breakdown.Coercive.Internal.FieldModes.gradField_periodic` (`Breakdown/Cert/CoerciveFieldModes.lean:340`).

**Theorem: The gradient vanishes off the support.** The test-field gradient vanishes at the stated point outside its spatial support. Source: `Breakdown.Coercive.Internal.FieldModes.gradField_eq_zero` (`Breakdown/Cert/CoerciveFieldModes.lean:346`).

**Definition: Truncate a field to a ball.** Multiply the field by the indicator of a closed spatial ball. Source: `Breakdown.Coercive.Internal.FieldModes.ballPart` (`Breakdown/Cert/CoerciveFieldModes.lean:355`).

**Theorem: A bounded truncation has finite L² norm.** Truncating the periodic velocity to the stated ball gives a measurable periodic L² field. Source: `Breakdown.Coercive.Internal.FieldModes.isSquareField_ballPart` (`Breakdown/Cert/CoerciveFieldModes.lean:358`).

**Theorem: Local modes ignore the outer truncation.** Inside the stated ball, the velocity mode of the truncated field equals the original velocity mode. Source: `Breakdown.Coercive.Internal.FieldModes.modeVel_ballPart` (`Breakdown/Cert/CoerciveFieldModes.lean:388`).

**Theorem: Axial rotation fixes zero.** Every axial rotation sends the zero vector to zero. Source: `Breakdown.Coercive.Internal.FieldModes.axialRot_zero_vec` (`Breakdown/Cert/CoerciveFieldModes.lean:398`).

**Theorem: A velocity mode vanishes off the support.** If the field vanishes on the relevant rotation orbit, its velocity mode is zero. Source: `Breakdown.Coercive.Internal.FieldModes.modeVel_eq_zero` (`Breakdown/Cert/CoerciveFieldModes.lean:401`).

**Theorem: A gradient mode vanishes off the support.** If the gradient vanishes on the relevant rotation orbit, its gradient mode is zero. Source: `Breakdown.Coercive.Internal.FieldModes.modeGrad_eq_zero` (`Breakdown/Cert/CoerciveFieldModes.lean:409`).

### Breakdown.Cert.CoerciveFrequencySeminorm

Angular and temporal frequency estimates control the weighted Fourier seminorm by the physical field, gradient, and transport energies.

**Paper context:** Appendix B, Proposition B.1: finiteness and control of the frequency-weighted seminorm.

**Theorem: An integer square bounds its magnitude.** The absolute value of an integer, viewed as real, is at most its square. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.int_abs_le_sq` (`Breakdown/Cert/CoerciveFrequencySeminorm.lean:21`).

**Theorem: Bound the radial-gradient correction.** The squared norm after subtracting half a matrix applied to the radius is at most twice the original square plus half the radius square times the matrix square. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.cnormSq_sub_half_le` (`Breakdown/Cert/CoerciveFrequencySeminorm.lean:30`).

**Theorem: Combine the two frequency estimates.** The given nonnegative algebraic bounds control the weighted frequency contribution by the transport, gradient, and radially weighted velocity terms. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.real_bound` (`Breakdown/Cert/CoerciveFrequencySeminorm.lean:67`).

**Theorem: A scalar factors out of mode averaging.** Multiplying the averaged field by a real constant multiplies its complex Fourier mode average by that constant. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.modeAverage_mul_left` (`Breakdown/Cert/CoerciveFrequencySeminorm.lean:94`).

**Definition: Velocity with a radial damping factor.** Multiply velocity by the reciprocal square root of one plus the squared radius. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.dampedField` (`Breakdown/Cert/CoerciveFrequencySeminorm.lean:110`).

**Theorem: Damping factors out of velocity modes.** The radial damping factor multiplies every coordinate of the velocity mode. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.modeVel_dampedField` (`Breakdown/Cert/CoerciveFrequencySeminorm.lean:113`).

**Theorem: Damping of the mode energy.** The damped velocity-mode square equals the original mode square divided by one plus the squared radius. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.cnormSq_modeVel_dampedField` (`Breakdown/Cert/CoerciveFrequencySeminorm.lean:123`).

**Theorem: Damping of the physical velocity energy.** The damped physical velocity square equals the original velocity square divided by one plus the squared radius. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.norm_dampedField_sq` (`Breakdown/Cert/CoerciveFrequencySeminorm.lean:131`).

**Theorem: Weighted frequency energy is finite.** The total period mode energy weighted by the spatial weight and the absolute integer frequencies is finite. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.weightedFrequency_lt_top` (`Breakdown/Cert/CoerciveFrequencySeminorm.lean:245`).

### Breakdown.Cert.CoerciveFrequencySeminormAngular

The angular generator and rotation covariance relate angular integer frequencies to physical gradient and cylindrical-radius bounds.

**Paper context:** Appendix B, Proposition B.1: the angular-frequency part of the seminorm estimate.

**Theorem: Cylindrical radius is at most distance.** The squared distance from the rotation axis is at most the squared Euclidean radius. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.cylRadius_sq_le_norm_sq` (`Breakdown/Cert/CoerciveFrequencySeminormAngular.lean:19`).

**Theorem: Negation preserves complex square norms.** Negating a complex coordinate vector leaves its squared norm unchanged. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.cnormSq_neg'` (`Breakdown/Cert/CoerciveFrequencySeminormAngular.lean:24`).

**Theorem: The imaginary frequency factor's norm.** Multiplication by ik multiplies the complex-vector norm square by k². Source: `Breakdown.Coercive.FrequencySeminorm.Internal.cnormSq_smul_I` (`Breakdown/Cert/CoerciveFrequencySeminormAngular.lean:27`).

**Theorem: Bound the angular derivative.** Contracting the gradient array with the axial rotation generator has squared norm at most the radius square times the gradient-array square. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.contracted_grad_le` (`Breakdown/Cert/CoerciveFrequencySeminormAngular.lean:33`).

**Theorem: An angular-frequency square bound.** The angular-frequency square times the vector energy is controlled by twice the vector energy plus twice the radius-weighted gradient energy. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.angular_pointwise` (`Breakdown/Cert/CoerciveFrequencySeminormAngular.lean:55`).

**Theorem: Angular mode energy is controlled.** Almost everywhere, the angular-frequency-weighted velocity-mode square is bounded by twice its velocity square and twice its radius-weighted gradient square. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.angular_mode_bound` (`Breakdown/Cert/CoerciveFrequencySeminormAngular.lean:73`).

### Breakdown.Cert.CoerciveFrequencySeminormBound

An adjustable split estimate controls ordinary and piece-weight seminorms and proves their convergence under the stated smooth approximation.

**Paper context:** Appendix B, Proposition B.1: continuity of frequency and piece seminorms in the approximation topology.

**Definition: Constant for the frequency estimate.** Set the explicit coefficient 2B times the sum of 2(P/(2π))² and 4. Source: `Breakdown.Coercive.FrequencyBound.boundConstant` (`Breakdown/Cert/CoerciveFrequencySeminormBound.lean:16`).

**Definition: Energy controlling the frequency sum.** Add the period integrals of the transport square, gradient square, and radially weighted velocity square. Source: `Breakdown.Coercive.FrequencyBound.fieldSize` (`Breakdown/Cert/CoerciveFrequencySeminormBound.lean:18`).

**Theorem: Compare the two radial weights.** The inverse-quadratic-weight velocity energy is at most twice the energy weighted by the inverse square of one plus radius. Source: `Breakdown.Coercive.FrequencyBound.Internal.dampedField_periodLIntegral_le` (`Breakdown/Cert/CoerciveFrequencySeminormBound.lean:27`).

**Theorem: Compare the two radial weights.** The energy weighted by the inverse square of one plus radius is at most the inverse-quadratic-weight velocity energy. Source: `Breakdown.Coercive.FrequencyBound.Internal.weighted_le_damped` (`Breakdown/Cert/CoerciveFrequencySeminormBound.lean:49`).

**Theorem: The combined field energy is finite.** The velocity, gradient, and transport contributions defining the combined field-size functional have finite total value. Source: `Breakdown.Coercive.FrequencyBound.Internal.fieldSize_lt_top` (`Breakdown/Cert/CoerciveFrequencySeminormBound.lean:57`).

**Theorem: The damped velocity lies in period L².** The radially damped velocity is strongly measurable up to a null set, periodic, and square integrable over one period. Source: `Breakdown.Coercive.FrequencyBound.Internal.dampedField_square` (`Breakdown/Cert/CoerciveFrequencySeminormBound.lean:64`).

**Theorem: Bound the moving-frame frequency.** The absolute moving-frame frequency is bounded by the stated coefficient times the sum of the squared integer frequencies. Source: `Breakdown.Coercive.FrequencyBound.Internal.abs_freq_le` (`Breakdown/Cert/CoerciveFrequencySeminormBound.lean:79`).

**Theorem: Young bound with a positive parameter.** Twice a real product is at most the weighted first square plus the reciprocally weighted second square. Source: `Breakdown.Coercive.FrequencyBound.Internal.two_mul_norm_le` (`Breakdown/Cert/CoerciveFrequencySeminormBound.lean:98`).

**Theorem: Split a complex-vector square.** The squared norm of a sum is at most (1+t) times the first square plus (1+1/t) times the second for positive t. Source: `Breakdown.Coercive.FrequencyBound.Internal.cnormSq_add_le_split` (`Breakdown/Cert/CoerciveFrequencySeminormBound.lean:105`).

**Theorem: Split a complex-vector difference square.** The squared norm of a difference has the same adjustable two-square bound for positive t. Source: `Breakdown.Coercive.FrequencyBound.Internal.cnormSq_sub_le_split` (`Breakdown/Cert/CoerciveFrequencySeminormBound.lean:118`).

**Definition: A weighted sum of velocity modes.** Sum the weighted squared velocity-mode integrals over space, one period, and all frequency pairs. Source: `Breakdown.Coercive.FrequencyBound.Internal.modeSum` (`Breakdown/Cert/CoerciveFrequencySeminormBound.lean:131`).

**Theorem: Integrate an a.e. upper bound.** The pointwise two-term upper bound gives the corresponding two-term bound between iterated nonnegative integrals. Source: `Breakdown.Coercive.FrequencyBound.Internal.iter_le_of_ae` (`Breakdown/Cert/CoerciveFrequencySeminormBound.lean:134`).

**Theorem: Measurability of weighted mode energy.** Under the stated hypotheses, the weighted squared velocity-mode norm is measurable up to a null set. Source: `Breakdown.Coercive.FrequencyBound.Internal.aemeasurable_weightedMode` (`Breakdown/Cert/CoerciveFrequencySeminormBound.lean:147`).

**Theorem: Compare two weighted mode energies.** Each of the two weighted mode energies is bounded by the other and their difference energy with the stated adjustable factors. Source: `Breakdown.Coercive.FrequencyBound.Internal.modeSum_split` (`Breakdown/Cert/CoerciveFrequencySeminormBound.lean:154`).

**Theorem: Convert a finite weighted bound to reals.** The finite extended-real inequality gives the corresponding real inequality after applying toReal. Source: `Breakdown.Coercive.FrequencyBound.Internal.toReal_split` (`Breakdown/Cert/CoerciveFrequencySeminormBound.lean:245`).

**Theorem: Two-sided split bounds give convergence.** The stated adjustable split bounds imply convergence of the sequence to the specified limit. Source: `Breakdown.Coercive.FrequencyBound.Internal.tendsto_of_split` (`Breakdown/Cert/CoerciveFrequencySeminormBound.lean:254`).

**Theorem: Convergence of real energy values.** The real values of the nonnegative energy functional on the approximating fields converge to its value on the limiting field. Source: `Breakdown.Coercive.FrequencyBound.Internal.tendsto_toReal_of_split` (`Breakdown/Cert/CoerciveFrequencySeminormBound.lean:303`).

**Theorem: A vanishing upper bound forces zero.** The nonnegative sequence tends to zero when bounded above by the stated vanishing control sequence. Source: `Breakdown.Coercive.FrequencyBound.Internal.tendsto_zero_of_le` (`Breakdown/Cert/CoerciveFrequencySeminormBound.lean:317`).

**Theorem: Control both squared frequencies.** The total frequency-square-weighted mode energy is bounded by the explicit constant times the transport, gradient, and weighted-velocity energy. Source: `Breakdown.Coercive.FrequencyBound.weightedFrequencySq_le` (`Breakdown/Cert/CoerciveFrequencySeminormBound.lean:329`).

**Theorem: Control frequency energy of a difference.** The total frequency-square-weighted mode error is bounded by the same explicit constant times the difference field's transport and derivative energies. Source: `Breakdown.Coercive.FrequencyBound.weightedFrequencySq_sub_le` (`Breakdown/Cert/CoerciveFrequencySeminormBound.lean:447`).

**Theorem: An explicit frequency-seminorm bound.** The squared frequency seminorm is bounded by the displayed constant times the combined transport and derivative energy. Source: `Breakdown.Coercive.FrequencyBound.frequencySeminormSq_le` (`Breakdown/Cert/CoerciveFrequencySeminormBound.lean:460`).

**Theorem: An explicit piece-seminorm bound.** The squared velocity-piece seminorm is bounded by the sum of the piece constants times the combined transport and derivative energy. Source: `Breakdown.Coercive.FrequencyBound.pieceSeminormSq_le` (`Breakdown/Cert/CoerciveFrequencySeminormBound.lean:488`).

**Theorem: Frequency energies pass to the limit.** The squared frequency seminorm of the error tends to zero, and the real frequency energies of the approximations converge to the limiting energy. Source: `Breakdown.Coercive.FrequencyBound.frequencySeminormSq_tendsto` (`Breakdown/Cert/CoerciveFrequencySeminormBound.lean:532`).

**Theorem: Piece seminorms pass to the limit.** The squared piece seminorm of the error tends to zero, and the real piece-seminorm energies converge to the limiting field's value. Source: `Breakdown.Coercive.FrequencyBound.pieceSeminormSq_tendsto` (`Breakdown/Cert/CoerciveFrequencySeminormBound.lean:564`).

**Theorem: Transport and derivative errors vanish.** The combined velocity, gradient, and transport error functional tends to zero under the smooth-approximation specification. Source: `Breakdown.Coercive.FrequencyBound.fieldSize_tendsto_of_approximation` (`Breakdown/Cert/CoerciveFrequencySeminormBound.lean:604`).

**Theorem: Frequency energies pass to the limit.** The squared frequency seminorm of the error tends to zero, and the real frequency energies of the approximations converge to the limiting energy. Source: `Breakdown.Coercive.FrequencyBound.frequencySeminormSq_tendsto_of_approximation` (`Breakdown/Cert/CoerciveFrequencySeminormBound.lean:614`).

**Theorem: Piece seminorms pass to the limit.** The squared piece seminorm of the error tends to zero, and the real piece-seminorm energies converge to the limiting field's value. Source: `Breakdown.Coercive.FrequencyBound.pieceSeminormSq_tendsto_of_approximation` (`Breakdown/Cert/CoerciveFrequencySeminormBound.lean:629`).

### Breakdown.Cert.CoerciveFrequencySeminormBoundSub

Differences of perturbations retain the required weak derivative, transport, periodicity, and integrability properties for the seminorm estimate.

**Paper context:** Appendix B, Proposition B.1: applying the seminorm bound to approximation errors.

**Theorem: Subtract two weak-gradient identities.** The difference of two weak gradients is the weak gradient of the difference field. Source: `Breakdown.Coercive.FrequencyBound.Internal.isWeakGradient_sub` (`Breakdown/Cert/CoerciveFrequencySeminormBoundSub.lean:20`).

**Theorem: Bound a sixth-power difference.** The sixth power of a norm difference is at most 64 times the sum of the two sixth powers. Source: `Breakdown.Coercive.FrequencyBound.Internal.sixth_sub_le` (`Breakdown/Cert/CoerciveFrequencySeminormBoundSub.lean:45`).

**Theorem: Bound a squared difference.** The squared norm of a difference is at most twice the sum of the two norm squares. Source: `Breakdown.Coercive.FrequencyBound.Internal.sq_sub_le` (`Breakdown/Cert/CoerciveFrequencySeminormBoundSub.lean:58`).

**Theorem: Bound a matrix discrepancy square.** The squared matrix discrepancy is at most twice the sum of the two matrix squares. Source: `Breakdown.Coercive.FrequencyBound.Internal.matSq_sub_le` (`Breakdown/Cert/CoerciveFrequencySeminormBoundSub.lean:63`).

**Theorem: Squared matrix norm is nonnegative.** The squared matrix norm is nonnegative for the stated data. Source: `Breakdown.Coercive.FrequencyBound.Internal.matSq_nonneg` (`Breakdown/Cert/CoerciveFrequencySeminormBoundSub.lean:70`).

**Theorem: Squared matrix norm is continuous.** Under the stated hypotheses, the squared matrix norm is continuous. Source: `Breakdown.Coercive.FrequencyBound.Internal.continuous_matSq` (`Breakdown/Cert/CoerciveFrequencySeminormBoundSub.lean:73`).

**Theorem: Second-derivative trace is continuous.** Under the stated hypotheses, the second-derivative trace is continuous. Source: `Breakdown.Coercive.FrequencyBound.Internal.continuous_secondDerivTrace` (`Breakdown/Cert/CoerciveFrequencySeminormBoundSub.lean:77`).

**Theorem: The Hessian trace respects subtraction.** Under the stated hypotheses, the second-derivative trace commutes with subtraction. Source: `Breakdown.Coercive.FrequencyBound.Internal.secondDerivTrace_sub` (`Breakdown/Cert/CoerciveFrequencySeminormBoundSub.lean:82`).

**Theorem: Period integration preserves order.** An almost-everywhere pointwise bound implies the same bound between the nonnegative period integrals. Source: `Breakdown.Coercive.FrequencyBound.Internal.periodLIntegral_mono` (`Breakdown/Cert/CoerciveFrequencySeminormBoundSub.lean:88`).

**Theorem: Period integral preserves scaling.** Under the stated hypotheses, the nonnegative period integral commutes with multiplication by a constant. Source: `Breakdown.Coercive.FrequencyBound.Internal.periodLIntegral_const_mul` (`Breakdown/Cert/CoerciveFrequencySeminormBoundSub.lean:92`).

**Theorem: Period integral preserves addition.** Under the stated hypotheses, the nonnegative period integral commutes with addition. Source: `Breakdown.Coercive.FrequencyBound.Internal.periodLIntegral_add` (`Breakdown/Cert/CoerciveFrequencySeminormBoundSub.lean:98`).

**Theorem: Period integral is finite.** Under the stated hypotheses, the nonnegative period integral is finite. Source: `Breakdown.Coercive.FrequencyBound.Internal.periodLIntegral_lt_top_of_two` (`Breakdown/Cert/CoerciveFrequencySeminormBoundSub.lean:109`).

**Theorem: Period control gives local integrability.** The stated almost-everywhere strongly measurable periodic field with finite period squared energy is locally integrable on space-time. Source: `Breakdown.Coercive.FrequencyBound.Internal.locallyIntegrable_of_periodic` (`Breakdown/Cert/CoerciveFrequencySeminormBoundSub.lean:122`).

**Theorem: Field pairing is integrable.** Under the stated hypotheses, the field pairing is integrable. Source: `Breakdown.Coercive.FrequencyBound.Internal.integrable_inner_of_locallyIntegrable` (`Breakdown/Cert/CoerciveFrequencySeminormBoundSub.lean:154`).

**Definition: The adjoint transport of a test field.** Combine the negative time derivative, negative field, and negative half radial derivative of the test field. Source: `Breakdown.Coercive.FrequencyBound.Internal.testTransport` (`Breakdown/Cert/CoerciveFrequencySeminormBoundSub.lean:162`).

**Theorem: Adjoint test transport is continuous.** Under the stated hypotheses, the adjoint test transport is continuous. Source: `Breakdown.Coercive.FrequencyBound.Internal.testTransport_continuous` (`Breakdown/Cert/CoerciveFrequencySeminormBoundSub.lean:165`).

**Theorem: Compact support: adjoint test transport.** Under the stated hypotheses, the adjoint test transport has compact support. Source: `Breakdown.Coercive.FrequencyBound.Internal.testTransport_hasCompactSupport` (`Breakdown/Cert/CoerciveFrequencySeminormBoundSub.lean:172`).

**Theorem: Subtract two weak perturbations.** The differences of the velocity, gradient, second derivative, and transport fields satisfy the weak perturbation conditions without a symmetry restriction. Source: `Breakdown.Coercive.FrequencyBound.isPerturbation_sub` (`Breakdown/Cert/CoerciveFrequencySeminormBoundSub.lean:195`).

### Breakdown.Cert.CoerciveFrequencySeminormTransportModes

The weak similarity-transport identity is carried through time-angle averaging, with weighted tests and Fourier phases making the modewise temporal derivative relation explicit.

**Paper context:** Appendix B, Proposition B.1: transport control of temporal mode frequencies.

**Theorem: Weak integration by parts in radius.** Testing a weak gradient in the radial direction transfers the derivative to the test weight and adds the dimension-three term. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.weak_radial` (`Breakdown/Cert/CoerciveFrequencySeminormTransportModes.lean:20`).

**Theorem: Local integrability of weak transport.** The stated weak transport field is locally integrable on space-time. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.derivative_locallyIntegrable` (`Breakdown/Cert/CoerciveFrequencySeminormTransportModes.lean:71`).

**Theorem: Weak gradients of complex modes.** The real and imaginary gradient modes are the weak gradients of the corresponding velocity modes. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.mode_weakGradient` (`Breakdown/Cert/CoerciveFrequencySeminormTransportModes.lean:103`).

**Theorem: Velocity orbit is integrable.** Under the stated hypotheses, the shifted and rotated velocity is integrable. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.integrable_family` (`Breakdown/Cert/CoerciveFrequencySeminormTransportModes.lean:131`).

**Theorem: Read modes as real orbit averages.** Almost everywhere in space, the real and imaginary velocity modes equal their cosine-weighted and negative-sine-weighted orbit averages. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.ae_modeVel_average` (`Breakdown/Cert/CoerciveFrequencySeminormTransportModes.lean:139`).

**Theorem: Interchange testing and averaging.** The spatial test pairing of an orbit average equals the average of the spatial test pairings. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.average_pairing` (`Breakdown/Cert/CoerciveFrequencySeminormTransportModes.lean:151`).

**Theorem: Test transport vanishes off support.** The test weight and its radial derivative combine to zero outside the stated support. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.test_weight_zero` (`Breakdown/Cert/CoerciveFrequencySeminormTransportModes.lean:163`).

**Theorem: Continuity of the radial test weight.** Under the stated hypotheses, the test function plus half its radial derivative is continuous. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.continuous_test_weight` (`Breakdown/Cert/CoerciveFrequencySeminormTransportModes.lean:170`).

**Theorem: Integrable weighted orbit pairings.** Under the stated hypotheses, the weighted spatial integral of the velocity orbit is integrable. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.integrable_pairing_family` (`Breakdown/Cert/CoerciveFrequencySeminormTransportModes.lean:175`).

**Theorem: Velocity orbit is integrable.** Under the stated hypotheses, the shifted and rotated velocity is locally integrable. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.locallyIntegrable_angleFamily` (`Breakdown/Cert/CoerciveFrequencySeminormTransportModes.lean:198`).

**Theorem: Locally integrable time-orbit pairings.** Under the stated hypotheses, the time-dependent weighted velocity-orbit pairing is locally integrable. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.locallyIntegrable_pairing_time` (`Breakdown/Cert/CoerciveFrequencySeminormTransportModes.lean:224`).

**Definition: A smooth cutoff for one period.** Build a smooth time cutoff from translated transition functions to localise periodic testing. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.timeCutoff` (`Breakdown/Cert/CoerciveFrequencySeminormTransportModes.lean:247`).

**Definition: Derivative of the period cutoff.** Subtract the derivatives of the two translated transition functions. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.timeCutoffDeriv` (`Breakdown/Cert/CoerciveFrequencySeminormTransportModes.lean:249`).

**Theorem: The transition derivative vanishes.** The smooth transition function has derivative zero outside its transition interval. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.deriv_smoothTransition_eq_zero` (`Breakdown/Cert/CoerciveFrequencySeminormTransportModes.lean:251`).

**Theorem: Smooth period cutoff is smooth.** Under the stated hypotheses, the smooth period cutoff is smooth. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.contDiff_timeCutoff` (`Breakdown/Cert/CoerciveFrequencySeminormTransportModes.lean:260`).

**Theorem: Smooth period cutoff has compact support.** Under the stated hypotheses, the smooth period cutoff has compact support. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.hasCompactSupport_timeCutoff` (`Breakdown/Cert/CoerciveFrequencySeminormTransportModes.lean:264`).

**Theorem: Time derivative is continuous.** Under the stated hypotheses, the time derivative is continuous. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.continuous_deriv_smoothTransition` (`Breakdown/Cert/CoerciveFrequencySeminormTransportModes.lean:274`).

**Theorem: The derivative of the period cutoff.** The cutoff derivative is the difference of the two shifted transition derivatives. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.hasDerivAt_timeCutoff` (`Breakdown/Cert/CoerciveFrequencySeminormTransportModes.lean:277`).

**Theorem: Time derivative has compact support.** Under the stated hypotheses, the time derivative has compact support. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.hasCompactSupport_deriv_shift` (`Breakdown/Cert/CoerciveFrequencySeminormTransportModes.lean:285`).

**Theorem: The cutoff derivative pairs to zero.** The integral of the period-cutoff derivative times a one-periodic function is zero. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.integral_timeCutoffDeriv_mul` (`Breakdown/Cert/CoerciveFrequencySeminormTransportModes.lean:293`).

**Theorem: The cutoff selects one period.** Integrating a one-periodic function against the time cutoff gives its integral over one unit period. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.integral_timeCutoff_mul` (`Breakdown/Cert/CoerciveFrequencySeminormTransportModes.lean:310`).

**Theorem: Separate time and space test weights.** The space-time integral of the two weighted orbit terms equals the time integral of their spatial pairings. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.exchange_weight` (`Breakdown/Cert/CoerciveFrequencySeminormTransportModes.lean:353`).

**Theorem: Derivative off the topological support.** The supplied derivative vanishes outside the topological support of its function. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.deriv_zero_off_tsupport` (`Breakdown/Cert/CoerciveFrequencySeminormTransportModes.lean:414`).

**Theorem: Weak transport along an orbit.** The temporally tested velocity-orbit pairing obeys the stated weak transport identity with the transport-source orbit pairing. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.time_weak_transport` (`Breakdown/Cert/CoerciveFrequencySeminormTransportModes.lean:419`).

**Theorem: Continuous weights preserve local L¹.** Multiplying the stated locally integrable field by a continuous scalar function preserves local integrability. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.locallyIntegrable_continuous_mul` (`Breakdown/Cert/CoerciveFrequencySeminormTransportModes.lean:518`).

**Theorem: Integrability from compact test weights.** The product of the stated locally integrable field and compactly supported continuous scalar function is integrable. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.integrable_compact_mul` (`Breakdown/Cert/CoerciveFrequencySeminormTransportModes.lean:523`).

**Theorem: Compact support of the test weight.** Under the stated hypotheses, the test function plus half its radial derivative has compact support. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.hasCompactSupport_test_weight` (`Breakdown/Cert/CoerciveFrequencySeminormTransportModes.lean:527`).

**Theorem: Transport against a periodic time weight.** Testing the orbit equation with a differentiable periodic time weight gives the weight-derivative term and the source pairing. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.angle_transport` (`Breakdown/Cert/CoerciveFrequencySeminormTransportModes.lean:531`).

**Theorem: Differentiate the cosine Fourier weight.** The derivative of the cosine Fourier weight is 2π times the temporal frequency times the negative-sine weight. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.hasDerivAt_weightRe` (`Breakdown/Cert/CoerciveFrequencySeminormTransportModes.lean:605`).

**Theorem: Differentiate the sine Fourier weight.** The derivative of the negative-sine Fourier weight is minus 2π times the temporal frequency times the cosine weight. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.hasDerivAt_weightIm` (`Breakdown/Cert/CoerciveFrequencySeminormTransportModes.lean:617`).

**Theorem: Cosine Fourier weight formula.** Under the stated hypotheses, the cosine Fourier weight has the stated period. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.weightRe_periodic` (`Breakdown/Cert/CoerciveFrequencySeminormTransportModes.lean:630`).

**Theorem: Negative sine Fourier weight formula.** Under the stated hypotheses, the negative sine Fourier weight has the stated period. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.weightIm_periodic` (`Breakdown/Cert/CoerciveFrequencySeminormTransportModes.lean:637`).

**Theorem: Cosine Fourier weight is continuous.** Under the stated hypotheses, the cosine Fourier weight is continuous. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.continuous_weightRe` (`Breakdown/Cert/CoerciveFrequencySeminormTransportModes.lean:644`).

**Theorem: Continuity: negative sine Fourier weight.** Under the stated hypotheses, the negative sine Fourier weight is continuous. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.continuous_weightIm` (`Breakdown/Cert/CoerciveFrequencySeminormTransportModes.lean:647`).

**Theorem: Average the time transport identity.** The supplied identity at each angle integrates to the corresponding identity over the full time-angle rectangle. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.family_transport_of_angle` (`Breakdown/Cert/CoerciveFrequencySeminormTransportModes.lean:650`).

**Theorem: Transport of real and imaginary averages.** The two real Fourier weights give the coupled real and imaginary orbit-transport identities. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.family_transport` (`Breakdown/Cert/CoerciveFrequencySeminormTransportModes.lean:685`).

**Theorem: Weak transport of the extracted mode.** The real and imaginary velocity modes satisfy the paired weak transport identities with the temporal-frequency coupling. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.core_pairings` (`Breakdown/Cert/CoerciveFrequencySeminormTransportModes.lean:723`).

**Theorem: Read a real vector coordinate.** A coordinate of the reconstructed real vector is the real part of the matching complex coordinate. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.reVec_apply` (`Breakdown/Cert/CoerciveFrequencySeminormTransportModes.lean:756`).

**Theorem: Read an imaginary vector coordinate.** A coordinate of the reconstructed imaginary vector is the imaginary part of the matching complex coordinate. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.imVec_apply` (`Breakdown/Cert/CoerciveFrequencySeminormTransportModes.lean:759`).

**Theorem: Apply the real-part matrix.** Each coordinate of the reconstructed real matrix acting on a vector is the row sum of real matrix entries times vector coordinates. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.reMat_apply` (`Breakdown/Cert/CoerciveFrequencySeminormTransportModes.lean:762`).

**Theorem: Apply the imaginary-part matrix.** Each coordinate of the reconstructed imaginary matrix acting on a vector is the row sum of imaginary matrix entries times vector coordinates. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.imMat_apply` (`Breakdown/Cert/CoerciveFrequencySeminormTransportModes.lean:766`).

**Definition: The transport identity in one mode.** Subtract the transport mode from the temporal-frequency, half-velocity, and radial-gradient terms. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.transportDefect` (`Breakdown/Cert/CoerciveFrequencySeminormTransportModes.lean:770`).

**Theorem: Local L¹ of radial operator evaluation.** Applying the locally integrable linear-map field to its spatial argument gives a locally integrable vector field. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.locallyIntegrable_apply_self` (`Breakdown/Cert/CoerciveFrequencySeminormTransportModes.lean:775`).

**Theorem: Real part of the transport defect.** The real transport defect is the half-velocity and half-radial-gradient combination minus the frequency-coupled imaginary velocity and real source. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.reVec_transportDefect` (`Breakdown/Cert/CoerciveFrequencySeminormTransportModes.lean:788`).

**Theorem: Imaginary part of the transport defect.** The imaginary transport defect is the half-velocity and half-radial-gradient combination plus the frequency-coupled real velocity minus the imaginary source. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.imVec_transportDefect` (`Breakdown/Cert/CoerciveFrequencySeminormTransportModes.lean:798`).

**Theorem: Separate the radial test pairings.** The two transported test pairings split into the scalar multiple and radial-derivative pairings appearing in the weak transport identity. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.split_pairing` (`Breakdown/Cert/CoerciveFrequencySeminormTransportModes.lean:808`).

**Theorem: Local integrability of complex modes.** The real and imaginary velocity-mode representatives are locally integrable in space. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.locallyIntegrable_modeVel` (`Breakdown/Cert/CoerciveFrequencySeminormTransportModes.lean:839`).

**Theorem: Test weights give integrable products.** The product of the stated compact test function and locally integrable field is integrable. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.integrable_test_smul` (`Breakdown/Cert/CoerciveFrequencySeminormTransportModes.lean:855`).

**Theorem: The transport defect tests to zero.** The stated weak mode equations make the transport defect have zero pairing with every allowed scalar test. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.defect_pairing_zero` (`Breakdown/Cert/CoerciveFrequencySeminormTransportModes.lean:859`).

**Theorem: The mode transport defect vanishes.** The transport defect is zero almost everywhere in space under the weak transport hypotheses. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.ae_transportDefect` (`Breakdown/Cert/CoerciveFrequencySeminormTransportModes.lean:883`).

**Theorem: A time shift gives a Fourier phase.** Shifting the averaged field in time multiplies its mode average by the corresponding unit complex temporal phase. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.modeAverage_shift` (`Breakdown/Cert/CoerciveFrequencySeminormTransportModes.lean:931`).

**Theorem: Time dependence of a velocity mode.** A velocity mode at time σ equals its value at time zero multiplied by the temporal Fourier phase. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.modeVel_shift` (`Breakdown/Cert/CoerciveFrequencySeminormTransportModes.lean:976`).

**Theorem: Time dependence of a gradient mode.** A gradient mode at time σ equals its value at time zero multiplied by the temporal Fourier phase. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.modeGrad_shift` (`Breakdown/Cert/CoerciveFrequencySeminormTransportModes.lean:985`).

**Theorem: Scale the complex-vector norm square.** Multiplication by a complex scalar multiplies the vector norm square by the scalar's squared norm. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.cnormSq_smul` (`Breakdown/Cert/CoerciveFrequencySeminormTransportModes.lean:996`).

**Theorem: The transport frequency factor's norm.** The squared norm of ia plus one half equals a² plus one quarter. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.norm_sq_transport_factor` (`Breakdown/Cert/CoerciveFrequencySeminormTransportModes.lean:1002`).

### Breakdown.Cert.CoerciveFrequencySeminormWeight

A weighted spatial estimate supplies finite radially damped velocity energy for the frequency-seminorm argument.

**Paper context:** Appendix B, Proposition B.1: weighted velocity control entering the frequency estimate.

**Theorem: Finite quadratically damped energy.** The period integral of ‖v‖² divided by 1 + ‖y‖² is finite under the perturbation hypotheses. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.weighted_velocity_lt_top` (`Breakdown/Cert/CoerciveFrequencySeminormWeight.lean:17`).

### Breakdown.Cert.CoerciveFrequencySeminormWeightSlice

The weighted estimate is proved on spatial slices using compactly supported test fields and integration by parts.

**Paper context:** Appendix B, Proposition B.1: slice-level support for the radial velocity estimate.

**Theorem: Function F is integrable.** Under the stated hypotheses, the function F is integrable. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.integrable_of_vanish_field` (`Breakdown/Cert/CoerciveFrequencySeminormWeightSlice.lean:20`).

**Theorem: A radial Hardy bound for a test field.** The test-field square weighted by 1/(1+|y|²) is bounded by four times its gradient-square integral. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.weighted_sq_le_grad_test` (`Breakdown/Cert/CoerciveFrequencySeminormWeightSlice.lean:24`).

**Theorem: Radial Hardy bound in the energy space.** The radially weighted velocity energy is at most four times the squared Fourier energy-space norm. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.weighted_sq_le_velocity_norm` (`Breakdown/Cert/CoerciveFrequencySeminormWeightSlice.lean:78`).

**Theorem: A radial Hardy bound for weak fields.** The radially weighted velocity-square integral is at most four times the weak-gradient square integral. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.slice_weighted_sq_le` (`Breakdown/Cert/CoerciveFrequencySeminormWeightSlice.lean:116`).

### Breakdown.Cert.CoerciveFrequencySeminormWeightSmooth

Smooth radial damping functions and their derivatives supply the concrete vector fields used to prove the weighted velocity bound.

**Paper context:** Appendix B, Proposition B.1: radial test-field calculus for weighted energy control.

**Definition: An inverse quadratic radial weight.** Use the reciprocal of one plus the squared spatial radius as a radial damping weight. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.radialDamp` (`Breakdown/Cert/CoerciveFrequencySeminormWeightSmooth.lean:16`).

**Definition: A coordinate with radial damping.** Multiply one spatial coordinate by the inverse quadratic radial weight. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.radialField` (`Breakdown/Cert/CoerciveFrequencySeminormWeightSmooth.lean:18`).

**Theorem: The radial denominator is positive.** The quantity 1 + ‖y‖² is strictly positive. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.one_add_norm_sq_pos` (`Breakdown/Cert/CoerciveFrequencySeminormWeightSmooth.lean:20`).

**Theorem: Norm square from coordinates.** The squared Euclidean norm equals the sum of the three coordinate squares. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.norm_sq_eq_sum` (`Breakdown/Cert/CoerciveFrequencySeminormWeightSmooth.lean:22`).

**Theorem: Differentiate the radial damping weight.** The coordinate derivative of 1/(1+|y|²) equals minus twice that coordinate times the squared weight. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.fderiv_radialDamp_apply` (`Breakdown/Cert/CoerciveFrequencySeminormWeightSmooth.lean:26`).

**Theorem: The derivative of a coordinate.** A coordinate function has derivative equal to the corresponding coordinate projection. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.hasFDerivAt_coord` (`Breakdown/Cert/CoerciveFrequencySeminormWeightSmooth.lean:35`).

**Theorem: The radial damping weight is smooth.** Under the stated hypotheses, the inverse quadratic radial weight is smooth. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.contDiff_radialDamp` (`Breakdown/Cert/CoerciveFrequencySeminormWeightSmooth.lean:39`).

**Theorem: Differentiate a damped coordinate.** The matching coordinate derivative is the radial weight minus twice the coordinate square times the squared weight. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.fderiv_radialField` (`Breakdown/Cert/CoerciveFrequencySeminormWeightSmooth.lean:43`).

**Theorem: Radially damped coordinate is smooth.** Under the stated hypotheses, the radially damped coordinate is smooth. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.contDiff_radialField` (`Breakdown/Cert/CoerciveFrequencySeminormWeightSmooth.lean:53`).

**Theorem: The radial field controls its weight.** The divergence of the radially damped coordinate field is at least the radial damping weight. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.radialDiv_ge` (`Breakdown/Cert/CoerciveFrequencySeminormWeightSmooth.lean:56`).

**Theorem: Function F is integrable.** Under the stated hypotheses, the function F is integrable. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.integrable_of_vanish` (`Breakdown/Cert/CoerciveFrequencySeminormWeightSmooth.lean:72`).

**Theorem: A scalar radial Hardy inequality.** The scalar field square weighted by 1/(1+|y|²) has integral at most four times the gradient-square integral. Source: `Breakdown.Coercive.FrequencySeminorm.Internal.weighted_sq_le_grad_smooth` (`Breakdown/Cert/CoerciveFrequencySeminormWeightSmooth.lean:76`).

### Breakdown.Cert.CoerciveGain

Rotation difference quotients and weak angular derivatives bound the vector and matrix frame generators, providing the frequency gain used by the mode estimates.

**Paper context:** Appendix B, Proposition B.1: rotational mode gain and weak derivative control.

**Definition: The axial rotation vector field.** Use the vector (-y₁, y₀, 0) as the infinitesimal generator of axial rotation. Source: `Breakdown.Coercive.GainInternal.azimuthalField` (`Breakdown/Cert/CoerciveGain.lean:14`).

**Theorem: The angular generator's norm square.** The squared norm of the axial rotation generator equals the squared cylindrical radius. Source: `Breakdown.Coercive.GainInternal.azimuthalField_sq` (`Breakdown/Cert/CoerciveGain.lean:16`).

**Theorem: Extract an angular derivative gain.** The supplied angular identity yields the inverse-radius lower bound with coefficient (|k|-c)². Source: `Breakdown.Coercive.GainInternal.gain_of_identity` (`Breakdown/Cert/CoerciveGain.lean:21`).

**Theorem: Combine iterated full-measure claims.** The iterated almost-everywhere statement holds almost everywhere for the space-time product measure. Source: `Breakdown.Coercive.GainInternal.ae_of_ae_ae` (`Breakdown/Cert/CoerciveGain.lean:74`).

**Theorem: Axial rotation is continuous.** Under the stated hypotheses, the axial rotation is continuous. Source: `Breakdown.Coercive.GainInternal.continuous_axialRot` (`Breakdown/Cert/CoerciveGain.lean:89`).

**Theorem: Axial rotation is continuous.** Under the stated hypotheses, the axial rotation is continuous. Source: `Breakdown.Coercive.GainInternal.continuous_axialRot_comp` (`Breakdown/Cert/CoerciveGain.lean:93`).

**Theorem: Continuous coordinates of a field.** Each coordinate of the stated continuous vector field is continuous. Source: `Breakdown.Coercive.GainInternal.continuous_coord` (`Breakdown/Cert/CoerciveGain.lean:98`).

**Theorem: Axial rotation is measurable.** Under the stated hypotheses, the axial rotation is measurable. Source: `Breakdown.Coercive.GainInternal.measurable_axialRot` (`Breakdown/Cert/CoerciveGain.lean:103`).

**Theorem: Orbit maps preserve null preimages.** Under the stated hypotheses, the time-shift and rotation evaluation map maps preimages of null sets to null sets under the stated measures. Source: `Breakdown.Coercive.GainInternal.shift_quasiMeasurePreserving` (`Breakdown/Cert/CoerciveGain.lean:106`).

**Theorem: Null sets under restricted orbit maps.** Under the stated hypotheses, the restricted time-shift and rotation evaluation map maps preimages of null sets to null sets under the stated measures. Source: `Breakdown.Coercive.GainInternal.shift_quasiMeasurePreserving_restrict` (`Breakdown/Cert/CoerciveGain.lean:153`).

**Theorem: Fourier mode average is measurable.** Under the stated hypotheses, the Fourier mode average is strongly measurable up to a null set. Source: `Breakdown.Coercive.GainInternal.aesm_average` (`Breakdown/Cert/CoerciveGain.lean:165`).

**Theorem: Velocity mode is measurable.** Under the stated hypotheses, the velocity mode is strongly measurable up to a null set. Source: `Breakdown.Coercive.GainInternal.modeVel_aesm` (`Breakdown/Cert/CoerciveGain.lean:198`).

**Theorem: Gradient mode is measurable.** Under the stated hypotheses, the gradient mode is strongly measurable up to a null set. Source: `Breakdown.Coercive.GainInternal.modeGrad_aesm` (`Breakdown/Cert/CoerciveGain.lean:208`).

**Theorem: Second-derivative mode is measurable.** Under the stated hypotheses, the second-derivative mode is strongly measurable up to a null set. Source: `Breakdown.Coercive.GainInternal.modeSecondDeriv_aesm` (`Breakdown/Cert/CoerciveGain.lean:228`).

**Theorem: Read a real vector coordinate.** A coordinate of the reconstructed real vector is the real part of the matching complex coordinate. Source: `Breakdown.Coercive.GainInternal.reVec_apply` (`Breakdown/Cert/CoerciveGain.lean:255`).

**Theorem: Read an imaginary vector coordinate.** A coordinate of the reconstructed imaginary vector is the imaginary part of the matching complex coordinate. Source: `Breakdown.Coercive.GainInternal.imVec_apply` (`Breakdown/Cert/CoerciveGain.lean:258`).

**Theorem: Read a real matrix column.** Evaluating the reconstructed real matrix on a coordinate basis vector returns the real part of the selected matrix entry. Source: `Breakdown.Coercive.GainInternal.reMat_apply` (`Breakdown/Cert/CoerciveGain.lean:261`).

**Theorem: Read an imaginary matrix column.** Evaluating the reconstructed imaginary matrix on a coordinate basis vector returns the imaginary part of the selected matrix entry. Source: `Breakdown.Coercive.GainInternal.imMat_apply` (`Breakdown/Cert/CoerciveGain.lean:264`).

**Theorem: Local integrability after complexifying.** The complex-valued coercion of each coordinate of the stated locally integrable real field is locally integrable. Source: `Breakdown.Coercive.GainInternal.li_coord` (`Breakdown/Cert/CoerciveGain.lean:267`).

**Theorem: Local integrability of operator columns.** Under the stated hypotheses, the selected column of the operator field is locally integrable. Source: `Breakdown.Coercive.GainInternal.li_apply` (`Breakdown/Cert/CoerciveGain.lean:274`).

**Theorem: Function f is integrable.** Under the stated hypotheses, the function f is locally integrable. Source: `Breakdown.Coercive.GainInternal.li_complex` (`Breakdown/Cert/CoerciveGain.lean:281`).

**Theorem: Continuity of a test partial.** Under the stated hypotheses, the coordinate derivative of the test function is continuous. Source: `Breakdown.Coercive.GainInternal.test_deriv_continuous` (`Breakdown/Cert/CoerciveGain.lean:291`).

**Theorem: Compact support of a test partial.** Under the stated hypotheses, the coordinate derivative of the test function has compact support. Source: `Breakdown.Coercive.GainInternal.test_deriv_support` (`Breakdown/Cert/CoerciveGain.lean:295`).

**Theorem: Coordinates commute with integration.** Taking a vector coordinate commutes with the stated Bochner integral. Source: `Breakdown.Coercive.GainInternal.integral_coord` (`Breakdown/Cert/CoerciveGain.lean:299`).

**Theorem: A real coordinate weak derivative.** The coordinatewise weak-gradient pairing equals the negative pairing with the derivative of the scalar test. Source: `Breakdown.Coercive.GainInternal.weak_component_real` (`Breakdown/Cert/CoerciveGain.lean:304`).

**Theorem: Complex coordinate weak derivatives.** The complex field and gradient coordinates are locally integrable and satisfy their coordinatewise weak integration-by-parts identities. Source: `Breakdown.Coercive.GainInternal.weak_components` (`Breakdown/Cert/CoerciveGain.lean:315`).

**Theorem: The derivative of axial rotation at zero.** Differentiating the angle of axial rotation at zero gives the axial rotation generator. Source: `Breakdown.Coercive.GainInternal.hasDerivAt_axialRot` (`Breakdown/Cert/CoerciveGain.lean:350`).

**Definition: Differentiate around the axis.** Take the directional derivative along the axial rotation vector field. Source: `Breakdown.Coercive.GainInternal.azimuthalDeriv` (`Breakdown/Cert/CoerciveGain.lean:372`).

**Theorem: Linear angular-generator coordinates.** Each coordinate of the angular generator is a continuous linear functional that vanishes on its own basis vector. Source: `Breakdown.Coercive.GainInternal.azimuthal_linear` (`Breakdown/Cert/CoerciveGain.lean:375`).

**Theorem: Rotation preserves spatial integration.** Integrating a function after axial rotation gives the original spatial integral. Source: `Breakdown.Coercive.GainInternal.rot_integral` (`Breakdown/Cert/CoerciveGain.lean:384`).

**Theorem: Opposite rotations cancel.** Rotating by an angle and then its negative returns the original vector. Source: `Breakdown.Coercive.GainInternal.rot_inv` (`Breakdown/Cert/CoerciveGain.lean:390`).

**Theorem: Complex test products are integrable.** The product of the complexified compact test function and the stated locally integrable complex field is integrable. Source: `Breakdown.Coercive.GainInternal.test_integrable` (`Breakdown/Cert/CoerciveGain.lean:394`).

**Theorem: Weak differentiation around the axis.** The gradient contracted with the angular generator transfers to minus the angular derivative of the scalar test under integration. Source: `Breakdown.Coercive.GainInternal.weak_along` (`Breakdown/Cert/CoerciveGain.lean:400`).

**Theorem: Differentiate a tested rotation.** The rotation difference quotients of the tested integral converge to minus the pairing with the test function's azimuthal derivative. Source: `Breakdown.Coercive.GainInternal.slope_limit` (`Breakdown/Cert/CoerciveGain.lean:451`).

**Theorem: The weak angular-mode identity.** Almost everywhere, angular differentiation of the mode equals its frequency times i plus the frame-action term. Source: `Breakdown.Coercive.GainInternal.angular_identity` (`Breakdown/Cert/CoerciveGain.lean:585`).

**Theorem: The vector frame generator has norm ≤1.** The angular frame generator on complex vectors does not increase the squared complex norm. Source: `Breakdown.Coercive.GainInternal.vel_bound` (`Breakdown/Cert/CoerciveGain.lean:675`).

**Theorem: A two-square bound for complex vectors.** The squared norm of a complex-vector sum is at most twice the sum of its two squared norms. Source: `Breakdown.Coercive.GainInternal.cnormSq_add_le` (`Breakdown/Cert/CoerciveGain.lean:680`).

**Theorem: The matrix frame generator has norm ≤2.** The angular frame generator on complex matrices has squared norm at most four times the matrix norm square. Source: `Breakdown.Coercive.GainInternal.grad_bound` (`Breakdown/Cert/CoerciveGain.lean:689`).

**Theorem: Differentiate the inverse rotation.** Differentiating the negative-angle rotation at zero gives minus the axial rotation generator. Source: `Breakdown.Coercive.GainInternal.hasDerivAt_axialRot_neg` (`Breakdown/Cert/CoerciveGain.lean:719`).

**Theorem: Zero rotation fixes the coordinate basis.** At zero angle, a rotated coordinate basis vector has its usual Kronecker-delta coordinates. Source: `Breakdown.Coercive.GainInternal.unit_apply` (`Breakdown/Cert/CoerciveGain.lean:727`).

**Theorem: Angular frequency controls derivatives.** The supplied hypotheses establish the two inverse-radius lower bounds from angular frequencies at least two. Source: `Breakdown.Coercive.modeAzimuthalGainHolds_proof_of` (`Breakdown/Cert/CoerciveGain.lean:735`).

### Breakdown.Cert.CoerciveMain

The concrete proofs of rotation, Parseval, weak derivatives, smooth identities, approximation, and absorption are supplied to the assembly theorems to establish the multiplier-density and certificate coercivity endpoints.

**Paper context:** Appendix B, Proposition B.1, and §7: proof assembly connecting analytic multiplier estimates to the certificate.

**Theorem: Establish the projection specification.** The established spectral-projection specification implies the certificate projection interface. Source: `Breakdown.Coercive.projectionHolds_of_spec` (`Breakdown/Cert/CoerciveMain.lean:44`).

**Theorem: Parseval for fields and derivatives.** The supplied hypotheses establish the mode-square identities for velocity and derivatives together with the corresponding pairing sum. Source: `Breakdown.Coercive.modeSquareSumHolds_proved` (`Breakdown/Cert/CoerciveMain.lean:47`).

**Theorem: A multiplier with a density bound.** The supplied hypotheses establish existence of a multiplier with the stated norm bound and signed mode-density inequality. Source: `Breakdown.Coercive.multiplierDensityHolds_proof` (`Breakdown/Cert/CoerciveMain.lean:50`).

**Theorem: A piece multiplier with a density bound.** The supplied hypotheses establish existence of a piece multiplier with the stated norm bound and signed piece-density inequality. Source: `Breakdown.Coercive.pieceMultiplierDensityHolds_proof` (`Breakdown/Cert/CoerciveMain.lean:69`).

**Theorem: Angular frequency controls derivatives.** The supplied hypotheses establish the two inverse-radius lower bounds from angular frequencies at least two. Source: `Breakdown.Coercive.modeAzimuthalGainHolds_proof` (`Breakdown/Cert/CoerciveMain.lean:89`).

**Theorem: Bound the mean stretching term.** The supplied hypotheses establish control of the averaged negative stretching form by the summed stretching charges. Source: `Breakdown.Coercive.stretchMeanBoundHolds_proof` (`Breakdown/Cert/CoerciveMain.lean:95`).

### Breakdown.Cert.CoerciveModeDerivative

Averaging along time-rotation orbits preserves weak velocity and gradient derivatives and zero divergence, after the required product-measure and integrability arguments are established.

**Paper context:** Appendix B, Proposition B.1: differentiation of the Fourier-mode fields.

**Theorem: Axial rotation is continuous.** Under the stated hypotheses, the axial rotation is continuous. Source: `Breakdown.Coercive.ModeDerivative.Internal.continuous_axialRot_prod` (`Breakdown/Cert/CoerciveModeDerivative.lean:14`).

**Theorem: Opposite rotations cancel.** Rotating by an angle and then its negative returns the original vector. Source: `Breakdown.Coercive.ModeDerivative.Internal.axialRot_neg_apply` (`Breakdown/Cert/CoerciveModeDerivative.lean:18`).

**Theorem: Cancel opposite rotations.** Rotating by the negative angle and then the original angle returns the vector. Source: `Breakdown.Coercive.ModeDerivative.Internal.axialRot_apply_neg` (`Breakdown/Cert/CoerciveModeDerivative.lean:22`).

**Theorem: Axial rotation preserves length.** Axial rotation preserves the Euclidean norm. Source: `Breakdown.Coercive.ModeDerivative.Internal.norm_axialRot` (`Breakdown/Cert/CoerciveModeDerivative.lean:26`).

**Definition: Rotate position with its angle.** Rotate the spatial component by the angle coordinate while keeping the time-angle pair fixed. Source: `Breakdown.Coercive.ModeDerivative.Internal.rotSkew` (`Breakdown/Cert/CoerciveModeDerivative.lean:30`).

**Theorem: Read the angle-dependent rotation.** The orbit-coordinate map leaves the time-angle pair fixed and rotates the spatial coordinate by the stored angle. Source: `Breakdown.Coercive.ModeDerivative.Internal.rotSkew_apply` (`Breakdown/Cert/CoerciveModeDerivative.lean:40`).

**Theorem: Angle-dependent spatial rotation formula.** Under the stated hypotheses, the angle-dependent spatial rotation preserves the stated measure. Source: `Breakdown.Coercive.ModeDerivative.Internal.rotSkew_measurePreserving` (`Breakdown/Cert/CoerciveModeDerivative.lean:43`).

**Definition: One period and one angular turn.** Take product volume on the time interval (0,1] and angle interval (0,2π]. Source: `Breakdown.Coercive.ModeDerivative.Internal.angleMeasure` (`Breakdown/Cert/CoerciveModeDerivative.lean:60`).

**Theorem: Rotated orbit maps preserve null sets.** Under the stated hypotheses, the time-shift and rotation evaluation map maps preimages of null sets to null sets under the stated measures. Source: `Breakdown.Coercive.ModeDerivative.Internal.quasiMeasurePreserving_rotated` (`Breakdown/Cert/CoerciveModeDerivative.lean:63`).

**Theorem: Integrable time-rotation orbit data.** Under the stated hypotheses, the field evaluated along time-shift and rotation orbits is integrable. Source: `Breakdown.Coercive.ModeDerivative.Internal.integrable_rotated` (`Breakdown/Cert/CoerciveModeDerivative.lean:79`).

**Theorem: Expand a vector in the coordinate basis.** A physical vector is the sum of its coordinate multiples of the three unit vectors. Source: `Breakdown.Coercive.ModeDerivative.Internal.vec_eq_sum` (`Breakdown/Cert/CoerciveModeDerivative.lean:139`).

**Theorem: Test a weak gradient in any direction.** The weak-gradient identity holds in an arbitrary fixed direction, with the derivative transferred to the scalar test. Source: `Breakdown.Coercive.ModeDerivative.Internal.weakGradient_apply` (`Breakdown/Cert/CoerciveModeDerivative.lean:144`).

**Theorem: Isometries preserve local integrability.** Composing the stated locally integrable field with the specified linear isometry preserves local integrability. Source: `Breakdown.Coercive.ModeDerivative.Internal.locallyIntegrable_comp_isometry` (`Breakdown/Cert/CoerciveModeDerivative.lean:175`).

**Theorem: Isometries preserve spatial integrals.** Composition with the stated linear isometry preserves the spatial integral. Source: `Breakdown.Coercive.ModeDerivative.Internal.integral_comp_isometry` (`Breakdown/Cert/CoerciveModeDerivative.lean:183`).

**Theorem: Rotate a weak-gradient identity.** The rotated field has weak gradient given by conjugating the original weak gradient by the same rotation. Source: `Breakdown.Coercive.ModeDerivative.Internal.weakGradient_rotate` (`Breakdown/Cert/CoerciveModeDerivative.lean:187`).

**Theorem: Function F is integrable.** Under the stated hypotheses, the function F is integrable. Source: `Breakdown.Coercive.ModeDerivative.Internal.integrable_of_restrict_tsupport` (`Breakdown/Cert/CoerciveModeDerivative.lean:247`).

**Theorem: Interchange averaging and pairing.** The weighted spatial integral of a parameter average equals the parameter average of the weighted spatial integral. Source: `Breakdown.Coercive.ModeDerivative.Internal.average_swap` (`Breakdown/Cert/CoerciveModeDerivative.lean:256`).

**Theorem: Weighted orbit data are integrable.** The stated scalar-weighted orbit field is integrable over the product measure. Source: `Breakdown.Coercive.ModeDerivative.Internal.integrable_weight` (`Breakdown/Cert/CoerciveModeDerivative.lean:300`).

**Theorem: Average weak gradients.** The parameter average of the weak gradients is the weak gradient of the averaged field under the stated integrability hypotheses. Source: `Breakdown.Coercive.ModeDerivative.Internal.weakGradient_average` (`Breakdown/Cert/CoerciveModeDerivative.lean:312`).

**Definition: Choose the rotation isometry.** Choose the linear isometry whose action is the stated axial rotation. Source: `Breakdown.Coercive.ModeDerivative.Internal.rotIso` (`Breakdown/Cert/CoerciveModeDerivative.lean:351`).

**Theorem: The chosen isometry is axial rotation.** The selected linear isometry acts exactly as axial rotation by its chosen angle. Source: `Breakdown.Coercive.ModeDerivative.Internal.rotIso_apply` (`Breakdown/Cert/CoerciveModeDerivative.lean:353`).

**Theorem: Opposite rotation is the inverse.** The inverse of the selected rotation isometry acts as axial rotation by the negative angle. Source: `Breakdown.Coercive.ModeDerivative.Internal.rotIso_symm_apply` (`Breakdown/Cert/CoerciveModeDerivative.lean:356`).

**Definition: The temporal and angular phase.** Add 2π times the temporal frequency and time shift to the angular frequency times the angle shift. Source: `Breakdown.Coercive.ModeDerivative.Internal.modePhase` (`Breakdown/Cert/CoerciveModeDerivative.lean:360`).

**Definition: Real part of the Fourier weight.** Divide the cosine of the mode phase by 2π. Source: `Breakdown.Coercive.ModeDerivative.Internal.weightRe` (`Breakdown/Cert/CoerciveModeDerivative.lean:362`).

**Definition: Imaginary part of the Fourier weight.** Divide the negative sine of the mode phase by 2π. Source: `Breakdown.Coercive.ModeDerivative.Internal.weightIm` (`Breakdown/Cert/CoerciveModeDerivative.lean:364`).

**Definition: Conjugate a derivative by rotation.** Rotate the input of a linear map and rotate its output back. Source: `Breakdown.Coercive.ModeDerivative.Internal.rotConj` (`Breakdown/Cert/CoerciveModeDerivative.lean:366`).

**Theorem: Read a conjugated derivative.** The conjugated linear map rotates its input, applies the original map, and rotates the output back. Source: `Breakdown.Coercive.ModeDerivative.Internal.rotConj_apply` (`Breakdown/Cert/CoerciveModeDerivative.lean:370`).

**Definition: A shifted and rotated velocity.** Shift time, rotate position, and rotate the velocity value back into the original frame. Source: `Breakdown.Coercive.ModeDerivative.Internal.velFamily` (`Breakdown/Cert/CoerciveModeDerivative.lean:375`).

**Definition: A shifted and rotated gradient.** Evaluate the gradient on the shifted orbit and conjugate it by the axial rotation. Source: `Breakdown.Coercive.ModeDerivative.Internal.gradFamily` (`Breakdown/Cert/CoerciveModeDerivative.lean:378`).

**Definition: One rotated gradient column.** Evaluate the gradient on a rotated basis vector and rotate the result back. Source: `Breakdown.Coercive.ModeDerivative.Internal.columnFamily` (`Breakdown/Cert/CoerciveModeDerivative.lean:382`).

**Definition: A rotated second-derivative column.** Fix one rotated derivative direction and conjugate the remaining second-derivative map by rotation. Source: `Breakdown.Coercive.ModeDerivative.Internal.secondDerivFamily` (`Breakdown/Cert/CoerciveModeDerivative.lean:386`).

**Theorem: The cosine Fourier weight is bounded.** The absolute value of the normalised cosine Fourier weight is at most one. Source: `Breakdown.Coercive.ModeDerivative.Internal.abs_weightRe_le` (`Breakdown/Cert/CoerciveModeDerivative.lean:390`).

**Theorem: The sine Fourier weight is bounded.** The absolute value of the normalised negative-sine Fourier weight is at most one. Source: `Breakdown.Coercive.ModeDerivative.Internal.abs_weightIm_le` (`Breakdown/Cert/CoerciveModeDerivative.lean:396`).

**Theorem: Cosine Fourier weight is measurable.** Under the stated hypotheses, the cosine Fourier weight is measurable. Source: `Breakdown.Coercive.ModeDerivative.Internal.measurable_weightRe` (`Breakdown/Cert/CoerciveModeDerivative.lean:402`).

**Theorem: The negative-sine weight is measurable.** Under the stated hypotheses, the negative sine Fourier weight is measurable. Source: `Breakdown.Coercive.ModeDerivative.Internal.measurable_weightIm` (`Breakdown/Cert/CoerciveModeDerivative.lean:405`).

**Theorem: Evaluate the time-angle phase.** The phase at (τ,φ) is 2π times the temporal frequency times τ plus the angular frequency times φ. Source: `Breakdown.Coercive.ModeDerivative.Internal.modePhase_apply` (`Breakdown/Cert/CoerciveModeDerivative.lean:408`).

**Theorem: The mode average as one product integral.** The mode average equals the normalised complex-exponential integral over the time-angle rectangle. Source: `Breakdown.Coercive.ModeDerivative.Internal.modeAverage_eq_integral` (`Breakdown/Cert/CoerciveModeDerivative.lean:411`).

**Theorem: Real modes are cosine averages.** The real part of the Fourier mode average is the integral against the normalised cosine weight. Source: `Breakdown.Coercive.ModeDerivative.Internal.re_modeAverage` (`Breakdown/Cert/CoerciveModeDerivative.lean:435`).

**Theorem: Imaginary modes use negative sine.** The imaginary part of the Fourier mode average is the integral against the normalised negative-sine weight. Source: `Breakdown.Coercive.ModeDerivative.Internal.im_modeAverage` (`Breakdown/Cert/CoerciveModeDerivative.lean:453`).

**Theorem: Integrability of weighted parameter data.** Under the stated hypotheses, the scalar-weighted parameter field is integrable. Source: `Breakdown.Coercive.ModeDerivative.Internal.integrable_weight_smul` (`Breakdown/Cert/CoerciveModeDerivative.lean:471`).

**Theorem: Coordinates commute with integration.** Taking a vector coordinate commutes with the stated Bochner integral. Source: `Breakdown.Coercive.ModeDerivative.Internal.integral_coord` (`Breakdown/Cert/CoerciveModeDerivative.lean:481`).

**Theorem: Integrable parameter-field coordinates.** Under the stated hypotheses, the selected coordinate of the parameter field is integrable. Source: `Breakdown.Coercive.ModeDerivative.Internal.integrable_coord` (`Breakdown/Cert/CoerciveModeDerivative.lean:485`).

**Theorem: Basis values determine a linear map.** Two continuous linear maps agree when they agree on the three coordinate basis vectors. Source: `Breakdown.Coercive.ModeDerivative.Internal.clm_ext_unitVector` (`Breakdown/Cert/CoerciveModeDerivative.lean:489`).

**Theorem: Read a column of the real matrix.** Applying the reconstructed real matrix to a basis vector returns the vector of real parts of that column. Source: `Breakdown.Coercive.ModeDerivative.Internal.reMat_apply_unitVector` (`Breakdown/Cert/CoerciveModeDerivative.lean:495`).

**Theorem: Read a column of the imaginary matrix.** Applying the reconstructed imaginary matrix to a basis vector returns the vector of imaginary parts of that column. Source: `Breakdown.Coercive.ModeDerivative.Internal.imMat_apply_unitVector` (`Breakdown/Cert/CoerciveModeDerivative.lean:500`).

**Theorem: Real vector modes are weighted averages.** The real vector reconstructed from a mode average equals the vector-valued cosine-weighted average. Source: `Breakdown.Coercive.ModeDerivative.Internal.reVec_modeAverage` (`Breakdown/Cert/CoerciveModeDerivative.lean:505`).

**Theorem: Imaginary vector modes as averages.** The imaginary vector reconstructed from a mode average equals the vector-valued negative-sine-weighted average. Source: `Breakdown.Coercive.ModeDerivative.Internal.imVec_modeAverage` (`Breakdown/Cert/CoerciveModeDerivative.lean:516`).

**Theorem: Real matrix modes are weighted averages.** The real matrix reconstructed from a mode average equals the matrix-valued cosine-weighted average. Source: `Breakdown.Coercive.ModeDerivative.Internal.reMat_modeAverage` (`Breakdown/Cert/CoerciveModeDerivative.lean:527`).

**Theorem: Imaginary matrix modes as averages.** The imaginary matrix reconstructed from a mode average equals the matrix-valued negative-sine-weighted average. Source: `Breakdown.Coercive.ModeDerivative.Internal.imMat_modeAverage` (`Breakdown/Cert/CoerciveModeDerivative.lean:538`).

**Theorem: Weak derivatives ignore null-set changes.** Changing a field and its weak gradient on null sets preserves the weak-gradient relation. Source: `Breakdown.Coercive.ModeDerivative.Internal.isWeakGradient_congr_ae` (`Breakdown/Cert/CoerciveModeDerivative.lean:549`).

**Theorem: Integrable slices almost everywhere.** The stated product-integrability assumption gives an integrable parameter slice for almost every spatial point. Source: `Breakdown.Coercive.ModeDerivative.Internal.ae_slice_integrable` (`Breakdown/Cert/CoerciveModeDerivative.lean:560`).

**Theorem: Linear combinations of weak gradients.** The finite linear combination of weak gradients is the weak gradient of the same combination of fields. Source: `Breakdown.Coercive.ModeDerivative.Internal.weakGradient_sum` (`Breakdown/Cert/CoerciveModeDerivative.lean:574`).

**Theorem: A gradient column's weak derivative.** Evaluating the gradient on a fixed vector gives a field whose weak gradient is the matching second-derivative column. Source: `Breakdown.Coercive.ModeDerivative.Internal.weakGradient_column_apply` (`Breakdown/Cert/CoerciveModeDerivative.lean:610`).

**Theorem: A shift preserves full-measure claims.** The given almost-everywhere time property remains true after the fixed shift on almost every averaging parameter. Source: `Breakdown.Coercive.ModeDerivative.Internal.ae_shift` (`Breakdown/Cert/CoerciveModeDerivative.lean:625`).

**Theorem: Weak derivatives along velocity orbits.** For almost every averaging parameter, the rotated gradient is the weak gradient of the shifted and rotated velocity. Source: `Breakdown.Coercive.ModeDerivative.Internal.ae_weakGradient_vel` (`Breakdown/Cert/CoerciveModeDerivative.lean:632`).

**Theorem: Weak derivatives along gradient orbits.** For almost every averaging parameter, the rotated second-derivative column is the weak gradient of the rotated gradient column. Source: `Breakdown.Coercive.ModeDerivative.Internal.ae_weakGradient_column` (`Breakdown/Cert/CoerciveModeDerivative.lean:641`).

**Theorem: Rotation preserves integrability.** Applying the stated angle-dependent isometry to the integrable field preserves integrability under the product measure. Source: `Breakdown.Coercive.ModeDerivative.Internal.integrable_of_rot` (`Breakdown/Cert/CoerciveModeDerivative.lean:651`).

**Theorem: Axial rotation is continuous.** Under the stated hypotheses, the axial rotation is continuous. Source: `Breakdown.Coercive.ModeDerivative.Internal.continuous_axialRot_comp` (`Breakdown/Cert/CoerciveModeDerivative.lean:659`).

**Theorem: Coordinate unit vectors have norm one.** Every coordinate unit vector has Euclidean norm one. Source: `Breakdown.Coercive.ModeDerivative.Internal.norm_unitVector_one` (`Breakdown/Cert/CoerciveModeDerivative.lean:664`).

**Theorem: Rotated derivative is continuous.** Under the stated hypotheses, the rotated derivative is continuous. Source: `Breakdown.Coercive.ModeDerivative.Internal.continuous_rotConj` (`Breakdown/Cert/CoerciveModeDerivative.lean:667`).

**Theorem: Rotation bounds the derivative norm.** The operator norm of the rotation-conjugated derivative is at most that of the original derivative. Source: `Breakdown.Coercive.ModeDerivative.Internal.norm_rotConj_le` (`Breakdown/Cert/CoerciveModeDerivative.lean:677`).

**Theorem: Velocity orbit is integrable.** Under the stated hypotheses, the shifted and rotated velocity is integrable. Source: `Breakdown.Coercive.ModeDerivative.Internal.integrable_velFamily` (`Breakdown/Cert/CoerciveModeDerivative.lean:684`).

**Theorem: Gradient orbit is integrable.** Under the stated hypotheses, the shifted and rotated gradient is integrable. Source: `Breakdown.Coercive.ModeDerivative.Internal.integrable_gradFamily` (`Breakdown/Cert/CoerciveModeDerivative.lean:693`).

**Theorem: Rotated gradient column is integrable.** Under the stated hypotheses, the rotated gradient column is integrable. Source: `Breakdown.Coercive.ModeDerivative.Internal.integrable_columnFamily` (`Breakdown/Cert/CoerciveModeDerivative.lean:701`).

**Theorem: Continuous rotated Hessian columns.** Under the stated hypotheses, the rotation-conjugated Hessian column is continuous. Source: `Breakdown.Coercive.ModeDerivative.Internal.continuous_secondDerivConj` (`Breakdown/Cert/CoerciveModeDerivative.lean:716`).

**Theorem: Integrable rotated Hessian columns.** Under the stated hypotheses, the rotated second-derivative column is integrable. Source: `Breakdown.Coercive.ModeDerivative.Internal.integrable_secondDerivFamily` (`Breakdown/Cert/CoerciveModeDerivative.lean:731`).

**Theorem: The coordinate diagonal sum is the trace.** The sum of the three diagonal coordinates of a linear map equals its trace. Source: `Breakdown.Coercive.ModeDerivative.Internal.sum_diag_eq_trace` (`Breakdown/Cert/CoerciveModeDerivative.lean:746`).

**Theorem: Trace is invariant under frame rotation.** Conjugating a linear map by axial rotation leaves the sum of its diagonal entries unchanged. Source: `Breakdown.Coercive.ModeDerivative.Internal.diag_sum_rotate` (`Breakdown/Cert/CoerciveModeDerivative.lean:753`).

**Theorem: Shift-rotation maps preserve measure.** Under the stated hypotheses, the time-shift and rotation transformation preserves the stated measure. Source: `Breakdown.Coercive.ModeDerivative.Internal.measurePreserving_shiftRot` (`Breakdown/Cert/CoerciveModeDerivative.lean:766`).

**Theorem: Orbit maps preserve null preimages.** Under the stated hypotheses, the time-shift and rotation evaluation map maps preimages of null sets to null sets under the stated measures. Source: `Breakdown.Coercive.ModeDerivative.Internal.quasiMeasurePreserving_shiftRot` (`Breakdown/Cert/CoerciveModeDerivative.lean:789`).

**Theorem: Recover an almost-everywhere zero field.** The iterated almost-everywhere zero statement implies the asserted almost-everywhere zero field. Source: `Breakdown.Coercive.ModeDerivative.Internal.ae_zero_of_ae_ae` (`Breakdown/Cert/CoerciveModeDerivative.lean:796`).

**Theorem: Weak gradients have zero trace.** The weak gradient of the solenoidal perturbation has zero coordinate trace almost everywhere. Source: `Breakdown.Coercive.ModeDerivative.Internal.ae_trace_zero` (`Breakdown/Cert/CoerciveModeDerivative.lean:811`).

**Theorem: Zero trace on almost every orbit.** The shifted and rotated weak-gradient trace is zero for almost every space-time point and averaging parameter. Source: `Breakdown.Coercive.ModeDerivative.Internal.ae_ae_trace_rot` (`Breakdown/Cert/CoerciveModeDerivative.lean:820`).

**Theorem: Integrable bounded orbit data.** Under the stated hypotheses, the field evaluated along bounded time-rotation orbits is integrable. Source: `Breakdown.Coercive.ModeDerivative.Internal.integrable_shiftRot_box` (`Breakdown/Cert/CoerciveModeDerivative.lean:827`).

**Theorem: Integrable shifted rotation slices.** The shifted and rotated field is integrable over the time-angle rectangle at almost every space-time point. Source: `Breakdown.Coercive.ModeDerivative.Internal.ae_integrable_shiftRot` (`Breakdown/Cert/CoerciveModeDerivative.lean:863`).

**Theorem: A product integral for orbit averages.** The iterated interval integral over time and angle equals the integral over their product measure. Source: `Breakdown.Coercive.ModeDerivative.Internal.iterated_intervalIntegral_eq` (`Breakdown/Cert/CoerciveModeDerivative.lean:878`).

**Theorem: Every gradient mode has zero trace.** The trace of each gradient mode is zero almost everywhere in space-time. Source: `Breakdown.Coercive.ModeDerivative.Internal.divergence_part` (`Breakdown/Cert/CoerciveModeDerivative.lean:885`).

**Theorem: Gradient modes are orbit averages.** The gradient mode equals the mode average of the rotation-conjugated gradient family. Source: `Breakdown.Coercive.ModeDerivative.Internal.modeGrad_eq_average` (`Breakdown/Cert/CoerciveModeDerivative.lean:931`).

**Theorem: Hessian columns as orbit averages.** A fixed second-derivative-mode column equals the mode average of its rotated second-derivative family. Source: `Breakdown.Coercive.ModeDerivative.Internal.modeSecondDeriv_eq_average` (`Breakdown/Cert/CoerciveModeDerivative.lean:939`).

**Theorem: Velocity modes retain weak derivatives.** On almost every time slice, the real and imaginary gradient modes are the weak gradients of their velocity modes. Source: `Breakdown.Coercive.ModeDerivative.Internal.velocity_part` (`Breakdown/Cert/CoerciveModeDerivative.lean:950`).

**Theorem: Weak derivatives of gradient modes.** On almost every time slice, each real and imaginary second-derivative-mode column is the weak gradient of its gradient-mode column. Source: `Breakdown.Coercive.ModeDerivative.Internal.secondDeriv_part` (`Breakdown/Cert/CoerciveModeDerivative.lean:979`).

**Theorem: Modes preserve weak derivatives.** The supplied hypotheses establish the weak-gradient identities for real and imaginary modes and the zero trace of the gradient mode. Source: `Breakdown.Coercive.modeDerivativeHolds_of` (`Breakdown/Cert/CoerciveModeDerivative.lean:1018`).

### Breakdown.Cert.CoerciveModeL2

Period-slab L² calculus and Parseval estimates control integrated complex mode pairings, including the continuity of weighted mode sums in their varying field.

**Paper context:** Appendix B, Proposition B.1: L² continuity of mode pairings.

**Definition: Volume over one time period.** Use the product of volume on the closed unit time interval and spatial volume. Source: `Breakdown.Coercive.ModeL2Internal.slab` (`Breakdown/Cert/CoerciveModeL2.lean:14`).

**Definition: A periodic L² field.** Require almost-everywhere strong measurability, time periodicity, and finite squared norm over one period. Source: `Breakdown.Coercive.ModeL2Internal.IsSquareField` (`Breakdown/Cert/CoerciveModeL2.lean:16`).

**Theorem: Coordinate projections are continuous.** Each Euclidean coordinate projection is continuous. Source: `Breakdown.Coercive.ModeL2Internal.continuous_coord` (`Breakdown/Cert/CoerciveModeL2.lean:20`).

**Theorem: Axial rotation is continuous.** Under the stated hypotheses, the axial rotation is continuous. Source: `Breakdown.Coercive.ModeL2Internal.continuous_axialRot_pair` (`Breakdown/Cert/CoerciveModeL2.lean:23`).

**Theorem: Shift-rotation maps preserve measure.** Under the stated hypotheses, the time-shift and rotation transformation preserves the stated measure. Source: `Breakdown.Coercive.ModeL2Internal.measurePreserving_shiftRot` (`Breakdown/Cert/CoerciveModeL2.lean:33`).

**Theorem: Orbit maps preserve null preimages.** Under the stated hypotheses, the time-shift and rotation evaluation map maps preimages of null sets to null sets under the stated measures. Source: `Breakdown.Coercive.ModeL2Internal.quasiMeasurePreserving_shiftRot` (`Breakdown/Cert/CoerciveModeL2.lean:45`).

**Theorem: Nested orbit maps preserve null sets.** Under the stated hypotheses, the time-shift and rotation evaluation map maps preimages of null sets to null sets under the stated measures. Source: `Breakdown.Coercive.ModeL2Internal.quasiMeasurePreserving_shiftRot_nested` (`Breakdown/Cert/CoerciveModeL2.lean:66`).

**Theorem: Measurable transformed orbit fields.** Under the stated hypotheses, the transformed field along time-rotation orbits is strongly measurable up to a null set. Source: `Breakdown.Coercive.ModeL2Internal.aestronglyMeasurable_comp_shiftRot_nested` (`Breakdown/Cert/CoerciveModeL2.lean:74`).

**Theorem: Fourier mode average is measurable.** Under the stated hypotheses, the Fourier mode average is strongly measurable up to a null set. Source: `Breakdown.Coercive.ModeL2Internal.aestronglyMeasurable_modeAverage` (`Breakdown/Cert/CoerciveModeL2.lean:86`).

**Theorem: Rotated vector coordinate is continuous.** Under the stated hypotheses, the rotated vector coordinate is continuous. Source: `Breakdown.Coercive.ModeL2Internal.continuous_rotCoord` (`Breakdown/Cert/CoerciveModeL2.lean:107`).

**Theorem: Continuous rotated matrix coordinates.** Under the stated hypotheses, the rotation-conjugated matrix coordinate is continuous. Source: `Breakdown.Coercive.ModeL2Internal.continuous_rotGradCoord` (`Breakdown/Cert/CoerciveModeL2.lean:113`).

**Theorem: Velocity mode is measurable.** Under the stated hypotheses, the velocity mode is strongly measurable up to a null set. Source: `Breakdown.Coercive.ModeL2Internal.aestronglyMeasurable_modeVel` (`Breakdown/Cert/CoerciveModeL2.lean:127`).

**Theorem: Gradient mode is measurable.** Under the stated hypotheses, the gradient mode is strongly measurable up to a null set. Source: `Breakdown.Coercive.ModeL2Internal.aestronglyMeasurable_modeGrad` (`Breakdown/Cert/CoerciveModeL2.lean:135`).

**Theorem: Ambient null sets remain slab-null.** The period-slab measure is absolutely continuous with respect to full space-time volume. Source: `Breakdown.Coercive.ModeL2Internal.slab_ac` (`Breakdown/Cert/CoerciveModeL2.lean:146`).

**Theorem: Slab times lie in the unit interval.** Almost every point for the slab measure has its time coordinate in the closed unit interval. Source: `Breakdown.Coercive.ModeL2Internal.slab_ae_mem` (`Breakdown/Cert/CoerciveModeL2.lean:151`).

**Theorem: The period integral as a slab integral.** The nonnegative period integral equals the nonnegative integral over the period-slab measure. Source: `Breakdown.Coercive.ModeL2Internal.periodLIntegral_eq_slab` (`Breakdown/Cert/CoerciveModeL2.lean:159`).

**Theorem: Real value of a finite period integral.** For the stated integrable nonnegative field, the real value of the nonnegative period integral equals its ordinary slab integral. Source: `Breakdown.Coercive.ModeL2Internal.toReal_periodLIntegral` (`Breakdown/Cert/CoerciveModeL2.lean:167`).

**Theorem: Integrability on the period slab.** Under the stated hypotheses, the field restricted to the period slab is integrable. Source: `Breakdown.Coercive.ModeL2Internal.integrable_of_periodLIntegral` (`Breakdown/Cert/CoerciveModeL2.lean:173`).

**Theorem: Squared complex norm is nonnegative.** The squared complex norm is nonnegative for the stated data. Source: `Breakdown.Coercive.ModeL2Internal.cnormSq_nonneg` (`Breakdown/Cert/CoerciveModeL2.lean:179`).

**Theorem: Subtract the second complex argument.** The difference of two pairings with the same first argument equals the pairing with the difference of the second arguments. Source: `Breakdown.Coercive.ModeL2Internal.cdot_sub_right` (`Breakdown/Cert/CoerciveModeL2.lean:182`).

**Theorem: Expand the square norm of a difference.** The squared complex-array norm of a − b equals their two squared norms minus twice the real part of their complex pairing. Source: `Breakdown.Coercive.ModeL2Internal.cnormSq_sub` (`Breakdown/Cert/CoerciveModeL2.lean:188`).

**Theorem: Young's inequality for two real factors.** For positive t, the product xy is bounded by half of tx² plus y²/t. Source: `Breakdown.Coercive.ModeL2Internal.mul_le_half_sq` (`Breakdown/Cert/CoerciveModeL2.lean:195`).

**Theorem: Bound a complex pairing by two squares.** The norm of the complex coordinate pairing is at most half the sum of the two complex-vector norm squares. Source: `Breakdown.Coercive.ModeL2Internal.norm_cdot_le` (`Breakdown/Cert/CoerciveModeL2.lean:201`).

**Theorem: An adjustable bound for a signed pairing.** The weighted imaginary pairing is bounded by the absolute weight times the adjustable two-square Young bound. Source: `Breakdown.Coercive.ModeL2Internal.abs_re_weighted_le` (`Breakdown/Cert/CoerciveModeL2.lean:213`).

**Theorem: Field pairing is measurable.** Under the stated hypotheses, the field pairing is strongly measurable up to a null set. Source: `Breakdown.Coercive.ModeL2Internal.aestronglyMeasurable_cdot` (`Breakdown/Cert/CoerciveModeL2.lean:219`).

**Theorem: Squared complex norm is measurable.** Under the stated hypotheses, the squared complex norm is strongly measurable up to a null set. Source: `Breakdown.Coercive.ModeL2Internal.aestronglyMeasurable_cnormSq` (`Breakdown/Cert/CoerciveModeL2.lean:226`).

**Theorem: Integrable velocity-mode squares.** Under the stated hypotheses, the squared norm of the velocity mode is integrable. Source: `Breakdown.Coercive.ModeL2Internal.integrable_cnormSq_modeVel` (`Breakdown/Cert/CoerciveModeL2.lean:232`).

**Theorem: The mode energies sum to physical energy.** The series of integrated velocity-mode squares has sum equal to the physical period L² energy. Source: `Breakdown.Coercive.ModeL2Internal.hasSum_cnormSq_modeVel` (`Breakdown/Cert/CoerciveModeL2.lean:245`).

**Theorem: Integrable real mode pairings.** Under the stated hypotheses, the real pairing of the two velocity modes is integrable. Source: `Breakdown.Coercive.ModeL2Internal.integrable_re_cdot_modeVel` (`Breakdown/Cert/CoerciveModeL2.lean:263`).

**Theorem: Integrable squared mode discrepancies.** Under the stated hypotheses, the squared discrepancy of the two velocity modes is integrable. Source: `Breakdown.Coercive.ModeL2Internal.integrable_cnormSq_modeVel_sub` (`Breakdown/Cert/CoerciveModeL2.lean:282`).

**Theorem: Mode errors sum to physical error energy.** The series of integrated velocity-mode discrepancy squares has sum equal to the physical period L² error. Source: `Breakdown.Coercive.ModeL2Internal.hasSum_cnormSq_modeVel_sub` (`Breakdown/Cert/CoerciveModeL2.lean:289`).

**Definition: An integrated signed mode pairing.** Integrate the real part of i times a mode weight times the complex pairing of two velocity modes. Source: `Breakdown.Coercive.ModeL2Internal.weightedModeTerm` (`Breakdown/Cert/CoerciveModeL2.lean:342`).

**Theorem: Integrable weighted mode pairings.** Under the stated hypotheses, the weighted imaginary velocity-mode pairing is integrable. Source: `Breakdown.Coercive.ModeL2Internal.integrable_weightedMode` (`Breakdown/Cert/CoerciveModeL2.lean:345`).

**Theorem: Read a mode term on the period slab.** The iterated time-space mode pairing equals its integral over the period-slab measure. Source: `Breakdown.Coercive.ModeL2Internal.weightedModeTerm_eq` (`Breakdown/Cert/CoerciveModeL2.lean:372`).

**Theorem: Control a change in a mode pairing.** The difference of weighted mode pairings is bounded by the fixed mode energy and the changed field's mode discrepancy using the stated splitting parameter. Source: `Breakdown.Coercive.ModeL2Internal.weightedModeTerm_sub_le` (`Breakdown/Cert/CoerciveModeL2.lean:379`).

**Theorem: Continuity of weighted mode pairings.** A uniform constant controls the summed change in the weighted mode pairings by the period L² distance, and the relevant series are summable. Source: `Breakdown.Coercive.ModeL2Internal.weightedMode_bound` (`Breakdown/Cert/CoerciveModeL2.lean:415`).

**Theorem: Weighted mode sums are continuous in L².** The summed weighted mode pairing converges when its varying field converges in the stated period L² sense. Source: `Breakdown.Coercive.ModeL2Internal.weightedMode_tendsto` (`Breakdown/Cert/CoerciveModeL2.lean:477`).

**Theorem: A compact continuous field lies in L².** A continuous periodic field with the stated compact spatial support satisfies the periodic L² field conditions. Source: `Breakdown.Coercive.ModeL2Internal.isSquareField_of_continuous` (`Breakdown/Cert/CoerciveModeL2.lean:509`).

### Breakdown.Cert.CoerciveModeRotation

The time-angle Fourier phase and change of angular variable establish the rotation covariance formulas for velocity and gradient modes.

**Paper context:** Appendix B, Proposition B.1: rotation laws for the Fourier-mode decomposition.

**Definition: The complex Fourier phase.** Exponentiate minus i times the combined temporal and angular phase. Source: `Breakdown.Coercive.Internal.ModeRotation.expFactor` (`Breakdown/Cert/CoerciveModeRotation.lean:14`).

**Definition: Measure on the averaging rectangle.** Use product volume on one time period and one full angular turn. Source: `Breakdown.Coercive.Internal.ModeRotation.boxMeasure` (`Breakdown/Cert/CoerciveModeRotation.lean:17`).

**Definition: Move along a time-rotation orbit.** Shift the time coordinate and rotate the spatial coordinate by the averaging parameters. Source: `Breakdown.Coercive.Internal.ModeRotation.orbitMap` (`Breakdown/Cert/CoerciveModeRotation.lean:20`).

**Theorem: The iterated Fourier averaging formula.** The mode average is the complex-exponential integral over one time period and one angular turn, divided by 2π. Source: `Breakdown.Coercive.Internal.ModeRotation.modeAverage_eq` (`Breakdown/Cert/CoerciveModeRotation.lean:22`).

**Theorem: The Fourier phase has norm one.** The complex Fourier phase has norm one. Source: `Breakdown.Coercive.Internal.ModeRotation.norm_expFactor` (`Breakdown/Cert/CoerciveModeRotation.lean:26`).

**Theorem: Complex Fourier phase is continuous.** Under the stated hypotheses, the complex Fourier phase is continuous. Source: `Breakdown.Coercive.Internal.ModeRotation.continuous_expFactor` (`Breakdown/Cert/CoerciveModeRotation.lean:30`).

**Theorem: An angular shift changes the phase.** Replacing the angle φ by φ − ψ multiplies the Fourier phase by exp(i ι₂ ψ). Source: `Breakdown.Coercive.Internal.ModeRotation.expFactor_sub` (`Breakdown/Cert/CoerciveModeRotation.lean:34`).

**Theorem: The angular phase repeats after one turn.** Adding 2π to the angle leaves the integer-frequency Fourier phase unchanged. Source: `Breakdown.Coercive.Internal.ModeRotation.expFactor_add_period` (`Breakdown/Cert/CoerciveModeRotation.lean:42`).

**Theorem: An angular shift produces its phase.** Shifting the periodic angular integrand multiplies its Fourier integral by the angular frequency's complex phase. Source: `Breakdown.Coercive.Internal.ModeRotation.integral_shift` (`Breakdown/Cert/CoerciveModeRotation.lean:52`).

**Theorem: Use product measure for averaging.** The time-angle iterated integral equals the integral over the product averaging measure. Source: `Breakdown.Coercive.Internal.ModeRotation.iter_eq_prod` (`Breakdown/Cert/CoerciveModeRotation.lean:72`).

**Theorem: Finite linear combinations of modes.** Finite real linear combinations pass through the complex Fourier averaging integral under the stated hypotheses. Source: `Breakdown.Coercive.Internal.ModeRotation.modeAverage_sum` (`Breakdown/Cert/CoerciveModeRotation.lean:79`).

**Theorem: Read a coordinate of a vector sum.** A coordinate of a finite vector linear combination is the same linear combination of the coordinates. Source: `Breakdown.Coercive.Internal.ModeRotation.coord_sum` (`Breakdown/Cert/CoerciveModeRotation.lean:117`).

**Theorem: A coordinate formula for rotation.** A rotated coordinate is the sum of the input coordinates times the corresponding rotated basis-vector coordinates. Source: `Breakdown.Coercive.Internal.ModeRotation.axialRot_apply` (`Breakdown/Cert/CoerciveModeRotation.lean:121`).

**Theorem: Rotate the coordinate-basis expansion.** A rotated vector is the sum of the original coordinates times the rotated basis vectors. Source: `Breakdown.Coercive.Internal.ModeRotation.axialRot_eq_sum` (`Breakdown/Cert/CoerciveModeRotation.lean:125`).

**Theorem: Read a rotated linear combination.** A coordinate of a rotated finite linear combination is the same linear combination of the rotated coordinates. Source: `Breakdown.Coercive.Internal.ModeRotation.axialRot_sum_apply` (`Breakdown/Cert/CoerciveModeRotation.lean:131`).

**Theorem: Axial rotation preserves length.** Axial rotation preserves the Euclidean norm. Source: `Breakdown.Coercive.Internal.ModeRotation.norm_axialRot` (`Breakdown/Cert/CoerciveModeRotation.lean:137`).

**Theorem: Subtracting one turn preserves rotation.** Subtracting 2π from an axial rotation angle leaves the rotated vector unchanged. Source: `Breakdown.Coercive.Internal.ModeRotation.axialRot_sub_period` (`Breakdown/Cert/CoerciveModeRotation.lean:141`).

**Theorem: A rotation cancels its inverse.** Applying an axial rotation after its inverse returns the original vector. Source: `Breakdown.Coercive.Internal.ModeRotation.axialRot_cancel` (`Breakdown/Cert/CoerciveModeRotation.lean:147`).

**Theorem: Reassociate inverse frame rotations.** The inverse rotation by φ factors as rotation by ψ followed by inverse rotation by φ+ψ. Source: `Breakdown.Coercive.Internal.ModeRotation.axialRot_neg_comp` (`Breakdown/Cert/CoerciveModeRotation.lean:151`).

**Theorem: Axial rotation is continuous.** Under the stated hypotheses, the axial rotation is continuous. Source: `Breakdown.Coercive.Internal.ModeRotation.continuous_axialRot` (`Breakdown/Cert/CoerciveModeRotation.lean:157`).

**Theorem: Time-rotation orbit map is continuous.** Under the stated hypotheses, the time-rotation orbit map is continuous. Source: `Breakdown.Coercive.Internal.ModeRotation.continuous_orbitMap` (`Breakdown/Cert/CoerciveModeRotation.lean:161`).

**Theorem: Split orbit motion into time and space.** The time-rotation orbit map is a time translation paired with a linear spatial isometry. Source: `Breakdown.Coercive.Internal.ModeRotation.orbitMap_eq` (`Breakdown/Cert/CoerciveModeRotation.lean:166`).

**Theorem: Time-rotation orbit map formula.** Under the stated hypotheses, the time-rotation orbit map preserves the stated measure. Source: `Breakdown.Coercive.Internal.ModeRotation.measurePreserving_orbitMap` (`Breakdown/Cert/CoerciveModeRotation.lean:171`).

**Theorem: The orbit map is a measurable embedding.** Each fixed time-rotation orbit map is a measurable embedding. Source: `Breakdown.Coercive.Internal.ModeRotation.measurableEmbedding_orbitMap` (`Breakdown/Cert/CoerciveModeRotation.lean:177`).

**Theorem: A bounded orbit stays in a larger ball.** Under the stated time-shift and radius bounds, the orbit point belongs to the closed space-time ball of radius N+1. Source: `Breakdown.Coercive.Internal.ModeRotation.orbitMap_mem` (`Breakdown/Cert/CoerciveModeRotation.lean:183`).

**Theorem: Almost every orbit average is integrable.** For almost every space-time point, the field restricted to its time-rotation averaging orbit is integrable. Source: `Breakdown.Coercive.Internal.ModeRotation.ae_integrable_orbit` (`Breakdown/Cert/CoerciveModeRotation.lean:197`).

**Theorem: Velocity-orbit coordinate is integrable.** Under the stated hypotheses, the velocity-orbit coordinate is integrable. Source: `Breakdown.Coercive.Internal.ModeRotation.integrable_velComponent` (`Breakdown/Cert/CoerciveModeRotation.lean:262`).

**Theorem: Gradient-orbit coordinate is integrable.** Under the stated hypotheses, the gradient-orbit coordinate is integrable. Source: `Breakdown.Coercive.Internal.ModeRotation.integrable_gradComponent` (`Breakdown/Cert/CoerciveModeRotation.lean:275`).

**Theorem: Rotate a velocity mode with its phase.** Axial rotation of the evaluation point rotates the velocity-mode vector and multiplies it by the angular Fourier phase. Source: `Breakdown.Coercive.Internal.ModeRotation.modeVel_rotation_of` (`Breakdown/Cert/CoerciveModeRotation.lean:295`).

**Theorem: Rotate a gradient mode with its phase.** Axial rotation of the evaluation point conjugates the gradient-mode matrix and multiplies it by the angular Fourier phase. Source: `Breakdown.Coercive.Internal.ModeRotation.modeGrad_rotation_of` (`Breakdown/Cert/CoerciveModeRotation.lean:352`).

**Theorem: Modes transform by their angular phase.** The supplied hypotheses establish the rotation identities for velocity and gradient modes with their angular Fourier phase. Source: `Breakdown.Coercive.modeRotationHolds_of` (`Breakdown/Cert/CoerciveModeRotation.lean:431`).

### Breakdown.Cert.CoerciveNodes

This file names the propositions required by the analytic assembly, including rotation, Parseval, weak derivatives, field existence, smooth estimates, approximation, passage, and absorption; these declarations specify obligations rather than prove them.

**Paper context:** Appendix B, Proposition B.1: the explicit interfaces connecting the analytic proof stages.

**Interface definition: A multiplier with a density bound.** This proposition specifies existence of a multiplier with the stated norm bound and signed mode-density inequality under its listed hypotheses. Source: `Breakdown.Coercive.MultiplierDensityHolds` (`Breakdown/Cert/CoerciveNodes.lean:13`).

Supplied by `Breakdown.Coercive.multiplierDensity_of_field` (`lean/Breakdown/Cert/CoerciveAssembly.lean:13`); `Breakdown.Coercive.multiplierDensityHolds_of_nodes` (`lean/Breakdown/Cert/CoerciveAssembly.lean:64`); `Breakdown.Coercive.multiplierDensityHolds_proof` (`lean/Breakdown/Cert/CoerciveMain.lean:50`).

**Interface definition: A piece multiplier with a density bound.** This proposition specifies existence of a piece multiplier with the stated norm bound and signed piece-density inequality under its listed hypotheses. Source: `Breakdown.Coercive.PieceMultiplierDensityHolds` (`Breakdown/Cert/CoerciveNodes.lean:38`).

Supplied by `Breakdown.Coercive.pieceMultiplierDensity_of_field` (`lean/Breakdown/Cert/CoerciveAssembly.lean:21`); `Breakdown.Coercive.pieceMultiplierDensityHolds_of_nodes` (`lean/Breakdown/Cert/CoerciveAssembly.lean:99`); `Breakdown.Coercive.pieceMultiplierDensityHolds_proof` (`lean/Breakdown/Cert/CoerciveMain.lean:69`); `Breakdown.CoerciveWeak.pieceMultiplierDensity_of_weakHolds` (`lean/Breakdown/Cert/ExtendedCoerciveAssembly.lean:47`).

**Interface definition: Angular frequency controls derivatives.** This proposition specifies the two inverse-radius lower bounds from angular frequencies at least two under its listed hypotheses. Source: `Breakdown.Coercive.ModeAzimuthalGainHolds` (`Breakdown/Cert/CoerciveNodes.lean:63`).

Supplied by `Breakdown.Coercive.modeAzimuthalGainHolds_of_nodes` (`lean/Breakdown/Cert/CoerciveAssembly.lean:134`); `Breakdown.Coercive.modeAzimuthalGainHolds_proof_of` (`lean/Breakdown/Cert/CoerciveGain.lean:735`); `Breakdown.Coercive.modeAzimuthalGainHolds_proof` (`lean/Breakdown/Cert/CoerciveMain.lean:89`).

**Interface definition: Bound the mean stretching term.** This proposition specifies control of the averaged negative stretching form by the summed stretching charges under its listed hypotheses. Source: `Breakdown.Coercive.StretchMeanBoundHolds` (`Breakdown/Cert/CoerciveNodes.lean:73`).

Supplied by `Breakdown.Coercive.stretchMeanBoundHolds_of_nodes` (`lean/Breakdown/Cert/CoerciveAssembly.lean:140`); `Breakdown.Coercive.stretchMeanBoundHolds_proof` (`lean/Breakdown/Cert/CoerciveMain.lean:95`); `Breakdown.Coercive.stretchMeanBoundHolds_proof_of` (`lean/Breakdown/Cert/CoerciveStretch.lean:992`).

**Definition: Real vector from complex coordinates.** Collect the real parts of a complex coordinate vector into physical space. Source: `Breakdown.Coercive.reVec` (`Breakdown/Cert/CoerciveNodes.lean:84`).

**Definition: Imaginary vector from coordinates.** Collect the imaginary parts of a complex coordinate vector into physical space. Source: `Breakdown.Coercive.imVec` (`Breakdown/Cert/CoerciveNodes.lean:86`).

**Definition: Real matrix from complex coordinates.** Collect the real parts of a complex matrix into a real linear map. Source: `Breakdown.Coercive.reMat` (`Breakdown/Cert/CoerciveNodes.lean:88`).

**Definition: Imaginary matrix from coordinates.** Collect the imaginary parts of a complex matrix into a real linear map. Source: `Breakdown.Coercive.imMat` (`Breakdown/Cert/CoerciveNodes.lean:91`).

**Definition: Axial rotation of complex vectors.** Extend the real axial rotation matrix to complex vector coordinates. Source: `Breakdown.Coercive.rotC` (`Breakdown/Cert/CoerciveNodes.lean:94`).

**Definition: Axial rotation of complex matrices.** Conjugate a complex matrix by the real axial rotation matrix. Source: `Breakdown.Coercive.rotCMat` (`Breakdown/Cert/CoerciveNodes.lean:97`).

**Definition: The smooth equation's right side.** Combine temporal and radial transport, the negative second-derivative trace, and linear convection about the profile. Source: `Breakdown.Coercive.smoothRight` (`Breakdown/Cert/CoerciveNodes.lean:101`).

**Definition: Conditions for a solenoidal part.** Require a periodic L² field orthogonal to gradients and matching the original field against every solenoidal test. Source: `Breakdown.Coercive.IsSolenoidalPartOf` (`Breakdown/Cert/CoerciveNodes.lean:105`).

**Interface definition: The axial rotation identities.** This proposition specifies linear isometry, composition, periodicity, and cylindrical-coordinate identities for axial rotation under its listed hypotheses. Source: `Breakdown.Coercive.AxialRotationHolds` (`Breakdown/Cert/CoerciveNodes.lean:114`).

Supplied by `Breakdown.Coercive.axialRotationHolds_proof` (`lean/Breakdown/Cert/CoerciveRotation.lean:94`).

**Interface definition: Parseval on the averaging rectangle.** This proposition specifies equality between the squared Fourier coefficients and the normalised L² integral on one time-angle rectangle under its listed hypotheses. Source: `Breakdown.Coercive.TorusSquareSumHolds` (`Breakdown/Cert/CoerciveNodes.lean:121`).

Supplied by `Breakdown.Coercive.torusSquareSumHolds_proof` (`lean/Breakdown/Cert/CoerciveTorus.lean:59`).

**Interface definition: Parseval for fields and derivatives.** This proposition specifies the mode-square identities for velocity and derivatives together with the corresponding pairing sum under its listed hypotheses. Source: `Breakdown.Coercive.ModeSquareSumHolds` (`Breakdown/Cert/CoerciveNodes.lean:130`).

Supplied by `Breakdown.Coercive.modeSquareSumHolds_proved` (`lean/Breakdown/Cert/CoerciveMain.lean:47`); `Breakdown.Coercive.modeSquareSumHolds_of` (`lean/Breakdown/Cert/CoerciveSquareSum.lean:737`); `Breakdown.CoerciveWeak.modeSquareSumHolds_closed` (`lean/Breakdown/Cert/ExtendedCoerciveMain.lean:37`).

**Interface definition: Mode extraction and weak derivatives.** This proposition specifies the weak-gradient identities for real and imaginary modes and the zero trace of the gradient mode under its listed hypotheses. Source: `Breakdown.Coercive.ModeDerivativeHolds` (`Breakdown/Cert/CoerciveNodes.lean:151`).

Supplied by `Breakdown.Coercive.modeDerivativeHolds_of` (`lean/Breakdown/Cert/CoerciveModeDerivative.lean:1018`); `Breakdown.CoerciveWeak.modeDerivativeHolds_closed` (`lean/Breakdown/Cert/ExtendedCoerciveMain.lean:40`).

**Interface definition: Modes transform by their angular phase.** This proposition specifies the rotation identities for velocity and gradient modes with their angular Fourier phase under its listed hypotheses. Source: `Breakdown.Coercive.ModeRotationHolds` (`Breakdown/Cert/CoerciveNodes.lean:162`).

Supplied by `Breakdown.Coercive.modeRotationHolds_of` (`lean/Breakdown/Cert/CoerciveModeRotation.lean:431`); `Breakdown.CoerciveWeak.modeRotationHolds_closed` (`lean/Breakdown/Cert/ExtendedCoerciveMain.lean:44`).

**Interface definition: Select the solenoidal part.** This proposition specifies existence and uniqueness of a solenoidal projection with its norm, reflection, and orbit-equivariance properties under its listed hypotheses. Source: `Breakdown.Coercive.SolenoidalModeHolds` (`Breakdown/Cert/CoerciveNodes.lean:169`).

Supplied by `Breakdown.Coercive.solenoidalModeHolds_of` (`lean/Breakdown/Cert/CoerciveSolenoidal.lean:495`); `Breakdown.CoerciveWeak.solenoidalModeHolds_closed` (`lean/Breakdown/Cert/ExtendedCoerciveMain.lean:48`).

**Interface definition: The compact-test energy identity.** This proposition specifies the equality between testing the smooth equation against the negative Laplacian and vorticity energy plus stretching under its listed hypotheses. Source: `Breakdown.Coercive.EnergyIdentityHolds` (`Breakdown/Cert/CoerciveNodes.lean:178`).

No theorem in the library states this proposition as its result.

**Interface definition: The weighted div-curl identity.** This proposition specifies the weighted curl-gradient identity with the Hessian-of-weight correction for compactly supported divergence-free fields under its listed hypotheses. Source: `Breakdown.Coercive.CurlWeightIdentityHolds` (`Breakdown/Cert/CoerciveNodes.lean:185`).

Supplied by `Breakdown.Coercive.curlWeightIdentityHolds_proof` (`lean/Breakdown/Cert/CoerciveCurlWeight.lean:64`).

**Definition: Evaluate a density on mode sizes.** Evaluate a five-variable density on the second-derivative, curl-gradient, gradient, curl, and velocity amplitudes. Source: `Breakdown.Coercive.modeValues` (`Breakdown/Cert/CoerciveNodes.lean:192`).

**Definition: A signed density lower bound.** Express the lower bound by separating the positive and negative parts of the density and of the scalar energy. Source: `Breakdown.Coercive.IsDensityLowerBound` (`Breakdown/Cert/CoerciveNodes.lean:200`).

**Definition: The curl part of a mode pairing.** Sum the integrated signed curl-mode pairings over all frequency pairs. Source: `Breakdown.Coercive.epsPairing` (`Breakdown/Cert/CoerciveNodes.lean:204`).

**Definition: The velocity part of a mode pairing.** Sum the integrated signed velocity-mode pairings over all frequency pairs. Source: `Breakdown.Coercive.muPairing` (`Breakdown/Cert/CoerciveNodes.lean:209`).

**Definition: The vorticity energy over one period.** Integrate the squared vorticity gradient plus one quarter of the squared vorticity over space and one time period. Source: `Breakdown.Coercive.vorticityEnergy` (`Breakdown/Cert/CoerciveNodes.lean:213`).

**Definition: Density from the curl multiplier.** Collect the curl-weight contribution to the lower density, including its derivative and interaction costs. Source: `Breakdown.Coercive.modeEpsDensity` (`Breakdown/Cert/CoerciveNodes.lean:217`).

**Definition: Density from the velocity multiplier.** Collect the velocity-weight contribution to the lower density, including its gradient and mixed costs. Source: `Breakdown.Coercive.modeMuDensity` (`Breakdown/Cert/CoerciveNodes.lean:224`).

**Definition: Density from one curl piece.** Collect the curl-piece contribution with its frame frequency, absorption shares, and incoming and outgoing mode charges. Source: `Breakdown.Coercive.pieceEpsDensity` (`Breakdown/Cert/CoerciveNodes.lean:232`).

**Definition: Density from one velocity piece.** Collect the velocity-piece contribution with its frame frequency, absorption shares, and harmonic interaction charges. Source: `Breakdown.Coercive.pieceMuDensity` (`Breakdown/Cert/CoerciveNodes.lean:258`).

**Definition: One velocity-piece seminorm.** Sum the mode energy weighted by the piece's absolute sign, absolute frame frequency, and spatial weight. Source: `Breakdown.Coercive.pieceSeminormPart` (`Breakdown/Cert/CoerciveNodes.lean:275`).

**Definition: Positive curl-frequency term.** Multiply the squared curl amplitude by the nonnegative curl weight and absolute frame frequency. Source: `Breakdown.Coercive.modeEpsPos` (`Breakdown/Cert/CoerciveNodes.lean:281`).

**Definition: Curl multiplier remainder.** Collect the relative-velocity, stretching, and neighbouring-mode errors of the curl multiplier. Source: `Breakdown.Coercive.modeEpsRest` (`Breakdown/Cert/CoerciveNodes.lean:285`).

**Definition: Positive velocity-frequency term.** Multiply the velocity mode square by its weight, absolute frame frequency, and the factor one minus the velocity-energy coefficient. Source: `Breakdown.Coercive.modeMuPos` (`Breakdown/Cert/CoerciveNodes.lean:300`).

**Definition: Velocity multiplier remainder.** Collect the relative-velocity, transport, and neighbouring-mode errors of the velocity multiplier. Source: `Breakdown.Coercive.modeMuRest` (`Breakdown/Cert/CoerciveNodes.lean:304`).

**Definition: Positive curl and velocity terms.** Add the positive curl-frequency and velocity-frequency contributions. Source: `Breakdown.Coercive.modePos` (`Breakdown/Cert/CoerciveNodes.lean:315`).

**Definition: The full mode remainder.** Add the base density to the curl and velocity multiplier remainders. Source: `Breakdown.Coercive.modeRest` (`Breakdown/Cert/CoerciveNodes.lean:319`).

**Interface definition: The compact-test base-density bound.** This proposition specifies the signed lower bound of vorticity energy minus weighted energy by the base mode density for compact tests under its listed hypotheses. Source: `Breakdown.Coercive.BaseDensityHolds` (`Breakdown/Cert/CoerciveNodes.lean:325`).

No theorem in the library states this proposition as its result.

**Interface definition: Split the compact-test pairing.** This proposition specifies the decomposition into the second-derivative, curl-mode, and velocity-mode pairings for compact tests under its listed hypotheses. Source: `Breakdown.Coercive.ModePairingSplitHolds` (`Breakdown/Cert/CoerciveNodes.lean:336`).

Supplied by `Breakdown.Coercive.modePairingSplitHolds_of` (`lean/Breakdown/Cert/CoercivePairingSplit.lean:901`).

**Interface definition: The compact-test curl bound.** This proposition specifies the split lower bound for the curl-weight pairing of a compact test field under its listed hypotheses. Source: `Breakdown.Coercive.ModeEpsEstimateHolds` (`Breakdown/Cert/CoerciveNodes.lean:351`).

No theorem in the library states this proposition as its result.

**Interface definition: The compact-test velocity bound.** This proposition specifies the split lower bound for the velocity pairing after subtracting its frequency seminorm under its listed hypotheses. Source: `Breakdown.Coercive.ModeMuEstimateHolds` (`Breakdown/Cert/CoerciveNodes.lean:364`).

No theorem in the library states this proposition as its result.

**Interface definition: Split a compact-test piece pairing.** This proposition specifies the decomposition into the second-derivative pairing and sums of individual curl-piece and velocity-piece pairings under its listed hypotheses. Source: `Breakdown.Coercive.PiecePairingSplitHolds` (`Breakdown/Cert/CoerciveNodes.lean:378`).

No theorem in the library states this proposition as its result.

**Interface definition: The compact-test curl-piece bound.** This proposition specifies the split lower bound for each curl piece, including its mode remainder and block term under its listed hypotheses. Source: `Breakdown.Coercive.PieceEpsEstimateHolds` (`Breakdown/Cert/CoerciveNodes.lean:394`).

No theorem in the library states this proposition as its result.

**Interface definition: The compact-test velocity-piece bound.** This proposition specifies the split lower bound for each velocity piece after subtracting its piece seminorm under its listed hypotheses. Source: `Breakdown.Coercive.PieceMuEstimateHolds` (`Breakdown/Cert/CoerciveNodes.lean:409`).

No theorem in the library states this proposition as its result.

**Interface definition: Existence of the mode multiplier.** This proposition specifies finiteness of the frequency seminorm and existence of a variational multiplier with its norm bound under its listed hypotheses. Source: `Breakdown.Coercive.ModeFieldExistsHolds` (`Breakdown/Cert/CoerciveNodes.lean:425`).

Supplied by `Breakdown.Coercive.modeFieldExistsHolds_of` (`lean/Breakdown/Cert/CoerciveField.lean:1557`).

**Interface definition: The compact-test mode-density bound.** This proposition specifies the split lower bound for the multiplier gap of a compact test field under its listed hypotheses. Source: `Breakdown.Coercive.SmoothModeDensityHolds` (`Breakdown/Cert/CoerciveNodes.lean:434`).

No theorem in the library states this proposition as its result.

**Interface definition: The weak mode-density bound.** This proposition specifies the split lower bound for the multiplier gap of a weak perturbation with its given multiplier under its listed hypotheses. Source: `Breakdown.Coercive.ModeDensityOfFieldHolds` (`Breakdown/Cert/CoerciveNodes.lean:452`).

Supplied by `Breakdown.Coercive.modeDensityOfField_of_passage` (`lean/Breakdown/Cert/CoerciveAssembly.lean:48`).

**Interface definition: Existence of the piece multiplier.** This proposition specifies finiteness of the piece seminorm and existence of a variational piece multiplier with its norm bound under its listed hypotheses. Source: `Breakdown.Coercive.PieceFieldExistsHolds` (`Breakdown/Cert/CoerciveNodes.lean:473`).

Supplied by `Breakdown.Coercive.pieceFieldExistsHolds_of` (`lean/Breakdown/Cert/CoercivePieceField.lean:1365`).

**Interface definition: The compact-test piece-density bound.** This proposition specifies the split lower bound for the piece-multiplier gap of a compact test field under its listed hypotheses. Source: `Breakdown.Coercive.SmoothPieceDensityHolds` (`Breakdown/Cert/CoerciveNodes.lean:482`).

No theorem in the library states this proposition as its result.

**Interface definition: The weak piece-density bound.** This proposition specifies the split lower bound for the piece-multiplier gap of a weak perturbation with its given multiplier under its listed hypotheses. Source: `Breakdown.Coercive.PieceDensityOfFieldHolds` (`Breakdown/Cert/CoerciveNodes.lean:500`).

Supplied by `Breakdown.Coercive.pieceDensityOfField_of_passage` (`lean/Breakdown/Cert/CoerciveAssembly.lean:56`).

**Interface definition: Absorb the mode interaction costs.** This proposition specifies conversion of a split remainder bound into the signed total mode-density inequality under its listed hypotheses. Source: `Breakdown.Coercive.ModeAbsorbStepHolds` (`Breakdown/Cert/CoerciveNodes.lean:521`).

Supplied by `Breakdown.Coercive.modeAbsorbStepHolds_of` (`lean/Breakdown/Cert/CoerciveAbsorb.lean:1036`).

**Interface definition: Absorb the piece interaction costs.** This proposition specifies conversion of a split piece-remainder bound into the signed total piece-density inequality under its listed hypotheses. Source: `Breakdown.Coercive.PieceAbsorbStepHolds` (`Breakdown/Cert/CoerciveNodes.lean:535`).

Supplied by `Breakdown.Coercive.pieceAbsorbStepHolds_of` (`lean/Breakdown/Cert/CoercivePieceAbsorb.lean:252`).

**Interface definition: Smooth fields meet weak specifications.** This proposition specifies membership of a smooth perturbation in the weak perturbation class using its ordinary derivatives under its listed hypotheses. Source: `Breakdown.Coercive.SmoothPerturbationIsPerturbationHolds` (`Breakdown/Cert/CoerciveNodes.lean:549`).

Supplied by `Breakdown.Coercive.smoothPerturbationIsPerturbationHolds_proof` (`lean/Breakdown/Cert/CoerciveSmoothIsPerturbation.lean:306`).

**Interface definition: The smooth energy identity.** This proposition specifies the vorticity-energy and stretching identity for the smooth perturbation class under its listed hypotheses. Source: `Breakdown.Coercive.EnergyIdentitySmoothHolds` (`Breakdown/Cert/CoerciveNodes.lean:553`).

Supplied by `Breakdown.Coercive.energyIdentitySmoothHolds_proof` (`lean/Breakdown/Cert/CoerciveSmoothEnergyIdentity.lean:50`).

**Interface definition: Div-curl identity for decaying fields.** This proposition specifies the weighted curl-gradient identity for fields with the stated finite energy and decay assumptions under its listed hypotheses. Source: `Breakdown.Coercive.CurlWeightIdentityDecayHolds` (`Breakdown/Cert/CoerciveNodes.lean:562`).

Supplied by `Breakdown.Coercive.curlWeightIdentityDecayHolds_proof` (`lean/Breakdown/Cert/CoerciveSmoothCurlWeight.lean:310`).

**Interface definition: Weighted Laplacian integration by parts.** This proposition specifies the antisymmetric weighted Laplacian pairing identity with a Lipschitz weight under its listed hypotheses. Source: `Breakdown.Coercive.WeightedSumSecondPartialsPairingHolds` (`Breakdown/Cert/CoerciveNodes.lean:572`).

Supplied by `Breakdown.Coercive.weightedSumSecondPartialsPairingHolds_proof` (`lean/Breakdown/Cert/CoerciveSmoothSumSecondPartialsPairing.lean:238`).

**Interface definition: The smooth base-density bound.** This proposition specifies the signed base-density lower bound for the smooth perturbation class under its listed hypotheses. Source: `Breakdown.Coercive.BaseDensitySmoothHolds` (`Breakdown/Cert/CoerciveNodes.lean:583`).

Supplied by `Breakdown.Coercive.baseDensitySmoothHolds_of` (`lean/Breakdown/Cert/CoerciveSmoothBase.lean:1589`).

**Interface definition: Split the smooth mode pairing.** This proposition specifies the second-derivative, curl, and velocity decomposition of the smooth multiplier pairing under its listed hypotheses. Source: `Breakdown.Coercive.ModePairingSplitSmoothHolds` (`Breakdown/Cert/CoerciveNodes.lean:594`).

Supplied by `Breakdown.Coercive.modePairingSplitSmoothHolds_of` (`lean/Breakdown/Cert/CoerciveSmoothPairingSplit.lean:172`).

**Interface definition: The smooth curl-mode bound.** This proposition specifies the split lower bound for the curl-weight pairing of a smooth perturbation under its listed hypotheses. Source: `Breakdown.Coercive.ModeEpsEstimateSmoothHolds` (`Breakdown/Cert/CoerciveNodes.lean:609`).

Supplied by `Breakdown.Coercive.modeEpsEstimateSmoothHolds_of` (`lean/Breakdown/Cert/CoerciveSmoothEps.lean:105`).

**Interface definition: The smooth velocity-mode bound.** This proposition specifies the split lower bound for the velocity-weight pairing of a smooth perturbation after its seminorm is removed under its listed hypotheses. Source: `Breakdown.Coercive.ModeMuEstimateSmoothHolds` (`Breakdown/Cert/CoerciveNodes.lean:622`).

Supplied by `Breakdown.Coercive.modeMuEstimateSmoothHolds_of` (`lean/Breakdown/Cert/CoerciveSmoothMu.lean:94`).

**Interface definition: Split the smooth piece pairing.** This proposition specifies the decomposition of the smooth piece-multiplier pairing into the second-derivative and individual piece contributions under its listed hypotheses. Source: `Breakdown.Coercive.PiecePairingSplitSmoothHolds` (`Breakdown/Cert/CoerciveNodes.lean:636`).

Supplied by `Breakdown.Coercive.piecePairingSplitSmoothHolds_of` (`lean/Breakdown/Cert/CoerciveSmoothPiecePairingSplit.lean:268`).

**Interface definition: The smooth curl-piece bound.** This proposition specifies the split lower bound for every smooth curl piece including its block contribution under its listed hypotheses. Source: `Breakdown.Coercive.PieceEpsEstimateSmoothHolds` (`Breakdown/Cert/CoerciveNodes.lean:652`).

Supplied by `Breakdown.Coercive.pieceEpsEstimateSmoothHolds_of` (`lean/Breakdown/Cert/CoerciveSmoothPieceEps.lean:341`); `Breakdown.CoerciveWeak.pieceEpsEstimateSmooth_of_weak` (`lean/Breakdown/Cert/ExtendedCoerciveAssembly.lean:56`).

**Interface definition: The smooth velocity-piece bound.** This proposition specifies the split lower bound for every smooth velocity piece including its block contribution and seminorm subtraction under its listed hypotheses. Source: `Breakdown.Coercive.PieceMuEstimateSmoothHolds` (`Breakdown/Cert/CoerciveNodes.lean:667`).

Supplied by `Breakdown.Coercive.pieceMuEstimateSmoothHolds_of` (`lean/Breakdown/Cert/CoerciveSmoothPieceMu.lean:176`); `Breakdown.CoerciveWeak.pieceMuEstimateSmooth_of_weak` (`lean/Breakdown/Cert/ExtendedCoerciveAssembly.lean:65`).

**Interface definition: The smooth mode-density bound.** This proposition specifies the split lower bound for the multiplier gap of a smooth perturbation under its listed hypotheses. Source: `Breakdown.Coercive.ModeDensitySmoothHolds` (`Breakdown/Cert/CoerciveNodes.lean:683`).

Supplied by `Breakdown.Coercive.modeDensitySmoothHolds_of` (`lean/Breakdown/Cert/CoerciveSmoothDensity.lean:317`).

**Interface definition: The smooth piece-density bound.** This proposition specifies the split lower bound for the piece-multiplier gap of a smooth perturbation under its listed hypotheses. Source: `Breakdown.Coercive.PieceDensitySmoothHolds` (`Breakdown/Cert/CoerciveNodes.lean:701`).

Supplied by `Breakdown.Coercive.pieceDensitySmoothHolds_of` (`lean/Breakdown/Cert/CoerciveSmoothPieceDensity.lean:386`).

**Interface definition: Pass mode density to weak fields.** This proposition specifies transfer of the split mode-density inequality along a smooth approximation to the weak perturbation under its listed hypotheses. Source: `Breakdown.Coercive.ModeDensityPassageHolds` (`Breakdown/Cert/CoerciveNodes.lean:719`).

Supplied by `Breakdown.Coercive.modeDensityPassageHolds_of` (`lean/Breakdown/Cert/CoerciveDensityPassage.lean:374`).

**Interface definition: Pass piece density to weak fields.** This proposition specifies transfer of the split piece-density inequality along a smooth approximation to the weak perturbation under its listed hypotheses. Source: `Breakdown.Coercive.PieceDensityPassageHolds` (`Breakdown/Cert/CoerciveNodes.lean:741`).

Supplied by `Breakdown.Coercive.pieceDensityPassageHolds_of` (`lean/Breakdown/Cert/CoercivePieceDensityPassage.lean:322`); `Breakdown.CoerciveWeak.pieceDensityPassage_of_weak` (`lean/Breakdown/Cert/ExtendedCoerciveAssembly.lean:72`).

### Breakdown.Cert.CoercivePairingSplit

Periodic L² testing and solenoidal projection split the multiplier pairing into its negative-Laplacian, weighted curl-mode, and weighted velocity-mode contributions.

**Paper context:** Appendix B, Proposition B.1: decomposition of the ordinary multiplier pairing.

**Definition: Volume over one time period.** Use the product of volume on the closed unit time interval and spatial volume. Source: `Breakdown.Coercive.PairingSplitInternal.periodMeasure` (`Breakdown/Cert/CoercivePairingSplit.lean:17`).

**Theorem: The period measure is a slab restriction.** The period product measure is space-time volume restricted to the unit time slab. Source: `Breakdown.Coercive.PairingSplitInternal.periodMeasure_eq` (`Breakdown/Cert/CoercivePairingSplit.lean:19`).

**Theorem: Strong measurability on the period slab.** Under the stated hypotheses, the field restricted to the period slab is strongly measurable up to a null set. Source: `Breakdown.Coercive.PairingSplitInternal.aesm_period` (`Breakdown/Cert/CoercivePairingSplit.lean:23`).

**Theorem: Use product measure for period energy.** The iterated nonnegative squared-norm integral equals the squared-norm integral over the period product measure. Source: `Breakdown.Coercive.PairingSplitInternal.lintegral_period` (`Breakdown/Cert/CoercivePairingSplit.lean:28`).

**Theorem: Integrability of the period norm square.** Under the stated hypotheses, the squared field norm on the period slab is integrable. Source: `Breakdown.Coercive.PairingSplitInternal.sq_integrable` (`Breakdown/Cert/CoercivePairingSplit.lean:35`).

**Theorem: Integrable period inner products.** Under the stated hypotheses, the pointwise field pairing on the period slab is integrable. Source: `Breakdown.Coercive.PairingSplitInternal.inner_integrable` (`Breakdown/Cert/CoercivePairingSplit.lean:44`).

**Theorem: Read the period pairing on the slab.** The period pairing equals the integral of the pointwise inner product over the period-slab measure. Source: `Breakdown.Coercive.PairingSplitInternal.pairing_eq` (`Breakdown/Cert/CoercivePairingSplit.lean:55`).

**Theorem: Read the squared period norm.** The squared period norm equals the integral of the pointwise norm square over the period slab. Source: `Breakdown.Coercive.PairingSplitInternal.normSq_eq` (`Breakdown/Cert/CoercivePairingSplit.lean:60`).

**Theorem: Linear combinations in periodic L².** A real linear combination of two periodic L² fields is again a periodic L² field. Source: `Breakdown.Coercive.PairingSplitInternal.square_lin` (`Breakdown/Cert/CoercivePairingSplit.lean:68`).

**Theorem: Periodic L² fields are closed under sums.** The sum of two periodic L² fields is again a periodic L² field. Source: `Breakdown.Coercive.PairingSplitInternal.square_add` (`Breakdown/Cert/CoercivePairingSplit.lean:97`).

**Theorem: Add in the first period-pairing slot.** The period pairing distributes over addition of its first field. Source: `Breakdown.Coercive.PairingSplitInternal.pairing_add_left` (`Breakdown/Cert/CoercivePairingSplit.lean:102`).

**Theorem: Linearity of the period pairing.** The period pairing of a real linear combination equals the same combination of the period pairings. Source: `Breakdown.Coercive.PairingSplitInternal.pairing_lin_left` (`Breakdown/Cert/CoercivePairingSplit.lean:111`).

**Theorem: Expand the squared period norm of a sum.** The squared period norm of X + Y equals the two squared norms plus twice the period pairing of X and Y. Source: `Breakdown.Coercive.PairingSplitInternal.normSq_add` (`Breakdown/Cert/CoercivePairingSplit.lean:121`).

**Theorem: Period norms ignore null-set changes.** Almost-everywhere equal fields have the same period norm. Source: `Breakdown.Coercive.PairingSplitInternal.periodNorm_congr` (`Breakdown/Cert/CoercivePairingSplit.lean:134`).

**Theorem: The solenoidal part lies in periodic L².** A field satisfying the solenoidal-part conditions satisfies the periodic L² field conditions. Source: `Breakdown.Coercive.PairingSplitInternal.square_of_solenoidal` (`Breakdown/Cert/CoercivePairingSplit.lean:149`).

**Theorem: Compact continuous fields lie in L².** The stated continuous periodic field with uniform compact spatial support is a periodic L² field. Source: `Breakdown.Coercive.PairingSplitInternal.square_of_continuous` (`Breakdown/Cert/CoercivePairingSplit.lean:152`).

**Theorem: Separate a sum inside the test pairing.** The pairing with the sum of the two source fields equals the sum of their pairings under the stated integrability assumptions. Source: `Breakdown.Coercive.PairingSplitInternal.pairing_test_integrable_split` (`Breakdown/Cert/CoercivePairingSplit.lean:175`).

**Theorem: The spatial derivative has Cⁿ regularity.** The spatial derivative field has n continuous derivatives as a joint space-time function under the stated extra regularity hypothesis. Source: `Breakdown.Coercive.PairingSplitInternal.contDiff_slice` (`Breakdown/Cert/CoercivePairingSplit.lean:182`).

**Theorem: Derivatives vanish beyond the support.** A derivative vanishes outside the radius beyond which its original smooth field is zero. Source: `Breakdown.Coercive.PairingSplitInternal.fderiv_eq_zero_far` (`Breakdown/Cert/CoercivePairingSplit.lean:188`).

**Theorem: A test-potential gradient lies in L².** The gradient of a periodic test potential satisfies the periodic L² conditions. Source: `Breakdown.Coercive.PairingSplitInternal.gradient_square` (`Breakdown/Cert/CoercivePairingSplit.lean:195`).

**Theorem: Test fields have finite L² energy.** Every periodic test field satisfies the periodic L² conditions. Source: `Breakdown.Coercive.PairingSplitInternal.testField_square` (`Breakdown/Cert/CoercivePairingSplit.lean:211`).

**Theorem: Add two solenoidal projections.** The sum of the two solenoidal parts is a solenoidal part of the sum of the original fields. Source: `Breakdown.Coercive.PairingSplitInternal.solenoidal_add` (`Breakdown/Cert/CoercivePairingSplit.lean:214`).

**Theorem: Only the solenoidal part contributes.** Replacing a source by its solenoidal part leaves its pairing with the stated solenoidal multiplier unchanged. Source: `Breakdown.Coercive.PairingSplitInternal.pairing_eq_solenoidal` (`Breakdown/Cert/CoercivePairingSplit.lean:227`).

**Theorem: A multiplier is its own solenoidal part.** The variational multiplier satisfies the solenoidal-part specification for itself. Source: `Breakdown.Coercive.PairingSplitInternal.solenoidal_self_of_multiplier` (`Breakdown/Cert/CoercivePairingSplit.lean:259`).

**Theorem: Smooth equation source is C¹.** Under the stated hypotheses, the smooth equation source is continuously differentiable. Source: `Breakdown.Coercive.PairingSplitInternal.smoothRight_contDiff` (`Breakdown/Cert/CoercivePairingSplit.lean:264`).

**Theorem: Smooth equation source formula.** Under the stated hypotheses, the smooth equation source has time period one. Source: `Breakdown.Coercive.PairingSplitInternal.smoothRight_periodic` (`Breakdown/Cert/CoercivePairingSplit.lean:297`).

**Theorem: Bounded support of the smooth source.** The smooth equation source vanishes outside one spatial radius for all times. Source: `Breakdown.Coercive.PairingSplitInternal.smoothRight_far` (`Breakdown/Cert/CoercivePairingSplit.lean:311`).

**Theorem: The smooth source lies in periodic L².** The smooth equation source satisfies the periodic L² field conditions. Source: `Breakdown.Coercive.PairingSplitInternal.smoothRight_square` (`Breakdown/Cert/CoercivePairingSplit.lean:328`).

**Theorem: The period pairing is symmetric.** Interchanging the two real vector fields leaves the period pairing unchanged. Source: `Breakdown.Coercive.PairingSplitInternal.pairing_comm` (`Breakdown/Cert/CoercivePairingSplit.lean:334`).

**Theorem: Test-field pairings pass to the limit.** The pairings of the fixed L² field with the approximating test fields converge to its pairing with the limiting field. Source: `Breakdown.Coercive.PairingSplitInternal.pairing_tendsto` (`Breakdown/Cert/CoercivePairingSplit.lean:341`).

**Definition: The mode part of the pairing.** Sum the integrated signed curl and velocity pairings over the frequency lattice. Source: `Breakdown.Coercive.PairingSplitInternal.modeSum` (`Breakdown/Cert/CoercivePairingSplit.lean:374`).

**Theorem: Differentiate a fixed evaluation.** Differentiation of a linear-map-valued function evaluated at a fixed vector equals evaluation of its derivative at that vector. Source: `Breakdown.Coercive.PairingSplitInternal.fderiv_apply_const` (`Breakdown/Cert/CoercivePairingSplit.lean:380`).

**Theorem: A projection reads a coordinate.** The continuous coordinate projection applied to a vector returns its selected coordinate. Source: `Breakdown.Coercive.PairingSplitInternal.proj_apply` (`Breakdown/Cert/CoercivePairingSplit.lean:386`).

**Theorem: Differentiate a vector coordinate.** The derivative of a vector coordinate is the corresponding coordinate of the vector derivative. Source: `Breakdown.Coercive.PairingSplitInternal.fderiv_component` (`Breakdown/Cert/CoercivePairingSplit.lean:388`).

**Theorem: Coordinates retain differentiability.** Each coordinate of the stated differentiable field is differentiable at the point. Source: `Breakdown.Coercive.PairingSplitInternal.differentiableAt_component` (`Breakdown/Cert/CoercivePairingSplit.lean:395`).

**Theorem: Differentiate a zero trace.** The derivative of a trace-free matrix field is trace-free in the given direction. Source: `Breakdown.Coercive.PairingSplitInternal.trace_deriv_zero` (`Breakdown/Cert/CoercivePairingSplit.lean:399`).

**Theorem: The negative Laplacian is a test field.** The negative second-derivative trace of the stated periodic test field remains a periodic solenoidal test field. Source: `Breakdown.Coercive.PairingSplitInternal.sumSecondPartials_testField` (`Breakdown/Cert/CoercivePairingSplit.lean:417`).

**Definition: Integrated curl term at one mode.** Integrate the signed curl-mode pairing over space and one time period. Source: `Breakdown.Coercive.PairingSplitInternal.epsTerm` (`Breakdown/Cert/CoercivePairingSplit.lean:492`).

**Definition: Integrated velocity term at one mode.** Integrate the signed velocity-mode pairing over space and one time period. Source: `Breakdown.Coercive.PairingSplitInternal.muTerm` (`Breakdown/Cert/CoercivePairingSplit.lean:497`).

**Theorem: Curl respects a rotated frame.** The curl contraction of the conjugated gradient equals the rotated curl coordinate. Source: `Breakdown.Coercive.PairingSplitInternal.curlVec_conj` (`Breakdown/Cert/CoercivePairingSplit.lean:501`).

**Theorem: Finite linear combinations of modes.** Finite real linear combinations pass through the complex Fourier averaging integral under the stated hypotheses. Source: `Breakdown.Coercive.PairingSplitInternal.modeAverage_sum` (`Breakdown/Cert/CoercivePairingSplit.lean:510`).

**Theorem: Axial rotation is continuous.** Under the stated hypotheses, the axial rotation is continuous. Source: `Breakdown.Coercive.PairingSplitInternal.continuous_axialRot` (`Breakdown/Cert/CoercivePairingSplit.lean:554`).

**Theorem: Extracting a mode commutes with curl.** The curl of a gradient mode equals the velocity mode of the physical curl. Source: `Breakdown.Coercive.PairingSplitInternal.curlOfGrad_modeGrad` (`Breakdown/Cert/CoercivePairingSplit.lean:569`).

**Theorem: The curl field lies in periodic L².** The curl of the stated smooth periodic compactly supported field satisfies the periodic L² field conditions. Source: `Breakdown.Coercive.PairingSplitInternal.curl_square` (`Breakdown/Cert/CoercivePairingSplit.lean:605`).

**Theorem: Continuity of the summed curl pairing.** The curl-mode pairing series and its differences are summable, with the summed difference controlled by the stated norm of the changed test field. Source: `Breakdown.Coercive.PairingSplitInternal.epsTerm_bound` (`Breakdown/Cert/CoercivePairingSplit.lean:623`).

**Theorem: Continuity of the velocity pairing sum.** The velocity-mode pairing series and its differences are summable, with the summed difference controlled by the period L² distance of the test fields. Source: `Breakdown.Coercive.PairingSplitInternal.muTerm_bound` (`Breakdown/Cert/CoercivePairingSplit.lean:654`).

**Theorem: Axial rotation preserves length.** Axial rotation preserves the Euclidean norm. Source: `Breakdown.Coercive.PairingSplitInternal.norm_axialRot` (`Breakdown/Cert/CoercivePairingSplit.lean:670`).

**Theorem: Function g is integrable.** Under the stated hypotheses, the function g is integrable. Source: `Breakdown.Coercive.PairingSplitInternal.integrable_of_continuous_far` (`Breakdown/Cert/CoercivePairingSplit.lean:677`).

**Theorem: Curl vector is continuous.** Under the stated hypotheses, the curl vector is continuous. Source: `Breakdown.Coercive.PairingSplitInternal.continuous_curl` (`Breakdown/Cert/CoercivePairingSplit.lean:696`).

**Theorem: Velocity mode is continuous.** Under the stated hypotheses, the velocity mode is continuous. Source: `Breakdown.Coercive.PairingSplitInternal.continuous_apply_modeVel` (`Breakdown/Cert/CoercivePairingSplit.lean:706`).

**Theorem: Both mode pairings are integrable.** The weighted curl-mode and velocity-mode pairing integrands are integrable over the unit time slab under the stated field and weight hypotheses. Source: `Breakdown.Coercive.PairingSplitInternal.modeIntegrands_integrable` (`Breakdown/Cert/CoercivePairingSplit.lean:734`).

**Theorem: Compare two weighted mode energies.** Each of the two weighted mode energies is bounded by the other and their difference energy with the stated adjustable factors. Source: `Breakdown.Coercive.PairingSplitInternal.modeSum_split` (`Breakdown/Cert/CoercivePairingSplit.lean:790`).

**Theorem: Vanishing energies have vanishing roots.** The real square roots of the nonnegative extended-real energies tend to zero when those energies tend to zero. Source: `Breakdown.Coercive.PairingSplitInternal.sqrt_toReal_tendsto` (`Breakdown/Cert/CoercivePairingSplit.lean:807`).

**Theorem: A series error bound gives convergence.** The stated bound on the total series discrepancy implies convergence of the real series sums to the limiting series sum. Source: `Breakdown.Coercive.PairingSplitInternal.tsum_tendsto_of_bound` (`Breakdown/Cert/CoercivePairingSplit.lean:813`).

**Theorem: The mode sum tends to its split pairing.** The approximating mode-pairing sums converge to the sum of the limiting weighted curl pairing and weighted velocity pairing. Source: `Breakdown.Coercive.PairingSplitInternal.modeSum_tendsto` (`Breakdown/Cert/CoercivePairingSplit.lean:824`).

**Theorem: Split the multiplier pairing.** The solenoidal-source pairing with the multiplier equals the negative-Laplacian pairing plus the weighted curl-mode and velocity-mode pairings. Source: `Breakdown.Coercive.PairingSplitInternal.solenoidal_multiplier_pairing` (`Breakdown/Cert/CoercivePairingSplit.lean:857`).

**Theorem: Split the tested multiplier pairing.** The supplied hypotheses establish the decomposition into the second-derivative, curl-mode, and velocity-mode pairings for compact tests. Source: `Breakdown.Coercive.modePairingSplitHolds_of` (`Breakdown/Cert/CoercivePairingSplit.lean:901`).

### Breakdown.Cert.CoercivePassageCommon

This file collects weak difference fields, period Cauchy-Schwarz, stretching discrepancy estimates, and common almost-everywhere subsequences used by both density passages.

**Paper context:** Appendix B, Proposition B.1: shared estimates for passage from smooth to weak fields.

**Theorem: Subtract two weak-gradient identities.** The difference of two weak gradients is the weak gradient of the difference field. Source: `Breakdown.Coercive.Internal.PassageCommon.isWeakGradient_sub` (`Breakdown/Cert/CoercivePassageCommon.lean:14`).

**Theorem: Bound a sixth-power discrepancy.** The sixth power of the norm of x − y is at most 64 times the sum of their sixth-power norms. Source: `Breakdown.Coercive.Internal.PassageCommon.norm_sub_pow_six_le` (`Breakdown/Cert/CoercivePassageCommon.lean:40`).

**Theorem: A squared difference bound.** The squared norm of a difference is at most twice the sum of the two squared norms. Source: `Breakdown.Coercive.Internal.PassageCommon.norm_sub_sq_le` (`Breakdown/Cert/CoercivePassageCommon.lean:54`).

**Theorem: Differences retain period L² energy.** The difference of the two fields with finite period squared energies also has finite period squared energy. Source: `Breakdown.Coercive.Internal.PassageCommon.periodL2_sub` (`Breakdown/Cert/CoercivePassageCommon.lean:60`).

**Theorem: Squared matrix norm is continuous.** Under the stated hypotheses, the squared matrix norm is continuous. Source: `Breakdown.Coercive.Internal.PassageCommon.continuous_matSq` (`Breakdown/Cert/CoercivePassageCommon.lean:72`).

**Theorem: Bound a matrix discrepancy square.** The squared matrix discrepancy is at most twice the sum of the two matrix squares. Source: `Breakdown.Coercive.Internal.PassageCommon.matSq_sub_le` (`Breakdown/Cert/CoercivePassageCommon.lean:76`).

**Theorem: Squared matrix norm is nonnegative.** The squared matrix norm is nonnegative for the stated data. Source: `Breakdown.Coercive.Internal.PassageCommon.matSq_nonneg` (`Breakdown/Cert/CoercivePassageCommon.lean:82`).

**Theorem: The Hessian trace respects subtraction.** Under the stated hypotheses, the second-derivative trace commutes with subtraction. Source: `Breakdown.Coercive.Internal.PassageCommon.secondDerivTrace_sub` (`Breakdown/Cert/CoercivePassageCommon.lean:85`).

**Theorem: Read the joint time derivative.** The time derivative of a differentiable space-time field equals its joint derivative applied to the pure time direction. Source: `Breakdown.Coercive.Internal.PassageCommon.deriv_time_eq` (`Breakdown/Cert/CoercivePassageCommon.lean:91`).

**Theorem: Read the joint spatial derivative.** The spatial derivative of a differentiable space-time field equals its joint derivative applied to the corresponding pure spatial direction. Source: `Breakdown.Coercive.Internal.PassageCommon.fderiv_space_eq` (`Breakdown/Cert/CoercivePassageCommon.lean:101`).

**Definition: The adjoint test transport.** Combine the negative scaled time derivative, field, and half radial derivative of a test field. Source: `Breakdown.Coercive.Internal.PassageCommon.transportVector` (`Breakdown/Cert/CoercivePassageCommon.lean:113`).

**Theorem: Write transport with joint derivatives.** The test-field transport expression equals its scaled negative time derivative, negative field value, and negative half radial derivative in joint space-time notation. Source: `Breakdown.Coercive.Internal.PassageCommon.transportVector_eq` (`Breakdown/Cert/CoercivePassageCommon.lean:116`).

**Theorem: Adjoint test transport is continuous.** Under the stated hypotheses, the adjoint test transport is continuous. Source: `Breakdown.Coercive.Internal.PassageCommon.continuous_transportVector` (`Breakdown/Cert/CoercivePassageCommon.lean:123`).

**Theorem: Compact support: adjoint test transport.** Under the stated hypotheses, the adjoint test transport has compact support. Source: `Breakdown.Coercive.Internal.PassageCommon.hasCompactSupport_transportVector` (`Breakdown/Cert/CoercivePassageCommon.lean:132`).

**Theorem: Integrability of tested weak transport.** Under the stated hypotheses, the velocity paired with the test transport is integrable. Source: `Breakdown.Coercive.Internal.PassageCommon.integrable_velocity_transport` (`Breakdown/Cert/CoercivePassageCommon.lean:144`).

**Theorem: Field pairing is integrable.** Under the stated hypotheses, the field pairing is integrable. Source: `Breakdown.Coercive.Internal.PassageCommon.integrable_derivative_test` (`Breakdown/Cert/CoercivePassageCommon.lean:158`).

**Theorem: Subtract two weak perturbations.** The differences of the velocity, gradient, second derivative, and transport fields satisfy the weak perturbation conditions without a symmetry restriction. Source: `Breakdown.Coercive.Internal.PassageCommon.isPerturbation_sub` (`Breakdown/Cert/CoercivePassageCommon.lean:166`).

**Theorem: Approximation errors are perturbations.** The difference between a smooth approximating field and the weak field satisfies the perturbation conditions with the corresponding derivative and transport differences and no symmetry constraints. Source: `Breakdown.Coercive.Internal.PassageCommon.difference_isPerturbation` (`Breakdown/Cert/CoercivePassageCommon.lean:244`).

**Theorem: Cauchy-Schwarz over one period.** The period integral of a product of nonnegative quantities is bounded by the product of their period square-integral square roots. Source: `Breakdown.Coercive.Internal.PassageCommon.periodLIntegral_mul_le` (`Breakdown/Cert/CoercivePassageCommon.lean:253`).

**Theorem: The product error has vanishing integral.** The stated square-integral controls imply that the period integral of the nonnegative error product tends to zero. Source: `Breakdown.Coercive.Internal.PassageCommon.periodLIntegral_mul_tendsto_zero` (`Breakdown/Cert/CoercivePassageCommon.lean:283`).

**Theorem: Bound the alternating symbol.** Every alternating-symbol value has absolute value at most one. Source: `Breakdown.Coercive.Internal.PassageCommon.abs_alternatingSymbol_le` (`Breakdown/Cert/CoercivePassageCommon.lean:304`).

**Theorem: Bound a sum of three coordinates.** If each of three real summands has absolute value at most M, their sum has absolute value at most 3M. Source: `Breakdown.Coercive.Internal.PassageCommon.abs_sum_three_le` (`Breakdown/Cert/CoercivePassageCommon.lean:307`).

**Theorem: A coordinate is bounded by the norm.** The absolute value of any Euclidean coordinate is at most the vector norm. Source: `Breakdown.Coercive.Internal.PassageCommon.abs_coord_le` (`Breakdown/Cert/CoercivePassageCommon.lean:312`).

**Theorem: Bound a derivative coordinate.** A coordinate of a linear map evaluated on a coordinate basis vector has absolute value at most its operator norm. Source: `Breakdown.Coercive.Internal.PassageCommon.abs_apply_unit_le` (`Breakdown/Cert/CoercivePassageCommon.lean:316`).

**Theorem: Bound a second-derivative coordinate.** A coordinate of a bilinear map evaluated on two coordinate basis vectors has absolute value at most its operator norm. Source: `Breakdown.Coercive.Internal.PassageCommon.abs_apply₂_unit_le` (`Breakdown/Cert/CoercivePassageCommon.lean:321`).

**Theorem: Bound a curl coordinate.** Each curl coordinate has absolute value at most nine times the gradient operator norm. Source: `Breakdown.Coercive.Internal.PassageCommon.abs_curlVec_le` (`Breakdown/Cert/CoercivePassageCommon.lean:327`).

**Theorem: Bound a curl-gradient coordinate.** Each curl-gradient coordinate has absolute value at most nine times the second-derivative operator norm. Source: `Breakdown.Coercive.Internal.PassageCommon.abs_vortGrad_le` (`Breakdown/Cert/CoercivePassageCommon.lean:342`).

**Definition: A bilinear stretching expression.** Use two velocity-gradient pairs to polarise the strain, vorticity-gradient, and mixed stretching terms. Source: `Breakdown.Coercive.Internal.PassageCommon.stretchPair` (`Breakdown/Cert/CoercivePassageCommon.lean:353`).

**Theorem: Bound the polarised stretching form.** The polarised stretching form is bounded by 729 times the three products involving the background gradient or Hessian and the input field or gradient norms. Source: `Breakdown.Coercive.Internal.PassageCommon.abs_stretchPair_le` (`Breakdown/Cert/CoercivePassageCommon.lean:359`).

**Theorem: Curl vector preserves subtraction.** Under the stated hypotheses, the curl vector commutes with subtraction. Source: `Breakdown.Coercive.Internal.PassageCommon.curlVec_sub` (`Breakdown/Cert/CoercivePassageCommon.lean:426`).

**Theorem: Polarise the stretching difference.** The difference of the two quadratic stretching forms splits into two bilinear terms containing the velocity and gradient differences. Source: `Breakdown.Coercive.Internal.PassageCommon.stretchForm_sub_eq` (`Breakdown/Cert/CoercivePassageCommon.lean:431`).

**Theorem: Control operator norm by column energy.** The squared operator norm is at most three times the sum of the squared column norms. Source: `Breakdown.Coercive.Internal.PassageCommon.norm_sq_le_matSq` (`Breakdown/Cert/CoercivePassageCommon.lean:441`).

**Theorem: Decay bounds the background gradient.** The background decay hypothesis bounds the gradient operator norm by the absolute decay constant. Source: `Breakdown.Coercive.Internal.PassageCommon.norm_fderiv_le_of_decay` (`Breakdown/Cert/CoercivePassageCommon.lean:450`).

**Theorem: Weighted background Hessian bound.** The background decay hypothesis bounds the Hessian operator norm times 1 + ‖y‖ by the absolute decay constant. Source: `Breakdown.Coercive.Internal.PassageCommon.norm_secondDeriv_mul_le_of_decay` (`Breakdown/Cert/CoercivePassageCommon.lean:461`).

**Theorem: Bound stretching by field energies.** The stretching form is bounded by 729 times the absolute decay constant times six gradient-square units plus the radially weighted velocity square. Source: `Breakdown.Coercive.Internal.PassageCommon.abs_stretchForm_le` (`Breakdown/Cert/CoercivePassageCommon.lean:476`).

**Theorem: Control a stretching discrepancy.** The stretching difference is bounded by quadratic and mixed terms in the gradient discrepancy and radially weighted velocity discrepancy, with factor 729 times the absolute decay constant. Source: `Breakdown.Coercive.Internal.PassageCommon.abs_stretchForm_sub_le` (`Breakdown/Cert/CoercivePassageCommon.lean:519`).

**Theorem: Stretching has finite absolute integral.** The absolute stretching form has finite integral over one time period under the decay and perturbation hypotheses. Source: `Breakdown.Coercive.Internal.PassageCommon.stretchForm_finite` (`Breakdown/Cert/CoercivePassageCommon.lean:588`).

**Theorem: Stretching errors vanish in period L¹.** The period integral of the absolute difference between the approximating and limiting stretching forms tends to zero. Source: `Breakdown.Coercive.Internal.PassageCommon.stretchForm_tendsto` (`Breakdown/Cert/CoercivePassageCommon.lean:607`).

**Theorem: Choose one almost-everywhere subsequence.** One strictly increasing subsequence makes every member of the countable error family tend to zero almost everywhere in the time slab. Source: `Breakdown.Coercive.Internal.PassageCommon.ae_subseq_tendsto_zero` (`Breakdown/Cert/CoercivePassageCommon.lean:699`).

**Theorem: Recover a vanishing real sequence.** Convergence to zero after nonnegative extended-real conversion implies convergence to zero for the stated nonnegative real sequence. Source: `Breakdown.Coercive.Internal.PassageCommon.tendsto_zero_of_ofReal` (`Breakdown/Cert/CoercivePassageCommon.lean:737`).

**Theorem: Choose simultaneous field convergence.** One strictly increasing subsequence gives almost-everywhere convergence of all indexed errors, velocity, gradient, and the squared second-derivative discrepancy. Source: `Breakdown.Coercive.Internal.PassageCommon.ae_subseq_fields` (`Breakdown/Cert/CoercivePassageCommon.lean:743`).

### Breakdown.Cert.CoercivePerturbationFacts

The local-integrability, local-square-integrability, and full-Hessian-energy requirements for weak perturbations are exposed as separate specifications for later mode arguments.

**Paper context:** Appendix B, Proposition B.1: weak-perturbation regularity interfaces.

**Interface definition: Local integrability of weak data.** This proposition specifies local integrability of the velocity, gradient, and second derivative of every weak perturbation under its listed hypotheses. Source: `Breakdown.Coercive.PerturbationLocalIntegrabilityHolds` (`Breakdown/Cert/CoercivePerturbationFacts.lean:12`).

Supplied by `Breakdown.Coercive.perturbationLocalIntegrabilityHolds_proof` (`lean/Breakdown/Cert/CoercivePerturbationFactsProof.lean:746`).

**Interface definition: Control the full second derivative.** This proposition specifies the bound of the full second-derivative energy by the squared trace energy of a weak perturbation under its listed hypotheses. Source: `Breakdown.Coercive.PerturbationSecondDerivBoundHolds` (`Breakdown/Cert/CoercivePerturbationFacts.lean:18`).

Supplied by `Breakdown.Coercive.perturbationSecondDerivBoundHolds_proof` (`lean/Breakdown/Cert/CoercivePerturbationFactsProof.lean:738`).

**Interface definition: Local L² control of velocity.** This proposition specifies finite velocity L² mass on every spatial ball over one time period under its listed hypotheses. Source: `Breakdown.Coercive.PerturbationLocalSquareIntegrabilityHolds` (`Breakdown/Cert/CoercivePerturbationFacts.lean:22`).

Supplied by `Breakdown.Coercive.perturbationLocalSquareIntegrabilityHolds_proof` (`lean/Breakdown/Cert/CoercivePerturbationFactsProof.lean:742`).

### Breakdown.Cert.CoercivePerturbationFactsProof

Spatial mollification, weak partial derivatives, Hessian-trace identities, and the energy-space embedding establish the perturbation regularity and local-energy specifications.

**Paper context:** Appendix B, Proposition B.1: proofs of the weak-perturbation regularity facts.

**Definition: A shrinking smooth spatial bump.** Choose a smooth bump with inner radius 1/(n+1) and outer radius 2/(n+1). Source: `Breakdown.Coercive.Internal.PerturbationFacts.bump` (`Breakdown/Cert/CoercivePerturbationFactsProof.lean:21`).

**Definition: The normalised spatial mollifier.** Normalise the shrinking smooth spatial bump to have integral one. Source: `Breakdown.Coercive.Internal.PerturbationFacts.kernel` (`Breakdown/Cert/CoercivePerturbationFactsProof.lean:25`).

**Definition: Scalar convolution in space.** Convolve a real kernel with a real field using scalar multiplication and spatial volume. Source: `Breakdown.Coercive.Internal.PerturbationFacts.convolve` (`Breakdown/Cert/CoercivePerturbationFactsProof.lean:27`).

**Definition: A weak coordinate derivative.** Require the distributional integration-by-parts identity against every smooth compactly supported scalar test. Source: `Breakdown.Coercive.Internal.PerturbationFacts.IsWeakPartial` (`Breakdown/Cert/CoercivePerturbationFactsProof.lean:30`).

**Theorem: Differentiate a convolution kernel.** A coordinate derivative of the convolution equals convolution with the corresponding derivative of its kernel. Source: `Breakdown.Coercive.Internal.PerturbationFacts.fderiv_convolve` (`Breakdown/Cert/CoercivePerturbationFactsProof.lean:33`).

**Theorem: Move a derivative through convolution.** Convolving the kernel derivative with a field equals convolving the kernel with the field's weak partial derivative. Source: `Breakdown.Coercive.Internal.PerturbationFacts.convolve_partial_eq` (`Breakdown/Cert/CoercivePerturbationFactsProof.lean:45`).

**Theorem: Weighted integral Cauchy-Schwarz.** The square of the integral of AB is at most the integral of A times the integral of AB² for the stated nonnegative measurable data. Source: `Breakdown.Coercive.Internal.PerturbationFacts.sq_lintegral_mul_le` (`Breakdown/Cert/CoercivePerturbationFactsProof.lean:64`).

**Theorem: The convolution L² estimate.** The squared L² energy of the convolution is at most the kernel's squared L¹ norm times the input's squared L² energy. Source: `Breakdown.Coercive.Internal.PerturbationFacts.lintegral_convolve_sq_le` (`Breakdown/Cert/CoercivePerturbationFactsProof.lean:88`).

**Definition: Weak derivatives on one time slice.** Collect local integrability, first and second weak coordinate derivatives, and finite first-derivative squares for a scalar slice. Source: `Breakdown.Coercive.Internal.PerturbationFacts.IsSliceData` (`Breakdown/Cert/CoercivePerturbationFactsProof.lean:134`).

**Theorem: Smoothness includes order two.** Derivative order two is below the infinite smoothness order. Source: `Breakdown.Coercive.Internal.PerturbationFacts.two_le_smooth` (`Breakdown/Cert/CoercivePerturbationFactsProof.lean:143`).

**Theorem: Mixed partial derivatives commute.** The two coordinate second derivatives of the stated smooth scalar function agree after interchanging their directions. Source: `Breakdown.Coercive.Internal.PerturbationFacts.second_symm` (`Breakdown/Cert/CoercivePerturbationFactsProof.lean:145`).

**Theorem: Convolution is smooth.** Under the stated hypotheses, the convolution is smooth. Source: `Breakdown.Coercive.Internal.PerturbationFacts.convolve_contDiff` (`Breakdown/Cert/CoercivePerturbationFactsProof.lean:158`).

**Theorem: Smooth coordinate kernel derivatives.** Under the stated hypotheses, the coordinate derivative of the mollifier kernel is smooth. Source: `Breakdown.Coercive.Internal.PerturbationFacts.partial_contDiff` (`Breakdown/Cert/CoercivePerturbationFactsProof.lean:162`).

**Theorem: Compact support of kernel partials.** Under the stated hypotheses, the coordinate derivative of the mollifier kernel has compact support. Source: `Breakdown.Coercive.Internal.PerturbationFacts.partial_hasCompactSupport` (`Breakdown/Cert/CoercivePerturbationFactsProof.lean:166`).

**Theorem: Convolution is integrable.** Under the stated hypotheses, the convolution is square integrable. Source: `Breakdown.Coercive.Internal.PerturbationFacts.memLp_convolve` (`Breakdown/Cert/CoercivePerturbationFactsProof.lean:170`).

**Theorem: Integrate a mixed-derivative square.** The integral of the mixed-derivative square equals the integral of the product of the corresponding diagonal derivatives under the stated decay and integrability hypotheses. Source: `Breakdown.Coercive.Internal.PerturbationFacts.integral_identity` (`Breakdown/Cert/CoercivePerturbationFactsProof.lean:182`).

**Theorem: Mollifier kernel is smooth.** Under the stated hypotheses, the mollifier kernel is smooth. Source: `Breakdown.Coercive.Internal.PerturbationFacts.kernel_contDiff` (`Breakdown/Cert/CoercivePerturbationFactsProof.lean:218`).

**Theorem: Mollifier kernel has compact support.** Under the stated hypotheses, the mollifier kernel has compact support. Source: `Breakdown.Coercive.Internal.PerturbationFacts.kernel_hasCompactSupport` (`Breakdown/Cert/CoercivePerturbationFactsProof.lean:220`).

**Theorem: Scalar Hessian and trace energies agree.** The total integrated square of the scalar Hessian equals the integrated square of its trace under the stated smoothness and integrability hypotheses. Source: `Breakdown.Coercive.Internal.PerturbationFacts.real_identity` (`Breakdown/Cert/CoercivePerturbationFactsProof.lean:223`).

**Theorem: Mollified Hessian and trace energies.** The full squared energy of the mollified Hessian equals the squared energy of its mollified trace on the spatial slice. Source: `Breakdown.Coercive.Internal.PerturbationFacts.slice_identity` (`Breakdown/Cert/CoercivePerturbationFactsProof.lean:259`).

**Theorem: Mollifier kernel is nonnegative.** The mollifier kernel is nonnegative for the stated data. Source: `Breakdown.Coercive.Internal.PerturbationFacts.kernel_nonneg` (`Breakdown/Cert/CoercivePerturbationFactsProof.lean:304`).

**Theorem: The mollifier has unit mass.** The integral of the mollifier kernel's nonnegative norm equals one. Source: `Breakdown.Coercive.Internal.PerturbationFacts.lintegral_kernel` (`Breakdown/Cert/CoercivePerturbationFactsProof.lean:306`).

**Theorem: Mollification decreases trace energy.** The squared spatial integral of the mollified trace is at most that of the original trace. Source: `Breakdown.Coercive.Internal.PerturbationFacts.slice_trace_le` (`Breakdown/Cert/CoercivePerturbationFactsProof.lean:314`).

**Theorem: The mollifier support shrinks to zero.** The outer radii of the spatial mollifier bumps tend to zero. Source: `Breakdown.Coercive.Internal.PerturbationFacts.bump_rOut_tendsto` (`Breakdown/Cert/CoercivePerturbationFactsProof.lean:336`).

**Theorem: Weak Hessian energy is trace-controlled.** The integrated sum of squared weak second derivatives is at most the squared integral energy of their diagonal sum. Source: `Breakdown.Coercive.Internal.PerturbationFacts.slice_secondDeriv_le` (`Breakdown/Cert/CoercivePerturbationFactsProof.lean:341`).

**Theorem: Coordinate basis vectors have norm one.** Every coordinate basis vector has norm one. Source: `Breakdown.Coercive.Internal.PerturbationFacts.norm_unitVector_eq` (`Breakdown/Cert/CoercivePerturbationFactsProof.lean:378`).

**Theorem: Coordinates retain local integrability.** Each coordinate of the stated locally integrable vector field is locally integrable. Source: `Breakdown.Coercive.Internal.PerturbationFacts.component_locallyIntegrable` (`Breakdown/Cert/CoercivePerturbationFactsProof.lean:381`).

**Theorem: Local integrability of weak columns.** Under the stated hypotheses, the selected column of the weak derivative is locally integrable. Source: `Breakdown.Coercive.Internal.PerturbationFacts.apply_locallyIntegrable` (`Breakdown/Cert/CoercivePerturbationFactsProof.lean:386`).

**Theorem: Extract a scalar weak partial.** Each coordinate of the vector weak-gradient relation gives the corresponding scalar weak partial derivative. Source: `Breakdown.Coercive.Internal.PerturbationFacts.weak_component` (`Breakdown/Cert/CoercivePerturbationFactsProof.lean:392`).

**Theorem: Extract scalar weak slice data.** The coordinate components of the weak field, gradient, and Hessian satisfy the scalar slice-data specification. Source: `Breakdown.Coercive.Internal.PerturbationFacts.sliceData_of` (`Breakdown/Cert/CoercivePerturbationFactsProof.lean:409`).

**Theorem: Expand the full Hessian square.** The nonnegative extended-real Hessian square is the sum of the squares of all its coordinate entries. Source: `Breakdown.Coercive.Internal.PerturbationFacts.secondDerivSq_eq` (`Breakdown/Cert/CoercivePerturbationFactsProof.lean:429`).

**Theorem: Expand the squared trace norm.** The nonnegative extended-real squared trace norm is the sum over output coordinates of the squared diagonal sums. Source: `Breakdown.Coercive.Internal.PerturbationFacts.traceSq_eq` (`Breakdown/Cert/CoercivePerturbationFactsProof.lean:445`).

**Theorem: Trace control of vector Hessian energy.** On the stated weak spatial slice, the full Hessian-square integral is at most the squared trace-norm integral. Source: `Breakdown.Coercive.Internal.PerturbationFacts.slice_secondDerivSq_le` (`Breakdown/Cert/CoercivePerturbationFactsProof.lean:452`).

**Theorem: Squared matrix norm is continuous.** Under the stated hypotheses, the squared matrix norm is continuous. Source: `Breakdown.Coercive.Internal.PerturbationFacts.continuous_matNorm` (`Breakdown/Cert/CoercivePerturbationFactsProof.lean:470`).

**Theorem: Measurability of slice gradient energy.** Under the stated hypotheses, the time-dependent spatial gradient energy is measurable up to a null set. Source: `Breakdown.Coercive.Internal.PerturbationFacts.aemeasurable_matNorm` (`Breakdown/Cert/CoercivePerturbationFactsProof.lean:474`).

**Theorem: Finite gradient energy on a.e. slices.** For almost every time in the unit period, the spatial integral of the squared column norm of the weak gradient is finite. Source: `Breakdown.Coercive.Internal.PerturbationFacts.ae_matSq_lt_top` (`Breakdown/Cert/CoercivePerturbationFactsProof.lean:483`).

**Theorem: Trace control of period Hessian energy.** The full second-derivative energy over one period is at most the squared trace-norm energy over that period. Source: `Breakdown.Coercive.Internal.PerturbationFacts.secondDeriv_bound` (`Breakdown/Cert/CoercivePerturbationFactsProof.lean:489`).

**Theorem: Bound operator norm by column norms.** The operator norm of a linear map is at most the sum of the norms of its three coordinate columns. Source: `Breakdown.Coercive.Internal.PerturbationFacts.opNorm_le_sum_apply` (`Breakdown/Cert/CoercivePerturbationFactsProof.lean:500`).

**Theorem: The weak gradient is locally integrable.** The weak gradient field is locally integrable on space-time under the perturbation hypotheses. Source: `Breakdown.Coercive.Internal.PerturbationFacts.gradient_locallyIntegrable` (`Breakdown/Cert/CoercivePerturbationFactsProof.lean:516`).

**Theorem: The weak Hessian is locally integrable.** The weak second-derivative field is locally integrable on space-time under the perturbation hypotheses. Source: `Breakdown.Coercive.Internal.PerturbationFacts.secondDeriv_locallyIntegrable` (`Breakdown/Cert/CoercivePerturbationFactsProof.lean:528`).

**Theorem: Control operator norm by column energy.** The squared operator norm is at most three times the sum of the squared coordinate-column norms. Source: `Breakdown.Coercive.Internal.PerturbationFacts.sq_norm_le_three_matNorm` (`Breakdown/Cert/CoercivePerturbationFactsProof.lean:554`).

**Theorem: Represent a weak field in energy space.** There is an energy-space element representing the weak velocity almost everywhere whose squared norm equals the spatial gradient energy. Source: `Breakdown.Coercive.Internal.PerturbationFacts.slice_embed` (`Breakdown/Cert/CoercivePerturbationFactsProof.lean:566`).

**Theorem: Local L¹ control from gradient energy.** The velocity's L¹ integral on a unit ball is bounded by the energy-space embedding norm, one plus its gradient energy, and the stated ball-volume factor. Source: `Breakdown.Coercive.Internal.PerturbationFacts.slice_ball_bound` (`Breakdown/Cert/CoercivePerturbationFactsProof.lean:598`).

**Theorem: Read the squared L² norm as an integral.** The nonnegative integral of the pointwise norm square equals the square of the extended L² norm. Source: `Breakdown.Coercive.Internal.PerturbationFacts.lintegral_sq_eq_eLpNorm` (`Breakdown/Cert/CoercivePerturbationFactsProof.lean:619`).

**Theorem: Local L² control from gradient energy.** The velocity's L² energy on a closed ball is bounded by its gradient energy times the squared Sobolev embedding and ball-volume factor. Source: `Breakdown.Coercive.Internal.PerturbationFacts.slice_ball_sq_bound` (`Breakdown/Cert/CoercivePerturbationFactsProof.lean:628`).

**Theorem: Finite local period L² energy.** The velocity's squared norm has finite integral over the unit time period and the stated closed spatial ball. Source: `Breakdown.Coercive.Internal.PerturbationFacts.velocity_localSquare` (`Breakdown/Cert/CoercivePerturbationFactsProof.lean:666`).

**Theorem: The weak velocity is locally integrable.** The weak velocity field is locally integrable on space-time under the perturbation hypotheses. Source: `Breakdown.Coercive.Internal.PerturbationFacts.velocity_locallyIntegrable` (`Breakdown/Cert/CoercivePerturbationFactsProof.lean:689`).

**Theorem: Control the full second derivative.** The supplied hypotheses establish the bound of the full second-derivative energy by the squared trace energy of a weak perturbation. Source: `Breakdown.Coercive.perturbationSecondDerivBoundHolds_proof` (`Breakdown/Cert/CoercivePerturbationFactsProof.lean:738`).

**Theorem: Local L² control of velocity.** The supplied hypotheses establish finite velocity L² mass on every spatial ball over one time period. Source: `Breakdown.Coercive.perturbationLocalSquareIntegrabilityHolds_proof` (`Breakdown/Cert/CoercivePerturbationFactsProof.lean:742`).

**Theorem: Local integrability of weak data.** The supplied hypotheses establish local integrability of the velocity, gradient, and second derivative of every weak perturbation. Source: `Breakdown.Coercive.perturbationLocalIntegrabilityHolds_proof` (`Breakdown/Cert/CoercivePerturbationFactsProof.lean:746`).
<!-- /passage:front -->

