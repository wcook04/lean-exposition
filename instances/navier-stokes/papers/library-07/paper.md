
<!-- passage:front -->
# Library guide 7: Breakdown/Cert

**Navier–Stokes pages:** [the paper](../navier-stokes-paper/paper.pdf) · [proof routes](../navier-stokes-routes/paper.md) · [routes in detail](../navier-stokes-route-details/paper.md) · library guide: [1](../navier-stokes-library-01/paper.md) [2](../navier-stokes-library-02/paper.md) [3](../navier-stokes-library-03/paper.md) [4](../navier-stokes-library-04/paper.md) [5](../navier-stokes-library-05/paper.md) [6](../navier-stokes-library-06/paper.md) **7** [8](../navier-stokes-library-08/paper.md) [9](../navier-stokes-library-09/paper.md) [10](../navier-stokes-library-10/paper.md) [11](../navier-stokes-library-11/paper.md) [12](../navier-stokes-library-12/paper.md) [13](../navier-stokes-library-13/paper.md) [14](../navier-stokes-library-14/paper.md) [15](../navier-stokes-library-15/paper.md) [16](../navier-stokes-library-16/paper.md) [17](../navier-stokes-library-17/paper.md) [18](../navier-stokes-library-18/paper.md) [19](../navier-stokes-library-19/paper.md) [20](../navier-stokes-library-20/paper.md) [21](../navier-stokes-library-21/paper.md) [22](../navier-stokes-library-22/paper.md) [23](../navier-stokes-library-23/paper.md) [24](../navier-stokes-library-24/paper.md) [25](../navier-stokes-library-25/paper.md) [26](../navier-stokes-library-26/paper.md) [27](../navier-stokes-library-27/paper.md) [28](../navier-stokes-library-28/paper.md) [29](../navier-stokes-library-29/paper.md) [30](../navier-stokes-library-30/paper.md)

*A plain title and a sentence for each declaration in `Breakdown.Cert.FreeTransportHeatLimit` to `Breakdown.Cert.WeakCompact` of Alpöge and Buckmaster's Lean at `ad53419de079eb8f95f60313473374624a348546`, in the authors' file order. Prepared with AI assistance. The authors have not reviewed it.*

Each paragraph names one declaration and says whether it is a definition, a proposition that the library defines (its name usually ends in `Holds` or `Statement`) or a proved result, then what it states. Click a paragraph to open its Lean on the right.

### Breakdown.Cert.FreeTransportHeatLimit

The mild propagator has an initial trace as elapsed time tends to zero. This file proves that trace through its heat representation and test-function pairings. §7.5: the free similarity equation

**Source namespace `Breakdown.Cert.Internal.PropagatorTrace`.**

**Heat flow with the similarity dilation** · definition. `rescaledHeat`: The rescaled heat field combines heat evolution, spatial dilation and the inverse square-root amplitude factor. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportHeatLimit.lean#L17).

**The frequency formula for smoothing** · theorem. `Breakdown.Cert.FreeTransportHeatLimit.smoothH_coe`: At positive time, the smoothed element's ambient L² representative is obtained by the scalar Fourier multiplier. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportHeatLimit.lean#L20).

**Smoothing gives the heat Laplacian root** · theorem. `isHalfSspOf_smoothH`: The smoothed square-root Laplacian operator realizes the square-root Laplacian of the heat-evolved field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportHeatLimit.lean#L25).

**Dilation preserves the Laplacian root** · theorem. `isHalfSspOf_dilX`: Dilation with the inverse square-root amplitude preserves the square-root Laplacian relation with the correspondingly dilated derivative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportHeatLimit.lean#L35).

**The propagator's rescaled heat reading** · theorem. `velocity_slicePropagator_ae`: Almost everywhere in space, the propagated velocity is the physical reading of the normalized rescaled heat field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportHeatLimit.lean#L53).

**The similarity scale starts at one** · theorem. `tendsto_exp_neg`: As positive elapsed time tends to zero, its negative exponential tends to one. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportHeatLimit.lean#L64).

**The heat trace returns the input** · theorem. `tendsto_heat_trace`: The heat evolution at one minus the negative exponential converges to the initial field as elapsed time tends to zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportHeatLimit.lean#L70).

**Rescaled heat returns its initial value** · theorem. `tendsto_rescaledHeat`: The rescaled and dilated heat field converges to its initial field as positive elapsed time tends to zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportHeatLimit.lean#L82).

**A compact-test bound for an L² field** · theorem. `pairing_bound`: Uniformly bounded tests supported in a fixed ball have integrable L² pairings controlled by the test bound and ball-volume factor. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportHeatLimit.lean#L112).

**Convergence of compact-test pairings** · theorem. `tendsto_pairing_of_bound`: L² convergence of the fields and the uniform compact-test bounds give convergence of the physical pairings. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportHeatLimit.lean#L170).

**The initial tested propagator trace** · theorem. `tendsto_propagator_pairing_of_bound`: The propagator's physical velocity pairing converges to the initial physical field pairing under the compact-test bounds. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportHeatLimit.lean#L200).

**Source namespace `Breakdown.Cert`.**

**The propagator has its initial trace** · theorem. `tendsto_propagator_pairing`: Testing the propagated physical velocity against the continuous compact test recovers the initial physical field in the zero-time limit. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportHeatLimit.lean#L217).

### Breakdown.Cert.FreeTransportMild

The physical weak equation is obtained by integrating a differentiated propagator pairing. This file justifies the time integration, endpoint trace and interchange of integrals. §7.5: the free similarity equation

**Sobolev control gives local energy** · theorem. `lintegral_ball_sq_le`: The velocity representative's square integral on a ball is bounded by the velocity embedding norm, a ball-volume factor and the homogeneous norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportMild.lean#L18).

**The velocity is integrable against tests** · theorem. `integrable_inner_velocity`: The physical velocity reading has an integrable time-space pairing with the compact test vector. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportMild.lean#L50).

**The adjoint similarity-transport test** · definition. `transportTest`: The transport test combines minus the period-scaled time derivative, minus the test and minus half the radial derivative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportMild.lean#L110).

**The spatial Laplacian of a test** · definition. `sspTest`: The test Laplacian is the sum of the three second coordinate derivatives. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportMild.lean#L113).

**The physical pairing of a lifted curve** · definition. `sliceVelocityPairing`: The slice velocity pairing integrates the physical velocity of the lifted homogeneous-space curve against the time-space test. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportMild.lean#L116).

**Read time derivatives from joint ones** · theorem. `deriv_time_eq`: The test's time derivative is its joint derivative evaluated on the unit time direction. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportMild.lean#L119).

**Smooth spatial test derivatives** · theorem. `contDiff_partialField`: Each spatial coordinate derivative of a smooth time-space test is jointly smooth. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportMild.lean#L125).

**Joint derivatives in the transport test** · theorem. `transportTest_eq`: The adjoint transport test can be written using the time and spatial restrictions of the joint derivative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportMild.lean#L135).

**The test Laplacian is continuous** · theorem. `continuous_sspTest`: The spatial Laplacian of the smooth time-space test is jointly continuous. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportMild.lean#L143).

**Compact support of the test Laplacian** · theorem. `hasCompactSupport_sspTest`: The test Laplacian has compact time-space support. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportMild.lean#L148).

**Continuity of the full adjoint test** · theorem. `continuous_transportTest`: The adjoint transport test minus its Laplacian is jointly continuous. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportMild.lean#L163).

**Compact support of the adjoint test** · theorem. `hasCompactSupport_transportTest`: The transport-minus-Laplacian test has compact time-space support. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportMild.lean#L179).

**Move a velocity derivative onto a test** · theorem. `slice_column_velocity`: The weak velocity-gradient relation gives integrable coordinate pairings and the signed integration-by-parts identity. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportMild.lean#L201).

**Move both test derivatives onto the test** · theorem. `slice_byParts_velocity`: The gradient-test pairing equals minus the velocity pairing with the test Laplacian on each spatial slice. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportMild.lean#L232).

**The time-space Laplacian test identity** · theorem. `integral_matInner_eq_ssp`: The integrated gradient-test pairing is minus the velocity pairing with the test Laplacian. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportMild.lean#L261).

**Physical and curve pairings agree** · theorem. `integral_inner_velocity_eq_slices`: The time-space velocity-test integral equals the lifted gradient-curve slice velocity pairing. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportMild.lean#L273).

**A uniform slice-pairing bound exists** · theorem. `exists_velocity_pairing_bound`: The compact test family gives a common integrable envelope and a uniform linear bound for every homogeneous-space velocity pairing. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportMild.lean#L301).

**Continuity of velocity test pairings** · theorem. `continuous_velocity_pairing`: The physical velocity pairing is continuous jointly in test time and homogeneous-space input. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportMild.lean#L372).

**Velocity tests admit the pairing** · theorem. `isSlicePairingBound_velocity`: The velocity-test pairing has constants giving the bounded compact-time slice-pairing predicate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportMild.lean#L414).

**Pair the inverse over past times** · theorem. `slicePairing_gradInv_eq_Ioi`: For positive period under the propagator and inverse hypotheses, the inverse velocity pairing with a continuous compact test equals the elapsed-time integral of propagated shifted-test pairings. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportMild.lean#L451).

**Exchange the two time integrals** · theorem. `integral_swap_propagator`: The propagated physical test pairing permits interchanging positive elapsed time and base time integrals. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportMild.lean#L460).

**The propagator's initial physical trace** · theorem. `propagator_initial_trace`: The zero-time limit of the propagated velocity pairing is the initial physical field paired with the initial test. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportMild.lean#L478).

**The elapsed-time pairing is integrable** · theorem. `integrableOn_propagator_pairing`: The propagated velocity pairing with the compact test is integrable over positive elapsed times. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportMild.lean#L485).

**Continuity of period-scaled shifts** · theorem. `continuous_timeShift`: The test shifted by base time and elapsed time divided by the period remains jointly continuous. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportMild.lean#L502).

**Compact support after time rescaling** · theorem. `hasCompactSupport_timeShift`: The period-scaled time shift preserves compact support of the time-space test. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportMild.lean#L506).

**The inverse pairing with base time first** · theorem. `slicePairing_gradInv_eq`: For positive period under the propagator and inverse hypotheses, exchanging time integrals expresses the inverse velocity pairing as a base-time integral of propagated shifted-test pairings. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportMild.lean#L519).

**Integrate the propagator identity** · theorem. `propagator_transport_pairing`: Integrating the propagator against the adjoint transport-minus-Laplacian test recovers its initial physical test pairing. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportMild.lean#L528).

**Recover the forcing pairing from slices** · theorem. `integral_inner_of_slices`: The physical forcing-test integral is the integral of the slice pairings of its Hilbert-space representative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportMild.lean#L615).

**The mild inverse solves the tested PDE** · theorem. `mild_slice_pairing`: The gradient-inverse velocity paired with the adjoint transport-minus-Laplacian test equals the physical forcing-test integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportMild.lean#L630).

**Verify the selected inverse** · theorem. `freeInvSpec_of`: Assuming the free-inverse existence property and a positive period, the selected free inverse satisfies its defining gradient relation. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportMild.lean#L642).

**The physical mild transport equation** · theorem. `mild_transport`: The physical velocity transport-test pairing equals the forcing-test pairing minus the gradient-test pairing. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportMild.lean#L648).

### Breakdown.Cert.FreeTransportReading

The mild solution's abstract curves must be represented by periodic physical fields. This file constructs the transport reading and proves the weak Hessian integration-by-parts formula. §7.5: the free similarity equation

**The physical transport curve** · definition. `transportCurve`: The transport curve is the physical forcing curve minus the physical second-component curve. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportReading.lean#L19).

**A physical representative of transport** · proposition definition. `IsTransportPart`: A transport representative is measurable and periodic and agrees almost everywhere with the physical transport curve on time slices. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportReading.lean#L23).

**Choose a periodic transport reading** · theorem. `exists_transportPart`: The physical transport curve admits a jointly measurable periodic field representative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportReading.lean#L27).

**Locally integrable gradient columns** · theorem. `locallyIntegrable_column`: Each coordinate column of the weak gradient is locally integrable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportReading.lean#L30).

**Identify the physical gradient columns** · theorem. `column_ae_eq_partialX`: Each physical gradient column equals the corresponding homogeneous-space partial derivative almost everywhere. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportReading.lean#L36).

**The squared extended L² norm formula** · theorem. `lintegral_enorm_sq_Lp`: The integral of the squared extended norm of the representative equals the squared extended L² norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportReading.lean#L47).

**Convert a finite sum of squared norms** · theorem. `ofReal_sum_norm_sq`: The extended-nonnegative image of a finite sum of norm squares equals the sum of their squared extended norms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportReading.lean#L51).

**Integrate finite column energies** · theorem. `lintegral_sum_slices`: The nonnegative integral of the sum of column square norms equals the sum of their L² norm squares. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportReading.lean#L57).

**Finite period energy of a finite family** · theorem. `lintegral_sum_curve`: A finite family of L²-valued time-circle curves has finite summed square integral over one real period. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportReading.lean#L64).

**Slice bounds give finite period energy** · theorem. `periodLIntegral_lt_top_of_slices`: The stated slice representatives and L² curve bounds imply finiteness of the nonnegative periodic integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportReading.lean#L77).

**Finite period energy of the trace** · theorem. `sumSecondPartials_finite_of_reading`: The physical Hessian reading has a trace with finite periodic square integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportReading.lean#L91).

**Finite period energy of transport** · theorem. `derivative_finite_of_transportPart`: The physical representative of the transport curve has finite periodic square integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportReading.lean#L103).

**The Hessian trace is continuous** · theorem. `Breakdown.Cert.FreeTransportReading.continuous_secondDerivTrace`: Taking the sum of the three diagonal Hessian evaluations is a continuous operation. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportReading.lean#L110).

**The full forcing field** · definition. `fullField`: The full field is the physical transport field minus the trace of its supplied Hessian. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportReading.lean#L116).

**The transport curve's physical formula** · theorem. `transportCurve_ae`: Almost everywhere in real time, the transport curve is physical forcing minus the physical second component. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportReading.lean#L119).

**Cancel the second-component subtraction** · theorem. `sub_sub_neg_self`: Subtracting the negative of the previously subtracted term restores the original value. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportReading.lean#L133).

**The full field represents the forcing** · theorem. `fullField_slices`: Almost every time slice of the full physical field represents the original Hilbert-space forcing. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportReading.lean#L136).

**Admissibility of the periodic full field** · theorem. `isPeriodicField_fullField`: The reconstructed full field satisfies the periodic-field conditions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportReading.lean#L148).

**Each unit interval has the same integral** · theorem. `lintegral_unit_of_periodic`: A periodic nonnegative function has the same integral on every integer-translated unit interval. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportReading.lean#L162).

**Bound a multiple-period interval** · theorem. `lintegral_Ioc_le_of_unit`: A uniform unit-period integral bound gives the number-of-periods bound on an interval of integer length. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportReading.lean#L171).

**Periodic L² fields are test-integrable** · theorem. `integrable_inner_of_periodic`: A finite-period-energy field has an integrable time-space pairing with a compact test. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportReading.lean#L187).

**The inner product in coordinates** · theorem. `inner_eq_sum_coord`: The spatial inner product is the sum of the three coordinate products. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportReading.lean#L252).

**A test coordinate is a scalar test** · theorem. `isTestFunction_coord`: Each coordinate of a spatial vector test is a smooth compactly supported scalar test. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportReading.lean#L256).

**A derivative commutes with coordinates** · theorem. `fderiv_coord`: The derivative of a vector coordinate is that coordinate of the vector derivative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportReading.lean#L261).

**Weak Hessian integration by coordinates** · theorem. `slice_component`: The coordinate test paired with a diagonal weak Hessian entry equals minus the derivative test paired with the corresponding gradient entry. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportReading.lean#L269).

**A coordinate of a finite vector sum** · theorem. `coord_sum`: Taking one coordinate of a finite vector sum equals summing that coordinate of the summands. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportReading.lean#L294).

**Coordinate integration by parts exists** · theorem. `slice_terms_integrable`: Both the Hessian-test product and gradient-test-derivative product are spatially integrable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportReading.lean#L297).

**Integrate the Hessian trace by parts** · theorem. `slice_byParts`: The spatial matrix-gradient pairing equals minus the Hessian-trace test pairing. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportReading.lean#L316).

**Restrict the joint test derivative** · theorem. `fderiv_slice`: The spatial derivative of a fixed-time test is the joint derivative restricted to spatial directions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportReading.lean#L341).

**Every test slice is smooth** · theorem. `contDiff_slice`: Every fixed-time slice of the smooth joint test is infinitely differentiable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportReading.lean#L347).

**Every test slice has compact support** · theorem. `hasCompactSupport_slice`: Every fixed-time slice of the compact joint test has compact spatial support. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportReading.lean#L351).

**Test derivative columns are continuous** · theorem. `partial_continuous`: Each spatial derivative column of the joint test is continuous. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportReading.lean#L357).

**Compact support of test derivatives** · theorem. `partial_hasCompactSupport`: Each spatial derivative column of the joint test has compact time-space support. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportReading.lean#L367).

**Finite energy of gradient columns** · theorem. `column_finite_of_reading`: Each physical gradient column has finite periodic square integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportReading.lean#L380).

**The weak Hessian trace test formula** · theorem. `integral_matInner_eq`: The time-space gradient-test pairing is integrable and equals minus the time-space Hessian-trace pairing. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportReading.lean#L393).

### Breakdown.Cert.FreeTransportRescaled

Similarity coordinates turn the propagator into a rescaled heat evolution. This file differentiates its test pairing and identifies the temporal, Laplacian and drift terms. §7.5: the free similarity equation

**The spatial sum of second partials** · definition. `spaceSsp`: The spatial Laplacian sums the three second coordinate derivatives of the vector field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportRescaled.lean#L15).

**A test in expanding coordinates** · definition. `rescaledTest`: The rescaled test evaluates the original time slice at position multiplied by the exponential half-time scale. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportRescaled.lean#L18).

**The smoothed heat Laplacian root** · theorem. `isHalfSspOf_heat_smoothH`: The heat-evolved field and the smoothed square-root Laplacian field satisfy the square-root Laplacian relation. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportRescaled.lean#L20).

**The propagator is a dilated heat field** · theorem. `velocity_slicePropagator_ae`: Almost everywhere, the propagated velocity is the physical heat field dilated by the negative time exponential. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportRescaled.lean#L35).

**Change variables in a dilated pairing** · theorem. `integral_inner_dilateField`: The physical dilation pairing equals the inverse-scale factor times the original field paired with the inversely rescaled test. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportRescaled.lean#L54).

**The square root of the exponential scale** · theorem. `sqrt_exp_neg`: The square root of the negative time exponential equals the negative half-time exponential. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportRescaled.lean#L71).

**A rescaled heat pairing formula** · theorem. `integral_inner_velocity_slicePropagator`: The propagated velocity-test pairing equals an exponential factor times the heat field paired with the spatially rescaled test. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportRescaled.lean#L75).

**A physical integral is an L² pairing** · theorem. `integral_inner_eq_inner_toLp`: The physical integral pairing equals the L² inner product with the test's L² class. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportRescaled.lean#L89).

**Convert a sum into L²** · theorem. `toLpOrZero_add`: For square-integrable inputs, the L²-or-zero conversion preserves addition. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportRescaled.lean#L100).

**Convert a scalar multiple into L²** · theorem. `toLpOrZero_smul`: For square-integrable inputs, the L²-or-zero conversion preserves scalar multiplication. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportRescaled.lean#L106).

**The rescaled test remains admissible** · theorem. `isSpaceTimeTestVector_rescaled`: The similarity-rescaled test remains a smooth compactly supported time-space test vector. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportRescaled.lean#L112).

**The rescaled test's time derivative** · theorem. `deriv_rescaled`: The time derivative of the rescaled test is its original time derivative plus the half-weighted radial derivative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportRescaled.lean#L126).

**Differentiate a spatially scaled input** · theorem. `fderiv_comp_const_smul`: The derivative after constant spatial scaling is the scalar multiple of the original derivative at the scaled point. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportRescaled.lean#L158).

**The Laplacian under spatial rescaling** · theorem. `spaceSsp_rescaled`: The Laplacian of the rescaled test is the time exponential times the original Laplacian at the rescaled point. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportRescaled.lean#L165).

**A test slice belongs to L²** · theorem. `memLp_slice`: Each smooth compactly supported spatial test slice belongs to L². [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportRescaled.lean#L194).

**The time derivative of a test lies in L²** · theorem. `memLp_timeDeriv`: Each fixed-time temporal derivative of the test belongs to spatial L². [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportRescaled.lean#L198).

**The test Laplacian belongs to L²** · theorem. `memLp_spaceSsp`: The spatial sum of second partials of the test belongs to L². [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportRescaled.lean#L216).

**Convert a difference into L²** · theorem. `toLpOrZero_sub`: For square-integrable inputs, the L²-or-zero conversion preserves subtraction. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportRescaled.lean#L235).

**An L² bound from support and supremum** · theorem. `norm_toLpOrZero_le`: A field bounded by a constant and supported in a ball has L² norm bounded by that constant times the square root of the ball volume. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportRescaled.lean#L241).

**A uniform ball contains every test** · theorem. `support_bound`: The compact joint test has a single spatial radius beyond which every time slice vanishes. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportRescaled.lean#L271).

**A uniform quadratic time remainder** · theorem. `remainder_bound`: The smooth compact test has a uniform quadratic Taylor remainder bound in its time variable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportRescaled.lean#L281).

**Differentiate the L²-valued test curve** · theorem. `hasDerivAt_toLp_of_test`: The L² curve of test slices is differentiable with derivative represented by the temporal derivative of the test. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportRescaled.lean#L341).

**Relate real and complex pairings** · theorem. `inner_realVec_eq`: The real-vector pairing is the real part of the corresponding complex inner product after complexification. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportRescaled.lean#L372).

**Move the Fourier transform in a pairing** · theorem. `inner_freqTrR_eq`: The complex inner product with a forward Fourier transform equals the pairing with the inverse transform in the other slot. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportRescaled.lean#L376).

**The physical pairing in Fourier space** · theorem. `integral_inner_toPhys_eq`: The physical test integral is the real part of the frequency-space inner product with the Fourier transform of the complexified test. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportRescaled.lean#L383).

**Move the Fourier Laplacian onto the test** · theorem. `integral_inner_ssp_of_isSspOf`: The second-order Fourier relation gives the physical integral identity with minus the test Laplacian. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportRescaled.lean#L402).

**The propagator pairing in rescaled L²** · theorem. `pairing_eq_inner_rescaled`: The propagated velocity pairing is the exponential factor times the heat-field L² inner product with the rescaled test. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportRescaled.lean#L450).

**Move the heat Laplacian onto the test** · theorem. `inner_sspHeat_eq`: The scaled negative second-order heat term paired with a test equals the heat field paired with the scaled test Laplacian. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportRescaled.lean#L458).

**Assemble the rescaled adjoint expression** · theorem. `rescaled_sum_eq`: The original temporal, Laplacian, scaling and drift test terms become the rescaled temporal derivative, scaled Laplacian and rescaled test. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportRescaled.lean#L471).

**Split the three test contributions** · theorem. `integral_inner_sum`: The physical pairing with the three-term test sum is the corresponding sum of L² pairings. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportRescaled.lean#L485).

**Identify the propagator derivative** · theorem. `pairing_value_eq`: The physical adjoint-test pairing equals the three heat-and-rescaled-test terms from the product rule. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportRescaled.lean#L493).

**Differentiate a propagator pairing** · theorem. `hasDerivAt_pairing_slicePropagator`: At positive elapsed time, the derivative of the propagator pairing is its pairing against the temporal, Laplacian, scaling and radial test terms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportRescaled.lean#L513).

### Breakdown.Cert.FrozenBridge

The smooth certificate route needs the same physical-to-abstract coercivity transfer. This file proves simultaneous rotation invariance on almost every time slice and then establishes the frozen-profile bridge. §7.7: coercivity and the linearized inverse, with analytic support lemmas

**Source namespace `Breakdown.Cert.Internal.FrozenBridge`.**

**Read time as its fractional part** · theorem. `Breakdown.Cert.FrozenBridge.circleRep_coe`: The chosen representative of a real time modulo one is its fractional part. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FrozenBridge.lean#L18).

**A circle representative returns** · theorem. `Breakdown.Cert.FrozenBridge.coe_circleRep`: Projecting the chosen real representative back to the time circle gives the original point. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FrozenBridge.lean#L23).

**Transfer null sets to the time circle** · theorem. `ae_circleRep`: An almost-everywhere real-time property holds almost everywhere when time-circle points are read through their chosen real representatives. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FrozenBridge.lean#L26).

**Transfer a quotient-compatible property** · theorem. `ae_circleRep_coe`: An almost-everywhere property of real time and its circle class transfers to circle points and their real representatives. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FrozenBridge.lean#L34).

**View an isometry as a linear operator** · definition. `asCLM`: The spatial linear isometry is regarded as a continuous linear map on space. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FrozenBridge.lean#L39).

**The operator has the same action** · theorem. `asCLM_apply`: The continuous linear map underlying an isometry sends every spatial vector to the same image as that isometry. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FrozenBridge.lean#L42).

**Recover an isometry from its operator** · theorem. `asCLM_injective`: Two spatial linear isometries with the same underlying continuous linear map are equal. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FrozenBridge.lean#L44).

**View a linear operator as a function** · definition. `asMap`: The continuous linear operator is regarded as a continuous map from space to itself. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FrozenBridge.lean#L47).

**Continuous passage to function space** · theorem. `continuous_asMap`: The passage from a continuous linear operator to its continuous-map representation is continuous. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FrozenBridge.lean#L49).

**Orthogonal maps preserve spatial measure** · theorem. `measurePreserving_asMap`: The continuous-map representation of a spatial linear isometry preserves Lebesgue measure. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FrozenBridge.lean#L52).

**Invariant curves have fixed slices** · theorem. `rot_ae`: A curve invariant under the symmetry set has rotation-fixed Hilbert-space slices almost everywhere for each admitted pure rotation. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FrozenBridge.lean#L57).

**Read rotation invariance in space** · theorem. `fix_of_rot`: A rotation-fixed homogeneous-space element has a physical velocity representative satisfying the same rotation law almost everywhere. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FrozenBridge.lean#L77).

**Rotation laws persist under limits** · theorem. `fix_closed`: A spatial L⁶ field invariant under a convergent sequence of orthogonal maps is invariant almost everywhere under its limit. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FrozenBridge.lean#L85).

**Choose countably many dense operators** · theorem. `exists_countable_dense`: Every set of spatial linear operators contains a countable subset whose closure contains the original set. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FrozenBridge.lean#L127).

**One null set handles all rotations** · theorem. `ae_invariant`: Almost every time slice of an invariant curve satisfies all admitted pure-rotation laws for its physical velocity. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FrozenBridge.lean#L132).

**Weak gradient columns are unique** · theorem. `col_ae`: Almost-everywhere equal fields with weak gradients have almost-everywhere equal gradient columns in every coordinate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FrozenBridge.lean#L150).

**The convection Hölder exponents** · theorem. `conjExponent_three_six`: The exponents three and six combine to exponent two in Hölder's inequality. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FrozenBridge.lean#L165).

**A decaying profile gives L² convection** · theorem. `memLp_sliceConvection`: A twice differentiable profile with inverse-radius velocity decay and inverse-square gradient decay gives a square-integrable convection slice. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FrozenBridge.lean#L176).

**Expand a spatial vector in coordinates** · theorem. `vec_sum`: Every spatial vector is the sum of its three coordinates times the corresponding unit vectors. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FrozenBridge.lean#L229).

**The frozen bound on a graph slice** · theorem. `Breakdown.Cert.FrozenBridge.slice_bridge`: Under the reading and symmetry hypotheses, the frozen spatial estimate bounds the graph-slice energy below by minus the form constant times its weighted energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FrozenBridge.lean#L234).

**Source namespace `Breakdown.Cert`.**

**Prove the frozen-profile bridge** · theorem. `frozenBridgeHolds_of`: The slice-reading, free-equivariance, projection and convection properties together establish the frozen-profile coercivity bridge. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FrozenBridge.lean#L315).

### Breakdown.Cert.GradInvSpec

The gradient inverse is defined by a positive-time propagator integral. This file proves the scalar majorant integrable, establishes the operator's continuity and linearity, and verifies its specification and norm bound. §7.5: the free similarity equation

**Source namespace `Breakdown.Cert`.**

**The integrated propagator bound** · definition. `propagatorBound`: The propagator bound is the positive-time integral of the exponential smoothing majorant. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/GradInvSpec.lean#L14).

**Source namespace `Breakdown.Cert.GradInv.Internal`.**

**The propagator's scalar majorant** · definition. `kernel`: The scalar kernel is the exponential decay factor multiplied by the inverse square root of the heat smoothing scale. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/GradInvSpec.lean#L19).

**Positive elapsed heat time** · theorem. `one_sub_exp_pos`: For positive elapsed time, one minus its negative exponential is strictly positive. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/GradInvSpec.lean#L21).

**Inverse square root as a real power** · theorem. `rpow_neg_half_eq`: For a nonnegative real input, its negative half power equals the inverse of its square root. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/GradInvSpec.lean#L26).

**The sharp squared smoothing bound** · theorem. `phiFactor_sq_le_sharp`: At positive smoothing time, the squared Fourier smoothing factor is at most the reciprocal of twice Euler's number times that time. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/GradInvSpec.lean#L29).

**Bound the Fourier smoothing factor** · theorem. `abs_phiFactor_le`: At positive smoothing time, the Fourier smoothing factor has absolute value at most the inverse square root of twice Euler's number times that time. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/GradInvSpec.lean#L46).

**The smoothing factor is even** · theorem. `phiFactor_neg`: Negating the frequency leaves the scalar Fourier smoothing factor unchanged. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/GradInvSpec.lean#L53).

**Smoothing preserves the frequency space** · theorem. `smoothH_mem`: At positive time, multiplication by the scalar smoothing factor preserves the admissible frequency subspace. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/GradInvSpec.lean#L56).

**The frequency formula for smoothing** · theorem. `Breakdown.Cert.GradInvSpec.smoothH_coe`: At positive time, the smoothed element's ambient L² representative is obtained by the scalar Fourier multiplier. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/GradInvSpec.lean#L61).

**Small dilations are contractions** · theorem. `norm_dilX_le_one`: For a positive dilation scale at most one, the homogeneous-space dilation operator has norm at most one. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/GradInvSpec.lean#L65).

**Source namespace `Breakdown.Cert`.**

**The smoothing operator norm bound** · theorem. `norm_smoothH_le`: At positive time, the smoothed norm is bounded by the input norm divided by the square root of twice Euler's number times that time. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/GradInvSpec.lean#L74).

**Bound one propagated slice** · theorem. `norm_slicePropagator_le`: At positive elapsed time, the propagated slice norm is at most the scalar kernel times the input norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/GradInvSpec.lean#L81).

**Source namespace `Breakdown.Cert.GradInv.Internal`.**

**The scalar kernel is positive** · theorem. `kernel_pos`: The propagator's scalar majorant is strictly positive at every positive elapsed time. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/GradInvSpec.lean#L95).

**The scalar kernel is continuous** · theorem. `continuousOn_kernel`: The propagator's scalar majorant is continuous on the positive half-line. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/GradInvSpec.lean#L98).

**Compare positive reciprocal scales** · theorem. `inv_le_inv_add_one`: Positive scales a and b satisfying b² ≤ a²(1 + b²) also satisfy 1/a ≤ 1/b + 1. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/GradInvSpec.lean#L105).

**An integrable bound for the kernel** · theorem. `kernel_le`: At positive time, the kernel is bounded by the sum of an exponentially damped inverse-square-root term and the same exponential. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/GradInvSpec.lean#L115).

**The comparison kernel is integrable** · theorem. `integrableOn_majorant`: The sum of the exponentially damped inverse-square-root term and exponential term is integrable over positive time. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/GradInvSpec.lean#L141).

**The propagator kernel is integrable** · theorem. `integrableOn_kernel`: The scalar kernel has a finite integral over the positive half-line. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/GradInvSpec.lean#L149).

**Read the bound as the kernel integral** · theorem. `propagatorBound_eq`: The propagator bound equals the integral of the scalar kernel over positive elapsed time. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/GradInvSpec.lean#L156).

**Source namespace `Breakdown.Cert`.**

**The explicit bound integrand exists** · theorem. `integrableOn_propagatorBound`: The explicit exponential smoothing formula defining the propagator bound is integrable over positive time. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/GradInvSpec.lean#L160).

**The propagator bound is positive** · theorem. `propagatorBound_pos`: The positive-time integral defining the propagator bound is strictly positive. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/GradInvSpec.lean#L165).

**Source namespace `Breakdown.Cert.GradInv.Internal`.**

**Time translation preserves the L² norm** · theorem. `norm_shiftLp`: Translating a Hilbert-space-valued curve on the time circle leaves its L² norm unchanged. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/GradInvSpec.lean#L176).

**Bound the slice operator norm** · theorem. `norm_slicePropagator_op_le`: At positive elapsed time, the slice propagator's operator norm is at most the scalar kernel. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/GradInvSpec.lean#L180).

**Bound the integrated-propagator input** · theorem. `norm_propagatorIntegrand_le`: At positive elapsed time, the shifted propagator integrand has norm at most the kernel times the forcing norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/GradInvSpec.lean#L183).

**The L² norm as a squared integral** · theorem. `norm_sq_eq_integral`: The squared norm of a Hilbert-space-valued L² class equals the integral of the squared norm of its representative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/GradInvSpec.lean#L194).

**Apply bounded convergent operators** · theorem. `tendsto_apply_of_norm_le`: Convergence at the limiting input, an eventual operator-norm bound and convergence of inputs imply convergence of the applied operators. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/GradInvSpec.lean#L201).

**Lift strong convergence to L² curves** · theorem. `tendsto_compLpL`: Pointwise strong convergence with an eventual uniform operator bound gives strong convergence of the induced operators on each L² curve. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/GradInvSpec.lean#L217).

**Smoothing varies continuously in time** · theorem. `continuousOn_smoothH`: For each homogeneous-space input, its smoothed value depends continuously on strictly positive smoothing time. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/GradInvSpec.lean#L268).

**The propagated slice varies continuously** · theorem. `continuousOn_slicePropagator`: For each homogeneous-space input, the propagated slice depends continuously on strictly positive elapsed time. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/GradInvSpec.lean#L274).

**A local propagator norm bound** · theorem. `eventually_norm_slicePropagator_le`: Near any positive elapsed time, the slice operator norm is eventually bounded by the kernel at that time plus one. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/GradInvSpec.lean#L294).

**Continuous period-scaled time shifts** · theorem. `continuous_shift`: The L² curve obtained by shifting time by minus elapsed time divided by the period depends continuously on elapsed time. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/GradInvSpec.lean#L302).

**Continuity of the inverse integrand** · theorem. `continuousOn_propagatorIntegrand`: For fixed period and forcing, the shifted propagator integrand is continuous at every positive elapsed time. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/GradInvSpec.lean#L309).

**Source namespace `Breakdown.Cert`.**

**The inverse integrand is integrable** · theorem. `integrable_propagatorIntegrand`: For every period and forcing, the shifted propagator integrand is Bochner integrable over positive elapsed time. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/GradInvSpec.lean#L327).

**Source namespace `Breakdown.Cert.GradInv.Internal`.**

**Bound the integrated propagator** · theorem. `norm_integral_propagator_le`: The integrated propagator has norm at most the scalar propagator bound times the forcing norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/GradInvSpec.lean#L336).

**The propagator integrand is additive** · theorem. `propagatorIntegrand_add`: Applying the shifted propagator to a sum of forcings gives the sum of their propagator integrands. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/GradInvSpec.lean#L344).

**The propagator integrand is homogeneous** · theorem. `propagatorIntegrand_smul`: Multiplying the forcing by a real scalar multiplies its shifted propagator integrand by that scalar. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/GradInvSpec.lean#L349).

**The integrated propagator is additive** · theorem. `integral_propagatorIntegrand_add`: Integrating the shifted propagator of a sum gives the sum of the two integrated propagators. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/GradInvSpec.lean#L354).

**The integrated propagator is homogeneous** · theorem. `integral_propagatorIntegrand_smul`: The integrated shifted propagator commutes with multiplication of the forcing by a real scalar. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/GradInvSpec.lean#L361).

**Package the integral as a linear map** · definition. `integralLinear`: The positive-time integral of the shifted propagator defines a linear operator on the Hilbert space of time-circle curves. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/GradInvSpec.lean#L367).

**Source namespace `Breakdown.Cert`.**

**Verify the gradient-inverse formula** · theorem. `gradInv_spec`: The selected gradient inverse satisfies the integral specification at every period parameter. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/GradInvSpec.lean#L377).

**A uniform gradient-inverse bound** · theorem. `norm_gradInv_le`: The gradient-inverse output norm is bounded by the propagator bound times the forcing norm for every period parameter. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/GradInvSpec.lean#L382).

### Breakdown.Cert.HalfOrderGraphMem

This file identifies the closed correction-space graph with the square-root Laplacian relation, whose Fourier symbol is 2π‖ξ‖ and whose differential order is one. Section 7.5: support for the graph-space realization of the free inverse.

**Source namespace `Breakdown.Cert.HalfOrderGraph.Internal`.**

**The square-root Laplacian graph** · definition. `halfSspSubmodule`: The square-root Laplacian graph subspace consists of pairs whose second component is the square-root Laplacian of the first. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HalfOrderGraphMem.lean#L13).

**Membership in the square-root graph** · theorem. `mem_halfSspSubmodule`: A pair belongs to the graph subspace exactly when its components satisfy the square-root Laplacian relation. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HalfOrderGraphMem.lean#L40).

**Convergence of first components** · theorem. `tendsto_fst_coe`: Convergence of pairs in the product energy space gives convergence of their first components in complex L2. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HalfOrderGraphMem.lean#L43).

**Convergence of second components** · theorem. `tendsto_snd_coe`: Convergence of pairs in the product energy space gives convergence of their second components in complex L2. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HalfOrderGraphMem.lean#L48).

**The square-root graph is closed** · theorem. `isClosed_halfSspSubmodule`: The subspace defined by the square-root Laplacian relation is closed. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HalfOrderGraphMem.lean#L53).

**Two descriptions of the graph agree** · theorem. `halfOrderGraph_eq_halfSspSubmodule`: The closure-based graph equals the subspace defined directly by the square-root Laplacian relation. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HalfOrderGraphMem.lean#L73).

**Source namespace `Breakdown.Cert`.**

**A graph element from its two parts** · theorem. `exists_xbar_of_halfSsp`: A pair satisfying the square-root Laplacian relation is represented by an element of the completed graph space. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HalfOrderGraphMem.lean#L91).

**The graph norm splits into two parts** · theorem. `norm_xbar_sq`: The squared graph norm is the sum of the squared gradient and second-part norms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HalfOrderGraphMem.lean#L95).

**The square-root Laplacian is unique** · theorem. `halfSsp_unique`: Two square-root Laplacians of the same energy-space element are equal. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HalfOrderGraphMem.lean#L98).

### Breakdown.Cert.HeldContracts

This file bounds the difference between two held iterations by a fixed multiple of their distance. Section 7.8: contraction of the held nonlinear correction.

**Source namespace `Breakdown.Cert.Internal.HeldContracts`.**

**Measure on one time period** · definition. `periodMeasure`: The period measure is the product of Lebesgue measure on the closed unit time interval and spatial volume. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldContracts.lean#L15).

**Period measure as a restriction** · theorem. `periodMeasure_eq`: The product period measure equals space-time volume restricted to the unit time slab. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldContracts.lean#L18).

**Measurability on one period** · theorem. `aesm_period`: A field measurable for space-time volume remains almost everywhere strongly measurable for the period measure. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldContracts.lean#L22).

**Period energy as a squared L2 norm** · theorem. `periodLIntegral_eq`: The period integral of the squared field norm equals its squared extended L2 norm on the unit time slab. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldContracts.lean#L28).

**The period norm is an L2 norm** · theorem. `periodNorm_eq`: The real period norm is the real value of the extended L2 norm for the period measure. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldContracts.lean#L43).

**Finite L2 norm for periodic fields** · theorem. `eLpNorm_lt_top`: A periodic square-integrable field has finite extended L2 norm on one time period. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldContracts.lean#L49).

**L2 bound for a negative sum** · theorem. `eLpNorm_neg_add_le`: The L2 norm of the negative sum of two periodic fields is at most the sum of their L2 norms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldContracts.lean#L58).

**Negative sums preserve periodicity** · theorem. `isPeriodicField_neg_add`: The negative sum of two periodic square-integrable fields is again a periodic square-integrable field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldContracts.lean#L68).

**Period norm of a negative sum** · theorem. `periodNorm_neg_add_le`: The period norm of a negative sum is bounded by the sum of the two period norms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldContracts.lean#L78).

**Local period norm below the full norm** · theorem. `periodBallNorm_le`: Restricting a periodic field to a spatial ball cannot increase its period norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldContracts.lean#L86).

**The period norm is nonnegative** · theorem. `periodNorm_nonneg`: The real period norm of any field is nonnegative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldContracts.lean#L92).

**Pairing a negative sum** · theorem. `integral_neg_add_pairing`: Against a space-time test field, the integral pairing with a negative sum is the negative sum of the two integral pairings. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldContracts.lean#L94).

**The gradient supremum as an L∞ norm** · theorem. `Breakdown.Cert.HeldContracts.supGrad_eq_eLpNorm`: The gradient supremum is the extended L∞ norm of the graph-space gradient map. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldContracts.lean#L105).

**Finite gradient bounds for differences** · theorem. `Breakdown.Cert.HeldContracts.supGrad_sub_lt_top`: The difference of two corrections with finite gradient supremum again has finite gradient supremum. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldContracts.lean#L108).

**Weighted energy is nonnegative** · theorem. `Breakdown.Cert.HeldContracts.energyW_nonneg`: A nonnegative weight gives nonnegative weighted energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldContracts.lean#L115).

**A sum of squares is nonnegative** · theorem. `sum_sq_nonneg`: The sum of the squared real coordinates is nonnegative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldContracts.lean#L119).

**Energy below the combined size** · theorem. `Breakdown.Cert.HeldContracts.sqrt_energyW_le_sizeZ`: The square root of the weighted energy is bounded by the combined correction-and-multiplier size. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldContracts.lean#L122).

**Multiplier norm below the combined size** · theorem. `Breakdown.Cert.HeldContracts.vecNorm_le_sizeZ`: For a nonnegative weight, the Euclidean multiplier norm is bounded by the combined size. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldContracts.lean#L126).

**Energy below the squared combined size** · theorem. `energyW_le_sq`: For a nonnegative weight, weighted energy is bounded by the square of the combined size. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldContracts.lean#L130).

**A quadratic contraction estimate** · theorem. `sq_bound`: Bounds on energy, multiplier size and forcing convert the quadratic estimate into the displayed scalar contraction coefficient. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldContracts.lean#L136).

**Rescaling a product by a positive rate** · theorem. `mul_eq_mul_div_mul`: Multiplying by a positive rate after dividing by it leaves the original product unchanged. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldContracts.lean#L159).

**A scaled bound from a squared bound** · theorem. `scaled_le`: The squared estimate and the coefficient smallness condition imply the required scaled linear bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldContracts.lean#L162).

**The field part of the bordered map** · theorem. `Breakdown.Cert.HeldContracts.bordered_fst`: The field component of the bordered operator is the forcing plus convection of its free inverse plus the actuator field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldContracts.lean#L179).

**The pin part of the bordered map** · theorem. `Breakdown.Cert.HeldContracts.bordered_snd`: The finite-dimensional component of the bordered operator is the pin map of the free inverse. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldContracts.lean#L182).

**The forcing in the held iteration** · theorem. `Breakdown.Cert.HeldContracts.heldRight_fst`: The field part of the held right-hand side is the negative defect minus the quadratic product of the correction. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldContracts.lean#L185).

**The pin target in the held iteration** · theorem. `Breakdown.Cert.HeldContracts.heldRight_snd`: The finite-dimensional part of the held right-hand side is the prescribed target gap. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldContracts.lean#L188).

**Subtracting held right-hand sides** · theorem. `heldRight_sub_fst`: The difference of two held field right-hand sides is the negative difference of their quadratic products. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldContracts.lean#L191).

**The bordered map preserves differences** · theorem. `bordered_sub`: Applying the bordered operator to a difference gives the difference of the two outputs. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldContracts.lean#L196).

**The forcing difference is bilinear** · theorem. `sub_fst_eq`: For two bordered solutions, the forcing difference splits into the two bilinear terms involving their correction difference. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldContracts.lean#L200).

**The difference has zero pin data** · theorem. `sub_pin_eq`: Two bordered solutions with the same held target have a free-inverse difference whose pin map is zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldContracts.lean#L212).

**Distance between inverse images** · theorem. `heldDist_step`: The held distance between two free-inverse states is the maximum of their combined difference size and their scaled gradient supremum. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldContracts.lean#L224).

**Combined size below held distance** · theorem. `sizeZ_le_heldDist`: The combined size of a state difference is bounded by the held distance. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldContracts.lean#L231).

**Gradient difference below held distance** · theorem. `sup_le_heldDist`: The scaled gradient supremum of a state difference is bounded by the held distance. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldContracts.lean#L234).

**The zero multiplier has zero norm** · theorem. `vecNorm_zero`: The Euclidean norm of the zero multiplier vector is zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldContracts.lean#L238).

**The difference forcing is periodic** · theorem. `forcing_periodic`: The product estimate makes the two-term nonlinear difference forcing a periodic square-integrable field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldContracts.lean#L245).

**A bound for the physical forcing** · theorem. `forcing_norm`: If each bilinear contribution is bounded by the same scalar, their negative sum has period norm at most twice that scalar. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldContracts.lean#L250).

**A bound for the represented forcing** · theorem. `forcing_normH`: The Hilbert-space representative of the nonlinear difference forcing has norm at most twice the bound on each bilinear contribution. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldContracts.lean#L259).

**Physical and abstract forcing pairings** · theorem. `forcing_pairing`: The physical difference forcing pairs with a test field exactly as its Hilbert-space representative pairs with the represented test. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldContracts.lean#L272).

**Coercivity with zero pin difference** · theorem. `coercive_part`: With zero pin data, the global and ball forcing estimates combine into the total coercivity constant times the forcing bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldContracts.lean#L291).

**Use the maximal period in the bound** · theorem. `ratio_bound`: For a certified parameter in the box, replacing its period by the maximal period enlarges the contraction coefficient. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldContracts.lean#L313).

**The scaled gradient contraction bound** · theorem. `sup_part`: The certified quadratic gradient estimate and combined-size bound yield the scaled gradient bound needed by the held metric. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldContracts.lean#L327).

**The core held contraction estimate** · theorem. `contract_core`: The coercive, supremum and product hypotheses bound the distance between two updated states by the explicit contraction factor times their input distance. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldContracts.lean#L373).

**Source namespace `Breakdown.Cert`.**

**Assemble the held contraction theorem** · theorem. `heldContractsHolds_of`: The bordered inverse, coercivity, supremum, product and invariance interfaces supply the held contraction interface. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldContracts.lean#L419).

### Breakdown.Cert.HeldExistsUnique

This file turns a fixed point of the held iteration into a solution of the bordered nonlinear system and proves uniqueness. Section 7.8: existence and uniqueness at a fixed parameter.

**Source namespace `Breakdown.Cert.Internal.HeldExistsUnique`.**

**The chosen bordered inverse is valid** · theorem. `Breakdown.Cert.HeldExistsUnique.borderedInv_spec`: When a bordered inverse exists, the selected inverse satisfies its defining specification. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldExistsUnique.lean#L14).

**The field part of the bordered map** · theorem. `Breakdown.Cert.HeldExistsUnique.bordered_fst`: The field component of the bordered operator is the forcing plus convection of its free inverse plus the actuator field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldExistsUnique.lean#L20).

**The pin part of the bordered map** · theorem. `Breakdown.Cert.HeldExistsUnique.bordered_snd`: The finite-dimensional component of the bordered operator is the pin map of the free inverse. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldExistsUnique.lean#L23).

**The pin target in the held iteration** · theorem. `Breakdown.Cert.HeldExistsUnique.heldRight_snd`: The finite-dimensional part of the held right-hand side is the prescribed target gap. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldExistsUnique.lean#L26).

**The held forcing preserves symmetry** · theorem. `heldRight_mem`: For certified data and an invariant correction, the held field right-hand side lies in the invariant Hilbert subspace. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldExistsUnique.lean#L29).

**The correction after one held step** · theorem. `heldStep_fst`: A held step applies the free inverse to the field component of the bordered inverse of the current right-hand side. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldExistsUnique.lean#L36).

**The multiplier after one held step** · theorem. `heldStep_snd`: A held step takes its new multiplier from the finite-dimensional component of the bordered inverse. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldExistsUnique.lean#L39).

**The forcing in the held iteration** · theorem. `Breakdown.Cert.HeldExistsUnique.heldRight_fst`: The field part of the held right-hand side is the negative defect minus the quadratic product of the correction. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldExistsUnique.lean#L42).

**One held step written as a pair** · theorem. `heldStep_mk`: The held update is the pair consisting of its free-inverse correction and its bordered-inverse multiplier. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldExistsUnique.lean#L46).

**The inverse solves the bordered system** · theorem. `borderedInv_apply`: For invariant right-hand sides at a certified parameter, the chosen bordered inverse preserves invariance and solves the bordered equation. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldExistsUnique.lean#L50).

**Zero graph parts give zero energy** · theorem. `energyW_eq_zero_of`: If the gradient part vanishes almost everywhere and the second part is zero, the weighted energy is zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldExistsUnique.lean#L56).

**A zero gradient has zero supremum** · theorem. `supGrad_eq_zero_of`: An almost everywhere zero graph gradient has zero gradient supremum. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldExistsUnique.lean#L79).

**The zero correction has zero gradient** · theorem. `coe_zero_ae`: The time representative of the zero graph correction has zero gradient part almost everywhere. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldExistsUnique.lean#L85).

**The zero correction has zero energy** · theorem. `energyW_zero`: The weighted energy of the zero correction is zero for every weight. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldExistsUnique.lean#L90).

**The zero correction has zero supremum** · theorem. `supGrad_zero`: The gradient supremum of the zero correction is zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldExistsUnique.lean#L93).

**An inverse solution is a fixed point** · theorem. `fixed_of_solution`: A pair returned unchanged by the bordered inverse equation gives a fixed point of the held update after applying the free inverse. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldExistsUnique.lean#L95).

**A held solution solves the bordered map** · theorem. `bordered_of_solution`: The field and multiplier of a held solution satisfy the bordered equation with the held right-hand side. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldExistsUnique.lean#L101).

**The zero state is admissible** · theorem. `zero_mem_heldSet`: The zero correction and zero multiplier belong to the held set for certified data. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldExistsUnique.lean#L114).

**Move a negative sum to the left** · theorem. `add_eq_zero_aux`: An equality between a sum and a negative term gives the corresponding three-term sum equal to zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldExistsUnique.lean#L128).

**Assemble a held solution from bounds** · theorem. `solution_of_eqs`: The bordered equation, invariance, free-inverse identity and size bounds together give a held solution. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldExistsUnique.lean#L133).

**A held fixed point gives a solution** · theorem. `solution_of_fixed`: An admissible fixed point yields a held solution through the chosen bordered inverse. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldExistsUnique.lean#L144).

**Recover a held solution by inversion** · theorem. `inv_of_solution`: A held solution gives an admissible state and is recovered by applying the bordered inverse to its held right-hand side. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldExistsUnique.lean#L155).

**Source namespace `Breakdown.Cert`.**

**A unique held solution exists** · theorem. `heldExistsUniqueHolds_of`: The fixed-point, metric, self-map, contraction and inverse interfaces imply existence and uniqueness of the held solution. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldExistsUnique.lean#L170).

### Breakdown.Cert.HeldLimit

This file passes held solutions to a parameter limit, using weak compactness for graph variables and strong local convergence for the nonlinear term. Section 7.8: stability and continuity of the selected held solution.

**Source namespace `Breakdown.Cert.Internal.HeldLimit`.**

**Varying operators preserve weak limits** · theorem. `tendsto_inner_clm_apply`: Norm-convergent bounded operators applied to a bounded weakly convergent sequence converge against every test vector. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimit.lean#L17).

**A weak limit preserves a zero sum** · theorem. `inner_sum_eq_zero_of_tendsto`: If the five summands converge against a test vector and their sums vanish, the limiting sum pairs to zero with that test. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimit.lean#L39).

**Weak convergence of finite coordinates** · theorem. `tendsto_clm_of_weak`: A continuous linear map to a finite-dimensional coordinate space sends weak convergence to ordinary convergence. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimit.lean#L56).

**The invariant Hilbert space is closed** · theorem. `isClosed_invariantHH`: The Hilbert subspace fixed by the specified symmetries is closed. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimit.lean#L70).

**Weighted gradient energy is nonnegative** · theorem. `weighted_integral_nonneg`: A nonnegative weight gives a nonnegative time integral of the slice gradient energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimit.lean#L75).

**Weighted energy is nonnegative** · theorem. `Breakdown.Cert.HeldLimit.energyW_nonneg`: A nonnegative weight gives nonnegative weighted energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimit.lean#L83).

**Second derivatives below weighted energy** · theorem. `secondCLM_sq_le`: For a nonnegative weight, the squared second-part norm is bounded by the weighted energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimit.lean#L89).

**Energy below the combined size** · theorem. `Breakdown.Cert.HeldLimit.sqrt_energyW_le_sizeZ`: The square root of the weighted energy is bounded by the combined correction-and-multiplier size. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimit.lean#L95).

**Multiplier norm below the combined size** · theorem. `Breakdown.Cert.HeldLimit.vecNorm_le_sizeZ`: For a nonnegative weight, the Euclidean multiplier norm is bounded by the combined size. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimit.lean#L99).

**Each multiplier coordinate is bounded** · theorem. `abs_le_vecNorm`: The absolute value of each multiplier coordinate is bounded by its Euclidean norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimit.lean#L103).

**The function norm below Euclidean norm** · theorem. `Breakdown.Cert.HeldLimit.norm_le_vecNorm`: The norm of the finite coordinate function is bounded by its Euclidean norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimit.lean#L108).

**Bound one term of a zero sum** · theorem. `norm_le_of_add_eq_zero`: When five vectors sum to zero, the norm of the first is at most the sum of the other four norms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimit.lean#L113).

**The L2 norm squared is an integral** · theorem. `l2_norm_sq_eq_integral`: The squared norm of an L2 element equals the integral of the squared norm of its representative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimit.lean#L121).

**An L2 representative has finite energy** · theorem. `l2_integrable_norm_sq`: The squared norm of the representative of an L2 element is integrable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimit.lean#L127).

**A quadratic split survives L2 lifting** · theorem. `norm_sq_compLpL_add`: A pointwise two-part squared-norm identity remains true after applying the two maps to L2 functions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimit.lean#L132).

**The L∞ bound controls the L2 norm** · theorem. `norm_compLpL_le_top`: On the probability measure used here, the L2 norm of a mapped function is bounded by its finite L∞ norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimit.lean#L145).

**Split the graph-space norm** · theorem. `norm_sq_xbar`: The graph-space squared norm is the sum of the squared norms of its two component maps. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimit.lean#L153).

**Split the time-dependent graph norm** · theorem. `norm_sq_eq`: The squared correction norm equals the squared gradient-map norm plus the squared second-map norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimit.lean#L156).

**The gradient norm below its supremum** · theorem. `gradCLM_norm_le`: The finite gradient supremum bounds the gradient-map L2 norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimit.lean#L159).

**A square identity gives a linear bound** · theorem. `le_add_of_sq_eq`: For nonnegative quantities, a sum-of-squares identity bounds the left quantity by the sum of the two parts. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimit.lean#L164).

**Bound the correction by its two parts** · theorem. `norm_le_add`: The correction norm is at most the sum of its gradient and second-part norms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimit.lean#L168).

**Convergent operators have a common bound** · theorem. `exists_bound_of_tendsto`: A norm-convergent sequence of continuous linear maps admits one nonnegative operator bound valid for every index. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimit.lean#L171).

**The L∞ ball is convex** · theorem. `convex_topBall`: The subset of L2 functions with a fixed extended L∞ bound is convex. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimit.lean#L178).

**The L∞ ball is closed in L2** · theorem. `isClosed_topBall`: The subset of L2 functions with a fixed extended L∞ bound is closed. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimit.lean#L194).

**An L∞ bound survives weak convergence** · theorem. `topBall_of_weak`: A uniform extended L∞ bound on the images under a continuous linear map passes to a weak limit. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimit.lean#L208).

**Identify the gradient supremum** · theorem. `supGrad_eq`: The gradient supremum equals the extended L∞ norm of the represented gradient. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimit.lean#L217).

**The gradient bound survives a weak limit** · theorem. `supGrad_le_of_weak`: A uniform gradient supremum bound passes to the weakly convergent correction limit. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimit.lean#L220).

**Volume weighted by the energy weight** · definition. `weightedVolume`: The weighted spatial measure has density given by the nonnegative part of the weight. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimit.lean#L228).

**A bounded weight bounds the measure** · theorem. `weightedVolume_le`: An upper bound on the weight bounds the weighted measure by the corresponding scalar multiple of volume. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimit.lean#L231).

**L2 fields remain L2 for bounded weights** · theorem. `memLp_weighted`: A bounded nonnegative weight makes every spatial L2 field an L2 field for the weighted measure. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimit.lean#L238).

**Null sets remain null after weighting** · theorem. `ae_weighted`: A statement true almost everywhere for volume is true almost everywhere for the weighted measure. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimit.lean#L242).

**The linear weighted L2 embedding** · definition. `weightedLin`: The weighted embedding regards an ordinary L2 field as an L2 field for the bounded weighted measure. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimit.lean#L246).

**Norm bound for the weighted embedding** · theorem. `weightedLin_norm_le`: The weighted L2 embedding has norm bounded by the square root of the upper bound on the weight. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimit.lean#L256).

**The continuous weighted L2 embedding** · definition. `weightedCLM`: The norm estimate upgrades the weighted embedding to a continuous linear map. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimit.lean#L266).

**Weighted norm as an energy integral** · theorem. `weightedCLM_norm_sq`: The squared norm of the weighted embedding equals the integral of the weight times the squared field norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimit.lean#L270).

**A squared linear image norm is convex** · theorem. `convexOn_norm_sq_comp`: The squared norm of a continuous linear image is convex on the whole real vector space. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimit.lean#L282).

**Quadratic bounds survive weak limits** · theorem. `quadratic_le_of_weak`: A uniform bound on a finite sum of squared linear-image norms passes to a weak limit. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimit.lean#L289).

**Integrability of weighted energy** · theorem. `Breakdown.Cert.HeldLimit.integrable_weighted`: A bounded nonnegative weight makes the weighted squared norm of an L2 field integrable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimit.lean#L311).

**Weighted derivative norms of a slice** · theorem. `sliceWeightedGrad_eq`: The weighted gradient energy of a slice is the sum of three squared weighted derivative norms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimit.lean#L319).

**One weighted derivative of a graph pair** · definition. `weightedGradPart`: The weighted derivative map composes a graph pair's gradient part with one spatial derivative and the weighted L2 embedding. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimit.lean#L327).

**Weighted energy of a graph pair** · theorem. `weighted_slice_eq`: The weighted slice energy of a graph pair equals the sum of its three weighted derivative norms squared. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimit.lean#L331).

**Integrate a finite quadratic sum** · theorem. `integral_sum_norm_sq`: Integrating the sum of squared linear-image norms gives the sum of the squared lifted L2 norms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimit.lean#L336).

**Time-integrated weighted gradient norms** · theorem. `weighted_integral_eq`: The time integral of weighted slice energy equals the sum of the squared time-L2 norms of the weighted derivative maps. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimit.lean#L347).

**Weighted energy as squared linear norms** · theorem. `energyW_eq`: The weighted correction energy is the squared second-part norm plus the three squared weighted gradient norms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimit.lean#L356).

**A combined quadratic bound persists** · theorem. `sqrt_le_of_weak`: A uniform square-root bound on linear-image energies and finite multiplier coordinates passes to their weak and ordinary limits. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimit.lean#L361).

**The combined size survives weak limits** · theorem. `sizeZ_le_of_weak`: The combined correction-and-multiplier size bound passes to a weak correction limit and a convergent multiplier vector. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimit.lean#L396).

**The selected reading is valid** · theorem. `Breakdown.Cert.HeldLimit.isReadingOf_readingOf`: The selected velocity, gradient and second-derivative representatives give a valid physical reading of the correction. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimit.lean#L414).

**Monotonicity of local period integrals** · theorem. `periodBallLIntegral_mono`: A pointwise comparison of nonnegative integrands gives the same comparison of their period integrals over a spatial ball. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimit.lean#L423).

**One squared component below the norm** · theorem. `sq_component_le`: The squared norm of any component is bounded by the squared Euclidean norm of the vector. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimit.lean#L428).

**Convergence of one nonlinear column** · theorem. `column_integral_tendsto`: Strong local convergence of the scalar and gradient columns gives convergence of their tested product integrals. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimit.lean#L431).

**Expand a map in coordinate directions** · theorem. `Breakdown.Cert.HeldLimit.apply_eq_sum`: A linear map applied to a vector is the sum of its coordinate-direction values weighted by the vector coordinates. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimit.lean#L464).

**Expand a tested linear map** · theorem. `inner_apply_eq_sum`: Pairing a linear image with a vector equals the sum of the coordinate-weighted pairings of its columns. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimit.lean#L470).

**Convergence of tested advection** · theorem. `tendsto_integral_apply`: The local convergence hypotheses imply convergence of the tested gradient-applied-to-velocity integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimit.lean#L475).

**Local convergence gives product pairings** · theorem. `tendsto_inner_productH_of_local`: Local convergence of free-inverse readings gives convergence of their quadratic Hilbert-space product against each represented test. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimit.lean#L505).

**Extract convergent nonlinear pairings** · theorem. `tendsto_inner_productH`: The compactness and reading hypotheses supply a subsequence whose quadratic products converge against every space-time test field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimit.lean#L539).

**Source namespace `Breakdown.Cert`.**

**Held solutions pass to parameter limits** · theorem. `heldLimitHolds_of`: The continuity, compactness, energy and product interfaces together supply the held-solution limit interface. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimit.lean#L563).

### Breakdown.Cert.HeldLimitProducts

This file proves that strong local L2 convergence is sufficient to pass the quadratic terms to the held-solution limit. Section 7.8: local convergence of nonlinear pairings.

**Source namespace `Breakdown.Cert.Internal.HeldLimitProducts`.**

**The L2 seminorm from squared integrals** · theorem. `eLpNorm_two_eq_lintegral`: The extended L2 seminorm is the square root of the integral of the squared norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimitProducts.lean#L13).

**Finite squared integral gives L2** · theorem. `memLp_two_of_lintegral`: A measurable function with finite squared-norm integral belongs to L2. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimitProducts.lean#L24).

**Squared integral convergence gives L2** · theorem. `tendsto_eLpNorm_sub_of_lintegral`: Convergence to zero of the squared difference integrals gives convergence to zero of the L2 difference seminorms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimitProducts.lean#L31).

**Real inner product is multiplication** · theorem. `inner_real_eq_mul`: The real inner product of two real numbers is their product. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimitProducts.lean#L39).

**The product of two L2 functions is L1** · theorem. `integrable_mul_of_memLp`: Two scalar L2 functions have an integrable product. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimitProducts.lean#L42).

**A product integral is an L2 pairing** · theorem. `integral_mul_eq_inner`: The integral of a product of scalar L2 functions equals the inner product of their L2 classes. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimitProducts.lean#L48).

**Eventually finite L2 seminorms** · theorem. `eventually_memLp_of_eLpNorm`: Convergence of the L2 difference seminorm to zero eventually places the sequence in L2. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimitProducts.lean#L56).

**From seminorm limits to L2 limits** · theorem. `tendsto_toLp_of_eLpNorm`: Convergence of representative L2 differences gives convergence of the corresponding L2 classes. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimitProducts.lean#L64).

**Convergence of products in L2** · theorem. `tendsto_integral_mul_of_eLpNorm`: L2 convergence of both scalar factors gives eventual integrability and convergence of their product integrals. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimitProducts.lean#L75).

**Periodicity preserves unit integrals** · theorem. `lintegral_unit_Icc`: For a one-periodic nonnegative function, integrating over any integer unit interval gives the same value. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimitProducts.lean#L100).

**A long interval is bounded by periods** · theorem. `lintegral_Icc_nat_le`: The nonnegative integral over the interval from minus N to N is bounded by twice N times the unit-period integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimitProducts.lean#L111).

**A space-time box is bounded by periods** · theorem. `lintegral_box_le`: A periodic nonnegative integrand on a finite time slab and spatial ball is bounded by the corresponding multiple of its local period integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimitProducts.lean#L144).

**Finite period bounds give finite boxes** · theorem. `lt_top_of_box`: A finite period integral remains finite after multiplication by twice a natural-number time radius. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimitProducts.lean#L154).

**A bounded test controls squared pairings** · theorem. `sq_inner_le`: A pointwise bound on the test vector bounds the squared pairing by that bound squared times the field norm squared. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimitProducts.lean#L157).

**An L2 bound for scalar test pairings** · theorem. `lintegral_inner_le`: A uniform test-vector bound controls the integral of the squared scalar pairing by the field's squared-norm integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimitProducts.lean#L164).

**An L2 bound for differences of pairings** · theorem. `lintegral_inner_sub_le`: A uniformly bounded test vector transfers an L2 field difference bound to the difference of scalar pairings. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimitProducts.lean#L173).

**Source namespace `Breakdown.Cert.Internal.HeldLimit`.**

**Local L2 limits preserve test products** · theorem. `scalar_product_integral_tendsto`: Strong local period-L2 convergence of both factors gives integrability and convergence of their compactly tested scalar-product integrals. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimitProducts.lean#L187).

### Breakdown.Cert.HeldLimitReadings

This file realizes velocity and gradient readings as bounded local L2 maps so compactness can be applied to their representatives. Section 7.8: strong local convergence of physical readings.

**Source namespace `Breakdown.Cert.Internal.HeldLimitReadings`.**

**Measure on a period and a spatial ball** · definition. `ballMeasure`: The ball measure restricts time to one unit period and space to the closed ball of the given radius. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimitReadings.lean#L14).

**Measurability on a bounded cylinder** · theorem. `aestronglyMeasurable_ball`: Almost everywhere strong measurability for space-time volume descends to the period-and-ball measure. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimitReadings.lean#L17).

**Iterated nullity gives product nullity** · theorem. `ae_prod_of_ae_ae`: Measurable fields equal almost everywhere in time and then in space are equal almost everywhere for the product measure. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimitReadings.lean#L22).

**Equality on a bounded cylinder** · theorem. `ae_ball`: Almost everywhere equality for the full product measure descends to the bounded period-and-ball cylinder. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimitReadings.lean#L39).

**Local period energy as one integral** · theorem. `periodBallLIntegral_eq`: The local period squared-norm integral equals the squared-norm integral for the ball measure. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimitReadings.lean#L47).

**Finite local energy gives local L2** · theorem. `memLp_of_lintegral`: A measurable field with finite local period squared-norm integral belongs to L2 for the ball measure. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimitReadings.lean#L57).

**A bounded linear family of local fields** · structure. `IsLocalFamily`: A local family is measurable, linear almost everywhere, and has local squared L2 norm bounded by a fixed multiple of the input norm squared. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimitReadings.lean#L68).

**A local family's fields lie in L2** · theorem. `memLp`: Every field in a bounded local family belongs to L2 on the period-and-ball cylinder. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimitReadings.lean#L79).

**The local representative's squared norm** · theorem. `ofReal_norm_sq`: The squared L2 norm of a local-family representative equals its local period energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimitReadings.lean#L83).

**The local family's operator bound** · theorem. `norm_le`: The norm of a local-family representative is at most the square root of its energy constant times the input norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimitReadings.lean#L90).

**The linear map of local representatives** · definition. `lin`: The almost everywhere linear local family defines a linear map into the local L2 space. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimitReadings.lean#L102).

**Evaluate the local linear map** · theorem. `lin_apply`: The local linear map sends an input to the L2 class of its selected local field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimitReadings.lean#L113).

**Bound the local linear map** · theorem. `lin_norm_le`: The local linear map satisfies the operator bound given by the square root of the family's energy constant. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimitReadings.lean#L116).

**The bounded map of local representatives** · definition. `clm`: The norm estimate turns the local-family map into a continuous linear map. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimitReadings.lean#L121).

**Evaluate the bounded local map** · theorem. `clm_apply`: The continuous local-family map has the same L2 value as the original representative construction. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimitReadings.lean#L124).

**The bounded map retains the field** · theorem. `clm_ae`: The representative of the continuous local map agrees almost everywhere with the original local-family field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimitReadings.lean#L128).

**Local distance as difference energy** · theorem. `ofReal_norm_sub_sq`: The squared L2 distance of two local-map values equals the period energy of the difference of their fields. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimitReadings.lean#L133).

**Local Cauchy and weak limits agree** · theorem. `tendsto_of_fundamental_weak`: If mapped images are Cauchy and the inputs converge weakly, the images converge strongly to the image of the weak limit. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimitReadings.lean#L144).

**Strong convergence of a local family** · theorem. `tendsto`: The local-family compactness and weak-limit hypotheses make the squared local difference energy tend to zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimitReadings.lean#L163).

**Addition of selected physical readings** · theorem. `add_ae`: Representatives of a linear image of a sum agree almost everywhere with the sum of the two selected representatives. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimitReadings.lean#L186).

**Scaling selected physical readings** · theorem. `smul_ae`: Representatives of a linear image of a scalar multiple agree almost everywhere with the scaled selected representative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimitReadings.lean#L208).

**Velocity readings form a local family** · theorem. `velocity_family`: The selected velocity readings form a bounded local family with the ball-volume constant used here. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimitReadings.lean#L228).

**Gradient columns form local families** · theorem. `column_family`: Each selected gradient column forms a bounded local family with energy constant one. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimitReadings.lean#L243).

**Source namespace `Breakdown.Cert.Internal.HeldLimit`.**

**Local L2 convergence of a reading** · proposition definition. `IsLocalReadingLimit`: A local reading limit requires finite velocity and gradient-column energies on every positive-radius ball and convergence of all corresponding squared differences to zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimitReadings.lean#L266).

**Convert graph limits to reading limits** · theorem. `isLocalReadingLimit_of`: The graph-space convergence hypotheses yield local L2 convergence of the selected velocity and gradient readings. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimitReadings.lean#L275).

**A subsequence of local reading limits** · theorem. `reading_tendsto_local`: The free-inverse compactness hypotheses supply a strictly increasing subsequence with the required local L2 reading limit. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldLimitReadings.lean#L292).

### Breakdown.Cert.HeldMapsTo

This file checks that a held update stays within the certified size and gradient bounds. Section 7.8: preservation of the set used for the contraction.

**Source namespace `Breakdown.Cert.Internal.HeldMapsTo`.**

**L2 norm from the squared representative** · theorem. `ofReal_sq_norm_Lp`: The squared L2 norm equals the nonnegative integral of the squared norm of its representative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldMapsTo.lean#L17).

**Energy of a represented periodic curve** · theorem. `periodLIntegral_curve`: A periodic field representing a Hilbert-valued curve has period energy equal to that curve's squared norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldMapsTo.lean#L25).

**Smooth dependence of spatial derivatives** · theorem. `Breakdown.Cert.HeldMapsTo.contDiff_fderiv_slice`: Sufficient joint smoothness gives the asserted joint smoothness of the spatial derivative map. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldMapsTo.lean#L39).

**The profile defect is measurable** · theorem. `aestronglyMeasurable_defectField`: The regularity hypotheses on the profile, pressure and actuator fields make the defect almost everywhere strongly measurable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldMapsTo.lean#L46).

**The profile defect is time periodic** · theorem. `defectField_periodic`: Periodic profile, pressure and actuator data give a time-periodic defect field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldMapsTo.lean#L84).

**The represented curve gives the norm** · theorem. `periodNorm_eq_of_curve`: The period norm of a field representing the curve equals the curve's Hilbert-space norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldMapsTo.lean#L97).

**Represent a negative field difference** · theorem. `curve_neg_sub`: The negative difference of the two represented curves represents the negative difference of their physical fields almost everywhere. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldMapsTo.lean#L104).

**Bounds for a negative field difference** · theorem. `neg_sub_periodic`: The negative difference of two periodic fields is periodic and its norm is bounded by the sum of their period norms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldMapsTo.lean#L120).

**Restrict a field to a spatial ball** · definition. `ballPart`: The ball part keeps a field on the closed spatial ball and sets it to zero outside. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldMapsTo.lean#L134).

**Local norm is a restricted field norm** · theorem. `periodBallNorm_eq`: The local period norm equals the period norm of the field restricted to the ball. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldMapsTo.lean#L137).

**Monotonicity of period norms** · theorem. `periodNorm_mono`: Pointwise domination of field norms gives domination of their finite period norms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldMapsTo.lean#L150).

**Ball restriction preserves periodicity** · theorem. `ballPart_periodic`: Restricting a periodic square-integrable field to a spatial ball preserves that property. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldMapsTo.lean#L156).

**Ball restriction preserves subtraction** · theorem. `ballPart_neg_sub`: Restricting a negative field difference to a ball gives the negative difference of the two restricted fields. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldMapsTo.lean#L174).

**The local norm obeys the triangle bound** · theorem. `periodBallNorm_neg_sub_le`: The local period norm of a negative difference is bounded by the sum of the two local period norms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldMapsTo.lean#L181).

**Local norm below global period norm** · theorem. `periodBallNorm_le_periodNorm`: The period norm over a spatial ball is bounded by the full period norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldMapsTo.lean#L187).

**A squared integral gives a norm bound** · theorem. `periodNorm_le_of`: A nonnegative scalar bound on the period squared-norm integral yields the corresponding period-norm bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldMapsTo.lean#L192).

**A local energy bound gives a local norm** · theorem. `periodBallNorm_le_of`: A nonnegative bound on the local period squared-norm integral yields the corresponding ball-period norm bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldMapsTo.lean#L199).

**The certified defect is a periodic field** · theorem. `defect_periodicField`: At a certified parameter, the profile defect with its specified multipliers is a periodic square-integrable field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldMapsTo.lean#L207).

**Weighted energy is nonnegative** · theorem. `Breakdown.Cert.HeldMapsTo.energyW_nonneg`: A nonnegative weight gives nonnegative weighted energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldMapsTo.lean#L218).

**Energy below combined state size** · theorem. `sqrt_energy_le_sizeZ`: The square root of the weighted energy is at most the combined correction-and-multiplier size. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldMapsTo.lean#L224).

**Multiplier norm below the combined size** · theorem. `Breakdown.Cert.HeldMapsTo.vecNorm_le_sizeZ`: For a nonnegative weight, the Euclidean multiplier norm is bounded by the combined size. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldMapsTo.lean#L228).

**A size bound gives an energy bound** · theorem. `energy_le_sq`: For a nonnegative weight, a bound on the combined size gives the squared bound on weighted energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldMapsTo.lean#L232).

**The chosen bordered inverse is valid** · theorem. `Breakdown.Cert.HeldMapsTo.borderedInv_spec`: When a bordered inverse exists, the selected inverse satisfies its defining specification. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldMapsTo.lean#L242).

**The pin part of the bordered map** · theorem. `Breakdown.Cert.HeldMapsTo.bordered_snd`: The finite-dimensional component of the bordered operator is the pin map of the free inverse. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldMapsTo.lean#L248).

**The updated size stays inside the ball** · theorem. `size_arith`: The scalar forcing and smallness inequalities bound the updated combined size by twice the certified size radius. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldMapsTo.lean#L253).

**The updated gradient stays bounded** · theorem. `sup_arith`: The scalar quadratic estimate and certificate inequalities bound the updated gradient supremum squared by the permitted radius squared. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldMapsTo.lean#L266).

**Both bounds for a held update** · theorem. `step_bounds`: Solving the bordered equation for admissible input gives both the required combined-size bound and the gradient-supremum bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldMapsTo.lean#L281).

**Source namespace `Breakdown.Cert`.**

**The held update preserves its domain** · theorem. `heldMapsToHolds_of`: The inverse, coercivity, product and data interfaces together imply that the held iteration maps its admissible set to itself. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldMapsTo.lean#L384).

### Breakdown.Cert.HeldMetric

This file proves closedness, norm control, triangle inequalities and limit stability for the held distance used in the fixed-point argument. Section 7.8: the metric needed by the contraction theorem.

**Source namespace `Breakdown.Cert.Internal.HeldMetric`.**

**The spatial energy measure** · definition. `weightedMeasure`: The spatial energy measure has density equal to the nonnegative part of the weight. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldMetric.lean#L16).

**Bound the weighted spatial measure** · theorem. `weightedMeasure_le`: A scalar upper bound on the weight bounds the weighted measure by the same multiple of volume. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldMetric.lean#L19).

**Ordinary L2 embeds in weighted L2** · theorem. `memLp_weightedMeasure`: A bounded nonnegative weight carries every ordinary L2 field into weighted L2. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldMetric.lean#L26).

**Volume null sets remain weighted null** · theorem. `ae_weightedMeasure`: Any statement holding almost everywhere for volume also holds almost everywhere for the weighted measure. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldMetric.lean#L30).

**Embed a field into weighted L2** · definition. `weightedEmbed`: The weighted embedding sends a field to its equivalence class for the weighted L2 measure. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldMetric.lean#L34).

**Bound the weighted L2 embedding** · theorem. `weightedEmbed_norm_le`: The norm of the weighted embedding is bounded by the square root of the weight's upper bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldMetric.lean#L44).

**The bounded weighted embedding** · definition. `weightedEmbedL`: The weighted embedding and its norm estimate define a continuous linear map. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldMetric.lean#L54).

**Weighted embedding norm as an integral** · theorem. `weightedEmbedL_norm_sq`: The squared weighted-embedding norm equals the integral of the weight times the field's squared norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldMetric.lean#L58).

**Weighted square integrability** · theorem. `integrable_weight_mul_sq`: A bounded nonnegative weight makes the squared norm of an L2 field integrable after weighting. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldMetric.lean#L70).

**Weighted energy splits by coordinates** · theorem. `sliceWeightedGrad_eq_sum`: The weighted slice gradient energy is the sum of the three squared weighted derivative norms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldMetric.lean#L78).

**One weighted gradient column** · definition. `weightedColumn`: The weighted-column map extracts one derivative of a graph pair's gradient part and embeds it into weighted L2. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldMetric.lean#L86).

**Slice energy from lifted columns** · theorem. `slice_ae_eq`: The slice energy agrees almost everywhere in time with the sum of the squared norms of the lifted weighted columns. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldMetric.lean#L90).

**The time-dependent slice energy is L1** · theorem. `integrable_slice`: The weighted slice gradient energy of a graph correction is integrable in time. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldMetric.lean#L100).

**Integrated slice energy as L2 norms** · theorem. `integral_slice_eq`: Integrating the weighted slice energy gives the sum of the squared time-L2 weighted-column norms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldMetric.lean#L107).

**The weighted gradient norm** · definition. `weightedNorm`: The weighted norm is the square root of the sum of the three squared lifted weighted-column norms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldMetric.lean#L116).

**Combined size as one quadratic sum** · theorem. `sizeZ_eq_sum`: The combined size is the square root of the second-part energy, the weighted column energies and the multiplier coordinate squares. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldMetric.lean#L119).

**Three components of the combined size** · theorem. `sizeZ_eq_three`: The combined size is the Euclidean combination of second-part norm, weighted gradient norm and multiplier norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldMetric.lean#L125).

**The combined size is continuous** · theorem. `continuous_sizeZ`: For the admissible bounded weight, the combined correction-and-multiplier size is continuous. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldMetric.lean#L134).

**Triangle inequality for squared sums** · theorem. `sqrt_sum_sq_le`: Coordinatewise triangle bounds imply the triangle inequality for the square root of a sum of squares. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldMetric.lean#L139).

**Triangle inequality for three components** · theorem. `sqrt_three_le`: Bounds on three nonnegative components give the corresponding Euclidean triangle inequality. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldMetric.lean#L158).

**The weighted gradient triangle bound** · theorem. `weightedNorm_add_le`: The weighted gradient norm of a sum is at most the sum of the weighted gradient norms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldMetric.lean#L174).

**The multiplier triangle inequality** · theorem. `vecNorm_add_le`: The Euclidean norm of a sum of multiplier vectors is at most the sum of their norms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldMetric.lean#L180).

**The combined-size triangle inequality** · theorem. `sizeZ_add_le`: The combined size of a sum of states is at most the sum of their combined sizes. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldMetric.lean#L183).

**The weight controls unweighted energy** · theorem. `Breakdown.Cert.HeldMetric.sliceWeightedGrad_ge`: A positive lower bound on the weight bounds the weighted slice energy below by that constant times the squared energy-space norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldMetric.lean#L195).

**Integrate a constant gradient weight** · theorem. `integral_gradSq_const_mul`: The time integral of a constant times the squared slice gradient norm equals that constant times the squared gradient-map norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldMetric.lean#L203).

**Integrate the lower weight bound** · theorem. `integral_slice_ge`: The lower weight bound persists after integration of the slice gradient energy in time. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldMetric.lean#L207).

**Weighted bounds for both graph parts** · theorem. `energyW_ge`: The weighted energy bounds below the second-part norm squared plus the lower weight constant times the gradient norm squared. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldMetric.lean#L215).

**The correction norm splits by graph part** · theorem. `Breakdown.Cert.HeldMetric.norm_sq_xx`: The squared correction norm equals the sum of its squared gradient and second-part norms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldMetric.lean#L220).

**The function norm below Euclidean norm** · theorem. `Breakdown.Cert.HeldMetric.norm_le_vecNorm`: The norm of the finite coordinate function is bounded by its Euclidean norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldMetric.lean#L231).

**Combined size controls the ambient norm** · theorem. `sizeZ_lower`: The combined size bounds the ambient state norm after multiplication by the square root of the smaller of one and the positive weight lower bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldMetric.lean#L237).

**Symmetry constraints form a closed set** · theorem. `isClosed_invariant`: The invariant Hilbert subspace associated with the chosen symmetries is closed. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldMetric.lean#L274).

**The gradient supremum as an L∞ norm** · theorem. `Breakdown.Cert.HeldMetric.supGrad_eq_eLpNorm`: The gradient supremum is the extended L∞ norm of the graph-space gradient map. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldMetric.lean#L294).

**Gradient supremum of a sum** · theorem. `supGrad_add_le`: The gradient supremum of a sum is bounded by the sum of the gradient suprema. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldMetric.lean#L302).

**Gradient supremum of a difference** · theorem. `supGrad_sub_le`: The gradient supremum of a difference is bounded by the sum of the two gradient suprema. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldMetric.lean#L312).

**Differences have finite gradient bounds** · theorem. `supGrad_sub_ne_top`: Finite gradient suprema for two corrections imply that their difference has a finite gradient supremum. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldMetric.lean#L322).

**Limit retains the metric supremum bound** · theorem. `sup_part_le`: The assumed convergence and uniform supremum estimate give the same scaled supremum bound for the limit. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldMetric.lean#L327).

**The certificate weight is admissible** · theorem. `admissible`: The certificate conditions make the supplied weight admissible with the specified positive lower bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldMetric.lean#L341).

**Source namespace `Breakdown.Cert`.**

**Prove the held-distance properties** · theorem. `heldMetricHolds_of`: The weighted-energy and supremum constructions prove the closedness, Hilbert-norm lower bound, triangle inequality and limit property packaged by the held-distance interface. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldMetric.lean#L348).

### Breakdown.Cert.HeldNonzero

This file uses the certificate lower bound on the approximate profile to rule out cancellation by the small correction. Section 7.8: nonvanishing of the corrected weak profile.

**Source namespace `Breakdown.Cert.Internal.HeldNonzero`.**

**A smooth derivative is a weak gradient** · theorem. `Breakdown.Cert.HeldNonzero.isWeakGradient_of_contDiff`: A continuously differentiable field has its classical derivative as a weak gradient. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldNonzero.lean#L15).

**Equal weak gradients have equal energy** · theorem. `periodLIntegral_matSq_eq`: The weak-gradient identification equates the period integrals of the two gradient squared norms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldNonzero.lean#L30).

**The positive weight controls gradients** · theorem. `weighted_lower`: The positive lower weight bound controls the period gradient energy by the full weighted physical energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldNonzero.lean#L52).

**The physical weighted energy is finite** · theorem. `weighted_ne_top`: A valid graph reading with the stated energy bounds has finite period weighted physical energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldNonzero.lean#L67).

**The profile bound forbids cancellation** · theorem. `arith_contra`: The strict profile lower bound and the smaller correction upper bound contradict complete cancellation. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldNonzero.lean#L134).

**Source namespace `Breakdown.Cert`.**

**The corrected held profile is nonzero** · theorem. `heldNonzeroHolds_of`: The reading, energy and slice interfaces turn the certificate gap into nonvanishing of the corrected held profile. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldNonzero.lean#L142).

### Breakdown.Cert.HeldWeakEquation

This file expands the weak equation for the approximate profile plus its held correction and cancels the actuator forcing when the total multiplier vanishes. Section 7.8: export of the nonlinear weak profile.

**Source namespace `Breakdown.Cert.Internal.HeldWeakEquation`.**

**The transported similarity test** · definition. `transportTest`: The transported test combines the time derivative, the test itself and the radial derivative with the similarity-equation coefficients. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldWeakEquation.lean#L21).

**The approximate-profile weak integrand** · definition. `barPart`: The background part is the similarity weak integrand evaluated at the approximate profile and its classical gradient. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldWeakEquation.lean#L24).

**The linear correction integrand** · definition. `linPart`: The linear part pairs the correction with the transported test and its gradient with the test gradient. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldWeakEquation.lean#L27).

**The mixed nonlinear integrand** · definition. `crossPart`: The mixed part contains the two advection pairings involving one approximate-profile factor and one correction factor. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldWeakEquation.lean#L30).

**The quadratic correction integrand** · definition. `quadPart`: The quadratic part is the negative test-gradient pairing of the correction with its own advective product. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldWeakEquation.lean#L34).

**Split the corrected weak integrand** · theorem. `integrand_split`: The weak integrand of the corrected profile is the sum of the background, linear, mixed and quadratic parts. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldWeakEquation.lean#L37).

**Separate the actuator contribution** · theorem. `defect_split`: The defect with a multiplier equals the zero-multiplier defect plus the corresponding actuator combination. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldWeakEquation.lean#L46).

**Spatial derivatives of a joint test** · theorem. `slice_fderiv_eq_joint`: The spatial derivative of a test slice is the joint derivative restricted to the spatial coordinate inclusion. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldWeakEquation.lean#L52).

**Time derivatives of a joint test** · theorem. `slice_deriv_eq_joint`: The time derivative of a test slice is the joint derivative applied to the unit time direction. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldWeakEquation.lean#L60).

**Spatial test derivatives remain compact** · theorem. `test_fderiv`: A space-time test field has a continuous, compactly supported spatial derivative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldWeakEquation.lean#L68).

**Time test derivatives remain compact** · theorem. `test_deriv`: A space-time test field has a continuous, compactly supported time derivative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldWeakEquation.lean#L80).

**A local L2 bound for velocity slices** · theorem. `velocity_slice_bound`: Almost every velocity slice has its ball-L2 energy bounded by the velocity-embedding norm, the gradient supremum and the ball volume. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldWeakEquation.lean#L92).

**Velocity has local space-time L2 energy** · theorem. `velocity_box_sq`: A valid reading with finite gradient supremum has integrable squared velocity on every bounded time-and-space cylinder. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldWeakEquation.lean#L138).

**Local velocity and quadratic pairings** · theorem. `velocity_local`: Against a continuous compactly supported test, the velocity pairing and its coordinate-weighted quadratic pairings are integrable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldWeakEquation.lean#L167).

**Compact support fits in a time slab** · theorem. `support_subset_box`: A compactly supported space-time function vanishes outside some bounded symmetric time slab. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldWeakEquation.lean#L228).

**Bound a pairing inside its time support** · theorem. `pairing_bound_box`: The test support permits a pairing bound by the field's squared norm on the time slab plus the test's squared norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldWeakEquation.lean#L241).

**Periodic fields can be tested compactly** · theorem. `pairing_integrable`: A periodic square-integrable field has an integrable pairing with any continuous compactly supported test. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldWeakEquation.lean#L254).

**Certified actuators are periodic fields** · theorem. `actuator_periodic`: Each certified actuator is a periodic square-integrable field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldWeakEquation.lean#L273).

**Test finite actuator combinations** · theorem. `actuator_integrable`: A finite linear combination of certified actuators has an integrable pairing with a space-time test field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldWeakEquation.lean#L280).

**Perturbation columns are periodic** · theorem. `column_periodic`: Each gradient column of a valid perturbation is a periodic square-integrable field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldWeakEquation.lean#L293).

**The linear weak terms are integrable** · theorem. `lin_integrable`: A valid bounded-gradient reading and perturbation give integrability of the transport, gradient and forcing test pairings. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldWeakEquation.lean#L304).

**Spatial differentiation by inclusion** · theorem. `bar_inr`: For a differentiable joint function, differentiating a spatial slice equals differentiating in the corresponding joint spatial direction. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldWeakEquation.lean#L329).

**Time differentiation by inclusion** · theorem. `bar_inl`: For a differentiable joint function, differentiating the time slice equals differentiating in the joint unit time direction. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldWeakEquation.lean#L338).

**A compact factor gives compact pairing** · theorem. `bar_cst_inner_right`: Pairing any field with a compactly supported field gives a compactly supported scalar function. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldWeakEquation.lean#L346).

**A product-rule flux** · definition. `barFlux`: The auxiliary flux is the sum of the two terms in the derivative of a field-test inner product. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldWeakEquation.lean#L354).

**The product-rule flux integrates to zero** · theorem. `bar_parts_zero`: Under the derivative and compact-test hypotheses, the product-rule flux is integrable and its full-space integral vanishes. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldWeakEquation.lean#L357).

**Differentiate a radial coordinate factor** · theorem. `bar_deriv_Y`: Differentiating a coordinate times the profile gives the profile plus that coordinate times its directional derivative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldWeakEquation.lean#L390).

**Differentiate a quadratic profile factor** · theorem. `bar_deriv_A`: The derivative of a profile coordinate times the profile splits into the two product-rule terms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldWeakEquation.lean#L406).

**Smoothness of each profile slice** · theorem. `bar_slice_contDiff`: Joint smoothness of the profile implies the same smoothness for every spatial time slice. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldWeakEquation.lean#L421).

**Identify the spatial derivative column** · theorem. `bar_L_eq`: A profile's spatial derivative column equals its joint derivative in the corresponding spatial direction. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldWeakEquation.lean#L425).

**Profile derivative columns are C1** · theorem. `bar_L_contDiff`: A jointly C2 profile has jointly C1 spatial derivative columns. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldWeakEquation.lean#L430).

**Recover the second derivative** · theorem. `bar_deriv_L`: The directional derivative of a profile derivative column equals the corresponding repeated second derivative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldWeakEquation.lean#L435).

**Differentiate a pressure-direction field** · theorem. `bar_deriv_Q`: The spatial derivative of pressure times a coordinate basis vector is the directional pressure derivative times that vector. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldWeakEquation.lean#L447).

**Read a coordinate by inner product** · theorem. `bar_inner_unit`: Pairing a coordinate basis vector with a spatial vector returns the corresponding coordinate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldWeakEquation.lean#L454).

**The time integration-by-parts flux** · definition. `barT`: The time flux combines the profile's and the test's time derivatives through the product rule. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldWeakEquation.lean#L457).

**The radial integration-by-parts flux** · definition. `barY`: The radial flux uses a coordinate-weighted profile and its spatial derivative in the product rule. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldWeakEquation.lean#L461).

**The diffusion integration-by-parts flux** · definition. `barL`: The diffusion flux pairs a spatial profile derivative and its repeated derivative with the test and test derivative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldWeakEquation.lean#L466).

**The advection integration-by-parts flux** · definition. `barA`: The advection flux applies the product rule to a profile coordinate multiplied by the profile. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldWeakEquation.lean#L471).

**The pressure integration-by-parts flux** · definition. `barQ`: The pressure flux applies the product rule to pressure times a coordinate basis vector. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldWeakEquation.lean#L477).

**Combine the spatial flux terms** · definition. `barE`: The combined spatial flux uses the radial, diffusion, advection and pressure fluxes with their equation coefficients. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldWeakEquation.lean#L482).

**Split the background integrand** · theorem. `bar_pointwise`: For divergence-free profile and test, the background weak integrand equals the defect pairing plus time and spatial flux terms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldWeakEquation.lean#L486).

**The time flux has zero integral** · theorem. `bar_T_zero`: The smooth profile and compact test make the time flux integrable with zero integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldWeakEquation.lean#L505).

**The spatial flux has zero integral** · theorem. `bar_E_zero`: The profile, pressure and compact-test regularity make each combined spatial flux integrable with zero integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldWeakEquation.lean#L513).

**Expand the zero-multiplier defect** · theorem. `bar_S_eq`: The zero-multiplier defect expands into time, linear, radial, diffusion, advection and pressure derivatives of the approximate profile. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldWeakEquation.lean#L542).

**The zero-multiplier defect is continuous** · theorem. `bar_S_continuous`: The profile and pressure regularity hypotheses make the zero-multiplier defect continuous in space-time. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldWeakEquation.lean#L567).

**The background equation tests the defect** · theorem. `bar_identity_general`: For a smooth divergence-free profile, the background weak integral equals the integral pairing with its zero-multiplier defect. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldWeakEquation.lean#L589).

**The certified background defect identity** · theorem. `bar_identity`: At a certified parameter, the approximate-profile weak integral equals its zero-multiplier defect paired with the test. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldWeakEquation.lean#L617).

**Read a coordinate from the right** · theorem. `cross_inner_unit`: Pairing a spatial vector with a coordinate basis vector gives the corresponding coordinate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldWeakEquation.lean#L630).

**A test for the mixed advection terms** · definition. `crossTest`: The mixed test combines profile-coordinate multiples of test derivatives with profile-derivative pairings along coordinate vectors. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldWeakEquation.lean#L633).

**Write the mixed term as a pairing** · theorem. `cross_eq_inner`: The mixed weak integrand is the negative inner product of the correction with the mixed test. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldWeakEquation.lean#L637).

**The mixed weak integrand is integrable** · theorem. `cross_integrable`: Certified profile data and a finite-gradient reading make the mixed weak integrand integrable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldWeakEquation.lean#L643).

**Mixed convection pairing is integrable** · theorem. `cross_conv_integrable`: The physical mixed convection expression has an integrable pairing with a space-time test field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldWeakEquation.lean#L667).

**Expand the quadratic weak pairing** · theorem. `cross_pair_expand`: The weak quadratic pairing of a sum expands into its two pure terms and two mixed terms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldWeakEquation.lean#L685).

**Expand the derivative trilinear form** · theorem. `cross_tri_expand`: The derivative trilinear form of two sums expands into the four pairwise contributions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldWeakEquation.lean#L691).

**A derivative trilinear integrand** · definition. `crossTri`: The auxiliary trilinear integrand sums velocity coordinates times gradient-column pairings with the test. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldWeakEquation.lean#L699).

**Polarize integration by parts** · theorem. `cross_polarize_gen`: The pure and sum integration-by-parts identities yield the identity for the two mixed weak pairings. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldWeakEquation.lean#L703).

**Mixed weak pairings from trilinear forms** · theorem. `cross_polarize`: For energy-space velocities and a divergence-free test, the sum of mixed weak pairings is the negative sum of the two trilinear forms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldWeakEquation.lean#L742).

**The approximate profile is a weak slice** · theorem. `cross_isSlice`: Each certified approximate-profile time slice satisfies the weak-slice regularity conditions with some bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldWeakEquation.lean#L768).

**Embed each approximate-profile slice** · theorem. `cross_profile_embed`: Every certified profile slice has an energy-space representative whose velocity and derivative columns agree almost everywhere with the physical profile. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldWeakEquation.lean#L827).

**Identify the mixed weak pairing** · theorem. `cross_slice_left`: Matching physical representatives rewrites the mixed integrand as the negative sum of the two weak pair forms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldWeakEquation.lean#L839).

**Expand the physical mixed convection** · theorem. `cross_slice_right`: Matching velocity and gradient representatives rewrites the physical mixed convection pairing as the two coordinate trilinear sums. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldWeakEquation.lean#L846).

**The mixed identity holds on time slices** · theorem. `cross_slice`: For almost every time, the spatial mixed weak integral equals the spatial mixed convection pairing. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldWeakEquation.lean#L855).

**The full mixed convection identity** · theorem. `cross_identity`: The integrable mixed weak term has full space-time integral equal to the physical mixed convection pairing. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldWeakEquation.lean#L900).

**A space-time test gives spatial tests** · theorem. `quad_slice_test`: Each time slice of a space-time test field is a valid spatial test field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldWeakEquation.lean#L914).

**A test derivative column stays compact** · theorem. `quad_column`: Each spatial derivative column of a space-time test is continuous and compactly supported. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldWeakEquation.lean#L920).

**Canonical correction reading is valid** · theorem. `quad_reading`: The chosen physical representatives form a valid reading of the correction. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldWeakEquation.lean#L927).

**The constant unit weight is admissible** · theorem. `quad_weight`: The constant weight one is admissible with lower bound one. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldWeakEquation.lean#L936).

**Expand a quadratic directional pairing** · theorem. `quad_point`: Matching vector coordinates and matrix columns gives the coordinate expansion of the tested directional derivative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldWeakEquation.lean#L939).

**The quadratic identity holds by slices** · theorem. `quad_slice`: For almost every time, the quadratic weak integral equals the physical quadratic product paired with the test. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldWeakEquation.lean#L946).

**The full quadratic product identity** · theorem. `quad_identity`: The product bound and finite-gradient reading make the quadratic weak term integrable and identify its full integral with the physical product pairing. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldWeakEquation.lean#L969).

**Source namespace `Breakdown.Cert`.**

**Held solution gives the weak equation** · theorem. `heldWeakEquationHolds_of`: The free-equation, convection, data and product-pairing interfaces supply the held weak-equation interface. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/HeldWeakEquation.lean#L996).

### Breakdown.Cert.Invariance

This file proves that the free, convection, product, actuator and defect constructions respect the prescribed space-time symmetries. Section 7: symmetry reduction of the bordered correction equation.

**Source namespace `Breakdown.Cert.Internal.Invariance`.**

**Return from a circle representative** · theorem. `coe_circleRep`: The real representative of a time-circle point maps back to that point. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Invariance.lean#L19).

**Equal circle times give equal values** · theorem. `periodic_eq`: A one-periodic function has equal values at real times representing the same circle point. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Invariance.lean#L22).

**Shift a periodic circle representative** · theorem. `periodic_shift`: Evaluating a periodic function at the representative of a shifted circle point agrees with shifting its real representative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Invariance.lean#L32).

**Periodic values descend to the circle** · theorem. `periodic_coe`: Evaluating a periodic function after choosing the circle representative leaves its value unchanged. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Invariance.lean#L36).

**Recognize an invariant Hilbert field** · theorem. `mem_invariantHH_of`: The prescribed shift-equals-rotation identities imply membership in the invariant Hilbert subspace. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Invariance.lean#L40).

**An invariant field obeys each symmetry** · theorem. `shift_of_mem`: Membership in the invariant subspace gives the shift-equals-rotation identity for every allowed symmetry. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Invariance.lean#L45).

**Represent a time shift pointwise** · theorem. `shift_coe`: The L2 representative of a time shift equals the shifted original representative almost everywhere. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Invariance.lean#L50).

**Represent a spatial rotation pointwise** · theorem. `rot_coe`: The representative of a rotated Hilbert curve equals the slice-wise rotation almost everywhere. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Invariance.lean#L58).

**Time shifts preserve null sets** · theorem. `ae_shift`: An almost everywhere statement on the time circle remains true after any time shift. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Invariance.lean#L62).

**Lift a pointwise symmetry to L2** · theorem. `shift_eq_rot_of_ae`: An almost everywhere shift-rotation identity of representatives gives equality of the corresponding Hilbert-space elements. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Invariance.lean#L66).

**Read an L2 symmetry pointwise** · theorem. `ae_of_shift_eq`: A shift-rotation equality in the Hilbert space gives the corresponding representative identity almost everywhere in time. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Invariance.lean#L74).

**Symmetry of the chosen circle curve** · theorem. `circleLpOrZero_shift`: A pointwise shift-rotation identity is preserved by the circle-L2 construction, including its zero fallback. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Invariance.lean#L81).

**Symmetry of graph gradient slices** · theorem. `grad_shift`: An invariant graph correction has gradient slices related by the prescribed shift and rotation almost everywhere. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Invariance.lean#L98).

**Undo a spatial push-forward** · theorem. `pushForward_symm`: Pushing a field forward by an isometry and then its inverse recovers the field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Invariance.lean#L107).

**Rotations preserve spatial L2** · theorem. `memLp_pushForward`: An isometric spatial push-forward preserves membership in L2. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Invariance.lean#L112).

**The solenoidal reading respects equality** · theorem. `Breakdown.Cert.Invariance.solField_congr`: Almost everywhere equal fields have equal solenoidal Hilbert-space readings. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Invariance.lean#L117).

**The solenoidal reading is subtractive** · theorem. `solField_sub`: The solenoidal reading of a difference of L2 fields equals the difference of their readings. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Invariance.lean#L125).

**Undo a Hilbert-space rotation** · theorem. `rotX_rotX_symm`: Rotating an energy-space element by an inverse isometry and then the isometry returns the original element. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Invariance.lean#L130).

**Projection commutes with rotation** · theorem. `solField_pushForward`: The solenoidal reading of a pushed-forward L2 field is the rotation of its original reading. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Invariance.lean#L135).

**Rotations preserve coordinate pairings** · theorem. `sum_coord_rot`: The coordinate sum pairing two rotated vectors recovers the corresponding original coordinate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Invariance.lean#L193).

**Rotate a coordinate contraction** · theorem. `rot_sum`: A simultaneous rotation of vector coordinates and derivative columns rotates their contracted sum. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Invariance.lean#L202).

**Derivative of a pushed-forward field** · theorem. `fderiv_pushForward`: The derivative of a pushed-forward field is its original derivative conjugated by the spatial isometry. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Invariance.lean#L210).

**Convection respects spatial rotation** · theorem. `sliceConvection_pushForward`: Slice convection of a pushed-forward profile and rotated perturbation equals the pushed-forward original convection almost everywhere. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Invariance.lean#L225).

**The quadratic slice respects rotation** · theorem. `productSlice_rot`: Rotating both inputs of the product slice gives the spatial push-forward of the original product almost everywhere. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Invariance.lean#L238).

**The chosen convection map is valid** · theorem. `convectionSpec_of`: When the convection specification is realizable, the selected convection map satisfies it. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Invariance.lean#L246).

**Profile obeys the prescribed symmetry** · theorem. `profile_shift`: At a certified parameter, shifting the profile time equals pushing the profile forward by the paired spatial symmetry. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Invariance.lean#L252).

**Certified profile slices are C2** · theorem. `profile_contDiff`: Every time slice of a certified approximate profile is twice continuously differentiable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Invariance.lean#L259).

**Convection preserves the invariant space** · theorem. `convection_mem`: Convection at the certified profile sends an invariant correction to an invariant Hilbert-space field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Invariance.lean#L263).

**The self-product preserves invariance** · theorem. `productH_mem`: The quadratic product of an invariant correction belongs to the same invariant Hilbert subspace. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Invariance.lean#L278).

**Physical symmetry passes to the curve** · theorem. `physToHH_shift`: The physical-to-Hilbert construction carries a shift-rotation field identity to the same identity for its curve. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Invariance.lean#L286).

**Project an almost everywhere symmetry** · theorem. `solField_shift_of_ae`: An almost everywhere physical shift-rotation identity gives the corresponding identity of projected slices for almost every time. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Invariance.lean#L302).

**The actuator map is a finite sum** · theorem. `actuatorH_apply`: The abstract actuator map is the multiplier-weighted sum of its actuator slices. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Invariance.lean#L312).

**Actuator combinations preserve symmetry** · theorem. `actuatorH_mem`: Every finite multiplier combination of certified actuators lies in the prescribed invariant subspace. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Invariance.lean#L316).

**The profile equation without pressure** · definition. `profilePart`: The profile part collects time, linear, radial, diffusion and nonlinear advection terms before pressure and actuators are added. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Invariance.lean#L324).

**Split the defect into three parts** · theorem. `defectField_eq`: The defect is the sum of the pressure-free profile part, the actuator combination and the pressure gradient. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Invariance.lean#L328).

**Expand a vector in the standard basis** · theorem. `vec_eq_sum`: Every spatial vector is the sum of its coordinates times the standard basis vectors. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Invariance.lean#L333).

**Represent a linear scalar functional** · theorem. `apply_eq_inner`: A real linear functional on space equals pairing with the vector formed from its coordinate-direction values. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Invariance.lean#L337).

**Pressure gradients respect rotations** · theorem. `gradientAt_pushForward`: The gradient of pressure composed with the inverse isometry is the rotated original pressure gradient. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Invariance.lean#L344).

**The Laplacian respects rotations** · theorem. `sumSecondPartialsAt_pushForward`: The sum of second spatial partials of a pushed-forward field is the rotation of the original sum. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Invariance.lean#L362).

**Test coordinates have compact support** · theorem. `coord_hasCompactSupport`: Every coordinate of a compactly supported vector test has compact support. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Invariance.lean#L389).

**Test coordinates are smooth** · theorem. `coord_contDiff`: Every coordinate of a smooth vector test is smooth. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Invariance.lean#L393).

**Differentiate one test coordinate** · theorem. `coord_fderiv`: The derivative of a coordinate function is the corresponding coordinate of the vector derivative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Invariance.lean#L397).

**A compact smooth factor is integrable** · theorem. `integrable_mul_of_compact`: A continuous product with the specified compact support is integrable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Invariance.lean#L406).

**Expand a gradient pairing** · theorem. `inner_gradientAt`: The inner product with a scalar gradient is the sum of its directional derivatives times the vector coordinates. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Invariance.lean#L415).

**Pressure gradients vanish against tests** · theorem. `integral_gradient_test`: A sufficiently regular scalar gradient has zero integral pairing with a compact divergence-free test. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Invariance.lean#L420).

**Projection removes a gradient field** · theorem. `solField_gradientAt`: An integrable gradient field satisfying the regularity hypotheses has zero solenoidal reading. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Invariance.lean#L455).

**Pressure gradient preserves subtraction** · theorem. `gradientAt_sub`: The gradient of a differentiable scalar difference is the difference of the two gradients. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Invariance.lean#L462).

**Time derivatives retain profile symmetry** · theorem. `deriv_shift`: The time derivative of the certified profile obeys the same coupled time-shift and spatial-rotation identity. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Invariance.lean#L468).

**Pressure-free defect retains symmetry** · theorem. `profilePart_shift`: The pressure-free profile equation transforms by the prescribed space-time symmetry. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Invariance.lean#L483).

**The full certified defect is periodic** · theorem. `defect_periodic`: The certified profile, pressure and actuator data give a time-periodic defect field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Invariance.lean#L494).

**Smooth dependence of spatial derivatives** · theorem. `Breakdown.Cert.Invariance.contDiff_fderiv_slice`: Sufficient joint smoothness gives the asserted joint smoothness of the spatial derivative map. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Invariance.lean#L507).

**The pressure-free defect is continuous** · theorem. `continuous_profilePart`: The profile regularity assumptions make its pressure-free equation residual jointly continuous. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Invariance.lean#L514).

**Pressure gradients vary continuously** · theorem. `continuous_gradientAt_slice`: Joint pressure regularity gives continuity of the spatial pressure gradient in space-time. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Invariance.lean#L538).

**The defect is L2 at almost every time** · theorem. `defect_memLp_ae`: The certified defect belongs to spatial L2 for almost every time slice. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Invariance.lean#L546).

**The projected defect obeys symmetry** · theorem. `defect_shift`: After solenoidal projection, the certified defect satisfies the prescribed shift-rotation identity almost everywhere in time. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Invariance.lean#L565).

**Source namespace `Breakdown.Cert`.**

**Assemble invariance of the certificate** · theorem. `invarianceHolds_of`: Projection, convection and physical-data identities establish all invariance clauses for the certificate operators. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Invariance.lean#L615).

### Breakdown.Cert.JointRepresentative

This file moves between L2-valued time curves and jointly measurable periodic fields without choosing representatives independently on each slice. Section 7: physical readings of the abstract correction spaces.

**Source namespace `Breakdown.Cert`.**

**One is a positive period** · instance. `zero_lt_one_fact`: The local instance supplies positivity of the unit period. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/JointRepresentative.lean#L11).

**Source namespace `Breakdown.Cert.JointRepresentativeInternal`.**

**Simple curve has a joint representative** · theorem. `simpleSlice_stronglyMeasurable`: Evaluating the Lp-valued simple curve on its spatial variable gives a strongly measurable joint field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/JointRepresentative.lean#L17).

**A geometric-series coefficient** · theorem. `two_mul_inv_four`: Twice the reciprocal of four equals the reciprocal of two in the extended nonnegative reals. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/JointRepresentative.lean#L35).

**The geometric error sum is finite** · theorem. `tsum_inv_two_pow_ne_top`: The sum of powers of one half is finite in the extended nonnegative reals. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/JointRepresentative.lean#L39).

**Control a geometric approximation error** · theorem. `le_mul_inv_two_pow`: The stated scalar inequality bounds the approximation error by the geometric factor used in the representative construction. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/JointRepresentative.lean#L43).

**A measurable curve has a joint reading** · theorem. `joint_of_stronglyMeasurable`: A strongly measurable Lp-valued curve admits a jointly strongly measurable field agreeing with its slices almost everywhere. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/JointRepresentative.lean#L50).

**An integrable curve has a joint reading** · theorem. `joint_of_memLp_one`: An integrable Lp-valued curve admits a jointly strongly measurable representative with almost everywhere slice agreement. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/JointRepresentative.lean#L128).

**Lift circle null-set statements to time** · theorem. `ae_coe_of_ae`: An almost everywhere statement on the unit time circle holds for almost every real representative time. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/JointRepresentative.lean#L138).

**Recover measurability from distances** · theorem. `measurable_of_dist_dense`: Measurability of distances to a countable dense family implies measurability of the target-valued function. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/JointRepresentative.lean#L145).

**Square the extended L2 norm** · theorem. `sq_eLpNorm_two`: The square of the extended L2 norm equals the integral of the squared extended pointwise norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/JointRepresentative.lean#L169).

**The slice L2 norm is measurable** · theorem. `measurable_eLpNorm_two_slice`: For a measurable joint field, its extended spatial L2 norm varies measurably with the first variable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/JointRepresentative.lean#L175).

**Build an L2 curve from a joint field** · theorem. `curve_of_joint`: A jointly measurable field with finite iterated squared norm defines an L2-valued L2 curve with the matching norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/JointRepresentative.lean#L185).

**Equal circle times give periodic values** · theorem. `periodic_of_coe_eq`: A field factoring through the time circle takes equal values at real times with the same circle class. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/JointRepresentative.lean#L247).

**Source namespace `Breakdown.Cert`.**

**A periodic joint representative exists** · theorem. `exists_joint_representative`: Every L2 curve on the unit time circle has a jointly measurable, exactly periodic physical representative agreeing almost everywhere with its slices. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/JointRepresentative.lean#L260).

**A periodic field defines an L2 curve** · theorem. `exists_curve_of_joint`: A measurable periodic field with finite period energy defines an L2 curve whose squared norm is that period energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/JointRepresentative.lean#L274).

### Breakdown.Cert.LocalCompactness

This file extracts subsequences whose velocity and gradient readings are Cauchy on every fixed spatial ball. Section 7.8: local compactness of bounded free-inverse images.

**Canonical reading satisfies its contract** · theorem. `reading_spec`: The canonical velocity, gradient and Hessian fields satisfy the graph correction's physical-reading specification. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/LocalCompactness.lean#L18).

**A squared L2 norm is an integral** · theorem. `Breakdown.Cert.LocalCompactness.norm_sq_eq_integral`: The squared norm of an L2 curve equals the integral of its pointwise squared norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/LocalCompactness.lean#L27).

**The nonnegative squared-norm integral** · theorem. `lintegral_norm_sq`: The nonnegative integral of a representative's squared norm equals its L2 norm squared as an extended nonnegative real. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/LocalCompactness.lean#L35).

**The gradient map agrees with its slices** · theorem. `gradCLM_ae`: The represented gradient map equals the gradient part of the graph curve almost everywhere in time. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/LocalCompactness.lean#L42).

**The second map agrees with its slices** · theorem. `secondCLM_ae`: The represented second-part map equals the second part of the graph curve almost everywhere in time. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/LocalCompactness.lean#L47).

**The correction norm splits by graph part** · theorem. `Breakdown.Cert.LocalCompactness.norm_sq_xx`: The squared correction norm equals the sum of its squared gradient and second-part norms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/LocalCompactness.lean#L52).

**Separate the free-energy bounds** · theorem. `real_bounds'`: The scalar free-energy inequalities give the separate gradient and second-part bounds and a total squared-norm bound with factor five. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/LocalCompactness.lean#L73).

**A component is bounded by total energy** · theorem. `real_le_of_sq`: A nonnegative component of a sum-of-squares bound is at most the total norm bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/LocalCompactness.lean#L81).

**Uniform bounds for the free inverse** · theorem. `norm_le_of_free`: The free inverse has gradient norm at most twice the forcing norm, second-part norm at most the forcing norm, and squared norm at most five times its square. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/LocalCompactness.lean#L87).

**Graph components have smaller norms** · theorem. `norm_le_of_xbar`: Both component norms of a graph-space pair are bounded by the graph norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/LocalCompactness.lean#L93).

**A ball bound for a velocity reading** · theorem. `ball_velocity_le`: The local velocity squared-norm integral is bounded by the graph-pair norm squared times the ball volume. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/LocalCompactness.lean#L96).

**Read a gradient column almost everywhere** · theorem. `Breakdown.Cert.LocalCompactness.column_ae`: A physical gradient column agrees almost everywhere with the corresponding energy-space derivative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/LocalCompactness.lean#L117).

**Restriction bounds a spatial L2 norm** · theorem. `ball_l2_le`: The squared-norm integral over a ball is bounded by the full L2 norm squared of its representative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/LocalCompactness.lean#L133).

**One derivative below the graph norm** · theorem. `norm_partialX_le`: The squared norm of one gradient derivative is bounded by the graph-pair norm squared. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/LocalCompactness.lean#L141).

**Spatial balls have finite volume** · theorem. `ofReal_toReal_ball`: Taking the real value of a finite ball's volume and converting back recovers that volume. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/LocalCompactness.lean#L151).

**Convert ball volume to real form** · theorem. `ofReal_mul_volume`: Multiplication by the finite ball volume commutes with the stated conversion from real nonnegative bounds. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/LocalCompactness.lean#L156).

**Local period energy of velocity** · theorem. `period_velocity_le`: A graph curve controls the local period velocity energy by its squared norm times the ball volume. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/LocalCompactness.lean#L162).

**Local period energy of a gradient column** · theorem. `period_column_le`: A graph curve's squared norm controls each gradient column's local period energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/LocalCompactness.lean#L183).

**Linear readings preserve differences** · theorem. `sub_ae`: A physical difference represents the same linear map applied to the difference of the two graph corrections almost everywhere. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/LocalCompactness.lean#L198).

**A reading column matches its derivative** · theorem. `reading_column_ae`: For almost every time, each reading gradient column equals the corresponding energy-space derivative almost everywhere in space. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/LocalCompactness.lean#L214).

**Velocity differences have finite energy** · theorem. `fin_velocity`: The canonical velocities of two graph corrections have finite local period squared-difference energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/LocalCompactness.lean#L221).

**Gradient differences have finite energy** · theorem. `fin_column`: The canonical gradient columns of two graph corrections have finite local period squared-difference energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/LocalCompactness.lean#L227).

**Local period norms grow with radius** · theorem. `periodBallNorm_mono`: Increasing a nonnegative ball radius cannot decrease the local period norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/LocalCompactness.lean#L236).

**Include the volume factor in the bound** · theorem. `real_mul_bound`: The scalar graph-norm estimate bounds the energy times the volume factor by the common compactness bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/LocalCompactness.lean#L244).

**An energy bound uniform in the radius** · theorem. `real_bound`: The scalar norm estimate is bounded by the enlarged compactness constant using the nonnegative volume factor. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/LocalCompactness.lean#L249).

**Being Cauchy on a fixed spatial ball** · proposition definition. `FundamentalAt`: A subsequence is fundamental at a radius when its pairwise local period norms become arbitrarily small. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/LocalCompactness.lean#L253).

**A subsequence remains Cauchy** · theorem. `fundamentalAt_sub`: An eventual subsequence of a locally Cauchy sequence is locally Cauchy at the same radius. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/LocalCompactness.lean#L256).

**Refine a locally Cauchy subsequence** · theorem. `fundamentalAt_comp`: Composing the chosen indices with a strictly increasing subsequence preserves local Cauchy convergence. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/LocalCompactness.lean#L264).

**The successive subsequence refinements** · definition. `diagSeq`: The diagonal construction recursively composes the refinements chosen at successive stages. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/LocalCompactness.lean#L268).

**One subsequence meets all stages** · theorem. `exists_diagonal`: The compatible refinement hypotheses yield one strictly increasing subsequence satisfying every indexed requirement. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/LocalCompactness.lean#L272).

**Apply the local translation criterion** · theorem. `criterion_apply`: The uniform energy and translation bounds yield a further subsequence that is Cauchy on the chosen ball. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/LocalCompactness.lean#L306).

**A locally Cauchy velocity subsequence** · theorem. `step_velocity`: The free-inverse translation bounds supply a further subsequence with locally Cauchy velocity readings. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/LocalCompactness.lean#L330).

**A locally Cauchy gradient subsequence** · theorem. `step_column`: The free-inverse translation bounds supply a further subsequence with locally Cauchy readings of a chosen gradient column. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/LocalCompactness.lean#L368).

### Breakdown.Cert.MultiplierContinuity

This file selects the held multiplier and proves that its dependence on the parameter is continuous inside the certified box. Section 7.8: continuity before the finite-dimensional zero argument.

**Source namespace `Breakdown.Cert.Internal.MultiplierContinuity`.**

**The selected held multiplier** · definition. `heldMultiplier`: The held multiplier chooses one multiplier of an existing held solution and defaults to zero if no solution exists. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/MultiplierContinuity.lean#L14).

**The selected multiplier has a solution** · theorem. `heldMultiplier_spec`: When a held solution exists, the selected multiplier is accompanied by a forcing that solves the held system. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/MultiplierContinuity.lean#L17).

**The total multiplier has two terms** · theorem. `multiplierOf_eq`: The total multiplier is the sum of the approximate-profile multiplier and the selected held correction multiplier. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/MultiplierContinuity.lean#L23).

**The held multiplier is continuous** · theorem. `heldMultiplier_continuousOn`: Existence, uniqueness and the held-limit property make the selected held multiplier continuous on the parameter box. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/MultiplierContinuity.lean#L26).

**Source namespace `Breakdown.Cert`.**

**The total multiplier is continuous** · theorem. `multiplierContinuityHolds_of`: The certified approximate multiplier and the continuous selected correction multiplier supply the total-multiplier continuity interface. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/MultiplierContinuity.lean#L54).

### Breakdown.Cert.Nodes

This file names the analytic propositions used to assemble the earlier certificate route, separating required interfaces from their later proofs. Section 7: contracts for projection, inversion, compactness and held solutions.

**A periodic square-integrable field** · proposition definition. `IsPeriodicField`: A periodic field is jointly measurable, exactly one-periodic in time and has finite period squared-norm integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Nodes.lean#L13).

**An admissible positive bounded weight** · proposition definition. `IsAdmissibleWeight`: An admissible weight is measurable, bounded above, and bounded below everywhere by the specified positive constant. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Nodes.lean#L17).

**Symmetry of a graph correction** · proposition definition. `IsInvariantXX`: A graph correction is invariant when its gradient-map image belongs to the prescribed invariant Hilbert subspace. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Nodes.lean#L20).

**One slice of a graph correction** · definition. `sliceOf`: The slice operation evaluates the graph correction's time-circle representative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Nodes.lean#L22).

**One physical gradient column** · definition. `gradColumn`: A gradient column is the physical gradient applied to the chosen coordinate basis vector. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Nodes.lean#L24).

**The solenoidal projection contract** · interface proposition. `ProjectionHolds`: The projection interface requires a contractive projection, the physical pairing identity and identity on represented solenoidal fields. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Nodes.lean#L26).

Proved by `Breakdown.Coercive.projectionHolds_of_spec`.

**A bound for the free propagator** · interface proposition. `PropagatorBoundHolds`: The propagator interface requires the explicit positive-time kernel bound and continuity in positive propagation time. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Nodes.lean#L50).

Proved by `Breakdown.extended_certificate_orbit_proved`. The interface is constructed inside that proof.

**The gradient inverse contract** · interface proposition. `GradInvHolds`: The gradient-inverse interface requires integrability of the propagator integral and an operator satisfying the inverse specification for every positive period. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Nodes.lean#L55).

Proved by `Breakdown.extended_certificate_orbit_proved`. The interface is constructed inside that proof.

**The local free-energy identity** · interface proposition. `FreeEnergyLocalHolds`: The local-energy interface asks for a continuous periodic gradient-energy representative satisfying the integrated forcing-dissipation identity on every ordered time interval. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Nodes.lean#L63).

Proved by `Breakdown.Cert.freeEnergyLocalHolds_of`.

**The free inverse preserves symmetry** · interface proposition. `FreeEquivariantHolds`: The equivariance interface requires a positive-period free inverse to carry invariant forcing to an invariant graph correction. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Nodes.lean#L71).

Proved by `Breakdown.Cert.freeEquivariantHolds_of`.

**Weak continuity in the period** · interface proposition. `PeriodContinuityHolds`: The period-continuity interface requires bounded weakly convergent forcings and convergent positive periods to give weakly convergent free-inverse corrections. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Nodes.lean#L81).

Proved by `Breakdown.Cert.periodContinuityHolds_of`.

**A pointwise bound for one velocity slice** · interface proposition. `SliceSupBoundHolds`: The slice-supremum interface bounds velocity squared almost everywhere by the product of the two graph-part norms divided by twice pi. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Nodes.lean#L88).

Proved by `Breakdown.Cert.sliceSupBoundHolds_of`.

**The nonlinear product pairing contract** · interface proposition. `ProductPairingHolds`: The product-pairing interface identifies the abstract product against tests with the physical product integral when the second input has finite gradient supremum. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Nodes.lean#L105).

Proved by `Breakdown.Cert.productPairingHolds_of`.

**Subtracting two quadratic products** · interface proposition. `ProductSubHolds`: The product-subtraction interface gives the two-term bilinear difference identity in the Hilbert space and almost everywhere physically. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Nodes.lean#L110).

Proved by `Breakdown.Cert.productSubHolds_of`.

**Convection at the certified profile** · interface proposition. `ConvectionHolds`: The convection interface requires a realized bounded operator and identifies its abstract test pairing with the physical linearized advection term. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Nodes.lean#L116).

Proved by `Breakdown.Cert.convectionHolds_of`.

**Invariance of all certificate terms** · interface proposition. `InvarianceHolds`: The invariance interface requires convection, quadratic products, actuators and the defect to lie in the prescribed invariant subspace. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Nodes.lean#L124).

Proved by `Breakdown.Cert.invarianceHolds_of`.

**Continuity of the convection operator** · interface proposition. `ConvectionContinuityHolds`: The convection-continuity interface requires norm continuity of the operator on the certified parameter box. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Nodes.lean#L130).

Proved by `Breakdown.Cert.convectionContinuityHolds_of`.

**Physical meanings of certificate data** · interface proposition. `DataHolds`: The data interface binds abstract defects, actuators and pins to physical pairings and their certified quantitative bounds. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Nodes.lean#L133).

Proved by `Breakdown.Cert.dataHolds_of`.

**Continuity of targets and defect tests** · interface proposition. `DataContinuityHolds`: The data-continuity interface requires continuity of the pin target and every tested defect pairing on the parameter box. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Nodes.lean#L145).

Proved by `Breakdown.Cert.dataContinuityHolds_of`.

**Coercivity for the bordered equation** · interface proposition. `CoerciveBorderedHolds`: The coercivity interface bounds combined state size by global forcing, local forcing and pin norms for a represented bordered right-hand side. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Nodes.lean#L149).

Proved by `Breakdown.Cert.coerciveBorderedHolds_of`.

**The frozen-form lower-bound bridge** · interface proposition. `FrozenBridgeHolds`: The frozen bridge interface requires an almost everywhere slice lower bound for diffusion and profile convection in terms of weighted graph energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Nodes.lean#L158).

Proved by `Breakdown.Cert.frozenBridgeHolds_of`.

**The correction's gradient supremum bound** · interface proposition. `SupBoundHolds`: The supremum interface requires finite gradient supremum and the specified quadratic estimate involving weighted energy, bordered forcing and actuator size. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Nodes.lean#L169).

Proved by `Breakdown.Cert.supBoundHolds_of`.

**Uniform time-translation control** · interface proposition. `TimeModulusHolds`: The time-modulus interface gives a rate tending to zero that controls local velocity and gradient-column time shifts uniformly over a positive period interval. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Nodes.lean#L179).

Proved by `Breakdown.Cert.timeModulusHolds_of`.

**Spatial shifts controlled by derivatives** · interface proposition. `SpaceModulusHolds`: The space-modulus interface bounds local velocity shifts by the gradient norm and gradient-column shifts by the second-part norm, each times the shift length. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Nodes.lean#L187).

Proved by `Breakdown.Cert.spaceModulusHolds_of`.

**Compactness from small translations** · interface proposition. `TranslationCriterionHolds`: The translation interface turns uniform local energy and vanishing time-and-space translation bounds into a locally Cauchy subsequence. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Nodes.lean#L194).

Proved by `Breakdown.Cert.translationCriterionHolds_proof`.

**Convection after inversion is compact** · interface proposition. `ConvectionCompactHolds`: The compactness interface requires convection composed with the free inverse to be a compact operator at every certified parameter. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Nodes.lean#L215).

Proved by `Breakdown.Cert.convectionCompactHolds_of`.

**Invertibility of the bordered operator** · interface proposition. `BorderedInvertibleHolds`: The bordered-inverse interface requires an inverse specification and injectivity on pairs with invariant forcing components. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Nodes.lean#L219).

Proved by `Breakdown.Cert.borderedInvertibleHolds_of`.

**Metric and limit bounds on the held set** · interface proposition. `HeldMetricHolds`: The held-metric interface requires closedness, a positive ambient-norm lower bound, the triangle inequality and preservation of distance bounds under limits. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Nodes.lean#L235).

Proved by `Breakdown.Cert.heldMetricHolds_of`.

**The held step preserves its domain** · interface proposition. `HeldMapsToHolds`: The self-map interface requires every certified held step to map the admissible held set into itself. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Nodes.lean#L243).

Proved by `Breakdown.Cert.heldMapsToHolds_of`.

**A strict held contraction** · interface proposition. `HeldContractsHolds`: The contraction interface requires, at each certified parameter, a factor strictly below one controlling held distances after one step. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Nodes.lean#L247).

Proved by `Breakdown.Cert.heldContractsHolds_of`.

**A unique held solution at each parameter** · interface proposition. `HeldExistsUniqueHolds`: The held-solution interface requires existence and uniqueness of both forcing and multiplier at every parameter in the certified box. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Nodes.lean#L251).

Proved by `Breakdown.Cert.heldExistsUniqueHolds_of`.

**Held solutions survive parameter limits** · interface proposition. `HeldLimitHolds`: The held-limit interface requires a subsequence whose multipliers converge to those of a held solution at the limiting parameter. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Nodes.lean#L255).

Proved by `Breakdown.Cert.heldLimitHolds_of`.

**Continuity of the total multiplier** · interface proposition. `MultiplierContinuityHolds`: The multiplier-continuity interface requires the total selected multiplier to be continuous throughout the certified box. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Nodes.lean#L262).

Proved by `Breakdown.Cert.multiplierContinuityHolds_of`.

**Held solution with zero total multiplier** · interface proposition. `ExistsZeroHeldHolds`: The zero-multiplier interface asks for a parameter and held solution whose correction multiplier cancels the approximate multiplier. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Nodes.lean#L265).

Proved by `Breakdown.Cert.existsZeroHeldHolds_of`.

**The unforced weak equation contract** · interface proposition. `HeldWeakEquationHolds`: The weak-equation interface requires the corrected profile to have zero tested similarity residual once the total multiplier vanishes. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Nodes.lean#L269).

Proved by `Breakdown.Cert.heldWeakEquationHolds_of`.

**The corrected profile cannot vanish** · interface proposition. `HeldNonzeroHolds`: The nonvanishing interface requires every certified held correction to leave a profile that is not zero almost everywhere. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Nodes.lean#L278).

Proved by `Breakdown.Cert.heldNonzeroHolds_of`.

**Export a weak similarity profile** · interface proposition. `SigmaProfileOfHeldHolds`: The profile-export interface requires a zero-total-multiplier held solution to produce a weak similarity profile with its associated derivatives and bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Nodes.lean#L283).

Proved by `Breakdown.Cert.sigmaProfileOfHeldHolds_of`.

### Breakdown.Cert.PeriodContinuity

This file proves weak continuity of the free inverse as both the forcing and the positive period vary. Section 7.8: the linear limit step for held solutions.

**Zero gradient forces a zero graph pair** · theorem. `gradPart_eq_zero`: A graph pair with zero gradient part is zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/PeriodContinuity.lean#L17).

**Gradient-map representative by slices** · theorem. `gradCLM_ae`: The representative of the gradient map agrees almost everywhere with the gradient part of each graph slice. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/PeriodContinuity.lean#L33).

**The second-map representative by slices** · theorem. `secondCLM_ae`: The representative of the second-part map agrees almost everywhere with the second part of each graph slice. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/PeriodContinuity.lean#L37).

**The gradient map detects a correction** · theorem. `gradCLM_injective`: The gradient map is injective on graph corrections. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/PeriodContinuity.lean#L41).

**The time L2 norm as an integral** · theorem. `norm_sq_lp`: The squared norm of an L2 curve on the time circle is its integrated squared slice norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/PeriodContinuity.lean#L51).

**Squared L2 curve norms are integrable** · theorem. `integrable_norm_sq_lp`: The squared representative norm of a time-L2 curve is integrable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/PeriodContinuity.lean#L58).

**The correction norm splits by graph part** · theorem. `Breakdown.Cert.PeriodContinuity.norm_sq_xx`: The squared correction norm equals the sum of its squared gradient and second-part norms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/PeriodContinuity.lean#L62).

**A quadratic bound gives a factor two** · theorem. `le_two_mul_of_sq`: The stated nonnegative squared estimate implies the norm bound with factor two. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/PeriodContinuity.lean#L75).

**The selected free inverse is valid** · theorem. `freeInv_spec`: When the positive-period free-inverse specification is realizable, the selected operator satisfies it. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/PeriodContinuity.lean#L80).

**The free inverse has norm at most two** · theorem. `norm_freeInv_le`: For a positive period, the free-inverse correction norm is at most twice the forcing norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/PeriodContinuity.lean#L85).

**Read a time shift on representatives** · theorem. `coeFn_shift`: The representative of a time-shifted Hilbert curve equals the shifted representative almost everywhere. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/PeriodContinuity.lean#L89).

**Opposite time shifts cancel** · theorem. `shift_neg_shift`: Applying a time shift after its negative gives the original Hilbert curve. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/PeriodContinuity.lean#L97).

**Move a shift across an inner product** · theorem. `inner_shift`: Moving a time shift from one side of an inner product to the other changes its sign. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/PeriodContinuity.lean#L107).

**Fixed curve varies continuously by shift** · theorem. `continuous_shift`: Time shifts of a fixed Hilbert curve depend continuously on the shift parameter. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/PeriodContinuity.lean#L120).

**Lift the slice propagator to time curves** · definition. `propOp`: The propagated-curve operator applies the slice propagator pointwise in time as a continuous linear map. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/PeriodContinuity.lean#L127).

**The inverse integrand is shift then flow** · theorem. `integrand_eq`: The gradient-inverse integrand equals the lifted propagator applied to the forcing shifted by minus propagation time divided by period. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/PeriodContinuity.lean#L130).

**Move the propagator onto the test** · theorem. `inner_integrand`: The tested propagator integrand can be written by applying the adjoint propagator and opposite shift to the test vector. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/PeriodContinuity.lean#L133).

**Pair a strong limit with a weak limit** · theorem. `tendsto_inner_strong_weak`: A strongly convergent test sequence paired with a bounded weakly convergent sequence has the expected scalar limit. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/PeriodContinuity.lean#L140).

**Pairing with the inverse integral** · theorem. `inner_gradInv_eq`: The inner product with the gradient inverse equals the integral of inner products with its positive-time propagator integrand. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/PeriodContinuity.lean#L165).

**An integrable bound for inverse pairings** · theorem. `norm_inner_integrand_le`: A uniform forcing bound dominates the tested inverse integrand by the common kernel times the test norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/PeriodContinuity.lean#L170).

**Pointwise limits of inverse pairings** · theorem. `tendsto_inner_integrand`: Convergent positive periods and bounded weak forcing convergence give convergence of the tested propagator integrand at each positive propagation time. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/PeriodContinuity.lean#L184).

**Weak convergence of gradient inverses** · theorem. `tendsto_inner_gradInv`: Dominated convergence gives the tested limit of gradient inverses for convergent periods and bounded weakly convergent forcings. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/PeriodContinuity.lean#L203).

**Select a weakly convergent index map** · theorem. `exists_subseq`: For positive periods converging to a positive limit and uniformly bounded forcing converging weakly, there is an index map along which the free inverses converge weakly to the inverse of the limiting data. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/PeriodContinuity.lean#L226).

### Breakdown.Cert.PeriodIntegral

This file identifies integration over one real-time period with integration on the unit time circle. Section 7: measure conventions for periodic physical readings.

**Source namespace `Breakdown.Cert`.**

**Integrate a nonnegative circle function** · theorem. `lintegral_Icc_coe`: A nonnegative function pulled back from the time circle has the same integral over the closed unit interval and the circle. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/PeriodIntegral.lean#L12).

**Integrate circle functions on a period** · theorem. `integral_Icc_coe`: The integral of a function on the time circle equals the integral of its real-time pullback over the closed unit interval. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/PeriodIntegral.lean#L18).

**Source namespace `Breakdown.Cert.PeriodIntegralInternal`.**

**A measure-preserving representative** · theorem. `measurePreserving_equivIoc_val`: Choosing the representative in the half-open unit interval preserves the circle's volume measure. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/PeriodIntegral.lean#L27).

**Return from the half-open representative** · theorem. `coe_equivIoc_val`: The chosen half-open interval representative maps back to the original time-circle point. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/PeriodIntegral.lean#L32).

**Every integer period has circle measure** · theorem. `measurePreserving_mk_int`: The quotient map from any integer-translated half-open unit interval to the circle preserves measure. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/PeriodIntegral.lean#L36).

**Source namespace `Breakdown.Cert`.**

**Circle and real-time null sets agree** · theorem. `ae_coe_iff`: A predicate holds almost everywhere on the circle exactly when its pullback holds almost everywhere in real time. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/PeriodIntegral.lean#L44).

**A periodic field descends to the circle** · theorem. `exists_lift_of_periodic`: An exactly one-periodic field factors through a field on the unit time circle. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/PeriodIntegral.lean#L57).

**Measurability agrees across the quotient** · theorem. `aestronglyMeasurable_lift_iff`: For matching lifted fields, joint almost everywhere strong measurability is equivalent on circle-space and real-time-space. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/PeriodIntegral.lean#L62).

**A measurable periodic lift exists** · theorem. `aestronglyMeasurable_lift_of_periodic`: A jointly measurable periodic field admits a jointly measurable lift to the time circle. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/PeriodIntegral.lean#L88).

### Breakdown.Cert.ProductBound

This file controls the physical nonlinear product by weighted graph energy and a gradient supremum. Section 7.6: support for the quadratic estimate.

**Expand a map in coordinate directions** · theorem. `Breakdown.Cert.ProductBound.apply_eq_sum`: A linear map applied to a vector is the sum of its coordinate-direction values weighted by the vector coordinates. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProductBound.lean#L16).

**Basis values determine a linear map** · theorem. `Breakdown.Cert.ProductBound.ext_of_unit`: Two linear maps agreeing on the three coordinate basis vectors are equal. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProductBound.lean#L21).

**Bound a coordinate contraction** · theorem. `norm_sum_smul_sq_le`: The squared norm of a coordinate-weighted column sum is bounded by the coordinate norm squared times the sum of column norms squared. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProductBound.lean#L27).

**Integrate the squared column norms** · theorem. `lintegral_sum_sq`: The integral of a finite sum of squared L2 column norms equals the sum of their L2 norms squared. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProductBound.lean#L41).

**Spatial L2 energy as an integral** · theorem. `lintegral_norm_sq_L2R`: The squared spatial L2 norm equals the nonnegative squared-norm integral of its representative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProductBound.lean#L50).

**Bounded coefficient gives an L2 product** · theorem. `lintegral_sum_smul_le`: A pointwise bound on the coefficient vector controls the squared integral of its contraction with L2 columns. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProductBound.lean#L55).

**The product slice is advection** · theorem. `Breakdown.Cert.ProductBound.productSlice_apply`: The product slice contracts the first velocity's coordinates with the second input's derivative columns. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProductBound.lean#L66).

**The graph norms bound a product slice** · theorem. `lintegral_productSlice_le`: The velocity supremum estimate bounds a product slice's L2 energy by the two first-input graph norms and the second gradient norm squared. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProductBound.lean#L70).

**Locally integrable operator action** · theorem. `Breakdown.Cert.ProductBound.locallyIntegrable_apply`: Applying a locally integrable linear-map field to a fixed vector gives a locally integrable vector field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProductBound.lean#L80).

**A reading gradient matches its columns** · theorem. `ae_gradient_eq`: For almost every time, a physical reading gradient agrees almost everywhere with the map built from the graph gradient's derivative columns. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProductBound.lean#L94).

**Physical and graph energies agree** · theorem. `lintegral_matSq_eq`: For almost every time, the physical gradient squared-norm integral equals the squared norm of the graph gradient part. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProductBound.lean#L100).

**Negation preserves squared L2 energy** · theorem. `lintegral_congr_neg`: A field equal almost everywhere to the negative of an L2 representative has the same squared-norm integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProductBound.lean#L112).

**Norms of negative representatives** · theorem. `aemeasurable_of_ae_neg`: A field equal almost everywhere to a negative L2 representative has a measurable squared norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProductBound.lean#L120).

**Hessian-trace energy equals graph energy** · theorem. `lintegral_trace_eq`: For almost every time, the Hessian-trace squared-norm integral equals the squared norm of the graph second part. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProductBound.lean#L127).

**Identify a physical product slice** · theorem. `apply_eq_productSlice`: Matching velocity and derivative-column representatives identifies the matrix-applied-to-velocity expression with the product slice. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProductBound.lean#L135).

**Bound the physical product on a slice** · theorem. `lintegral_productField_le`: For almost every time, the physical product energy obeys the same graph-norm bound as the represented product slice. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProductBound.lean#L140).

**Measurability of linear-image energy** · theorem. `aemeasurable_sq`: The squared norm of a continuous linear map applied to a graph curve is almost everywhere measurable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProductBound.lean#L152).

**Integrate a weighted nonnegative sum** · theorem. `lintegral_add_mul_eq`: The nonnegative integral of a sum with a constant weight splits into the weighted sum of the integrals. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProductBound.lean#L157).

**Integrate the two graph energies** · theorem. `lintegral_energy_slices`: The unit-period integral of the second-part and constant-weight gradient energies equals their lifted Hilbert norms squared. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProductBound.lean#L162).

**Matrix squared norm is nonnegative** · theorem. `matSq_nonneg`: The sum of the squared coordinate-column norms of a matrix is nonnegative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProductBound.lean#L177).

**Bound weighted energy on both sides** · theorem. `slice_energy_bounds`: Lower and upper pointwise weight bounds sandwich the weighted slice energy between the corresponding constant-weight energies. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProductBound.lean#L180).

**Read an extended energy lower bound** · theorem. `le_toReal_of`: A finite extended-real energy inequality yields the corresponding real-valued lower bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProductBound.lean#L196).

**The weight controls both graph energies** · theorem. `energy_ge`: Weighted energy bounds below the second-part energy plus the positive weight lower bound times gradient energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProductBound.lean#L201).

**Slice gradients lie below the supremum** · theorem. `ae_norm_le_supGrad`: With finite gradient supremum, the graph gradient norm is at most that supremum almost everywhere in time. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProductBound.lean#L230).

**A weighted arithmetic-geometric bound** · theorem. `mul_le_energy`: A product of two nonnegative norms is controlled by their weighted sum of squares divided by twice the square root of the weight. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProductBound.lean#L236).

**The squared product constant** · theorem. `supBoundFactor_sq`: The squared product constant is the reciprocal of four pi times the square root of the positive weight lower bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProductBound.lean#L243).

**The product constant is nonnegative** · theorem. `supBoundFactor_nonneg`: The coefficient used in the product estimate is nonnegative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProductBound.lean#L247).

**Control a slice product by energy** · theorem. `slice_real_le`: The gradient supremum and weighted arithmetic-geometric estimate bound the real slice product by the weighted energy expression. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProductBound.lean#L251).

**The extended-real slice product bound** · theorem. `slice_ennreal_le`: The real slice product estimate gives its extended nonnegative-real version for integration. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProductBound.lean#L264).

**Combine a weighted squared bound** · theorem. `ofReal_combine`: The extended-real weighted sum of squares equals the conversion of the corresponding real nonnegative expression. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProductBound.lean#L280).

**Finish the squared product estimate** · theorem. `final_real_le`: A weighted-energy upper bound converts the scalar product expression into the square of the final product-norm bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProductBound.lean#L286).

**The full period product estimate** · theorem. `lintegral_Icc_le`: Integrating the slice estimate bounds the product energy by the square of the product constant times root weighted energy times gradient supremum. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProductBound.lean#L292).

**Energy of an L2 equivalence class** · theorem. `ofReal_norm_toLp_sq`: The squared norm of the L2 class of a function equals its nonnegative squared-norm integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProductBound.lean#L323).

**The fallback L2 map respects energy** · theorem. `ofReal_norm_toLpOrZero_sq_le`: The squared norm of the L2-or-zero construction never exceeds the function's squared-norm integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProductBound.lean#L333).

**Projection cannot increase field energy** · theorem. `ofReal_norm_solField_sq_le`: The squared solenoidal reading norm is bounded by the physical field's squared-norm integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProductBound.lean#L340).

**Bound a chosen circle curve by energy** · theorem. `ofReal_norm_circleLpOrZero_sq_le`: The circle-L2-or-zero construction satisfies the supplied period energy bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProductBound.lean#L345).

**Take the root of an extended bound** · theorem. `sqrt_toReal_le`: A nonnegative squared bound on a finite extended-real quantity bounds the square root of its real value. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProductBound.lean#L356).

**Recover a real norm from its square** · theorem. `le_of_ofReal_sq_le`: For nonnegative real quantities, the converted squared inequality implies the original linear bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProductBound.lean#L360).

**The selected reading is valid** · theorem. `Breakdown.Cert.ProductBound.isReadingOf_readingOf`: The selected velocity, gradient and second-derivative representatives give a valid physical reading of the correction. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProductBound.lean#L364).

### Breakdown.Cert.ProductPairing

This file identifies the represented nonlinear product with the physical advection pairing against divergence-free tests. Section 7.6: support for the quadratic product and its weak reading.

**Source namespace `Breakdown.Cert.Internal.ProductPairing`.**

**Expand a map in coordinate directions** · theorem. `Breakdown.Cert.ProductPairing.apply_eq_sum`: A linear map applied to a vector is the sum of its coordinate-direction values weighted by the vector coordinates. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProductPairing.lean#L16).

**Basis values determine a linear map** · theorem. `Breakdown.Cert.ProductPairing.ext_of_unit`: Two linear maps agreeing on the three coordinate basis vectors are equal. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProductPairing.lean#L21).

**Locally integrable operator action** · theorem. `Breakdown.Cert.ProductPairing.locallyIntegrable_apply`: Applying a locally integrable linear-map field to a fixed vector gives a locally integrable vector field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProductPairing.lean#L27).

**Weak gradients are unique a.e.** · theorem. `weakGradient_unique`: Two locally integrable weak gradients of the same velocity agree almost everywhere. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProductPairing.lean#L32).

**The selected reading is valid** · theorem. `Breakdown.Cert.ProductPairing.isReadingOf_readingOf`: The selected velocity, gradient and second-derivative representatives give a valid physical reading of the correction. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProductPairing.lean#L41).

**The product slice is advection** · theorem. `Breakdown.Cert.ProductPairing.productSlice_apply`: The product slice contracts the first velocity's coordinates with the second input's derivative columns. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProductPairing.lean#L50).

**Read the physical directional derivative** · theorem. `ae_apply_eq`: For almost every time, applying the second reading's gradient to the first reading's velocity equals the represented product slice almost everywhere in space. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProductPairing.lean#L54).

**Canonical product has the right slices** · theorem. `ae_productField_eq`: The physical product field agrees almost everywhere by time slices with the product of the two graph gradient slices. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProductPairing.lean#L66).

**Circle representative is fractional part** · theorem. `circleRep_coe`: The chosen representative of a real time on the unit circle is its fractional part. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProductPairing.lean#L73).

**Periodic fields ignore circle choices** · theorem. `periodic_circleRep`: A one-periodic field has the same value at a real time and at its chosen circle representative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProductPairing.lean#L78).

**The solenoidal reading respects equality** · theorem. `Breakdown.Cert.ProductPairing.solField_congr`: Almost everywhere equal fields have equal solenoidal Hilbert-space readings. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProductPairing.lean#L84).

**Chosen curve respects almost equality** · theorem. `circleLpOrZero_congr`: Almost everywhere equal slice curves have equal circle-L2-or-zero representatives. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProductPairing.lean#L92).

**Abstract product represents the field** · theorem. `productH_eq_physToHH`: The Hilbert-space nonlinear product equals the physical-to-Hilbert image of its physical product field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProductPairing.lean#L101).

**Source namespace `Breakdown.Cert`.**

**The nonlinear product pairing is correct** · theorem. `productPairingHolds_of`: The physical realization and test-pairing interfaces identify abstract nonlinear pairings with their physical integrals. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProductPairing.lean#L115).

### Breakdown.Cert.ProductSub

This file expands the difference of two quadratic terms into two bilinear terms at both physical and Hilbert-space levels. Section 7.6: the difference estimate used by the held contraction.

**Slice equality gives joint equality** · theorem. `ae_eq_of_ae_slices`: Measurable functions equal almost everywhere on almost every slice are equal almost everywhere for the product measure. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProductSub.lean#L17).

**The quadratic slice difference identity** · theorem. `productSlice_sub`: The difference of two self-products splits almost everywhere into the difference-first and difference-second bilinear terms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProductSub.lean#L35).

**Use a named difference in the product** · theorem. `productSlice_sub_of_eq`: If a third energy-space element is the input difference, it can replace that difference in the quadratic slice identity. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProductSub.lean#L51).

**Gradient slices preserve subtraction** · theorem. `ae_gradPart_sub`: The gradient slice of a correction difference equals the difference of gradient slices almost everywhere in time. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProductSub.lean#L57).

**The supremum is the gradient L∞ norm** · theorem. `supGrad_eq_gradCLM`: The gradient supremum equals the extended L∞ norm of the represented gradient map. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProductSub.lean#L68).

**Finite gradient bounds for differences** · theorem. `Breakdown.Cert.ProductSub.supGrad_sub_lt_top`: The difference of two corrections with finite gradient supremum again has finite gradient supremum. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProductSub.lean#L71).

**The unit weight is admissible** · theorem. `admissible_one`: The constant weight one is admissible with positive lower bound one. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProductSub.lean#L78).

**Physical quadratic difference identity** · theorem. `ae_slices`: For almost every time, the physical difference of self-products equals the two bilinear difference terms almost everywhere in space. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProductSub.lean#L81).

**Lift the product identity into L2** · theorem. `toLpOrZero_sub_eq`: Under the L2 and almost everywhere identity hypotheses, the L2-or-zero map preserves the four-term difference relation. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProductSub.lean#L91).

**Lift the difference identity** · theorem. `physToHH_sub_eq`: A valid four-term physical field relation passes through the physical-to-Hilbert representation. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProductSub.lean#L99).

### Breakdown.Cert.ProjectionSpec

This file constructs the orthogonal solenoidal projection in Fourier variables and verifies its physical test-pairing contract. Section 7.5: support for forcing projection in the free equation.

**Source namespace `Breakdown.Cert.Internal.ProjectionSpec`.**

**The longitudinal Fourier projection** · theorem. `longitudinal_eq`: The longitudinal symbol projects a complex vector onto the frequency direction using the inverse frequency norm squared. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProjectionSpec.lean#L16).

**The frequency vector has the right norm** · theorem. `inner_freqVec_self`: The complex inner product of a frequency vector with itself is the squared real frequency norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProjectionSpec.lean#L21).

**Longitudinal projection is idempotent** · theorem. `longitudinal_idem`: Projecting onto the frequency direction twice gives the same result as projecting once. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProjectionSpec.lean#L26).

**Longitudinal projection is self-adjoint** · theorem. `inner_longitudinal_left`: The longitudinal projection can be moved between the two sides of the complex inner product. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProjectionSpec.lean#L37).

**Real self-adjointness of the symbol** · theorem. `real_inner_longitudinal_left`: The same longitudinal projection is self-adjoint for the real inner product on complex vectors. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProjectionSpec.lean#L43).

**The symbol respects reality symmetry** · theorem. `conjVec_longitudinal_neg`: Conjugating the longitudinal projection at negative frequency equals projecting the conjugate at positive frequency. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProjectionSpec.lean#L50).

**The multiplier acts pointwise** · theorem. `fieldOp_longitudinal_ae`: The Fourier multiplier with longitudinal symbol agrees almost everywhere with pointwise longitudinal projection. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProjectionSpec.lean#L56).

**Solenoidal means are transverse** · theorem. `fieldOp_solenoidal`: The solenoidal Fourier multiplier is the identity minus the longitudinal multiplier. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProjectionSpec.lean#L60).

**Longitudinal multiplier is idempotent** · theorem. `fieldOp_longitudinal_idem`: The induced longitudinal multiplier on L2 is a projection. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProjectionSpec.lean#L71).

**Multiplier preserves reality symmetry** · theorem. `reflConj_fieldOp_longitudinal`: Reflection-conjugation commutes with the longitudinal Fourier multiplier. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProjectionSpec.lean#L78).

**Longitudinal multiplier is self-adjoint** · theorem. `inner_fieldOp_longitudinal`: The longitudinal L2 multiplier can be moved across the real Hilbert inner product. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProjectionSpec.lean#L88).

**Solenoidal fields are transverse** · theorem. `fieldOp_longitudinal_of_mem`: The longitudinal multiplier vanishes on the solenoidal Fourier subspace. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProjectionSpec.lean#L96).

**Solenoidal real fields obey conjugacy** · theorem. `reflConj_of_mem`: Elements of the real solenoidal Fourier subspace are fixed by reflection-conjugation. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProjectionSpec.lean#L99).

**Removing longitudinal part gives a field** · theorem. `sub_longitudinal_mem`: Subtracting the longitudinal component from a reality-symmetric Fourier field gives an element of the solenoidal subspace. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProjectionSpec.lean#L102).

**Fourier construction of the projection** · definition. `projRaw`: The raw projection complexifies a real L2 field, applies the Fourier transform and removes its longitudinal component. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProjectionSpec.lean#L109).

**Expand the raw projection** · theorem. `projRaw_apply`: The raw projection is the transformed field minus the longitudinal part of that transform. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProjectionSpec.lean#L111).

**The raw projection lands in the subspace** · theorem. `projRaw_mem`: Every raw projected real L2 field lies in the real solenoidal Fourier subspace. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProjectionSpec.lean#L117).

**Solenoidal projection as a bounded map** · definition. `projCLM`: The raw projection restricted to its verified range is a continuous linear map into the solenoidal Hilbert space. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProjectionSpec.lean#L121).

**Verify the projection specification** · theorem. `projCLM_spec`: The explicitly constructed projection satisfies the required projection specification. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProjectionSpec.lean#L123).

**The Fourier transform preserves the norm** · theorem. `norm_freqTrR`: The real-linear Fourier transform on the complex L2 space is norm preserving. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProjectionSpec.lean#L125).

**Recover a Fourier field from its reading** · theorem. `freqTrR_complexify_toPhys`: Complexifying and Fourier transforming a physical reading recovers the original reality-symmetric Fourier field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProjectionSpec.lean#L128).

**The real-to-Fourier isometric embedding** · definition. `transformIsometry`: Complexification followed by Fourier transformation defines a real linear isometric embedding. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProjectionSpec.lean#L155).

**Fourier pairings are preserved** · theorem. `inner_transform`: Transforming two real L2 fields preserves their real inner product. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProjectionSpec.lean#L161).

**The solenoidal symbol is contractive** · theorem. `norm_solenoidalSymbol_le`: The operator norm of the solenoidal projection symbol is at most one at every frequency. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProjectionSpec.lean#L165).

**The projection symbol is measurable** · theorem. `aesm_solenoidalSymbol`: The solenoidal Fourier symbol is almost everywhere strongly measurable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProjectionSpec.lean#L170).

**Source namespace `Breakdown.Cert`.**

**Selected projection meets its contract** · theorem. `solProj_spec`: The selected solenoidal projection satisfies the projection specification. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProjectionSpec.lean#L179).

**The chosen projection's Fourier formula** · theorem. `solProj_coe`: The chosen projection equals the transformed real field with its longitudinal component removed. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProjectionSpec.lean#L184).

**Physical solenoidal reading is isometric** · theorem. `Breakdown.Cert.ProjectionSpec.norm_toPhysH`: The physical reading of a solenoidal Hilbert-space element has the same L2 norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProjectionSpec.lean#L189).

**Projection cannot increase the L2 norm** · theorem. `norm_solProj_le`: The solenoidal projection has output norm at most its real L2 input norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProjectionSpec.lean#L192).

**Unfold the physical Hilbert reading** · theorem. `toPhysH_apply`: The physical solenoidal reading is the ordinary Fourier-space physical reading of the underlying element. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProjectionSpec.lean#L197).

**Projection preserves solenoidal pairings** · theorem. `inner_solProj`: Pairing a projected field with a solenoidal element equals pairing the original field with that element's physical reading. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProjectionSpec.lean#L199).

**Projection recovers a solenoidal element** · theorem. `solProj_toPhysH`: Projecting the physical reading of a solenoidal element returns that element. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProjectionSpec.lean#L204).

**A solenoidal test survives projection** · theorem. `toPhysH_solField_test`: The physical reading of a projected spatial test equals its L2 equivalence class. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProjectionSpec.lean#L209).

**Projected tests give physical integrals** · theorem. `inner_solField_test`: The abstract inner product with a projected test equals the integral of the physical field-test pairing. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ProjectionSpec.lean#L219).

### Breakdown.Cert.ReadingEnergy

This file proves that physical velocity-gradient and Hessian-trace energies agree with the graph-space norms used by the certificate. Section 7.5: support for physical interpretation of graph energy.

**Gradient columns are locally integrable** · theorem. `locallyIntegrable_column`: Applying a locally integrable gradient field to a coordinate basis vector gives a locally integrable column. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ReadingEnergy.lean#L18).

**Weak-gradient columns are unique** · theorem. `column_ae_of_weakGradient`: Corresponding columns of two weak gradients of the same field agree almost everywhere. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ReadingEnergy.lean#L24).

**Read a gradient column almost everywhere** · theorem. `Breakdown.Cert.ReadingEnergy.column_ae`: A physical gradient column agrees almost everywhere with the corresponding energy-space derivative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ReadingEnergy.lean#L33).

**Matrix energy from derivative columns** · theorem. `matSq_ae`: The physical gradient squared norm agrees almost everywhere with the sum of the three represented derivative-column squared norms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ReadingEnergy.lean#L40).

**Derivative-column energy is integrable** · theorem. `integrable_sum_partialX`: The sum of squared represented derivative-column norms is integrable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ReadingEnergy.lean#L48).

**Recover the derivative norm** · theorem. `integral_sum_partialX`: The integral of the three derivative-column energies equals the squared energy-space norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ReadingEnergy.lean#L52).

**Physical solenoidal reading is isometric** · theorem. `Breakdown.Cert.ReadingEnergy.norm_toPhysH`: The physical reading of a solenoidal Hilbert-space element has the same L2 norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ReadingEnergy.lean#L58).

**The physical Hessian trace has L2 energy** · theorem. `trace_integral`: A physical Hessian trace representing the graph second part is square integrable with exactly that part's norm squared. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ReadingEnergy.lean#L61).

**An admissible weight has a finite bound** · theorem. `weight_bound`: An admissible weight has one nonnegative upper bound and is nonnegative everywhere. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ReadingEnergy.lean#L72).

**A bounded weight preserves integrability** · theorem. `integrable_weighted`: Multiplying the nonnegative integrable energy density by the admissible bounded weight remains integrable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ReadingEnergy.lean#L77).

**Weighted slice energy is nonnegative** · theorem. `sliceWeightedGrad_nonneg`: An admissible nonnegative weight gives nonnegative weighted gradient energy on every slice. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ReadingEnergy.lean#L84).

**A uniform upper bound on slice energy** · theorem. `sliceWeightedGrad_le`: The weight upper bound yields one constant controlling every weighted slice energy by the squared energy-space norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ReadingEnergy.lean#L89).

**A squared L2 norm is an integral** · theorem. `Breakdown.Cert.ReadingEnergy.norm_sq_eq_integral`: The squared norm of an L2 curve equals the integral of its pointwise squared norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ReadingEnergy.lean#L98).

**Represented gradient squares agree** · theorem. `gradSq_ae`: The squared norm of the gradient-map representative equals that of the graph slice gradient almost everywhere in time. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ReadingEnergy.lean#L108).

**Gradient norm is integrated slice energy** · theorem. `norm_sq_gradCLM`: The squared gradient-map norm equals the integral of the squared graph slice gradient norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ReadingEnergy.lean#L114).

**Slice gradient energy is integrable** · theorem. `integrable_gradSq`: The squared norm of the graph gradient slices is integrable in time. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ReadingEnergy.lean#L117).

**Represented second-part squares agree** · theorem. `secondSq_ae`: The squared norm of the second-map representative equals that of the graph slice second part almost everywhere in time. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ReadingEnergy.lean#L121).

**Integrate the second-part slice energy** · theorem. `norm_sq_secondCLM`: The squared second-map norm equals the integral of the squared graph slice second-part norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ReadingEnergy.lean#L127).

**Second-part slice energy is integrable** · theorem. `integrable_secondSq`: The squared norm of the graph second-part slices is integrable in time. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ReadingEnergy.lean#L130).

**Read finite period energy as an integral** · theorem. `toReal_periodLIntegral`: The finite physical period integral equals the ordinary integral of its matched time-circle energy density. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ReadingEnergy.lean#L134).

**Physical and graph weighted energies** · theorem. `slice_energy`: The physical squared Hessian-trace plus weighted gradient integral equals the graph slice's second-part and weighted gradient energies. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ReadingEnergy.lean#L167).

**Physical and graph gradient energies** · theorem. `slice_matNorm`: The physical matrix squared-norm integral equals the squared graph gradient-part norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ReadingEnergy.lean#L197).

**Matrix squared norm is continuous** · theorem. `continuous_matSq`: The sum of squared matrix-column norms is a continuous function of the matrix. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ReadingEnergy.lean#L209).

**The Hessian trace is continuous** · theorem. `Breakdown.Cert.ReadingEnergy.continuous_secondDerivTrace`: Taking the second-derivative trace is continuous as a map of bilinear operators. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ReadingEnergy.lean#L214).

**Periodic gradients have periodic energy** · theorem. `periodic_matSq`: A time-periodic gradient field has a time-periodic matrix-energy density. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ReadingEnergy.lean#L219).

**Period gradient energy is the graph norm** · theorem. `matNorm_part`: The real value of the physical period gradient energy equals the squared gradient-map norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ReadingEnergy.lean#L253).

### Breakdown.Cert.ReadingExists

This file chooses jointly measurable periodic velocity, gradient and Hessian fields for every graph correction. Section 7.5: construction of physical readings of the free equation.

**Source namespace `Breakdown.Cert.Internal.ReadingExists`.**

**Equal columns give equal gradient fields** · theorem. `gradField_ae`: Almost everywhere equality of all derivative columns gives almost everywhere equality of the assembled gradient fields. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ReadingExists.lean#L31).

**Assembling measurable gradient columns** · theorem. `aestronglyMeasurable_gradField`: Jointly measurable columns assemble into an almost everywhere strongly measurable gradient field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ReadingExists.lean#L37).

**The Fourier velocity has a weak gradient** · theorem. `weakGradient_velocity`: The represented velocity has the gradient built from its three energy-space derivative columns as a weak gradient. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ReadingExists.lean#L49).

**Weak derivatives of derivative columns** · theorem. `weakGradient_partial`: The square-root Laplacian graph relation gives each derivative column its represented weak gradient. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ReadingExists.lean#L57).

**A physical reading of one graph slice** · theorem. `slice_reading`: Matched slice representatives provide weak first and second derivatives, the signed Hessian-trace identity and the Hessian energy bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ReadingExists.lean#L70).

**Transfer a circle reading to real time** · theorem. `ae_slice`: The selected joint representative agrees almost everywhere in real time and space with the linear image of each circle slice. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ReadingExists.lean#L127).

**Convert the squared curve norm** · theorem. `ofReal_norm_sq_eq`: The squared L2 curve norm equals the nonnegative integral of the representative's squared norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ReadingExists.lean#L139).

**Energy after a bounded slice map** · theorem. `ofReal_norm_compLpL_sq`: The squared norm of a slice-wise continuous linear map equals its integrated pointwise squared norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ReadingExists.lean#L148).

**Choose a periodic representative** · theorem. `exists_slice_representative`: A continuous linear image of a time-circle curve has a jointly measurable periodic physical representative with almost everywhere slice agreement. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ReadingExists.lean#L156).

**Source namespace `Breakdown.Cert`.**

**Every graph correction has a reading** · theorem. `exists_reading`: Every graph correction admits velocity, gradient and Hessian readings with the period Hessian bound controlled by the graph second part. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ReadingExists.lean#L169).

### Breakdown.Cert.Rescale

This file transports measurable fields, integrals and weak equations between normalized time and a general positive period. Section 7: support for the weak profile time normalization.

**Rescale only the time coordinate** · definition. `timeScale`: A nonzero time factor defines a homeomorphism that scales time and leaves space fixed. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Rescale.lean#L13).

**Evaluate the time rescaling** · theorem. `timeScale_apply`: The time-scaling homeomorphism sends a point to the scaled time with the same spatial coordinate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Rescale.lean#L16).

**Time scaling is a measurable embedding** · theorem. `measurableEmbedding_timeScale`: Scaling time by a nonzero factor gives a measurable embedding of space-time. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Rescale.lean#L19).

**The measure factor for time scaling** · theorem. `map_timeScale`: The push-forward of space-time volume under nonzero time scaling is volume multiplied by the absolute reciprocal scale. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Rescale.lean#L23).

**Time scaling preserves null sets** · theorem. `quasiMeasurePreserving_timeScale`: A nonzero time scaling is quasi-measure-preserving on space-time volume. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Rescale.lean#L31).

**Scalar time scaling preserves null sets** · theorem. `quasiMeasurePreserving_mul`: Multiplication by a nonzero scalar is quasi-measure-preserving for real Lebesgue measure. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Rescale.lean#L36).

**Time scaling preserves integrability** · theorem. `integrable_timeScale_iff`: A nonzero time rescaling preserves and reflects integrability of the pulled-back function. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Rescale.lean#L41).

**Change variables under time scaling** · theorem. `integral_timeScale`: Integrating a function after nonzero time scaling multiplies its original integral by the absolute reciprocal scale. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Rescale.lean#L47).

**Rescale a period integral to unit time** · theorem. `setLIntegral_Icc_inv_mul`: For a positive period, its nonnegative integral after inverse time rescaling equals the period times the unit-interval integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Rescale.lean#L52).

**Match the two weak similarity integrands** · theorem. `weakSimilarityIntegrand_eq`: Inverse-period rescaling identifies the weak similarity integrand with the normalized-period integrand and the correspondingly rescaled test. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Rescale.lean#L63).

**Time rescaling preserves test fields** · theorem. `isSpaceTimeTestField_comp`: Composing a space-time test with a positive time dilation gives another valid space-time test. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Rescale.lean#L76).

### Breakdown.Cert.SigmaProfileOfHeld

This file adds the held correction to the approximate profile and verifies its weak derivatives, integrability and divergence conditions. Section 7.8: support for exporting the nonlinear solution.

**Source namespace `Breakdown.Cert.Internal.SigmaProfileOfHeld`.**

**Smooth derivatives are weak derivatives** · theorem. `Breakdown.Cert.SigmaProfileOfHeld.isWeakGradient_of_contDiff`: A continuously differentiable field has its classical derivative as a weak gradient. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SigmaProfileOfHeld.lean#L12).

**Weak gradients add** · theorem. `isWeakGradient_add`: The sum of two fields with weak gradients has the sum of those gradients as its weak gradient. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SigmaProfileOfHeld.lean#L28).

**Smooth gradient column has a derivative** · theorem. `isWeakGradient_column_of_contDiff`: A sufficiently smooth field's gradient column has the corresponding flipped second derivative as its weak gradient. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SigmaProfileOfHeld.lean#L57).

**Bound a power of a sum** · theorem. `norm_add_pow_le`: The norm of a sum raised to a natural power is bounded by two to that power times the sum of the individual powers. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SigmaProfileOfHeld.lean#L70).

**Integrate the power-of-a-sum bound** · theorem. `lintegral_norm_add_pow_le`: The nonnegative integral of a sum's norm power is bounded by the corresponding weighted integrals of the two separate powers. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SigmaProfileOfHeld.lean#L87).

**Decay controls the full-space integral** · theorem. `lintegral_le_of_decay`: An integrable radial decay majorant bounds the nonnegative integral of the dominated density. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SigmaProfileOfHeld.lean#L106).

**The decay integral is nonnegative** · theorem. `integral_decay_nonneg`: The integral of the stated nonnegative radial decay function is nonnegative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SigmaProfileOfHeld.lean#L114).

**Raise a decay estimate to a power** · theorem. `pow_le_of_decay`: The pointwise decay hypothesis yields the corresponding power bound with the required radial exponent. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SigmaProfileOfHeld.lean#L117).

**Nonnegative certificate decay constant** · theorem. `decay_nonneg`: The certified decay constant is nonnegative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SigmaProfileOfHeld.lean#L127).

**Certified profile slices are C2** · theorem. `profile_slice`: At a certified parameter, every spatial profile slice is twice continuously differentiable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SigmaProfileOfHeld.lean#L132).

**The certified profile is jointly C2** · theorem. `profile_joint`: The certified approximate profile is twice continuously differentiable jointly in time and space. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SigmaProfileOfHeld.lean#L135).

**Sixth-power decay of the profile** · theorem. `profile_sixth`: The sixth power of the profile norm is bounded by the sixth power of the decay constant times radial decay of order six. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SigmaProfileOfHeld.lean#L139).

**Squared gradient decay** · theorem. `profile_grad_sq`: The squared profile-gradient norm is bounded by the squared decay constant times radial decay of order four. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SigmaProfileOfHeld.lean#L145).

**Squared Hessian decay** · theorem. `profile_secondDeriv_sq`: The squared profile-Hessian norm is bounded by the squared decay constant times radial decay of order six. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SigmaProfileOfHeld.lean#L151).

**Corrected-field sixth-power bound** · theorem. `sixth_bound`: The profile decay and correction L6 bound give a uniform sixth-power integral bound for their sum. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SigmaProfileOfHeld.lean#L157).

**An L2 bound for the corrected gradient** · theorem. `grad_bound`: The profile-gradient decay and correction gradient bound give a uniform squared-gradient integral bound for their sum. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SigmaProfileOfHeld.lean#L171).

**The corrected Hessian has finite energy** · theorem. `secondDeriv_finite_of_period`: The profile decay and correction's period Hessian bound make the full corrected Hessian square integrable over one period. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SigmaProfileOfHeld.lean#L186).

**Corrected gradient has weak derivatives** · theorem. `weak_secondDeriv_sum`: Each column of the corrected gradient has the corresponding corrected Hessian column as a weak gradient. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SigmaProfileOfHeld.lean#L207).

**Corrected field remains divergence free** · theorem. `divergence_sum`: The profile and correction divergence identities imply zero trace of their summed gradient almost everywhere. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SigmaProfileOfHeld.lean#L225).

**Profile Hessian is jointly measurable** · theorem. `measurable_secondDeriv_profile`: The certified profile's spatial Hessian is a measurable function of space-time. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SigmaProfileOfHeld.lean#L236).

**Source namespace `Breakdown.Cert`.**

**Assemble the corrected weak profile** · theorem. `sigmaProfileOfHeldHolds_of`: The reading, bounds, nonvanishing and weak-equation interfaces give the weak similarity profile exported by a zero-multiplier held solution. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SigmaProfileOfHeld.lean#L247).

### Breakdown.Cert.SliceFields

This file reconstructs gradient and Hessian fields from Fourier derivative columns and proves their slice energy identities. Section 7.5: support for physical graph-space readings.

**Source namespace `Breakdown.Cert.Internal.SliceFields`.**

**Assemble a gradient from columns** · definition. `gradField`: The gradient field is the continuous linear map whose coordinate columns are the supplied vector fields. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SliceFields.lean#L19).

**Apply the assembled gradient** · theorem. `gradField_apply`: Applying the assembled gradient to a vector contracts its coordinates with the supplied columns. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SliceFields.lean#L23).

**Recover a chosen gradient column** · theorem. `gradField_unit`: Applying the assembled gradient to a coordinate basis vector returns that column. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SliceFields.lean#L27).

**L2 columns give an L2 gradient** · theorem. `memLp_gradField`: If every column lies in L2, the assembled linear-map field lies in L2. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SliceFields.lean#L31).

**Assemble a Hessian from double columns** · definition. `secondDerivField`: The second-derivative field assembles the supplied two-index columns into a continuous bilinear map. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SliceFields.lean#L37).

**Apply the assembled Hessian** · theorem. `secondDerivField_apply`: The assembled Hessian acts by the double coordinate contraction of its supplied columns. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SliceFields.lean#L40).

**Recover one Hessian coefficient** · theorem. `secondDerivField_unit`: Applying the Hessian to two coordinate basis vectors returns the corresponding supplied coefficient field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SliceFields.lean#L45).

**A flipped Hessian column** · theorem. `flip_secondDerivField`: Fixing the second argument of the Hessian gives the gradient assembled from the corresponding column family. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SliceFields.lean#L49).

**The Hessian trace is a diagonal sum** · theorem. `secondDerivTrace_secondDerivField`: The trace of the assembled Hessian is the sum of its diagonal coefficient fields. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SliceFields.lean#L57).

**Bound the Hessian by its coefficients** · theorem. `norm_secondDerivField_sq_le`: The squared operator norm of the assembled Hessian is bounded by the sum of squared norms of all its coordinate coefficients. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SliceFields.lean#L61).

**Spatial L2 representatives have energy** · theorem. `integrable_norm_sq_L2R`: The squared norm of a spatial L2 representative is integrable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SliceFields.lean#L76).

**Integrate a spatial representative** · theorem. `integral_norm_sq_L2R`: The integral of the squared representative norm equals the squared spatial L2 norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SliceFields.lean#L79).

**The derivative norms recover the energy** · theorem. `sum_norm_partialX_sq`: The sum of the squared norms of the three physical derivatives equals the squared energy-space norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SliceFields.lean#L82).

**Second derivative trace has a minus sign** · theorem. `sum_partialX_derivX`: The sum of the represented repeated derivatives is the negative physical reading of the graph second part. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SliceFields.lean#L86).

**The velocity derivative columns** · definition. `velGrad`: The velocity-gradient column family consists of the three represented physical derivatives of the energy-space input. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SliceFields.lean#L91).

**The velocity Hessian columns** · definition. `velSecondDeriv`: The Hessian column family applies each physical derivative to each normalized Fourier derivative of the graph second part. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SliceFields.lean#L93).

**Energy-space velocities belong to L6** · theorem. `lintegral_sixth_lt_top`: The represented velocity of any energy-space element has finite sixth-power integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SliceFields.lean#L96).

**Source namespace `Breakdown.Cert`.**

**Construct the complete physical slice** · theorem. `slice_fields`: A square-root Laplacian graph pair admits physical gradient and Hessian fields with weak derivatives, zero divergence, L6 velocity and exact gradient and Hessian-trace energies. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SliceFields.lean#L106).

### Breakdown.Cert.SliceFieldsBound

This file supplies the finite-dimensional bilinear norm estimate used when assembling a Hessian from its coefficients. Section 7.5: support for Hessian norm bounds.

**Bound a double coordinate contraction** · theorem. `norm_double_sum_le`: A bilinear coefficient sum is bounded by the two input norms times the square root of the sum of coefficient norms squared. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SliceFieldsBound.lean#L9).

### Breakdown.Cert.SliceFieldsDivergence

This file proves that physical velocities reconstructed from the solenoidal Fourier space have zero weak divergence. Section 7.5: support for solenoidal physical readings.

**Source namespace `Breakdown.Cert.Internal.SliceFieldsDivergence`.**

**The represented divergence map** · definition. `divMap`: The divergence map adds the matching coordinate of each represented derivative column and encodes the scalar result in one vector coordinate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SliceFieldsDivergence.lean#L16).

**Divergence is the derivative trace** · theorem. `divMap_ae`: The represented divergence agrees almost everywhere with the trace of the physical derivative columns, encoded in the first coordinate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SliceFieldsDivergence.lean#L20).

**Test fields have zero divergence** · theorem. `divMap_embed`: The divergence map vanishes on embedded divergence-free test fields. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SliceFieldsDivergence.lean#L36).

**Energy-space fields are divergence-free** · theorem. `divMap_apply_eq_zero`: Density of solenoidal tests extends zero divergence to every element of the energy space. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SliceFieldsDivergence.lean#L46).

**Source namespace `Breakdown.Cert`.**

**The physical derivative trace vanishes** · theorem. `partialX_divergence`: The sum of the diagonal derivative-column coordinates is zero almost everywhere in space. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SliceFieldsDivergence.lean#L57).

### Breakdown.Cert.SliceFieldsIsometry

This file verifies that the real physical reading preserves the L2 norm on reality-symmetric Fourier fields. Section 7.5: support for physical energy identities.

**Source namespace `Breakdown.Cert.Internal.SliceFieldsIsometry`.**

**Split a complex vector into real parts** · theorem. `vec_decomp`: A complex vector is the sum of its complexified real part and i times its complexified imaginary part. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SliceFieldsIsometry.lean#L16).

**The imaginary-part map on L2** · definition. `imagL`: The imaginary-part map takes the real part after multiplication by minus i. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SliceFieldsIsometry.lean#L21).

**Split a complex L2 field** · theorem. `split`: A complex L2 field splits into its complexified real and imaginary parts. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SliceFieldsIsometry.lean#L23).

**Conjugacy changes the sign of i** · theorem. `reflConj_I_smul`: Reflection-conjugation of i times a field is minus i times the reflection-conjugated field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SliceFieldsIsometry.lean#L45).

**Complexification preserves vector norms** · theorem. `norm_complexifyVec'`: Complexifying a real spatial vector preserves its norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SliceFieldsIsometry.lean#L58).

**The real L2 norm is squared energy** · theorem. `l2R_norm_sq`: The squared norm of a real L2 field equals its integrated pointwise squared norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SliceFieldsIsometry.lean#L64).

**Complexification preserves L2 norms** · theorem. `norm_complexify`: Complexifying a real L2 field preserves its L2 norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SliceFieldsIsometry.lean#L70).

**Source namespace `Breakdown.Cert`.**

**The real physical reading is isometric** · theorem. `norm_toPhys_of_mem_sig`: The physical reading of a field in the reality-symmetric solenoidal subspace preserves its L2 norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SliceFieldsIsometry.lean#L83).

### Breakdown.Cert.SliceFieldsSymbol

This file realizes normalized Fourier derivative multipliers within the solenoidal energy space. Section 7.5: support for the gradient and Hessian representation.

**A normalized Fourier derivative map** · definition. `derivOp`: The derivative operator is the L2 Fourier multiplier given by the chosen normalized derivative symbol. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SliceFieldsSymbol.lean#L14).

**The derivative multiplier acts pointwise** · theorem. `derivOp_ae`: The derivative operator agrees almost everywhere with multiplication by its Fourier symbol. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SliceFieldsSymbol.lean#L16).

**Derivative symbols preserve real fields** · theorem. `star_derivSymbol_neg`: Conjugating the derivative symbol at negative frequency gives its value at positive frequency. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SliceFieldsSymbol.lean#L21).

**Complex-linear longitudinal projection** · theorem. `longitudinal_smul`: The longitudinal symbol commutes with complex scalar multiplication. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SliceFieldsSymbol.lean#L25).

**The derivative preserves solenoidality** · theorem. `derivOp_mem`: The normalized derivative multiplier preserves the real solenoidal Fourier subspace. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SliceFieldsSymbol.lean#L31).

**Normalized derivative on energy space** · definition. `derivX`: The derivative multiplier restricts to a continuous linear map on the solenoidal energy space. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SliceFieldsSymbol.lean#L67).

**Unfold the restricted derivative** · theorem. `derivX_coe`: The restricted energy-space derivative has the original Fourier multiplier as its underlying L2 value. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SliceFieldsSymbol.lean#L69).

**Physical derivative from its Fourier map** · theorem. `partialX_eq`: The represented physical derivative is the physical reading of the normalized Fourier derivative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SliceFieldsSymbol.lean#L72).

**Read the energy-space derivative symbol** · theorem. `derivX_ae`: The energy-space derivative agrees almost everywhere in frequency with multiplication by its normalized symbol. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SliceFieldsSymbol.lean#L76).

**Derivative symbol squares sum to one** · theorem. `sum_norm_derivSymbol_sq`: At nonzero frequency, the three normalized derivative-symbol squared norms sum to one. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SliceFieldsSymbol.lean#L81).

**Derivative maps split the energy norm** · theorem. `sum_norm_derivX_sq`: The sum of the squared energy-space derivative norms equals the input energy norm squared. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SliceFieldsSymbol.lean#L87).

**Derivatives preserve the graph relation** · theorem. `halfSsp_derivX`: Applying the same normalized derivative to both graph components preserves their square-root Laplacian relation. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SliceFieldsSymbol.lean#L100).

**Square a normalized derivative symbol** · theorem. `derivSymbol_mul_self`: The square of a normalized derivative symbol is minus the coordinate frequency squared divided by total frequency norm squared. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SliceFieldsSymbol.lean#L106).

**Squared symbols sum to minus one** · theorem. `sum_derivSymbol_mul_self`: At nonzero frequency, the sum of the three squared derivative symbols is minus one. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SliceFieldsSymbol.lean#L113).

**Repeated derivatives sum to minus I** · theorem. `sum_derivX_derivX`: The sum of the three repeated normalized derivatives is the negative of the input energy-space element. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SliceFieldsSymbol.lean#L121).

### Breakdown.Cert.SliceReading

This file replaces exceptional time slices by zero so the selected velocity and gradient satisfy their weak-reading conditions at every time. Section 7: support for the everywhere-in-time weak profile contract.

**Bound a gradient by its columns** · theorem. `norm_gradField_sq_le`: The squared norm of the assembled gradient map is bounded by the sum of its column norms squared. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SliceReading.lean#L15).

**L6 norm gives the sixth-power integral** · theorem. `lintegral_sixth_eq`: The sixth-power integral of an L6 representative equals the sixth power of its norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SliceReading.lean#L36).

**The zero field has zero weak gradient** · theorem. `isWeakGradient_zero`: The zero vector field has the zero linear-map field as a weak gradient. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SliceReading.lean#L49).

**A real time with consistent readings** · proposition definition. `IsGoodTime`: A good real time is one where the velocity, both derivative families and scalar energy match their graph-curve representatives. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SliceReading.lean#L52).

**Consistent readings at a circle time** · proposition definition. `IsGoodAt`: Good data at a circle time agree almost everywhere with the graph velocity and derivative representatives and have the matching gradient energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SliceReading.lean#L61).

**Real and circle good times agree** · theorem. `isGoodTime_iff`: The good-time predicate at a real time is exactly the good-data predicate at its time-circle class. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SliceReading.lean#L68).

**Good times repeat every period** · theorem. `isGoodTime_add_one`: For periodic reading data, a real time is good exactly when the time one period later is good. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SliceReading.lean#L73).

**Velocity restricted to good slices** · definition. `goodVel`: The chosen velocity keeps the supplied velocity on good time slices and is zero on all other slices. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SliceReading.lean#L87).

**Gradient restricted to good slices** · definition. `goodGrad`: The chosen gradient uses the supplied columns on good time slices and the zero map otherwise. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SliceReading.lean#L92).

**The chosen velocity agrees at good times** · theorem. `goodVel_of_good`: At a good time, the chosen velocity equals the original velocity field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SliceReading.lean#L101).

**Chosen velocity vanishes at bad times** · theorem. `goodVel_of_not`: At a time that is not good, the chosen velocity is identically zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SliceReading.lean#L105).

**The chosen gradient agrees at good times** · theorem. `goodGrad_of_good`: At a good time, the chosen gradient is the map assembled from the supplied columns. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SliceReading.lean#L109).

**Chosen gradient vanishes at bad times** · theorem. `goodGrad_of_not`: At a time that is not good, the chosen gradient is the zero map. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SliceReading.lean#L114).

**Good slices have the full weak reading** · theorem. `good_slice`: A good time supplies weak first and second derivatives, the signed Hessian-trace identity and the graph-controlled Hessian bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SliceReading.lean#L118).

**Good slices are divergence free** · theorem. `divergence_of_good`: At a good time, the assembled gradient has zero trace almost everywhere in space. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SliceReading.lean#L129).

**An energy bound gives an L6 bound** · theorem. `sixth_le_of_ae`: A velocity representative of an energy-space element obeys the sixth-power bound supplied by the velocity embedding and the energy bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SliceReading.lean#L138).

**Assembled gradient has bounded energy** · theorem. `grad_le_of_ae`: Derivative-column representatives bound the assembled gradient's squared integral by the energy-space norm squared. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SliceReading.lean#L154).

**Uniform L6 control on good slices** · theorem. `sixth_le_of_good`: The scalar energy bound gives the stated sixth-power velocity bound at every good time. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SliceReading.lean#L177).

**Gradient energy on good slices** · theorem. `grad_le_of_good`: At a good time, the assembled gradient energy is bounded by the graph gradient-part norm squared. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SliceReading.lean#L183).

**Representative Hessian has finite energy** · theorem. `secondDeriv_lt_top_of_good`: The good-slice representatives have finite period Hessian energy under the graph second-part bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SliceReading.lean#L188).

**A reading valid at every time** · theorem. `exists_everywhere_reading`: The energy hypotheses give a periodic reading with weak gradient and zero divergence at every time, uniform velocity and gradient bounds, and finite period Hessian energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SliceReading.lean#L207).

### Breakdown.Cert.SpaceModulus

This file bounds spatial translations of the physical reading by the corresponding graph derivative norms. Section 7.8: support for the local compactness argument.

**Source namespace `Breakdown.Cert.Internal.SpaceModulus`.**

**Bound a derivative in one direction** · theorem. `norm_apply_sq_le`: The squared norm of a linear map applied to a shift is bounded by the shift norm squared times the sum of column norms squared. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SpaceModulus.lean#L19).

**Average energy bounds the average vector** · theorem. `norm_intervalIntegral_sq_le`: The squared norm of an integral over the unit interval is bounded by the integral of the squared norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SpaceModulus.lean#L39).

**A spatial difference is a line integral** · theorem. `sub_eq_intervalIntegral`: A smooth field's difference along a shift equals the integral of its directional derivative along the joining segment. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SpaceModulus.lean#L63).

**Bound a shift by derivative energy** · theorem. `lintegral_translate_sub_le`: The squared L2 norm of a smooth spatial translation difference is bounded by shift length squared times gradient energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SpaceModulus.lean#L77).

**Approximate an energy field by tests** · theorem. `exists_test_seq`: Every energy-space element admits solenoidal test approximants converging in energy and almost everywhere to its velocity. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SpaceModulus.lean#L125).

**Translation bounds pass to limits** · theorem. `lintegral_translate_le_of_tendsto`: An almost everywhere limit of fields with the common translation-energy bound inherits that bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SpaceModulus.lean#L144).

**The velocity translation estimate** · theorem. `lintegral_velocity_translate_sub_le`: The velocity's squared L2 translation difference is bounded by shift length squared times its energy-space norm squared. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SpaceModulus.lean#L166).

**A ball version of the shift estimate** · theorem. `slice_bound`: A represented velocity obeys the same shift-energy bound after restricting the integral to a spatial ball. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SpaceModulus.lean#L177).

**A local norm from its energy bound** · theorem. `periodBallNorm_le`: The stated nonnegative local period energy bound yields the corresponding local period-norm bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SpaceModulus.lean#L187).

**The selected reading is valid** · theorem. `Breakdown.Cert.SpaceModulus.isReadingOf_readingOf`: The selected velocity, gradient and second-derivative representatives give a valid physical reading of the correction. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SpaceModulus.lean#L207).

**One normalized derivative is contractive** · theorem. `norm_derivX_sq_le`: The squared norm of one normalized energy-space derivative is at most the input norm squared. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SpaceModulus.lean#L216).

**Integrate a scaled gradient energy** · theorem. `integral_scaled_gradSq`: The time integral of shift length squared times slice gradient energy equals the square of shift length times the gradient-map norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SpaceModulus.lean#L221).

**Integrate a scaled second-part energy** · theorem. `integral_scaled_secondSq`: The analogous second-part integral equals the square of shift length times the second-map norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SpaceModulus.lean#L227).

**Spatial shifts of velocity are small** · theorem. `velocity_part`: The local period norm of the velocity shift difference is at most shift length times the gradient-map norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SpaceModulus.lean#L233).

**A gradient column is another velocity** · theorem. `column_eq`: Each gradient column is almost everywhere the velocity reading of a normalized derivative of the graph second part. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SpaceModulus.lean#L244).

**Control shifts of gradient columns** · theorem. `column_part`: The local period norm of a gradient-column shift difference is at most shift length times the second-map norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SpaceModulus.lean#L258).

**Source namespace `Breakdown.Cert`.**

**Assemble the spatial translation bounds** · theorem. `spaceModulusHolds_of`: The graph and reading interfaces establish both velocity and gradient-column spatial translation estimates. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SpaceModulus.lean#L277).

### Breakdown.Cert.StConclusion

This file records the normalized-time weak profile contract produced at the end of the held construction. Section 7.8: the exported nonlinear weak profile object.

**A nonzero normalized-time weak profile** · structure. `IsSigmaProfile`: The predicate packages a positive period, measurable fields, periodic nonzero velocity, a weak gradient on every time slice, a weak Hessian on almost every slice, divergence-free slices, uniform sixth-power and gradient-energy bounds, finite period Hessian energy and the unforced weak equation. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/StConclusion.lean#L18).

### Breakdown.Cert.SupBound

This file converts the local free-energy identity and the frozen-form estimate into a global-in-time gradient bound. Section 7.7: support for the supremum bound in the bordered estimate.

**Source namespace `Breakdown.Cert.Internal.SupBound`.**

**Control energy growth on an interval** · theorem. `sub_le_of_identity`: The integrated energy identity bounds the growth between two times by the accumulated nonnegative forcing term. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SupBound.lean#L18).

**Period averaging bounds each time value** · theorem. `le_of_identity`: The energy identity and periodic averaging bound each value by its mean plus the scaled forcing integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SupBound.lean#L32).

**An L2 energy integral equals the norm** · theorem. `integral_norm_sq_eq`: The integral of a representative's squared norm equals its L2 norm squared. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SupBound.lean#L85).

**Two L2 norms have an integrable product** · theorem. `integrable_norm_mul`: The product of the pointwise norms of two L2 fields is integrable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SupBound.lean#L93).

**Take the square root of L2 energy** · theorem. `rpow_integral_eq`: The square root of the squared-norm integral equals the L2 norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SupBound.lean#L103).

**Cauchy-Schwarz for norm products** · theorem. `integral_norm_mul_le`: The integral of the product of pointwise norms is at most the product of the two L2 norms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SupBound.lean#L109).

**Bounded weights preserve squared energy** · theorem. `Breakdown.Cert.SupBound.integrable_weighted`: A bounded nonnegative weight makes the weighted squared norm of an L2 field integrable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SupBound.lean#L120).

**Continuity estimate for weighted energy** · theorem. `weighted_sub_le`: The difference of two weighted energies is bounded by the weight bound times their L2 difference norm times the sum of their L2 norms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SupBound.lean#L127).

**Weighted L2 energy is continuous** · theorem. `continuous_weighted`: For a bounded weight, the weighted squared-norm integral depends continuously on the L2 field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SupBound.lean#L151).

**Expand weighted energy by derivatives** · theorem. `sliceWeightedGrad_eq`: The weighted slice gradient energy is the sum of the three weighted derivative-column energy integrals. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SupBound.lean#L161).

**Weighted slice energy is continuous** · theorem. `continuous_sliceWeightedGrad`: The weighted gradient energy is a continuous function of the energy-space element. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SupBound.lean#L168).

**The weight controls unweighted energy** · theorem. `Breakdown.Cert.SupBound.sliceWeightedGrad_ge`: A positive lower bound on the weight bounds the weighted slice energy below by that constant times the squared energy-space norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SupBound.lean#L176).

**The upper weight controls slice energy** · theorem. `sliceWeightedGrad_le`: A pointwise upper bound on the weight bounds the weighted slice gradient energy by that constant times the unweighted energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SupBound.lean#L185).

**A slice bound gives a finite supremum** · theorem. `supGrad_bound`: A common bound on the represented slice gradient energy gives finite gradient supremum and its squared bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SupBound.lean#L194).

**Source namespace `Breakdown.Cert`.**

**Assemble the gradient supremum estimate** · theorem. `supBoundHolds_of`: The free-energy, frozen-form and certificate-data interfaces yield the specified gradient-supremum estimate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SupBound.lean#L437).

### Breakdown.Cert.SupBoundHalfSsp

This file extends the sharp velocity estimate from smooth tests to all square-root Laplacian graph pairs. Section 7.6: support for the velocity supremum and product bounds.

**Source namespace `Breakdown.Cert.Internal.SupBoundHalfSsp`.**

**The L2 inner product is an integral** · theorem. `inner_eq_integral`: The real Hilbert inner product of two complex L2 fields equals the integral of their pointwise real inner products. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SupBoundHalfSsp.lean#L16).

**The Laplacian energy pairing** · theorem. `inner_eq_norm_sq`: Pairing an energy-space element with its negative Laplacian equals the squared norm of its square-root Laplacian when both graph relations hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SupBoundHalfSsp.lean#L20).

**Heat flow preserves the graph relation** · theorem. `isHalfSspOf_heat`: Applying heat flow to both graph components preserves their square-root Laplacian relation. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SupBoundHalfSsp.lean#L29).

**The pointwise estimate for smooth tests** · theorem. `sq_le_test`: A solenoidal test field satisfies the pointwise velocity bound with coefficient one over twice pi and the corresponding derivative energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SupBoundHalfSsp.lean#L37).

**Approximate energy and its pairing** · theorem. `exists_test_near`: A square-root Laplacian graph pair admits solenoidal tests close in energy with derivative pairing arbitrarily close from above to the second-part energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SupBoundHalfSsp.lean#L52).

**Source namespace `Breakdown.Cert`.**

**The sharp pointwise graph estimate** · theorem. `sq_le_of_halfSsp`: A square-root Laplacian graph pair has velocity squared at most its two component norms' product divided by twice pi almost everywhere. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SupBoundHalfSsp.lean#L95).

### Breakdown.Cert.SupBoundRadial

This file evaluates the radial Fourier integral that fixes the constant in the velocity supremum estimate. Section 7.6: support for the sharp interpolation constant.

**Source namespace `Breakdown.Internal.SupBoundRadial`.**

**Optimizing square-root scale is positive** · theorem. `sqrt_scale_pos`: For positive coefficients, the square root of their ratio is positive. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SupBoundRadial.lean#L12).

**Simplify the optimizing scale** · theorem. `mul_sqrt_scale`: For positive coefficients, the first coefficient times the square root of their ratio equals the square root of their product. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SupBoundRadial.lean#L15).

**An arctangent antiderivative** · theorem. `hasDerivAt_prim`: The scaled arctangent has derivative equal to the reciprocal quadratic radial denominator. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SupBoundRadial.lean#L21).

**The antiderivative's limit at infinity** · theorem. `tendsto_prim`: The scaled arctangent tends to pi divided by twice its scaling denominator at positive infinity. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SupBoundRadial.lean#L32).

**The reciprocal quadratic is integrable** · theorem. `integrableOn_Ioi`: For positive coefficients, the reciprocal quadratic radial function is integrable on the positive half-line. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SupBoundRadial.lean#L40).

**Evaluate the radial integral** · theorem. `integral_Ioi`: The positive-half-line integral of the reciprocal quadratic is pi divided by twice the square root of the coefficient product. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SupBoundRadial.lean#L45).

**Cancel the radial Jacobian** · theorem. `radial_eqOn`: For positive radius, the radial Jacobian cancels the quadratic factor in the reciprocal quartic denominator. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SupBoundRadial.lean#L53).

**Unit ball has volume four pi over three** · theorem. `volume_real_ball_one`: The real volume of the spatial unit ball is four pi divided by three. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SupBoundRadial.lean#L63).

**Source namespace `Breakdown`.**

**Reciprocal Fourier weight is integrable** · theorem. `integrable_inv_radial`: The reciprocal sum of positive quadratic and quartic frequency weights is integrable in three-dimensional space. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SupBoundRadial.lean#L72).

**Evaluate the radial Fourier integral** · theorem. `integral_inv_radial`: The integral of the reciprocal quadratic-plus-quartic frequency weight is twice pi squared divided by the square root of the coefficient product. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SupBoundRadial.lean#L79).

### Breakdown.Cert.SupBoundReal

This file optimizes the scalar inequalities used to convert the Fourier integral estimate into the sharp velocity bound. Section 7.6: support for the velocity interpolation inequality.

**A weighted arithmetic-geometric bound** · theorem. `le_half_weighted`: Positive scaling bounds a nonnegative quantity by half the corresponding weighted square plus reciprocal weight. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SupBoundReal.lean#L9).

**Optimize over positive scales** · theorem. `sq_le_of_forall_t`: An inequality valid for every positive auxiliary scale implies the product bound on the square of the target quantity. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SupBoundReal.lean#L18).

**The scaled Fourier supremum estimate** · theorem. `key_bound`: The integral estimates bound the target square by the scale-weighted gradient and Laplacian energies divided by four pi. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SupBoundReal.lean#L47).

**Optimize the gradient-Laplacian balance** · theorem. `sq_le_of_forall_scale`: Optimizing over the positive scale gives the target square bounded by the product of the two energy square roots divided by twice pi. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SupBoundReal.lean#L53).

**Simplify Fourier normalization** · theorem. `sqrt_radial_weight`: The radial integral constant with the Fourier quadratic and quartic weights simplifies to one over four pi. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SupBoundReal.lean#L105).

### Breakdown.Cert.SupBoundTestField

This file proves the pointwise gradient-Laplacian interpolation estimate first for smooth compactly supported fields. Section 7.6: support for the velocity supremum estimate.

**Source namespace `Breakdown.Internal.SupBoundTestField`.**

**Real vectors keep their complex norms** · theorem. `norm_complexifyVec`: Complexification preserves the norm of a real vector. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SupBoundTestField.lean#L18).

**A compact smooth field as a Schwartz map** · definition. `toRapid`: Complexifying a smooth compactly supported field produces a Schwartz function. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SupBoundTestField.lean#L24).

**The Schwartz map has the original values** · theorem. `coe_toRapid`: The Schwartz representative evaluates to the complexified original field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SupBoundTestField.lean#L28).

**Fourier inversion bounds a point value** · theorem. `norm_le_integral`: A Schwartz field's pointwise norm is at most the integral of the norm of its Fourier transform. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SupBoundTestField.lean#L31).

**Frequency coordinates recover its norm** · theorem. `sum_sq_coord`: The sum of squared real frequency coordinates equals the squared Euclidean frequency norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SupBoundTestField.lean#L37).

**Fourier energy of one derivative** · theorem. `norm_sq_transform_partialDeriv`: A coordinate derivative contributes four pi squared times the coordinate frequency squared to the transformed squared norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SupBoundTestField.lean#L41).

**Fourier energy of the full gradient** · theorem. `sum_norm_sq_transform_partialDeriv`: Summing coordinate derivative energies gives four pi squared times frequency norm squared times the transformed squared norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SupBoundTestField.lean#L50).

**The Laplacian of a Schwartz field** · definition. `sspS`: The auxiliary Schwartz Laplacian is the sum of the three repeated coordinate directional derivatives. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SupBoundTestField.lean#L55).

**Square the Fourier derivative factor** · theorem. `coord_sq_complex`: The square of the imaginary Fourier derivative factor is minus four pi squared times the coordinate frequency squared. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SupBoundTestField.lean#L58).

**The Fourier symbol of the Laplacian** · theorem. `transform_sspS`: Fourier transformation sends the Schwartz Laplacian to minus four pi squared times frequency norm squared times the transform. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SupBoundTestField.lean#L66).

**Fourier energy of the Laplacian** · theorem. `norm_sq_transform_sspS`: The transformed Laplacian energy is sixteen pi to the fourth times frequency norm to the fourth times the transformed field energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SupBoundTestField.lean#L72).

**Schwartz fields have finite energy** · theorem. `integrable_norm_sq`: The squared norm of a Schwartz field is integrable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SupBoundTestField.lean#L78).

**The Schwartz derivative reads physically** · theorem. `coe_pd_toRapid`: A coordinate derivative of the Schwartz representation equals the complexified physical derivative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SupBoundTestField.lean#L82).

**The Schwartz Laplacian reads physically** · theorem. `coe_sspS_toRapid`: The Schwartz Laplacian equals the complexified physical sum of second partial derivatives. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SupBoundTestField.lean#L86).

**Plancherel for the gradient energy** · theorem. `integral_grad_eq`: The physical gradient energy equals the sum of the Fourier derivative energies. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SupBoundTestField.lean#L93).

**Plancherel for the Laplacian energy** · theorem. `integral_ssp_eq`: The physical Laplacian energy equals the Fourier energy of the Schwartz Laplacian. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SupBoundTestField.lean#L108).

**The zero frequency is a null set** · theorem. `ae_ne_zero`: Almost every spatial frequency is nonzero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SupBoundTestField.lean#L116).

**Source namespace `Breakdown`.**

**The sharp compact-field supremum bound** · theorem. `supBound_test_field`: A smooth compactly supported field has pointwise norm squared at most the product of its gradient and Laplacian L2 norms divided by twice pi. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/SupBoundTestField.lean#L123).

### Breakdown.Cert.TestDense

This file shows that the represented solenoidal space-time test fields separate the forcing Hilbert space. Section 7.5: support for identifying physical and abstract weak equations.

**A smooth test belongs to H1** · theorem. `isH1Field_of_test`: Every spatial test field satisfies the H1 field conditions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TestDense.lean#L17).

**Test's projected Fourier representation** · theorem. `coe_solField_test`: For a solenoidal test, the projected field is its complexified L2 Fourier transform. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TestDense.lean#L21).

**A test gives a square-root graph pair** · theorem. `halfSsp_solField_embed`: The projected test and its energy embedding satisfy the square-root Laplacian relation. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TestDense.lean#L27).

**Test Laplacian gives the next graph pair** · theorem. `halfSsp_embed_solField_negSsp`: The energy embedding of a test and the projected negative Laplacian satisfy the next square-root Laplacian relation. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TestDense.lean#L36).

**Subtract square-root graph pairs** · theorem. `isHalfSspOf_sub`: Subtracting two square-root Laplacian graph pairs preserves the square-root Laplacian relation. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TestDense.lean#L52).

**Subtract full second-derivative pairs** · theorem. `isSspOf_sub`: Subtracting two full second-derivative pairs preserves that derivative relation. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TestDense.lean#L60).

**Transfer derivative orthogonality** · theorem. `inner_eq_zero_of_ssp`: The derivative relation and test orthogonality imply the stated zero inner product. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TestDense.lean#L68).

**Fourier cutoffs remain in the space** · theorem. `exists_mul`: The admissible scalar frequency multiplier applied to an energy-space field has an energy-space representative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TestDense.lean#L101).

**Orthogonality forces annular vanishing** · theorem. `zero_on_annulus`: The orthogonality hypotheses force the Fourier representative to vanish almost everywhere on the specified positive-frequency annulus. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TestDense.lean#L108).

**Tests determine an energy-space element** · theorem. `eq_zero_of_forall_inner`: An energy-space element orthogonal to every allowed test representative is zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TestDense.lean#L190).

**Circle representatives lie in one period** · theorem. `circleRep_mem`: The chosen real representative of a time-circle point belongs to the half-open interval from zero to one. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TestDense.lean#L213).

**Recover a time already in one period** · theorem. `circleRep_coe`: For a real time in the chosen half-open unit interval, taking its circle representative returns that time. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TestDense.lean#L218).

**The circle representative is measurable** · theorem. `measurable_circleRep`: The chosen real representative map on the time circle is measurable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TestDense.lean#L222).

**Separate time and space test factors** · theorem. `isSpaceTimeTestField_prod`: The permitted smooth compact time factor times a spatial test is a space-time test field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TestDense.lean#L225).

**Periodize a supported product test** · theorem. `periodize_prod`: On the specified period interval, periodizing the supported time-space product returns the original product. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TestDense.lean#L240).

**Projecting a scaled test is linear** · theorem. `solField_smul`: Scaling a test before solenoidal projection gives the same scalar multiple of its projected representative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TestDense.lean#L261).

**Represent a separated test** · theorem. `testInHH_prod_ae`: The represented time-space product test equals its time factor times the projected spatial test almost everywhere on the circle. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TestDense.lean#L271).

**Pairing against separated tests** · theorem. `inner_testInHH_prod`: The Hilbert inner product with a separated test equals the time integral of the scalar time factor times the slice pairing. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TestDense.lean#L296).

**Vanishing scalar tests force zero** · theorem. `ae_zero_of_integral`: An integrable scalar function whose compact-test integrals vanish is zero almost everywhere. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TestDense.lean#L305).

**Space-time tests separate slices** · theorem. `ae_inner_zero`: Orthogonality to all separated space-time tests forces the slice pairing with each spatial test to vanish almost everywhere. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TestDense.lean#L340).

### Breakdown.Cert.TestPairing

This file periodizes compact space-time tests and identifies their physical pairings with the forcing Hilbert-space pairing. Section 7.5: support for the weak test-pairing interface.

**A compact test fits in a bounded box** · theorem. `exists_bound`: A compact space-time test has one nonnegative bound for both its time support and spatial support. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TestPairing.lean#L19).

**Each test slice is smooth** · theorem. `slice_contDiff`: Every spatial slice of a space-time test is smooth. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TestPairing.lean#L32).

**Slices vanish outside test support** · theorem. `slice_eq_zero`: A spatial test slice vanishes at points beyond the support bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TestPairing.lean#L36).

**Each test slice has compact support** · theorem. `slice_hasCompactSupport`: Every spatial slice of a compact space-time test has compact support. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TestPairing.lean#L44).

**Each test slice belongs to L2** · theorem. `slice_memLp`: Every smooth compact spatial slice of the test is square integrable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TestPairing.lean#L49).

**The periodized test is a finite sum** · theorem. `periodize_eq_sum`: On the specified unit interval, the periodized compact test is the finite sum of its relevant integer translates. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TestPairing.lean#L53).

**The periodized test repeats every unit** · theorem. `periodize_periodic`: The periodized test is exactly one-periodic in time. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TestPairing.lean#L76).

**Periodization preserves continuity** · theorem. `periodize_continuous`: The compact support makes periodization a jointly continuous space-time field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TestPairing.lean#L85).

**Periodization preserves spatial support** · theorem. `periodize_zero`: The periodized test vanishes outside the original uniform spatial support bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TestPairing.lean#L101).

**A periodized test has finite energy** · theorem. `periodize_lintegral_lt_top`: The period integral of the periodized test's squared norm is finite. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TestPairing.lean#L106).

**The periodized test is a periodic field** · theorem. `periodize_isPeriodicField`: The periodized compact test satisfies joint measurability, periodicity and finite period energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TestPairing.lean#L144).

**Take coordinates through a finite sum** · theorem. `component_sum`: A coordinate of a finite vector sum is the sum of the corresponding coordinates. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TestPairing.lean#L150).

**Periodized slices are solenoidal tests** · theorem. `periodize_slice`: Each periodized slice is smooth, compactly supported and divergence free. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TestPairing.lean#L154).

**L2 fields have integrable pairings** · theorem. `integrable_inner_of_memLp`: The pointwise inner product of two L2 fields is integrable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TestPairing.lean#L174).

**Integer shifts preserve periodic values** · theorem. `shift_int`: A one-periodic field has the same value after the indicated integer time shift. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TestPairing.lean#L181).

**Finite-period bounds control slabs** · theorem. `periodic_lintegral_lt_top`: A periodic nonnegative density with finite unit-period integral has finite integral over the given bounded integer time interval. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TestPairing.lean#L187).

**Restrict time before forming the product** · theorem. `restrict_prod_eq`: Restricting space-time volume to a time slab equals restricted time volume times full spatial volume. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TestPairing.lean#L220).

**Periodic fields have finite slab energy** · theorem. `integrableOn_sq`: A periodic square-integrable field has integrable squared norm on each bounded integer time slab. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TestPairing.lean#L225).

**Bound a compactly supported pairing** · theorem. `pairing_bound`: The physical field-test pairing is bounded by the field's squared norm on the support slab plus the test's squared norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TestPairing.lean#L239).

**The physical test pairing is integrable** · theorem. `integrable_pairing`: A periodic square-integrable field pairs integrably with any space-time test. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TestPairing.lean#L258).

**Represent a periodic field in L2** · theorem. `exists_curve`: A physical periodic field gives an L2-valued circle curve whose solenoidal projection represents its forcing Hilbert element. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TestPairing.lean#L280).

**Compute the pairing over one period** · theorem. `inner_eq_of_ae`: Matched representatives identify the Hilbert inner product with the integral of projected slice pairings over the unit time interval. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TestPairing.lean#L306).

### Breakdown.Cert.TimeModulus

This file assembles a time-translation rate for free-inverse velocity and gradient readings, uniformly over a positive interval of periods. Section 7.8: support for compactness in the held-solution limit.

**Source namespace `Breakdown.Cert.Internal.TimeModulus`.**

**The selected reading is valid** · theorem. `Breakdown.Cert.TimeModulus.isReadingOf_readingOf`: The selected velocity, gradient and second-derivative representatives give a valid physical reading of the correction. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulus.lean#L16).

**A local energy bound controls the norm** · theorem. `periodBallNorm_le_of_lintegral_le`: A nonnegative bound on local period squared energy gives the corresponding local period-norm bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulus.lean#L25).

**One square is bounded by the total** · theorem. `le_of_sq_add_le`: A nonnegative component of the squared energy bound is at most the total bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulus.lean#L35).

**Bound the free inverse's second part** · theorem. `second_le_of_freeInv`: The second-part norm of a positive-period free inverse is at most the forcing norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulus.lean#L39).

**Extract the gradient's factor-two bound** · theorem. `le_two_mul_of_sq_add_le`: The weighted quadratic estimate gives the nonnegative gradient bound with factor two. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulus.lean#L43).

**Bound the free inverse's gradient** · theorem. `grad_le_of_freeInv`: The gradient-map norm of the positive-period free inverse is at most twice the forcing norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulus.lean#L47).

**Combine the two vanishing time rates** · theorem. `rate_tendsto`: The maximum of the velocity rate and the square-root gradient rate tends to zero with a positive time shift. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulus.lean#L51).

**Enlarge a squared scalar bound** · theorem. `ofReal_sq_le_max`: Replacing a nonnegative coefficient by its larger maximum preserves the converted squared bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulus.lean#L62).

**The combined rate controls a column** · theorem. `column_algebra`: The scalar column estimate is bounded by the square of the common chosen rate times the forcing scale. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulus.lean#L66).

**Physical solenoidal reading is isometric** · theorem. `Breakdown.Cert.TimeModulus.norm_toPhysH`: The physical reading of a solenoidal Hilbert-space element has the same L2 norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulus.lean#L81).

**Physical reading has norm at most one** · theorem. `toPhysH_opNorm_le`: The physical reading map has operator norm at most one. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulus.lean#L84).

**Pointwise and L2 norms agree** · theorem. `norm_eq_of_ae_norm_eq`: Almost everywhere equality of representative pointwise norms gives equality of the two L2 norms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulus.lean#L87).

**Bound the represented transport forcing** · theorem. `transportCurve_norm_le`: The transport curve norm is at most the forcing norm plus the graph second-part norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulus.lean#L92).

**Sum matched slice energies over a period** · theorem. `periodLIntegral_eq_of_slices`: Matched physical slice energies identify the period integral with the finite sum of the corresponding curve norms squared. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulus.lean#L107).

**Physical and curve forcing norms agree** · theorem. `transportPart_periodLIntegral`: The physical transport forcing's period energy equals the represented transport curve's norm squared. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulus.lean#L127).

**Convert a norm bound to extended energy** · theorem. `enorm_sq_le_ofReal`: A nonnegative real norm bound yields the corresponding extended squared-norm bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulus.lean#L137).

**A controlled free-equation perturbation** · theorem. `perturbation_bound`: A free-inverse reading admits perturbation forcing with period energy bounded by four times the forcing norm squared. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulus.lean#L142).

**The L6-to-local-L2 volume factor** · definition. `ballFactor`: The ball factor is the spatial ball volume raised to the exponent one half minus one sixth. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulus.lean#L162).

**The ball factor is finite** · theorem. `ballFactor_ne_top`: The finite spatial ball volume gives a finite local embedding factor. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulus.lean#L165).

**L6 controls L2 on a finite ball** · theorem. `ball_lintegral_le`: The squared local L2 energy of an L6 field is bounded by its L6 norm times the ball factor, squared. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulus.lean#L170).

**Multiply two converted squared factors** · theorem. `ofReal_sq_mul_sq`: The product of two converted scalar squares equals the conversion of the squared product. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulus.lean#L179).

**A local velocity energy bound** · theorem. `slice_velocity_le`: The local squared velocity integral is bounded by the squared velocity-map norm and ball factor times the energy-space norm squared. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulus.lean#L184).

**Real and extended squared norms agree** · theorem. `ofReal_norm_sq_eq`: Converting a real squared norm to the extended nonnegative reals gives the squared extended norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulus.lean#L193).

**Read a finite extended product bound** · theorem. `enorm_factor_eq`: For the finite factor used here, the product of extended squared norms equals the converted real squared product. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulus.lean#L197).

**Physical velocity has the local bound** · theorem. `velocity_ball_slice`: A physical velocity representative inherits the local L2 bound from its energy-space element. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulus.lean#L207).

**Integrate a common slice-energy bound** · theorem. `period_const_mul_le`: A pointwise bound by a constant times represented slice energy integrates to that constant times the curve norm squared. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulus.lean#L215).

**The local velocity period estimate** · theorem. `local_velocity_le`: A physical reading's local period velocity energy is bounded by the gradient-map norm and the local embedding constant. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulus.lean#L226).

**A uniform local embedding constant** · theorem. `local_velocity_bound`: At a fixed radius, one nonnegative constant controls every reading's local velocity period energy by its graph gradient norm squared. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulus.lean#L243).

**Split the extended derivative norm** · theorem. `sum_enorm_partialX_sq`: The three derivative extended squared norms sum to the input extended squared norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulus.lean#L250).

**Time-integrated derivative-column bound** · theorem. `sum_enorm_column_le`: The sum of the lifted derivative-column energies is bounded by the graph gradient-map energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulus.lean#L254).

**Bound physical energy by graph energy** · theorem. `gradient_energy_bound`: The physical period matrix energy is at most the graph gradient-map norm squared. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulus.lean#L282).

**Square an ordered nonnegative bound** · theorem. `sq_le_of_le`: An ordered pair of nonnegative real bounds remains ordered after squaring and conversion to extended reals. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulus.lean#L296).

**Choose a common forcing scale** · theorem. `velocity_algebra`: The enlarged forcing coefficient simultaneously bounds the forcing and local velocity terms required by the time-shift estimate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulus.lean#L299).

**Write the time rate as a square** · theorem. `sqrt_rate_sq`: The linear-in-shift energy coefficient equals the square of its square-root time rate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulus.lean#L305).

**A vanishing velocity time-shift rate** · theorem. `velocity_shift_bound`: Uniformly over the positive period interval, the local velocity shift energy is bounded by a nonnegative rate tending to zero times the forcing norm, squared. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulus.lean#L311).

**Source namespace `Breakdown.Cert`.**

**A common time-translation rate** · theorem. `timeModulusHolds_of`: The velocity and gradient estimates combine into the uniform vanishing time-translation rate required by the compactness interface. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulus.lean#L345).

### Breakdown.Cert.TimeModulusGradient

This file converts a local velocity time-shift estimate into one for gradient columns using a larger spatial ball and the graph second-part bound. Section 7.8: support for local compactness of free-inverse readings.

**Source namespace `Breakdown.Cert.Internal.TimeModulus`.**

**Local gradient interpolation** · theorem. `slice_local_bound`: On a fixed ball, gradient-column energy is bounded by the nearby velocity energy and the graph second-part norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusGradient.lean#L16).

**Source namespace `Breakdown.Cert.Internal.TimeModulus.GradientShift`.**

**Norm bound gives extended squared energy** · theorem. `enorm_sq_le_of_norm_le`: A nonnegative real norm bound implies the corresponding extended squared-norm bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusGradient.lean#L26).

**Real and extended squared norms match** · theorem. `ofReal_sq_norm_eq`: The conversion of a real squared norm equals the extended squared norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusGradient.lean#L31).

**Real-time shifts preserve null sets** · theorem. `ae_shift`: An almost everywhere statement in real time remains true after a time shift. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusGradient.lean#L35).

**Circle-time shifts preserve null sets** · theorem. `ae_shift_circle`: An almost everywhere statement on the time circle remains true after a circle shift. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusGradient.lean#L38).

**The graph-slice time difference** · definition. `shiftDiff`: The shift difference subtracts a graph slice from the slice at the shifted time. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusGradient.lean#L42).

**Local energy of a velocity time shift** · definition. `shiftBallEnergy`: The shift energy is the spatial ball integral of the squared velocity difference at two times. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusGradient.lean#L45).

**Second-part size of a time difference** · definition. `shiftSecondNorm`: The shifted second-part norm is the extended norm of the second graph component of the time difference. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusGradient.lean#L48).

**Velocity of a graph difference** · theorem. `velocity_shiftDiff_ae`: The velocity of the graph-slice difference equals the difference of the two slice velocities almost everywhere. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusGradient.lean#L50).

**Derivative of a graph difference** · theorem. `partialX_shiftDiff_ae`: A derivative of the graph-slice difference equals the difference of the two represented derivatives almost everywhere. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusGradient.lean#L61).

**Read physical velocity time differences** · theorem. `slice_diff_velocity`: For almost every time, the physical velocity difference represents the velocity of the graph-slice difference. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusGradient.lean#L72).

**Read physical gradient time differences** · theorem. `slice_diff_column`: For almost every time, the physical gradient-column difference represents the derivative of the graph-slice difference. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusGradient.lean#L81).

**Time-shift pullback preserves measure** · theorem. `shiftLp_eq`: The L2 time-shift map is pullback along the measure-preserving circle translation. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusGradient.lean#L92).

**A time shift preserves the L2 norm** · theorem. `shiftLp_norm`: The L2 norm of a time-shifted curve equals the original norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusGradient.lean#L96).

**A shifted difference has a double bound** · theorem. `shift_sub_norm_le`: The norm of a time-shift difference is at most twice the original curve norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusGradient.lean#L100).

**Read the shifted second-part curve** · theorem. `shift_sub_ae`: The second-map time-shift difference represents the second part of the graph-slice difference almost everywhere. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusGradient.lean#L104).

**Bound the period second-part difference** · theorem. `second_shift_lintegral`: The period integral of the squared shifted second-part norm is at most four times the original second-map norm squared. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusGradient.lean#L122).

**The second-part shift size is measurable** · theorem. `second_shift_aemeasurable`: The shifted second-part norm is almost everywhere measurable over one time period. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusGradient.lean#L140).

**The local shift energy is measurable** · theorem. `velocity_diff_aemeasurable`: The local velocity shift energy is almost everywhere measurable as a function of time. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusGradient.lean#L151).

**Combine the two gradient-shift terms** · theorem. `final_algebra`: The scalar estimate combines the product and squared-velocity terms into the common coefficient used after integration. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusGradient.lean#L169).

**Take the root of an extended bound** · theorem. `sqrt_bound`: The asserted extended squared bound implies the corresponding square-root bound by the nonnegative real constant. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusGradient.lean#L177).

**Squaring the extended square root** · theorem. `rpow_half_sq`: Squaring the half power of a nonnegative extended real returns the original value. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusGradient.lean#L183).

**The slice gradient-shift estimate** · theorem. `pointwise_shift_bound`: Almost every gradient-column shift energy is controlled by the larger-ball velocity shift energy and the shifted second-part norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusGradient.lean#L187).

**Integrate the local gradient-shift bound** · theorem. `integrated_bound`: The scalar energy and second-part bounds control the period integral of the gradient-shift majorant. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusGradient.lean#L215).

**Source namespace `Breakdown.Cert.Internal.TimeModulus`.**

**A uniform gradient time-shift estimate** · theorem. `gradient_shift_bound`: A larger-ball velocity shift bound gives a smaller-ball gradient shift bound by a fixed constant times velocity size times second-part norm plus velocity size squared. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusGradient.lean#L247).

### Breakdown.Cert.TimeModulusRepresentation

This file derives an almost everywhere time-integral formula from the weak transport equation, with the local integrability needed to test it. Section 7.8: support for the velocity time-translation estimate.

**Velocity's normalized time derivative** · definition. `transportRate`: The transport rate is the period times the forcing minus the linear velocity and radial-gradient contributions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusRepresentation.lean#L16).

**Integrate a scalar test backwards** · definition. `shiftIntegral`: The shifted test integral averages the scalar test along the backward time segment of the chosen length. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusRepresentation.lean#L20).

**The error in the time-integral formula** · definition. `transportDefect`: The transport defect is the velocity time difference minus the integral of its proposed transport rate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusRepresentation.lean#L23).

**Integrating shifts preserves smoothness** · theorem. `contDiff_shift_integral`: Integrating translates of a compactly supported smooth function over a finite interval preserves its stated smoothness. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusRepresentation.lean#L27).

**Differentiate the shifted test integral** · theorem. `hasDerivAt_shiftIntegral`: The time derivative of the shifted test integral is the original test minus its backward time shift. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusRepresentation.lean#L65).

**The shifted test has compact support** · theorem. `shiftIntegral_support`: The time-integrated test has compact support and keeps its spatial projection within the original test support. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusRepresentation.lean#L83).

**The integrated test is admissible** · theorem. `shiftIntegral_test`: The integrated scalar test is smooth, compactly supported and stays inside the specified spatial ball. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusRepresentation.lean#L98).

**Periodic energy is equal on unit strips** · theorem. `unit_strip_lintegral`: The nonnegative integral of a periodic density is the same on every integer-translated unit time strip. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusRepresentation.lean#L113).

**Fubini for a time-space rectangle** · theorem. `iter_lintegral_eq_prod`: The iterated nonnegative time and space integrals equal the nonnegative integral over their product rectangle. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusRepresentation.lean#L136).

**Control a norm by one plus its square** · theorem. `enorm_le_one_add_sq`: Every extended pointwise norm is at most one plus its real squared norm converted to an extended value. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusRepresentation.lean#L144).

**Local energy gives strip integrability** · theorem. `integrableOn_unit_strip`: The finite-measure and squared-energy hypotheses make the field integrable on an integer unit time strip. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusRepresentation.lean#L150).

**Integrability over finite time strips** · theorem. `integrableOn_strip`: The unit-strip estimates imply integrability over the bounded symmetric time strip. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusRepresentation.lean#L178).

**From strip to local integrability** · theorem. `locallyIntegrableOn_of_strips`: Integrability on all bounded strips gives local integrability on the open spatial cylinder. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusRepresentation.lean#L201).

**Bound a matrix acting on position** · theorem. `norm_apply_sq_le_matSq`: The squared norm of a matrix applied to a vector is bounded by matrix energy times vector norm squared. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusRepresentation.lean#L213).

**Ball energy below full period energy** · theorem. `ball_lintegral_le_period`: A spatially restricted nonnegative period integral is at most the full-space period integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusRepresentation.lean#L231).

**The velocity is locally integrable** · theorem. `integrableOn_velocity_strip`: The physical reading and energy bounds make velocity integrable on each bounded time-and-space cylinder. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusRepresentation.lean#L236).

**Transport forcing is locally integrable** · theorem. `integrableOn_derivative_strip`: The perturbation forcing is integrable on each bounded time-and-space cylinder. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusRepresentation.lean#L243).

**Local integrability of radial gradients** · theorem. `integrableOn_gradient_apply_strip`: The gradient applied to the spatial position is integrable on every bounded cylinder. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusRepresentation.lean#L250).

**The transport rate is locally integrable** · theorem. `integrableOn_rate_strip`: The velocity, gradient and forcing bounds make the transport rate integrable on bounded cylinders. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusRepresentation.lean#L279).

**Time shifts preserve local L1** · theorem. `integrableOn_shift_strip`: A time translate of a field integrable on bounded cylinders remains integrable on the specified cylinder. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusRepresentation.lean#L289).

**Auxiliary time preserves null sets** · theorem. `quasiMeasurePreserving_time_shift`: The joint map adding the auxiliary time coordinate is quasi-measure-preserving for the product volume measures. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusRepresentation.lean#L310).

**Intermediate times stay within the shift** · theorem. `abs_le_of_mem_uIoc`: A time in the unordered interval between zero and the shift has absolute value at most the shift length. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusRepresentation.lean#L324).

**The time average is locally integrable** · theorem. `integrableOn_average_strip`: Integrating time translates over a finite shift interval preserves integrability on bounded cylinders. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusRepresentation.lean#L331).

**The transport rate is jointly measurable** · theorem. `aestronglyMeasurable_rate`: The physical reading and forcing measurability imply joint almost everywhere strong measurability of the transport rate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusRepresentation.lean#L393).

**Transport defect is locally integrable** · theorem. `integrableOn_transportDefect_strip`: The velocity time difference and integrated transport rate give an integrable defect on bounded cylinders. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusRepresentation.lean#L404).

**Compact weights give integrable tests** · theorem. `integrable_smul_of_strips`: Multiplying a locally integrable field by the specified compact scalar weight gives an integrable field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusRepresentation.lean#L415).

**The time derivative is a joint direction** · theorem. `deriv_time_eq`: The derivative in time equals the joint derivative applied to the unit time direction. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusRepresentation.lean#L439).

**Space derivative is a joint direction** · theorem. `fderiv_space_eq`: A spatial derivative of a joint scalar test equals the joint derivative applied to the corresponding spatial direction. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusRepresentation.lean#L445).

**Derivative-weighted fields are L1** · theorem. `integrable_fderiv_smul_of_strips`: The compact derivative-test hypotheses make its directional derivative times the local field integrable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusRepresentation.lean#L453).

**Multiply a local field by a compact test** · theorem. `integrable_test_smul_of_strips`: The compact scalar test times the locally integrable field is integrable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusRepresentation.lean#L471).

**Expand a linear map by its columns** · theorem. `clm_apply_eq_sum`: A continuous linear map applied to a vector is its coordinate-weighted sum of basis-column values. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusRepresentation.lean#L480).

**Coordinate pairings determine a vector** · theorem. `eq_of_inner_unitVector`: Equality of the three coordinate inner products implies equality of the spatial vectors. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusRepresentation.lean#L485).

**Joint tests give compact smooth slices** · theorem. `slice_test`: Each spatial time slice of the scalar test is smooth and compactly supported. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusRepresentation.lean#L492).

**Compact tested directional derivatives** · theorem. `fderiv_apply_compact`: The derivative of a smooth compact test applied to the specified continuous vector field is continuous and compactly supported. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusRepresentation.lean#L499).

**Integration by parts for dilation** · theorem. `slice_radial_identity`: The tested radial derivative integrates to minus the weak radial-gradient term minus three times the original tested field integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusRepresentation.lean#L506).

**Fubini for space-time volume** · theorem. `integral_prod_volume`: An integrable space-time field has integral equal to its iterated time and space integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusRepresentation.lean#L568).

**Spatial integration preserves time L1** · theorem. `integrable_slice_integral`: An integrable space-time field gives an integrable time function after spatial integration. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusRepresentation.lean#L573).

**Translation-invariant space-time volume** · theorem. `isAddLeftInvariant_volume_prod`: Space-time volume is invariant under left addition. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusRepresentation.lean#L578).

**Supported test fits in a finite cylinder** · theorem. `exists_time_bound_of_support`: The compact scalar test support lies in a bounded time interval and the prescribed closed spatial ball. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusRepresentation.lean#L582).

**Bound support under bounded time shifts** · theorem. `shifted_support_subset`: A support point shifted by a bounded time amount remains in the explicitly enlarged finite time cylinder. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusRepresentation.lean#L593).

**A supported scalar-field product is L1** · theorem. `integrable_smul_of_support`: The support and local integrability conditions make the scalar test times the field integrable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusRepresentation.lean#L604).

**Move a time average onto the test** · theorem. `integral_smul_average`: The integral pairing with a forward time average equals pairing the original field with the backward-integrated test. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusRepresentation.lean#L616).

**The weak transport time identity** · theorem. `weak_time_derivative`: The perturbation's weak equation identifies the transport rate as its weak time derivative against compact scalar tests. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusRepresentation.lean#L685).

**The time-formula defect is locally L1** · theorem. `transportDefect_locallyIntegrableOn`: The transport defect is locally integrable throughout the open spatial cylinder. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusRepresentation.lean#L784).

**The tested defect gives a weak identity** · theorem. `integral_smul_transportDefect`: Pairing the transport defect with a scalar test equals the negative weak time identity for the integrated test. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusRepresentation.lean#L791).

**The weak flow satisfies the time formula** · theorem. `transport_representation`: Almost everywhere on the specified ball, the velocity time difference equals the integral of its transport rate over the intervening interval. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusRepresentation.lean#L847).

### Breakdown.Cert.TimeModulusSliceBound

This file proves the local interpolation estimate connecting a gradient column to velocity on a larger ball and the graph second part. Section 7.8: support for gradient time-translation control.

**Squared energy equals extended L2 norm** · theorem. `lintegral_enorm_sq_eq`: The nonnegative squared-norm integral equals the square of the extended L2 seminorm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusSliceBound.lean#L15).

**Read finite L2 energy as a real integral** · theorem. `toReal_sq_eq_integral`: For a finite L2 seminorm, its real square equals the ordinary squared-norm integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusSliceBound.lean#L21).

**Cutoff error is the removed tail norm** · theorem. `cut_norm`: The norm of a frequency-cutoff error equals the L2 norm of the removed frequency portion. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusSliceBound.lean#L30).

**Cut off a graph pair in frequency** · theorem. `cut_pair`: Frequency truncation produces compatible first and second derivative pairs with errors given by their discarded tails. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusSliceBound.lean#L43).

**Approximate a square-root graph pair** · theorem. `halfSsp_test_dense`: A square-root Laplacian graph pair can be approximated simultaneously by an embedded test and its projected negative Laplacian. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusSliceBound.lean#L100).

**A smooth cutoff between two nearby balls** · theorem. `exists_cutoff`: There is a smooth scalar cutoff equal to one on the inner ball and zero with zero derivative outside the larger ball, with uniformly bounded derivative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusSliceBound.lean#L131).

**Differentiate a squared-cutoff field** · theorem. `fderiv_cut_apply`: The derivative of cutoff squared times a test splits into the cutoff derivative term and the weighted test derivative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusSliceBound.lean#L151).

**Absorb the cutoff cross term** · theorem. `cross_bound`: The cutoff cross term is bounded by half the principal derivative energy plus the controlled lower-order error. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusSliceBound.lean#L164).

**A local-to-global Cauchy-Schwarz bound** · theorem. `ball_integral_mul_le`: The product integral over a ball is bounded by the first local L2 norm times the second full-space L2 norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusSliceBound.lean#L177).

**The local derivative bound for tests** · theorem. `test_bound`: On the inner ball, a test derivative's energy is controlled by velocity energy on the larger ball and the global Laplacian norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusSliceBound.lean#L199).

**The real L2 norm on a spatial ball** · definition. `ballNorm`: The ball norm is the real value of the extended L2 norm for volume restricted to the spatial ball. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusSliceBound.lean#L345).

**The ball norm is nonnegative** · theorem. `ballNorm_nonneg`: The real local L2 ball norm is nonnegative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusSliceBound.lean#L348).

**A higher Lp norm controls local L2** · theorem. `ball_eLpNorm_le`: The allowed global Lp norm bounds the local L2 norm with the finite ball-volume factor. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusSliceBound.lean#L351).

**Control the change of a local L2 norm** · theorem. `ballNorm_sub_le`: The local norm of one field is at most the other's plus their global Lp difference norm times the ball factor. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusSliceBound.lean#L363).

**Local norm depends continuously on data** · theorem. `continuous_ballNorm`: Composing the ball norm with the given continuous linear map gives a continuous real function. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusSliceBound.lean#L407).

**The local L2 seminorm is finite** · theorem. `ballNorm_ne_top`: The global Lp hypotheses ensure finite L2 seminorm on every finite spatial ball. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusSliceBound.lean#L419).

**Local energy is the ball norm squared** · theorem. `lintegral_ball_eq`: The nonnegative squared-norm integral on the ball equals the square of the real ball norm converted to extended reals. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusSliceBound.lean#L427).

**Convert the local interpolation bound** · theorem. `ennreal_bound`: The real local interpolation bound gives the displayed extended-real energy inequality. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusSliceBound.lean#L434).

**Projection preserves test-Laplacian norm** · theorem. `norm_solField_negSsp`: The L2 norm of a test's negative Laplacian equals the norm of its solenoidal representative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusSliceBound.lean#L445).

**The local estimate in graph notation** · theorem. `test_pair_bound`: The local derivative estimate for tests is expressed through the embedded velocity and projected negative Laplacian norms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusSliceBound.lean#L451).

**Extend the local estimate to graph pairs** · theorem. `slice_local_bound_holds`: Density extends the local derivative estimate from tests to every square-root Laplacian graph pair. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusSliceBound.lean#L480).

### Breakdown.Cert.TimeModulusTransport

This file integrates the transport representation to bound velocity time shifts by the square root of the shift length. Section 7.8: support for the compactness time modulus.

**Choose a measurable periodic version** · theorem. `exists_measurable_periodic`: The periodic nonnegative density admits an exactly measurable periodic version equal to it almost everywhere. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusTransport.lean#L17).

**Circle integral equals a period integral** · theorem. `lintegral_Icc_circle`: The nonnegative integral on the unit time circle equals the integral of its real pullback over one closed period. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusTransport.lean#L44).

**Period integrals ignore their origin** · theorem. `periodic_lintegral_shift`: The nonnegative integral of a periodic density over one unit interval is invariant under time shifts. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusTransport.lean#L50).

**Integrate a measurable period average** · theorem. `shift_lintegral_of_measurable`: The period integral of a nonnegative time average equals its shift length times the original period integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusTransport.lean#L61).

**Shift a.e. equal representatives** · theorem. `ae_shift_eq`: Almost everywhere equal measurable densities remain equal for almost every auxiliary shift at every fixed base time, for almost every spatial point. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusTransport.lean#L88).

**Bound a periodic time-average integral** · theorem. `shift_period_lintegral_le`: The period integral of the nonnegative time average is at most its shift length times the original period integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusTransport.lean#L99).

**A short time average has a squared bound** · theorem. `sq_norm_intervalIntegral_le`: The squared norm of the integral over a positive time segment is bounded by its length times the integrated squared norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusTransport.lean#L120).

**Bound a matrix-vector product by energy** · theorem. `norm_apply_sq_le`: The squared norm of a matrix applied to a vector is at most its matrix energy times the vector norm squared. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusTransport.lean#L149).

**Matrix energy is nonnegative** · theorem. `matSq_nonneg'`: The sum of squared coordinate-column norms is nonnegative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusTransport.lean#L173).

**Matrix energy is continuous** · theorem. `continuous_matSq'`: The matrix energy depends continuously on the matrix. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusTransport.lean#L176).

**Three squared terms control a sum** · theorem. `three_sq_le`: The square of a three-term real sum is bounded by three times the sum of its squares. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusTransport.lean#L180).

**Bound the transport rate on a ball** · theorem. `rate_sq_le`: A bounded period and spatial radius control the transport rate squared by the forcing, velocity and gradient energies with the explicit common coefficient. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusTransport.lean#L183).

**Replace iterated nonnegative integration** · theorem. `iter_eq_prod`: The iterated time-space nonnegative integral equals the integral on the product rectangle. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusTransport.lean#L212).

**Combine forcing and field energies** · theorem. `ball_energy_le`: The three assumed energy bounds control their sum on the local period cylinder by three copies of the common squared bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusTransport.lean#L221).

**Extract the linear shift-energy rate** · theorem. `final_algebra`: For shifts at most one, the quadratic shift factor is bounded by the chosen linear shift coefficient. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusTransport.lean#L255).

**Control energy of velocity time shifts** · theorem. `transport_shift_bound`: For bounded positive periods, the physical perturbation and energy bounds control local velocity shift energy by a fixed constant times the shift length and energy bound squared. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TimeModulusTransport.lean#L263).

### Breakdown.Cert.TranslationCriterion

This file proves the local compactness criterion by mollifying fields, taking finite nets of the smoothed family and controlling the smoothing error through translations. Section 7.8: support for compactness of held corrections.

**Source namespace `Breakdown.Cert.Internal.TranslationCriterion`.**

**One closed period-and-ball cylinder** · definition. `boxSet`: The compactness box is the closed unit time interval times the closed spatial ball. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TranslationCriterion.lean#L12).

**Volume restricted to the compactness box** · definition. `boxMeasure`: The box measure is space-time volume restricted to the period-and-ball cylinder. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TranslationCriterion.lean#L14).

**The period-and-ball cylinder is compact** · theorem. `isCompact_boxSet`: The product of the closed unit time interval and the closed spatial ball is compact. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TranslationCriterion.lean#L16).

**The compactness cylinder is measurable** · theorem. `measurableSet_boxSet`: The period-and-ball cylinder is a measurable set. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TranslationCriterion.lean#L19).

**The compactness box has finite measure** · instance. `unnamed finite-measure instance`: The anonymous instance supplies finite measure of the restricted period-and-ball cylinder, using its compactness. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TranslationCriterion.lean#L22).

This instance has no written Lean identifier. Its explanation and source location are complete; the generated name must be observed before adding a named graph link. The provided trace helper records that observation without changing the authors' source.

**Local period energy is an L2 seminorm** · theorem. `periodBallLIntegral_eq`: The squared extended L2 seminorm for the box measure equals the local period energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TranslationCriterion.lean#L25).

**The local period norm is the box L2 norm** · theorem. `periodBallNorm_eq`: The local period norm equals the real value of the box-measure L2 seminorm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TranslationCriterion.lean#L43).

**Local energy increases with radius** · theorem. `periodBallLIntegral_mono`: Increasing the radius increases the local period nonnegative integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TranslationCriterion.lean#L49).

**Finite nets for a totally bounded range** · theorem. `exists_finset_net`: The total-boundedness hypothesis gives a finite selection of sequence points approximating every point within the chosen tolerance. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TranslationCriterion.lean#L53).

**Finite uniform nets for field families** · theorem. `exists_uniform_net`: A uniformly bounded equicontinuous family on the compact box has a finite net in uniform distance. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TranslationCriterion.lean#L69).

**Unit-period integrals ignore translation** · theorem. `lintegral_Icc_add`: A measurable periodic density has the same nonnegative integral after any time translation. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TranslationCriterion.lean#L101).

**Move a unit integration interval** · theorem. `lintegral_Icc_shift`: A periodic nonnegative density has the same integral over any unit-length interval. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TranslationCriterion.lean#L119).

**Local period energy is shift invariant** · theorem. `periodBallLIntegral_shift`: Shifting a periodic field in time leaves its local period integral unchanged. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TranslationCriterion.lean#L127).

**Measurability under the coordinate maps** · theorem. `aestronglyMeasurable_comp_map`: The stated quasi-measure-preserving time and space maps preserve joint almost everywhere strong measurability under composition. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TranslationCriterion.lean#L133).

**Finite energy bound gives finite L2 norm** · theorem. `eLpNorm_lt_top_of_bound`: The local period energy bound implies finite extended L2 seminorm on the box. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TranslationCriterion.lean#L139).

**Local differences have finite energy** · theorem. `periodBallLIntegral_sub_lt_top`: Two fields with finite local period energy have a difference with finite local period energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TranslationCriterion.lean#L147).

**Recover an extended norm bound** · theorem. `eLpNorm_le_of_periodBallNorm_le`: A finite local period-norm bound is nonnegative and bounds the corresponding extended L2 seminorm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TranslationCriterion.lean#L158).

**Small shifts fit into a larger ball** · theorem. `lintegral_ball_sub_le`: Shifting the inner-ball integrand by a vector of norm at most one bounds its integral by the integral over the ball enlarged by one. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TranslationCriterion.lean#L171).

**Set the translation rate to zero at zero** · definition. `shiftRate`: The adjusted rate agrees with the original rate away from zero and is exactly zero at zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TranslationCriterion.lean#L198).

**Three periods give the window bound** · theorem. `window_bound`: The energy bound on one period gives three times that bound on the enlarged time window from minus one to two. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TranslationCriterion.lean#L200).

**Combine time and space translations** · theorem. `joint_shift_bound`: The local energy of a joint time-space shift difference is bounded by the square of the sum of the adjusted translation rates. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TranslationCriterion.lean#L234).

**The enlarged smoothing window** · definition. `windowSet`: The smoothing window enlarges time to minus one through two and space to the ball of radius R plus one. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TranslationCriterion.lean#L350).

**A bump with the chosen support radius** · definition. `bumpOfRadius`: The smoothing bump has inner radius half the requested positive radius and outer radius equal to it. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TranslationCriterion.lean#L352).

**A normalized smooth averaging kernel** · definition. `mollifier`: The mollifier is the volume-normalized bump at the chosen positive radius. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TranslationCriterion.lean#L355).

**Mollify the window-restricted field** · definition. `smoothed`: The smoothed field convolves the normalized mollifier with the original field restricted to the enlarged window. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TranslationCriterion.lean#L357).

**Uniform bounds for the smoothed family** · theorem. `smoothed_bounds`: A common window-energy bound gives common pointwise and Lipschitz bounds for all mollified fields at a fixed smoothing radius. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TranslationCriterion.lean#L360).

**Write local energy with the box measure** · theorem. `periodBallLIntegral_eq_lintegral`: The local period squared-norm integral equals the squared extended-norm integral for the box measure. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TranslationCriterion.lean#L443).

**Window-restricted field is integrable** · theorem. `integrable_window`: The finite window-energy bound makes the field restricted to that window integrable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TranslationCriterion.lean#L457).

**Jensen's bound for a normalized weight** · theorem. `lintegral_sq_le_of_lintegral_eq_one`: For a nonnegative averaging weight of integral one, the square of the weighted average is bounded by the weighted average of squares. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TranslationCriterion.lean#L493).

**Left shifts preserve space-time volume** · instance. `isAddLeftInvariant_volume_prod`: The local instance supplies left-translation invariance of space-time volume. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TranslationCriterion.lean#L517).

**Right shifts preserve space-time volume** · instance. `isAddRightInvariant_volume_prod`: The local instance supplies right-translation invariance of space-time volume. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TranslationCriterion.lean#L521).

**Translations control the smoothing error** · theorem. `smoothed_error`: The local smoothing error energy is bounded by the supremum of local energies of shifts within the mollifier radius. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TranslationCriterion.lean#L525).

**Choose a controlled smooth approximation** · theorem. `exists_mollified`: The window-energy hypothesis gives a continuous uniformly bounded Lipschitz approximation with error controlled by small translations. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TranslationCriterion.lean#L646).

**Approximate the whole family uniformly** · theorem. `exists_smooth_approx`: Uniform energy and small-translation bounds give an equicontinuous uniformly bounded approximating family with the requested common local error. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TranslationCriterion.lean#L667).

**Finite nets give a Cauchy subsequence** · theorem. `fundamental_subseq_of_approx`: Uniformly accurate equicontinuous approximations yield a strictly increasing subsequence Cauchy in the local period norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TranslationCriterion.lean#L720).

**Source namespace `Breakdown.Cert`.**

**Compactness from translation bounds** · theorem. `translationCriterionHolds_proof`: The mollification and finite-net argument proves the stated local translation compactness criterion. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/TranslationCriterion.lean#L822).

### Breakdown.Cert.WeakCompact

This file supplies the weak subsequence and weak-closedness tools used in the held-solution limit argument. Section 7.8: support for weak compactness in the Hilbert spaces.

**Source namespace `WeakCompact.Internal`.**

**Bounded sequence has a weak subsequence** · theorem. `limit_in_closed_span`: A bounded sequence in the real Hilbert space has a strictly increasing weakly convergent subsequence with limit norm bounded by the same constant. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/WeakCompact.lean#L9).

**Source root scope.**

**Extract a weakly convergent subsequence** · theorem. `exists_weakly_convergent_subseq`: Every uniformly bounded Hilbert-space sequence admits a strictly increasing subsequence converging against every test vector. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/WeakCompact.lean#L54).

**Closed convex sets contain weak limits** · theorem. `mem_of_weak_limit`: A weak limit of points in a closed convex set belongs to that set. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/WeakCompact.lean#L60).
<!-- /passage:front -->

