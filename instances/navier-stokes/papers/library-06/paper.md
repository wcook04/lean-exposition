
<!-- passage:front -->
# Library guide 6: Breakdown/Cert

**Navier–Stokes pages:** [the paper](../navier-stokes-paper/paper.pdf) · [proof routes](../navier-stokes-routes/paper.md) · [routes in detail](../navier-stokes-route-details/paper.md) · library guide: [1](../navier-stokes-library-01/paper.md) [2](../navier-stokes-library-02/paper.md) [3](../navier-stokes-library-03/paper.md) [4](../navier-stokes-library-04/paper.md) [5](../navier-stokes-library-05/paper.md) **6** [7](../navier-stokes-library-07/paper.md) [8](../navier-stokes-library-08/paper.md) [9](../navier-stokes-library-09/paper.md) [10](../navier-stokes-library-10/paper.md) [11](../navier-stokes-library-11/paper.md) [12](../navier-stokes-library-12/paper.md) [13](../navier-stokes-library-13/paper.md) [14](../navier-stokes-library-14/paper.md) [15](../navier-stokes-library-15/paper.md) [16](../navier-stokes-library-16/paper.md) [17](../navier-stokes-library-17/paper.md) [18](../navier-stokes-library-18/paper.md) [19](../navier-stokes-library-19/paper.md) [20](../navier-stokes-library-20/paper.md) [21](../navier-stokes-library-21/paper.md) [22](../navier-stokes-library-22/paper.md) [23](../navier-stokes-library-23/paper.md) [24](../navier-stokes-library-24/paper.md) [25](../navier-stokes-library-25/paper.md) [26](../navier-stokes-library-26/paper.md) [27](../navier-stokes-library-27/paper.md) [28](../navier-stokes-library-28/paper.md) [29](../navier-stokes-library-29/paper.md) [30](../navier-stokes-library-30/paper.md)

*A plain title and a sentence for each declaration in `Breakdown.Cert.DataContinuity` to `Breakdown.Cert.FreeTransportCirclePairing` of Alpöge and Buckmaster's Lean at `ad53419de079eb8f95f60313473374624a348546`, in the authors' file order. Prepared with AI assistance. The authors have not reviewed it.*

Each paragraph names one declaration and says whether it is a definition, a proposition that the library defines (its name usually ends in `Holds` or `Statement`) or a proved result, then what it states. Click a paragraph to open its Lean on the right.

### Breakdown.Cert.DataContinuity

The parameter argument uses continuity of the tested defect and pinning data. This file proves those statements from the profile's smoothness, decay and parameter dependence. §7: certificate data and the similarity-profile construction

**Source namespace `Breakdown.Cert.Internal.DataContinuity`.**

**Expand a gradient pairing** · theorem. `inner_gradientAt`: The gradient pairing equals the sum of coordinate directional derivatives multiplied by the vector coordinates. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DataContinuity.lean#L13).

**A parameter slice derivative** · theorem. `partial_apply`: A derivative in the spatial variable is the joint derivative applied to a zero parameter component and the spatial direction. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DataContinuity.lean#L17).

**Integrability from compact support** · theorem. `integrable_of_cont_supp`: A continuous compactly supported function is integrable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DataContinuity.lean#L25).

**Pressure disappears against tests** · theorem. `pressure_pairing`: The pressure-gradient pairing with a solenoidal test is integrable and has integral zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DataContinuity.lean#L31).

**The smooth part of the defect** · definition. `smoothPart`: The smooth defect part combines the time derivative, similarity terms, Laplacian and self-advection before pressure and actuator terms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DataContinuity.lean#L102).

**Smooth dependence of profile gradients** · theorem. `contDiff_profile_fderiv`: The approximate profile's spatial derivative has the required joint differentiability in parameter, time and position. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DataContinuity.lean#L107).

**Continuous smooth residual data** · theorem. `continuousOn_smoothPart`: The smooth defect part depends continuously on parameter and time-space within the parameter box. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DataContinuity.lean#L114).

**Continuous residual test pairings** · theorem. `continuousOn_smooth_pairing`: The integral pairing of the smooth defect with a fixed test varies continuously across the parameter box. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DataContinuity.lean#L167).

**Periodic actuator regularity** · theorem. `Breakdown.Cert.DataContinuity.actuator_periodicField`: Each actuator satisfies the periodic-field conditions needed for physical pairings. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DataContinuity.lean#L177).

**Split the tested defect** · theorem. `defect_pairing_eq`: The tested defect is the smooth residual pairing plus the coefficient-weighted actuator pairings. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DataContinuity.lean#L182).

**Continuity of the tested defect** · theorem. `Breakdown.Cert.DataContinuity.continuousOn_defect`: For certificate data satisfying the stated hypotheses, the abstract defect's pairing with a fixed test is continuous on the admissible parameter set. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DataContinuity.lean#L224).

**Nonnegative matrix energy** · theorem. `matSq_nonneg`: The sum of squared matrix-column norms is nonnegative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DataContinuity.lean#L239).

**A matrix pairing estimate** · theorem. `matNorm_bound`: The absolute matrix pairing is bounded by half the sum of three times one operator norm squared and the other matrix energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DataContinuity.lean#L242).

**Square the profile-gradient decay** · theorem. `Breakdown.Cert.DataContinuity.sq_fderiv_le`: The squared profile-derivative norm is bounded by the squared decay constant times inverse fourth-power radial decay. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DataContinuity.lean#L258).

**The measure on the unit-time strip** · theorem. `Breakdown.Cert.DataContinuity.restrict_eq`: The product of restricted time volume and spatial volume equals full time-space volume restricted to the unit-time strip. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DataContinuity.lean#L273).

**Continuity of profile pin values** · theorem. `Breakdown.Cert.DataContinuity.continuousOn_pinValue`: Pairing a fixed pin with the profile gradient varies continuously over the parameter box. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DataContinuity.lean#L277).

**Source namespace `Breakdown.Cert`.**

**Prove continuity of the data** · theorem. `dataContinuityHolds_of`: The tested defect and pin-value estimates establish the analytic data-continuity interface. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DataContinuity.lean#L334).

### Breakdown.Cert.DenseEnergyCurveBand

The free equation is first analyzed on a frequency band where its graph quantities are controlled. This file constructs smooth periodic energy representatives and then lifts the dense-band argument to the graph space. §7.5: the free similarity equation

**Source namespace `Breakdown.Cert.Internal.DenseEnergyBand`.**

**The exterior frequency cutoff** · definition. `bandCut`: The frequency cutoff is zero inside the radius, rises linearly across a unit band and is capped at one. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L19).

**The capped Laplacian-root symbol** · definition. `halfSspCut`: The square-root Laplacian symbol is two pi times the frequency radius capped at the chosen band radius. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L21).

**The exterior cutoff operator** · definition. `bandOp`: The exterior frequency multiplier acts on homogeneous-space frequency data and returns an L² frequency field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L23).

**Fields supported in a frequency ball** · definition. `bandX`: The frequency-band subspace is the kernel of the exterior cutoff operator. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L26).

**The bounded Laplacian-root operator** · definition. `halfSspX`: The capped square-root Laplacian frequency multiplier is restricted to the homogeneous energy space. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L28).

**Heat flow in similarity variables** · definition. `semigroupX`: The similarity semigroup combines heat flow for one minus exponential time with dilation by the exponential scale. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L31).

**The past-time forcing integral** · definition. `mildIntegral`: The mild response integrates the propagated forcing over all positive elapsed times. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L34).

**The frequency band is closed** · theorem. `isClosed_bandX`: The frequency-band subspace is closed. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L38).

**The band cutoff is continuous** · theorem. `bandCut_cont`: The exterior frequency cutoff is continuous. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L41).

**The cutoff is bounded by one** · theorem. `bandCut_le`: The absolute exterior frequency cutoff is at most one. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L45).

**The cutoff outside the band** · theorem. `bandCut_ne_zero`: Beyond the band radius, the exterior frequency cutoff is nonzero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L51).

**The cutoff inside the band** · theorem. `bandCut_eq_zero`: Inside the frequency band, the exterior cutoff vanishes. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L54).

**Band membership through support** · theorem. `mem_bandX_iff`: A homogeneous-space element belongs to the band exactly when its frequency representative vanishes almost everywhere outside that radius. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L59).

**The capped symbol is continuous** · theorem. `halfSspCut_cont`: The capped square-root Laplacian symbol is continuous. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L81).

**A bounded Laplacian-root symbol** · theorem. `halfSspCut_le`: The absolute capped square-root Laplacian symbol is at most two pi times the absolute band radius. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L85).

**The capped symbol is even** · theorem. `halfSspCut_neg`: Negating the frequency leaves the capped square-root Laplacian symbol unchanged. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L94).

**The bounded operator in frequency space** · theorem. `halfSspX_coe`: The underlying frequency element of the bounded square-root Laplacian operator is given by the capped-symbol multiplier. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L98).

**The Laplacian-root multiplier formula** · theorem. `halfSspX_ae`: The bounded square-root Laplacian operator acts almost everywhere by multiplication by its capped symbol. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L104).

**Frequency bands grow with radius** · theorem. `bandX_mono`: Increasing the frequency radius enlarges the band subspace. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L111).

**Laplacian-root action preserves the band** · theorem. `halfSspX_mem_band`: The bounded square-root Laplacian operator preserves the chosen frequency band. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L117).

**Recover the actual Laplacian root** · theorem. `isHalfSspOf_of_mem_band`: On the frequency band, the capped square-root Laplacian operator realizes the actual square-root Laplacian relation. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L122).

**The bounded Laplacian root is symmetric** · theorem. `inner_halfSspX`: The capped square-root Laplacian operator can be moved between the two arguments of the real inner product. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L132).

**Similarity flow preserves the band** · theorem. `semigroupX_mem_band`: The similarity semigroup preserves the chosen frequency band for nonnegative times. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L141).

**The semigroup starts at identity** · theorem. `semigroupX_zero`: At zero elapsed time, the similarity semigroup fixes every homogeneous-space element. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L172).

**Compose heat and dilation families** · theorem. `semigroup_add_of_families`: The heat-dilation relations combine the two successive similarity-time propagations into their summed-time propagation. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L179).

**The similarity semigroup law** · theorem. `semigroupX_add`: Propagating through two nonnegative times equals propagation through their sum. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L216).

**Continuity of the composed propagator** · theorem. `semigroup_continuousOn_of_families`: The heat and dilation continuity hypotheses give continuous similarity propagation on nonnegative times. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L241).

**Continuous similarity trajectories** · theorem. `continuousOn_semigroupX`: For a fixed initial element, similarity propagation is continuous on nonnegative times. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L281).

**Zero cutoff characterizes the band** · theorem. `bandCut_eq_zero'`: Vanishing of the exterior frequency cutoff forces the frequency norm to be at most the band radius. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L293).

**Continuity of the capped symbol** · theorem. `continuous_halfSspCut'`: The capped square-root Laplacian frequency symbol is continuous. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L302).

**Bound the capped symbol** · theorem. `halfSspCut_bound'`: The capped square-root Laplacian symbol is bounded in absolute value by two pi times the absolute radius. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L306).

**Evenness of the capped symbol** · theorem. `halfSspCut_neg'`: The capped square-root Laplacian symbol is unchanged by frequency reflection. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L315).

**Continuity of the band cutoff** · theorem. `continuous_bandCut'`: The exterior frequency cutoff is continuous. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L318).

**The cutoff's absolute bound** · theorem. `bandCut_bound'`: The exterior frequency cutoff has absolute value at most one. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L322).

**The frequency multiplier representation** · theorem. `halfSspX_coe'`: The capped square-root Laplacian operator is represented in ambient frequency L² by multiplication with its capped radial symbol. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L330).

**The pointwise multiplier representative** · theorem. `halfSspX_ae'`: Almost everywhere, the square-root Laplacian action equals the capped symbol times the input representative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L335).

**The cutoff annihilates band data** · theorem. `band_ae'`: The exterior cutoff times a frequency-band representative vanishes almost everywhere. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L341).

**The smoothed Laplacian-root multiplier** · theorem. `smoothH_coe'`: The smoothed square-root Laplacian operator acts on the underlying frequency element by its smoothing symbol. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L354).

**Smooth the Laplacian root by heat** · theorem. `smoothH_eq_heat'`: On frequency-band data, smoothing the square-root Laplacian equals heat flow applied to the bounded square-root Laplacian. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L360).

**The propagator on band-limited data** · theorem. `slicePropagator_eq_of_mem_band`: On the frequency band, the slice propagator is similarity evolution applied to the bounded square-root Laplacian. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L377).

**The complex L² norm integral** · theorem. `normSq_L2C`: The squared complex L² norm equals the integral of the representative's squared norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L390).

**The frequency energy density** · definition. `sqY`: The frequency energy density is the squared norm of the selected L² representative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L403).

**Integrability of frequency energy** · theorem. `integrable_sqY`: The frequency energy density of an L² element is integrable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L405).

**Nonnegative frequency energy** · theorem. `sqY_nonneg`: The frequency energy density is nonnegative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L408).

**The heat-weighted frequency energy** · definition. `heatInt`: The heat energy integral weights the frequency energy density by the squared heat multiplier. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L412).

**The similarity-flow energy formula** · theorem. `norm_sq_semigroupX`: The squared norm of similarity evolution is its exponential scaling factor times the heat-weighted frequency energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L415).

**Differentiate the heat energy at zero** · theorem. `hasDerivAt_heatInt`: At zero heat time, differentiating the heat energy inserts minus eight pi squared times the frequency radius squared. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L440).

**The Laplacian-root energy formula** · theorem. `norm_sq_halfSspX`: The squared bounded square-root Laplacian norm is the frequency integral weighted by four pi squared times the frequency radius squared. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L478).

**The initial energy derivative** · theorem. `hasDerivWithinAt_norm_sq_semigroupX`: The right derivative of similarity-flow energy at zero is minus half the energy minus twice the square-root Laplacian energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L491).

**Periodic continuous curves are bounded** · theorem. `exists_bound_of_periodic`: A continuous periodic curve has a uniform bound on its norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L520).

**Source section `Abstract`.**

**Continuity of the propagator integrand** · theorem. `continuousOn_apply_comp`: Applying the continuously varying propagator to the continuous input curve gives a continuous integrand on nonnegative times. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L533).

**An exponential integrand bound** · theorem. `integrand_bound`: The forcing integrand is bounded almost everywhere by a fixed constant times exponential decay at rate one quarter. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L556).

**The exponential bound is integrable** · theorem. `integrable_bound`: The constant multiple of the quarter-rate exponential decay is integrable over positive elapsed times. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L568).

**Measurability of the mild integrand** · theorem. `aesm_integrand`: The propagated periodic forcing is almost everywhere strongly measurable over positive elapsed times. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L572).

**The mild forcing integral exists** · theorem. `integrable_integrand`: The exponential domination makes the propagated periodic forcing integrable over positive elapsed times. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L581).

**The mild response is continuous** · theorem. `mild_continuous`: The integrated past-time forcing response varies continuously in time. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L589).

**The mild response is periodic** · theorem. `mild_periodic`: A one-periodic forcing produces a one-periodic mild response. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L600).

**The response stays in the subspace** · theorem. `mild_mem`: The mild response stays in the closed invariant subspace containing the propagated forcing. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L607).

**Source sections `Abstract` / `EnergyW`.**

**A contractive propagator bound** · theorem. `norm_apply_le_of`: The propagator does not increase the norm under the supplied decay bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L629).

**Continuity along a forcing curve** · theorem. `continuousOn_apply_of`: The propagator acting on the time-dependent input is continuous on nonnegative times. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L637).

**Integrability of the response kernel** · theorem. `integrableOn_mild_of`: The propagated forcing is integrable over the positive elapsed-time interval. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L654).

**Shift a positive-tail integral** · theorem. `setIntegral_Ioi_shift`: An integral over the tail above a time equals the shifted integrand's integral over positive times. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L673).

**Split the past-time response** · theorem. `mild_split`: The mild response equals the earlier response propagated forward plus the forcing integral over the intervening interval. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L685).

**Differentiate a pairing with a zero term** · theorem. `hasDerivWithinAt_inner_of_zero`: When the second factor vanishes at the base point, the derivative of the inner product is determined by its derivative there. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L709).

**The new forcing at the endpoint** · theorem. `hasDerivWithinAt_rest`: The right derivative of the short forcing integral at its starting time is the period times the current forcing. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L717).

**The mild response energy identity** · theorem. `mild_energy`: The difference of response energies equals the time integral of the forcing pairing and the propagator's quadratic energy rate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L793).

**Source namespace `Breakdown.Cert.Internal.DenseEnergyBand`.**

**The period-scaled energy identity** · theorem. `final_identity`: The period-scaled energy difference equals the integral of forcing pairing minus square-root Laplacian and quarter-weighted energy losses. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L848).

**Continuous finite-band forcing data** · definition. `denseSet`: The dense candidate set consists of Hilbert-space forcing curves represented by continuous periodic curves in some finite frequency band. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L863).

**Add finite-band forcing curves** · theorem. `denseSet_add`: The sum of two continuous finite-band forcing curves again belongs to the candidate dense set. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L867).

**Zero is finite-band forcing data** · theorem. `denseSet_zero`: The zero forcing belongs to the continuous finite-band candidate set. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L878).

**Scale finite-band forcing curves** · theorem. `denseSet_smul`: A real multiple of finite-band forcing data stays in the candidate set. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L883).

**The finite-band forcing submodule** · definition. `denseClass`: The continuous finite-band forcing set is packaged as a real submodule of the forcing Hilbert space. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L891).

**Dominated convergence in L²** · theorem. `tendsto_Lp_two_of_dominated`: Pointwise convergence with the stated square-integrable domination implies convergence of the L² classes. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L897).

**A growing frequency cutoff** · definition. `cutFn`: The cutoff is one on the inner frequency ball, decreases linearly across the boundary band and vanishes outside the enlarged radius. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L931).

**The growing cutoff is continuous** · theorem. `continuous_cutFn`: The growing frequency cutoff is continuous. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L933).

**The growing cutoff is nonnegative** · theorem. `cutFn_nonneg`: The growing frequency cutoff is nonnegative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L936).

**The growing cutoff is at most one** · theorem. `cutFn_le_one`: The growing frequency cutoff is bounded above by one. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L938).

**The growing cutoff's absolute bound** · theorem. `abs_cutFn_le`: The absolute value of the growing frequency cutoff is at most one. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L941).

**The growing cutoff is even** · theorem. `cutFn_neg`: The growing frequency cutoff is unchanged by frequency reflection. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L945).

**Cut off an L² frequency field** · definition. `cutL2`: The L² cutoff operator multiplies a frequency field by the growing scalar cutoff. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L948).

**The cutoff preserves admissibility** · theorem. `cutL2_mem`: The cutoff multiplier preserves the admissible frequency subspace. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L951).

**The cutoff multiplier formula** · theorem. `cutL2_ae`: The L² cutoff acts almost everywhere by pointwise multiplication by its scalar cutoff. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L954).

**Cut off homogeneous-space data** · definition. `cutX`: The L² frequency cutoff is restricted to the homogeneous energy space. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L958).

**The homogeneous cutoff in L²** · theorem. `cutX_coe`: The frequency representative of the homogeneous-space cutoff equals the L² cutoff of the original representative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L960).

**Cutting off does not increase the norm** · theorem. `norm_cutX_le`: The homogeneous-space frequency cutoff has norm at most the input norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L963).

**The exterior cutoff is continuous** · theorem. `continuous_bandCut`: The exterior band cutoff is continuous. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L973).

**The exterior cutoff's absolute bound** · theorem. `abs_bandCut_le`: The exterior band cutoff has absolute value at most one. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L976).

**Complementary cutoffs annihilate** · theorem. `cut_band_zero`: The exterior cutoff beyond the enlarged radius annihilates the growing interior cutoff. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L981).

**The cutoff enters a finite band** · theorem. `cutX_mem_band`: The growing cutoff maps every homogeneous-space element into the frequency band of radius n plus one. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L993).

**The cutoffs converge to identity** · theorem. `tendsto_cutX`: As the cutoff radius grows, the cutoff elements converge in homogeneous-space norm to the original element. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L1009).

**Cut off a continuous periodic curve** · definition. `cutMap`: The cutoff map applies the homogeneous-space frequency cutoff to a continuous time-circle curve. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L1039).

**Cutoff curves lie in the dense class** · theorem. `toLp_cutMap_mem`: The L² class of a cut-off continuous periodic curve belongs to the finite-band forcing submodule. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L1042).

**Convergence of composed curve maps** · theorem. `tendsto_toLp_comp`: Pointwise convergence of the uniformly bounded operators gives L² convergence after composition with a continuous periodic curve. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L1052).

**Cutoff curves converge in L²** · theorem. `tendsto_toLp_cutMap`: The L² classes of the cut-off continuous periodic curves converge to the original curve's L² class. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L1078).

**Finite-band forcing curves are dense** · theorem. `dense_denseClass`: The continuous finite-band forcing submodule is dense in the forcing Hilbert space. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L1084).

**Represent an L²-valued integral** · theorem. `lpIntegral_ae_of_kernel`: The integral of the L²-valued curve is represented almost everywhere by the pointwise integral of its jointly measurable kernel. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L1094).

**Joint continuity of propagated values** · theorem. `continuous_apply_of_semigroup`: The semigroup acts continuously on a continuously varying time and input vector. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L1156).

**The selected witness satisfies its rule** · theorem. `spec_of_dite'`: When a witness exists, the conditional choice satisfies the predicate used to select it. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L1176).

**The gradient inverse integral** · theorem. `gradInv_eq'`: Under the gradient-inverse property and positive period, the selected gradient inverse equals the positive-time integral of its propagator integrand. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L1181).

**The periodic lift is continuous** · theorem. `continuous_lift'`: The lift of the continuous periodic curve to the time circle is continuous. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L1185).

**The time-circle quotient is continuous** · theorem. `continuous_coe_circle'`: The quotient map from real time to the time circle is continuous. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L1189).

**The periodic propagator kernel** · definition. `kernel'`: The kernel propagates the bounded square-root Laplacian of the shifted periodic input, using nonnegative elapsed time. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L1192).

**Continuity of the propagator kernel** · theorem. `continuous_kernel'`: The periodic propagator kernel is jointly continuous in elapsed time and the time-circle variable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L1195).

**Exponential decay of the kernel** · theorem. `norm_kernel_le'`: A uniform bound C on the capped square-root Laplacian input bounds the kernel norm by C times exp(−τ/4) for positive elapsed time. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L1207).

**Identify the periodic integrand** · theorem. `integrand_ae'`: The abstract propagator integrand is represented almost everywhere by the explicit time-circle kernel. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L1223).

**The inverse has a mild representative** · theorem. `gradInv_ae_mild`: For finite-band continuous forcing, the gradient inverse agrees almost everywhere with the mild similarity-time integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L1243).

**Transfer the Laplacian-root relation** · theorem. `isHalfSspOf_congr`: Replacing an element by an equal one preserves its specified square-root Laplacian relation. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L1281).

**A finite-band energy curve exists** · theorem. `curve_of_band`: Finite-band continuous forcing gives a representative curve satisfying the period-scaled energy identity. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L1287).

**Source namespace `Breakdown.Cert`.**

**Energy curves on a dense subspace** · theorem. `exists_dense_energyCurve_band`: There is a dense forcing subspace on which the inverse admits the required continuous energy curves and interval identity. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/DenseEnergyCurveBand.lean#L1342).

### Breakdown.Cert.ExistsZeroHeld

The finite-dimensional multiplier must vanish somewhere in the parameter box. This file translates the boundary inequalities and a box zero theorem into a parameter with zero held multiplier. §7.8: fixed-parameter contraction and the parameter zero

**Source namespace `Breakdown.Cert.Internal.ExistsZeroHeld`.**

**Nonnegative weighted energy** · theorem. `Breakdown.Cert.ExistsZeroHeld.energyW_nonneg_of`: The admissible weights make the perturbation's weighted energy nonnegative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExistsZeroHeld.lean#L12).

**A held coordinate is bounded** · theorem. `abs_le_sizeZ`: The absolute value of each multiplier coordinate is bounded by the combined held-state size. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExistsZeroHeld.lean#L17).

**Combine three scalar errors** · theorem. `abs_add_sub_le`: Bounds for the three scalar contributions give the stated bound for their sum and difference. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExistsZeroHeld.lean#L26).

**The selected total multiplier** · theorem. `Breakdown.Cert.ExistsZeroHeld.multiplierOf_eq`: The total multiplier is the approximate multiplier plus the multiplier selected with the held correction. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExistsZeroHeld.lean#L32).

**Source namespace `Breakdown.Cert`.**

**Find a zero total multiplier** · theorem. `existsZeroHeldHolds_of`: The held-state bounds and parameter-zero argument prove existence of a parameter with vanishing total multiplier. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExistsZeroHeld.lean#L40).

### Breakdown.Cert.ExtendedAdjointEnclosure

The weak-regularity certificate supplies quantitative adjoint residual bounds. This file connects their physical integrals to the operator enclosure used in the bordered inverse argument. §7: certificate data and the similarity-profile construction

**Continuous fixed-parameter profiles** · theorem. `continuous_profile_slice`: The approximate profile at a fixed parameter is jointly continuous in time and position. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedAdjointEnclosure.lean#L21).

**Continuous profile slice gradients** · theorem. `continuous_fderiv_profile_slice`: The spatial derivative of the fixed-parameter profile is jointly continuous. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedAdjointEnclosure.lean#L26).

**Integrability of transport pairings** · theorem. `Breakdown.Cert.ExtendedAdjointEnclosure.integrable_transport`: The profile-perturbation transport expression has an integrable pairing with each compactly supported test field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedAdjointEnclosure.lean#L33).

**A zero-actuator right-hand side** · theorem. `isRightSide_zero`: The physical reading satisfies the right-hand-side equation with zero actuator coefficients. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedAdjointEnclosure.lean#L75).

**A left inverse lifts to L² curves** · theorem. `compLpL_left_inverse`: A left-inverse pair of continuous linear maps remains a left-inverse pair after acting on L² curves. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedAdjointEnclosure.lean#L115).

**Physical representatives of forcing** · theorem. `exists_representative`: Every forcing Hilbert-space element has an admissible periodic physical-field representative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedAdjointEnclosure.lean#L127).

**Periodic actuator regularity** · theorem. `Breakdown.Cert.ExtendedAdjointEnclosure.actuator_periodicField`: Each actuator satisfies the periodic-field conditions needed for physical pairings. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedAdjointEnclosure.lean#L137).

**Nonnegative weighted energy** · theorem. `Breakdown.Cert.ExtendedAdjointEnclosure.energyW_nonneg_of`: The admissible weights make the perturbation's weighted energy nonnegative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedAdjointEnclosure.lean#L146).

**The adjoint linear-defect bound** · theorem. `delta_core`: The difference between the adjoint-tested linear equation and the coupled pin values is bounded by the adjoint defect times square-root weighted energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedAdjointEnclosure.lean#L152).

**Control the adjoint discrepancy** · theorem. `delta_bound`: The adjoint-tested inverse-plus-convection equation differs from its pin coupling by at most the adjoint-defect energy bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedAdjointEnclosure.lean#L190).

**The adjoint quadratic bound** · theorem. `quad_bound`: Testing the quadratic perturbation term against the adjoint field is bounded by the adjoint quadratic constant times weighted energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedAdjointEnclosure.lean#L215).

**Combine the adjoint enclosures** · theorem. `final_compare`: The quadratic and linear error estimates yield the displayed radius-dependent adjoint enclosure. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedAdjointEnclosure.lean#L248).

**The invariant transport map** · definition. `transportPart`: The invariant forcing subspace maps to forcing plus the convection of its free inverse. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedAdjointEnclosure.lean#L258).

**Pins of the invariant free inverse** · definition. `pinPart`: The invariant forcing subspace maps to the pin coordinates of its free inverse. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedAdjointEnclosure.lean#L263).

**Evaluate the invariant transport map** · theorem. `transportPart_apply`: The transport map on invariant forcing is the forcing plus the convection of its free inverse. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedAdjointEnclosure.lean#L268).

**Evaluate the invariant pin map** · theorem. `pinPart_apply`: The invariant pin map is the pin map applied to the free inverse. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedAdjointEnclosure.lean#L273).

### Breakdown.Cert.ExtendedAdjointPairing

The adjoint enclosure needs exact pairings between physical representatives and abstract curves. This file proves those identifications, including the periodic L² integral formulas. §7: certificate data and the similarity-profile construction

**Admissible adjoint fields** · theorem. `adjoint_isPeriodicField`: Each parameterized adjoint field satisfies the periodic-field conditions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedAdjointPairing.lean#L15).

**The L² norm as a square integral** · theorem. `Breakdown.Cert.ExtendedAdjointPairing.lintegral_sq_eq`: The nonnegative integral of the representative's squared norm equals the squared L² norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedAdjointPairing.lean#L27).

**Recover the L² representative** · theorem. `coe_ae_of_toLpOrZero`: A field converted to the given L² class agrees almost everywhere with that class's representative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedAdjointPairing.lean#L37).

**Physical pairing as an inner product** · theorem. `Breakdown.Cert.ExtendedAdjointPairing.pairing_eq_inner`: The integral pairing of the physical fields equals the inner product of their L² representatives. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedAdjointPairing.lean#L42).

**The projection residual is orthogonal** · theorem. `inner_sub_proj_proj`: The residual after solenoidal projection is orthogonal to the projected field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedAdjointPairing.lean#L56).

**The residual's squared norm pairing** · theorem. `inner_sub_proj_self`: Pairing the projection residual with the original field equals the residual's squared norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedAdjointPairing.lean#L60).

**The zero weak gradient relation** · theorem. `isWeakGradient_of_zero`: An identically zero vector field has the identically zero weak gradient. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedAdjointPairing.lean#L65).

**The zero perturbation** · theorem. `zero_isPerturbation`: Zero velocity, gradient, second derivative and forcing satisfy the perturbation conditions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedAdjointPairing.lean#L72).

### Breakdown.Cert.ExtendedAtProfile

The weak coercivity estimate is specialized to a parameterized certificate profile. This file verifies the reading, pairing and energy conditions that turn it into the operator estimate at that profile. §7.7: coercivity and the linearized inverse, with analytic support lemmas

**A weighted Euclidean triangle bound** · theorem. `weighted_sub_le`: The square root of the weighted squared difference is at most the sum of the two weighted square roots. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedAtProfile.lean#L17).

**Rescale row weights** · theorem. `rowNorm_div`: Dividing the row weights by a positive scalar squared divides the row norm by that scalar. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedAtProfile.lean#L42).

**Physical pairing as an inner product** · theorem. `Breakdown.Cert.ExtendedAtProfile.pairing_eq_inner`: The integral pairing of the physical fields equals the inner product of their L² representatives. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedAtProfile.lean#L53).

**A row-norm difference bound** · theorem. `rows_sub_le`: The row norm of a field difference is bounded by the original row norm plus the row bound times the other field's period norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedAtProfile.lean#L64).

**Continuous slice derivatives** · theorem. `Breakdown.Cert.ExtendedAtProfile.continuous_fderiv_slice`: The first spatial derivative varies continuously with the time-space point. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedAtProfile.lean#L111).

**A differentiable profile slice** · theorem. `profile_slice_smooth`: The fixed-parameter approximate profile is jointly once continuously differentiable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedAtProfile.lean#L118).

**The model-to-profile transport gap** · definition. `gapField`: The gap field records the change in transport when the model field and its gradient are replaced by the profile. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedAtProfile.lean#L122).

**The gap is an admissible field** · theorem. `isPeriodicField_gap`: The model-to-profile gap satisfies the periodic-field conditions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedAtProfile.lean#L127).

**Bound the model-to-profile gap** · theorem. `periodNorm_gap_le`: The period norm of the transport gap is bounded by the gap constant times the square root of weighted energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedAtProfile.lean#L150).

**Integrability of transport pairings** · theorem. `Breakdown.Cert.ExtendedAtProfile.integrable_transport`: The profile-perturbation transport expression has an integrable pairing with each compactly supported test field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedAtProfile.lean#L164).

**Integrable actuator test pairings** · theorem. `integrable_actuator_pairing`: The finite actuator combination has an integrable pairing with a compactly supported test. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedAtProfile.lean#L211).

**Move the equation to the model** · theorem. `isRightSide_model`: Subtracting the transport gap from the forcing converts the profile right-hand-side equation to the model equation. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedAtProfile.lean#L228).

**Nonnegative stationary energy** · theorem. `Breakdown.Cert.ExtendedAtProfile.stationaryEnergy_nonneg`: The admissible weight makes the stationary energy built from the first and second spatial derivatives nonnegative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedAtProfile.lean#L353).

**No transfer loss at the profile** · theorem. `transferLoss_atProfile`: Replacing the model by the profile makes the model-to-profile transfer-loss parameter zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedAtProfile.lean#L361).

**Transfer a certificate to the profile** · theorem. `isExtendedCertificate_atProfile`: The transformed data satisfy the extended certificate conditions with the model taken at the approximate profile. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedAtProfile.lean#L365).

### Breakdown.Cert.ExtendedBorderedInvertible

The extended linearized problem includes finite-dimensional actuator and pinning coordinates. This file assembles the enclosure and compactness inputs into invertibility of the bordered operator. §7.7: coercivity and the linearized inverse, with analytic support lemmas

**The bordered kernel is trivial** · theorem. `eq_zero_of_bordered_eq_zero`: The extended coercive estimate forces an element of the bordered operator's kernel to be zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedBorderedInvertible.lean#L16).

### Breakdown.Cert.ExtendedCoerciveAbsorbStep

The weak coercivity argument produces several error blocks. This file absorbs the epsilon-controlled blocks into the positive energy under the specified certificate inequalities. §7.7: coercivity and the linearized inverse, with analytic support lemmas

**Source section `Pieces`.**

**Absorb an epsilon piece** · theorem. `eps_piece_le_weak`: The epsilon density minus its positive part has a summable mode expansion bounded by the remainder modes and block term. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveAbsorbStep.lean#L22).

**The block correction is nonpositive** · theorem. `pieceBlockWith_nonpos`: The combined block correction has nonpositive sign under the admissibility hypotheses. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveAbsorbStep.lean#L163).

**The real mode absorption step** · theorem. `real_step_weak`: The full real mode density after subtracting its positive part is controlled by the summed remainder and block correction. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveAbsorbStep.lean#L188).

**A nonnegative mode absorption bound** · theorem. `pointwise_step_weak`: Separating positive and negative parts converts the real mode inequality to the nonnegative pointwise inequality used for integration. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveAbsorbStep.lean#L230).

**Restrict a first joint derivative** · theorem. `fderiv_slice_eq_of_one`: For a jointly once differentiable field, the slice derivative is the joint derivative restricted to spatial directions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveAbsorbStep.lean#L248).

**Continuity of first slice derivatives** · theorem. `continuous_fderiv_slice_of_one`: Joint continuous differentiability makes the spatial slice-derivative field continuous. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveAbsorbStep.lean#L257).

**Measurability of weak stretching** · theorem. `aem_stretchFormWith`: The stretching form using the specified weak second derivative is almost everywhere measurable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveAbsorbStep.lean#L267).

**Measurability of the coercive bound** · theorem. `aemeasurable_hypothesisSide_weak`: The positive-mode, remainder, block and stretching expression is almost everywhere measurable on the time slab. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveAbsorbStep.lean#L277).

**Measurability of negative stretching** · theorem. `aemeasurable_stretchNeg_weak`: The nonnegative image of the negative weak stretching form is almost everywhere measurable on the time slab. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveAbsorbStep.lean#L365).

### Breakdown.Cert.ExtendedCoerciveAbsorbStepMu

The lower-order mu blocks require their own absorption step. These estimates combine pressure, reflection and transport losses with the available weighted energy. §7.7: coercivity and the linearized inverse, with analytic support lemmas

**Source namespace `Breakdown.CoerciveWeak.Internal.AbsorbStep`.**

**Negative modes are conjugate** · theorem. `modeAverage_neg`: For real fields, the Fourier coefficient of the opposite mode is the complex conjugate of the original coefficient. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveAbsorbStepMu.lean#L17).

**Equal amplitudes at opposite modes** · theorem. `gradAmp_neg`: The gradient amplitude is unchanged on replacing a mode by its negative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveAbsorbStepMu.lean#L32).

**Frame frequencies change sign** · theorem. `frameFreq_neg`: Negating the mode negates its frequency in the moving frame. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveAbsorbStepMu.lean#L36).

**Reflect a symmetric finite sum** · theorem. `sum_neg_eq`: Summing over reflected indices gives the same sum on a reflection-invariant finite set. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveAbsorbStepMu.lean#L41).

**An indicator cannot enlarge magnitude** · theorem. `abs_ind_mul_le`: Multiplying a real number by an indicator leaves its absolute value no larger. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveAbsorbStepMu.lean#L46).

**Bound a symmetric-piece indicator** · theorem. `ind_inPiece_le`: Membership in a piece or its reflection is bounded by the sum of the two finite-set membership indicators. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveAbsorbStepMu.lean#L51).

**Split a finite sum by a condition** · theorem. `split_sum_ite`: A finite sum separates into the terms satisfying a condition and the terms failing it. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveAbsorbStepMu.lean#L58).

**Compare conditional finite sums** · theorem. `sum_ite_le`: Pointwise comparison gives the corresponding comparison after restricting a finite sum by a condition. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveAbsorbStepMu.lean#L64).

**Account for shifts across a piece** · theorem. `coef_le`: The shifted harmonic coefficient sum is controlled by the interior coefficient budget corrected by inward and outward mode transfers. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveAbsorbStepMu.lean#L72).

**The piecewise pressure square bound** · theorem. `pressure_le`: The pressure-mode convolution is square summable and bounded by the harmonic budget with inward and outward transfer corrections. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveAbsorbStepMu.lean#L126).

**Source section `Pieces`.**

**Absorb a mu piece** · theorem. `mu_piece_le_weak`: The mu density minus its positive part is summable and bounded by its remainder modes and block contribution. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveAbsorbStepMu.lean#L228).

### Breakdown.Cert.ExtendedCoerciveAssembly

This is an assembly point for the weak coercivity proof. It combines the energy identity, positive density and controlled error blocks into the final lower estimate. §7.7: coercivity and the linearized inverse, with analytic support lemmas

**Source namespace `Breakdown.CoerciveWeak`.**

**Weak multiplier fields from zero flow** · theorem. `pieceFieldExistsWeak_of_zeroFlow`: The admissible zero-flow construction supplies the weak multiplier-field existence interface. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveAssembly.lean#L14).

**Smooth data satisfy weak admissibility** · theorem. `isAdmissibleWeak_of_isAdmissibleHolds`: Smooth admissible data become weakly admissible when the specified Hessian is their actual second derivative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveAssembly.lean#L19).

**Identify the vorticity-gradient bound** · theorem. `vortGradSupWith_secondDerivFieldHolds`: Using the actual second derivative makes the weak vorticity-gradient supremum equal the smooth one. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveAssembly.lean#L29).

**Identify the smooth epsilon block** · theorem. `pieceEpsBlockWith_secondDerivFieldHolds`: The weak epsilon block specializes to the smooth epsilon block when the supplied Hessian is the actual second derivative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveAssembly.lean#L35).

**Identify the smooth combined block** · theorem. `pieceBlockWith_secondDerivFieldHolds`: The combined weak block specializes to the smooth block under the actual-Hessian substitution. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveAssembly.lean#L41).

**Recover smooth multiplier density** · theorem. `pieceMultiplierDensity_of_weakHolds`: The weak multiplier-density interface supplies the corresponding smooth multiplier-density interface. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveAssembly.lean#L47).

**Recover smooth epsilon estimates** · theorem. `pieceEpsEstimateSmooth_of_weak`: The weak epsilon estimate yields the smooth epsilon estimate interface. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveAssembly.lean#L56).

**Recover smooth mu estimates** · theorem. `pieceMuEstimateSmooth_of_weak`: The weak mu estimate yields the smooth mu estimate interface. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveAssembly.lean#L65).

**Recover the smooth density limit** · theorem. `pieceDensityPassage_of_weak`: The weak density-passage interface supplies the smooth passage-to-the-limit interface. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveAssembly.lean#L72).

**Assemble weak multiplier density** · theorem. `pieceMultiplierDensityWeakHolds_of_nodes`: The weak analytic node hypotheses combine to prove the weak multiplier-density interface. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveAssembly.lean#L82).

**Source section `Extended`.**

**Piece data give extended coercivity** · theorem. `extendedCoerciveClause_of_pieceDataHolds`: The verified piece-data and analytic interfaces supply the extended coercive certificate clause. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveAssembly.lean#L106).

### Breakdown.Cert.ExtendedCoerciveBordered

The coercive estimate is transferred to the bordered system with actuator and pinning coordinates. This file supplies the norm controls used to establish the bounded inverse. §7.7: coercivity and the linearized inverse, with analytic support lemmas

**Continuity of the approximate profile** · theorem. `continuous_profile`: The approximate profile at the fixed parameter is jointly continuous. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveBordered.lean#L17).

**Continuity of the profile gradient** · theorem. `continuous_fderiv_profile`: The fixed-parameter profile's spatial derivative is jointly continuous. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveBordered.lean#L21).

**Integrable convection test pairings** · theorem. `integrable_convection`: The physical convection expression has an integrable pairing with each compactly supported test. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveBordered.lean#L28).

**Integrability of actuator pairings** · theorem. `integrable_actuator`: The finite actuator combination has an integrable pairing with the test field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveBordered.lean#L70).

**The bordered equation is physical** · theorem. `isRightSide_of`: The abstract bordered equation gives the physical right-hand-side relation for the selected field reading. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveBordered.lean#L86).

**An energy bound with unit weights** · theorem. `unit_weight_bound`: The weighted coercive estimate yields the displayed unit-weight square-root bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveBordered.lean#L133).

### Breakdown.Cert.ExtendedCoerciveEnergyIdentity

The linearized energy pairing is decomposed into positive energy and profile interactions. These lemmas establish the full weak identity from its slice and integrability components. §7.7: coercivity and the linearized inverse, with analytic support lemmas

**Decay bounds on a fixed time slice** · theorem. `slice_decay`: On every time slice, a weak second-derivative state has nonnegative decay constant, bounded velocity and inverse-radius bounds for its gradient and supplied Hessian. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveEnergyIdentity.lean#L19).

**Build the weak slice data** · theorem. `slice_data`: The perturbation and coefficient assumptions supply the weak energy-identity data on a fixed time slice. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveEnergyIdentity.lean#L35).

**The zero flow satisfies decay bounds** · theorem. `zero_flow_decay`: A uniform decay constant exists for all zero-flow spatial derivatives through order two. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveEnergyIdentity.lean#L57).

**The advection energy pairing exists** · theorem. `advection_integrable`: The pairing of the convection expression with the negative second-derivative trace is spatially integrable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveEnergyIdentity.lean#L62).

**The stretching term is measurable** · theorem. `stretch_measurable`: The weak stretching integrand is almost everywhere strongly measurable on the spatial slice. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveEnergyIdentity.lean#L107).

**The stretching term is integrable** · theorem. `stretch_integrable`: The weak stretching integrand is spatially integrable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveEnergyIdentity.lean#L126).

**Convection becomes stretching** · theorem. `stretch_slice_weak`: The integral pairing of advection with the negative Laplacian equals the weak stretching integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveEnergyIdentity.lean#L204).

**The weak slice energy identity** · theorem. `slice_identity_weak`: Pairing the smooth right-hand side with the negative Laplacian yields the time-energy term, vorticity energies and weak stretching. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveEnergyIdentity.lean#L212).

### Breakdown.Cert.ExtendedCoerciveEnergyIdentityCross

This part of the energy calculation handles the cross convection terms. It proves the algebraic identities and integral cancellations that place them in the stretching expression. §7.7: coercivity and the linearized inverse, with analytic support lemmas

**Source namespace `Breakdown.CoerciveWeak.EnergyIdentityWeakInternal.CrossInternal`.**

**The energy envelope is square integrable** · theorem. `atom_sq_weak`: The square of the combined slice-energy envelope is integrable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveEnergyIdentityCross.lean#L22).

**Envelope domination gives integrability** · theorem. `int_atom`: An integrand dominated by the square-integrable slice-energy envelope has the required integrability. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveEnergyIdentityCross.lean#L43).

**Control a decaying product** · theorem. `dec_le`: The decay and field bounds control the indicated product by a constant times the slice-energy envelope. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveEnergyIdentityCross.lean#L51).

**Decay of coefficient vorticity** · theorem. `omega_le`: Each coefficient-vorticity coordinate is bounded by nine times the inverse-radius derivative bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveEnergyIdentityCross.lean#L60).

**A uniform coefficient-vorticity bound** · theorem. `omega_le'`: Each coefficient-vorticity coordinate is bounded by nine times the decay constant. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveEnergyIdentityCross.lean#L64).

**Decay of vorticity gradients** · theorem. `vg_le`: Each vorticity-gradient coordinate is bounded by nine times the inverse-radius Hessian bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveEnergyIdentityCross.lean#L68).

**A continuous vorticity-gradient map** · theorem. `vortGrad_continuous`: A fixed vorticity-gradient coordinate is a continuous function of the bilinear second-derivative map. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveEnergyIdentityCross.lean#L72).

**Measurable vorticity gradients** · theorem. `vg_meas`: Each specified weak vorticity-gradient coordinate is almost everywhere strongly measurable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveEnergyIdentityCross.lean#L77).

**Continuous coefficient vorticity** · theorem. `omega_cont`: Each coordinate of the coefficient vorticity is continuous. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveEnergyIdentityCross.lean#L81).

**A weak derivative of vorticity** · theorem. `omega_weak`: The indicated coordinate of the supplied Hessian gives the weak partial derivative of the coefficient-vorticity coordinate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveEnergyIdentityCross.lean#L85).

**An integrable weighted product** · theorem. `int_weight`: The product of the two fields divided by one plus the radius is integrable under their weighted energy assumptions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveEnergyIdentityCross.lean#L106).

**Source namespace `Breakdown.CoerciveWeak.EnergyIdentityWeakInternal`.**

**Move the vorticity cross derivative** · theorem. `x_term_weak`: The cross-vorticity integral equals the half-weighted alternating-symbol expression involving the weak coefficient-vorticity derivative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveEnergyIdentityCross.lean#L120).

### Breakdown.Cert.ExtendedCoerciveEnergyIdentityPoint

The weak energy identity relies on matrix identities valid at a spatial point. This file separates those finite-dimensional algebraic calculations from the measure-theoretic passage. §7.7: coercivity and the linearized inverse, with analytic support lemmas

**Expand the convection-curl pairing** · theorem. `curl_grad_weak`: The pointwise convection-curl pairing separates into transport, symmetric-gradient stretching, vorticity-gradient and cross-vorticity terms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveEnergyIdentityPoint.lean#L17).

**Expand the cross-vorticity derivative** · theorem. `x_expand_weak`: The product-rule expansion splits the cross-vorticity derivative into twice its Hessian term and the remaining derivative term. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveEnergyIdentityPoint.lean#L55).

**Recover the cross-vorticity term** · theorem. `y_point_weak`: The alternating-symbol derivative expression equals the negative cross-vorticity interaction. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveEnergyIdentityPoint.lean#L75).

### Breakdown.Cert.ExtendedCoerciveEnergyIdentitySlice

The energy calculation is first proved on spatial slices. This file supplies the slice integrability and integration-by-parts statements later integrated over a period. §7.7: coercivity and the linearized inverse, with analytic support lemmas

**Data for the weak slice identity** · structure. `WeakSliceData`: The slice data record smooth divergence-free perturbations, weighted energies, once differentiable coefficients and a measurable symmetric weak Hessian. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveEnergyIdentitySlice.lean#L18).

### Breakdown.Cert.ExtendedCoerciveEnergyIdentityStretch

The convection contribution is rewritten in terms of vorticity stretching. These lemmas identify the stretching integrand and justify the integral rearrangement under weak derivative hypotheses. §7.7: coercivity and the linearized inverse, with analytic support lemmas

**Source namespace `Breakdown.CoerciveWeak.EnergyIdentityWeakInternal.SliceStretchInternal`.**

**The slice envelope is square integrable** · theorem. `atom_sq_slice`: The weak slice assumptions make the combined slice-energy envelope square-integrable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveEnergyIdentityStretch.lean#L20).

**A uniform coefficient-gradient bound** · theorem. `grad_le_const`: The inverse-radius derivative decay bound implies the uniform bound by the decay constant. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveEnergyIdentityStretch.lean#L42).

**A product bound by slice energy** · theorem. `decay_mul_le`: The decay assumptions bound the indicated coefficient-field product by the slice-energy envelope. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveEnergyIdentityStretch.lean#L46).

**Source namespace `Breakdown.CoerciveWeak.EnergyIdentityWeakInternal`.**

**Transport contributes zero energy** · theorem. `transport_weak`: The divergence-free coefficient transport term has zero spatial integral in the weak vorticity-energy identity. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveEnergyIdentityStretch.lean#L60).

**Source namespace `Breakdown.CoerciveWeak.EnergyIdentityWeakInternal.SliceStretchInternal`.**

**The weak derivative of convection** · definition. `jetA`: The convection derivative expression combines coefficient and perturbation derivatives with the supplied weak coefficient Hessian. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveEnergyIdentityStretch.lean#L136).

**Measurability of Hessian substitution** · theorem. `aesm_pair`: Evaluating the continuous expression at the measurable Hessian gives an almost everywhere strongly measurable field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveEnergyIdentityStretch.lean#L142).

**Transfer a weak derivative relation** · theorem. `weakPartial_congr`: Replacing a function and its weak derivative by the specified equal representatives preserves the weak partial-derivative relation. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveEnergyIdentityStretch.lean#L147).

**The weak derivative of advection** · theorem. `weakPartial_adv`: The convection coordinate has the displayed weak partial derivative obtained from the product rule and supplied Hessian. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveEnergyIdentityStretch.lean#L153).

**Bound a convection coordinate** · theorem. `adv_le`: A convection coordinate is bounded by twice the decay constant times the slice-energy envelope. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveEnergyIdentityStretch.lean#L190).

**Bound the convection derivative** · theorem. `jetA_le`: A coordinate of the weak convection derivative is bounded by twelve times the decay constant times the energy envelope. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveEnergyIdentityStretch.lean#L203).

**Integrable integration-by-parts terms** · theorem. `int_adv_term`: The convection coordinate paired with a curl derivative is integrable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveEnergyIdentityStretch.lean#L230).

**Integrability after integration by parts** · theorem. `int_jet_term`: The weak convection derivative paired with a curl coordinate is integrable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveEnergyIdentityStretch.lean#L251).

**Integrate a weak convection derivative** · theorem. `term_ibp`: Integration by parts moves a spatial derivative from the perturbation curl to the weak convection term with a minus sign. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveEnergyIdentityStretch.lean#L274).

**Source namespace `Breakdown.CoerciveWeak.EnergyIdentityWeakInternal`.**

**The weak stretching identity** · theorem. `stretch_weak`: The convection-Laplacian pairing equals the integral of the symmetric-gradient, vorticity-gradient and alternating-symbol stretching terms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveEnergyIdentityStretch.lean#L321).

### Breakdown.Cert.ExtendedCoerciveEnergyIdentityWeak

This file develops the weak-derivative calculus used by the energy identity. Product rules, smooth factors and integration by parts permit the argument to work with a weak Hessian. §7.7: coercivity and the linearized inverse, with analytic support lemmas

**A spatial weak partial derivative** · proposition definition. `WeakPartial`: A weak partial derivative consists of local integrability and the integration-by-parts identity against compactly supported scalar tests. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveEnergyIdentityWeak.lean#L17).

**Unit vectors have norm one** · theorem. `unit_norm_one`: Each spatial coordinate unit vector has norm one. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveEnergyIdentityWeak.lean#L21).

**Local integrability under a linear map** · theorem. `locint_comp`: A continuous linear map preserves local integrability of a field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveEnergyIdentityWeak.lean#L24).

**A test times a weak derivative** · theorem. `test_mul_int`: Multiplying the locally integrable weak derivative by a compactly supported test gives an integrable function. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveEnergyIdentityWeak.lean#L29).

**A continuous test derivative** · theorem. `test_deriv_cont`: A coordinate derivative of a smooth scalar test is continuous. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveEnergyIdentityWeak.lean#L33).

**A test derivative has compact support** · theorem. `test_deriv_supp`: A coordinate derivative of a smooth compactly supported test is compactly supported. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveEnergyIdentityWeak.lean#L37).

**A derivative test pairing is integrable** · theorem. `test_deriv_mul_int`: The test derivative times the locally integrable field is integrable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveEnergyIdentityWeak.lean#L41).

**Classical derivatives give weak ones** · theorem. `weakPartial_of_contDiff`: A continuously differentiable function satisfies the weak partial-derivative identity with its classical derivative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveEnergyIdentityWeak.lean#L46).

**Add weak derivatives** · theorem. `add`: The weak derivative of a sum is the sum of the weak derivatives. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveEnergyIdentityWeak.lean#L52).

**Scale a weak derivative** · theorem. `const_mul`: A constant real multiple has the correspondingly scaled weak derivative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveEnergyIdentityWeak.lean#L64).

**Sum finitely many weak derivatives** · theorem. `sum`: A finite sum of functions has the finite sum of their weak derivatives. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveEnergyIdentityWeak.lean#L75).

**The weak product rule** · theorem. `mul_smooth`: Multiplying by a smooth function gives the weak product rule with one term for each differentiated factor. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveEnergyIdentityWeak.lean#L87).

**The Hessian gives weak second partials** · theorem. `weakPartial_secondDeriv`: A coordinate of the specified weak Hessian is the weak partial derivative of the corresponding first-derivative coordinate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveEnergyIdentityWeak.lean#L121).

**Weak integration by parts** · theorem. `weak_ibp`: The integrable pairing with a test derivative equals the negative pairing with the weak derivative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveEnergyIdentityWeak.lean#L142).

### Breakdown.Cert.ExtendedCoerciveMain

This import-level assembly exposes the weak coercivity development and closes four modal interfaces: square sums, derivatives, rotation and solenoidal modes. These facts feed the piecewise coercivity argument. §7.7: coercivity and the linearized inverse, with analytic support lemmas

**Close the mode square-sum interface** · theorem. `modeSquareSumHolds_closed`: The torus Fourier theory supplies the complete mode square-sum interface. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveMain.lean#L37).

**Close the mode derivative interface** · theorem. `modeDerivativeHolds_closed`: The mode differentiation construction supplies the mode derivative interface. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveMain.lean#L40).

**Close the mode rotation interface** · theorem. `modeRotationHolds_closed`: The axial-rotation construction supplies the mode rotation interface. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveMain.lean#L44).

**Close the solenoidal-mode interface** · theorem. `solenoidalModeHolds_closed`: The Fourier-solenoidal argument supplies the solenoidal-mode interface. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveMain.lean#L48).

### Breakdown.Cert.ExtendedCoerciveMinorant

A vorticity-gradient supremum need not have the desired measurable presentation. This file constructs a measurable lower envelope and proves the lower-integral identities needed to use it in the estimate. §7.7: coercivity and the linearized inverse, with analytic support lemmas

**Source section `General`.**

**A maximal measurable lower bound** · theorem. `exists_kernel_of_le`: Under the domination hypothesis, the nonnegative function has a measurable minorant dominating every measurable lower bound almost everywhere. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveMinorant.lean#L18).

**Recover a value from finite caps** · theorem. `iSup_min_natCast`: The supremum of all natural-number truncations of an extended nonnegative real is the original value. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveMinorant.lean#L54).

**Choose a measurable minorant** · theorem. `exists_kernel`: A nonnegative function admits a measurable minorant that is maximal among measurable lower bounds up to null sets. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveMinorant.lean#L63).

**The chosen measurable lower bound** · definition. `minorant`: The minorant chooses a measurable lower bound with the almost-everywhere maximality property. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveMinorant.lean#L78).

**The chosen minorant is measurable** · theorem. `measurable_minorant`: The selected extended-real minorant is measurable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveMinorant.lean#L83).

**The minorant lies below its input** · theorem. `minorant_le`: The selected measurable minorant is pointwise bounded by the original function. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveMinorant.lean#L86).

**Every measurable lower bound fits** · theorem. `ae_le_minorant`: Every measurable lower bound lies below the selected minorant almost everywhere. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveMinorant.lean#L89).

**Replace a coefficient by its minorant** · theorem. `lintegral_mul_minorant_of_measurable`: With a measurable nonnegative weight, replacing the coefficient by its measurable minorant preserves the nonnegative weighted integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveMinorant.lean#L93).

**Minorants preserve weighted integrals** · theorem. `lintegral_mul_minorant`: The permitted almost-everywhere measurable nonnegative weight gives the same integral with the coefficient or its measurable minorant. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveMinorant.lean#L109).

**A real measurable lower bound** · definition. `realMinorant`: The real minorant takes the real value of the chosen minorant of the coefficient's nonnegative image. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveMinorant.lean#L122).

**The real minorant is measurable** · theorem. `measurable_realMinorant`: The selected real-valued minorant is measurable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveMinorant.lean#L125).

**The real minorant is nonnegative** · theorem. `realMinorant_nonneg`: The selected real-valued minorant is nonnegative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveMinorant.lean#L128).

**The selected minorant is finite** · theorem. `minorant_ofReal_ne_top`: The minorant of the nonnegative image of a real-valued function is finite at every point. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveMinorant.lean#L131).

**Recover the nonnegative minorant** · theorem. `ofReal_realMinorant`: Taking the nonnegative image of the real minorant recovers the original selected extended-real minorant. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveMinorant.lean#L135).

**The real minorant is a lower bound** · theorem. `realMinorant_le`: For a nonnegative real coefficient, its real minorant is bounded pointwise by that coefficient. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveMinorant.lean#L139).

**Real measurable lower bounds fit** · theorem. `ae_le_realMinorant`: Every admissible measurable real lower bound lies below the real minorant almost everywhere. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveMinorant.lean#L142).

**The minorant keeps the product integral** · theorem. `lintegral_ofReal_mul_realMinorant`: The nonnegative integral of the weighted product is unchanged when its coefficient is replaced by the real minorant. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveMinorant.lean#L149).

**Preserve a sum with a weighted term** · theorem. `lintegral_add_ofReal_mul_realMinorant`: Adding the nonnegative background term still gives equal integrals before and after replacing the coefficient by its real minorant. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveMinorant.lean#L162).

**Preserve a truncated affine integral** · theorem. `lintegral_ofReal_add_mul_realMinorant`: The nonnegative image of an affine weighted expression has the same integral with the coefficient or its real minorant. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveMinorant.lean#L168).

**Replace coefficients in iterated sums** · theorem. `lintegral_lintegral_add_ofReal_mul_realMinorant`: The iterated integral of the background-plus-weighted term is unchanged by the real-minorant replacement. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveMinorant.lean#L181).

**Change coefficients in affine iterates** · theorem. `lintegral_lintegral_ofReal_add_mul_realMinorant`: The iterated nonnegative integral of the affine expression is unchanged by the real-minorant replacement. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveMinorant.lean#L188).

**Measurability on almost every slice** · theorem. `ae_aemeasurable_slice`: Joint almost-everywhere measurability implies almost-everywhere measurability of almost every parameter slice. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveMinorant.lean#L197).

**Measurability of real slices** · theorem. `ae_aemeasurable_slice_real`: The real-valued joint measurability hypothesis gives measurable slices outside a parameter null set. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveMinorant.lean#L205).

**Source namespace `Breakdown.CoerciveWeak.Internal.Minorant`.**

**A measurable vorticity lower envelope** · definition. `vortGradSupLower`: The vorticity-gradient supremum is replaced by its real measurable minorant with respect to spatial volume. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveMinorant.lean#L215).

**A nonnegative vorticity supremum** · theorem. `Breakdown.Cert.ExtendedCoerciveMinorant.vortGradSupWith_nonneg`: The supremum norm controlling the specified vorticity gradient is nonnegative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveMinorant.lean#L220).

**A measurable vorticity lower envelope** · theorem. `measurable_vortGradSupLower`: The selected lower envelope of the vorticity-gradient supremum is measurable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveMinorant.lean#L223).

**A nonnegative vorticity lower envelope** · theorem. `vortGradSupLower_nonneg`: The measurable vorticity-gradient lower envelope is nonnegative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveMinorant.lean#L226).

**The lower envelope is a lower bound** · theorem. `vortGradSupLower_le`: The measurable lower envelope is pointwise bounded by the vorticity-gradient supremum. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveMinorant.lean#L229).

**Measurable bounds fit the envelope** · theorem. `ae_le_vortGradSupLower`: Every admissible measurable lower bound of the vorticity-gradient supremum lies below its lower envelope almost everywhere. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveMinorant.lean#L232).

**Use the vorticity lower envelope** · theorem. `lintegral_ofReal_mul_vortGradSupLower`: Replacing the vorticity-gradient supremum by its lower envelope preserves the weighted nonnegative spatial integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveMinorant.lean#L236).

**Preserve a weighted stretching sum** · theorem. `lintegral_add_ofReal_mul_vortGradSupLower`: Adding a background term still gives the same integral after replacing the vorticity-gradient supremum by its lower envelope. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveMinorant.lean#L241).

**Preserve an affine stretching integral** · theorem. `lintegral_ofReal_add_mul_vortGradSupLower`: The nonnegative image of the affine stretching expression has the same integral under the lower-envelope replacement. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveMinorant.lean#L247).

**Use the envelope on a time set** · theorem. `setLIntegral_lintegral_add_ofReal_mul_vortGradSupLower`: The time-set and spatial nonnegative integrals of the background-plus-weighted expression are unchanged by the lower-envelope replacement. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveMinorant.lean#L253).

**Use the envelope in slab integrals** · theorem. `setLIntegral_lintegral_ofReal_add_mul_vortGradSupLower`: The affine stretching expression has equal time-set and spatial integrals before and after the lower-envelope replacement. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveMinorant.lean#L260).

### Breakdown.Cert.ExtendedCoerciveNodes

The weak coefficient route needs compatibility facts before the main estimate. This file states weak-Hessian symmetry, recovery from smooth data, vorticity-gradient compatibility and the zero-flow admissibility interface. §7.7: coercivity and the linearized inverse, with analytic support lemmas

**Symmetry of the weak Hessian** · interface proposition. `WeakSecondDerivSymmetricHolds`: This interface requires the supplied weak second derivative to be symmetric in its two spatial arguments almost everywhere on every time slice. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveNodes.lean#L14).

Proved by `Breakdown.CoerciveWeak.weakSecondDerivSymmetricHolds_proof`.

**Smooth data give a weak Hessian state** · interface proposition. `WeakSecondDerivStateOfContDiffHolds`: This interface turns a twice differentiable periodic divergence-free field with decay bounds into a weak second-derivative state. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveNodes.lean#L18).

A named provider for this exact interface was not identified in the source.

**The Hessian differentiates vorticity** · interface proposition. `VortGradMapSecondDerivFieldHolds`: This interface identifies the vorticity-gradient map of the actual Hessian with the spatial derivative of the curl. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveNodes.lean#L24).

Proved by `Breakdown.CoerciveWeak.vortGradMapSecondDerivFieldHolds_proof`.

**Piece speeds for the zero flow** · definition. `zeroFlowWeights`: The zero-flow weights retain the piece data while replacing each speed by the similarity-plus-frame radial speed. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveNodes.lean#L28).

**Weak data admit a zero-flow model** · interface proposition. `ZeroFlowAdmissibleHolds`: This interface requires weakly admissible piece data to remain smoothly admissible after the zero-flow speed replacement. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveNodes.lean#L33).

Proved by `Breakdown.CoerciveWeak.zeroFlowAdmissibleHolds_proof`.

### Breakdown.Cert.ExtendedCoercivePairingSplit

The Fourier-side pairing is split into positive density and error contributions. This file defines the split quantities and proves the algebra that organizes the weak coercivity bound. §7.7: coercivity and the linearized inverse, with analytic support lemmas

**Source namespace `Breakdown.CoerciveWeak.Internal.WeakPairingSplit`.**

**The signed epsilon mode weight** · definition. `epsWeight`: The epsilon mode weight is the piece sign multiplied by its spatial weight. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePairingSplit.lean#L27).

**The signed mu mode weight** · definition. `muWeight`: The mu mode weight includes the piece sign, its spatial weight and one plus the radius. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePairingSplit.lean#L30).

**A bound on epsilon mode weights** · theorem. `epsWeight_bound`: Every signed epsilon mode weight is bounded in absolute value by the prescribed epsilon bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePairingSplit.lean#L33).

**Measurable epsilon mode weights** · theorem. `epsWeight_measurable`: Each signed epsilon mode weight is spatially measurable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePairingSplit.lean#L40).

**A uniform bound on mu weights** · theorem. `muWeight_bound`: There is a uniform finite bound for all signed mu mode weights. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePairingSplit.lean#L44).

**Measurable mu mode weights** · theorem. `muWeight_measurable`: Each signed mu mode weight is spatially measurable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePairingSplit.lean#L58).

**Curl agrees with Fourier modes** · proposition definition. `HasCurlModes`: This proposition requires the curl formed from each gradient mode to equal the corresponding mode of the physical curl. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePairingSplit.lean#L63).

**Smooth fields have curl modes** · theorem. `hasCurlModes_of_contDiff`: Sufficient joint differentiability makes curl commute with the mode construction. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePairingSplit.lean#L67).

**The piece form as weighted modes** · theorem. `pieceForm_eq`: The piece form is the finite sum of epsilon curl-mode pairings and mu velocity-mode pairings. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePairingSplit.lean#L71).

**The piece pairing passes to limits** · theorem. `pieceForm_tendsto`: Approximating both the solenoidal component and curl gives convergence of the piece form. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePairingSplit.lean#L100).

**Separate epsilon and mu pairings** · theorem. `mode_tsum_split`: The summed piece form splits into its epsilon pairings against the field and mu pairings against the solenoidal component. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePairingSplit.lean#L134).

**Split the multiplier pairing** · theorem. `multiplier_pairing`: The multiplier pairing equals the Laplacian pairing together with the finite epsilon and mu pairing corrections. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePairingSplit.lean#L153).

**Continuity of the smooth right side** · theorem. `smoothRight_continuous`: The smooth right-hand-side field is jointly continuous. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePairingSplit.lean#L195).

**A nonnegative decay constant** · theorem. `decay_const_nonneg`: The field decay hypotheses imply that the decay constant is nonnegative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePairingSplit.lean#L212).

**A derivative increment bound** · theorem. `fderiv_sub_le_of_segment`: A bound for the second derivative along the segment controls the first-derivative difference by the segment length. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePairingSplit.lean#L217).

**Decay of the actual Hessian** · theorem. `secondDerivField_norm_le`: The actual second spatial derivative obeys the inverse-cubic radial decay bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePairingSplit.lean#L251).

**Decay through two derivatives** · theorem. `decay_iterated`: The field, first derivative and second derivative satisfy the corresponding inverse-radius decay bounds. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePairingSplit.lean#L283).

**The smooth right side has finite energy** · theorem. `smoothRight_square`: The smooth right-hand-side field belongs to the periodic square-integrable class. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePairingSplit.lean#L294).

**A local profile-gradient bound** · theorem. `fderiv_sub_le_near`: Near a fixed point, the profile-gradient difference is bounded by distance times the local inverse-cubic decay constant. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePairingSplit.lean#L307).

**Bound the smooth transport derivative** · theorem. `fderiv_smooth_part_le`: The transport-Laplacian-advection part is differentiable and its derivative is bounded by the listed perturbation derivatives and coefficient decay terms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePairingSplit.lean#L325).

**A local increment from differentiability** · theorem. `eventually_sub_le`: Sufficiently close to the base point, function increments are bounded by distance times the derivative norm plus any positive margin. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePairingSplit.lean#L373).

**Bound the right-side derivative** · theorem. `fderiv_smoothRight_le`: The derivative of the smooth right side is controlled by transport, third-derivative and decay-weighted lower-order terms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePairingSplit.lean#L382).

**Curl is continuous in the matrix** · theorem. `continuous_curlVec`: The matrix-to-curl-vector operation is continuous. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePairingSplit.lean#L463).

**The right-side curl has finite energy** · theorem. `smoothRight_curl_square`: The curl of the smooth right side belongs to the periodic square-integrable class. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePairingSplit.lean#L472).

**The right-side derivative envelope** · definition. `derivBound`: The derivative envelope combines the transport derivative, three times the third derivative and the decay-weighted first, second and zeroth derivatives. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePairingSplit.lean#L501).

**The derivative envelope is continuous** · theorem. `derivBound_continuous`: The selected right-side derivative envelope is jointly continuous. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePairingSplit.lean#L507).

**Continuity along a time-angle orbit** · theorem. `continuous_orbit`: Time translation and axial rotation give a continuous map from the time-angle parameters to time-space. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePairingSplit.lean#L518).

**Bound the derivative along an orbit** · theorem. `derivBound_on_box`: The continuous derivative envelope has a finite uniform bound on a fixed compact time-angle orbit box. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePairingSplit.lean#L523).

**The right side has the curl-mode rule** · theorem. `smoothRight_hasCurlModes`: The smooth right-hand-side field satisfies the commutation rule between curl and Fourier modes. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePairingSplit.lean#L533).

**Approximation transfers curl density** · theorem. `density_of_approx`: An approximation in field and curl energy yields a periodic test sequence approaching the solenoidal component and the original curl. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePairingSplit.lean#L557).

**An integral convergence criterion** · theorem. `periodLIntegral_tendsto_zero`: The specified domination and convergence assumptions make the nonnegative periodic integrals tend to zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePairingSplit.lean#L622).

**Weak Hessians give derivatives a.e.** · theorem. `ae_hasFDerivAt_joint`: For almost every time-space point, the supplied weak Hessian is the derivative of the coefficient gradient. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePairingSplit.lean#L644).

**Approximate a weak coefficient smoothly** · theorem. `smoothApprox_exists`: The weak coefficient admits smooth periodic approximations with uniform decay, pointwise first-derivative convergence and almost-everywhere Hessian convergence. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePairingSplit.lean#L673).

**Derivatives of right sides converge** · theorem. `fderiv_smoothRight_tendsto`: Convergence of the coefficient and its first two derivatives gives convergence of the corresponding smooth right-side derivatives. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePairingSplit.lean#L685).

**Approximate the weak right side** · theorem. `smoothRight_approx`: The weak right side admits periodic differentiable approximations converging in both field and curl square integrals. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePairingSplit.lean#L739).

**Density for the weak right side** · theorem. `smoothRight_curlDensity`: Periodic solenoidal tests approximate the solenoidal component of the weak right side together with its curl. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePairingSplit.lean#L825).

**Source namespace `Breakdown.CoerciveWeak`.**

**Prove the weak piece pairing split** · theorem. `piecePairingSplitSmoothWeakHolds_of`: The approximation and curl-density argument proves the weak smooth-piece pairing decomposition. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePairingSplit.lean#L840).

### Breakdown.Cert.ExtendedCoercivePairingSplitAeDiff

The splitting argument needs pointwise derivatives at almost every spatial point. These lemmas extract almost-everywhere differentiability and bounds from the weak second-derivative state. §7.7: coercivity and the linearized inverse, with analytic support lemmas

**The decay bound is nonnegative** · theorem. `Breakdown.Cert.ExtendedCoercivePairingSplitAeDiff.decay_nonneg`: The stated field bounds force the common decay constant to be nonnegative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePairingSplitAeDiff.lean#L18).

**The coefficient gradient is Lipschitz** · theorem. `fderiv_increment`: The weak second-derivative bound makes the coefficient gradient globally Lipschitz on each time slice. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePairingSplitAeDiff.lean#L23).

**Read a Hessian coordinate** · definition. `entry`: The coordinate functional evaluates a bilinear second derivative on two unit vectors and selects one output coordinate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePairingSplitAeDiff.lean#L36).

**Read a gradient coordinate** · definition. `column`: The gradient-coordinate functional evaluates a linear derivative on a unit vector and selects one output coordinate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePairingSplitAeDiff.lean#L41).

**A linear image is locally integrable** · theorem. `locallyIntegrable_clm_comp`: A continuous linear map applied to a locally integrable field is locally integrable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePairingSplitAeDiff.lean#L44).

**Weak and directional derivatives agree** · theorem. `entry_ae_eq`: Almost everywhere, the coordinate directional derivative of the coefficient gradient equals the corresponding supplied Hessian entry. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePairingSplitAeDiff.lean#L50).

**Coordinates determine a bilinear map** · theorem. `entry_ext`: Two bilinear maps with equal coordinate entries on the basis are equal. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePairingSplitAeDiff.lean#L99).

**The weak Hessian is a derivative** · theorem. `ae_hasFDerivAt`: On each time slice, the coefficient gradient has the supplied Hessian as its derivative almost everywhere. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePairingSplitAeDiff.lean#L119).

### Breakdown.Cert.ExtendedCoercivePairingSplitIncrement

Increment estimates connect weak derivative information to the Fourier modes used in the split. This file bounds those increments and identifies their limiting derivatives. §7.7: coercivity and the linearized inverse, with analytic support lemmas

**A vector's coordinate expansion** · theorem. `eq_sum_basis`: Every spatial vector is the sum of its coordinate multiples of the three unit vectors. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePairingSplitIncrement.lean#L19).

**A reflected kernel is a test function** · theorem. `reflect_isTestFunction`: The normalized bump reflected about a fixed point is a smooth compactly supported scalar test. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePairingSplitIncrement.lean#L23).

**Differentiate a reflected kernel** · theorem. `reflect_fderiv`: Differentiating the reflected translated kernel gives the negative of the kernel derivative at the reflected point. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePairingSplitIncrement.lean#L28).

**Evaluate a derivative convolution** · theorem. `conv_apply_eq`: Applying the kernel-derivative convolution to two directions gives the corresponding integral of directional kernel derivatives. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePairingSplitIncrement.lean#L38).

**The weak Hessian inside convolution** · theorem. `basis_apply_eq`: On basis directions, the derivative-kernel convolution equals convolution of the supplied weak Hessian with the kernel. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePairingSplitIncrement.lean#L70).

**The smoothed Hessian entry is integrable** · theorem. `integrable_basis`: Each kernel-weighted Hessian basis entry is integrable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePairingSplitIncrement.lean#L81).

**Convolution identifies the derivative** · theorem. `deriv_apply_eq`: For arbitrary directions, the derivative-kernel convolution is the integral of the kernel-weighted weak Hessian. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePairingSplitIncrement.lean#L90).

**The reflected kernel has mass one** · theorem. `integral_reflect`: The normalized reflected kernel has integral one. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePairingSplitIncrement.lean#L122).

**Bound a smoothed derivative** · theorem. `deriv_norm_le`: The weak derivative's uniform norm bound also bounds the derivative of the smoothed field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePairingSplitIncrement.lean#L127).

**A bump shrinking within a chosen radius** · definition. `shrinkingBump`: The smoothing bump has outer radius equal to the chosen radius divided by n plus two and half that inner radius. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePairingSplitIncrement.lean#L152).

**The outer radius of the shrinking bump** · theorem. `shrinkingBump_rOut`: The shrinking bump's outer radius is the chosen radius divided by n plus two. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePairingSplitIncrement.lean#L157).

**The bump radii tend to zero** · theorem. `shrinkingBump_tendsto`: The outer radii of the shrinking bumps converge to zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePairingSplitIncrement.lean#L160).

**A weak Hessian controls increments** · theorem. `increment_of_weakSecondDeriv`: A uniform bound for the weak second derivative controls the derivative-field increments by that bound times distance. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePairingSplitIncrement.lean#L167).

### Breakdown.Cert.ExtendedCoercivePairingSplitMollify

The split is first handled after time-space smoothing. This file builds the mollifier family, proves its support and derivative bounds, and controls the approximation errors. §7.7: coercivity and the linearized inverse, with analytic support lemmas

**Product volume is translation invariant** · theorem. `prodVolume_invariantClass`: Time-space product volume is an additive Haar measure. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePairingSplitMollify.lean#L16).

**A shrinking time-space bump** · definition. `bump`: The joint time-space bump has outer radius 1/(2(k + 2)) and inner radius 1/(4(k + 2)). [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePairingSplitMollify.lean#L24).

**The time-space bump's outer radius** · theorem. `bump_rOut`: The time-space bump has outer radius 1/(2(k + 2)). [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePairingSplitMollify.lean#L32).

**The time-space bump's inner radius** · theorem. `bump_rIn`: The time-space bump has inner radius 1/(4(k + 2)). [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePairingSplitMollify.lean#L34).

**A time-space radius at most one half** · theorem. `bump_rOut_le`: Every time-space smoothing bump has outer radius at most one half. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePairingSplitMollify.lean#L36).

**The time-space bump shrinks** · theorem. `bump_rOut_tendsto`: The outer radius of the time-space smoothing bump tends to zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePairingSplitMollify.lean#L40).

**The outer radius is twice the inner one** · theorem. `bump_ratio`: The outer radius of the time-space bump is at most twice its inner radius. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePairingSplitMollify.lean#L45).

**Smooth jointly in time and space** · definition. `smear`: The smoothed field is the convolution of the joint time-space field with the normalized time-space bump. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePairingSplitMollify.lean#L52).

**The time-space convolution formula** · theorem. `smear_eq`: Joint smoothing integrates the normalized bump against the field translated in both time and space. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePairingSplitMollify.lean#L56).

**The smoothing integrand is integrable** · theorem. `integrable_term`: The compactly supported time-space kernel times the translated field is integrable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePairingSplitMollify.lean#L60).

**Differentiate the jointly smoothed field** · theorem. `hasFDerivAt_smear`: The spatial derivative of the jointly smoothed field is the smoothing of its specified weak spatial derivative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePairingSplitMollify.lean#L67).

**Smoothing retains radial decay** · theorem. `norm_smear_le`: Joint smoothing preserves the radial decay rate with the displayed factor-eight enlargement of the constant. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePairingSplitMollify.lean#L100).

**Local integrability from decay** · theorem. `locallyIntegrable_of_bound`: Joint measurability and the radial bound imply local integrability of the field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePairingSplitMollify.lean#L136).

**Construct smooth weak-data approximants** · theorem. `smoothApprox_of`: Joint smoothing gives smooth periodic approximations with uniform derivative decay and the required pointwise and almost-everywhere limits. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePairingSplitMollify.lean#L146).

### Breakdown.Cert.ExtendedCoercivePassageBlockDefs

The regularized split has several separate error blocks. This file gives those blocks explicit definitions so that convergence and domination can be established component by component. §7.7: coercivity and the linearized inverse, with analytic support lemmas

**Source section `Block`.**

**The vorticity-gradient block factor** · definition. `blockGain`: The block gain sums weighted products of velocity-piece and vorticity-piece norms over the epsilon pieces. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePassageBlockDefs.lean#L22).

**The measurable block correction** · definition. `pieceBlockLower`: The lower block uses the zero-Hessian block and subtracts the measurable vorticity-gradient envelope times the block gain. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePassageBlockDefs.lean#L26).

**Zero Hessian gives zero vorticity bound** · theorem. `vortGradSupWith_zero`: The vorticity-gradient supremum for the zero second-derivative field is zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePassageBlockDefs.lean#L31).

**The block gain is nonnegative** · theorem. `blockGain_nonneg`: Nonnegative piece weights make the block gain nonnegative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePassageBlockDefs.lean#L39).

**Isolate the vorticity-gradient term** · theorem. `pieceBlockWith_eq`: The combined block equals its zero-Hessian part minus the vorticity-gradient supremum times the block gain. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePassageBlockDefs.lean#L43).

### Breakdown.Cert.ExtendedCoercivePassageDiff

The passage to the weak limit needs a bound on changes in the split expressions. These difference estimates control the regularized error terms by the prescribed coefficient envelopes. §7.7: coercivity and the linearized inverse, with analytic support lemmas

**Source section `Mu`.**

**Control differences in mu remainders** · theorem. `muRest_bound_one`: The weak mu remainder satisfies the common remainder-difference bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePassageDiff.lean#L27).

**Source section `Eps`.**

**Bound changes in epsilon remainders** · theorem. `epsRest_bound_with`: The epsilon remainder with the specified weak Hessian satisfies the common remainder-difference bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePassageDiff.lean#L161).

**Control the full remainder difference** · theorem. `rest_diff_bound_with`: The complete weak remainder satisfies the common difference-bound condition. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePassageDiff.lean#L217).

**Source section `Block`.**

**Control differences in mu blocks** · theorem. `muBlock_bound_one`: The mu block, placed at the zero mode, satisfies the common remainder-difference bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePassageDiff.lean#L238).

**Bound changes in lower epsilon blocks** · theorem. `epsBlockLower_bound`: The epsilon block using the lower envelope satisfies the common remainder-difference bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePassageDiff.lean#L291).

**Split the lower block into pieces** · theorem. `pieceBlockLower_eq`: The measurable combined block is the sum of the lower epsilon blocks and the mu blocks. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePassageDiff.lean#L359).

**Control the lower block difference** · theorem. `block_lower_diff_bound`: The lower combined block placed at the zero mode satisfies the common remainder-difference bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePassageDiff.lean#L377).

### Breakdown.Cert.ExtendedCoercivePassageRest

This file handles the remainder blocks in the smoothing limit. Its bounds and convergence statements justify passing those terms to the weak coefficient field. §7.7: coercivity and the linearized inverse, with analytic support lemmas

**Source section `Amplitudes`.**

**Decay of velocity mode amplitudes** · theorem. `velAmp_le_one`: A coefficient velocity-mode amplitude is at most three times the inverse-radius decay bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePassageRest.lean#L24).

**Decay of gradient mode amplitudes** · theorem. `gradAmp_le_one`: A coefficient gradient-mode amplitude is at most nine times the inverse-square decay bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePassageRest.lean#L37).

**Decay of vorticity mode amplitudes** · theorem. `vortAmp_le_one`: The coefficient vorticity-mode amplitude is at most 144 times the inverse-square decay constant at the spatial point. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePassageRest.lean#L53).

**Source section `Sups`.**

**Nonnegativity of first-order decay** · theorem. `decay_const_nonneg_one`: The first-order decay hypotheses force the decay constant to be nonnegative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePassageRest.lean#L74).

**A bound on moving-frame speed** · theorem. `frameSpeedSup_le_one`: The frame-speed supremum is bounded by the coefficient decay constant plus the radial similarity and rotation speeds. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePassageRest.lean#L79).

**Decay of the vorticity supremum** · theorem. `vortSup_le_one`: The coefficient-vorticity supremum is at most twenty-seven times the inverse-square decay bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePassageRest.lean#L99).

**Source section `SecondDerivDecay`.**

**Decay of Hessian mode amplitudes** · theorem. `secondDerivAmp_le_with`: The specified weak-Hessian mode amplitude is at most twenty-seven times the inverse-cubic decay bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePassageRest.lean#L114).

**Decay of vorticity-gradient modes** · theorem. `vortGradAmp_le_with`: The supplied weak vorticity-gradient mode amplitude is at most 729 times the inverse-cubic decay constant at the spatial point. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePassageRest.lean#L127).

**Source section `Pointwise`.**

**Decay does not enlarge its constant** · theorem. `decay_le_self_one`: For a nonnegative exponent and radius, the decay quotient is at most the decay constant. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePassageRest.lean#L147).

**Source section `MuPointwise`.**

**Bound velocity edge interactions** · theorem. `edge_pointwise_one`: The weighted velocity edge sum is controlled by harmonic count times the scaled velocity and gradient square sums. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePassageRest.lean#L158).

**Bound pressure mode interactions** · theorem. `press_pointwise_one`: The weighted pressure contribution is controlled by the displayed harmonic, weight and scaled-velocity square terms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePassageRest.lean#L199).

**Source namespace `Breakdown.CoerciveWeak.Internal.PassageRest`.**

**Bound mu edge interactions** · theorem. `muEdge_pointwise_one`: The mu edge-mode interaction is bounded by the harmonic count times the scaled-velocity and supplied-gradient square sums. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePassageRest.lean#L281).

**Bound epsilon remainder modes** · theorem. `epsRest_pointwise_one`: The negative epsilon remainder sum is bounded by the displayed combination of vorticity, vorticity-gradient, velocity and gradient square sums. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePassageRest.lean#L324).

**Square the complex amplitude** · theorem. `sq_sqrt_cnormSq`: The square root of the complex squared norm, squared again, equals that squared norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePassageRest.lean#L401).

**The combined mode-energy identity** · theorem. `ampSq_eq`: The sum of Hessian, vorticity-gradient, gradient, vorticity and scaled-velocity squares is the combined amplitude square. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePassageRest.lean#L404).

**Each mode family fits the total** · theorem. `families_le`: Each listed mode-family square sum is bounded by the combined mode-energy total. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePassageRest.lean#L410).

**Bound the absolute combined remainder** · theorem. `ofReal_abs_split`: The absolute base-plus-piece remainder is controlled by the base magnitude and the indicated nonnegative piece contributions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePassageRest.lean#L429).

**An integrable remainder envelope** · theorem. `rest_tsum_le_one`: A finite constant bounds the total absolute weak remainder modes by the combined mode-energy total. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePassageRest.lean#L455).

**Bound the mu block correction** · theorem. `muBlock_pointwise_one`: The negative mu block is bounded by a fixed coefficient times gradient and scaled-velocity mode energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePassageRest.lean#L579).

**Bound the weak epsilon block** · theorem. `epsBlock_pointwise_one`: The negative epsilon block is bounded by the displayed coefficient times the four required mode-energy families. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePassageRest.lean#L658).

**The weak epsilon block is nonpositive** · theorem. `epsBlockWith_nonpos`: Admissible data make the weak epsilon block nonpositive. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePassageRest.lean#L775).

**An envelope for the combined block** · theorem. `block_le_one`: A finite constant bounds the absolute weak combined block by the total mode energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePassageRest.lean#L797).

### Breakdown.Cert.ExtendedCoercivePassageRight

The right-side terms in the split are passed through the regularization limit here. The estimates retain the weighted control needed by the final pairing inequality. §7.7: coercivity and the linearized inverse, with analytic support lemmas

**Source namespace `Breakdown.CoerciveWeak.Internal.PassageRight`.**

**The limiting right side lies in L²** · theorem. `rightSideLimit_memL2_one`: The limiting physical right side is measurable and has finite periodic square integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePassageRight.lean#L18).

**The smooth right side lies in L²** · theorem. `smoothRight_memL2_one`: The smooth right side plus the actuator combination is measurable and has finite periodic square integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePassageRight.lean#L99).

**A uniform coefficient-field bound** · theorem. `norm_field_le_abs_one`: The coefficient field norm is bounded by the absolute decay constant. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePassageRight.lean#L112).

**A weighted derivative-application bound** · theorem. `norm_fderiv_field_apply_sq_le_one`: The squared derivative applied to a vector is bounded by the squared decay constant times its radius-weighted square norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePassageRight.lean#L124).

**Smooth right sides converge in L²** · theorem. `smoothRight_tendsto_one`: The smooth approximations with the actuator term converge in periodic square integral to the limiting right side. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePassageRight.lean#L146).

**Source section `Pairing`.**

**The limiting defect annihilates tests** · theorem. `rightSide_spaceTime_one`: The difference between the forcing and the limiting right side has an integrable test pairing of zero integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePassageRight.lean#L237).

**The limiting defect is orthogonal** · theorem. `rightSide_orthogonal_periodic_one`: The forcing-minus-limit difference has zero period pairing with every permitted periodic test. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePassageRight.lean#L288).

**Use the limiting right side in a pairing** · theorem. `pairing_rightSideLimit_eq_one`: Pairing the multiplier against the forcing gives the same value as pairing it against the limiting right side. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePassageRight.lean#L312).

### Breakdown.Cert.ExtendedCoercivePassageStretch

The stretching contribution is passed from smoothed coefficients to the weak state. This file supplies the corresponding majorants and limiting identities. §7.7: coercivity and the linearized inverse, with analytic support lemmas

**Source namespace `Breakdown.CoerciveWeak.Internal.PassageStretch`.**

**A uniform derivative bound** · theorem. `norm_fderiv_le_abs`: The coefficient's spatial derivative norm is bounded by the absolute decay constant. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePassageStretch.lean#L21).

**A weighted Hessian bound** · theorem. `norm_secondDeriv_mul_le_abs`: Multiplying the specified Hessian norm by one plus the radius gives at most the absolute decay constant. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePassageStretch.lean#L30).

**A weighted bound for weak stretching** · theorem. `abs_stretchFormWith_le`: The absolute weak stretching form is bounded by the displayed constant times gradient energy and radius-weighted velocity energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePassageStretch.lean#L45).

**Finite absolute stretching integral** · theorem. `stretchFormWith_finite`: The absolute weak stretching form has finite nonnegative periodic integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePassageStretch.lean#L88).

**Polarize the stretching difference** · theorem. `stretchFormWith_sub_eq`: The difference of the two quadratic stretching forms splits into the two indicated bilinear stretching pairings. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePassageStretch.lean#L107).

**Control a change in stretching** · theorem. `abs_stretchFormWith_sub_le`: The absolute stretching difference is bounded by the squared velocity-gradient error and its product with the limiting field size. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePassageStretch.lean#L117).

**Stretching converges in integral** · theorem. `stretchFormWith_tendsto`: Energy convergence of the fields and gradients makes the absolute stretching-error integral tend to zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePassageStretch.lean#L186).

**Source section `Modes`.**

**Pointwise limits of weak piece terms** · theorem. `piece_limits_weak`: The positive density, weak remainder and stretching terms converge pointwise along the field approximation. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePassageStretch.lean#L342).

### Breakdown.Cert.ExtendedCoercivePieceDensity

The positive density term is a main source of coercivity. This file assembles its measurable representation, energy comparison and lower bound for the weak state. §7.7: coercivity and the linearized inverse, with analytic support lemmas

**Source namespace `Breakdown.CoerciveWeak.Internal.PieceDensity`.**

**Transfer a split lower bound** · theorem. `split_iff_of_block_diff`: When the block correction has the permitted zero integral difference, the two split-lower-bound formulations are equivalent. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceDensity.lean#L22).

**Epsilon remainders are nonpositive** · theorem. `epsRestWith_nonpos`: The weak epsilon remainder is nonpositive. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceDensity.lean#L64).

**Lower epsilon blocks are nonpositive** · theorem. `epsBlockLower_nonpos`: The epsilon block with the nonnegative lower-envelope coefficient is nonpositive. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceDensity.lean#L74).

**The missing envelope contribution** · theorem. `epsBlockWith_eq`: The actual weak epsilon block is the lower-envelope block minus the supremum-envelope gap times its nonnegative piece factor. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceDensity.lean#L95).

**Restrict measurability to the slab** · theorem. `aem_slab`: Almost-everywhere measurability descends to the unit-time slab measure. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceDensity.lean#L105).

**Source namespace `Breakdown.CoerciveWeak`.**

**Prove the weak smooth-density bound** · theorem. `pieceDensitySmoothWeakHolds_of`: The epsilon, mu, stretching and base-density estimates assemble the weak smooth-density interface. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceDensity.lean#L114).

### Breakdown.Cert.ExtendedCoercivePieceDensityBase

The density estimate begins with pointwise matrix and Fourier quantities. These definitions and elementary bounds make the later integral comparison explicit. §7.7: coercivity and the linearized inverse, with analytic support lemmas

**Uniform second-derivative weight bounds** · theorem. `secondDerivNorm_convD_bound`: A single nonnegative constant bounds all coefficient-weight second-derivative norms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceDensityBase.lean#L21).

**The negative base density is integrable** · theorem. `base_neg_finite`: The negative part of the base mode density has finite time-space mode-summed integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceDensityBase.lean#L48).

### Breakdown.Cert.ExtendedCoercivePieceDensityEnergy

This file relates the positive density term to the perturbation's weighted energy. Derivative continuity and energy estimates justify the comparison before integration. §7.7: coercivity and the linearized inverse, with analytic support lemmas

**Continuous first spatial derivatives** · theorem. `Breakdown.Cert.ExtendedCoercivePieceDensityEnergy.continuous_fderiv_slice_one`: Joint continuous differentiability gives continuity of the spatial derivative field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceDensityEnergy.lean#L18).

**Stretching from finite-dimensional data** · theorem. `stretchFormWith_eq`: The weak stretching form is the finite-dimensional stretching expression applied to the gradient, coefficient derivative, Hessian and velocity. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceDensityEnergy.lean#L25).

**Measurability of slab stretching** · theorem. `aemeasurable_stretchFormWith_slab`: The weak stretching form is almost everywhere measurable on the unit-time slab. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceDensityEnergy.lean#L30).

**Integrability of slab stretching** · theorem. `stretchFormWith_integrable_slab`: The weak stretching form is integrable on the unit-time slab. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceDensityEnergy.lean#L45).

**Separate the signed stretching terms** · theorem. `energy_split`: The integrated weak energy splits into vorticity energy plus the finite positive stretching integral minus the finite negative stretching integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceDensityEnergy.lean#L123).

### Breakdown.Cert.ExtendedCoercivePieceDensityEnvelope

The density proof needs a measurable coefficient envelope for vorticity stretching. This file bounds that envelope and connects it to the weak coefficient data. §7.7: coercivity and the linearized inverse, with analytic support lemmas

**Measurable bounds lie below the envelope** · theorem. `lower_envelope_le_ae`: Every permitted measurable lower bound lies below the chosen lower envelope almost everywhere. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceDensityEnvelope.lean#L15).

**Choose a lower envelope with zero loss** · theorem. `exists_lower_envelope`: There is a measurable nonnegative lower envelope whose gap from the coefficient has zero integral against each permitted measurable weight. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceDensityEnvelope.lean#L43).

**Zero envelope loss across a period** · theorem. `lintegral_iter_envelope_eq_zero`: The coefficient-envelope gap has zero iterated weighted integral over one period. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceDensityEnvelope.lean#L117).

**A nonnegative vorticity supremum** · theorem. `Breakdown.Cert.ExtendedCoercivePieceDensityEnvelope.vortGradSupWith_nonneg`: The supremum norm controlling the specified vorticity gradient is nonnegative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceDensityEnvelope.lean#L135).

**The alternating symbol is bounded** · theorem. `abs_alternatingSymbol_le`: The absolute value of every three-dimensional alternating-symbol entry is at most one. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceDensityEnvelope.lean#L139).

**Coordinate unit vectors have norm one** · theorem. `norm_unitVector_eq_one`: Each coordinate unit vector has norm one. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceDensityEnvelope.lean#L142).

**Bound a vorticity-gradient coordinate** · theorem. `abs_vortGrad_le`: A vorticity-gradient coordinate has absolute value at most nine times the bilinear-map norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceDensityEnvelope.lean#L145).

**Bound the vorticity-gradient map** · theorem. `norm_vortGradMap_le`: The operator norm of the vorticity-gradient map is at most eighty-one times the bilinear-map norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceDensityEnvelope.lean#L168).

**A uniform vorticity-gradient bound** · theorem. `vortGradSupWith_le`: The specified vorticity-gradient supremum is at most eighty-one times the absolute decay constant. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceDensityEnvelope.lean#L186).

### Breakdown.Cert.ExtendedCoercivePieceDensityMeasure

This file supplies the measurability and integrability facts for the density argument. Those facts allow the pointwise lower bounds to become a periodic integral estimate. §7.7: coercivity and the linearized inverse, with analytic support lemmas

**Source namespace `Breakdown.CoerciveWeak`.**

**An epsilon block with a lower envelope** · definition. `epsBlockLower`: The lower epsilon block uses the supplied measurable envelope in the velocity-vorticity interaction while retaining the other block terms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceDensityMeasure.lean#L15).

**Source namespace `Breakdown.CoerciveWeak.Internal.PieceDensity`.**

**Continuous first spatial derivatives** · theorem. `Breakdown.Cert.ExtendedCoercivePieceDensityMeasure.continuous_fderiv_slice_one`: Joint continuous differentiability gives continuity of the spatial derivative field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceDensityMeasure.lean#L35).

**The frame-speed bound is measurable** · theorem. `measurable_frameSpeedSup_one`: The spatial supremum controlling the moving-frame speed is measurable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceDensityMeasure.lean#L42).

**The vorticity bound is measurable** · theorem. `measurable_vortSup_one`: The spatial supremum controlling coefficient vorticity is measurable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceDensityMeasure.lean#L61).

**Source section `Pieces`.**

**Measurability of all piece contributions** · theorem. `parts_measurable`: The positive terms, base density, weak remainders, lower blocks and envelope gain factors are almost everywhere measurable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceDensityMeasure.lean#L80).

### Breakdown.Cert.ExtendedCoercivePieceDensityPassage

The density bound is first obtained for regularized coefficients. This file passes it to the weak state while preserving the measurable-envelope formulation. §7.7: coercivity and the linearized inverse, with analytic support lemmas

**Source namespace `Breakdown.CoerciveWeak.Internal.PieceDensityPassageWeak`.**

**The block minorant preserves integrals** · theorem. `lintegral_block_minorant`: Replacing the vorticity-gradient supremum by its minorant preserves the indicated time-space nonnegative block integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceDensityPassage.lean#L37).

**Equivalent minorant block bounds** · theorem. `split_of_block_minorant`: The split lower bound is unchanged when its vorticity-gradient block coefficient is replaced by the measurable minorant. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceDensityPassage.lean#L49).

**Source section `Measurable`.**

**Measurable limiting contributions** · theorem. `joint_parts_aemeasurable`: The weak remainders, stretching, zero-Hessian block and block gain are jointly almost everywhere measurable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceDensityPassage.lean#L81).

**Measurable positive mode density** · theorem. `piecePos_aemeasurable`: Each positive piece-mode density is jointly almost everywhere measurable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceDensityPassage.lean#L198).

**Measurability on one period** · theorem. `aemeasurable_slab`: Almost-everywhere measurability for volume gives the same property for the unit-period product measure. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceDensityPassage.lean#L222).

**Source namespace `Breakdown.CoerciveWeak.Internal.PieceDensityPassageWeak`.**

**Measurable terms on almost every slice** · theorem. `slice_parts_aemeasurable`: The negative remainder, stretching, zero-Hessian block and block gain have measurable spatial slices for almost every time. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceDensityPassage.lean#L229).

**The lower block gives the same bound** · theorem. `split_lower_iff`: The original weak split lower bound is equivalent to the version using the measurable lower block. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceDensityPassage.lean#L258).

**Source section `Gap`.**

**The multipliers converge in L²** · theorem. `multiplier_tendsto_weak`: The multiplier fields of the approximating perturbations converge in periodic square integral to the limiting multiplier. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceDensityPassage.lean#L291).

**Retain the first two decay bounds** · theorem. `decay_one_of`: The full coefficient decay assumptions imply the decay bounds for derivative orders zero and one. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceDensityPassage.lean#L388).

**A first-order decay constant exists** · theorem. `decay_one`: There is a common decay constant for the coefficient and its first derivative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceDensityPassage.lean#L398).

**Replace forcing by the weak limit** · theorem. `rightSide_pairing_eq_weak`: The multiplier's period pairing with the forcing equals its pairing with the limiting right side. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceDensityPassage.lean#L403).

**Right-side pairings converge** · theorem. `right_pairing_tendsto_weak`: The smooth right sides paired with their multipliers converge to the forcing paired with the limiting multiplier. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceDensityPassage.lean#L425).

**Source namespace `Breakdown.CoerciveWeak.Internal.PieceDensityPassageWeak`.**

**The multiplier gap converges** · theorem. `gap_tendsto_weak`: The approximating multiplier gaps converge to the gap of the limiting weak data. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceDensityPassage.lean#L459).

**Finite negative remainder integral** · theorem. `rest_negative_finite_weak`: The nonnegative period integral of the negative weak mode remainders is finite. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceDensityPassage.lean#L500).

**Finite negative lower-block integral** · theorem. `block_lower_negative_finite`: The nonnegative integral of the negative measurable lower block over one period is finite. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceDensityPassage.lean#L530).

**The lower split's right side is finite** · theorem. `right_finite_lower`: The right side of the lower-envelope split has finite nonnegative time-space integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceDensityPassage.lean#L579).

**Measurability of the lower split** · theorem. `left_measurable_lower`: The lower split's left side has measurable spatial slices and a measurable spatial integral as a function of time. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceDensityPassage.lean#L623).

**The combined lower block is nonpositive** · theorem. `pieceBlockLower_nonpos`: The measurable lower combined block is nonpositive. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceDensityPassage.lean#L669).

**Measurable terms for the period measure** · theorem. `period_parts_aemeasurable`: The negative remainders, negative lower block and weak stretching are almost everywhere measurable for the period measure. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceDensityPassage.lean#L680).

**Choose pointwise convergent pieces** · theorem. `pieces_converge_ae_weak`: A subsequence makes all positive mode densities, weak remainders and stretching terms converge almost everywhere. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceDensityPassage.lean#L701).

**Negative remainder integrals converge** · theorem. `rest_negative_tendsto_weak`: The nonnegative time-space integrals of the negative remainders converge to the limiting weak remainder integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceDensityPassage.lean#L729).

**Lower-block integrals converge** · theorem. `block_lower_negative_tendsto`: The negative measurable lower-block integrals converge along the field approximation. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceDensityPassage.lean#L789).

**Pass the split estimate to a subsequence** · theorem. `subsequence_limits_lower`: A subsequence gives convergence of the lower split's integrated right side and a pointwise lower-limit bound for its left side. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceDensityPassage.lean#L865).

### Breakdown.Cert.ExtendedCoercivePieceDensityRight

The density comparison includes terms on the right of the split. This file bounds those contributions by the same energy quantities used by the positive term. §7.7: coercivity and the linearized inverse, with analytic support lemmas

**Continuous first spatial derivatives** · theorem. `Breakdown.Cert.ExtendedCoercivePieceDensityRight.continuous_fderiv_slice_one`: Joint continuous differentiability gives continuity of the spatial derivative field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceDensityRight.lean#L17).

**The weak right side is measurable** · theorem. `aesm_smoothRight_one`: The smooth right-hand-side expression with weak coefficient data is almost everywhere strongly measurable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceDensityRight.lean#L24).

**Finite period energy of the right side** · theorem. `right_side_sq`: The right-hand-side expression is measurable, time periodic and has finite periodic square integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceDensityRight.lean#L43).

### Breakdown.Cert.ExtendedCoercivePieceEps

The epsilon block collects derivative and orbit errors from the weak Fourier splitting. This file defines its pieces and assembles their quantitative bounds. §7.7: coercivity and the linearized inverse, with analytic support lemmas

**Source namespace `Breakdown.CoerciveWeak.Internal.ExtendedPieceEps`.**

**Indicators are nonnegative** · theorem. `ind_nonneg_of`: The real indicator of a proposition is nonnegative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEps.lean#L31).

**Nonnegative edge-mode sums** · theorem. `edgeSum_nonneg_of`: Nonnegative harmonic coefficients and amplitudes make the edge-mode sum nonnegative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEps.lean#L35).

**Separate positive and negative parts** · theorem. `ennreal_le_step`: The real inequality gives the stated extended-nonnegative inequality after moving negative parts to the opposite side. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEps.lean#L48).

**A split bound from the sign rules** · theorem. `splitBound_of_signs`: The specified sign and summation hypotheses give a split lower bound with zero stretching term. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEps.lean#L63).

**Source section `Bounds`.**

**The flow decay constant is nonnegative** · theorem. `flow_decay_nonneg`: The flow bounds force their common decay constant to be nonnegative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEps.lean#L85).

**A decay quotient stays below its bound** · theorem. `flow_decay_le_self`: The inverse-radius decay quotient is at most the nonnegative decay constant. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEps.lean#L89).

**Control coefficient velocity modes** · theorem. `velFlowAmp_le`: The velocity-mode amplitude is bounded by three times the inverse-radius coefficient decay. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEps.lean#L92).

**Control coefficient gradient modes** · theorem. `gradFlowAmp_le`: The gradient-mode amplitude is bounded by nine times the inverse-square coefficient decay. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEps.lean#L103).

**Control weak Hessian modes** · theorem. `secondDerivWithAmp_le`: The weak-Hessian mode amplitude is bounded by twenty-seven times the inverse-cubic decay constant. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEps.lean#L117).

**Control coefficient vorticity modes** · theorem. `vortFlowAmp_le`: The coefficient-vorticity mode amplitude obeys the displayed inverse-square decay estimate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEps.lean#L132).

**Control weak vorticity-gradient modes** · theorem. `vortGradWithAmp_le`: The supplied weak vorticity-gradient mode amplitude is at most 729 times the inverse-cubic decay constant at the spatial point. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEps.lean#L144).

**Control moving-frame speed** · theorem. `frameSpeedFlow_le`: The moving-frame speed is at most the coefficient bound plus the radial similarity and rotation contributions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEps.lean#L156).

**Control the coefficient vorticity** · theorem. `vortSupFlow_le`: The coefficient-vorticity supremum is bounded by twenty-seven times the inverse-square decay constant. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEps.lean#L174).

**Decay of the vorticity-gradient bound** · theorem. `vortGradSupWith_decay`: The specified vorticity-gradient supremum is at most eighty-one times the inverse-cubic decay constant. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEps.lean#L181).

**Source section `Signs`.**

**A nonpositive weak epsilon remainder** · theorem. `restWith_nonpos`: The epsilon remainder built from the weak Hessian is nonpositive. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEps.lean#L198).

**The weak epsilon block is nonpositive** · theorem. `blockWith_nonpos`: The epsilon block built from the weak Hessian is nonpositive. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEps.lean#L217).

**Source section `Pointwise`.**

**A mode-energy bound for the remainder** · theorem. `restWith_pointwise`: The summed negative epsilon remainders are bounded by the indicated weighted vorticity, vorticity-gradient, velocity and gradient mode energies. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEps.lean#L253).

**Source namespace `Breakdown.CoerciveWeak.Internal.ExtendedPieceEps`.**

**A mode-energy bound for the block** · theorem. `blockWith_pointwise`: The negative epsilon block is bounded by the displayed coefficient times the four mode-energy families. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEps.lean#L333).

**The positive epsilon sum is integrable** · theorem. `posWith_finite`: The summed positive epsilon density has finite nonnegative time-space integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEps.lean#L452).

**Integrable negative epsilon terms** · theorem. `negWith_finite`: The negative epsilon remainder sum together with the negative block has finite nonnegative time-space integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEps.lean#L554).

**An epsilon block with a supplied bound** · definition. `blockWithSup`: The epsilon block expression uses an explicit spatial vorticity-gradient bound in its velocity-vorticity term. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEps.lean#L634).

**Insert the vorticity-gradient supremum** · theorem. `pieceEpsBlockWith_eq_blockWithSup`: Supplying the actual vorticity-gradient supremum to the parameterized block gives the weak epsilon block. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEps.lean#L650).

**Larger bounds enlarge the negative block** · theorem. `neg_blockWithSup_mono`: Increasing the nonnegative supplied vorticity-gradient bound increases the nonnegative image of the negative block. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEps.lean#L656).

**Source section `WeakCore`.**

**The measurable negative epsilon sum** · definition. `negSeriesWith`: The negative series adds the negative epsilon remainder modes to the negative block using the measurable lower envelope. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEps.lean#L674).

**The curl remainder in a moving frame** · definition. `frameRestWith`: The frame remainder combines vorticity transport, coefficient stretching, weak vorticity-gradient transport, cross-stretching and frame rotation. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEps.lean#L681).

**A signed curl-mode remainder pairing** · definition. `restTermWith`: The remainder term is the real part of the imaginary weighted pairing of a curl mode with the frame-remainder mode. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEps.lean#L689).

**Vorticity transport in a moving frame** · definition. `transportPartWith`: This field differentiates perturbation vorticity along the coefficient flow plus similarity drift minus frame rotation. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEps.lean#L695).

**Coefficient stretching of vorticity** · definition. `stretchPartWith`: This field applies the coefficient derivative to the perturbation vorticity. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEps.lean#L699).

**Transport of coefficient vorticity** · definition. `vortTransportPartWith`: This field applies the specified coefficient-vorticity derivative to the perturbation velocity. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEps.lean#L702).

**Perturbation stretching of vorticity** · definition. `vortStretchPartWith`: This field applies the perturbation derivative to the coefficient vorticity. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEps.lean#L706).

**Split the moving-frame remainder** · theorem. `frameRestWith_eq`: The frame remainder is transport minus coefficient stretching plus vorticity transport minus cross-stretching plus rotation. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEps.lean#L709).

**The positive series is measurable** · theorem. `posSeries_aemeasurable`: The positive epsilon mode series is almost everywhere measurable on the unit-time slab. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEps.lean#L718).

**The negative series is measurable** · theorem. `negSeriesWith_aemeasurable`: The negative epsilon series using the lower envelope is almost everywhere measurable on the unit-time slab. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEps.lean#L732).

**Finite energy of the right-side gradient** · theorem. `rightGradient_finite_weak`: The gradient of the weak-coefficient right side is measurable, time periodic and has finite periodic matrix square integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEps.lean#L825).

**Subtract in the second complex slot** · theorem. `cdot_sub_right'`: The complex dot expression is additive over subtraction in its second argument. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEps.lean#L832).

**Add velocity Fourier modes** · theorem. `modeVel_add_of`: The velocity mode of the sum is the sum of the velocity modes under the orbit-integrability hypotheses. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEps.lean#L835).

**Subtract velocity Fourier modes** · theorem. `modeVel_sub_of`: The velocity mode of a difference is the difference of the velocity modes under the orbit-integrability hypotheses. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEps.lean#L849).

**Continuous fields are orbit integrable** · theorem. `orbit_integrable_of_continuous`: A continuous field is integrable on each compact time-angle rotation orbit. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEps.lean#L855).

**The slab measure respects null sets** · theorem. `slabMeasure_ac_volume`: The unit-time slab measure is absolutely continuous with respect to full time-space volume. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEps.lean#L861).

**Vorticity transport is orbit integrable** · theorem. `ae_orbit_integrable_vortTransport`: The weak vorticity-transport field is integrable on almost every time-angle orbit for the slab measure. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEps.lean#L866).

**Continuous smooth remainder pieces** · theorem. `parts_continuous`: Transport, coefficient stretching, cross-stretching and rotation are jointly continuous. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEps.lean#L912).

**Split each remainder-mode pairing** · theorem. `restTermWith_split`: Almost everywhere, each signed remainder pairing splits into transport, stretching, vorticity transport, cross-stretching and rotation pairings. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEps.lean#L948).

**Separate density from the remainder** · theorem. `pieceTerm_sub_weak`: Almost everywhere, subtracting the Laplacian piece from the right-side piece leaves the positive epsilon density plus its frame-remainder pairing. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEps.lean#L977).

**The four edge interactions are summable** · theorem. `edge_summable_weak`: The velocity, gradient, vorticity-gradient and vorticity edge-interaction families are summable over modes. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEps.lean#L1019).

**Compress the vorticity transport modes** · theorem. `transport_compression_weak`: At almost every point with finite negative series, transport has compressed coefficients with edge-error control and a frame-speed piece-norm bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEps.lean#L1052).

**Compress the stretching modes** · theorem. `stretch_compression_weak`: At almost every point with finite negative series, stretching admits compressed coefficients with edge errors and a half-vorticity-supremum bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEps.lean#L1071).

**Summable velocity-mode squares** · theorem. `summable_vel_ae_weak`: The squared velocity-mode amplitudes are summable at almost every slab point. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEps.lean#L1088).

**Expand the weak vorticity derivative** · theorem. `vortTransport_orbit_expansion_weak`: Almost everywhere on the slab and orbit, the rotated vorticity derivative equals its finite harmonic expansion. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEps.lean#L1116).

**The weak symbol obeys the lower envelope** · theorem. `vortTransport_symbol_bound_weak`: At almost every slab point, the finite vorticity-derivative symbol has squared operator bound given by the measurable lower envelope. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEps.lean#L1126).

**The weak transport convolution symbol** · theorem. `vortTransport_orbit_symbol_weak`: Almost everywhere, vorticity transport has a finite harmonic convolution formula and the lower-envelope matrix bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEps.lean#L1134).

**Compress weak vorticity transport** · theorem. `vortTransport_compression_weak`: At almost every point with finite negative series, weak vorticity transport has compressed coefficients with edge control and a lower-envelope norm bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEps.lean#L1150).

**Compress the cross-stretching modes** · theorem. `vortStretch_compression_weak`: At almost every point with finite negative series, cross-stretching has compressed coefficients controlled by vorticity and gradient piece norms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEps.lean#L1191).

**Bound the transport mode pairing** · theorem. `transport_bound_weak`: Almost everywhere where the negative series is finite, the transport pairing is summable and its negative sum is controlled by edge errors plus the frame-speed piece-norm term. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEps.lean#L1210).

**Bound the stretching mode pairing** · theorem. `stretch_bound_weak`: Almost everywhere where the negative series is finite, the stretching pairing is summable and its sum is bounded by edge errors plus the half-vorticity-supremum term. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEps.lean#L1230).

**Bound weak vorticity transport** · theorem. `vortTransport_bound_weak`: Almost everywhere where the negative series is finite, the weak vorticity-transport pairing is summable and its negative sum is bounded by edge errors plus the lower-envelope piece product. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEps.lean#L1249).

**Bound the cross-stretching pairing** · theorem. `vortStretch_bound_weak`: Almost everywhere where the negative series is finite, the cross-stretching pairing is summable and its sum is bounded by edge errors plus the vorticity-supremum piece product. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEps.lean#L1269).

**Bound the frame-rotation pairing** · theorem. `rotation_bound_weak`: Almost everywhere where the negative series is finite, the rotation pairing is summable and its negative sum is bounded by the frame speed times weighted vorticity-piece energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEps.lean#L1289).

**Combine the compressed remainder bounds** · theorem. `compression_bound_weak`: Almost everywhere, under the finiteness and summability hypotheses, the negative remainder sum is bounded by the negative series minus the gradient correction. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEps.lean#L1300).

**A pointwise positive-density bound** · theorem. `pointwise_lower_weak`: Almost everywhere, where the positive and negative series are finite, the positive epsilon density is bounded by the right-side pairing and negative corrections. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEps.lean#L1398).

**Integrate the weak epsilon estimate** · theorem. `core_of_weak_parts`: The integrated positive epsilon density is bounded by the epsilon right-side pairing plus the integrated measurable negative series. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEps.lean#L1442).

**Source namespace `Breakdown.CoerciveWeak.Internal.ExtendedPieceEps`.**

**The measurable epsilon inequality** · theorem. `core_inequality_measurable`: The epsilon core inequality holds with the measurable lower-envelope block in its negative contribution. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEps.lean#L1471).

**The full weak epsilon inequality** · theorem. `core_inequality_weak`: Replacing the lower-envelope block through its integral identity gives the epsilon core inequality with the actual weak block. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEps.lean#L1494).

### Breakdown.Cert.ExtendedCoercivePieceEpsAeSecondDeriv

The epsilon estimates require almost-everywhere second-derivative information. This file turns the weak Hessian into the pointwise derivative identities used in the orbit calculations. §7.7: coercivity and the linearized inverse, with analytic support lemmas

**Coordinates inherit a Lipschitz bound** · theorem. `coord_slopeBound`: Each coordinate of a Lipschitz vector field satisfies the same Lipschitz bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsAeSecondDeriv.lean#L19).

**Local integrability of gradient columns** · theorem. `column_locallyIntegrable`: Each coordinate-direction column of the weak gradient is locally integrable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsAeSecondDeriv.lean#L26).

**Directional and weak derivative pairings** · theorem. `integral_lineDeriv_coord`: The classical directional derivative and the given weak derivative have equal pairings against the compactly supported scalar test. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsAeSecondDeriv.lean#L34).

**Weak gradients agree with derivatives** · theorem. `ae_hasFDerivAt_of_weakGradient`: A Lipschitz field with the given weak gradient has that gradient as its derivative almost everywhere. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsAeSecondDeriv.lean#L66).

**Differentiate the coefficient gradient** · theorem. `ae_hasFDerivAt_fderiv`: The supplied weak Hessian differentiates the coefficient gradient at almost every spatial point on each time slice. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsAeSecondDeriv.lean#L102).

**Actual and supplied Hessians agree** · theorem. `ae_secondDerivField_eq`: The actual second-derivative field agrees almost everywhere on each time slice with the supplied weak Hessian. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsAeSecondDeriv.lean#L125).

### Breakdown.Cert.ExtendedCoercivePieceEpsExpansion

This file expands the epsilon contribution into named algebraic terms. The expansion separates the terms that receive different derivative, transport and stretching bounds. §7.7: coercivity and the linearized inverse, with analytic support lemmas

**Once differentiable spatial slices** · theorem. `slice_contDiff_of_once`: A jointly once continuously differentiable field has once continuously differentiable spatial slices. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsExpansion.lean#L17).

**Continuous first derivative slices** · theorem. `continuous_slice_fderiv_of_once`: The spatial derivative of the once continuously differentiable joint field is jointly continuous. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsExpansion.lean#L21).

**Differentiate the mode integrand** · theorem. `hasFDerivAt_integrand_of_once`: The specified mode-integrand derivative is its spatial derivative under the once differentiable coefficient hypotheses. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsExpansion.lean#L26).

**A continuous mode-integrand derivative** · theorem. `continuous_integrandDeriv_of_once`: The mode-integrand spatial derivative varies continuously across the compact time-angle parameters. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsExpansion.lean#L59).

**A continuous mode integrand** · theorem. `continuous_integrand_of_once`: The coefficient's mode integrand is continuous in the time-angle variables. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsExpansion.lean#L80).

**A velocity mode as a box integral** · theorem. `modeVel_eq_box_of_once`: The velocity-mode coordinate is the normalized integral of its rotated integrand over the time-angle box. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsExpansion.lean#L93).

**Differentiate a velocity mode** · theorem. `modeVel_hasFDerivAt_of_once`: A velocity-mode coordinate is spatially differentiable, and its derivative on each unit vector is the corresponding gradient-mode coordinate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsExpansion.lean#L103).

**Differentiable coefficient slices** · theorem. `slice_differentiable_of_once`: Each fixed-time coefficient field is spatially differentiable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsExpansion.lean#L140).

**The real gradient harmonic expansion** · theorem. `grad_expansion_once`: The rotated coefficient gradient equals its zero mode plus the real parts of the finite nonzero harmonic terms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsExpansion.lean#L144).

**Differentiate the mean field** · theorem. `meanField_fderiv_apply_once`: A coordinate of the mean-field derivative is the real part of the corresponding zero gradient mode. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsExpansion.lean#L189).

**The complex gradient harmonic expansion** · theorem. `gradW_expansion_once`: The complexified rotated coefficient gradient equals the mean-field gradient plus its finite nonzero harmonic expansion. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsExpansion.lean#L206).

**The vorticity harmonic expansion** · theorem. `vortW_expansion_once`: The rotated coefficient vorticity is the mean-field curl plus the finite harmonic sum of the mode curls. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsExpansion.lean#L220).

### Breakdown.Cert.ExtendedCoercivePieceEpsModeIdentity

The epsilon calculation is expressed through time-angle Fourier modes. These identities connect the physical coefficient and its mode derivatives to the modal energy terms. §7.7: coercivity and the linearized inverse, with analytic support lemmas

**The measure on one rotation orbit** · abbreviation. `orbitBox`: The orbit box uses the product time-angle measure for one temporal and angular period. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsModeIdentity.lean#L21).

**Null sets on almost every orbit** · theorem. `ae_orbit_of_ae`: A time-space almost-everywhere property holds almost everywhere along almost every time-angle rotation orbit. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsModeIdentity.lean#L23).

**Integrability of bounded orbit fields** · theorem. `ae_orbit_integrable_of_bound`: The measurable bounded field is integrable on almost every compact time-angle orbit. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsModeIdentity.lean#L27).

**Orbit equality gives equal modes** · theorem. `modeVel_congr_orbit`: Fields agreeing almost everywhere along the relevant orbit have equal velocity modes at its base point. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsModeIdentity.lean#L40).

**Good weak-Hessian points** · theorem. `ae_good_point`: At almost every time-space point the supplied weak Hessian differentiates the gradient and is symmetric. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsModeIdentity.lean#L60).

**The trace-free curl-product algebra** · theorem. `frame_alg_weak`: For the trace-free matrices in the calculation, the alternating-symbol product sum becomes the two negative matrix-curl actions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsModeIdentity.lean#L110).

**A coordinate of a matrix action** · theorem. `apply_expand_weak`: A coordinate of a linear-map application is the sum of input coordinates times the corresponding matrix entries. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsModeIdentity.lean#L121).

**Curl of two trace-free products** · theorem. `curl_comp_pair_weak`: For the trace-free pair, the sum of curls of the two compositions equals the negative sum of the crossed matrix-curl actions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsModeIdentity.lean#L130).

**Differentiate a time-dependent curl** · theorem. `hasDerivAt_curlVec_weak`: A differentiable matrix curve has curl derivative equal to the curl of its matrix derivative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsModeIdentity.lean#L148).

**Interchange Hessian arguments** · theorem. `flip_eq_of_symm_weak`: The actual Hessian is unchanged when its two spatial derivative arguments are interchanged under the smoothness hypothesis. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsModeIdentity.lean#L166).

**The moving-frame vorticity identity** · theorem. `vortField_identity_weak`: The right-side curl minus the Laplacian curl splits into temporal frequency, vorticity, frame rotation and weak coefficient-remainder terms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsModeIdentity.lean#L172).

**A continuous derivative envelope exists** · theorem. `ae_norm_gradField_smoothRight_le`: The right-side gradient norm has a continuous upper envelope outside a time-space null set. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsModeIdentity.lean#L263).

**A continuous field is orbit integrable** · theorem. `orbit_integrable_of_continuous_weak`: The field is integrable on each compact time-angle rotation orbit. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsModeIdentity.lean#L314).

**Add modes using orbit integrability** · theorem. `modeVel_add_orbit`: Orbit integrability permits velocity-mode extraction to commute with field addition. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsModeIdentity.lean#L320).

**The weak curl-mode equation** · theorem. `ae_mode_identity_weak`: Almost everywhere, the right-side vorticity mode minus the Laplacian mode is the frame-frequency multiple, the vorticity mode and the remainder mode. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsModeIdentity.lean#L334).

**Orbit equality preserves box integrals** · theorem. `boxInt_congr_orbit`: Almost-everywhere agreement on the time-angle box preserves its normalized integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsModeIdentity.lean#L409).

**The mode of a finite harmonic product** · theorem. `mode_product_orbit`: A finite coefficient expansion turns the product-field mode into the corresponding finite convolution with shifted velocity modes. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsModeIdentity.lean#L425).

### Breakdown.Cert.ExtendedCoercivePieceEpsOrbitSecondDeriv

Second derivatives along the symmetry orbit enter the epsilon block. This file proves their formulas and bounds from the weak spatial second derivatives. §7.7: coercivity and the linearized inverse, with analytic support lemmas

**The rotated Hessian mode integrand** · definition. `secondDerivIntegrand`: The Hessian integrand combines the Fourier phase with the rotated supplied second derivative and one selected coordinate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsOrbitSecondDeriv.lean#L22).

**Evaluate the Hessian integrand** · theorem. `secondDerivIntegrand_apply`: Applying the Hessian integrand to a direction gives the Fourier factor times the corresponding rotated Hessian coordinate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsOrbitSecondDeriv.lean#L28).

**Differentiate a gradient-mode integrand** · theorem. `hasFDerivAt_gradModeIntegrand_weak`: At a good weak-Hessian point, the gradient-mode integrand has the supplied rotated Hessian integrand as its derivative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsOrbitSecondDeriv.lean#L33).

**A Lipschitz gradient-mode integrand** · theorem. `increment_gradModeIntegrand`: The derivative decay bound makes the gradient-mode integrand Lipschitz with the absolute decay constant. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsOrbitSecondDeriv.lean#L45).

**Continuity of the gradient integrand** · theorem. `continuous_gradModeIntegrand_once`: The gradient-mode integrand is continuous in the time-angle variables. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsOrbitSecondDeriv.lean#L76).

**A gradient mode as a box integral** · theorem. `modeGrad_eq_box_once`: The gradient-mode coordinate is the normalized time-angle integral of the rotated gradient integrand. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsOrbitSecondDeriv.lean#L86).

**The Hessian integrand is measurable** · theorem. `aestronglyMeasurable_secondDerivIntegrand`: The rotated weak-Hessian mode integrand is almost everywhere strongly measurable on the time-angle box. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsOrbitSecondDeriv.lean#L97).

**Differentiate a gradient mode** · theorem. `modeGrad_hasFDerivAt_weak`: The derivative of a gradient-mode coordinate on each unit vector is the corresponding supplied Hessian-mode coordinate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsOrbitSecondDeriv.lean#L118).

**Uniformly bounded coefficient gradients** · theorem. `fderiv_bound`: The coefficient gradient has the common uniform norm bound over all time and space. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsOrbitSecondDeriv.lean#L152).

**The real weak-Hessian expansion** · theorem. `secondDeriv_expansion_weak`: The rotated supplied Hessian equals its zero mode plus the real part of the finite nonzero harmonic expansion. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsOrbitSecondDeriv.lean#L156).

**The zero Hessian mode is real** · theorem. `modeSecondDeriv_zero_real`: The zero Hessian mode equals the complexification of its real part. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsOrbitSecondDeriv.lean#L196).

**The complex weak-Hessian expansion** · theorem. `secondDerivC_expansion_weak`: The complexified rotated supplied Hessian equals its zero mode plus the finite nonzero harmonic expansion. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsOrbitSecondDeriv.lean#L202).

**Expand the vorticity derivative** · theorem. `vortGrad_expansion_at`: Applying the curl-gradient combination to the Hessian expansion gives the finite harmonic expansion of the rotated vorticity derivative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsOrbitSecondDeriv.lean#L219).

**The Hessian expansion holds on orbits** · theorem. `orbit_expansion_ae`: Outside null sets in time-space and on the orbit, the rotated vorticity derivative equals its finite Hessian-mode expansion. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsOrbitSecondDeriv.lean#L243).

### Breakdown.Cert.ExtendedCoercivePieceEpsRightGradient

The epsilon bound includes derivatives of the right-side mode. This file controls that gradient contribution with the coefficient decay and the perturbation energy. §7.7: coercivity and the linearized inverse, with analytic support lemmas

**A product-rule right-side bound** · theorem. `norm_fderiv_smoothRight_weak_le`: At differentiability points, the right-side derivative is bounded by transport, third-derivative and coefficient-perturbation product terms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsRightGradient.lean#L17).

**An integral bound gives finiteness** · theorem. `periodLIntegral_lt_top_of_ae_le`: An almost-everywhere nonnegative domination by a function with finite period integral makes the period integral finite. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsRightGradient.lean#L46).

**Finite right-side gradient energy** · theorem. `gradField_smoothRight_sq_finite_weak`: The weak-coefficient right-side gradient has finite periodic matrix square integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsRightGradient.lean#L51).

**Continuity of the weak right side** · theorem. `continuous_smoothRight_weak`: The right-hand-side field is jointly continuous under the weak-coefficient regularity assumptions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsRightGradient.lean#L158).

**Assemble right-side gradient regularity** · theorem. `rightGradient_finite_of_weak`: The right-side gradient is measurable, time periodic and square-integrable over one period. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsRightGradient.lean#L178).

### Breakdown.Cert.ExtendedCoercivePieceEpsRotation

Rotation terms arise when spatial derivatives are taken in an orbit-adapted frame. These identities and bounds account for those terms in the epsilon estimate. §7.7: coercivity and the linearized inverse, with analytic support lemmas

**Source namespace `Breakdown.CoerciveWeak.Internal.ExtendedPieceEps`.**

**A quarter-turn in the axial plane** · definition. `perpVec`: The perpendicular vector negates the second coordinate, moves the first into the second and sets the axial coordinate to zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsRotation.lean#L19).

**The physical vorticity field** · definition. `curlField`: The vorticity field is the curl vector of each spatial velocity derivative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsRotation.lean#L21).

**Frame rotation of vorticity** · definition. `rotationPartWith`: The rotation field is the frame coefficient times the axial-plane quarter-turn of perturbation vorticity. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsRotation.lean#L23).

**A signed imaginary curl-mode pairing** · definition. `modePart`: The mode pairing is the real part of the imaginary signed-weighted complex pairing of the curl mode with the chosen field mode. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsRotation.lean#L26).

**Source namespace `Breakdown.CoerciveWeak.Internal.ExtendedPieceEps.RotationPart`.**

**Continuous spatial slice derivatives** · theorem. `slice_fderiv_continuous`: The slice derivative field is jointly continuous under the smoothness assumptions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsRotation.lean#L32).

**Curl modes equal vorticity modes** · theorem. `curlMode_eq_modeVel`: Taking the curl of a gradient mode gives the velocity mode of the physical vorticity field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsRotation.lean#L37).

**The sign magnitude is the indicator** · theorem. `Breakdown.Cert.ExtendedCoercivePieceEpsRotation.abs_sgn_eq_ind`: The absolute piece sign equals the indicator of membership in the piece or its reflected copy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsRotation.lean#L46).

**The first rotated coordinate** · theorem. `rot_coord0`: Axial rotation gives cosine times the first coordinate minus sine times the second. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsRotation.lean#L51).

**The second rotated coordinate** · theorem. `rot_coord1`: Axial rotation gives sine times the first coordinate plus cosine times the second. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsRotation.lean#L54).

**The axial coordinate is fixed** · theorem. `rot_coord2`: Axial rotation leaves the third coordinate unchanged. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsRotation.lean#L57).

**The first perpendicular coordinate** · theorem. `perp_coord0`: The first coordinate of the axial-plane perpendicular is the negative second coordinate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsRotation.lean#L60).

**The second perpendicular coordinate** · theorem. `perp_coord1`: The second coordinate of the axial-plane perpendicular is the original first coordinate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsRotation.lean#L62).

**The perpendicular has zero axial part** · theorem. `perp_coord2`: The axial coordinate of the perpendicular vector is zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsRotation.lean#L64).

**Rotation commutes with the quarter-turn** · theorem. `rot_perp`: Rotating a scaled axial-plane quarter-turn gives the same scaled quarter-turn of the rotated vector. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsRotation.lean#L66).

**Extract a common real scalar from a mode** · theorem. `modeAverage_congr_mul`: An orbit identity by a fixed real factor gives the same scalar relation between the mode averages. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsRotation.lean#L79).

**The modes of frame rotation** · theorem. `modeVel_rotationPart`: The rotation-field mode is the frame-scaled quarter-turn of the vorticity mode. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsRotation.lean#L86).

**Bound the imaginary rotation pairing** · theorem. `rotation_term_le`: The absolute imaginary rotation pairing is at most the weight magnitude times the frame speed times the complex squared norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsRotation.lean#L98).

**Bound the total rotation contribution** · theorem. `rotation_bound_of`: The rotation-mode family is summable almost everywhere and its negative sum is bounded by the frame coefficient times weighted piece energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsRotation.lean#L127).

### Breakdown.Cert.ExtendedCoercivePieceEpsSlope

The epsilon estimate uses a slope bound for coefficient modes. This file derives that control from Lipschitz and weak-derivative information. §7.7: coercivity and the linearized inverse, with analytic support lemmas

**Source namespace `Breakdown.CoerciveWeak.Internal.WeakGradientSlope`.**

**An operator bound from three columns** · theorem. `opNorm_le_of_columns`: If each coordinate column is bounded by the same constant, the operator norm is at most three times that constant. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsSlope.lean#L18).

**Source section `Mollify`.**

**A reflected normalized test kernel** · theorem. `test_reflect`: The reflected translated normalized bump is a scalar test function. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsSlope.lean#L36).

**Derivative of a reflected bump** · theorem. `fderiv_reflect`: Differentiating the reflected bump introduces a minus sign in the original kernel derivative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsSlope.lean#L41).

**Differentiate a spatial convolution** · theorem. `mollify_hasFDerivAt`: The convolution with a smooth bump has derivative given by convolving with the bump derivative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsSlope.lean#L52).

**A derivative column after smoothing** · theorem. `mollify_column`: The derivative of the smoothed field on a unit vector equals the kernel integral of the corresponding weak-gradient column. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsSlope.lean#L58).

**Smoothing preserves a column bound** · theorem. `mollify_column_norm_le`: The kernel integral of a uniformly bounded weak-gradient column has the same norm bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsSlope.lean#L81).

**A Lipschitz bound for smoothed fields** · theorem. `mollify_slopeBound`: The column bounds give a Lipschitz constant of three times the common column bound for each smoothed field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsSlope.lean#L95).

**Weak gradients give Lipschitz bounds** · theorem. `slopeBound_of_weakGradient`: Passing the smoothing estimate to the limit gives a Lipschitz constant of three times the weak-gradient column bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsSlope.lean#L107).

**Source namespace `Breakdown.CoerciveWeak.Internal.WeakGradientSlope`.**

**Lipschitz coefficient-gradient columns** · theorem. `column_slopeBound`: The weak Hessian bound gives a Lipschitz constant of three times the decay constant for each gradient column. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsSlope.lean#L123).

**The coefficient gradient is Lipschitz** · theorem. `fderiv_slopeBound`: Combining the three column bounds gives a Lipschitz constant of nine times the decay constant for the gradient map. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsSlope.lean#L139).

### Breakdown.Cert.ExtendedCoercivePieceEpsStretch

The stretching part of the epsilon block is bounded here. The calculation combines coefficient-vorticity terms with Fourier-mode amplitudes and weighted energy. §7.7: coercivity and the linearized inverse, with analytic support lemmas

**Source namespace `Breakdown.CoerciveWeak.Internal.PieceEpsStretch`.**

**The symmetric harmonic matrix part** · definition. `symPart`: The symmetric part averages each harmonic coefficient matrix with its transpose. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsStretch.lean#L19).

**The antisymmetric harmonic matrix part** · definition. `antiPart`: The antisymmetric part is half the difference of each harmonic coefficient matrix and its transpose. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsStretch.lean#L22).

**Recover the matrix from its two parts** · theorem. `sym_add_anti`: Each harmonic matrix is the sum of its symmetric and antisymmetric parts. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsStretch.lean#L25).

**Symmetric coefficients are conjugate** · theorem. `symPart_conj`: The symmetric coefficient at the opposite harmonic is the conjugate transpose of the original symmetric coefficient. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsStretch.lean#L30).

**The antisymmetric part of the symbol** · theorem. `symbolMat_anti`: The symbol built from antisymmetric coefficients is half the difference of the full symbol and its transpose. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsStretch.lean#L37).

**Add in the second complex slot** · theorem. `cdot_add_right`: The complex dot expression is additive in its second argument. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsStretch.lean#L44).

**Split a matrix piece pairing** · theorem. `pairPiece_split`: Splitting the matrix coefficients into two families splits the corresponding piece pairing into their sum. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsStretch.lean#L47).

**Conjugate a symmetric piece pairing** · theorem. `pairPiece_conj`: Conjugation of the symmetric piece pairing corresponds to negating the harmonic and shifting the mode index. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsStretch.lean#L59).

**The symmetric pairing is real** · theorem. `tsum_pair_im`: The summable symmetric self-pairing has zero imaginary part. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsStretch.lean#L74).

**Control the antisymmetric matrix action** · theorem. `anti_rows_bound`: The squared action of a real antisymmetric matrix is bounded by one quarter of its curl-coordinate energy times the input square. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsStretch.lean#L92).

**Curl norm in a rotated frame** · theorem. `curl_components`: The squared curl norm is the sum of the three antisymmetric derivative-coordinate squares in the rotated axial frame. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsStretch.lean#L102).

**Compress a symmetric self-pairing** · theorem. `compression_self_split`: The coefficient split gives compressed modes with edge errors and a self-pairing bound controlled by the antisymmetric symbol. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsStretch.lean#L111).

**The stretching coefficient matrices** · definition. `stretchCoeff`: The stretching coefficients combine the mean-field derivative with the nonzero gradient modes. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsStretch.lean#L264).

**Source section `Bound`.**

**The half-vorticity stretching bound** · theorem. `stretch_compression_of`: Almost everywhere, compressed stretching modes admit edge-error control and a signed pairing bounded by half the coefficient-vorticity supremum times piece energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsStretch.lean#L273).

### Breakdown.Cert.ExtendedCoercivePieceEpsSumSecondPartials

The epsilon calculation includes the sum of spatial second partial derivatives. This file separates its mode contributions and proves the required signed integral bound. §7.7: coercivity and the linearized inverse, with analytic support lemmas

**Source section `Parts`.**

**Exchange the epsilon sum and integral** · theorem. `weakPairingExchange`: The epsilon pairing is the integral of its summable mode terms, with integrability established for the summed expression. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsSumSecondPartials.lean#L23).

**An integrable epsilon correction** · theorem. `weakGradPartIntegrable`: The gradient correction in the epsilon piece estimate is integrable on the time slab. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsSumSecondPartials.lean#L99).

**The sign magnitude is the indicator** · theorem. `Breakdown.Cert.ExtendedCoercivePieceEpsSumSecondPartials.abs_sgn_eq_ind`: The absolute piece sign equals the indicator of membership in the piece or its reflected copy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsSumSecondPartials.lean#L172).

**Bound a scaled weight derivative** · theorem. `norm_fderiv_const_mul_le`: The derivative norm of a scalar multiple is at most the scalar magnitude times the original derivative norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsSumSecondPartials.lean#L177).

**Cauchy-Schwarz within a mode piece** · theorem. `piece_sum_mul_le`: The weighted product over the symmetric mode piece is summable and bounded by the coefficient times the two piece norms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsSumSecondPartials.lean#L195).

**A lower bound for the Laplacian pairing** · theorem. `weakSumSecondPartialsPairingLower`: The epsilon Laplacian pairing plus its integrated gradient correction is nonnegative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsSumSecondPartials.lean#L249).

**A nonnegative Laplacian correction** · theorem. `weakSumSecondPartialsLower`: The gradient correction plus the summed Laplacian mode terms is integrable and has nonnegative slab integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsSumSecondPartials.lean#L394).

### Breakdown.Cert.ExtendedCoercivePieceEpsSymbolBound

The Fourier symbol controls the modal epsilon energy. This file proves the pointwise symbol bounds and their summed quadratic consequences. §7.7: coercivity and the linearized inverse, with analytic support lemmas

**A finite vorticity-derivative symbol** · definition. `symbolEntry`: Each symbol entry is the zero Hessian curl-gradient mode plus the finite phase-weighted nonzero harmonic terms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsSymbolBound.lean#L22).

**The squared action of the symbol** · definition. `symbolNormSq`: The symbol norm expression is the squared complex norm of the matrix symbol acting on its input. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsSymbolBound.lean#L28).

**The complex squared norm is nonnegative** · theorem. `cnormSq_nonneg_of`: The sum of squared complex coordinate magnitudes is nonnegative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsSymbolBound.lean#L32).

**Zero squared norm forces zero** · theorem. `eq_zero_of_cnormSq_eq_zero`: A complex vector with zero complex squared norm is the zero vector. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsSymbolBound.lean#L35).

**Fourier phases respect periods** · theorem. `torusPhase_shift`: Integer temporal shifts and full angular turns leave each torus Fourier phase unchanged. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsSymbolBound.lean#L40).

**The symbol norm respects periods** · theorem. `symbolNormSq_shift`: The squared symbol action is unchanged by integer time shifts and full angular turns. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsSymbolBound.lean#L51).

**Continuous symbol action** · theorem. `continuous_symbolNormSq`: The squared symbol action is continuous jointly in the two phase variables and the complex input vector. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsSymbolBound.lean#L57).

**Continuous phase dependence** · theorem. `continuous_symbolNormSq_angle`: For a fixed input, the squared symbol action is continuous in the time-angle variables. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsSymbolBound.lean#L64).

**Extend an almost-everywhere box bound** · theorem. `le_of_ae_box`: Continuity upgrades the almost-everywhere bound on the time-angle box to a bound at every point of the closed box. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsSymbolBound.lean#L71).

**The orbit derivative norms are bounded** · theorem. `bddAbove_vortGradMap`: The vorticity-gradient operator norms along all time-angle orbit points form a bounded set. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsSymbolBound.lean#L98).

**The symbol obeys the orbit supremum** · theorem. `symbol_le_sup_of_expansion`: The orbit expansion bounds the squared symbol action by the squared vorticity-gradient supremum times the input square. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsSymbolBound.lean#L108).

**Measurable symbol action in time-space** · theorem. `aem_symbolNormSq`: For fixed phases and input vector, the squared symbol action is almost everywhere measurable in time-space. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsSymbolBound.lean#L151).

**Absolute continuity of slab measure** · theorem. `slab_ac_volume`: The time-slab measure is absolutely continuous with respect to time-space volume. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsSymbolBound.lean#L168).

**A lower-envelope bound on the slab** · theorem. `ae_le_realMinorant_slab`: The admissible measurable spatially bounded expression is below the real minorant almost everywhere on the slab. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsSymbolBound.lean#L172).

**A common lower-envelope symbol bound** · theorem. `symbolNormSq_bound_of_expansion`: Outside one slab null set, the squared symbol action is bounded by the lower-envelope square for all phases and all complex inputs. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsSymbolBound.lean#L218).

**The expanded symbol bound** · theorem. `symbol_bound_of_expansion`: The explicit finite Hessian-mode symbol has the lower-envelope operator bound almost everywhere, uniformly in phases and input vectors. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsSymbolBound.lean#L271).

### Breakdown.Cert.ExtendedCoercivePieceEpsTransport

The epsilon transport term is estimated separately from stretching and rotation. These identities place its derivatives and frequency factors under the common energy bound. §7.7: coercivity and the linearized inverse, with analytic support lemmas

**Source namespace `Breakdown.CoerciveWeak.Internal.ExtendedPieceEpsTransport`.**

**The velocity harmonic expansion** · theorem. `velW_expansion_of_continuous`: The rotated continuous coefficient field equals its mean field plus the finite nonzero harmonic expansion. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsTransport.lean#L20).

**The first axial-rotation coordinate** · theorem. `rc0`: The first rotated coordinate is cosine times the first coordinate minus sine times the second. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsTransport.lean#L34).

**The second axial-rotation coordinate** · theorem. `rc1`: The second rotated coordinate is sine times the first coordinate plus cosine times the second. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsTransport.lean#L37).

**Axial rotation fixes the third axis** · theorem. `rc2`: The third coordinate is unchanged by axial rotation. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsTransport.lean#L40).

**The first axial-perpendicular coordinate** · theorem. `pc0`: The first coordinate of the axial perpendicular is the negative second coordinate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsTransport.lean#L43).

**The second coordinate normal to the axis** · theorem. `pc1`: The second coordinate of the axial perpendicular is the first coordinate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsTransport.lean#L45).

**No axial part in the perpendicular** · theorem. `pc2`: The axial perpendicular has zero third coordinate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsTransport.lean#L47).

**Rotate the moving-frame velocity** · theorem. `rot_frame_weak`: Undoing axial rotation moves the similarity drift and frame rotation to the base point while rotating the coefficient velocity. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsTransport.lean#L49).

**The epsilon piece avoids its reflection** · theorem. `piece_disjoint_weak`: No mode in the epsilon piece has its negative in the same piece. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsTransport.lean#L66).

**Restrict a square sum to a piece** · theorem. `ind_summable_weak`: Multiplying a summable complex square family by the symmetric-piece indicator preserves summability. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsTransport.lean#L81).

**Summable gradient and curl mode energies** · theorem. `summable_ae_weak`: The vorticity, vorticity-gradient and gradient squared-amplitude families are summable almost everywhere on the slab. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsTransport.lean#L90).

**Source section `Bound`.**

**Compress transport with edge errors** · theorem. `transport_compression_of`: The transport modes admit compressed coefficients with boundary-mode errors and a frame-speed product bound almost everywhere. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsTransport.lean#L142).

**Compress the vorticity stretch term** · theorem. `vortStretch_compression_of`: The cross-stretching modes admit compressed coefficients with edge errors and a coefficient-vorticity product bound almost everywhere. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceEpsTransport.lean#L232).

### Breakdown.Cert.ExtendedCoercivePieceMu

The mu block collects lower-order errors in the weak pairing split. This file combines its pressure, reflection and transport estimates into one controlled contribution. §7.7: coercivity and the linearized inverse, with analytic support lemmas

**Nonnegative piece indicators** · theorem. `ind_nonneg'`: The real indicator of a proposition is nonnegative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMu.lean#L19).

**The edge-mode sum is nonnegative** · theorem. `edgeSum_nonneg`: Nonnegative harmonic coefficients and amplitudes give a nonnegative edge-mode sum. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMu.lean#L24).

**A nonnegative frame-speed supremum** · theorem. `frameSpeedSup_nonneg`: The supremum controlling moving-frame speed is nonnegative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMu.lean#L32).

**Piece norms are nonnegative** · theorem. `pieceNorm_nonneg`: The square-root norm of the selected mode piece is nonnegative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMu.lean#L36).

**Nonpositive errors give the split bound** · theorem. `splitLowerBound_of_nonpos`: The nonpositive remainder and block hypotheses give the split lower bound with zero stretching contribution. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMu.lean#L39).

**The mu seminorm as a mode integral** · theorem. `seminorm_eq`: The mu piece seminorm equals the integrated mode squares weighted by the spatial weight and absolute frame frequency. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMu.lean#L65).

**The mu seminorm is finite** · theorem. `seminorm_finite`: The mu piece seminorm has finite nonnegative value. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMu.lean#L112).

**The negative mu correction is finite** · theorem. `negPart_finite`: The negative mu remainder modes plus the negative block have finite nonnegative time-space integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMu.lean#L159).

**Split the mu right-side pairing** · theorem. `pairing_additive`: The mu pairing splits into the transport-like right-side part and the reflected solenoidal correction. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMu.lean#L251).

**Bound the reflected correction below** · theorem. `reflected_pairing_bound`: The reflected correction's mu pairing is bounded below by the negative integrated pressure budget. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMu.lean#L284).

**The integrated mu transport bound** · theorem. `Breakdown.Cert.ExtendedCoercivePieceMu.transport_bound`: The integrated frequency gain minus edge and block losses is a lower bound for the transport part of the mu pairing. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMu.lean#L301).

**Subtract the pressure budget** · theorem. `pressure_bound`: Subtracting the integrated pressure budget from the transport pairing gives a lower bound for the solenoidal mu pairing. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMu.lean#L316).

### Breakdown.Cert.ExtendedCoercivePieceMuPressure

The pressure-related part of the mu block is bounded through its Fourier and gradient identities. These lemmas keep that contribution compatible with the divergence-free energy estimate. §7.7: coercivity and the linearized inverse, with analytic support lemmas

**Differentiate the antisymmetric tensor** · theorem. `tensor_coord`: The coordinate derivative of the antisymmetric transport tensor expands into the four product-rule terms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMuPressure.lean#L22).

**Expand a linear-map coordinate** · theorem. `apply_coord`: A coordinate of a linear-map application is the sum of matrix entries weighted by input coordinates. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMuPressure.lean#L37).

**The commutator annihilates gradients** · theorem. `tensor_orthogonal`: The divergence-free transport commutator has zero spatial pairing with a scalar gradient. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMuPressure.lean#L43).

**The transport remainder kills gradients** · theorem. `transport_orthogonal`: The right-side expression after subtracting twice the coefficient-gradient action has zero period pairing with periodic scalar gradients. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMuPressure.lean#L132).

**Split off the reflected solenoidal part** · theorem. `solenoidal_split`: The solenoidal right side equals the transport remainder plus the reflection of the coefficient-gradient term across its solenoidal projection. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMuPressure.lean#L193).

### Breakdown.Cert.ExtendedCoercivePieceMuReflect

Reflection symmetry supplies cancellations in the mu block. This file proves the reflected coefficient and mode identities needed for those cancellations and their bounds. §7.7: coercivity and the linearized inverse, with analytic support lemmas

**Source namespace `Breakdown.Coercive.Internal.WeakPieceMuHarmonics`.**

**The finite harmonic orbit expansion** · theorem. `orbit_expansion`: The rotated coefficient field equals the finite phase-weighted sum of its harmonic velocity modes. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMuReflect.lean#L19).

**Continuity of the coefficient derivative** · theorem. `continuous_slice_fderiv_of`: The spatial derivative of the coefficient is jointly continuous. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMuReflect.lean#L34).

**Differentiate the rotated mode integrand** · theorem. `hasFDerivAt_integrand_of`: The mode integrand has the displayed spatial derivative under the local differentiability hypotheses. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMuReflect.lean#L41).

**A continuous mode derivative integrand** · theorem. `continuous_integrandDeriv_of`: The derivative of the rotated mode integrand is continuous on the time-angle parameters. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMuReflect.lean#L74).

**Continuity of the rotated integrand** · theorem. `continuous_integrand_of`: The rotated mode integrand is continuous in time and angle. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMuReflect.lean#L95).

**The normalized velocity-mode integral** · theorem. `modeVel_eq_box_of`: Each velocity-mode coordinate is the normalized time-angle box integral of its rotated test integrand. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMuReflect.lean#L108).

**Source section `Derivative`.**

**Local coefficient-mode derivatives** · theorem. `modeVel_hasFDerivAt_local`: The velocity-mode derivative exists locally and its unit-vector values are the corresponding gradient modes. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMuReflect.lean#L122).

**The real gradient orbit expansion** · theorem. `grad_orbit_expansion_re`: The rotated gradient coordinate is the sum of the real parts of its finite harmonic terms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMuReflect.lean#L168).

**Source namespace `Breakdown.Coercive.Internal.WeakPieceMuHarmonics`.**

**The complex gradient orbit expansion** · theorem. `grad_orbit_expansion`: The complexified rotated gradient coordinate equals its finite phase-weighted harmonic expansion. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMuReflect.lean#L213).

**Bound a coefficient-gradient mode** · theorem. `stretch_mode_le`: The coefficient derivative acting on velocity has mode amplitude bounded by the finite convolution of gradient and velocity amplitudes. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMuReflect.lean#L227).

**Source namespace `Breakdown.Coercive.Internal.WeakPieceMuReflect`.**

**The pressure budget for a mu mode** · definition. `pressDensity`: The pressure density combines the harmonic convolution square and the weighted velocity square through the positive splitting parameter. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMuReflect.lean#L263).

**The reflected-field budget** · definition. `reflDensity`: The reflected density replaces the harmonic convolution square by the reflected field's actual mode square in the same splitting budget. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMuReflect.lean#L269).

**The weak reflected-pairing estimate** · theorem. `reflected_pairing_bound_weak`: The reflected field's mu pairing is bounded below by the negative integrated harmonic pressure budget. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMuReflect.lean#L275).

### Breakdown.Cert.ExtendedCoercivePieceMuTransport

This file treats transport in the mu block by an explicit weak integration-by-parts argument. It proves the necessary local integrability, boundary cancellation and remainder estimate. §7.7: coercivity and the linearized inverse, with analytic support lemmas

**Source namespace `Breakdown.Coercive.Internal.WeakPieceMuTransport`.**

**Time derivatives multiply by frequency** · theorem. `time_mode`: The time derivative's velocity mode is the original mode multiplied by two pi times the temporal frequency and the imaginary unit. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMuTransport.lean#L25).

**The angular derivative mode formula** · theorem. `turn_mode`: The angular-turn field's mode combines the azimuthal frequency multiple with the axial coordinate turn. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMuTransport.lean#L30).

**Split the rotated transport field** · theorem. `rotated_decomp`: The rotated inner field splits into time derivative, similarity scaling, frame advection, frame turn and negative Laplacian terms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMuTransport.lean#L36).

**The temporal derivative is continuous** · theorem. `timeDerivField_continuous`: The perturbation's temporal derivative field is jointly continuous. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMuTransport.lean#L47).

**The perturbation gradient is continuous** · theorem. `gradSlice_continuous`: The spatial gradient of the perturbation is jointly continuous. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMuTransport.lean#L60).

**The negative Laplacian is continuous** · theorem. `negSumSecondPartialsField_continuous`: The sum of negative second spatial partials is jointly continuous. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMuTransport.lean#L65).

**Continuity of a rotated application** · theorem. `applied_integrand_continuous`: The rotated derivative applied to the orbit vector is continuous in the time-angle parameters. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMuTransport.lean#L74).

**Split the transport mode** · theorem. `mode_split_of`: The inner-field mode separates into its frame-frequency, axial-turn, half-scaling, frame-advection and negative-Laplacian contributions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMuTransport.lean#L86).

**A nonnegative piece-product bound** · theorem. `piece_sum_mul_le`: The nonnegative sum of the weighted mode product is at most the coefficient times the two piece norms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMuTransport.lean#L144).

**Convert a nonnegative mode sum** · theorem. `tsum_eq_toReal_ofReal`: The real sum of the nonnegative family equals the real value of its extended-nonnegative sum. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMuTransport.lean#L180).

**Measurability of a piece norm** · theorem. `aem_pieceNorm_of`: Measurable mode-amplitude families give an almost everywhere measurable piece norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMuTransport.lean#L185).

**Measurability of an edge sum** · theorem. `aem_edgeSum`: The finite harmonic edge sum is almost everywhere measurable when its coefficient and amplitude families are. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMuTransport.lean#L199).

**The moving-frame vector bound** · theorem. `frame_term_le`: The frame vector is bounded by the decay constant plus similarity and rotation speeds times the spatial radius. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMuTransport.lean#L223).

**Measurable moving-frame speed** · theorem. `frameSpeedSup_measurable`: The supremum of the moving-frame speed is spatially measurable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMuTransport.lean#L246).

**Continuous rotated derivative entries** · theorem. `clm_orbit_continuous`: A rotated linear-map coordinate varies continuously on the time-angle orbit. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMuTransport.lean#L272).

**Modes of a derivative-field product** · theorem. `clm_mode_product`: A finite harmonic expansion of the vector coefficient turns the product mode into the corresponding shifted gradient-mode convolution. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMuTransport.lean#L280).

**Source section `Bounds`.**

**The mu piece transport decomposition** · theorem. `mode_split`: At the mu piece's frame speed, the transport mode splits into frame frequency, turn, scaling, advection and negative Laplacian. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMuTransport.lean#L346).

**Integrable frame-frequency terms** · theorem. `freq_integrable`: Each frame-frequency mode contribution is integrable over the time-space slab. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMuTransport.lean#L353).

**Weighted frame advection lies in L²** · theorem. `frameAdvection_square`: Frame advection divided by one plus the radius belongs to the periodic square-integrable field class. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMuTransport.lean#L396).

**Integrable frame-advection pairings** · theorem. `frameAdvection_integrable`: Each weighted frame-advection mode pairing is integrable on the time slab. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMuTransport.lean#L475).

**Integrable axial-turn pairings** · theorem. `turn_integrable`: Each axial-turn mode pairing is integrable on the time slab. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMuTransport.lean#L551).

**Integrable advection contributions** · theorem. `advection_integrable`: The sum of the turn and frame-advection contributions is integrable for each mode. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMuTransport.lean#L616).

**Integrable Laplacian mode pairings** · theorem. `sumSecondPartials_integrable`: Each weighted negative-Laplacian mode pairing is integrable on the time slab. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMuTransport.lean#L621).

**The two remainder pieces are integrable** · theorem. `rest_integrable`: The advection remainder and the negative-Laplacian pairing are integrable for every mode. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMuTransport.lean#L688).

**All three pairing pieces are integrable** · theorem. `pairing_integrable`: The frequency, advection and negative-Laplacian contributions are each integrable for every mode. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMuTransport.lean#L694).

**A frequency series as an integral sum** · theorem. `freq_tsum_eq`: The integrated frame-frequency terms are summable and sum to the real value of the nonnegative frequency series. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMuTransport.lean#L701).

**A square bound for Laplacian pairings** · theorem. `sumSecondPartials_term_le`: A common constant bounds each Laplacian mode pairing by the sum of scaled-velocity and Laplacian mode squares. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMuTransport.lean#L736).

**The Laplacian pairing family is summable** · theorem. `sumSecondPartials_family_summable`: The time-space integrals of the negative-Laplacian mode terms form a summable family. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMuTransport.lean#L784).

**A square bound for advection pairings** · theorem. `advection_term_le`: A common nonnegative constant bounds each advection term by scaled velocity and scaled frame-advection mode squares. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMuTransport.lean#L806).

**Advection integrals sum absolutely** · theorem. `advection_norm_summable`: The spatial-time integrals of the absolute advection-mode terms form a summable family. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMuTransport.lean#L905).

**The advection pairing family is summable** · theorem. `advection_family_summable`: The integrated turn-plus-frame-advection terms are summable over all modes. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMuTransport.lean#L926).

**The complete mode pairing is summable** · theorem. `pairing_summable`: The frequency, advection and Laplacian integral families are summable, and the frequency family has the stated nonnegative-series value. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMuTransport.lean#L936).

**Split the integrated mu pairing** · theorem. `pairing_decomp`: The complete mu pairing is the frequency gain plus the summed advection and negative-Laplacian integral contributions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMuTransport.lean#L943).

**Summable velocity energy in a piece** · theorem. `piece_vel_summable`: The velocity-mode squares restricted to the mu piece are summable almost everywhere on the time slab. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMuTransport.lean#L980).

**Gradient and velocity amplitudes sum** · theorem. `amp_summable`: The gradient and velocity squared-amplitude families are summable over modes at the indicated point. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMuTransport.lean#L1010).

**Separate interior and edge modes** · theorem. `frameAdvection_mode_split`: A frame-advection mode splits into its within-piece part and its boundary-crossing harmonic part. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMuTransport.lean#L1036).

**The exterior mode has an edge bound** · theorem. `outerMode_le`: The norm of the boundary-crossing frame-advection mode is bounded by the harmonic edge sum. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMuTransport.lean#L1066).

**The velocity-edge products are summable** · theorem. `edge_summable`: Products of velocity amplitudes with the frame-advection edge sums form a summable mode family. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMuTransport.lean#L1104).

**Bound the orbit-frame speed square** · theorem. `orbitFrame_sq_le`: The sum of squared orbit-frame coordinates is bounded by the squared frame-speed supremum. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMuTransport.lean#L1147).

**A finite compression-energy bound** · theorem. `inner_finset_bound`: For frequency sets satisfying the sign and piece-closure hypotheses, the compressed modal energy is at most frame-speed squared times the enclosed gradient-mode energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMuTransport.lean#L1198).

**Bound the compressed interior pairing** · theorem. `innerMode_piece_bound`: The interior velocity-mode product is summable and bounded by frame speed times the gradient and velocity piece norms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMuTransport.lean#L1247).

**A full frame-advection piece bound** · theorem. `frame_piece_bound`: The full frame-advection pairing is summable and bounded by the interior piece product plus the edge-mode sum almost everywhere. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMuTransport.lean#L1355).

**A pointwise lower advection bound** · theorem. `advection_pointwise`: The summed advection contributions are bounded below almost everywhere by the negative advection-loss expression. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMuTransport.lean#L1411).

**Exchange the advection sum and integral** · theorem. `advection_swap`: The summed advection contribution is integrable, and its integral equals the sum of its mode integrals. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMuTransport.lean#L1452).

**Integrate the advection loss** · theorem. `advection_loss_le`: The advection loss is integrable and its integral is bounded by the edge, turn and frame-advection block budgets. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMuTransport.lean#L1475).

**The integrated advection lower bound** · theorem. `advection_bound`: The sum of integrated advection contributions is bounded below by the negative total edge and block budgets. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMuTransport.lean#L1559).

**Measurable Laplacian slice integrals** · theorem. `sumSecondPartials_term_measurable`: The spatial integral of a Laplacian mode term is almost everywhere strongly measurable in time. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMuTransport.lean#L1577).

**The weight-gradient error is integrable** · theorem. `sumSecondPartials_weight_integrable`: The weight-gradient times gradient-amplitude and velocity-amplitude product is integrable on the time slab. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMuTransport.lean#L1594).

**A lower bound for one Laplacian mode** · theorem. `sumSecondPartials_mode_le`: Each integrated Laplacian mode contribution is bounded below by its negative weight-gradient error integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMuTransport.lean#L1643).

**Sum the weight-gradient losses** · theorem. `sumSecondPartials_series_le`: The integrated weight-gradient error family is summable and bounded by the Laplacian block budget. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMuTransport.lean#L1706).

**The integrated Laplacian lower bound** · theorem. `sumSecondPartials_bound`: The total integrated Laplacian contribution is bounded below by the negative Laplacian block budget. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMuTransport.lean#L1792).

**The integrated mu transport bound** · theorem. `Breakdown.Cert.ExtendedCoercivePieceMuTransport.transport_bound`: The integrated frequency gain minus edge and block losses is a lower bound for the transport part of the mu pairing. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoercivePieceMuTransport.lean#L1806).

### Breakdown.Cert.ExtendedCoerciveSecondDerivSymm

Weak Hessians must have the symmetry expected of second derivatives. This file proves almost-everywhere symmetry and the resulting derivative interchange identities. §7.7: coercivity and the linearized inverse, with analytic support lemmas

**Source namespace `Breakdown.CoerciveWeak.Internal.SecondDerivSymm`.**

**Local integrability of derivatives** · theorem. `locallyIntegrable_apply`: Evaluating the locally integrable derivative field on a fixed vector preserves local integrability. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveSecondDerivSymm.lean#L14).

**Integrate a vector derivative by parts** · theorem. `integral_smul_fderiv_of_test`: Pairing the derivative with a scalar test equals the negative pairing of the field with the test derivative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveSecondDerivSymm.lean#L21).

**Evaluate an iterated derivative** · theorem. `fderiv_fderiv_apply`: Differentiating a derivative evaluated at a fixed direction gives the second derivative applied to the two directions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveSecondDerivSymm.lean#L37).

**Exchange two test derivatives** · theorem. `pairing_eq`: The test-gradient pairing with a field derivative equals the negative pairing of the field with the corresponding test Hessian. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveSecondDerivSymm.lean#L44).

**Basis symmetry gives full symmetry** · theorem. `bilinear_symm_of_basis`: A bilinear map symmetric on every pair of basis vectors is symmetric on arbitrary vectors. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveSecondDerivSymm.lean#L56).

**Source namespace `Breakdown.CoerciveWeak`.**

**Prove symmetry of the weak Hessian** · theorem. `weakSecondDerivSymmetricHolds_proof`: Integration by parts and coordinate extensionality prove the weak-Hessian symmetry interface. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveSecondDerivSymm.lean#L72).

### Breakdown.Cert.ExtendedCoerciveStatement

This file states the weak coefficient and coercivity properties used by the extended certificate route. The interfaces specify regularity, decay, symmetry and the quantitative conclusion without selecting numerical certificate data. §7.7: coercivity and the linearized inverse, with analytic support lemmas

**Source namespace `Breakdown.CoerciveWeak`.**

**The weak-coefficient energy identity** · interface proposition. `EnergyIdentitySmoothWeakHolds`: This interface requires the period-integrated right-side pairing to equal vorticity energy and stretching for smooth perturbations of a weak-Hessian coefficient. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveStatement.lean#L16).

Proved by `Breakdown.CoerciveWeak.energyIdentitySmoothWeak_of_symmetric`.

**The weak piece pairing decomposition** · interface proposition. `PiecePairingSplitSmoothWeakHolds`: This interface splits the multiplier pairing into the Laplacian term and the finite epsilon and mu pairings under weak coefficient regularity. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveStatement.lean#L23).

Proved by `Breakdown.CoerciveWeak.piecePairingSplitSmoothWeakHolds_of`.

**The weak epsilon-piece lower bound** · interface proposition. `PieceEpsEstimateSmoothWeakHolds`: This interface requires the epsilon pairing to control its positive mode density after the weak remainder and block corrections. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveStatement.lean#L37).

Proved by `Breakdown.CoerciveWeak.pieceEpsEstimateSmoothWeakHolds_of`.

**The weak mu-piece lower bound** · interface proposition. `PieceMuEstimateSmoothWeakHolds`: This interface requires the mu pairing, adjusted by its seminorm, to control the positive mu density with its remainder and block terms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveStatement.lean#L50).

Proved by `Breakdown.CoerciveWeak.pieceMuEstimateSmoothWeakHolds_of`.

**A weak density bound for smooth inputs** · interface proposition. `PieceDensitySmoothWeakHolds`: This interface assembles the base, epsilon, mu and stretching estimates into a split bound for the smooth perturbation's multiplier gap. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveStatement.lean#L64).

Proved by `Breakdown.CoerciveWeak.pieceDensitySmoothWeakHolds_of`.

**Source section `Extended`.**

**Supply the extended coercive clause** · theorem. `isExtendedCertificate_of_clause`: Adding the proved coercive clause to the remaining certificate data establishes the extended certificate predicate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveStatement.lean#L85).

### Breakdown.Cert.ExtendedCoerciveVortGradMap

Vorticity-gradient quantities are packaged as finite-dimensional maps. Their continuity and norm bounds support the measurable-envelope and stretching estimates. §7.7: coercivity and the linearized inverse, with analytic support lemmas

**Source namespace `Breakdown.CoerciveWeak.Internal.VortGradMap`.**

**Curl as a linear map** · definition. `curlLinear`: The matrix-to-curl-vector operation is packaged as a real linear map. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveVortGradMap.lean#L13).

**Curl as a continuous linear map** · definition. `curlCLM`: Finite-dimensional continuity turns the linear curl map into a continuous linear map. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveVortGradMap.lean#L26).

**Evaluate the continuous curl map** · theorem. `curlCLM_apply`: The continuous linear curl map evaluates to the original curl-vector formula. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveVortGradMap.lean#L28).

**A unit vector's coordinates** · theorem. `unitVector_apply`: The coordinate of a unit vector is one at its own index and zero at all others. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveVortGradMap.lean#L30).

**Apply a map by its basis values** · theorem. `apply_eq_sum`: A linear map evaluated at a vector is the coordinate-weighted sum of its basis values. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveVortGradMap.lean#L33).

**Vorticity gradients as curl of a slice** · theorem. `vortGradMap_apply`: Applying the vorticity-gradient map to a direction equals taking the curl of the corresponding Hessian slice. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveVortGradMap.lean#L38).

**Source namespace `Breakdown.CoerciveWeak`.**

**Prove the vorticity derivative identity** · theorem. `vortGradMapSecondDerivFieldHolds_proof`: The continuous linear curl map proves that the actual Hessian differentiates the vorticity field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveVortGradMap.lean#L51).

### Breakdown.Cert.ExtendedCoerciveZeroFlow

Zero-velocity cases must satisfy the same weak-state interfaces as the general construction. This file proves the corresponding vanishing and admissibility statements. §7.7: coercivity and the linearized inverse, with analytic support lemmas

**Source namespace `Breakdown.CoerciveWeak.Internal.ZeroFlow`.**

**Rotation fixes the zero vector** · theorem. `axialRot_zero'`: Every axial rotation sends zero to zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveZeroFlow.lean#L16).

**The zero field has zero velocity modes** · theorem. `modeVel_zero`: Every velocity mode of the zero field is zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveZeroFlow.lean#L19).

**The zero field has zero gradient** · theorem. `gradField_zero`: The spatial gradient field of zero is zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveZeroFlow.lean#L23).

**The zero field has zero Hessian** · theorem. `secondDerivField_zero`: The second spatial derivative field of zero is zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveZeroFlow.lean#L26).

**The zero gradient has zero modes** · theorem. `modeGrad_zero`: Every gradient mode of the zero matrix field is zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveZeroFlow.lean#L29).

**The zero Hessian has zero modes** · theorem. `modeSecondDeriv_zero`: Every second-derivative mode of the zero bilinear field is zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveZeroFlow.lean#L33).

**The zero vector has zero square norm** · theorem. `cnormSq_zero'`: The complex squared norm of zero is zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveZeroFlow.lean#L37).

**Zero gradient modes have zero curl** · theorem. `curlOfGrad_zero`: The mode-curl combination of the zero gradient array is zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveZeroFlow.lean#L40).

**Zero Hessian modes give zero curl slopes** · theorem. `curlGradOfSecondDeriv_zero`: The curl-gradient combination of the zero Hessian array is zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveZeroFlow.lean#L43).

**The zero matrix has zero curl** · theorem. `curlVec_zero'`: The curl vector of the zero matrix is zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveZeroFlow.lean#L46).

**The zero-flow frame speed** · theorem. `speed_bound`: For the zero coefficient flow, the frame-vector norm is bounded by one half plus the frame-speed magnitude times radius. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveZeroFlow.lean#L49).

**Source namespace `Breakdown.CoerciveWeak`.**

**Prove zero-flow admissibility** · theorem. `zeroFlowAdmissibleHolds_proof`: The zero-field identities and frame-speed estimate prove the zero-flow admissibility interface. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveZeroFlow.lean#L81).

### Breakdown.Cert.ExtendedConvection

The extended route weakens the profile regularity needed for convection. This file constructs the bounded convection operator using first-order coefficient hypotheses. §§7.6–7.7: profile terms and the linearized operator

**First-order decaying coefficients** · structure. `IsFirstOrderCoefficient`: The first-order coefficient predicate requires joint continuous differentiability, time periodicity and velocity-gradient decay bounds. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedConvection.lean#L17).

**The extended profile is first-order data** · theorem. `isFirstOrderCoefficient_profile`: The extended certificate's approximate profile satisfies the first-order convection coefficient conditions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedConvection.lean#L23).

**Measurability of convection** · theorem. `Breakdown.Cert.ExtendedConvection.aesm_readingConvection`: The physical convection field is jointly almost everywhere strongly measurable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedConvection.lean#L29).

**The decay bound is nonnegative** · theorem. `Breakdown.Cert.ExtendedConvection.coefficient_nonneg`: The coefficient hypotheses force the decay constant to be nonnegative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedConvection.lean#L39).

**Differentiability of spatial slices** · theorem. `Breakdown.Cert.ExtendedConvection.slice_contDiff`: Joint differentiability implies the corresponding differentiability of each fixed-time spatial slice. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedConvection.lean#L45).

**The convection slice bound** · theorem. `Breakdown.Cert.ExtendedConvection.slice_bound`: The convection slice belongs to L² with norm bounded by the slice constant times the perturbation energy norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedConvection.lean#L119).

**A nonnegative slice bound** · theorem. `Breakdown.Cert.ExtendedConvection.sliceConst_nonneg`: The convection slice constant is nonnegative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedConvection.lean#L153).

**An integrated slice bound** · theorem. `Breakdown.Cert.ExtendedConvection.lintegral_slice_le`: The nonnegative square integral of a slice is bounded by the squared slice constant times its squared energy norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedConvection.lean#L160).

**A period convection bound** · theorem. `Breakdown.Cert.ExtendedConvection.periodLIntegral_le`: The physical convection field's periodic square integral is bounded by the squared slice constant times the squared gradient-curve norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedConvection.lean#L176).

**Convection is periodic** · theorem. `Breakdown.Cert.ExtendedConvection.periodic_readingConvection`: The physical convection field is periodic in time. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedConvection.lean#L202).

**A bounded convection curve exists** · theorem. `Breakdown.Cert.ExtendedConvection.exists_sliceCurve`: The convection slices admit an L²-valued time-circle representative with the slice-constant norm bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedConvection.lean#L209).

**The convection curve is a linear map** · theorem. `Breakdown.Cert.ExtendedConvection.exists_sliceCurveCLM`: The convection representatives assemble into a continuous linear map with a bound through the gradient-curve norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedConvection.lean#L233).

**Convert physical convection to HH** · theorem. `Breakdown.Cert.ExtendedConvection.physToHH_eq_convection`: The conversion of the physical convection field to the time-circle Hilbert space equals the abstract convection operator applied to the perturbation. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedConvection.lean#L248).

### Breakdown.Cert.ExtendedConvectionCompact

The compactness argument is adapted to first-order coefficient data here. Local control and spatial tails again make convection compact after the free inverse. §§7.6–7.7: profile terms and the linearized operator

**Separate exterior derivative decay** · theorem. `fderiv_tail_le_first`: Outside a ball, the profile derivative is bounded by a radius-decay factor times the integrable radial tail weight. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedConvectionCompact.lean#L18).

**An exterior L² derivative bound** · theorem. `eLpNorm_fderiv_tail_first`: The profile derivative acting on velocity has an exterior L² bound with inverse-square-root radius decay. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedConvectionCompact.lean#L39).

**The exterior derivative square bound** · theorem. `second_tail_first`: The exterior square integral of the profile-gradient term decays like the inverse of one plus the radius. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedConvectionCompact.lean#L81).

**Pointwise exterior convection control** · theorem. `tail_pointwise_first`: Outside the chosen ball, the convection square is bounded by weighted gradient-column squares and the profile-gradient contribution. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedConvectionCompact.lean#L116).

**Pointwise interior convection control** · theorem. `ball_pointwise_first`: The convection square is bounded by the decay constant squared times the local velocity and gradient-column squares. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedConvectionCompact.lean#L184).

**An interior convection estimate** · theorem. `slice_ball_first`: The convection square integral on a ball is bounded by the local velocity and gradient-column square integrals. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedConvectionCompact.lean#L207).

**Separate interior and exterior energy** · theorem. `slice_split_first`: The full convection square integral splits into a local velocity-gradient bound and a radius-decaying energy remainder. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedConvectionCompact.lean#L235).

**Convection difference as slice energy** · theorem. `conv_le_first`: The squared norm of a convection difference is bounded by the periodic square integral of the corresponding slice difference. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedConvectionCompact.lean#L248).

**Local and tail convection control** · theorem. `core_bound_first`: A convection difference is bounded by local velocity-gradient norms plus a radius-decaying multiple of the gradient-curve difference. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedConvectionCompact.lean#L276).

**Make the convection tail small** · theorem. `local_tail_bound_first`: For every positive tolerance, a radius and local constant bound convection differences by local physical norms plus a small gradient remainder. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedConvectionCompact.lean#L336).

**A compact inverse-image subsequence** · theorem. `fundamental_image_general`: Under the local compactness and tail hypotheses, the operator applied to free inverses of bounded forcing has a Cauchy image subsequence. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedConvectionCompact.lean#L355).

### Breakdown.Cert.ExtendedConvectionContinuity

The extended profile family has weaker regularity than the smooth route. These estimates still give operator-norm continuity of convection on its admissible parameter set. §§7.6–7.7: profile terms and the linearized operator

**Source namespace `Breakdown.Cert.Internal.ExtendedConvectionContinuity`.**

**Conversion preserves the profile** · theorem. `profile_eq`: The conversion to the earlier certificate carrier keeps the same approximate profile. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedConvectionContinuity.lean#L17).

**The decay bound is nonnegative** · theorem. `Breakdown.Cert.ExtendedConvectionContinuity.decay_nonneg`: The stated field bounds force the common decay constant to be nonnegative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedConvectionContinuity.lean#L20).

**Differentiability of spatial slices** · theorem. `Breakdown.Cert.ExtendedConvectionContinuity.slice_contDiff`: Joint differentiability implies the corresponding differentiability of each fixed-time spatial slice. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedConvectionContinuity.lean#L26).

**Compare the two radial decay weights** · theorem. `square_le_tailWeight`: Inverse-square decay is bounded by the inverse-three-halves tail weight times the nonnegative decay constant. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedConvectionContinuity.lean#L30).

**The first-order gradient-term bound** · theorem. `second_part_first_order`: The once differentiable coefficient's derivative acting on velocity satisfies the weighted L² estimate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedConvectionContinuity.lean#L39).

**A first-order convection bound** · theorem. `slice_bound_first_order`: The first-order velocity and derivative bounds give the full convection slice's L² estimate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedConvectionContinuity.lean#L79).

**Extended convection slices lie in L²** · theorem. `slice_memLp`: At an admissible parameter, the extended-profile convection slice is spatially square-integrable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedConvectionContinuity.lean#L113).

**The selected convection specification** · theorem. `Breakdown.Cert.ExtendedConvectionContinuity.convection_spec`: Assuming convection existence, valid certificate data and an admissible parameter, the selected convection operator satisfies the physical slice specification. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedConvectionContinuity.lean#L122).

**Bound a change in convection** · theorem. `Breakdown.Cert.ExtendedConvectionContinuity.norm_sub_apply_le`: The difference between two parameterized convection operators applied to one perturbation is bounded by their coefficient differences. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedConvectionContinuity.lean#L131).

**Continuous profile and derivative data** · theorem. `Breakdown.Cert.ExtendedConvectionContinuity.joint_continuous`: The profile and its spatial derivative depend jointly continuously on the certificate parameter, time and position. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedConvectionContinuity.lean#L170).

**Nearby parameters give close profiles** · theorem. `Breakdown.Cert.ExtendedConvectionContinuity.eventually_close`: Parameters sufficiently near the base parameter give uniform profile closeness and weighted derivative closeness on the parameter box. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedConvectionContinuity.lean#L181).

**A convection operator-norm bound** · theorem. `Breakdown.Cert.ExtendedConvectionContinuity.op_bound`: Coefficient closeness controls the operator norm of the difference between the corresponding convection maps. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedConvectionContinuity.lean#L245).

**Convection varies locally continuously** · theorem. `Breakdown.Cert.ExtendedConvectionContinuity.convection_close`: Every positive tolerance admits a parameter neighborhood where the convection operators are within that tolerance in operator norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedConvectionContinuity.lean#L269).

**Source namespace `Breakdown.Cert`.**

**Prove extended convection continuity** · theorem. `extendedConvectionContinuityHolds_of`: The first-order coefficient comparison proves continuity of the extended convection operator on the parameter set. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedConvectionContinuity.lean#L285).

### Breakdown.Cert.ExtendedData

Weak Hessian data must be converted into the same abstract defect, actuator and pinning objects. This file proves the physical interpretations and norm estimates for that conversion. §7: certificate data and the similarity-profile construction

**Source namespace `Breakdown.Cert.Internal.ExtendedData`.**

**The Hessian trace is continuous** · theorem. `Breakdown.Cert.ExtendedData.continuous_secondDerivTrace`: Taking the sum of the three diagonal Hessian evaluations is a continuous operation. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedData.lean#L17).

**Continuous first-order defect terms** · theorem. `continuous_weak_part`: The time, similarity and advection parts of the weak defect are jointly continuous. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedData.lean#L22).

**The weak defect is measurable** · theorem. `aestronglyMeasurable_weakDefect`: The weak defect including the supplied Hessian, pressure gradient and actuator fields is almost everywhere strongly measurable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedData.lean#L39).

**The weak defect is time periodic** · theorem. `weakDefect_periodic`: The weak defect inherits time periodicity from its coefficient and forcing data. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedData.lean#L54).

**The residual is an admissible field** · theorem. `Breakdown.Cert.ExtendedData.defect_field`: The certificate's defect field satisfies the periodic-field conditions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedData.lean#L71).

**The residual obeys its bound** · theorem. `Breakdown.Cert.ExtendedData.defect_norm`: The norm of the abstract defect is at most the certificate's defect bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedData.lean#L81).

**Finite actuator energy** · theorem. `Breakdown.Cert.ExtendedData.actuator_fin`: Each actuator field has finite nonnegative periodic square integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedData.lean#L90).

**Admissible actuator fields** · theorem. `Breakdown.Cert.ExtendedData.actuator_field`: Each actuator field satisfies the periodic-field conditions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedData.lean#L95).

**Measurability of folded pins** · theorem. `Breakdown.Cert.ExtendedData.pin_fold_meas`: The pin field evaluated at the chosen time representative is jointly almost everywhere strongly measurable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedData.lean#L99).

**Folding preserves pin energy** · theorem. `Breakdown.Cert.ExtendedData.pin_fold_period`: Folding the time variable preserves the pin field's periodic matrix square integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedData.lean#L104).

**Finite folded pin-column energy** · theorem. `Breakdown.Cert.ExtendedData.pin_fold_fin`: Each folded pin column has finite periodic square integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedData.lean#L112).

**L² curves representing pin columns** · theorem. `Breakdown.Cert.ExtendedData.exists_pin_curve`: Each pin column has a time-circle L²-valued representative agreeing with the folded physical column almost everywhere. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedData.lean#L122).

**A pin map exists** · theorem. `Breakdown.Cert.ExtendedData.exists_pinSpec`: For admissible certificate data, a continuous linear map satisfying the physical pin specification exists. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedData.lean#L133).

**The abstract pin is the physical pin** · theorem. `Breakdown.Cert.ExtendedData.pinMap_eq`: Evaluating the abstract pin map on a curve equals the pin value of its physical gradient reading. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedData.lean#L138).

**The physical actuator pairing** · theorem. `Breakdown.Cert.ExtendedData.actuator_pairing`: Pairing the abstract actuator against a test equals the integral pairing of the physical actuator sum against that test. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedData.lean#L162).

**Bound the actuator map** · theorem. `Breakdown.Cert.ExtendedData.actuator_norm_le`: The actuator norm is at most the certificate's actuator bound times the Euclidean coefficient norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedData.lean#L188).

**Source namespace `Breakdown.Cert`.**

**Construct the extended physical data** · theorem. `extendedDataHolds_of`: The weak defect, actuator and pin constructions establish the extended data interface. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedData.lean#L218).

### Breakdown.Cert.ExtendedDataContinuity

The weak defect representation includes Hessian-trace terms. This file uses tested integration by parts and dominated bounds to prove continuity of the defect and pinning pairings. §7: certificate data and the similarity-profile construction

**A derivative in the spatial direction** · theorem. `Breakdown.Cert.ExtendedDataContinuity.slice_fderiv_apply`: Applying a slice derivative equals applying the joint derivative to a vector with zero time component. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedDataContinuity.lean#L13).

**Bound a Hessian trace** · theorem. `Breakdown.Cert.ExtendedDataContinuity.norm_trace_le`: The norm of the Hessian trace is at most three times the Hessian operator norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedDataContinuity.lean#L21).

**Continuity of the Hessian trace map** · theorem. `continuous_trace`: The trace operation on bilinear second-derivative maps is continuous. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedDataContinuity.lean#L32).

**The Euclidean inner product formula** · theorem. `inner_eq_sum`: The real Euclidean inner product equals the sum of the coordinate products. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedDataContinuity.lean#L38).

**A compact time-space test support** · theorem. `testField_isCompact`: The joint time-space test field has compact topological support. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedDataContinuity.lean#L41).

**A spatial derivative of a joint test** · theorem. `testField_partial`: The spatial derivative of a test slice is its joint derivative applied to a direction with zero time component. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedDataContinuity.lean#L45).

**The first-order defect expression** · definition. `firstOrderPart`: The first-order part combines time derivative, similarity drift and self-advection before the Hessian, pressure and actuator terms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedDataContinuity.lean#L53).

**A tested gradient-energy term** · definition. `gradientPairing`: The gradient pairing is the sum of inner products between the three profile-gradient and test-gradient columns. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedDataContinuity.lean#L57).

**Continuity of profile gradients** · theorem. `continuous_profile_fderiv`: The approximate profile's gradient is jointly continuous in parameter, time and position. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedDataContinuity.lean#L62).

**Continuity of profile time derivatives** · theorem. `continuous_profile_timeDeriv`: The profile's time derivative is jointly continuous in parameter, time and position. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedDataContinuity.lean#L70).

**Continuous first-order defects** · theorem. `continuousOn_firstOrderPart`: The first-order defect part varies continuously across the parameter set and time-space. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedDataContinuity.lean#L79).

**Continuous tested gradient data** · theorem. `continuous_gradientPairing`: The gradient pairing with a fixed test is jointly continuous in parameter and time-space. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedDataContinuity.lean#L103).

**The gradient pairing has compact support** · theorem. `gradientPairing_eq_zero`: Outside the test's support, the profile-test gradient pairing is zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedDataContinuity.lean#L119).

**The gradient pairing is integrable** · theorem. `integrable_gradientPairing`: The tested profile-gradient pairing is integrable over time-space. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedDataContinuity.lean#L129).

**Continuous integrated gradient pairings** · theorem. `continuousOn_gradientPairing_integral`: The integral of the profile-test gradient pairing varies continuously over the parameter set. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedDataContinuity.lean#L138).

**The weak Hessian pairing is integrable** · theorem. `integrable_secondOrder_pairing`: The trace of the supplied weak profile Hessian has an integrable pairing with the test field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedDataContinuity.lean#L145).

**Weak Hessian integration by parts** · theorem. `slice_identity`: On each time slice, the Hessian-trace test integral is the negative of the gradient-pairing integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedDataContinuity.lean#L171).

**The integrated Hessian identity** · theorem. `secondOrder_integral`: The time-space Hessian-trace pairing equals the negative integrated gradient pairing. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedDataContinuity.lean#L247).

**First-order pairings are integrable** · theorem. `integrable_firstOrder_pairing`: The first-order defect paired with a fixed test is integrable over time-space. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedDataContinuity.lean#L257).

**Periodic actuator regularity** · theorem. `Breakdown.Cert.ExtendedDataContinuity.actuator_periodicField`: Each actuator satisfies the periodic-field conditions needed for physical pairings. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedDataContinuity.lean#L268).

**Expand the weak defect pairing** · theorem. `defect_inner_eq`: Pointwise pairing of the weak defect separates into first-order, Hessian-trace, actuator and pressure-gradient pairings. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedDataContinuity.lean#L274).

**The tested weak defect formula** · theorem. `defect_pairing_eq`: After integration by parts and pressure cancellation, the weak defect pairing is the first-order pairing plus the gradient pairing and actuator pairings. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedDataContinuity.lean#L288).

**Continuity of the tested defect** · theorem. `Breakdown.Cert.ExtendedDataContinuity.continuousOn_defect`: For certificate data satisfying the stated hypotheses, the abstract defect's pairing with a fixed test is continuous on the admissible parameter set. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedDataContinuity.lean#L320).

**Nonnegative column energy** · theorem. `columnSq_nonneg`: The sum of squared column norms of a matrix is nonnegative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedDataContinuity.lean#L341).

**Bound a columnwise inner product** · theorem. `columnInner_bound`: The absolute matrix pairing is bounded by half of three times the first operator norm squared plus the second column energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedDataContinuity.lean#L344).

**Square the profile-gradient decay** · theorem. `Breakdown.Cert.ExtendedDataContinuity.sq_fderiv_le`: The squared profile-derivative norm is bounded by the squared decay constant times inverse fourth-power radial decay. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedDataContinuity.lean#L360).

**The measure on the unit-time strip** · theorem. `Breakdown.Cert.ExtendedDataContinuity.restrict_eq`: The product of restricted time volume and spatial volume equals full time-space volume restricted to the unit-time strip. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedDataContinuity.lean#L375).

**Continuity of profile pin values** · theorem. `Breakdown.Cert.ExtendedDataContinuity.continuousOn_pinValue`: Pairing a fixed pin with the profile gradient varies continuously over the parameter box. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedDataContinuity.lean#L379).

### Breakdown.Cert.ExtendedExistsZeroHeld

The extended construction ends by finding a zero of the held multiplier. This file applies the finite-box zero argument to the continuous multiplier and the supplied face bounds. §7.8: fixed-parameter contraction and the parameter zero

**A transposed product in coordinates** · theorem. `transpose_mulVec_apply`: A coordinate of the transposed matrix-vector product is the corresponding column pairing. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedExistsZeroHeld.lean#L12).

**A combined coordinate-square bound** · theorem. `sum_sq_add_le`: If the Euclidean lengths of two finite coordinate families sum to at most a radius, their coordinatewise sum has squared length at most that radius squared. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedExistsZeroHeld.lean#L16).

**Separate the box-coordinate errors** · theorem. `box_split`: If the original multiplier error and held-correction error bounds sum to at most R, the adjusted multiplier lies within R of its target. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedExistsZeroHeld.lean#L36).

**Separate a stiff-coordinate correction** · theorem. `stiff_split`: The transformed total-multiplier error is the original transformed error plus the transformed held correction. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedExistsZeroHeld.lean#L46).

**The selected total multiplier** · theorem. `Breakdown.Cert.ExtendedExistsZeroHeld.multiplierOf_eq`: The total multiplier is the approximate multiplier plus the multiplier selected with the held correction. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedExistsZeroHeld.lean#L51).

**A held solution exists at each parameter** · theorem. `exists_held`: For the admissible parameter, there is a held forcing and multiplier pair satisfying the held-solution predicate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedExistsZeroHeld.lean#L58).

**The total stiff-coordinate error** · theorem. `stiff_term`: The frame-transformed total multiplier minus the scaled parameter equals the original error plus the selected correction's frame coordinate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedExistsZeroHeld.lean#L77).

### Breakdown.Cert.ExtendedFrozenBridge

The spatial frozen-profile estimate is transferred to graph-space slices with weak readings. This bridge lets physical coefficient bounds control the extended linearized operator. §7.7: coercivity and the linearized inverse, with analytic support lemmas

**A continuous convection field lies in L²** · theorem. `memLp_sliceConvection_of_continuous`: The stated continuous coefficient and derivative bounds make slice convection square-integrable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedFrozenBridge.lean#L15).

**Nonnegative stationary energy** · theorem. `Breakdown.Cert.ExtendedFrozenBridge.stationaryEnergy_nonneg`: The admissible weight makes the stationary energy built from the first and second spatial derivatives nonnegative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedFrozenBridge.lean#L67).

**A lower frozen-form bound at the profile** · theorem. `profile_form`: The profile's frozen quadratic form is bounded below by minus the form constant times stationary weighted energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedFrozenBridge.lean#L74).

**The frozen bound on a graph slice** · theorem. `Breakdown.Cert.ExtendedFrozenBridge.slice_bridge`: Under the reading and symmetry hypotheses, the frozen spatial estimate bounds the graph-slice energy below by minus the form constant times its weighted energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedFrozenBridge.lean#L86).

### Breakdown.Cert.ExtendedHeldContracts

For each fixed parameter, the nonlinear held map must contract. This file derives its contraction constant from the certificate's smallness inequalities and normalized transfer loss. §7.8: fixed-parameter contraction and the parameter zero

**Subtract the nonlinear held forcing** · theorem. `heldRight_sub_fst`: The difference of the two held right sides is the negative difference of the quadratic perturbation products. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedHeldContracts.lean#L15).

**The bordered difference equation** · theorem. `sub_fst_eq`: The first bordered component of the held-solution difference equals the negative bilinear expansion of the quadratic difference. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedHeldContracts.lean#L20).

**Normalization gives zero transfer loss** · theorem. `Breakdown.Cert.ExtendedHeldContracts.transferLoss_eq_zero`: The model-at-profile normalization makes the transfer-loss term zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedHeldContracts.lean#L50).

**Combine the coercive and row constants** · theorem. `coerciveSum_le`: The L² coercive constant plus the row bound is at most the total coercive constant. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedHeldContracts.lean#L54).

**A nonnegative frozen-form bound** · theorem. `formBound_nonneg`: The certificate conditions make the frozen-form bound nonnegative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedHeldContracts.lean#L59).

**Use the maximal period in the bound** · theorem. `ratio_bound`: Replacing the parameter period by its maximum enlarges the combined energy, actuator and coercive expression. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedHeldContracts.lean#L83).

**Smallness gives a supremum bound** · theorem. `small_second_unit`: The normalized certificate smallness condition controls the quadratic energy expression by the squared supremum bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedHeldContracts.lean#L97).

**The held step is contractive** · theorem. `contract_core`: The distance between two held-step images is at most the stated contraction factor times the original held distance. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedHeldContracts.lean#L130).

### Breakdown.Cert.ExtendedHeldExistsUnique

The fixed-parameter contraction yields a unique held solution. This file packages that existence and uniqueness for use by the later continuous parameter argument. §7.8: fixed-parameter contraction and the parameter zero

**The forcing part of the held right side** · theorem. `heldRight_fst`: The held right side's forcing component is minus the defect minus the quadratic perturbation term. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedHeldExistsUnique.lean#L17).

**The pin part of the held right side** · theorem. `heldRight_snd`: The second component of the held right side is the target pin gap. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedHeldExistsUnique.lean#L20).

**The correction part of the held step** · theorem. `heldStep_fst`: The held step's field component is the free inverse of the first bordered-inverse component. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedHeldExistsUnique.lean#L23).

**The multiplier part of the held step** · theorem. `heldStep_snd`: The held step's multiplier component is the second component of the bordered inverse. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedHeldExistsUnique.lean#L28).

**The complete held iteration formula** · theorem. `heldStep_mk`: The held step pairs the free inverse of the bordered forcing output with its multiplier output. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedHeldExistsUnique.lean#L32).

**The held forcing respects the symmetries** · theorem. `heldRight_mem`: The nonlinear held right side belongs to the invariant forcing subspace. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedHeldExistsUnique.lean#L38).

**The bordered inverse solves the equation** · theorem. `borderedInv_apply`: The bordered inverse returns invariant forcing and its bordered image is the supplied right side. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedHeldExistsUnique.lean#L45).

**A held solution is a fixed point** · theorem. `fixed_of_solution`: A held solution gives a fixed point of the held step after applying the free inverse to its forcing. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedHeldExistsUnique.lean#L52).

**Held solutions solve the bordered system** · theorem. `bordered_of_solution`: The forcing and multiplier of a held solution solve the bordered equation with its nonlinear held right side. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedHeldExistsUnique.lean#L59).

**The held set contains zero** · theorem. `zero_mem_heldSet`: The zero correction and zero multiplier belong to the held set. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedHeldExistsUnique.lean#L75).

**Component equations give held solutions** · theorem. `solution_of_eqs`: The bordered component identities and held bounds imply the held-solution predicate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedHeldExistsUnique.lean#L90).

**A fixed point gives a held solution** · theorem. `solution_of_fixed`: A fixed point of the held step yields the corresponding held forcing and multiplier solution. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedHeldExistsUnique.lean#L105).

**The inverse recovers held solutions** · theorem. `inv_of_solution`: A held solution lies in the held set and is recovered exactly by applying the bordered inverse to its held right side. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedHeldExistsUnique.lean#L118).

### Breakdown.Cert.ExtendedHeldMapsTo

The nonlinear map must preserve the closed ball on which contraction is used. This file proves the ball bound from the certificate estimates. §7.8: fixed-parameter contraction and the parameter zero

**The row estimate controls held size** · theorem. `size_arith_rows`: The scalar coercive and row estimates bound the combined held-state size by twice the chosen radius. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedHeldMapsTo.lean#L17).

**Negation preserves periodic-field data** · theorem. `neg_periodic`: The negative of an admissible periodic field is again an admissible periodic field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedHeldMapsTo.lean#L29).

**Bound the negative residual row norm** · theorem. `rows_neg_sub_le`: The row norm of minus defect minus quadratic forcing is bounded by the defect rows plus the row constant times the quadratic period norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedHeldMapsTo.lean#L35).

**Normalization gives zero transfer loss** · theorem. `Breakdown.Cert.ExtendedHeldMapsTo.transferLoss_eq_zero`: The model-at-profile normalization makes the transfer-loss term zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedHeldMapsTo.lean#L58).

**The held step stays inside both bounds** · theorem. `step_bounds`: The held-step output obeys the combined size bound and the gradient supremum bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedHeldMapsTo.lean#L63).

### Breakdown.Cert.ExtendedHeldWeakEquation

A held solution is interpreted as a physical weak solution with an actuator multiplier. These identities translate the abstract bordered equation into its tested time-space equation. §7.9: assembling the weak similarity profile

**Joint first derivatives of the profile** · theorem. `Breakdown.Cert.ExtendedHeldWeakEquation.profile_joint`: The approximate profile is jointly once continuously differentiable in time and space. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedHeldWeakEquation.lean#L19).

**Differentiate the similarity flux** · theorem. `joint_deriv_Y`: Differentiating the coordinate-times-field flux gives the field plus that coordinate times the spatial derivative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedHeldWeakEquation.lean#L23).

**Differentiate the quadratic flux** · theorem. `joint_deriv_A`: The derivative of a profile-component times the profile is the sum of its two product-rule terms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedHeldWeakEquation.lean#L39).

**The temporal flux integrates to zero** · theorem. `flux_time_zero`: The compactly supported temporal flux term is integrable with zero total integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedHeldWeakEquation.lean#L54).

**The spatial similarity-advection flux** · definition. `spaceFlux`: The spatial flux combines the negative half-weighted similarity term with the negative quadratic advection term. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedHeldWeakEquation.lean#L61).

**The spatial flux integrates to zero** · theorem. `flux_space_zero`: Each spatial similarity-advection flux is integrable with zero time-space integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedHeldWeakEquation.lean#L64).

**The first-order similarity residual** · definition. `restSmooth`: The smooth residual contains the time derivative, similarity scaling and drift, and the profile's self-advection. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedHeldWeakEquation.lean#L86).

**The profile-test gradient pairing** · definition. `gradPair`: The gradient pairing sums the inner products of corresponding profile and test derivative columns. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedHeldWeakEquation.lean#L90).

**The weak Hessian trace pairing** · definition. `secondDerivPair`: The second-derivative pairing is the test field paired with the trace of the supplied Hessian. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedHeldWeakEquation.lean#L93).

**Split the tested profile expression** · theorem. `bar_rest_split`: The tested profile expression is the smooth residual pairing plus temporal and spatial fluxes and the gradient pairing. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedHeldWeakEquation.lean#L97).

**The first-order residual is continuous** · theorem. `restSmooth_continuous`: The smooth residual field is jointly continuous. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedHeldWeakEquation.lean#L112).

**Continuous profile derivative columns** · theorem. `slice_column_continuous`: Each column of the profile's spatial derivative is jointly continuous. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedHeldWeakEquation.lean#L132).

**Integrability of the gradient pairing** · theorem. `gradPair_integrable`: The profile-test gradient pairing is integrable over time-space. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedHeldWeakEquation.lean#L144).

**The tested profile integral identity** · theorem. `bar_rest_identity`: After the flux terms integrate to zero, the profile weak-form integral equals the residual pairing plus the gradient pairing. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedHeldWeakEquation.lean#L153).

**The Hessian-trace norm bound** · theorem. `secondDerivTrace_norm_le`: The Hessian-trace norm is at most three times the bilinear derivative norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedHeldWeakEquation.lean#L184).

**The Hessian trace is continuous** · theorem. `secondDerivTrace_continuous`: Taking the trace of the bilinear second derivative is continuous. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedHeldWeakEquation.lean#L197).

**The decay bound is nonnegative** · theorem. `Breakdown.Cert.ExtendedHeldWeakEquation.decay_nonneg`: The stated field bounds force the common decay constant to be nonnegative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedHeldWeakEquation.lean#L203).

**The supplied Hessian is test-integrable** · theorem. `secondDerivPair_integrable`: The supplied profile Hessian trace paired with the compact test is integrable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedHeldWeakEquation.lean#L209).

**The gradient-Hessian slice identity** · theorem. `ssp_slice`: The gradient-pairing integral equals minus the supplied Hessian-trace pairing integral on each time slice. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedHeldWeakEquation.lean#L229).

**The gradient-Hessian time-space identity** · theorem. `ssp_zero`: The integrated profile-test gradient pairing is the negative integrated supplied Hessian-trace pairing. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedHeldWeakEquation.lean#L257).

**The complete weak defect decomposition** · theorem. `defect_parts`: The weak defect is the first-order residual minus the Hessian trace plus the actuator sum and pressure gradient. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedHeldWeakEquation.lean#L273).

**Admissible actuator fields** · theorem. `Breakdown.Cert.ExtendedHeldWeakEquation.actuator_field`: Each actuator field satisfies the periodic-field conditions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedHeldWeakEquation.lean#L280).

**Actuator sums can be tested** · theorem. `actuator_pair_integrable`: The finite actuator combination has an integrable pairing with the compactly supported test field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedHeldWeakEquation.lean#L287).

**The nonlinear cross term is integrable** · theorem. `cross_pair_integrable`: The profile-perturbation cross term in the weak formulation is integrable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedHeldWeakEquation.lean#L301).

**The coordinate convection identity** · theorem. `conv_point`: The two coordinate-sum cross pairings equal the pairing of the two matrix-vector convection terms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedHeldWeakEquation.lean#L324).

**Integrability of cross convection** · theorem. `conv_pair_integrable`: The sum of profile-on-perturbation and perturbation-on-profile convection has an integrable test pairing. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedHeldWeakEquation.lean#L333).

**A profile slice satisfies the weak class** · theorem. `slice_weak_profile`: Each approximate-profile slice satisfies the weak-profile slice conditions with some bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedHeldWeakEquation.lean#L387).

**Embed a profile slice into X** · theorem. `slice_embed`: A profile slice has a homogeneous-space element whose velocity and partial derivatives represent its physical velocity and gradient almost everywhere. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedHeldWeakEquation.lean#L447).

**Identify cross terms on time slices** · theorem. `slice_cross`: Almost every spatial slice has equal integrals for the weak cross term and the physical convection pairing. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedHeldWeakEquation.lean#L460).

**The full cross-pairing identity** · theorem. `cross_pair_identity`: The weak cross term is integrable and its integral equals the integral of the physical convection pairing. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedHeldWeakEquation.lean#L508).

### Breakdown.Cert.ExtendedInvariance

The construction must preserve the prescribed space-time symmetries. This file proves invariance of the defect and other data from their physical representations. §7: certificate data and the similarity-profile construction

**The profile respects its symmetry** · theorem. `profile_shift`: A prescribed time shift of the approximate profile equals its spatial push-forward by the associated symmetry. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedInvariance.lean#L20).

**Regularity of each profile slice** · theorem. `profile_slice_contDiff`: Every fixed-time profile slice is once continuously differentiable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedInvariance.lean#L27).

**Each profile slice is differentiable** · theorem. `profile_slice_differentiable`: Each fixed-time approximate-profile field is spatially differentiable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedInvariance.lean#L31).

**Convection preserves invariant forcing** · theorem. `convection_mem`: Applying convection to an invariant perturbation gives forcing in the prescribed symmetry-invariant subspace. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedInvariance.lean#L35).

**The actuator is symmetry invariant** · theorem. `actuatorH_mem`: Every abstract actuator combination lies in the invariant forcing subspace. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedInvariance.lean#L51).

**The first-order invariant residual** · definition. `smoothPart`: The smooth residual combines the time derivative, similarity scaling and drift, and self-advection before Hessian and pressure terms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedInvariance.lean#L60).

**The physical actuator combination** · definition. `forcePart`: The force part is the finite scalar-weighted sum of the physical actuator fields. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedInvariance.lean#L64).

**The defect without pressure** · definition. `restPart`: The residual part subtracts the specified pressure gradient from the physical defect. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedInvariance.lean#L67).

**Expand the pressure-free residual** · theorem. `restPart_eq`: The pressure-free residual is the smooth similarity residual minus the supplied Hessian trace plus the actuator combination. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedInvariance.lean#L70).

**Restore the pressure gradient** · theorem. `defect_eq`: The physical defect is the pressure-free residual plus the specified pressure gradient. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedInvariance.lean#L76).

**Symmetry of the profile time derivative** · theorem. `deriv_shift`: The profile's temporal derivative transforms by the same time shift and spatial symmetry as the profile. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedInvariance.lean#L80).

**Symmetry of the smooth residual** · theorem. `smoothPart_shift`: The first-order similarity residual respects the prescribed time-shift and spatial push-forward relation. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedInvariance.lean#L96).

**Continuity of the Hessian trace** · theorem. `continuous_secondDerivTrace'`: The trace of a bilinear second derivative depends continuously on that derivative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedInvariance.lean#L106).

**Time translation preserves volume** · theorem. `measurePreserving_shift`: Translation in the time coordinate preserves time-space volume. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedInvariance.lean#L109).

**Spatial isometries preserve volume** · theorem. `measurePreserving_rot`: Applying the spatial linear isometry while fixing time preserves time-space volume. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedInvariance.lean#L114).

**Time shifts preserve the full integral** · theorem. `integral_shift`: Translating the time coordinate does not change the full time-space integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedInvariance.lean#L119).

**Spatial rotations preserve the integral** · theorem. `integral_rot`: Applying the spatial isometry does not change the full time-space integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedInvariance.lean#L124).

**Symmetry of the weak Hessian trace** · theorem. `secondDeriv_ae`: The supplied profile Hessian trace respects the time-shift and spatial symmetry almost everywhere. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedInvariance.lean#L129).

**Symmetry of the actuator forcing** · theorem. `force_ae`: The actuator combination respects the time-shift and spatial symmetry almost everywhere. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedInvariance.lean#L151).

**Symmetry of the pressure-free residual** · theorem. `rest_ae`: The pressure-free residual respects the prescribed time-shift and spatial symmetry almost everywhere. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedInvariance.lean#L164).

**Continuity of the first-order residual** · theorem. `continuous_smoothPart`: The time, similarity and advection residual is jointly continuous. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedInvariance.lean#L170).

**Bound a Hessian trace** · theorem. `Breakdown.Cert.ExtendedInvariance.norm_trace_le`: The norm of the Hessian trace is at most three times the Hessian operator norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedInvariance.lean#L184).

**The profile is jointly differentiable** · theorem. `profile_joint_contDiff`: The approximate profile is jointly once continuously differentiable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedInvariance.lean#L198).

**The weak defect is an admissible field** · theorem. `defect_isPeriodicField`: The physical defect satisfies the periodic-field conditions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedInvariance.lean#L202).

**Testing gives compact support** · theorem. `inner_hasCompactSupport`: The pointwise inner product with the time-space test field has compact support. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedInvariance.lean#L234).

**Test the pressure-free residual** · theorem. `rest_integrable`: The pressure-free residual has an integrable pairing with the compactly supported solenoidal test. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedInvariance.lean#L244).

**Pressure drops out of the defect pairing** · theorem. `defect_pairing`: The defect and the pressure-free residual have equal integral pairings against a solenoidal test. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedInvariance.lean#L293).

**The defect is symmetry invariant** · theorem. `defect_mem`: The abstract defect lies in the prescribed invariant forcing subspace. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedInvariance.lean#L310).

### Breakdown.Cert.ExtendedInvarianceTest

Symmetry is checked through transformed test functions. This file develops the test transformations, derivative identities and support conditions needed for the invariance proof. §7: certificate data and the similarity-profile construction

**Time shifts preserve test fields** · theorem. `isSpaceTimeTestField_shift`: A time translate of a smooth compactly supported solenoidal time-space test is again such a test. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedInvarianceTest.lean#L17).

**A coordinate of the inverse rotation** · theorem. `coord_symm_eq`: A coordinate after inverse rotation is the inner product with the corresponding rotated unit vector. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedInvarianceTest.lean#L24).

**Rotations preserve solenoidal tests** · theorem. `isSpaceTimeTestField_rot`: Pulling a time-space test back by the spatial isometry and rotating its values preserves the test-field conditions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedInvarianceTest.lean#L30).

**Time translation of an L² curve** · theorem. `circleLpOrZero_comp_add`: Translating the time-circle representative agrees with the L² time-shift operator. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedInvarianceTest.lean#L60).

**Time shifts commute with conversion** · theorem. `physToHH_comp_add`: Converting the time-translated physical field equals time-shifting its Hilbert-space representation. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedInvarianceTest.lean#L89).

**Periodization commutes with time shifts** · theorem. `periodize_comp_add`: Periodizing a time-translated test equals translating the periodized test. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedInvarianceTest.lean#L98).

**Time-shifting a test representative** · theorem. `shiftLp_testInHH`: The time-shift operator on the Hilbert-space test equals the representative of the shifted physical test. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedInvarianceTest.lean#L105).

**Opposite time shifts cancel** · theorem. `shiftLp_shiftLp_neg`: Applying a time shift after the opposite shift returns the original curve. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedInvarianceTest.lean#L110).

**Move a time shift across a pairing** · theorem. `inner_shiftLp`: A time shift in the first inner-product slot becomes the opposite time shift in the second slot. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedInvarianceTest.lean#L118).

**Move a spatial rotation across a pairing** · theorem. `inner_rotX`: A rotation in the first homogeneous-space inner-product slot becomes its inverse in the second slot. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedInvarianceTest.lean#L124).

**Move a curve rotation across a pairing** · theorem. `inner_rotHH`: A spatial rotation in the first curve-space inner-product slot becomes the inverse rotation in the second slot. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedInvarianceTest.lean#L129).

**Rotate a time-circle L² curve** · theorem. `circleLpOrZero_comp_rot`: Applying the spatial rotation to the representative commutes with the time-circle L² conversion. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedInvarianceTest.lean#L137).

**Push-forwards commute with conversion** · theorem. `physToHH_comp_pushForward`: Converting the spatially pushed-forward physical field equals rotating its abstract Hilbert-space representation. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedInvarianceTest.lean#L166).

**Periodization respects rotated tests** · theorem. `periodize_rot`: Periodizing the pulled-back rotated test equals the corresponding spatial push-forward of the periodized test. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedInvarianceTest.lean#L176).

**Rotate a test representative** · theorem. `rotHH_testInHH`: The inverse spatial rotation of a Hilbert-space test is represented by the corresponding rotated physical test. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedInvarianceTest.lean#L182).

### Breakdown.Cert.ExtendedInvarianceTrace

The weak Hessian trace must transform correctly under symmetry. This file verifies that rule and the associated physical operator identities. §7: certificate data and the similarity-profile construction

**Transpose coordinates of an isometry** · theorem. `coord_rot_eq`: A matrix coordinate of the isometry equals the transposed coordinate of its inverse. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedInvarianceTrace.lean#L16).

**Orthogonality of rotated basis columns** · theorem. `sum_coord_rot_mul`: Summing products of rotated basis coordinates gives one for equal coordinate indices and zero otherwise. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedInvarianceTrace.lean#L25).

**Expand a bilinear map in coordinates** · theorem. `bilin_expand`: A bilinear map on two vectors is the double coordinate sum of its values on basis-vector pairs. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedInvarianceTrace.lean#L33).

**The bilinear trace is basis independent** · theorem. `bilin_trace_rot`: Summing a bilinear map on the rotated orthonormal basis gives the same diagonal sum as the original basis. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedInvarianceTrace.lean#L43).

**The rotated diagonal sum is the trace** · theorem. `trace_rot`: The diagonal sum on the rotated orthonormal basis equals the second-derivative trace. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedInvarianceTrace.lean#L58).

**Weak Hessian traces respect rotations** · theorem. `secondDerivTrace_pushForward`: The traces of the two weak Hessians related by spatial push-forward satisfy the same push-forward relation almost everywhere. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedInvarianceTrace.lean#L62).

### Breakdown.Cert.ExtendedMultiplierContinuity

After solving at each fixed parameter, the resulting multiplier must depend continuously on that parameter. This file proves that continuity so the finite-box zero theorem can be applied. §7.8: fixed-parameter contraction and the parameter zero

**Select the held multiplier** · definition. `heldMultiplier`: The held multiplier chooses a multiplier from an existing held solution and uses zero when no such solution exists. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedMultiplierContinuity.lean#L14).

**The selected multiplier has a solution** · theorem. `heldMultiplier_spec`: Under the held-existence hypotheses, some forcing pairs with the chosen held multiplier to form a held solution. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedMultiplierContinuity.lean#L17).

**The selected total multiplier** · theorem. `Breakdown.Cert.ExtendedMultiplierContinuity.multiplierOf_eq`: The total multiplier is the approximate multiplier plus the multiplier selected with the held correction. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedMultiplierContinuity.lean#L23).

**The held multiplier is continuous** · theorem. `heldMultiplier_continuousOn`: The selected held multiplier varies continuously on the admissible parameter set. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedMultiplierContinuity.lean#L26).

### Breakdown.Cert.ExtendedNodes

The extended construction is organized by named analytic obligations. This file defines the defect and held step, then states the row, symmetry, data, convection, frozen-form, supremum, metric and adjoint-pairing interfaces. §7: certificate data and the similarity-profile construction

**Source namespace `Breakdown.ExtendedCertificateData`.**

**The Hilbert-space weak defect** · definition. `defectH`: The abstract weak defect is the physical weak defect converted to the time-circle forcing Hilbert space. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedNodes.lean#L59).

**The normalized held iteration** · definition. `heldStep`: The held iteration applies the bordered inverse to the nonlinear held right side and then the free inverse to its forcing component. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedNodes.lean#L64).

**Source namespace `Breakdown.Cert`.**

**A normalized certificate gives a profile** · interface proposition. `ExtendedNormalOrbitHolds`: This interface requires an extended certificate normalized to unit multiplier weight and model equal to profile with zero gap and shift to produce a weak periodic similarity profile. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedNodes.lean#L92).

Proved by `Breakdown.Cert.extended_normal_orbit_of_nodes`.

**The finite row-norm estimates** · interface proposition. `RowNormHolds`: This interface requires the weighted orthonormal row norm to obey the triangle inequality, sign invariance and its period-norm bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedNodes.lean#L97).

Proved by `Breakdown.Cert.rowNormHolds`.

**Symmetry of the extended construction** · interface proposition. `ExtendedInvarianceHolds`: This interface requires convection, quadratic forcing, actuators and defect to lie in the prescribed invariant forcing subspace. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedNodes.lean#L115).

Proved by `Breakdown.Cert.extendedInvarianceHolds_of`.

**Continuity of extended convection** · interface proposition. `ExtendedConvectionContinuityHolds`: This interface requires the extended convection operator to vary continuously on the admissible parameter set. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedNodes.lean#L123).

Proved by `Breakdown.Cert.extendedConvectionContinuityHolds_of`.

**Physical readings of extended data** · interface proposition. `ExtendedDataHolds`: This interface requires the weak defect, actuators and pin map to have their physical test pairings and stated norm bounds. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedNodes.lean#L127).

Proved by `Breakdown.Cert.extendedDataHolds_of`.

**The extended frozen-form bridge** · interface proposition. `ExtendedFrozenBridgeHolds`: This interface transfers the profile frozen-form lower bound to almost every time-circle slice of the free inverse. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedNodes.lean#L153).

Proved by `Breakdown.Cert.extendedFrozenBridgeHolds_of`.

**A supremum bound for the free inverse** · interface proposition. `ExtendedSupBoundHolds`: This interface requires a finite gradient supremum for the invariant free inverse and the displayed coercive energy estimate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedNodes.lean#L164).

Proved by `Breakdown.Cert.extendedSupBoundHolds_of`.

**The held set and its metric** · interface proposition. `ExtendedHeldMetricHolds`: This interface requires the held set to be closed and its distance to dominate ambient norm, satisfy the triangle inequality and pass upper bounds to limits. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedNodes.lean#L185).

Proved by `Breakdown.Cert.extendedHeldMetricHolds_of`.

**The physical adjoint pairing** · interface proposition. `ExtendedAdjointPairingHolds`: This interface identifies the period pairing with each admissible adjoint field with the inner product of their abstract physical conversions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedNodes.lean#L225).

Proved by `Breakdown.Cert.extendedAdjointPairingHolds_of`.

### Breakdown.Cert.ExtendedRowNorm

The finite-dimensional pinning rows need a bound compatible with the Hilbert-space norm. This file derives that row bound from the supplied physical pinning data. §7: certificate data and the similarity-profile construction

**The unit-time product measure** · abbreviation. `slabMeasure`: The slab measure is Lebesgue time measure restricted to the closed unit interval multiplied by spatial volume. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedRowNorm.lean#L12).

**The slab measure as a restriction** · theorem. `slabMeasure_eq`: The unit-time product measure equals full time-space volume restricted to the unit-time strip. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedRowNorm.lean#L14).

**Field measurability on the slab** · theorem. `aestronglyMeasurable_slab`: The admissible periodic field is almost everywhere strongly measurable for the slab measure. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedRowNorm.lean#L18).

**A period energy as a slab integral** · theorem. `periodLIntegral_eq_slab'`: The iterated periodic square integral equals the single nonnegative square integral against the slab measure. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedRowNorm.lean#L23).

**The slab formula for period energy** · theorem. `periodLIntegral_eq_slab`: The field's periodic square integral is its nonnegative square integral on the unit-time slab. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedRowNorm.lean#L33).

**Integrable square energy on the slab** · theorem. `integrable_sq_slab`: The squared norm of an admissible periodic field is integrable for the slab measure. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedRowNorm.lean#L38).

**A periodic field belongs to slab L²** · theorem. `memLp_slab`: An admissible periodic field belongs to the slab L² space. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedRowNorm.lean#L48).

**Period pairing is an L² inner product** · theorem. `periodPairing_eq_inner`: The physical period pairing is the inner product of the two slab L² classes. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedRowNorm.lean#L52).

**The period norm is the slab L² norm** · theorem. `periodNorm_eq_norm`: The physical period norm equals the norm of the corresponding slab L² element. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedRowNorm.lean#L66).

**Add fields in the period pairing** · theorem. `periodPairing_add_left`: The period pairing is additive in its first field argument. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedRowNorm.lean#L81).

**Negate a field in the period pairing** · theorem. `periodPairing_neg_left`: Negating the first field negates the period pairing. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedRowNorm.lean#L88).

**Sum admissible periodic fields** · theorem. `isPeriodicField_add`: The sum of two admissible periodic fields remains admissible. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedRowNorm.lean#L93).

**The weighted row triangle inequality** · theorem. `weighted_sqrt_add_le`: The square root of the weighted coordinate sum of squares obeys the triangle inequality. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedRowNorm.lean#L106).

### Breakdown.Cert.ExtendedSigmaProfileOfHeld

A zero-multiplier held solution produces a similarity profile. This file assembles its weak equation, regularity, symmetry and periodicity into the required profile property. §7.9: assembling the weak similarity profile

**A classical gradient is a weak gradient** · theorem. `isWeakGradient_of_contDiff`: A continuously differentiable vector field satisfies the weak-gradient relation with its derivative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedSigmaProfileOfHeld.lean#L12).

**Add weak gradients** · theorem. `isWeakGradient_add`: The sum of two fields has the sum of their weak gradients. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedSigmaProfileOfHeld.lean#L28).

**Bound a power of a sum** · theorem. `norm_add_pow_le`: The norm of a sum to a natural power is bounded by two to that power times the sum of the two norm powers. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedSigmaProfileOfHeld.lean#L57).

**The radial decay envelope is continuous** · theorem. `continuous_decay`: The constant times the inverse radial power is a continuous function of position. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedSigmaProfileOfHeld.lean#L74).

**Integrate a power-of-sum bound** · theorem. `lintegral_norm_add_pow_le`: A decay envelope for the first field bounds the sum's nonnegative norm-power integral together with the second field's integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedSigmaProfileOfHeld.lean#L78).

**Convert the decay-envelope integral** · theorem. `lintegral_le_of_decay`: The nonnegative integral of the admissible real decay envelope is bounded by the nonnegative image of its real integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedSigmaProfileOfHeld.lean#L100).

**A nonnegative decay-envelope integral** · theorem. `integral_decay_nonneg`: The integral of the nonnegative radial decay envelope is nonnegative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedSigmaProfileOfHeld.lean#L107).

**Raise a decay bound to a power** · theorem. `pow_le_of_decay`: The given norm decay estimate yields the corresponding power estimate with its adjusted radial exponent. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedSigmaProfileOfHeld.lean#L110).

**The decay bound is nonnegative** · theorem. `Breakdown.Cert.ExtendedSigmaProfileOfHeld.decay_nonneg`: The stated field bounds force the common decay constant to be nonnegative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedSigmaProfileOfHeld.lean#L120).

**Once differentiable profile slices** · theorem. `profile_slice`: Each fixed-time approximate profile is once continuously differentiable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedSigmaProfileOfHeld.lean#L126).

**Joint first derivatives of the profile** · theorem. `Breakdown.Cert.ExtendedSigmaProfileOfHeld.profile_joint`: The approximate profile is jointly once continuously differentiable in time and space. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedSigmaProfileOfHeld.lean#L130).

**An integrable sixth-power profile bound** · theorem. `profile_sixth`: The profile's sixth power is bounded by the sixth power of its decay constant times inverse sixth-power radial decay. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedSigmaProfileOfHeld.lean#L134).

**An integrable profile-gradient bound** · theorem. `profile_grad_sq`: The squared profile-gradient norm is bounded by the squared decay constant times inverse fourth-power radial decay. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedSigmaProfileOfHeld.lean#L139).

**An integrable profile-Hessian bound** · theorem. `profile_secondDeriv_sq`: The squared supplied profile-Hessian norm is bounded by the squared decay constant times inverse sixth-power radial decay. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedSigmaProfileOfHeld.lean#L143).

**A sixth-power corrected-field bound** · theorem. `sixth_bound`: The corrected velocity's spatial sixth-power integral is bounded by the profile decay integral and the perturbation's uniform sixth-power bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedSigmaProfileOfHeld.lean#L147).

**A squared corrected-gradient bound** · theorem. `grad_bound`: The corrected gradient's spatial square integral is bounded by the profile-gradient decay integral and the perturbation-gradient bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedSigmaProfileOfHeld.lean#L164).

**The corrected Hessian has finite energy** · theorem. `secondDeriv_finite_of_period`: The sum of the profile's supplied Hessian and the perturbation Hessian has finite periodic square integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedSigmaProfileOfHeld.lean#L181).

**The corrected gradient's Hessian** · theorem. `weak_secondDeriv_sum`: Each column of the corrected gradient has the sum of the profile and perturbation Hessians as its weak gradient. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedSigmaProfileOfHeld.lean#L200).

**The corrected field is divergence free** · theorem. `divergence_sum`: The trace of the summed profile and perturbation gradients vanishes almost everywhere on each slice. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedSigmaProfileOfHeld.lean#L218).

### Breakdown.Cert.ExtendedStiffEnclosure

The bordered inverse also needs control of its finite-dimensional stiff part. This file proves the stated enclosure from the certificate's row and residual bounds. §7: certificate data and the similarity-profile construction

**Positive weights give nonnegative energy** · theorem. `energyW_nonneg_of_weight`: The weight positivity hypothesis makes the weighted perturbation energy nonnegative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedStiffEnclosure.lean#L11).

**The multiplier norm fits the held size** · theorem. `sqrt_sum_sq_le_sizeZ`: The Euclidean norm of the multiplier vector is bounded by the combined held-state size. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedStiffEnclosure.lean#L17).

### Breakdown.Cert.ExtendedUnitWeight

The finite-dimensional multiplier weight is normalized by rescaling actuators and multiplier coordinates. This file proves that the defect and adjusted multiplier stay compatible with that normalization and records the rescaled adjoint error. §7: certificate data and the similarity-profile construction

**Rescale the actuator coefficients** · theorem. `isRightSide_of_smul_actuator`: Scaling the actuator family can be absorbed into the multiplier coefficients in the physical right-side equation. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedUnitWeight.lean#L11).

**Cancel inverse actuator scalings** · theorem. `sum_smul_scale`: Scaling the coefficients and inversely scaling the actuator vectors leaves their finite linear combination unchanged. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedUnitWeight.lean#L22).

**Scale a period pairing** · theorem. `periodPairing_smul_left`: Multiplying the first physical field by a real scalar multiplies its period pairing by that scalar. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedUnitWeight.lean#L29).

**Scale the multiplier norm** · theorem. `vecNorm_smul`: The Euclidean coefficient norm scales by the scalar's absolute value. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedUnitWeight.lean#L34).

**Normalization preserves the defect** · theorem. `defect_withUnitWeight`: The unit-multiplier-weight normalization leaves the physical defect unchanged. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedUnitWeight.lean#L41).

**Keep the framed multipliers** · theorem. `frame_multiplier_withUnitWeight`: The frame coordinates of the approximate multiplier remain unchanged under unit-weight normalization. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedUnitWeight.lean#L51).

**Keep the adjusted multipliers** · theorem. `adjustedMultiplier_withUnitWeight`: The adjusted multiplier function is unchanged by unit-weight normalization. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedUnitWeight.lean#L59).

**Rescale the actuator-adjoint error** · theorem. `actuatorAdjointError_withUnitWeight`: Unit-weight normalization divides the actuator-adjoint error vector by the original multiplier weight. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedUnitWeight.lean#L66).

**Rescale the actuator square integral** · theorem. `actuator_norm_withUnitWeight`: The normalized actuator square integral is the original one multiplied by the reciprocal multiplier weight squared. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedUnitWeight.lean#L75).

### Breakdown.Cert.FixedPointCount

The box zero theorem is supported by a finite combinatorial parity argument. This file counts fully labelled simplices and relates their parity to boundary incidences. §7.8: the finite-box parameter step in the formal proof

**Source namespace `Breakdown.GridSimplex`.**

**All labels up to a bound occur** · proposition definition. `Covers`: The covering predicate requires every label from zero through the given bound to occur among the vertex labels. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FixedPointCount.lean#L6).

**Labels occur away from one vertex** · proposition definition. `CoversFrom`: The punctured covering predicate requires every positive label through the bound to occur at a vertex other than the omitted one. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FixedPointCount.lean#L9).

**Source namespace `Breakdown.GridSimplex.CountInternal`.**

**Full label coverage forces injectivity** · theorem. `injective_of_covers`: With the matching finite cardinalities, covering every required label makes the label map injective. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FixedPointCount.lean#L14).

**Exactly two faces carry the labels** · theorem. `card_doors_eq_two`: In the indicated repeated-label case, exactly two vertex omissions preserve all required positive labels. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FixedPointCount.lean#L27).

**Source namespace `Breakdown.GridSimplex`.**

**The parity of labelled faces** · theorem. `card_coversFrom_mod_two`: The number of punctured-covering faces is odd exactly when the full covering condition holds. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FixedPointCount.lean#L107).

### Breakdown.Cert.FixedPointDefs

The formal parameter argument uses a combinatorial fixed-point proof on a finite box. This file defines its grid, labels, simplices and incidence data. §7.8: the finite-box parameter step in the formal proof

**A simplex vertex in the grid** · definition. `vertex`: The j-th simplex vertex increments precisely the grid coordinates whose permutation rank is less than j. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FixedPointDefs.lean#L6).

**A fully labelled grid simplex** · proposition definition. `IsFull`: The simplex is full when its vertex labels cover every required label. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FixedPointDefs.lean#L9).

**A labelled simplex face** · proposition definition. `IsDoor`: The chosen omitted-vertex face is a door when its remaining vertices carry all required positive labels. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FixedPointDefs.lean#L12).

**An outer face of the grid** · proposition definition. `OnBoundary`: The boundary condition identifies an extreme simplex face lying on the upper or lower grid boundary. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FixedPointDefs.lean#L16).

**The set of fully labelled simplices** · definition. `fullSet`: The finite full set contains the grid cells and permutations whose associated simplex is fully labelled. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FixedPointDefs.lean#L22).

**The set of labelled faces** · definition. `doorSet`: The finite door set contains all simplex-face triples whose remaining vertices carry the required labels. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FixedPointDefs.lean#L27).

**The labelled faces on the boundary** · definition. `boundaryDoorSet`: The boundary-door set restricts the door set to faces lying on the outer grid boundary. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FixedPointDefs.lean#L32).

**Membership in the full-simplex set** · theorem. `mem_fullSet`: A grid-cell permutation belongs to the full set exactly when its simplex is fully labelled. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FixedPointDefs.lean#L36).

**Membership in the labelled-face set** · theorem. `mem_doorSet`: A face triple belongs to the door set exactly when it satisfies the door-label condition. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FixedPointDefs.lean#L42).

**Membership in the boundary-door set** · theorem. `mem_boundaryDoorSet`: A face belongs to the boundary-door set exactly when it is both a door and on the grid boundary. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FixedPointDefs.lean#L48).

**Grid simplex coordinates stay bounded** · theorem. `vertex_le`: Every coordinate of a simplex vertex is at most the outer grid bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FixedPointDefs.lean#L54).

### Breakdown.Cert.FixedPointFace

The combinatorial proof must identify which faces lie on the boundary. This file relates boundary doors to fully labelled simplices in one lower dimension. §7.8: the finite-box parameter step in the formal proof

**Source namespace `Breakdown.GridSimplex.FaceInternal`.**

**Vertices of the upper boundary simplex** · theorem. `vertex_cons_succ`: The successor vertices of the boundary simplex are obtained by adjoining the upper boundary coordinate to the lower-dimensional vertices. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FixedPointFace.lean#L7).

**Boundary labels are positive** · theorem. `label_pos`: The labelling condition forces labels on the designated upper boundary face to be positive. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FixedPointFace.lean#L16).

**Boundary doors give full simplices** · theorem. `isDoor_cons_iff`: The selected upper-boundary door condition is equivalent to fullness of the induced lower-dimensional labelling after subtracting one. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FixedPointFace.lean#L23).

**The only permitted boundary-door shape** · theorem. `boundary_shape`: The boundary labelling rules force a boundary door to lie on the designated first-coordinate upper face. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FixedPointFace.lean#L52).

**Source namespace `Breakdown.GridSimplex`.**

**Count boundary doors one dimension lower** · theorem. `card_boundaryDoorSet`: The number of boundary doors equals the number of full simplices for the induced lower-dimensional labelling. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FixedPointFace.lean#L91).

### Breakdown.Cert.FixedPointOdd

The parity calculation culminates in an odd number of fully labelled simplices. That nonemptiness is the combinatorial existence step behind the box fixed-point theorem. §7.8: the finite-box parameter step in the formal proof

**An odd count of full simplices** · theorem. `odd_card_fullSet`: The boundary-compatible labelling has an odd number of fully labelled simplices. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FixedPointOdd.lean#L7).

**A simplex crosses every binary label** · theorem. `exists_complete_simplex`: There is a grid simplex whose vertices include both truth values for every coordinate label. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FixedPointOdd.lean#L53).

### Breakdown.Cert.FixedPointPivot

Adjacent labelled simplices are related by a pivot operation. This file proves the pivot identities and incidence properties used in the finite counting argument. §7.8: the finite-box parameter step in the formal proof

**Source namespace `Breakdown.GridSimplex`.**

**Door parity equals full-simplex parity** · theorem. `card_doorSet_mod_two`: The number of labelled faces has the same parity as the number of fully labelled simplices. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FixedPointPivot.lean#L6).

**Source namespace `Breakdown.GridSimplex.PivotInternal`.**

**Increase one grid coordinate** · definition. `up`: The upward move increments the selected grid coordinate while keeping it below the finite-grid bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FixedPointPivot.lean#L37).

**Decrease one grid coordinate** · definition. `down`: The downward move subtracts one from the selected natural grid coordinate and leaves the others fixed. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FixedPointPivot.lean#L40).

**The upward move in natural coordinates** · theorem. `coe_up`: The upward move is the coordinatewise conditional increment capped by the grid's last value. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FixedPointPivot.lean#L43).

**The downward move in natural coordinates** · theorem. `coe_down`: The downward move subtracts one only at the selected coordinate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FixedPointPivot.lean#L48).

**The lower adjacent face index** · definition. `lo`: The lower pivot index is the omitted face index minus one, interpreted within the finite index type. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FixedPointPivot.lean#L53).

**The upper adjacent face index** · definition. `hi`: The upper pivot index is the omitted face index capped by the last coordinate index. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FixedPointPivot.lean#L55).

**Pair the two simplices across a face** · definition. `pivot`: The pivot crosses an extreme face by moving its base cell and cyclically rotating the permutation, or crosses an interior face by swapping adjacent ranks. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FixedPointPivot.lean#L57).

**The last face is distinct from the first** · theorem. `last_ne_zero'`: The last face index in this positive-dimensional simplex is not zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FixedPointPivot.lean#L65).

**Pivot across the first face** · theorem. `pivot_zero`: Pivoting across the first face moves the selected base coordinate upward and cyclically rotates the permutation backward. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FixedPointPivot.lean#L68).

**Pivot across the last face** · theorem. `pivot_last`: Pivoting across the last face moves the selected base coordinate downward and cyclically rotates the permutation forward. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FixedPointPivot.lean#L73).

**Pivot across an interior face** · theorem. `pivot_mid`: An interior-face pivot leaves the base cell unchanged and swaps the two adjacent permutation ranks. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FixedPointPivot.lean#L78).

**The inverse cyclic index formula** · theorem. `coe_rot_symm`: The inverse cyclic permutation sends zero to the last index and subtracts one from every other index. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FixedPointPivot.lean#L83).

**The cyclic index formula** · theorem. `coe_rot`: The cyclic permutation sends the last index to zero and adds one to every other index. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FixedPointPivot.lean#L93).

**Vertices after the upward pivot** · theorem. `vertex_up`: Away from the omitted face, the upward-pivot simplex vertices are the shifted original vertices. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FixedPointPivot.lean#L100).

**Vertices after the downward pivot** · theorem. `vertex_down`: The successor vertices after the downward pivot match the original simplex vertices. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FixedPointPivot.lean#L115).

**The shared vertices survive the swap** · theorem. `vertex_swap`: Swapping the adjacent ranks preserves the simplex vertices belonging to the shared face. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FixedPointPivot.lean#L132).

**Room for the upward pivot** · theorem. `not_boundary_zero`: A first face off the boundary leaves enough grid room for the upward pivot. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FixedPointPivot.lean#L145).

**Room for the downward pivot** · theorem. `not_boundary_last`: A last face off the boundary has a nonzero base coordinate available for the downward pivot. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FixedPointPivot.lean#L151).

**Track the inverse backward rotation** · theorem. `symm_rot_symm`: The last coordinate selected by the inverse backward-rotated permutation is the original first selected coordinate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FixedPointPivot.lean#L155).

**Track the inverse forward rotation** · theorem. `symm_rot`: The first coordinate selected by the inverse forward-rotated permutation is the original last selected coordinate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FixedPointPivot.lean#L159).

**Pivoting twice returns the original face** · theorem. `pivot_pivot`: On interior doors, applying the pivot twice recovers the original face triple. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FixedPointPivot.lean#L165).

**An interior pivot has no fixed point** · theorem. `pivot_ne`: The pivot of an interior face differs from that face. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FixedPointPivot.lean#L201).

**The pivot stays off the boundary** · theorem. `pivot_not_boundary`: The pivot of an interior door remains an interior face. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FixedPointPivot.lean#L221).

**The pivot preserves door labels** · theorem. `pivot_door`: The shared face retains its door-label condition after the pivot. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FixedPointPivot.lean#L250).

**Source namespace `Breakdown.GridSimplex`.**

**Interior doors occur in pairs** · theorem. `even_card_interior_doors`: The fixed-point-free pivot involution makes the number of interior doors even. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FixedPointPivot.lean#L294).

**The boundary determines simplex parity** · theorem. `card_fullSet_mod_two_eq`: The number of fully labelled simplices has the same parity as the number of boundary doors. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FixedPointPivot.lean#L314).

### Breakdown.Cert.FreeEnergyLocal

The free equation first has a continuous energy representative on dense forcing data. This file obtains uniform bounds and passes through L² approximation to produce such a representative for general forcing. §7.5: the free similarity equation

**Continuous periodic energy readings** · proposition definition. `IsEnergyCurve`: An energy curve represents the free inverse's gradient almost everywhere and satisfies the period-scaled interval energy identity. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeEnergyLocal.lean#L17).

**Verify the chosen free inverse** · theorem. `freeInvSpec_freeInv`: Assuming the free-inverse existence property and a positive period, the selected free inverse satisfies its defining gradient relation. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeEnergyLocal.lean#L24).

**Recover the energy-curve predicate** · theorem. `energyCurve_of_local`: The local energy-curve data supply the continuous periodic representative and its interval energy identity. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeEnergyLocal.lean#L30).

**Energy curves for dense forcing data** · theorem. `exists_dense_curve`: There is a dense forcing submodule on which every forcing has a continuous periodic energy curve. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeEnergyLocal.lean#L65).

**The curve L² norm as an integral** · theorem. `norm_sq_eq_integral_circle`: The squared L² norm of a time-circle curve equals the integral of its representative's squared norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeEnergyLocal.lean#L80).

**The curve's square norm is integrable** · theorem. `integrable_norm_sq_circle`: The representative of a time-circle L² curve has integrable squared norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeEnergyLocal.lean#L86).

**One-period integrability of a lift** · theorem. `lift_intervalIntegrable`: An integrable time-circle function has an integrable real lift on every interval of length one. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeEnergyLocal.lean#L92).

**Integrating a full period** · theorem. `lift_intervalIntegral`: The real lift's integral over any full period equals its time-circle integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeEnergyLocal.lean#L97).

**A uniform bound from the energy identity** · theorem. `sup_bound_core`: For positive period P, the continuous energy representative satisfying the periodic energy identity has pointwise squared norm at most (4 + 6P) times forcing energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeEnergyLocal.lean#L101).

**A uniform energy-reading bound** · theorem. `norm_sq_le_of_energyCurve`: An energy curve has squared norm at most four plus six times the period, multiplied by the forcing norm squared. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeEnergyLocal.lean#L185).

**Subtract energy representatives** · theorem. `energyCurve_sub`: The representative curve for a forcing difference equals the pointwise difference of the two original energy curves. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeEnergyLocal.lean#L218).

**A limit represents the limiting gradient** · theorem. `ae_eq_of_tendsto`: The convergent representative curves give an almost-everywhere representative of the free inverse for the limiting forcing. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeEnergyLocal.lean#L244).

**The forcing-minus-dissipation density** · definition. `circInt`: The circle integrand pairs forcing with the second component of its free inverse and subtracts that component's squared norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeEnergyLocal.lean#L278).

**The energy integrand is integrable** · theorem. `integrable_circInt`: The forcing-minus-second-component energy integrand is integrable over the time circle. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeEnergyLocal.lean#L282).

**Control a change in the energy integrand** · theorem. `circ_bound`: The change in the forcing-minus-square expression is bounded by the listed products of input and second-component differences. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeEnergyLocal.lean#L296).

**Products of curve norms are integrable** · theorem. `integrable_norm_mul_circle`: The product of the norms of two time-circle L² curves is integrable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeEnergyLocal.lean#L313).

**Cauchy-Schwarz on the time circle** · theorem. `integral_norm_mul_le_circle`: The integral of the product of two curve norms is at most the product of their L² norms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeEnergyLocal.lean#L325).

**A norm-difference product is integrable** · theorem. `integrable_norm_sub_mul_circle`: The norm of an L² curve difference times another L² curve norm is integrable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeEnergyLocal.lean#L346).

**Bound a curve-difference pairing** · theorem. `integral_norm_sub_mul_le_circle`: The integral of the norm-difference product is at most the L² difference norm times the other curve norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeEnergyLocal.lean#L354).

**Read the energy through the curve map** · theorem. `circInt_ae`: The slice-based energy integrand agrees almost everywhere with the formula using the second-component curve map. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeEnergyLocal.lean#L366).

**An integral bound for energy differences** · theorem. `circ_integral_le`: The integral of the absolute difference of the two energy densities is bounded by the four L² norm products. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeEnergyLocal.lean#L376).

**Energy densities converge in L¹** · theorem. `tendsto_circInt`: Converging forcing data make the corresponding energy densities converge in absolute integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeEnergyLocal.lean#L407).

**An interval bound from the circle** · theorem. `lift_bound`: The lifted function is interval integrable and its integral is bounded by the interval's ceiling length times its circle norm integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeEnergyLocal.lean#L428).

**The interval energy terms converge** · theorem. `tendsto_rhs_of_tendsto`: Forcing convergence and uniform representative convergence pass the right-hand side of the interval energy identity to the limit. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeEnergyLocal.lean#L468).

**Energy curves survive limits** · theorem. `energyCurve_of_tendsto`: The limit of the convergent energy-curve data is an energy curve for the limiting forcing. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeEnergyLocal.lean#L537).

**Take a square root of a norm bound** · theorem. `le_sqrt_mul_of_sq_le`: The squared inequality and nonnegativity give the corresponding square-root bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeEnergyLocal.lean#L559).

**Choose a continuous periodic energy** · theorem. `exists_energy_function`: Every forcing has a continuous periodic scalar energy representative satisfying the interval energy identity. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeEnergyLocal.lean#L607).

### Breakdown.Cert.FreeEquivariant

The free inverse must preserve the certificate's symmetries. This file proves commutation of the propagator, its integral and the inverse with the relevant symmetry actions. §7.5: the free similarity equation

**A representative of a shifted curve** · theorem. `coeFn_shiftLp`: The shifted L² curve is represented almost everywhere by translation of the original time-circle representative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeEquivariant.lean#L17).

**Time shift commutes with value maps** · theorem. `shiftLp_compLpL`: Shifting a curve commutes with applying a continuous linear map to its values. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeEquivariant.lean#L22).

**Time shifts commute** · theorem. `shiftLp_shiftLp`: Two time-shift operators on L² curves commute. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeEquivariant.lean#L34).

**Lift commuting maps to curve spaces** · theorem. `compLpL_comm`: The stated composition identity between value maps gives the corresponding identity between their induced L² maps. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeEquivariant.lean#L43).

**Rotation commutes with smoothing** · theorem. `rotX_smoothH`: Spatial rotation commutes with the smoothed square-root Laplacian operator. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeEquivariant.lean#L58).

**Rotation commutes with the propagator** · theorem. `rotX_slicePropagator`: Spatial rotation commutes with the slice propagator. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeEquivariant.lean#L77).

**Rotation commutes on propagator curves** · theorem. `rotHH_compLpL_slicePropagator`: Rotating a time-circle curve commutes with applying the slice propagator pointwise. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeEquivariant.lean#L88).

**The invariant-forcing condition** · theorem. `mem_invariantHH_iff`: Forcing is invariant exactly when each prescribed time shift agrees with the corresponding spatial rotation. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeEquivariant.lean#L93).

**Propagation preserves invariance** · theorem. `propagatorIntegrand_mem`: Each propagator integrand of invariant forcing lies in the same invariant subspace. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeEquivariant.lean#L106).

**Integrals preserve invariance** · theorem. `integral_mem`: The integral of the invariant propagator integrands remains in the closed invariant forcing subspace. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeEquivariant.lean#L131).

**Identify the selected gradient inverse** · theorem. `gradInv_eq`: When a gradient-inverse specification witness exists, the definition selects that witness. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeEquivariant.lean#L144).

**The gradient inverse's fallback value** · theorem. `gradInv_eq_zero`: If no gradient-inverse specification witness exists, the conditional definition returns zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeEquivariant.lean#L148).

**The gradient inverse preserves symmetry** · theorem. `gradInv_mem`: The selected gradient inverse maps invariant forcing into the invariant subspace. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeEquivariant.lean#L152).

**The free inverse is its selected witness** · theorem. `freeInv_eq`: When a free-inverse specification witness exists, the definition is the operator chosen from that witness. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeEquivariant.lean#L161).

### Breakdown.Cert.FreeInv

The free inverse is built from its gradient inverse and the graph relation. This file defines the selected bounded operator and proves the algebraic and norm properties needed downstream. §7.5: the free similarity equation

**Source namespace `Breakdown.Cert`.**

**Dense forcing has full energy data** · theorem. `exists_dense_energyCurve`: A dense forcing submodule admits continuous periodic gradient representatives, second-component curves and the interval energy identity. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeInv.lean#L14).

**Source namespace `Breakdown.Cert.Internal.FreeInv`.**

**The Laplacian-root derivative is unique** · theorem. `second_eq_of_halfSsp`: Two elements satisfying the same square-root Laplacian relation are equal. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeInv.lean#L29).

**The graph gradient determines its input** · theorem. `gradPart_injective`: The gradient component uniquely determines an element of the square-root Laplacian graph space. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeInv.lean#L36).

**Read the gradient map on curve values** · theorem. `Breakdown.Cert.FreeInv.gradCLM_ae`: Almost everywhere on the time circle, the gradient-curve map is the gradient component of the original representative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeInv.lean#L44).

**The second-component curve formula** · theorem. `secondCLM_ae`: Almost everywhere, the second-component curve map evaluates to the second component of the original graph-space representative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeInv.lean#L48).

**The gradient determines the graph curve** · theorem. `gradCLM_injective`: The gradient-component map on L² graph-space curves is injective. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeInv.lean#L52).

**The graph norm from its components** · theorem. `norm_xbar_le`: The graph-space norm is at most the sum of its gradient and second-component norms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeInv.lean#L60).

**Bound a curve by two value maps** · theorem. `norm_le_compLpL_add`: The pointwise two-map norm estimate integrates to the sum of the two induced L² norms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeInv.lean#L68).

**The curve graph norm from its components** · theorem. `norm_XX_le`: The graph-curve norm is at most the sum of the gradient-curve and second-component-curve norms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeInv.lean#L90).

**A quadratic estimate bounds both parts** · theorem. `bound_of_le_inner`: The scalar energy inequality bounds the combined quadratic energy and gives the separate second and gradient norm bounds. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeInv.lean#L93).

**Extend the graph inverse from dense data** · theorem. `exists_extension`: The compatible bounded graph lift defined on dense data extends to a continuous linear map with the same quadratic energy bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeInv.lean#L102).

**A bounded free inverse exists** · theorem. `exists_freeInvSpec_bound`: A dense forcing subspace with compatible graph lifts satisfying the energy inequality extends, under graph closedness, to a free inverse with the same forcing bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeInv.lean#L156).

**The product norm is at most the norm sum** · theorem. `norm_toLp_le`: The L² product norm of a pair is bounded by the sum of its component norms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeInv.lean#L163).

**Lift compatible curves into a subspace** · theorem. `exists_pair_lift`: The compatible L² component curves have an L²-valued lift to the closed graph subspace. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeInv.lean#L174).

**The L² curve square-norm formula** · theorem. `norm_sq_Lp_eq`: The squared norm of the L² curve is the integral of its pointwise squared representative norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeInv.lean#L193).

**The full-period energy identity** · theorem. `period_identity`: The forcing-second-component inner product equals second-component energy plus one quarter of gradient energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeInv.lean#L200).

**Assemble the two graph components** · theorem. `exists_xx_of_halfSsp`: Compatible square-root Laplacian-related gradient and second-component curves define one graph-space L² curve. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeInv.lean#L239).

**The graph energy is bounded by forcing** · theorem. `le_inner_of_eq`: The identified graph components satisfy the energy inequality against the forcing-second-component inner product. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeInv.lean#L253).

**Lift an energy curve into graph space** · theorem. `second_of_curve`: The energy-curve data give a graph-space curve with the prescribed gradient inverse and the forcing-pairing energy bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeInv.lean#L261).

**Dense data admit bounded graph lifts** · theorem. `exists_dense_second`: A dense forcing subspace has graph lifts of the gradient inverse satisfying the forcing-pairing energy inequality. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeInv.lean#L282).

**The conditional choice is valid** · theorem. `spec_of_dite`: When a specification witness exists, the conditional chosen value satisfies that specification. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeInv.lean#L290).

**Transfer the extension's energy estimate** · theorem. `bound_transfer`: Identifying the relevant components transfers the quadratic energy bound from the constructed extension to the selected operator. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeInv.lean#L295).

**A free inverse with the energy bound** · theorem. `exists_freeInv_bound`: With the propagator bound, gradient-inverse formula and closed graph, a positive period admits a free inverse obeying the combined energy bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeInv.lean#L306).

**The selected free inverse has the bound** · theorem. `freeInv_of_bound`: With graph closedness, existence of a free inverse obeying the quadratic forcing bound transfers that bound to the selected free inverse. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeInv.lean#L312).

### Breakdown.Cert.FreePerturbation

The free inverse is read as a physical velocity field with weak derivatives. This file supplies the periodicity, integrability and perturbation conditions used by the nonlinear construction. §7.5: the free similarity equation

**Combine almost-everywhere slice laws** · theorem. `ae_prod_of_ae_ae`: Almost-everywhere slice agreement gives almost-everywhere agreement for time-space volume. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreePerturbation.lean#L14).

**Time-shifted curve representatives** · theorem. `shiftLp_ae`: The time-shift operator is represented almost everywhere by the corresponding translation of the time-circle argument. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreePerturbation.lean#L31).

**Rotated curve representatives** · theorem. `rotHH_ae`: The rotation operator is represented almost everywhere by applying the spatial rotation to each curve value. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreePerturbation.lean#L38).

**Read the gradient map on curve values** · theorem. `Breakdown.Cert.FreePerturbation.gradCLM_ae`: Almost everywhere on the time circle, the gradient-curve map is the gradient component of the original representative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreePerturbation.lean#L42).

**Circle translation preserves null sets** · theorem. `ae_add_circle`: An almost-everywhere time-circle property remains true after a fixed time translation. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreePerturbation.lean#L46).

**The gradient obeys the symmetry relation** · theorem. `shift_eq_rot`: The invariant graph curve's gradient has equal prescribed time-shift and spatial-rotation images. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreePerturbation.lean#L50).

**Symmetry of almost every circle slice** · theorem. `shift_slices_circle`: Almost every time-circle gradient slice transforms by the prescribed spatial rotation after the matching time shift. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreePerturbation.lean#L59).

**Symmetry of almost every real-time slice** · theorem. `shift_slices`: The gradient representatives satisfy the corresponding time-shift and rotation relation for almost every real time. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreePerturbation.lean#L67).

**The physical reading inherits symmetry** · theorem. `invariant_of_reading`: A physical velocity reading of invariant graph data obeys the prescribed space-time symmetry almost everywhere. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreePerturbation.lean#L74).

**The physical gradient is trace free** · theorem. `divergence_free_of_reading`: The physical gradient reading has zero trace almost everywhere in time and space. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreePerturbation.lean#L104).

**Almost every velocity slice lies in L⁶** · theorem. `sixth_power_of_reading`: The physical velocity reading has finite sixth-power spatial integral for almost every time. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreePerturbation.lean#L112).

**Finite periodic physical gradient energy** · theorem. `gradient_finite_of_reading`: The physical gradient reading has finite periodic matrix square integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreePerturbation.lean#L118).

**A circle representative returns** · theorem. `Breakdown.Cert.FreePerturbation.coe_circleRep`: Projecting the chosen real representative back to the time circle gives the original point. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreePerturbation.lean#L130).

**Identify a spatial L² representative** · theorem. `toLpOrZero_eq_of_ae`: The L²-or-zero conversion of an almost-everywhere representative of an L² field equals that field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreePerturbation.lean#L133).

**Identify a time-circle L² representative** · theorem. `circleLpOrZero_eq_of_ae`: The time-circle L²-or-zero conversion recovers the given curve from its almost-everywhere representative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreePerturbation.lean#L140).

**The full physical field gives forcing** · theorem. `physToHH_fullField`: The full physical field formed from the transport reading and Hessian converts to the original abstract forcing. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreePerturbation.lean#L147).

**The full-field test identity** · theorem. `integral_fullField`: The full-field test integral is the transport-field pairing plus the physical gradient pairing. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreePerturbation.lean#L164).

**The free inverse solves the weak PDE** · theorem. `weakEquation_of_reading`: The physical transport and gradient pairings of the free inverse equal the abstract forcing paired with the test. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreePerturbation.lean#L183).

### Breakdown.Cert.FreeTransport

The free inverse must satisfy the physical transport equation. This file exposes the transport property once the mild-propagator calculation and representative-reading results have been established. §7.5: the free similarity equation

**Separate transport from the full forcing** · theorem. `integral_inner_transportPart`: The transport-field pairing is the full-field pairing minus the gradient-test pairing. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransport.lean#L14).

**The physical weak transport identity** · theorem. `transport_of_reading`: The velocity paired with the adjoint similarity-transport test equals the transport-field pairing. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransport.lean#L34).

### Breakdown.Cert.FreeTransportCirclePairing

The propagator acts on time-circle curves while the equation is tested in real time. This file proves the periodic pairing and change-of-variable identities that connect those descriptions. §7.5: the free similarity equation

**A bounded compact-time slice pairing** · proposition definition. `IsSlicePairingBound`: The slice-pairing predicate records joint continuity, linearity in the field, a uniform norm bound and compact temporal support. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportCirclePairing.lean#L15).

**Integrate a whole number of periods** · theorem. `lintegral_Ioc_nat`: The nonnegative integral of a periodic lift over an integer number of periods is that integer times its circle integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportCirclePairing.lean#L20).

**Bound an interval by whole periods** · theorem. `lintegral_Icc_le`: The lifted nonnegative integral on a bounded interval is controlled by the displayed whole-period count times the circle integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportCirclePairing.lean#L34).

**An L¹ bound from the circle L² norm** · theorem. `lintegral_enorm_le`: The integral of the time-circle curve's norm is bounded by its L² norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportCirclePairing.lean#L43).

**The lifted curve is strongly measurable** · theorem. `stronglyMeasurable_coe`: The real-time lift of the time-circle L² representative is strongly measurable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportCirclePairing.lean#L57).

**Local integrability of the lifted norm** · theorem. `integrableOn_norm_coe`: The norm of the lifted curve is integrable on every bounded closed real interval. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportCirclePairing.lean#L61).

**Bound the lifted norm on an interval** · theorem. `integral_norm_coe_le`: The lifted norm integral over the interval is bounded by the whole-period count times the curve norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportCirclePairing.lean#L74).

**A test pairing with a lifted curve** · definition. `circlePairing`: The circle pairing integrates the time-dependent slice functional against the real-time lift of the curve. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportCirclePairing.lean#L85).

**Integrability of the circle pairing** · theorem. `integrable_pairing`: The compact-time support and slice norm bound make the lifted pairing integrable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportCirclePairing.lean#L90).

**The circle pairing is additive** · theorem. `circlePairing_add`: The lifted circle pairing of a sum equals the sum of its pairings. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportCirclePairing.lean#L101).

**The circle pairing respects scaling** · theorem. `circlePairing_smul`: The lifted circle pairing of a scalar multiple equals the scalar multiple of the pairing. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportCirclePairing.lean#L112).

**Bound the lifted circle pairing** · theorem. `abs_circlePairing_le`: The absolute circle pairing is bounded by the slice constant times the number of covering periods times the curve norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportCirclePairing.lean#L123).

**The lifted pairing is linear** · definition. `circlePairingCLM`: The bounded circle pairing is packaged as a continuous real linear functional on the forcing Hilbert space. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportCirclePairing.lean#L136).

**Evaluate the continuous circle pairing** · theorem. `circlePairingCLM_apply`: The continuous linear pairing map evaluates to the original lifted pairing integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportCirclePairing.lean#L143).

**The representative after time shift** · theorem. `shiftLp_apply_ae`: Almost everywhere, the shifted L² curve equals the original representative at the translated circle argument. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportCirclePairing.lean#L146).

**The propagator integrand by slices** · theorem. `propagatorIntegrand_apply_ae`: Almost everywhere, the propagator integrand is the slice propagator applied to the shifted forcing curve. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportCirclePairing.lean#L151).

**The real-time propagator integrand** · theorem. `coe_propagatorIntegrand_ae`: For almost every real time, the propagator integrand equals the propagated forcing at time delayed by elapsed time divided by period. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportCirclePairing.lean#L157).

**Shift a propagator pairing onto the test** · theorem. `circlePairing_propagatorIntegrand`: Pairing the propagator integrand shifts the elapsed-time translation from the forcing into the slice test functional. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportCirclePairing.lean#L172).

**Pair the inverse through its kernel** · theorem. `circlePairing_gradInv`: The gradient-inverse pairing is the elapsed-time integral of the shifted propagated slice pairings. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportCirclePairing.lean#L187).

**Measurability of shifted kernel pairings** · theorem. `stronglyMeasurable_shifted`: For fixed elapsed time, the shifted propagated slice-pairing function is strongly measurable in base time. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportCirclePairing.lean#L199).

**Continuity away from zero elapsed time** · theorem. `continuous_shifted_max`: Clamping elapsed time below a positive number makes the shifted propagated pairing continuous. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportCirclePairing.lean#L206).

**Measurability of the two-time kernel** · theorem. `aestronglyMeasurable_kernelPairing`: The shifted propagated pairing is jointly almost everywhere strongly measurable in positive elapsed time and base time. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportCirclePairing.lean#L216).

**An integrable kernel-pairing bound** · theorem. `lintegral_kernelPairing_le`: The base-time integral of the kernel pairing's norm is bounded by the propagator kernel and the forcing's circle norm integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportCirclePairing.lean#L244).

**The two-time pairing is integrable** · theorem. `integrable_kernelPairing`: The propagated pairing is integrable over positive elapsed times and all base times. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportCirclePairing.lean#L277).

**Exchange the two time integrals** · theorem. `integral_swap_kernelPairing`: The integrability bound permits exchanging the elapsed-time and base-time integrals of the propagated pairing. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/FreeTransportCirclePairing.lean#L294).
<!-- /passage:front -->

