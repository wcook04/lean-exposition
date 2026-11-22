
<!-- passage:front -->
# Library guide 8: Breakdown/CertCell

**Navier–Stokes pages:** [the paper](../navier-stokes-paper/paper.pdf) · [proof routes](../navier-stokes-routes/paper.md) · [routes in detail](../navier-stokes-route-details/paper.md) · library guide: [1](../navier-stokes-library-01/paper.md) [2](../navier-stokes-library-02/paper.md) [3](../navier-stokes-library-03/paper.md) [4](../navier-stokes-library-04/paper.md) [5](../navier-stokes-library-05/paper.md) [6](../navier-stokes-library-06/paper.md) [7](../navier-stokes-library-07/paper.md) **8** [9](../navier-stokes-library-09/paper.md) [10](../navier-stokes-library-10/paper.md) [11](../navier-stokes-library-11/paper.md) [12](../navier-stokes-library-12/paper.md) [13](../navier-stokes-library-13/paper.md) [14](../navier-stokes-library-14/paper.md) [15](../navier-stokes-library-15/paper.md) [16](../navier-stokes-library-16/paper.md) [17](../navier-stokes-library-17/paper.md) [18](../navier-stokes-library-18/paper.md) [19](../navier-stokes-library-19/paper.md) [20](../navier-stokes-library-20/paper.md) [21](../navier-stokes-library-21/paper.md) [22](../navier-stokes-library-22/paper.md) [23](../navier-stokes-library-23/paper.md) [24](../navier-stokes-library-24/paper.md) [25](../navier-stokes-library-25/paper.md) [26](../navier-stokes-library-26/paper.md) [27](../navier-stokes-library-27/paper.md) [28](../navier-stokes-library-28/paper.md) [29](../navier-stokes-library-29/paper.md) [30](../navier-stokes-library-30/paper.md)

*A plain title and a sentence for each declaration in `Breakdown.CertCell.ActuatorPairing` to `Breakdown.CertCell.AssemblyRowExpansionActuator` of Alpöge and Buckmaster's Lean at `ad53419de079eb8f95f60313473374624a348546`, in the authors' file order. Prepared with AI assistance. The authors have not reviewed it.*

Each paragraph names one declaration and says whether it is a definition, a proposition that the library defines (its name usually ends in `Holds` or `Statement`) or a proved result, then what it states. Click a paragraph to open its Lean on the right.

### Breakdown.CertCell.ActuatorPairing

This file closes the actuator pairing identity by combining the solenoidal test identity with approximation of an actuator by admissible solenoidal tests. Appendix B.3: support for actuator rows in the cell pairing stage.

**Equality from arbitrarily close pairs** · theorem. `eq_of_forall_close_equal_pair`: Two real numbers are equal if arbitrarily accurate approximations to them can be chosen equal. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairing.lean#L9).

**Assemble the actuator pairing identity** · theorem. `actuatorPairing_of_solenoidal_and_gradient`: The solenoidal pairing theorem and simultaneous approximation of the two actuator pairings imply the actuator-pairing interface. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairing.lean#L20).

### Breakdown.CertCell.ActuatorPairingDensity

This file extends the multiplier identity from smooth periodic tests to compactly supported C1 solenoidal fields by mollification and convergence of the mode sums. Appendix B.2–B.3: support for the multiplier and actuator pairing identities.

**Source namespace `Breakdown.CertCell.Internal.ActuatorPairingDensity`.**

**Space-time volume is Haar measure** · theorem. `prodVolume_addInvariant`: The product space-time volume is an additive Haar measure. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingDensity.lean#L23).

**Negation preserves space-time volume** · theorem. `prodVolume_isNegInvariant`: Space-time volume is invariant under negation. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingDensity.lean#L29).

**A sequence of shrinking smooth bumps** · definition. `bumpSeq`: The bump sequence uses positive inner and outer radii shrinking to zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingDensity.lean#L34).

**The normalized smoothing kernel** · definition. `kernel`: The smoothing kernel is the volume-normalized member of the shrinking bump sequence. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingDensity.lean#L40).

**Smooth a periodic vector field** · definition. `smoothed`: The smoothed field is the convolution of the normalized space-time kernel with the original field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingDensity.lean#L42).

**Extract a diagonal gradient coordinate** · definition. `componentMap`: The component map evaluates a matrix on a coordinate basis vector and then takes the matching coordinate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingDensity.lean#L45).

**Evaluate a diagonal coordinate map** · theorem. `componentMap_apply`: Applying the component map returns the specified diagonal entry of the linear map. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingDensity.lean#L48).

**The mollifier is nonnegative** · theorem. `kernel_nonneg`: Every smoothing kernel value is nonnegative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingDensity.lean#L50).

**The mollifier is integrable** · theorem. `kernel_integrable`: Each normalized smoothing kernel is integrable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingDensity.lean#L52).

**The mollifier has integral one** · theorem. `kernel_integral`: Each normalized smoothing kernel has full-space integral one. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingDensity.lean#L54).

**The mollifier is continuous** · theorem. `kernel_continuous`: Each smoothing kernel is continuous. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingDensity.lean#L56).

**Mollifier vanishes outside its support** · theorem. `kernel_eq_zero`: The kernel is zero beyond its prescribed outer support radius. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingDensity.lean#L59).

**The mollifier support shrinks to zero** · theorem. `rOut_tendsto`: The outer radii of the smoothing bumps tend to zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingDensity.lean#L71).

**Write smoothing as an averaged translate** · theorem. `smoothed_eq`: The convolution equals the integral of kernel-weighted backward space-time translates of the field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingDensity.lean#L74).

**Periodic compact data are bounded** · theorem. `exists_bound_of_periodic`: A continuous time-periodic field with uniformly bounded spatial support has one global norm bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingDensity.lean#L80).

**Weighted translated field is integrable** · theorem. `integrable_kernel_smul`: The kernel and field bounds make the kernel-weighted translated field integrable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingDensity.lean#L99).

**Averages preserve uniform norm bounds** · theorem. `norm_kernel_integral_le`: A uniform pointwise norm bound also bounds the norm of the normalized convolution average. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingDensity.lean#L107).

**C1 joint field has differentiable slices** · theorem. `slice_differentiableAt`: Every spatial time slice of the joint C1 field is differentiable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingDensity.lean#L116).

**Supplied spatial gradient is continuous** · theorem. `gradField_continuous`: The C1 and reading hypotheses make the spatial gradient jointly continuous. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingDensity.lean#L122).

**Differentiate the mollified field** · theorem. `smoothed_hasFDerivAt`: The derivative of the mollified field is the kernel average of the original spatial gradient. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingDensity.lean#L126).

**Mollification averages gradients** · theorem. `smoothed_fderiv`: The spatial derivative of the smoothed field equals convolution with the supplied gradient field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingDensity.lean#L150).

**Mollification makes the field smooth** · theorem. `smoothed_contDiff`: The mollified field is smooth jointly in time and space. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingDensity.lean#L155).

**Mollification preserves time periodicity** · theorem. `smoothed_periodic`: Smoothing a time-periodic field preserves its exact time periodicity. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingDensity.lean#L160).

**Smoothing enlarges support by one** · theorem. `smoothed_far`: A field supported within radius R has its smoothed version vanish outside radius R plus one. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingDensity.lean#L168).

**Mollification preserves zero divergence** · theorem. `smoothed_divergence`: The smoothed solenoidal field remains divergence free at every time and point. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingDensity.lean#L180).

**Smooth approximants are periodic tests** · theorem. `smoothed_testField`: The smoothed fields satisfy all periodic-test smoothness, support and divergence conditions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingDensity.lean#L202).

**Curl depends continuously on gradients** · theorem. `continuous_curlVec`: The map from a gradient matrix to its curl vector is continuous. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingDensity.lean#L210).

**The Hessian trace is continuous** · theorem. `Breakdown.CertCell.ActuatorPairingDensity.continuous_secondDerivTrace`: Taking the second-derivative trace is continuous as a map of bilinear operators. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingDensity.lean#L217).

**A gradient bound gives a curl bound** · theorem. `curlVec_bound`: A uniform bound on gradient matrices supplies one nonnegative bound on their curl vectors. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingDensity.lean#L221).

**Dominated errors vanish in period energy** · theorem. `periodLIntegral_tendsto_zero`: The stated pointwise convergence and common integrable bounds make the squared period error tend to zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingDensity.lean#L227).

**The smoothed fields converge pointwise** · theorem. `smoothed_tendsto`: Shrinking-kernel smoothing converges to the original continuous field at each point. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingDensity.lean#L259).

**Smoothed gradients converge pointwise** · theorem. `smoothed_fderiv_tendsto`: The smoothed spatial derivatives converge pointwise to the original continuous gradient. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingDensity.lean#L263).

**The combined signed curl weight** · definition. `epsWeight`: The epsilon weight adds the mode-sign-weighted spatial weights of all epsilon pieces. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingDensity.lean#L273).

**The combined signed velocity weight** · definition. `muWeight`: The mu weight adds the mode-sign-weighted spatial weights of all mu pieces. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingDensity.lean#L276).

**The curl of a smooth time field** · definition. `curlOf`: The curl field applies the curl map to the spatial derivative of each time slice. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingDensity.lean#L279).

**Curl from a supplied gradient field** · definition. `gradCurl`: The gradient-curl field applies the curl map directly to the supplied physical gradient. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingDensity.lean#L281).

**One mode's multiplier pairing** · definition. `modeIntegral`: The mode integral collects the epsilon curl pairings and mu velocity pairings for one harmonic mode over a time period. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingDensity.lean#L283).

**Split the multiplier pairing into modes** · theorem. `multiplierRight_eq`: The multiplier right-hand side is its negative Hessian-trace pairing plus the sum of all harmonic mode contributions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingDensity.lean#L291).

**Mode signs have magnitude at most one** · theorem. `abs_sgn_le`: Every piecewise mode sign has absolute value at most one. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingDensity.lean#L297).

**Source section `Weights`.**

**The curl weight has a uniform bound** · theorem. `epsWeight_abs_le`: The admissibility bounds control the combined signed epsilon weight by its prescribed supremum. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingDensity.lean#L306).

**The velocity weight has a uniform bound** · theorem. `muWeight_bound`: The finite admissible mu-piece family has one bound valid for every mode and spatial point. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingDensity.lean#L313).

**The curl weight is measurable** · theorem. `epsWeight_measurable`: The signed finite sum defining the epsilon weight is measurable in space. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingDensity.lean#L322).

**The velocity weight is measurable** · theorem. `muWeight_measurable`: The signed finite sum defining the mu weight is measurable in space. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingDensity.lean#L329).

**Source namespace `Breakdown.CertCell.Internal.ActuatorPairingDensity`.**

**Physical curl has finite period energy** · theorem. `gradCurl_square`: The perturbation gradient hypotheses make its curl a square-integrable periodic field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingDensity.lean#L338).

**Localize to finite period energy** · theorem. `ballPart_square`: Restricting the perturbation velocity to the specified ball gives a square-integrable periodic field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingDensity.lean#L348).

**Combine weighted mode real parts** · theorem. `re_sum_weight`: A finite sum of real parts with real weights equals the real part formed with the sum of those weights. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingDensity.lean#L356).

**Source section `ModeSums`.**

**Identify the two weighted mode pairings** · theorem. `modeIntegral_eq`: Each mode integral equals the weighted curl-mode pairing plus the weighted localized-velocity-mode pairing. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingDensity.lean#L368).

**Pass limits through multiplier sums** · theorem. `modeSum_tendsto`: The velocity and curl convergence hypotheses imply convergence of the full infinite sum of multiplier mode pairings. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingDensity.lean#L412).

**Source namespace `Breakdown.CertCell`.**

**Multiplier identity for solenoidal tests** · theorem. `multiplierField_pairing_of_solenoidal`: For admissible data, a compactly supported periodic C1 solenoidal field pairs with the multiplier field according to the required right-hand side. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingDensity.lean#L469).

### Breakdown.CertCell.ActuatorPairingGradient

This file approximates actuator pairings by solenoidal test pairings while preserving the multiplier expression. Appendix B.3: support for the actuator pairing stage.

**Source namespace `Breakdown.CertCell.Internal.ActuatorPairingGradient`.**

**A.e. equality preserves period pairings** · theorem. `iter_congr_ae`: Almost everywhere equality of the integrands preserves the iterated period-and-space integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingGradient.lean#L16).

**Scaled velocity has finite period energy** · theorem. `scaled_square`: The spatially scaled perturbation velocity is a square-integrable periodic field under the admissibility hypotheses. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingGradient.lean#L25).

**Supplied curl has finite period energy** · theorem. `curlG_square`: The curl of the perturbation gradient is a square-integrable periodic field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingGradient.lean#L37).

**Separate curl and velocity mode sums** · theorem. `pieceModeSum_split`: The piecewise multiplier mode sum splits into the finite sums of epsilon curl-mode and mu velocity-mode pairings. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingGradient.lean#L44).

**The excluded mu-mode terms vanish** · theorem. `mu_terms_zero`: The assumed mode exclusion makes the mu-weighted mode pairing sum zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingGradient.lean#L69).

**Source namespace `Breakdown.CertCell`.**

**Approximate both actuator pairings** · theorem. `multiplierField_pairing_gradient_part`: Every positive tolerance admits a compact periodic C1 solenoidal field approximating both the actuator-multiplier pairing and its multiplier right-hand side within that tolerance. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingGradient.lean#L92).

### Breakdown.CertCell.ActuatorPairingGradientDensity

This file constructs periodic solenoidal approximations of an actuator and controls their curl and Hessian-trace pairings. Appendix B.3: density support for the actuator pairing identity.

**Bound operator norm by column energy** · theorem. `opNorm_sq_le_columnSq`: The squared matrix operator norm is bounded by three times its matrix-column energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingGradientDensity.lean#L20).

**The actuator has finite period energy** · theorem. `actuator_square`: The actuator facts imply that the actuator is a square-integrable periodic field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingGradientDensity.lean#L31).

**The actuator gradient has finite energy** · theorem. `gradField_norm_sq_finite`: The squared norm of the actuator gradient has finite period integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingGradientDensity.lean#L34).

**Actuator gradient is locally integrable** · theorem. `gradField_locallyIntegrable`: The actuator-gradient energy bound gives local integrability in space-time. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingGradientDensity.lean#L46).

**Actuator curl has finite period energy** · theorem. `curl_actuator_square`: The curl of the actuator gradient is a square-integrable periodic field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingGradientDensity.lean#L56).

**The existing mollifier is a convolution** · theorem. `mollify_eq_conv`: The smooth-approximation mollifier equals convolution of its kernel with the joint field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingGradientDensity.lean#L75).

**Integrate a scalar bound over a period** · theorem. `periodLIntegral_le_const_mul`: Pointwise domination by a nonnegative constant multiple gives the corresponding period-integral bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingGradientDensity.lean#L81).

**Regularity of the mollified actuator** · theorem. `mollified_actuator`: The mollified actuator is C1, periodic, has finite field and gradient energies, and its derivative is the convolution of the original gradient. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingGradientDensity.lean#L91).

**The mollified actuator converges in L2** · theorem. `mollified_tendsto`: The period squared difference between the mollified actuator and the original tends to zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingGradientDensity.lean#L126).

**Mollified actuator curls converge in L2** · theorem. `mollified_curl_tendsto`: The period squared difference of the mollified and original actuator curls tends to zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingGradientDensity.lean#L131).

**Solenoidal tests approximate actuators** · theorem. `actuator_density`: There are periodic solenoidal tests converging in period L2 to the chosen solenoidal component and in curl energy to the actuator curl. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingGradientDensity.lean#L149).

**The Hessian trace preserves subtraction** · theorem. `secondTrace_sub`: The trace of a difference of Hessians is the difference of their traces. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingGradientDensity.lean#L210).

**The Hessian coefficients bound its trace** · theorem. `secondTrace_sq_le`: The squared Hessian-trace norm is bounded by three times the full squared coefficient energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingGradientDensity.lean#L214).

**The negative Hessian trace is continuous** · theorem. `continuous_negTrace`: Taking the negative trace is a continuous map on the Hessian operator space. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingGradientDensity.lean#L232).

**Negative trace has finite period energy** · theorem. `negTrace_square`: The perturbation's negative Hessian trace is a square-integrable periodic field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingGradientDensity.lean#L237).

**The negative trace is already solenoidal** · theorem. `negTrace_solenoidal_self`: The perturbation's negative Hessian trace is its own solenoidal component. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingGradientDensity.lean#L245).

### Breakdown.CertCell.ActuatorPairingGradientModes

This file proves that taking the solenoidal component preserves absent harmonic modes, using orbit averages and real and imaginary test pairings. Appendix B.3: harmonic support control for actuator approximation.

**Period L2 gives local integrability** · theorem. `locallyIntegrable_of_square`: A square-integrable periodic field is locally integrable on space-time. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingGradientModes.lean#L22).

**The cylindrical axis has zero volume** · theorem. `ae_off_axis`: Almost every spatial point has nonzero cylindrical radius. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingGradientModes.lean#L28).

**The space-time axis has measure zero** · theorem. `ae_off_axis_joint`: Almost every space-time point has spatial position off the cylindrical axis. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingGradientModes.lean#L44).

**The period slab is restricted volume** · theorem. `slab_eq_restrict`: The period slab measure equals space-time volume restricted to the unit time interval. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingGradientModes.lean#L48).

**The orbit slab is a product restriction** · theorem. `slab_prod_eq`: The product of the period slab and orbit measure is the corresponding restriction of the full product measure. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingGradientModes.lean#L51).

**The orbit slab measure is smaller** · theorem. `slab_prod_le`: The period-restricted orbit product measure is bounded by the unrestricted product measure. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingGradientModes.lean#L56).

**The localized orbit norm is integrable** · theorem. `integrable_orbit_norm`: The localized time-rotation orbit of a square-integrable field has integrable norm on the specified product domain. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingGradientModes.lean#L60).

**The rotated time orbit is measurable** · theorem. `aesm_orbit`: The time-shifted, spatially rotated field and inverse vector rotation give an almost everywhere strongly measurable orbit field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingGradientModes.lean#L90).

**The tested orbit pairing is integrable** · theorem. `integrable_orbit_pair`: The square-integrability and compact-test bounds make the field's orbit pairing integrable over one period and the orbit variables. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingGradientModes.lean#L102).

**A harmonic pairing is an orbit average** · theorem. `modeVel_pair_ae`: Almost everywhere, the complex mode paired with a real field is its exponential-weighted time-rotation orbit pairing average. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingGradientModes.lean#L141).

**Integrate the mode-pairing formula** · theorem. `modePair_eq`: The integrated mode pairing equals the exponential-weighted integral of the corresponding physical orbit pairings. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingGradientModes.lean#L179).

**Read the real vector coordinate** · theorem. `reVec_coord`: The real-vector coordinate is the real part of the corresponding complex coordinate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingGradientModes.lean#L210).

**Read the imaginary vector coordinate** · theorem. `imVec_coord`: The imaginary-vector coordinate is the imaginary part of the corresponding complex coordinate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingGradientModes.lean#L213).

**Real-vector pairings are real parts** · theorem. `inner_reVec`: Pairing the real part of a complex vector with a real vector gives the real part of their complex bilinear pairing. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingGradientModes.lean#L216).

**Imaginary pairings use imaginary parts** · theorem. `inner_imVec`: Pairing the imaginary part of a complex vector with a real vector gives the imaginary part of their complex bilinear pairing. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingGradientModes.lean#L222).

**The real part has no larger energy** · theorem. `norm_reVec_sq_le`: The squared norm of the real part is bounded by the full complex squared norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingGradientModes.lean#L228).

**The imaginary part has no larger energy** · theorem. `norm_imVec_sq_le`: The squared norm of the imaginary part is bounded by the full complex squared norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingGradientModes.lean#L236).

**Periodic compact test fields are bounded** · theorem. `exists_bound_periodic`: The periodic compact-support assumptions provide one global norm bound for the test field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingGradientModes.lean#L244).

**Harmonic projections remain periodic** · theorem. `modeVel_periodic`: The velocity harmonic mode of a periodic field is periodic in time. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingGradientModes.lean#L263).

**Real mode components are measurable** · theorem. `aesm_reVec_modeVel`: The real-vector part of the selected velocity mode is almost everywhere strongly measurable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingGradientModes.lean#L274).

**Imaginary mode components are measurable** · theorem. `aesm_imVec_modeVel`: The imaginary-vector part of the selected velocity mode is almost everywhere strongly measurable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingGradientModes.lean#L282).

**Each projected mode has finite energy** · theorem. `periodLIntegral_cnormSq_lt_top`: The selected velocity mode has finite period complex squared-norm integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingGradientModes.lean#L290).

**Pointwise bounds give period bounds** · theorem. `periodLIntegral_le_of`: Pointwise domination of the integrands gives the corresponding period-integral inequality. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingGradientModes.lean#L299).

**Take the real part after integration** · theorem. `re_pairing_eq`: The iterated period integral of a complex pairing's real part equals the real part of its slab integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingGradientModes.lean#L304).

**Integrate imaginary parts** · theorem. `im_pairing_eq`: The iterated period integral of a complex pairing's imaginary part equals the imaginary part of its slab integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingGradientModes.lean#L310).

**Projection preserves absent modes** · theorem. `solenoidalPart_modeVel_ae_zero`: If a field has zero selected mode and its solenoidal decomposition is respected by all time-rotation orbits, its solenoidal part has zero selected mode almost everywhere. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ActuatorPairingGradientModes.lean#L316).

### Breakdown.CertCell.AssemblyAllocationSplit

This file splits the global quadratic allocation into its finite cell contributions and the remaining harmonic-mode terms. Appendix B.3: support for summing the cell and exterior allocations.

**Source namespace `Breakdown.CertCell.Assembly.Internal.AllocationSplitParts`.**

**Split an absolute value into two signs** · theorem. `ofReal_abs_split`: The converted absolute value is the sum of the converted positive and negative values. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyAllocationSplit.lean#L19).

**Finite signed parts give integrability** · theorem. `integrable_of_parts`: A measurable real function is integrable when both its positive and negative nonnegative integrals are finite. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyAllocationSplit.lean#L24).

**Integrate by positive and negative parts** · theorem. `integral_eq_parts`: The ordinary real integral is the real value of the positive-part integral minus that of the negative-part integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyAllocationSplit.lean#L35).

**The cell rectangle is measurable** · theorem. `measurableSet_boxRect`: The closed rectangle underlying a cell box is measurable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyAllocationSplit.lean#L41).

**Cell lies in the cylindrical half-plane** · theorem. `boxRect_ae_le`: The cell rectangle lies in the physical half-plane up to a volume-null set. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyAllocationSplit.lean#L44).

**Combine signed infinite allocations** · theorem. `tsum_allocation`: The stated summability and allocation identities turn the four signed totals into a finite retained sum plus the remaining infinite sum. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyAllocationSplit.lean#L62).

**The allocation gap is measurable** · theorem. `aemeasurable_gap`: Measurable charges, weights and squared quantities give a measurable square-root expression for the allocation gap. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyAllocationSplit.lean#L101).

**Split a cylindrical average by sign** · theorem. `mean_split`: The radial-weighted real mean equals the difference of the positive and negative nonnegative orbit averages. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyAllocationSplit.lean#L120).

**The remaining density is the charge gap** · theorem. `density_sub_offMode`: Subtracting the off-mode density from the label density yields the explicitly allocated curl, gradient, velocity and mixed charge terms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyAllocationSplit.lean#L197).

**Source namespace `Breakdown.CertCell.Assembly`.**

**Regular data give the allocation split** · theorem. `allocationSplit_of_regular`: True-field regularity, mesh validity, regular charges, density measurability and finite pieces imply the allocation split. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyAllocationSplit.lean#L219).

**Establish the allocation-split interface** · theorem. `allocationSplitHolds`: The assembled analytic regularity results establish the allocation-split interface. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyAllocationSplit.lean#L304).

### Breakdown.CertCell.AssemblyAnnihilatorGradient

This file exports the result that a locally square-integrable field annihilating compact solenoidal tests is a gradient field. Appendix B.3: support for the pressure and annihilator decomposition.

**An annihilator is a gradient field** · theorem. `annihilatorGradient_holds`: The mollification, potential and closure arguments establish the annihilator-to-gradient interface. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyAnnihilatorGradient.lean#L8).

### Breakdown.CertCell.AssemblyAnnihilatorGradientBound

This file bounds the averaged line integrals used to construct a scalar potential for an annihilator field. Appendix B.3: support for the gradient-potential construction.

**The affine change-of-variables factor** · theorem. `lintegral_affine`: A nonzero spatial dilation and translation multiply the full nonnegative integral by the absolute inverse cube of the dilation. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyAnnihilatorGradientBound.lean#L10).

**Affine distortion costs a factor eight** · theorem. `lintegral_affine_le`: For the permitted dilation range, the transformed nonnegative integral is at most eight times the original. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyAnnihilatorGradientBound.lean#L18).

**Bound the average over line segments** · theorem. `key_bound`: The integral over endpoints, unit-ball base points and segment parameters is bounded by eight times the outer-ball volume times the full density integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyAnnihilatorGradientBound.lean#L31).

### Breakdown.CertCell.AssemblyAnnihilatorGradientClosure

This file passes scalar potentials of smooth approximations to a weak potential for the original locally square-integrable annihilator. Appendix B.3: support for closing the annihilator gradient argument.

**Cauchy-Schwarz for unnormalized averages** · theorem. `lintegral_sq_le`: The square of a nonnegative integral is at most the measure of the domain times the integral of its square. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyAnnihilatorGradientClosure.lean#L15).

**Segments stay in the outer region** · theorem. `region_bound`: The segment average over the outer ball is controlled by eight times its volume times the density integral over that ball. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyAnnihilatorGradientClosure.lean#L28).

**Measurability of the segment integrand** · theorem. `measurable_integrand`: A measurable field gives a strongly measurable field-position pairing along the averaging segments. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyAnnihilatorGradientClosure.lean#L50).

**The averaged potential is measurable** · theorem. `stronglyMeasurable_avgPotential`: The segment-averaged scalar potential is strongly measurable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyAnnihilatorGradientClosure.lean#L54).

**Bound distances between endpoints** · theorem. `norm_sub_le_of_mem`: Endpoints in the specified outer and unit balls are at distance at most the outer radius plus one. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyAnnihilatorGradientClosure.lean#L59).

**Bound averaged potential differences** · theorem. `enorm_avgPotential_sub_le`: The pointwise potential difference is bounded by the segment length bound times the averaged norm difference of the fields. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyAnnihilatorGradientClosure.lean#L65).

**The zero field gives zero potential** · theorem. `avgPotential_zero`: The segment-averaged potential of the zero vector field is identically zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyAnnihilatorGradientClosure.lean#L114).

**Bound the averaged potential pointwise** · theorem. `enorm_avgPotential_le`: The potential norm is bounded by the segment length bound times the averaged field norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyAnnihilatorGradientClosure.lean#L117).

**Measurability of segment averages** · theorem. `measurable_region_lintegral`: The nonnegative density averaged along segments depends measurably on the outer endpoint. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyAnnihilatorGradientClosure.lean#L124).

**L1 control of potential differences** · theorem. `lintegral_avgPotential_sub_le`: The local integral of a potential difference is bounded by the explicit geometric factor times the local field L1 difference. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyAnnihilatorGradientClosure.lean#L128).

**Control potential L2 by field L2** · theorem. `lintegral_avgPotential_sq_le`: The local potential squared integral is bounded by the segment-length and volume factors times the local field squared integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyAnnihilatorGradientClosure.lean#L147).

**A supported scalar product is integrable** · theorem. `integrable_mul_of_supp`: The compact-support and local integrability hypotheses make the scalar product integrable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyAnnihilatorGradientClosure.lean#L172).

**Bound a compactly weighted integral** · theorem. `enorm_integral_mul_le`: A uniform scalar test bound controls the weighted integral norm by that bound times the local field L1 norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyAnnihilatorGradientClosure.lean#L180).

**Continuity of the potential** · theorem. `continuous_avgPotential`: The segment-averaged potential of a continuous field is continuous. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyAnnihilatorGradientClosure.lean#L200).

**Continuous segment pairing is integrable** · theorem. `integrand_integrable_of_continuous`: A continuous field makes the potential's segment integrand integrable over the compact averaging domain. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyAnnihilatorGradientClosure.lean#L207).

**Differentiate the averaged potential** · theorem. `weak_identity`: The scalar-test integration identity identifies the weak gradient of the averaged potential with the field times the unit-ball volume. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyAnnihilatorGradientClosure.lean#L215).

**The original annihilator is a gradient** · theorem. `gradient_of_annihilator`: A measurable locally square-integrable field annihilating all smooth compact divergence-free tests is a gradient field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyAnnihilatorGradientClosure.lean#L324).

### Breakdown.CertCell.AssemblyAnnihilatorGradientMollify

This file mollifies an annihilator and proves that each smoothed field has symmetric derivative, enabling a scalar potential. Appendix B.3: support for the annihilator gradient construction.

**Commute scalar multiplication** · definition. `smulFlip`: The flipped continuous bilinear map lets convolution multiply a vector field value by a scalar kernel value. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyAnnihilatorGradientMollify.lean#L10).

**Mollify a spatial annihilator field** · definition. `mollify`: The mollified field is convolution of the vector field with the scalar kernel through flipped scalar multiplication. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyAnnihilatorGradientMollify.lean#L12).

**Reconstruct a vector from coordinates** · theorem. `sum_coord`: The coordinate-weighted sum of standard basis vectors is the original vector. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyAnnihilatorGradientMollify.lean#L14).

**Evaluate a functional by basis values** · theorem. `clm_sum_coord`: A scalar linear functional applied to a vector is the coordinate-weighted sum of its basis values. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyAnnihilatorGradientMollify.lean#L18).

**A compact antisymmetric derivative test** · theorem. `stationary_pair`: The difference of the two kernel-derivative directions is a smooth compactly supported divergence-free test field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyAnnihilatorGradientMollify.lean#L22).

**The mollified annihilator is smooth** · theorem. `mollify_contDiff`: Convolving with the smooth compact kernel gives a smooth vector field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyAnnihilatorGradientMollify.lean#L59).

**The mollified derivative is symmetric** · theorem. `mollify_symm`: Annihilation of compact divergence-free tests forces the derivative of the mollified field to have symmetric pairings. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyAnnihilatorGradientMollify.lean#L63).

**Mollifiers approximate the local field** · theorem. `approx_mollify`: For every positive tolerance and local ball, a smooth compact kernel gives a mollified field within that local L1 tolerance. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyAnnihilatorGradientMollify.lean#L93).

### Breakdown.CertCell.AssemblyAnnihilatorGradientPotential

This file constructs scalar potentials for smooth vector fields with symmetric derivative, first from the origin and then by averaging over base points. Appendix B.3: support for the annihilator gradient construction.

**The potential integrated from the origin** · definition. `radialPotential`: The radial potential integrates the field along the straight segment from the origin to the point. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyAnnihilatorGradientPotential.lean#L9).

**Derivative of the radial integrand** · definition. `radialDeriv`: The radial derivative combines the field derivative along the segment with the direct field contribution to the position pairing. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyAnnihilatorGradientPotential.lean#L12).

**Differentiate the radial line pairing** · theorem. `hasFDerivAt_radial_integrand`: The derivative of the radial field-position pairing is the specified continuous linear radial-derivative map. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyAnnihilatorGradientPotential.lean#L15).

**Radial derivative varies continuously** · theorem. `continuous_radialDeriv`: For the smooth field, the radial derivative is continuous in the segment parameter. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyAnnihilatorGradientPotential.lean#L26).

**A symmetric derivative gives a potential** · theorem. `hasFDerivAt_radialPotential`: For a smooth field with symmetric derivative, the radial potential has derivative equal to pairing with the field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyAnnihilatorGradientPotential.lean#L34).

**The radial potential is continuous** · theorem. `continuous_radialPotential`: The radial potential of the permitted continuous field is continuous. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyAnnihilatorGradientPotential.lean#L104).

**Potential differences are line integrals** · theorem. `radialPotential_shift`: The line integral between two base points equals the difference of their radial potential values. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyAnnihilatorGradientPotential.lean#L109).

**The potential averaged over a unit ball** · definition. `avgPotential`: The averaged potential integrates line pairings from all base points in the unit ball to the target point. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyAnnihilatorGradientPotential.lean#L133).

**Averaged potential fixes the constant** · theorem. `avgPotential_eq`: The averaged potential is unit-ball volume times the radial potential minus the radial potential's unit-ball integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyAnnihilatorGradientPotential.lean#L136).

**A compact scalar product is integrable** · theorem. `integrable_mul_of_support`: The stated continuity and compact-support assumptions make the scalar product integrable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyAnnihilatorGradientPotential.lean#L158).

**The averaged potential's weak derivative** · theorem. `avgPotential_weak`: Testing the averaged potential's derivative gives the field pairing multiplied by the unit-ball volume and the integration-by-parts sign. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyAnnihilatorGradientPotential.lean#L162).

### Breakdown.CertCell.AssemblyBandIntegrable

This file supplies integrability of the twelve-component band profile used by cell elimination. Appendix B.3: support for band-mode quadratic forms.

**Source namespace `Breakdown.CertCell.Assembly.Internal.BandIntegrable`.**

**The packed profile norm splits** · theorem. `pairVec_sq`: The squared norm of the packed twelve-component profile is the gradient-column energy plus velocity energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyBandIntegrable.lean#L20).

**Measurable packed profile coordinates** · theorem. `pairVec_meas`: Measurable gradient and velocity components give measurable coordinates of the packed band profile. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyBandIntegrable.lean#L25).

**Source namespace `Breakdown.CertCell.Assembly`.**

**Weighted integrability of band profiles** · theorem. `bandProfileIntegrable_holds`: The field regularity and component energy facts establish the band-profile integrability interface. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyBandIntegrable.lean#L36).

### Breakdown.CertCell.AssemblyBandTurned

This file expresses azimuthal derivatives of a harmonic field in the cylindrical frame, providing the relations used to eliminate velocity components. Appendix B.3: support for turned band profiles.

**Source namespace `Breakdown.CertCell.Assembly.TurnedProfile`.**

**Cylindrical angular derivatives** · theorem. `angular_local`: Almost everywhere at positive radius, the three angular-gradient components satisfy the azimuthal-frequency relations with the cylindrical-frame velocity components. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyBandTurned.lean#L21).

**Zero cylindrical radius is negligible** · theorem. `fst_ne_zero_ae`: Almost every point of the radial-height plane has nonzero radial coordinate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyBandTurned.lean#L71).

**Source namespace `Breakdown.CertCell.Assembly`.**

**Band profiles obey turning relations** · theorem. `bandProfileTurned_holds`: The local angular identities establish the turned-band profile interface. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyBandTurned.lean#L84).

### Breakdown.CertCell.AssemblyCellRange

This file tracks how changing the scalar-potential gauge affects cell moments and places the physical data in the permitted cell row range. Appendix B.3: support for pressure gauges and true cell data.

**Closed cell rectangles are compact** · theorem. `rect_compact'`: A product of two closed bounded intervals is compact. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyCellRange.lean#L16).

**Continuous weights preserve cell L1** · theorem. `cont_mul_int`: The stated continuous bounded cell weight times the integrable complex field is integrable on the cell set. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyCellRange.lean#L19).

**The pressure mode of one is constant** · theorem. `presMode_one_const`: Every harmonic pressure mode of the constant unit potential is independent of the spatial point. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyCellRange.lean#L23).

**The constant pressure mode is integrable** · theorem. `presMode_one_int`: The pressure mode of the unit potential is integrable on the stated finite-measure cell set. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyCellRange.lean#L28).

**Remove a positive radial weight from L1** · theorem. `int_of_weighted`: On a cell bounded away from the axis, integrability with the radial weight implies ordinary integrability. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyCellRange.lean#L33).

**Integrability of radial strip moments** · theorem. `radial_grad_int`: The weighted derivative term in the radial strip moment is integrable under the stated rectangle and derivative hypotheses. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyCellRange.lean#L45).

**Shift a potential by a constant** · theorem. `integral_shift`: The pointwise shifted-integrand relation passes to the corresponding integral plus the constant times the unit moment. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyCellRange.lean#L63).

**Gauge shifts of radial moments** · theorem. `radial_shift`: Shifting the potential by a constant changes the radial strip moment by that constant times the unit-potential radial moment. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyCellRange.lean#L68).

**Gauge shifts of height moments** · theorem. `height_shift`: Shifting the potential by a constant changes the height strip moment by that constant times the unit-potential height moment. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyCellRange.lean#L91).

**Pressure modes track gauge changes** · theorem. `potential_shift_ae`: Almost everywhere, changing the scalar-potential gauge adds the gauge difference times the harmonic mode of the unit potential. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyCellRange.lean#L117).

**All boundary moments track the gauge** · theorem. `moment_shift`: The combined cell moment changes by the gauge difference times its unit-pressure moment. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyCellRange.lean#L132).

**The difference between the two gauges** · definition. `ballGaugeGap`: The gauge gap is the unit-ball mean of the physical potential minus the real part of the cell's normalized gauge value. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyCellRange.lean#L163).

**True data equal head plus gauge** · theorem. `trueData_eq_head`: The true cell data equal the head data plus the gauge gap times the unit-pressure moment. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyCellRange.lean#L166).

### Breakdown.CertCell.AssemblyCrossWaveTraceFree

This file states the trace-free cross-wave stretching estimate and defines the quadratic charge used to pay for it. Appendix B.2–B.3: support for the sharp stretching charges.

**The charge assigned to one wave class** · definition. `classCharge`: The class charge combines curl energy with length-weighted gradient and velocity energies. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyCrossWaveTraceFree.lean#L11).

**The trace-free cross-wave bound** · interface proposition. `CrossWaveTraceFreeBoundHolds`: The interface asks that operator bounds and zero curl-gradient trace control the resonant cross-wave sum by two weighted class charges using the square-root-seven-halves constant. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyCrossWaveTraceFree.lean#L14).

Proved by `Breakdown.CertCell.Bridge.crossWaveTraceFreeBound`.

### Breakdown.CertCell.AssemblyCrossWaveTraceFreeProof

This file proves the trace-free cross-wave estimate by averaging finite Fourier sums on a sufficiently fine grid and applying the pointwise bound. Appendix B.2–B.3: support for the sharp stretching estimate.

**Nonnegative complex coefficient energy** · lemma. `gridCnormSq_nonneg`: The sum of squared complex coordinate norms is nonnegative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyCrossWaveTraceFreeProof.lean#L11).

**A discrete Fourier phase** · definition. `phaseOnGrid`: The grid phase is the complex exponential for the integer frequency at the chosen uniform grid point. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyCrossWaveTraceFreeProof.lean#L14).

**Grid phases add frequencies** · lemma. `phaseOnGrid_mul`: Multiplying two grid phases gives the phase at the sum of their frequencies. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyCrossWaveTraceFreeProof.lean#L17).

**Conjugation negates the grid frequency** · lemma. `phaseOnGrid_conj`: The conjugate of a grid phase is the phase with the negated frequency. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyCrossWaveTraceFreeProof.lean#L25).

**Discrete Fourier orthogonality** · lemma. `phaseOnGrid_sum`: Within the stated nonaliasing frequency range, summing a grid phase gives the grid size at zero frequency and zero otherwise. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyCrossWaveTraceFreeProof.lean#L33).

**Read azimuthal phases on the grid** · lemma. `azimuthPhase_onGrid`: At the chosen azimuthally scaled grid points, the azimuthal phase equals the discrete Fourier phase. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyCrossWaveTraceFreeProof.lean#L78).

**Curl is additive in its gradient** · lemma. `tfCurlOfGrad_add`: The curl of a sum of gradient arrays is the sum of their curls. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyCrossWaveTraceFreeProof.lean#L87).

**Curl respects complex scaling** · lemma. `tfCurlOfGrad_smul`: Scaling the gradient array scales its curl by the same complex scalar. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyCrossWaveTraceFreeProof.lean#L91).

**The curl gradient is additive** · lemma. `tfCurlGrad_add`: The curl-gradient map preserves sums of Hessian arrays. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyCrossWaveTraceFreeProof.lean#L96).

**The curl gradient respects scaling** · lemma. `tfCurlGrad_smul`: Scaling a Hessian array scales its curl gradient by the same complex scalar. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyCrossWaveTraceFreeProof.lean#L100).

**Stretching is additive in the model** · lemma. `tfBilin_add_model`: Adding two model gradient-Hessian pairs adds their stretching bilinear forms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyCrossWaveTraceFreeProof.lean#L105).

**Stretching scales with the model** · lemma. `tfBilin_smul_model`: Scaling the model gradient-Hessian pair scales its stretching bilinear form. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyCrossWaveTraceFreeProof.lean#L112).

**Add the first stretching field** · lemma. `tfBilin_add_left`: Adding the first velocity-gradient pairs adds their stretching bilinear contributions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyCrossWaveTraceFreeProof.lean#L119).

**Stretching scales with the first field** · lemma. `tfBilin_smul_left`: Scaling the first velocity-gradient pair scales the stretching bilinear form. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyCrossWaveTraceFreeProof.lean#L126).

**Add the second stretching field** · lemma. `tfBilin_add_right`: Adding the second velocity-gradient pairs adds their stretching bilinear contributions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyCrossWaveTraceFreeProof.lean#L133).

**Stretching scales with the second field** · lemma. `tfBilin_smul_right`: Scaling the second velocity-gradient pair scales the stretching bilinear form. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyCrossWaveTraceFreeProof.lean#L140).

**Take curl through a weighted finite sum** · lemma. `tfCurlOfGrad_sum`: The curl of a finite weighted gradient sum is the corresponding weighted sum of curls. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyCrossWaveTraceFreeProof.lean#L147).

**Take curl gradient through a finite sum** · lemma. `tfCurlGrad_sum`: The curl gradient of a finite weighted Hessian sum is the corresponding weighted sum of curl gradients. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyCrossWaveTraceFreeProof.lean#L154).

**Curl commutes with conjugation** · lemma. `tfCurlOfGrad_star`: The curl of the conjugated gradient array equals the conjugated curl. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyCrossWaveTraceFreeProof.lean#L162).

**Conjugation preserves coefficient energy** · lemma. `tfCnormSq_star`: Conjugation leaves the complex squared coordinate norm unchanged. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyCrossWaveTraceFreeProof.lean#L166).

**Coefficient energy as a complex sum** · lemma. `tfCnormSq_ofReal`: The real coefficient energy embedded in the complex numbers equals the sum of each coordinate times its conjugate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyCrossWaveTraceFreeProof.lean#L169).

**Discrete Parseval in complex form** · lemma. `gridMeanSqComplex`: Under the frequency separation conditions, the grid sum of products of Fourier sums equals the grid size times the sum of coefficient energies. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyCrossWaveTraceFreeProof.lean#L173).

**Discrete Parseval for squared norms** · lemma. `gridMeanSq`: Under the nonaliasing conditions, the summed squared Fourier norms on the grid equal the grid size times the summed coefficient squared norms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyCrossWaveTraceFreeProof.lean#L209).

**The model slot as a linear functional** · definition. `tfModelMap`: With the two perturbation slots fixed, stretching is a complex linear functional of the model gradient-Hessian pair. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyCrossWaveTraceFreeProof.lean#L220).

**First field slot as a linear functional** · definition. `tfLeftMap`: With the model and second field fixed, stretching is a complex linear functional of the first velocity-gradient pair. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyCrossWaveTraceFreeProof.lean#L231).

**Second field slot as a linear functional** · definition. `tfRightMap`: With the model and first field fixed, stretching is a complex linear functional of the second velocity-gradient pair. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyCrossWaveTraceFreeProof.lean#L242).

**Expand all three stretching slots** · lemma. `tfTriple_expand`: Stretching of three finite linear combinations expands into the weighted triple sum of their individual contributions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyCrossWaveTraceFreeProof.lean#L253).

**The grid average selects resonances** · lemma. `gridMeanTriple`: With sufficiently separated grid frequencies, the averaged triple Fourier stretching sum retains exactly terms whose two input frequencies sum to the output frequency. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyCrossWaveTraceFreeProof.lean#L275).

**Parseval for the quadratic class charge** · lemma. `gridMeanClassCharge`: The grid sum of class charges equals the grid size times the sum of the individual mode charges under the frequency separation assumptions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyCrossWaveTraceFreeProof.lean#L301).

**Balance a product with a positive weight** · lemma. `tfTwice_mul_le`: Twice a product is bounded by a positive weighted square plus its reciprocal-weighted square. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyCrossWaveTraceFreeProof.lean#L330).

**Balance two stretching pairings** · lemma. `tfWeightedPair`: The weighted product estimates bound the two-way stretching expression by the two scaled quadratic class energies. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyCrossWaveTraceFreeProof.lean#L337).

**Class charge is unchanged by conjugation** · lemma. `classCharge_star`: Conjugating both velocity and gradient coefficients leaves the class charge unchanged. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyCrossWaveTraceFreeProof.lean#L352).

**Pass the pointwise bound to the average** · lemma. `tfMeanCombine`: The grid norm and charge identities turn the summed pointwise estimate into the weighted bound for the averaged interaction. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyCrossWaveTraceFreeProof.lean#L357).

**Prove the trace-free cross-wave estimate** · theorem. `crossWaveTraceFreeBound`: Discrete Fourier orthogonality and the sharp pointwise trace-free estimate establish the cross-wave bound interface. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyCrossWaveTraceFreeProof.lean#L375).

### Breakdown.CertCell.AssemblyCrossWaveTraceFreeProofPointwise

This file proves the pointwise trace-free stretching bound with the square-root-seven-halves coefficient used by the cross-wave estimate. Appendix B.2–B.3: support for the sharp stretching constant.

**Complex squared norms are nonnegative** · lemma. `tfCnormSq_nonneg`: The finite complex squared coordinate norm is nonnegative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyCrossWaveTraceFreeProofPointwise.lean#L11).

**Cauchy-Schwarz for complex sums** · lemma. `tfNorm_sum_mul_le`: The norm of a coordinatewise complex product sum is bounded by the product of the two Euclidean coefficient norms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyCrossWaveTraceFreeProofPointwise.lean#L14).

**Take roots of a quadratic operator bound** · lemma. `tfSqrt_le`: The nonnegative squared estimate implies the corresponding square-root bound with the operator coefficient. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyCrossWaveTraceFreeProofPointwise.lean#L20).

**Expand the energy of a complex sum** · lemma. `tfCnormSq_add`: The complex squared norm of a sum is the two separate energies plus twice the real conjugate cross pairing. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyCrossWaveTraceFreeProofPointwise.lean#L25).

**The antisymmetric curl coefficients** · definition. `rotCoeff`: The rotational coefficient array is the alternating-symbol contraction of a vector. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyCrossWaveTraceFreeProofPointwise.lean#L34).

**The cross-product coefficient array** · definition. `crossVec`: The cross-vector coefficients encode the alternating-symbol contraction with the velocity vector. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyCrossWaveTraceFreeProofPointwise.lean#L37).

**The mixed curl-gradient coefficients** · definition. `spinCoeff`: The spin coefficient contracts the curl-gradient matrix with the cross-vector array, with factor one half. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyCrossWaveTraceFreeProofPointwise.lean#L40).

**The mixed stretching pairing** · definition. `pairForm`: The pointwise pair form combines the matrix-applied velocity paired with curl and its alternating-symbol correction. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyCrossWaveTraceFreeProofPointwise.lean#L43).

**The pairing is a coefficient contraction** · lemma. `pairForm_eq`: The mixed pair form is the contraction of the gradient with the sum of rotational and spin coefficient arrays. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyCrossWaveTraceFreeProofPointwise.lean#L48).

**Energy of the rotational coefficients** · lemma. `rotCoeff_cnormSq`: The rotational coefficient energy is twice the original vector energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyCrossWaveTraceFreeProofPointwise.lean#L54).

**Energy of the cross-product coefficients** · lemma. `crossVec_cnormSq`: Summing the cross-vector coefficient energies gives twice the velocity energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyCrossWaveTraceFreeProofPointwise.lean#L59).

**Bound the spin coefficient energy** · lemma. `spinCoeff_cnormSq_le`: The matrix operator bound controls the spin coefficient energy by half its squared bound times the velocity energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyCrossWaveTraceFreeProofPointwise.lean#L64).

**The rotation-spin contraction identity** · lemma. `rot_spin_contract`: The explicit contraction splits into a matrix-applied vector term and a trace term. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyCrossWaveTraceFreeProofPointwise.lean#L81).

**Conjugate the spin coefficients** · lemma. `spinCoeff_conj`: Conjugating the spin coefficients conjugates the matrix and velocity entries in their defining expression. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyCrossWaveTraceFreeProofPointwise.lean#L89).

**Bound a half-weighted real part** · lemma. `half_re_le`: Twice the real part of a complex number multiplied by one half is at most its norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyCrossWaveTraceFreeProofPointwise.lean#L94).

**Control the rotation-spin cross term** · lemma. `cross_term_le`: Under the trace-free matrix bound, the rotation-spin cross term is controlled by the matrix bound and the relevant vector norms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyCrossWaveTraceFreeProofPointwise.lean#L100).

**The sharp mixed-pairing bound** · lemma. `pairForm_bound`: A trace-free matrix with the stated operator bound controls the mixed pairing by square root of seven halves times that bound and the two input norms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyCrossWaveTraceFreeProofPointwise.lean#L135).

**The strain bound controls curl pairings** · lemma. `symPart_bound`: The symmetric-gradient operator bound controls the two-curl pairing by that bound times the two curl norms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyCrossWaveTraceFreeProofPointwise.lean#L163).

**Bound the four-term stretching expansion** · lemma. `norm_four_le`: The norm of the signed four-term sum is at most the sum of the four term norms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyCrossWaveTraceFreeProofPointwise.lean#L180).

**Pointwise trace-free stretching bound** · theorem. `traceFreeTripleBound`: The strain and trace-free curl-gradient bounds control the stretching triple by its curl product and the two velocity-gradient products with the sharp coefficient. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyCrossWaveTraceFreeProofPointwise.lean#L186).

### Breakdown.CertCell.AssemblyEliminationStage

This file eliminates band-mode velocity variables through the angular relations and proves the resulting quadratic bound by completing squares. Appendix B.3: support for cell band elimination.

**Source namespace `Breakdown.CertCell.Assembly.TurnedBand`.**

**Split gradient and velocity coordinates** · theorem. `sum_twelve_split`: A sum over the twelve profile coordinates splits into nine gradient coordinates and three velocity coordinates. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyEliminationStage.lean#L18).

**Group the nine gradient coordinates** · theorem. `sum_nine_split`: A sum over the nine gradient coordinates splits into the three coordinate rows. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyEliminationStage.lean#L22).

**The angular turning determinant** · theorem. `turnMatrix_det`: The turning matrix determinant is i times the azimuthal frequency times one minus its square. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyEliminationStage.lean#L29).

**Nonexceptional modes can be turned** · theorem. `turnMatrix_det_isUnit`: Away from the exceptional frequencies zero and plus or minus one, the turning matrix determinant is a unit. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyEliminationStage.lean#L36).

**Recover velocity from angular gradients** · theorem. `turned_velocity`: For a nonexceptional mode, the angular relations recover velocity coordinates by the inverse turning matrix applied to radial-weighted angular derivatives. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyEliminationStage.lean#L45).

**Expand the transformed gradient pairing** · theorem. `turned_extra`: Pairing with the turned gradient vector expands into the original gradient pairing plus the inverse-matrix velocity correction. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyEliminationStage.lean#L59).

**Eliminate velocity from a full pairing** · theorem. `turned_dot`: A twelve-coordinate pairing with a profile satisfying the turning relations equals the nine-coordinate pairing with its turned test vector. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyEliminationStage.lean#L77).

**The reversed turned pairing identity** · theorem. `turned_dot_right`: The same elimination identity holds when the profile coordinates appear first in the complex products. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyEliminationStage.lean#L90).

**Discarding velocity terms lowers energy** · theorem. `weight_split_le`: For nonnegative coordinate weights, the nine-gradient weighted energy is bounded by the full twelve-coordinate energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyEliminationStage.lean#L99).

**Source namespace `Breakdown.CertCell.Assembly.TurnedBand.Internal`.**

**Complete the positive quadratic square** · theorem. `cross_le`: A Hermitian positive-definite quadratic form bounds the linear-minus-quadratic expression by its inverse-weighted square. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyEliminationStage.lean#L112).

**Realize the inverse quadratic bound** · theorem. `le_exists`: Under the positive-definite hypotheses, some vector realizes a value at least the inverse-weighted square in the completed-square expression. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyEliminationStage.lean#L132).

**A finite cylindrical half-plane region** · structure. `IsHalfBox`: A half-box is measurable, has finite volume and has nonnegative radial coordinate bounded above. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyEliminationStage.lean#L149).

**Weighted square integrability on a cell** · proposition definition. `Wsq`: The weighted-square predicate requires measurability and integrability of radial coordinate times the function norm squared. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyEliminationStage.lean#L155).

**Weighted L2 for bounded fields** · theorem. `wsq_of_bounded`: On a finite half-box, a bounded measurable function satisfies the weighted-square predicate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyEliminationStage.lean#L160).

**Weighted L2 factors have an L1 product** · theorem. `integrable_mul`: Two weighted-square functions have an integrable radial-weighted complex product. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyEliminationStage.lean#L173).

**Weighted L2 is closed under addition** · theorem. `wsq_add`: The sum of two weighted-square functions again satisfies the weighted-square predicate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyEliminationStage.lean#L183).

**Scaling preserves weighted L2** · theorem. `wsq_const_mul`: Multiplying a weighted-square function by a complex constant preserves the property. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyEliminationStage.lean#L197).

**Bounded radial factors preserve L2** · theorem. `wsq_fst_mul`: On the bounded half-box, multiplying by the radial coordinate preserves weighted-square integrability. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyEliminationStage.lean#L203).

**Conjugation preserves weighted L2** · theorem. `wsq_conj`: Conjugating a weighted-square function preserves its weighted-square integrability. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyEliminationStage.lean#L218).

**The zero function has weighted L2 energy** · theorem. `wsq_zero`: The zero function satisfies the weighted-square predicate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyEliminationStage.lean#L223).

**Finite sums preserve weighted L2** · theorem. `wsq_sum`: A finite sum of weighted-square functions remains weighted-square integrable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyEliminationStage.lean#L225).

**Almost equality preserves weighted L2** · theorem. `wsq_congr`: A function almost everywhere equal to a weighted-square function has the same integrability property. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyEliminationStage.lean#L234).

**Move a finite pairing into the integral** · theorem. `dot_sum_integral`: The integrability hypotheses permit a fixed complex vector pairing to pass through the finite sum of cell integrals. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyEliminationStage.lean#L239).

**Move coefficients into cell integrals** · theorem. `sum_integral_mul`: Finite coefficients can be moved inside the finite sum and cell integrals under the stated integrability conditions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyEliminationStage.lean#L248).

**Real parts commute with cell integrals** · theorem. `re_sum_integral`: The real part of a finite sum of integrals equals the sum of the integrals of the real parts. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyEliminationStage.lean#L257).

**Integrate the completed-square expansion** · theorem. `integral_combine`: The seven-term integrable expression integrates to the corresponding signed and scalar-weighted combination of integrals. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyEliminationStage.lean#L263).

**Completed scalar square is nonnegative** · theorem. `square_completion`: For positive quadratic weight, the two-coordinate quadratic expression plus its reciprocal-weighted correction is nonnegative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyEliminationStage.lean#L284).

**Finite weighted products are integrable** · theorem. `integrable_sum`: A finite sum of products of weighted-square functions is integrable after multiplication by the radial coordinate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyEliminationStage.lean#L317).

**Fixed division preserves integrability** · theorem. `integrable_sum_div`: The same finite weighted products remain integrable after division by the given constant coefficients. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyEliminationStage.lean#L324).

**Integrability from a complex product** · theorem. `integrableOn_scaled_re`: The stated nonzero scaling and complex-integrability hypotheses imply integrability of the real density. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyEliminationStage.lean#L334).

**Each cell rectangle is a half-box** · theorem. `rect_halfBox`: A valid cell mesh gives each cell rectangle the finite measurable half-box properties. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyEliminationStage.lean#L340).

**Turning preserves weighted L2** · theorem. `wsq_turned`: For nonexceptional modes, the turned test vector retains weighted-square integrability on the half-box. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyEliminationStage.lean#L347).

**Source namespace `Breakdown.CertCell.Assembly.TurnedBand`.**

**Eliminated band has the required bound** · theorem. `band_bound`: The band elimination value is bounded by the band quadratic and linear forms together with the row pairings and slack-adjusted Gram term. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyEliminationStage.lean#L364).

### Breakdown.CertCell.AssemblyExteriorNonneg

This file combines the exterior off-mode inequality with the assigned stretching charges to prove nonnegativity of the exterior contribution. Appendix B.3: support for the exterior part of the global cell form.

**Source namespace `Breakdown.CertCell.Assembly.Internal.ExteriorNonneg`.**

**Balance the signed differences** · theorem. `ofReal_balance`: The positive and negative parts of two real numbers and their difference satisfy the stated exact balance. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyExteriorNonneg.lean#L19).

**One mode's signed integral balance** · theorem. `mode_step`: The nonnegative difference hypothesis yields the comparison of the positive and negative integrals for one mode. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyExteriorNonneg.lean#L37).

**Sum the signed mode balances** · theorem. `total_step`: The modewise balances and finite total terms combine into the inequality between the two full signed sums. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyExteriorNonneg.lean#L74).

**Equal coercivity leaves data unchanged** · theorem. `formNeg_eq_withCoercivity`: Replacing the form coercivity by its existing value leaves the negative form unchanged. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyExteriorNonneg.lean#L94).

**The exterior charge allocation gap** · definition. `chargeGap`: The charge gap combines assigned curl, gradient and velocity energies with the mixed gradient-velocity charge. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyExteriorNonneg.lean#L105).

**Exterior density equals the charge gap** · theorem. `chargeDensity_eq`: The exterior charge density is exactly the charge-gap expression evaluated on the exterior charges and physical modes. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyExteriorNonneg.lean#L115).

**The density with charges removed** · theorem. `offMode_eq`: The radial-weighted label density minus the exterior charge density equals the radial-weighted off-mode density. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyExteriorNonneg.lean#L124).

**The exterior charge gap is measurable** · theorem. `aemeasurable_chargeGap`: The charge and physical-mode regularity hypotheses make the charge-gap function almost everywhere measurable on the region. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyExteriorNonneg.lean#L133).

**Source namespace `Breakdown.CertCell.Assembly`.**

**The exterior off-mode signed balance** · theorem. `exteriorOffMode_balance`: The valid exterior cover yields the required comparison between negative and positive off-mode integrals on the exterior half-plane. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyExteriorNonneg.lean#L168).

**The exterior contribution is nonnegative** · theorem. `exteriorNonneg_of_sound_of_measurable`: The measurable-density, regularity, admissibility, mode-class, mesh, finite-form, valid-cover and stretching-charge hypotheses together imply exterior nonnegativity. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyExteriorNonneg.lean#L212).

### Breakdown.CertCell.AssemblyExteriorStretch

This file states the pointwise exterior stretching bound and the harmonic triple-sum identity used to integrate it. Appendix B.2–B.3: support for assigning stretching costs outside the mesh.

**Source section `ExteriorStretch`.**

**The loss assigned to one exterior mode** · definition. `exteriorPointLoss`: The exterior point loss evaluates the sharp charge expression on the exterior coefficients and the mode's band profile. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyExteriorStretch.lean#L22).

**Source namespace `Breakdown.CertCell.Assembly`.**

**Exterior pointwise stretching interface** · interface proposition. `ExteriorPointBoundHolds`: The interface requires exterior regularity and bounded valid charges to bound negative mean stretching almost everywhere by the summed modal point losses. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyExteriorStretch.lean#L29).

Proved by `Breakdown.CertCell.Assembly.exteriorPointBound_of_tripleSum`.

**Harmonic triple-sum stretching interface** · interface proposition. `MeanStretchTripleSumHolds`: The interface requires the mean stretch to equal the sum of mode-pair interactions with the finitely supported model harmonics almost everywhere. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyExteriorStretch.lean#L40).

Proved by `Breakdown.CertCell.Assembly.meanStretchTripleSum`.

**Integrate the exterior pointwise bound** · theorem. `exteriorStretchCharged_of_point`: The pointwise stretching and triple-sum interfaces yield the exterior stretching-charge interface. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyExteriorStretch.lean#L53).

**Source namespace `Breakdown.CertCell.Assembly.Internal.ExteriorStretch`.**

**Triple matrix is the physical coupling** · theorem. `sesq12_tripleMatrix_eq_coupling`: The twelve-coordinate triple-matrix pairing equals the pairing with the true physical coupling matrix. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyExteriorStretch.lean#L301).

### Breakdown.CertCell.AssemblyExteriorStretchPointwise

This file supplies the measurable mode sums and charge inequalities behind the exterior pointwise stretching estimate. Appendix B.2–B.3: support for exterior mode allocation.

**Complex mode energy is nonnegative** · theorem. `cnormSq_nonneg'`: The sum of squared complex mode coordinates is nonnegative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyExteriorStretchPointwise.lean#L23).

**Bound the energy of a difference** · theorem. `norm_sub_sq_le`: The squared norm of a difference is at most twice each of the two squared norms added together. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyExteriorStretchPointwise.lean#L26).

**Gradient energy bounds curl energy** · theorem. `curl_cnormSq_le`: The complex curl energy is at most twice the complex gradient energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyExteriorStretchPointwise.lean#L31).

**The scalar charge-gap expression** · definition. `gapValue`: The scalar gap combines curl, gradient and velocity squares with the mixed square-root product term. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyExteriorStretchPointwise.lean#L44).

**A lower bound on the charge gap** · theorem. `gapValue_lower`: The coefficient bounds give the stated lower bound on the charge gap in terms of gradient energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyExteriorStretchPointwise.lean#L48).

**The charge gap has an energy majorant** · theorem. `gapValue_abs_weighted`: The bounded charge coefficients control the absolute gap by a fixed coefficient times velocity plus gradient energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyExteriorStretchPointwise.lean#L65).

**The allocated gap covers the sharp loss** · theorem. `loss_le_gapValue`: The positivity and coefficient hypotheses bound the sharp stretching loss by the scalar charge gap. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyExteriorStretchPointwise.lean#L109).

**Finite signed parts give integrability** · theorem. `integrable_of_pos_neg`: Finite integrals of both converted signs of a measurable function imply its integrability. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyExteriorStretchPointwise.lean#L141).

**The label-minus-tail density is the gap** · theorem. `density_gap`: Subtracting the off-mode density from the label density gives the scalar charge-gap expression on the physical mode energies. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyExteriorStretchPointwise.lean#L156).

**Measurable inputs give a measurable gap** · theorem. `aemeasurable_gapValue`: The charge-gap expression is almost everywhere measurable when its scalar coefficient and energy inputs are. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyExteriorStretchPointwise.lean#L170).

**Positive-part conversion ignores max** · theorem. `ofReal_max_zero`: Converting a real maximum with zero to extended nonnegative reals gives the same result as converting the original real number. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyExteriorStretchPointwise.lean#L183).

**Recover a number from its signed parts** · theorem. `max_sub_max`: The positive part minus the negative part of a real number equals that number. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyExteriorStretchPointwise.lean#L188).

**The pointwise signed allocation balance** · theorem. `point_ennreal`: The scalar modal inequalities imply the extended-real balance between negative and positive radial-weighted allocations. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyExteriorStretchPointwise.lean#L193).

**Finite integral gives a.e. summability** · theorem. `ae_summable_of_lintegral`: A finite integral of a nonnegative mode sum gives almost everywhere summability of its mode values. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyExteriorStretchPointwise.lean#L231).

**Read the gradient from packed data** · theorem. `gradOf_pairVec`: The gradient projection of a packed gradient-velocity vector returns the original gradient array. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyExteriorStretchPointwise.lean#L243).

**Read the velocity from packed data** · theorem. `velOf_pairVec`: The velocity projection of the packed vector returns the original velocity. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyExteriorStretchPointwise.lean#L249).

**Read the physical band gradient** · theorem. `gradOf_bandProfile`: The gradient part of a band profile is the corresponding labelled physical gradient mode. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyExteriorStretchPointwise.lean#L253).

**Read the physical band velocity** · theorem. `velOf_bandProfile`: The velocity part of a band profile is the corresponding labelled physical velocity mode. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyExteriorStretchPointwise.lean#L260).

**Split mean stretching into signed parts** · theorem. `meanStretch_eq_parts`: The mean stretch is the normalized difference of its positive and negative nonnegative time-rotation integrals. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyExteriorStretchPointwise.lean#L267).

**The model decay bound is nonnegative** · theorem. `decay_const_nonneg`: The stated model decay bound has a nonnegative constant. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyExteriorStretchPointwise.lean#L304).

**Negative phases are conjugate phases** · theorem. `phase_neg_star`: The harmonic phase at a negated label is the complex conjugate of the original phase. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyExteriorStretchPointwise.lean#L310).

**Reconstruct the framed model gradient** · theorem. `givenGrad_frame`: The finitely supported model gradient in the rotating frame is the phase-weighted sum of its harmonic gradient coefficients. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyExteriorStretchPointwise.lean#L314).

**Reconstruct the framed model Hessian** · theorem. `givenSecond_frame`: Almost everywhere in the half-plane, the model Hessian frame components equal their finite phase-weighted harmonic reconstruction. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyExteriorStretchPointwise.lean#L336).

**Strain and gradient forms agree** · theorem. `inner_strain_eq`: Pairing a vector with its image under the strain gives the same real quadratic form as the full gradient. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyExteriorStretchPointwise.lean#L359).

**Packed mode energy splits into two parts** · theorem. `cnormSq_pairVec`: The complex norm squared of a packed band vector is gradient energy plus velocity energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyExteriorStretchPointwise.lean#L368).

**Physical mode energies are summable** · theorem. `ae_mode_summable`: For almost every half-plane point, the labelled velocity and gradient mode-energy families are summable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyExteriorStretchPointwise.lean#L380).

### Breakdown.CertCell.AssemblyExteriorValueSets

This file states the bridge from the far-field value sets to valid exterior stretching-charge bounds. Appendix B.3–B.4: support for the exterior charge verification.

**Far-field values supply exterior charges** · interface proposition. `ExteriorValuesChargeHolds`: The interface requires scalar chart-bound facts and the far-field conditions to imply a valid region-charge bound on the exterior half-plane. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyExteriorValueSets.lean#L17).

Proved by `Breakdown.CertCell.Assembly.exteriorValuesChargeHolds`.

### Breakdown.CertCell.AssemblyExteriorValueSetsProof

This file proves the far-field-value bridge by identifying cylindrical evaluations with their half-plane values. Appendix B.3–B.4: support for exterior charge bounds.

**Source namespace `Breakdown.CertCell.Assembly.Internal.ExteriorValueSets`.**

**Rotate the radial-height plane point** · theorem. `rotate_planePoint`: Axial rotation of the radial-height plane point is the corresponding cylindrical point. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyExteriorValueSetsProof.lean#L17).

**Scalar chart bounds ignore the azimuth** · theorem. `eval_cylPoint`: The scalar chart-bound evaluation at a cylindrical point equals its evaluation at the corresponding half-plane point. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyExteriorValueSetsProof.lean#L21).

**Source namespace `Breakdown.CertCell.Assembly`.**

**Prove the exterior value-set bridge** · theorem. `exteriorValuesChargeHolds`: The scalar chart evaluations establish the interface taking far-field conditions to valid exterior region charges. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyExteriorValueSetsProof.lean#L30).

### Breakdown.CertCell.AssemblyFlipAverage

This file shows that reflection-averaging a right-hand side preserves the weak equation when the profile and actuator data have the required reflection symmetry. Appendix B.3: support for matching symmetric row fields.

**Source namespace `Breakdown.CertCell.Assembly.Internal.FlipAverageRight`.**

**Reflect a vector test in space and value** · definition. `flipConj`: The conjugated test reflects its spatial argument and then reflects its vector value. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyFlipAverage.lean#L23).

**Reflect the spatial point in space-time** · definition. `flipPair`: The space-time flip leaves time fixed and reflects the spatial coordinate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyFlipAverage.lean#L25).

**The flip uses the spatial isometry** · theorem. `flipPair_eq`: The space-time flip equals the identity in time paired with the reflection isometry. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyFlipAverage.lean#L27).

**Reflection preserves vector differences** · theorem. `flipPoint_sub`: Reflecting a vector difference gives the difference of the reflected vectors. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyFlipAverage.lean#L29).

**Reflection preserves finite vector sums** · theorem. `flipPoint_sum`: Reflecting a finite vector sum gives the sum of its reflected vectors. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyFlipAverage.lean#L32).

**Reflection preserves the full integral** · theorem. `integral_flip`: Composing with the space-time reflection leaves the integral unchanged. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyFlipAverage.lean#L35).

**Reflection preserves and reflects L1** · theorem. `integrable_flip_iff`: A function composed with the space-time flip is integrable exactly when the original function is. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyFlipAverage.lean#L38).

**A reflected test is still a test** · theorem. `flipConj_test`: The reflected conjugate of a space-time test field is again a valid test field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyFlipAverage.lean#L42).

**Differentiate the reflected vector field** · theorem. `fderiv_conj`: The derivative of a reflection-conjugated field is the original derivative conjugated by reflection. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyFlipAverage.lean#L46).

**Reflection commutes with time derivative** · theorem. `deriv_conj`: The time derivative of a reflected vector curve equals the reflection of its derivative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyFlipAverage.lean#L53).

**Derivatives preserve equivariance** · theorem. `fderiv_field_flip`: The derivative of a reflection-equivariant field transforms by the same reflection in its input and output directions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyFlipAverage.lean#L59).

**Move reflection through matrix pairings** · theorem. `matInner_conj`: The matching reflection-conjugacy identities transfer the matrix inner product between its two arguments. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyFlipAverage.lean#L68).

**The similarity transport test** · definition. `transportTest`: The transport test combines the time derivative, the test and its radial derivative with the similarity coefficients. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyFlipAverage.lean#L76).

**The transported test respects reflection** · theorem. `transportTest_conj`: Transporting the reflected test equals reflecting the transported original test at the flipped point. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyFlipAverage.lean#L79).

**Reflection preserves the forcing pairing** · theorem. `derivative_pairing_flip`: The perturbation derivative identity and field symmetries make the forcing pairing identical for the original and reflected tests. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyFlipAverage.lean#L86).

**The remaining weak-equation terms** · definition. `restIntegrand`: The remainder integrand combines profile convection, actuator forcing and gradient-test energy after separating the free transport forcing. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyFlipAverage.lean#L105).

**Separate forcing from the weak remainder** · theorem. `integrand_split`: The full weak right-hand-side integrand splits into its forcing pairing plus the defined remainder integrand. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyFlipAverage.lean#L110).

**The remainder transforms by reflection** · theorem. `rest_flip`: The symmetric profile, actuator and perturbation data make the reflected-test remainder equal almost everywhere to the flipped original remainder. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyFlipAverage.lean#L119).

**Reflection preserves the weak pairing** · theorem. `rhs_flip`: The weak equation's full right-hand-side pairing has equal values on the test and its reflected conjugate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyFlipAverage.lean#L141).

**Reflected-field pairing is integrable** · theorem. `pairing_integrable`: The specified periodic field and compact test have an integrable physical pairing. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyFlipAverage.lean#L173).

**Move reflection averages onto tests** · theorem. `average_pairing`: Pairing the reflection-averaged field with a test equals half its original-test pairing plus half its reflected-test pairing. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyFlipAverage.lean#L179).

**Source namespace `Breakdown.CertCell.Assembly`.**

**Averaged field remains a right-hand side** · theorem. `flipAverage_rightSide`: Under the required field symmetries, reflection-averaging a valid right-hand side preserves its weak right-hand-side specification. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyFlipAverage.lean#L201).

**Prove the reflection-average interface** · theorem. `flipAverageRightSide_holds`: The reflection identities and integrability arguments establish the right-hand-side preservation interface. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyFlipAverage.lean#L225).

### Breakdown.CertCell.AssemblyFormSplit

This file splits the global quadratic form into its finitely many mesh cells and the exterior region, with the coordinate axes discarded as a null set. Appendix B.3: support for the cell and complement form decomposition.

**Source namespace `Breakdown.CertCell.Assembly.Internal`.**

**The half-plane axes are null** · theorem. `axes_null`: The boundary axes of the closed half-plane have two-dimensional Lebesgue measure zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyFormSplit.lean#L16).

**Cell rectangles lie in the half-plane** · theorem. `rect_sub`: Each cell rectangle lies in the closed half-plane. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyFormSplit.lean#L29).

**Cell rectangles are measurable** · theorem. `rect_measurable`: Each cell rectangle is a measurable set. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyFormSplit.lean#L34).

**Split a nonnegative half-plane integral** · theorem. `lintegral_halfPlane_split`: The nonnegative integral over the half-plane equals the sum over mesh-cell integrals plus the exterior integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyFormSplit.lean#L37).

**Regroup mode and cell contributions** · theorem. `regroup`: The nonnegative sum of mode contributions can be rearranged into its finite cell sum and exterior sum. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyFormSplit.lean#L61).

**Source namespace `Breakdown.CertCell.Assembly`.**

**Prove the global form split** · theorem. `formSplit_holds`: The measurable mesh decomposition and null boundary establish the global form-splitting interface. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyFormSplit.lean#L69).

### Breakdown.CertCell.AssemblyHarmonicAnnihilator

This file takes a smooth periodic time harmonic of a space-time annihilator and proves that it still annihilates stationary divergence-free tests. Appendix B.3: support for recovering the pressure harmonics.

**Source namespace `Breakdown.CertCell.Assembly.Internal`.**

**A cutoff covering one period** · definition. `harmonicCutoff`: The harmonic cutoff is the difference between a smooth transition and its unit translate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyHarmonicAnnihilator.lean#L18).

**The harmonic cutoff is smooth** · theorem. `harmonicCutoff_contDiff`: The harmonic cutoff is infinitely differentiable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyHarmonicAnnihilator.lean#L20).

**The cutoff vanishes outside two periods** · theorem. `harmonicCutoff_eq_zero`: The harmonic cutoff vanishes outside the interval from zero to two. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyHarmonicAnnihilator.lean#L24).

**The harmonic cutoff is bounded by one** · theorem. `harmonicCutoff_abs_le`: The absolute value of the harmonic cutoff is at most one. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyHarmonicAnnihilator.lean#L32).

**Two shifted cutoffs sum to one** · theorem. `harmonicCutoff_add_shift`: On the unit interval, the cutoff and its unit translate sum to one. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyHarmonicAnnihilator.lean#L41).

**The cutoff extracts a period integral** · theorem. `integral_harmonicCutoff_mul`: For an integrable periodic integrand, multiplying by the cutoff and integrating over the real line gives its unit-period integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyHarmonicAnnihilator.lean#L48).

**A harmonic stationary test is valid** · theorem. `harmonic_testField`: Multiplying a stationary test by the cutoff and a smooth periodic scalar produces a valid space-time test field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyHarmonicAnnihilator.lean#L82).

**Swap measurable space-time arguments** · theorem. `harmonic_swap_aesm`: Almost everywhere strong measurability is preserved when the time and space variables are exchanged. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyHarmonicAnnihilator.lean#L102).

**The harmonic average is measurable** · theorem. `harmonic_weighted_aesm`: The spatial field obtained by a weighted time-period average is almost everywhere strongly measurable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyHarmonicAnnihilator.lean#L112).

**Local square bounds give box L1** · theorem. `harmonic_box_integrable`: Local square integrability yields integrability on a unit time interval times a compact spatial ball. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyHarmonicAnnihilator.lean#L119).

**Integrability on the shifted box** · theorem. `harmonic_box_integrable_shift`: Periodicity transfers the box integrability bound to the interval from one to two. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyHarmonicAnnihilator.lean#L141).

**The mean obeys a squared-norm bound** · theorem. `harmonic_sq_norm_integral_le`: For a probability measure, the squared norm of an integral is at most the integral of the squared norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyHarmonicAnnihilator.lean#L164).

**Harmonic averaging preserves local L2** · theorem. `harmonic_weighted_localSquare`: A periodic field with local square bounds retains local square integrability after averaging against a bounded periodic weight. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyHarmonicAnnihilator.lean#L185).

**The harmonic average annihilates tests** · theorem. `harmonic_weighted_annihilates`: A measurable periodic space-time annihilator with local square bounds has weighted period average orthogonal to every stationary test when the smooth periodic weight is bounded by one. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyHarmonicAnnihilator.lean#L217).

**Source namespace `Breakdown.CertCell.Assembly`.**

**Prove the harmonic annihilator rule** · theorem. `harmonicAnnihilator_holds`: The cutoff test and local integrability arguments establish the harmonic-annihilator interface. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyHarmonicAnnihilator.lean#L311).

### Breakdown.CertCell.AssemblyLinkInitial

This file turns the global form split and reflection average into the initial bound used by the finite tree calculation. Appendix B.3: support for initializing the cell-elimination tree.

**Source namespace `Breakdown.CertCell.Assembly.Internal.InitialLink`.**

**Positive and negative parts recover a** · theorem. `max_sub_max_neg`: Subtracting the negative part of a real number from its positive part recovers that number. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyLinkInitial.lean#L20).

**Convert the cell bound to real form** · theorem. `real_le_of_cell_bound`: The finite cell estimate converts its extended positive and negative form terms into the required real inequality. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyLinkInitial.lean#L27).

**Equal coercivity leaves forms unchanged** · theorem. `formPos_withFormCoercivity`: Changing the form-coercivity field to an equal value leaves both the positive and negative forms unchanged. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyLinkInitial.lean#L49).

**The reflection average is measurable** · theorem. `flipAverage_measurable`: The reflection average of a measurable field is measurable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyLinkInitial.lean#L70).

**The reflection average is periodic** · theorem. `flipAverage_periodic`: Reflection-averaging preserves time periodicity. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyLinkInitial.lean#L80).

**Bound the reflection-average energy** · theorem. `norm_sq_half_sum_le`: The squared norm of half the sum of a vector and a reflected vector is at most the sum of their squared norms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyLinkInitial.lean#L87).

**The reflection average has finite energy** · theorem. `flipAverage_finite`: A field with finite period energy has a reflection average with finite period energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyLinkInitial.lean#L98).

**Source namespace `Breakdown.CertCell.Assembly`.**

**The form split bounds the initial state** · theorem. `initialStateBound_of_split`: The form decomposition and the supplied cell bounds imply the initial-state inequality. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyLinkInitial.lean#L132).

**Assemble the initial-state bound** · theorem. `initialStateHolds_of_split`: The split-form hypotheses establish the initial-state interface. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyLinkInitial.lean#L218).

**Use the global form-split interface** · theorem. `initialStateHolds_of_formSplit`: The form-splitting interface supplies the initial-state interface for the elimination tree. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyLinkInitial.lean#L222).

### Breakdown.CertCell.AssemblyLinkPressure

This file assembles pressure recovery from the annihilator potential, harmonic extraction, reflection average and regularity of the equation remainder. Appendix B.3: support for the pressure fields used in cell pairings.

**Assemble pressure recovery** · theorem. `pressureRecoveryHolds_of_pressureParts`: The gradient-annihilator, harmonic-annihilator, reflection-average and remainder interfaces together imply the pressure-recovery interface. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyLinkPressure.lean#L15).

### Breakdown.CertCell.AssemblyModelLabels

This file records that model harmonics outside the finite label set contribute no plane values or derivatives. Appendix B.3: support for finite model-mode sums.

**Unlisted model harmonics vanish** · theorem. `modelPlaneValues_eq_zero_of_not_mem`: A label outside the model label set has zero model velocity, vorticity, strain and vorticity-gradient plane values. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyModelLabels.lean#L15).

### Breakdown.CertCell.AssemblyOddStream

This file converts real time harmonics to complex modes and uses the mode-class symmetry to eliminate odd stream moments. Appendix B.3: support for the symmetry constraints on cell moments.

**Source namespace `Breakdown.CertCell.Assembly.Internal.OddStream`.**

**Complex modes combine cosine and sine** · theorem. `timeMode_lift`: For a periodic second-order field, velocity and gradient modes agree almost everywhere at positive radius with the cosine-harmonic mode plus i times the sine-harmonic mode. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyOddStream.lean#L31).

**Odd axisymmetric labels miss the lattice** · theorem. `not_lattice_of_odd`: An odd temporal frequency with zero azimuthal frequency is outside the admissible harmonic lattice. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyOddStream.lean#L59).

**Zero height is a null plane set** · theorem. `ae_snd_ne_zero`: The height coordinate is nonzero almost everywhere in the radial-height plane. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyOddStream.lean#L68).

**Combine two vanishing strip relations** · theorem. `strip_combine`: The real strip identities combine into the corresponding zero complex strip integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyOddStream.lean#L75).

**Source namespace `Breakdown.CertCell.Assembly`.**

**Odd stream moments vanish** · theorem. `oddStreamZero_holds`: The mode-lattice exclusion and real-to-complex harmonic identities prove the odd-stream-zero statement. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyOddStream.lean#L83).

### Breakdown.CertCell.AssemblyOffModes

This file proves that the certified complementary-mode cover controls every mode outside the resolved set, including conservative enlargements of the charge deductions. Appendix B.3: support for the complementary-mode estimate.

**Source namespace `Breakdown.CertCell.Assembly.Internal.OffModeCover`.**

**Zero height is a null plane set** · theorem. `null_axis_plane`: The height coordinate is nonzero almost everywhere in the radial-height plane. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyOffModes.lean#L24).

**Larger charges lower the quadratic form** · theorem. `quad_withStretch_antitone`: Increasing the curl, gradient and velocity charges decreases the adjusted pointwise quadratic form. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyOffModes.lean#L33).

**Larger charges lower off-mode density** · theorem. `offModeDensity_antitone`: With the stretching constant fixed, increasing the curl, gradient and velocity charges decreases the off-mode density. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyOffModes.lean#L41).

**A dominating sound cover removes modes** · theorem. `offModesVanish_of_sound_of_dominates`: A sound complementary-mode cover with charges dominating the required deductions implies the off-modes conclusion. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyOffModes.lean#L51).

**Source namespace `Breakdown.CertCell.Assembly`.**

**Use a sound complementary-mode cover** · theorem. `offModesVanish_of_sound`: Soundness of the complementary-mode cover establishes the off-modes interface. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyOffModes.lean#L100).

**Prove the complementary-mode interface** · theorem. `offModesVanishHolds`: The verified mode-cover construction supplies the off-modes interface. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyOffModes.lean#L111).

### Breakdown.CertCell.AssemblyPairingStage

This file separates resolved, band and remaining pairing terms and bounds their residuals by the allocated strain and Gram costs. Appendix B.3: support for the actuator-pairing stage of the tree.

**Source section `Classes`.**

**The physical pairing cross term** · definition. `pairCross`: The cross term integrates the real pairing of the physical gradient with the weighted pairing profile over one cell. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPairingStage.lean#L18).

**Inactive profiles have zero cross term** · theorem. `pairCross_dead`: If the profile is not live on the cell, its pairing cross term is zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPairingStage.lean#L23).

**The pairing share is a label sum** · theorem. `share_eq`: The cell pairing share is the finite sum of cross terms over the pairing labels. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPairingStage.lean#L35).

**Identify a band pairing contribution** · theorem. `band_term_eq`: The band-linear contribution is the pairing cross term for a pairing label and is zero for other labels. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPairingStage.lean#L81).

**Bound the resolved pairing term** · theorem. `resolved_bound`: The resolved low-gradient pairing is bounded by the physical cross term plus the allocated tail-strain cost and active Gram penalty. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPairingStage.lean#L102).

**Bound the remaining pairing from below** · theorem. `other_bound`: The physical cross term for a remaining label is bounded below by the negative allocated leakage energy and active Gram penalty. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPairingStage.lean#L271).

**Split a sum into three label classes** · theorem. `sum_split_three`: A finite sum splits into resolved labels, band labels and labels belonging to neither class. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPairingStage.lean#L389).

**Prove the pairing stage on one cell** · theorem. `stage_cell`: The three label estimates combine to give the cell pairing-stage inequality. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPairingStage.lean#L402).

**Source namespace `Breakdown.CertCell.Assembly`.**

**Assemble the pairing-stage interface** · theorem. `pairingStageHolds_of_lowTailSplit`: The low-tail splitting interface supplies the orthogonality estimates needed for the pairing-stage interface. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPairingStage.lean#L525).

### Breakdown.CertCell.AssemblyPairingStageParts

This file supplies the projection, integrability and algebra facts used to compare physical gradients with the finite polynomial pairing profiles. Appendix B.3: analytic support for the pairing stage.

**Source namespace `Breakdown.CertCell.Assembly`.**

**Polynomial residual orthogonality** · proposition definition. `ProjResidualOrthogonal`: The predicate requires the weighted projection residual to pair to zero with every polynomial in the cell degree space under the stated basis and integrability conditions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPairingStageParts.lean#L12).

**Source namespace `Breakdown.CertCell.Assembly.Internal.RestrictedPairing`.**

**Control line weight by radial weight** · theorem. `lineWeight_le_scaled`: The line weight is bounded by the radius times one for an axis cell, or by the inverse inner radius for a cell away from the axis. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPairingStageParts.lean#L27).

**Extract a packed gradient coordinate** · theorem. `pairVec_at_grad`: The gradient slot of the packed pairing vector equals the corresponding gradient coordinate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPairingStageParts.lean#L36).

**Extract a packed velocity coordinate** · theorem. `pairVec_at_vel`: The velocity slot of the packed pairing vector equals the corresponding velocity coordinate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPairingStageParts.lean#L44).

**The weighted complex product is L1** · theorem. `weighted_conj_integrable`: The stated weighted square bounds make the radial product with the conjugated coefficient integrable on the cell. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPairingStageParts.lean#L51).

**Swap a real conjugate pairing** · theorem. `re_conj_swap`: The real part of a complex product with the second factor conjugated equals the real part with the first factor conjugated instead. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPairingStageParts.lean#L83).

**Expand the real gradient pairing** · theorem. `re_integral_pair_sum`: The real part of the integrated gradient pairing equals the integral of the coordinatewise real conjugate products. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPairingStageParts.lean#L86).

**The summed cross density is integrable** · theorem. `cross_sum_integrable`: The componentwise weighted bounds make the finite sum defining the cross-pairing density integrable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPairingStageParts.lean#L114).

**Simplify the half-scaled real pairing** · theorem. `conj_half_mul_re`: The conjugate-product identity converts the half-scaled pairing into its real bilinear form. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPairingStageParts.lean#L124).

**Tail energy is nonnegative** · theorem. `tailNormSq_nonneg`: The squared norm allocated to the tail is nonnegative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPairingStageParts.lean#L131).

**Source section `Data`.**

**The low profile is continuous** · theorem. `lowProfile_continuous`: The finite cell-polynomial low profile is continuous. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPairingStageParts.lean#L140).

**Cell states recover physical weights** · theorem. `pairWeightOf_cellState`: Extracting pairing weights from the physical cell state gives the complexified physical pairing weights. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPairingStageParts.lean#L149).

**Pairing profiles are measurable bounded** · theorem. `profile_regular`: The finite pairing profile is measurable and bounded on its cell rectangle. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPairingStageParts.lean#L159).

**A profile with a nonzero component** · proposition definition. `ProfileLive`: A profile is live when some pairing-profile component is not almost everywhere zero on the cell. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPairingStageParts.lean#L174).

**Inactive profiles vanish a.e.** · theorem. `profile_ae_zero`: A profile that is not live has every pairing-profile component zero almost everywhere on the cell. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPairingStageParts.lean#L177).

**Identify the packed gradient component** · theorem. `gradAt_eq_bandProfile`: The gradient coefficient agrees with the gradient slot in the band profile. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPairingStageParts.lean#L195).

**Physical gradients have weighted L2** · theorem. `grad_regular`: The physical gradient coefficients are measurable and square integrable for both the line and radial cell weights. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPairingStageParts.lean#L202).

### Breakdown.CertCell.AssemblyPiecesFinite

This file proves finiteness of the positive and negative cell contributions by comparing them with the global form and a summable charge majorant. Appendix B.3: integrability support for the cell form decomposition.

**Source namespace `Breakdown.CertCell.Assembly.Internal.PiecesFinite`.**

**Cells lie almost everywhere inside** · theorem. `rect_ae_le_halfPlane`: A cell rectangle is contained almost everywhere in the open half-plane. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPiecesFinite.lean#L19).

**Cell rectangles are measurable** · theorem. `measurableSet_rect`: Each cell rectangle is a measurable set. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPiecesFinite.lean#L35).

**Equal coercivity preserves negative form** · theorem. `formNeg_withCoercivity`: Replacing the coercivity field by an equal value leaves the negative form unchanged. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPiecesFinite.lean#L38).

**The local negative form is bounded** · theorem. `cellNeg_le_formNeg`: The negative contribution on a cell is at most the global negative form. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPiecesFinite.lean#L49).

**Bound the adjusted quadratic gap** · theorem. `quad_gap_le`: The absolute gap between the original and charge-adjusted quadratic forms is bounded by the explicit cubic coefficient times the selected squared components. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPiecesFinite.lean#L57).

**An extended majorant for charge gaps** · theorem. `ofReal_split`: The real quadratic gap is bounded in extended nonnegative form by a multiple of three gradient-energy terms and the radius-scaled velocity energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPiecesFinite.lean#L127).

**The radial gradient-energy density** · definition. `gradAmount`: The gradient amount is the extended nonnegative value of the squared complex-gradient norm times radius. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPiecesFinite.lean#L135).

**The weighted velocity-energy density** · definition. `velAmount`: The velocity amount is the extended nonnegative value of the squared complex-velocity norm times radius divided by squared distance to the origin. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPiecesFinite.lean#L138).

**A common charge-energy majorant** · definition. `chargeMajorant`: The charge majorant is a fixed coefficient times three gradient amounts plus the radius-scaled velocity amount. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPiecesFinite.lean#L141).

**The charge majorant is measurable** · theorem. `aemeasurable_chargeMajorant`: The charge majorant is almost everywhere measurable under the physical-field regularity assumptions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPiecesFinite.lean#L145).

**The charge majorant is summable** · theorem. `tsum_chargeMajorant_lt_top`: The sum over modes of the integrated charge majorants is finite. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPiecesFinite.lean#L160).

**Enlarge the region in a majorant bound** · theorem. `setLIntegral_le_add`: A pointwise local bound by two nonnegative functions bounds the local integral by the local first integral plus the second integral on a containing region. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPiecesFinite.lean#L180).

**Control velocity on a bounded rectangle** · theorem. `vel_le`: The radius-weighted velocity amount on the bounded rectangle is controlled by the inverse-distance-weighted amount times the squared coordinate bounds. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPiecesFinite.lean#L188).

**Source namespace `Breakdown.CertCell.Assembly`.**

**Finite cell pieces from azimuth bounds** · theorem. `cellPiecesFinite_of_azimuth`: The azimuthal decomposition and regular charge bounds imply finiteness of the cell form pieces. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPiecesFinite.lean#L206).

**Assemble cell-piece finiteness** · theorem. `cellPiecesFiniteHolds_of_azimuth`: Positive azimuth order, mesh validity, cell-calculus conditions, the coefficient lower bound, finite negative form and regular charges imply the cell-pieces-finite conclusion. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPiecesFinite.lean#L327).

**Prove the cell-finiteness interface** · theorem. `cellPiecesFiniteHolds`: The azimuthal summability estimates establish the cell-pieces-finite interface. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPiecesFinite.lean#L334).

### Breakdown.CertCell.AssemblyPotentialEps

This file exposes the resolved epsilon-potential estimate assembled from its sharp charge and box-penalty bounds. Appendix B.3: support for the resolved potential stage.

**Prove the resolved epsilon stage** · theorem. `epsResolvedStage_holds`: The supporting charge estimates establish the resolved epsilon-stage interface. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialEps.lean#L12).

### Breakdown.CertCell.AssemblyPotentialEpsCore

This file turns the sharp split charge into a box-pair penalty and integrates the pointwise domination to obtain the resolved epsilon estimate. Appendix B.3: analytic support for the resolved epsilon stage.

**Source namespace `Breakdown.CertCell.Assembly.Internal.EpsResolved`.**

**Complex squared norm is nonnegative** · theorem. `cnormSq_nonneg_aux`: The sum of squared complex-component norms is nonnegative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialEpsCore.lean#L19).

**The split charge is nonnegative** · theorem. `splitCharge_nonneg_aux`: Nonnegative charge coefficients give a nonnegative split charge on velocity and gradient inputs. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialEpsCore.lean#L22).

**The box penalty bounds the split charge** · theorem. `splitCharge_le_boxPair`: The split charge is bounded by the corresponding box-pair penalty under the coefficient bounds. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialEpsCore.lean#L28).

**Integrate a nonnegative sum bound** · theorem. `setIntegral_add_le_of_nonneg`: Pointwise domination and the stated nonnegativity and integrability conditions imply that the sum of the two integrals is bounded by the majorant integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialEpsCore.lean#L36).

**Source namespace `Breakdown.CertCell.Assembly`.**

**Assemble the resolved epsilon estimate** · theorem. `epsResolvedStage_holds_of`: The supplied sharp-charge and box-penalty bounds establish the resolved epsilon-stage interface. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialEpsCore.lean#L58).

### Breakdown.CertCell.AssemblyPotentialExpand

This file expands mean stretching into harmonic couplings and splits the resulting profiles into finite polynomial and remainder parts. Appendix B.3: support for the potential expansion used in the cell bounds.

**Source section `Main`.**

**The cell polynomial basis is continuous** · theorem. `continuous_basis`: Every tensor-product cell-basis polynomial is continuous. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpand.lean#L28).

**The low profile is continuous** · theorem. `continuous_lowProfile`: The finite cell-polynomial low profile is continuous. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpand.lean#L32).

**Upper profiles have the required bounds** · theorem. `good_upper`: The upper profiles satisfy the measurable and integrability conditions packaged by the Good predicate on the cell rectangle. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpand.lean#L42).

**The physical coupling is admissible** · theorem. `couplingOK_rect`: The physical coupling satisfies the required coupling conditions on the cell rectangle. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpand.lean#L53).

**Physical profiles are Good** · theorem. `good_true`: The physical profiles satisfy the measurable and integrability conditions packaged by the Good predicate on the cell rectangle. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpand.lean#L61).

**Harmonic labels admit negation** · theorem. `harmonicLabels_neg`: Negating a potential harmonic label gives another potential harmonic label. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpand.lean#L68).

**Reverse the physical real coupling** · theorem. `trueCoupling_sym`: The real sesquilinear coupling with the negated label and reversed inputs equals the original real coupling. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpand.lean#L75).

**Source namespace `Breakdown.CertCell.Assembly`.**

**Prove the stretching split** · theorem. `stretchSplit`: The polynomial and remainder profiles satisfy the stretching-split interface. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpand.lean#L84).

**Expand stretching within a mode class** · theorem. `stretchExpansion_of_class`: Assembly regularity, physical-field regularity, potential conditions and mode-class symmetry imply the stretching expansion. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpand.lean#L97).

**Use mode symmetry in the expansion** · theorem. `stretchExpansion_of_modeClass`: The mode-class assumptions provide the exact stretching expansion under the stated regularity and potential conditions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpand.lean#L121).

**Mean stretching is a harmonic sum** · theorem. `meanStretch_eq_labelSum_of_modeClass`: For a mode-class field, the coupling series is summable and its label sum equals mean stretching almost everywhere on the half-plane. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpand.lean#L129).

### Breakdown.CertCell.AssemblyPotentialExpandCoupling

This file constructs the physical stretching-coupling matrix from harmonic derivatives, proves its conjugation symmetry and boundedness, and identifies its sesquilinear form with the stretching triple. Appendix B.3: algebraic and analytic support for the potential expansion.

**Source section `Coupling`.**

**Negation preserves harmonic labeling** · theorem. `Breakdown.CertCell.AssemblyPotentialExpandCoupling.labelHarmonic_neg`: The harmonic associated to a negated label is the negative of the original harmonic. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpandCoupling.lean#L26).

**Negative gradient modes are conjugates** · theorem. `labelGrad_neg`: The gradient coefficient at a negated label is the complex conjugate of the original coefficient. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpandCoupling.lean#L30).

**Negative Hessian modes are conjugates** · theorem. `labelSecond_neg`: The Hessian coefficient at a negated label is the complex conjugate of the original coefficient. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpandCoupling.lean#L37).

**Conjugate every input of the triple** · theorem. `Breakdown.CertCell.AssemblyPotentialExpandCoupling.conj_modelTriple`: Conjugating the model triple equals the triple of the conjugated tensors, velocities and gradients. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpandCoupling.lean#L44).

**Swap the two field inputs** · theorem. `modelTriple_comm`: The model triple is symmetric under exchanging its two velocity-gradient input pairs. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpandCoupling.lean#L53).

**Velocity basis vectors are real** · theorem. `conj_velOf_single`: Complex conjugation leaves each velocity vector extracted from a coordinate basis vector unchanged. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpandCoupling.lean#L58).

**Gradient basis vectors are real** · theorem. `conj_gradOf_single`: Complex conjugation leaves each gradient matrix extracted from a coordinate basis vector unchanged. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpandCoupling.lean#L64).

**Star fixes the velocity basis** · theorem. `star_velOf_single`: The star operation fixes every extracted coordinate velocity vector. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpandCoupling.lean#L70).

**Star fixes the gradient basis** · theorem. `star_gradOf_single`: The star operation fixes every extracted coordinate gradient matrix. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpandCoupling.lean#L73).

**Conjugation commutes with curl gradients** · theorem. `curlSecond_conj`: Taking the curl gradient of a conjugated second-derivative tensor gives the conjugate curl gradient. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpandCoupling.lean#L76).

**Physical coupling matrix is symmetric** · theorem. `trueCoupling_symm`: Interchanging the row and column indices leaves the physical coupling matrix unchanged. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpandCoupling.lean#L80).

**Negative coupling labels are conjugates** · theorem. `trueCoupling_neg`: The physical coupling matrix at the negative label is the entrywise conjugate matrix. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpandCoupling.lean#L85).

**Reverse and conjugate the coupling** · theorem. `sesq12_trueCoupling_neg`: The sesquilinear form with negative label and reversed inputs is the complex conjugate of the original form. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpandCoupling.lean#L90).

**Source section `CouplingRegular`.**

**A coupling entry from derivative data** · definition. `entryFn`: The entry function evaluates the model triple on fixed coordinate basis inputs using the supplied gradient and Hessian data. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpandCoupling.lean#L104).

**Coupling entries depend continuously** · theorem. `continuous_entryFn`: Every coupling-entry function is continuous in its gradient and Hessian inputs. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpandCoupling.lean#L108).

**Express coupling through derivative data** · theorem. `trueCoupling_eq`: Each physical coupling entry is its entry function evaluated on the corresponding harmonic gradient and Hessian. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpandCoupling.lean#L114).

**The weak-state bound is nonnegative** · theorem. `decay_nonneg`: The bound in a weak second-derivative state is nonnegative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpandCoupling.lean#L118).

**Harmonic gradients obey the state bound** · theorem. `labelGrad_given_le`: Every component of the harmonic gradient is bounded in norm by the weak second-derivative state bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpandCoupling.lean#L122).

**Harmonic Hessians obey the state bound** · theorem. `labelSecond_given_le`: Every component of the harmonic Hessian is bounded in norm by the weak second-derivative state bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpandCoupling.lean#L136).

**Harmonic derivative data are measurable** · theorem. `labelGiven_meas`: The harmonic gradient and Hessian of a weak second-derivative state are almost everywhere strongly measurable on the half-plane. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpandCoupling.lean#L149).

**Bound entries on bounded input data** · theorem. `entryFn_bound`: Uniform component bounds for the gradient and Hessian give a uniform bound for each coupling-entry function. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpandCoupling.lean#L174).

**The physical coupling is bounded** · theorem. `trueCoupling_bound`: A weak second-derivative bound on the given field yields a uniform bound on every physical coupling entry at a fixed label. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpandCoupling.lean#L183).

**The physical coupling is measurable** · theorem. `trueCoupling_meas`: Every physical coupling entry is almost everywhere strongly measurable on the half-plane. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpandCoupling.lean#L195).

**Source section `Expand`.**

**Curl commutes with scalar multiplication** · theorem. `curl_smul`: Multiplying a gradient by a complex scalar multiplies its curl by the same scalar. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpandCoupling.lean#L208).

**Scale the first bilinear input** · theorem. `bilin_smul_left`: The model bilinear form is complex linear in its first velocity-gradient input pair. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpandCoupling.lean#L213).

**Scale the second bilinear input** · theorem. `bilin_smul_right`: The model bilinear form is complex linear in its second velocity-gradient input pair. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpandCoupling.lean#L235).

**The triple as a first-slot linear map** · definition. `firstSlot`: Holding the other inputs fixed makes the model triple a complex linear map of its first packed field input. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpandCoupling.lean#L257).

**The triple as a second-slot linear map** · definition. `secondSlot`: Holding the other inputs fixed makes the model triple a complex linear map of its second packed field input. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpandCoupling.lean#L269).

**A coordinate selector is a basis vector** · theorem. `single_eq`: The indicator selecting one coordinate equals the corresponding single-coordinate basis vector. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpandCoupling.lean#L281).

**Expand the triple in coordinates** · theorem. `triple_expand`: The model triple equals the double sum of its coordinate-basis values weighted by the two packed input vectors. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpandCoupling.lean#L285).

**Source section `Pointwise`.**

**The matrix form is the stretching triple** · theorem. `sesq12_trueCoupling_eq`: The physical coupling sesquilinear form equals the stretching triple with the second field input unconjugated and the first field input conjugated. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpandCoupling.lean#L309).

**Extract the physical band velocity** · theorem. `velOf_bandProfile`: The velocity component of the band profile is the corresponding harmonic velocity coefficient. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpandCoupling.lean#L327).

**Extract the physical band gradient** · theorem. `gradOf_bandProfile`: The gradient component of the band profile is the corresponding harmonic gradient coefficient. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpandCoupling.lean#L332).

**A zero first field gives zero stretching** · theorem. `stretchTriple_zero_left`: The stretching triple vanishes when its first velocity-gradient pair is zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpandCoupling.lean#L338).

**Zero second field gives zero stretching** · theorem. `stretchTriple_zero_right`: The stretching triple vanishes when its second velocity-gradient pair is zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpandCoupling.lean#L342).

**Harmonic labeling preserves differences** · theorem. `labelHarmonic_sub`: The harmonic associated to a difference of labels is the difference of their harmonics. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpandCoupling.lean#L346).

**Harmonic labeling preserves sums** · theorem. `labelHarmonic_add`: The harmonic associated to a sum of labels is the sum of their harmonics. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpandCoupling.lean#L350).

### Breakdown.CertCell.AssemblyPotentialExpandLattice

This file removes the harmonics forbidden by the mode class and rewrites the remaining orbit sum using the finite potential labels. Appendix B.3: support for indexing the stretching expansion by admissible labels.

**Source section `OffLattice`.**

**Velocity-mode zero survives time shift** · theorem. `modeVel_zero_of_shift`: For a periodic field, a velocity mode that vanishes at one time shift also vanishes at the zero shift. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpandLattice.lean#L26).

**Gradient-mode zero survives time shift** · theorem. `modeGrad_zero_of_shift`: For a periodic gradient field, a gradient mode that vanishes at one time shift also vanishes at the zero shift. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpandLattice.lean#L39).

**Zero complex squared norm forces zero** · theorem. `eq_zero_of_cnormSq`: A complex vector with zero sum of squared component norms is zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpandLattice.lean#L53).

**Gradient energy is locally finite** · theorem. `gradient_local_finite`: The perturbation regularity bounds give finite gradient energy over one period and any compact spatial ball. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpandLattice.lean#L58).

**Forbidden lattice modes vanish** · theorem. `ae_offLattice_zero`: The class-support interface and mode-class perturbation assumptions make both velocity and gradient modes outside the harmonic lattice vanish almost everywhere on the half-plane. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpandLattice.lean#L70).

**Source section `PointwiseSum`.**

**One real stretching-orbit contribution** · definition. `orbitTerm`: The orbit term is the real stretching triple coupling a perturbation mode with its shift by a given-field harmonic. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpandLattice.lean#L124).

**Rewrite orbit terms in label coordinates** · theorem. `orbitTerm_label`: At a half-plane point, an orbit term indexed by admissible harmonics equals the real physical-coupling form between the corresponding band profiles. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpandLattice.lean#L128).

**Source section `LabelSum`.**

**Mean stretching equals the label series** · theorem. `meanStretch_eq_labelSum`: The mode-sum and class-support interfaces, positive azimuth order and harmonic expansion imply almost everywhere summability and equality of mean stretching with the labeled coupling series. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpandLattice.lean#L145).

### Breakdown.CertCell.AssemblyPotentialExpandLink

This file exposes the fully assembled stretching-expansion result after the coupling and lattice arguments. Appendix B.3: the interface linking the physical form to potential couplings.

**Prove the stretching-expansion interface** · theorem. `stretchExpansionHolds`: The harmonic coupling, summability and mode-class results establish the stretching-expansion interface. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpandLink.lean#L9).

### Breakdown.CertCell.AssemblyPotentialExpandPairs

This file develops a summable bilinear pairing calculus for mode-indexed profiles and proves the exact resolved, band and remainder split. Appendix B.3: support for decomposing and integrating potential interactions.

**Source namespace `Breakdown.CertCell.Assembly.Internal.StretchPairs`.**

**Mode-indexed twelve-component profiles** · abbreviation. `Profiles`: Profiles assign a complex twelve-component velocity-gradient vector to each mode label and half-plane point. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpandPairs.lean#L19).

**Measurable profiles with summable energy** · structure. `Good`: The Good predicate packages component measurability, radial square integrability for each mode and summability of those mode energies. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpandPairs.lean#L21).

**One weighted coupling contribution** · definition. `pairTerm`: A pair term is the radius times the real sesquilinear coupling of one profile mode with the harmonically shifted second profile. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpandPairs.lean#L26).

**The integrated mode-pairing sum** · definition. `pairSum`: The pair sum adds the integrated pair terms over all mode labels and a finite harmonic set. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpandPairs.lean#L29).

**Bounded measurable coupling data** · structure. `CouplingOK`: The coupling predicate requires a measurable region with nonnegative radius and measurable, uniformly bounded matrix entries for each selected harmonic. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpandPairs.lean#L33).

**Bound the twelve-component coupling** · theorem. `norm_sesq12_le`: An entrywise matrix bound controls the sesquilinear form by six times that bound times the sum of the squared input norms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpandPairs.lean#L40).

**Pair terms are measurable** · theorem. `pairTerm_meas`: Admissible coupling data and measurable profiles give almost everywhere strongly measurable pair terms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpandPairs.lean#L63).

**Control a pair term by its two energies** · theorem. `pairTerm_bound`: The pair-term norm is bounded by six times the matrix bound times the sum of the two radial mode energies. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpandPairs.lean#L72).

**Pair terms are integrable** · theorem. `pairTerm_integrable`: Admissible coupling data and Good profiles make each pair term integrable on the region. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpandPairs.lean#L87).

**Integrated pair terms are summable** · theorem. `pairTerm_summable`: Admissible coupling data and summable profile energies make the sequence of integrated pair terms summable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpandPairs.lean#L95).

**Add profiles in the first pair input** · theorem. `pairTerm_add_left`: The pointwise pair term is additive in its first profile input. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpandPairs.lean#L109).

**Add profiles in the second pair input** · theorem. `pairTerm_add_right`: The pointwise pair term is additive in its second profile input. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpandPairs.lean#L116).

**Add profiles in the first summed input** · theorem. `pairSum_add_left`: Under the Good-profile and coupling conditions, the integrated pair sum is additive in its first input. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpandPairs.lean#L123).

**Add profiles in the second summed input** · theorem. `pairSum_add_right`: Under the Good-profile and coupling conditions, the integrated pair sum is additive in its second input. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpandPairs.lean#L138).

**The integrated pairing is symmetric** · theorem. `pairSum_symm`: For a harmonic set closed under negation and a coupling with the required reversal symmetry, the pair sum of Good profiles is unchanged by exchanging its inputs. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpandPairs.lean#L153).

**Radial squared mass is measurable** · theorem. `sqMass_meas`: A measurable profile has almost everywhere strongly measurable radial squared mass. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpandPairs.lean#L172).

**Integrated radial mass is nonnegative** · theorem. `sqMass_nonneg`: On a region with nonnegative radius, the integral of the radial squared profile norm is nonnegative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpandPairs.lean#L176).

**Energy domination preserves Good** · theorem. `good_comb`: A measurable profile dominated in squared norm by twice the energies of two Good profiles is Good on a measurable region with nonnegative radius. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpandPairs.lean#L180).

**Good profiles are closed under addition** · theorem. `good_add`: The sum of two Good profiles is Good under the region measurability and nonnegative-radius assumptions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpandPairs.lean#L203).

**Differences of Good profiles are Good** · theorem. `good_sub`: The difference of two Good profiles is Good under the region measurability and nonnegative-radius assumptions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpandPairs.lean#L210).

**Mode restriction preserves Good profiles** · theorem. `good_restrict`: Restricting a Good profile to any set of mode labels preserves the Good property. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpandPairs.lean#L217).

**Finite continuous profiles are Good** · theorem. `good_finite`: A continuous profile supported on finitely many mode labels is Good on a compact region. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpandPairs.lean#L237).

**Source section `Split`.**

**Split the full quadratic pair sum** · theorem. `split_core`: Under the support, symmetry and disjointness hypotheses, the full self-pairing splits into the low-profile term, twice the three resolved-tail, band and remaining cross terms, and the tail self-pairing. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpandPairs.lean#L248).

**Source section `Integrate`.**

**Integrated pair norms are summable** · theorem. `pairTerm_normSummable`: The sum over labels of the integrals of pair-term norms converges under the Good-profile and coupling conditions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpandPairs.lean#L302).

**Interchange the series and integral** · theorem. `pairSum_integral`: The integral of the pointwise mode and harmonic sum equals the sum of the integrated pair terms under the absolute-summability bounds. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialExpandPairs.lean#L318).

### Breakdown.CertCell.AssemblyPotentialGroups

This file bounds groups of model interactions by balanced charges on resolved modes and their partners, then checks that the allocated entry charges pay those costs. Appendix B.3: support for the grouped potential interactions.

**The split charge is nonnegative** · theorem. `splitCharge_nonneg`: Nonnegative charge coefficients give a nonnegative split charge on velocity and gradient inputs. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroups.lean#L24).

**Rewrite the generic charge coefficient** · theorem. `half_sqrt_nine_halves`: Half of the square root of nine halves equals three divided by twice the square root of two. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroups.lean#L35).

**The class charge is nonnegative** · theorem. `classCharge_nonneg`: The admissible class coefficient and nonnegative strain and gradient bounds give a nonnegative class charge. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroups.lean#L47).

**Class and group charge formulas agree** · theorem. `classCharge_group`: Using a group entry for the class-charge parameters gives exactly its group charge. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroups.lean#L55).

**Both class coefficients are nonnegative** · theorem. `Breakdown.CertCell.AssemblyPotentialGroups.kappa_nonneg`: Either allowed class coefficient, the square root of seven halves or of nine halves, is nonnegative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroups.lean#L61).

**Second modes inherit derivative symmetry** · theorem. `modeSecond_swap`: Symmetry of the second derivative in its derivative slots passes to its harmonic coefficient. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroups.lean#L64).

**A symmetric Hessian has trace-free curl** · theorem. `curlSecond_trace`: The curl-gradient tensor formed from a second derivative symmetric in its derivative slots has zero trace. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroups.lean#L74).

**Bound one wave slice by two charges** · theorem. `sliceWaveBound`: A valid cross-wave entry bounds twice the norm of a slice interaction by balanced cross charges on its source and partner modes. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroups.lean#L96).

**Sum temporal slices to recover all modes** · theorem. `sum_slices`: Summing the first-coordinate slices over the second-coordinate image of a finite mode set recovers its full sum. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroups.lean#L150).

**A nonnegative slice sum is bounded** · theorem. `sum_slices_le`: A selected collection of shifted slices has nonnegative sum at most the sum over the full partner-mode set. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroups.lean#L163).

**Bound a group of wave interactions** · theorem. `groupWaveBound`: A valid wave entry bounds the grouped interaction by balanced class charges, with the trace-free condition required for the sharper square-root-of-seven-halves coefficient. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroups.lean#L184).

**Bound one wave interaction** · theorem. `pairWaveBound`: The wave-entry assumptions bound an individual interaction by balanced class charges, using the trace-free premise when the sharper coefficient is chosen. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroups.lean#L239).

**Regroup uncovered cross interactions** · theorem. `regroupCross`: A covering, disjoint group assignment rewrites the resolved-to-remaining interaction sum as the sum over its groups and partner labels. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroups.lean#L251).

**Group waves have trace-free curl** · theorem. `groupWave_traceFree`: The assembled group wave has zero trace in its reconstructed curl-gradient field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroups.lean#L306).

**Model triples equal group-wave triples** · theorem. `groupModelTriple_eq`: The group-wave strain and vorticity-gradient data give the same triple as the corresponding model plane values. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroups.lean#L316).

**Label reflection commutes with negation** · theorem. `labelFlip_neg`: Reflecting a negated label gives the negative of its reflected label. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroups.lean#L339).

**Negative model plane values conjugate** · theorem. `matPlaneValue_neg`: The model matrix plane value at a negated label is the complex conjugate of its original value. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroups.lean#L342).

**Absent model labels give zero triples** · theorem. `modelTriple_off_model`: Under the potential conditions, the model triple at a harmonic label vanishes on the cell when the negated label is absent from the model support. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroups.lean#L350).

**Groups control the remaining cross sum** · theorem. `groupCrossBound`: Potential conditions and the disjoint covering hypotheses bound the resolved-to-remaining model interaction by the summed balanced group charges. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroups.lean#L368).

**Entry charges pay all partner costs** · theorem. `partnerCostLeCharges`: For modes outside both resolved and band sets, the potential conditions make the entry charges dominate the group, leakage, credit, pairing and potential-remainder costs on nonnegative energy weights. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroups.lean#L417).

**Add the first bilinear field input** · theorem. `modelBilin_add_left`: The model bilinear form distributes over addition of its first velocity-gradient pair. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroups.lean#L462).

**Add the second bilinear field input** · theorem. `modelBilin_add_right`: The model bilinear form distributes over addition of its second velocity-gradient pair. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroups.lean#L468).

**Scale the first bilinear field input** · theorem. `modelBilin_smul_left`: The model bilinear form is complex linear in its first velocity-gradient pair. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroups.lean#L474).

**Scale the second bilinear field input** · theorem. `modelBilin_smul_right`: The model bilinear form is complex linear in its second velocity-gradient pair. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroups.lean#L481).

**Add the first triple field input** · theorem. `modelTriple_add_left`: The model triple distributes over addition of its first velocity-gradient pair. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroups.lean#L488).

**Add the second triple field input** · theorem. `modelTriple_add_right`: The model triple distributes over addition of its second velocity-gradient pair. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroups.lean#L495).

**Scale the first triple field input** · theorem. `modelTriple_smul_left`: The model triple is complex linear in its first velocity-gradient pair. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroups.lean#L502).

**Scale the second triple field input** · theorem. `modelTriple_smul_right`: The model triple is complex linear in its second velocity-gradient pair. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroups.lean#L509).

**Expand a sum in the first triple input** · theorem. `modelTriple_sum_left`: The model triple of a finite linear combination in its first field input is the same linear combination of the individual triples. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroups.lean#L516).

**Expand a sum in the second triple input** · theorem. `modelTriple_sum_right`: The model triple of a finite linear combination in its second field input is the same linear combination of the individual triples. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroups.lean#L530).

**Expand packed velocity in the basis** · theorem. `velOf_eq_sum`: The velocity extracted from a packed vector is the coordinate-weighted sum of the basis velocities. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroups.lean#L544).

**Expand packed gradient in the basis** · theorem. `gradOf_eq_sum`: The gradient extracted from a packed vector is the coordinate-weighted sum of the basis gradients. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroups.lean#L548).

**Expand conjugated packed velocity** · theorem. `star_velOf_eq_sum`: The conjugated extracted velocity is the sum of conjugated basis velocities weighted by the conjugated coordinates. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroups.lean#L552).

**Expand conjugated packed gradient** · theorem. `star_gradOf_eq_sum`: The conjugated extracted gradient is the sum of conjugated basis gradients weighted by the conjugated coordinates. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroups.lean#L557).

**The model matrix recovers its triple** · theorem. `sesq_modelTriple`: The sesquilinear form of the model-triple matrix equals the model triple evaluated on the packed input fields with the first input conjugated. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroups.lean#L562).

**Swap the two field inputs** · theorem. `modelTriple_swap`: The model triple is unchanged by exchanging its two velocity-gradient pairs. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroups.lean#L575).

**Conjugate every input of the triple** · theorem. `Breakdown.CertCell.AssemblyPotentialGroups.conj_modelTriple`: Conjugating the model triple equals the triple of the conjugated tensors, velocities and gradients. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroups.lean#L580).

**Convert stretching to the model triple** · theorem. `stretchTriple_eq_modelTriple`: The stretching triple equals the model triple formed from the symmetric gradient and the curl of the second derivative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroups.lean#L588).

**Negating a harmonic label** · theorem. `Breakdown.CertCell.AssemblyPotentialGroups.labelHarmonic_neg`: The harmonic associated to a negated label is the negative of the original harmonic. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroups.lean#L593).

**Negative real-field modes conjugate** · theorem. `modeAverage_neg`: For a real-valued input field, the mode average at a negative frequency is the complex conjugate of the original average. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroups.lean#L600).

**Negative gradient labels conjugate** · theorem. `labelGrad_neg`: The gradient mode at the negative label is the star of the original gradient mode. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroups.lean#L620).

**Negative Hessian modes are conjugates** · theorem. `secondModes_neg`: The second-derivative mode at the negative label is the star of the original mode. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroups.lean#L626).

**Reverse the real physical coupling** · theorem. `sesq_realCoupling`: The real physical-coupling form equals the stretching triple at the negated label with the packed field roles reversed and the matching conjugation. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroups.lean#L632).

**Reverse the real model coupling** · theorem. `sesq_couplingModel`: The real model-coupling form equals the model triple at the negated harmonic label with the corresponding packed inputs and conjugation. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroups.lean#L651).

### Breakdown.CertCell.AssemblyPotentialGroupsChargeAux

This file proves the elementary positivity and weighted integrability estimates needed to add the potential charges. Appendix B.3: analytic support for the potential charge stage.

**The split charge is nonnegative** · theorem. `splitCharge_nonneg`: Nonnegative curl, gradient and velocity coefficients give a nonnegative split charge. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsChargeAux.lean#L22).

**Both class coefficients are nonnegative** · theorem. `Breakdown.CertCell.AssemblyPotentialGroupsChargeAux.kappa_nonneg`: Either allowed class coefficient, the square root of seven halves or of nine halves, is nonnegative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsChargeAux.lean#L33).

**Cell radii are nonnegative** · theorem. `Breakdown.CertCell.AssemblyPotentialGroupsChargeAux.rect_fst_nonneg`: Every point of a valid cell rectangle has a nonnegative radial coordinate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsChargeAux.lean#L36).

**Complex squared norm is nonnegative** · theorem. `Breakdown.CertCell.AssemblyPotentialGroupsChargeAux.cnormSq_nonneg'`: The sum of squared complex-component norms is nonnegative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsChargeAux.lean#L40).

**Alternating symbol has size at most one** · theorem. `alternatingSymbol_abs_le`: Every component of the three-dimensional alternating symbol has absolute value at most one. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsChargeAux.lean#L43).

**Bound curl energy by gradient energy** · theorem. `Breakdown.CertCell.AssemblyPotentialGroupsChargeAux.curl_cnormSq_le`: The complex squared norm of the curl is at most twenty-seven times the complex squared norm of the gradient. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsChargeAux.lean#L47).

**Packed energy splits into its two parts** · theorem. `gradOf_velOf_cnormSq`: The gradient and velocity squared norms extracted from a packed vector sum to its twelve-coordinate squared norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsChargeAux.lean#L70).

**Bound the split charge by packed energy** · theorem. `Breakdown.CertCell.AssemblyPotentialGroupsChargeAux.splitCharge_le`: With nonnegative coefficients, the split charge is bounded by twenty-seven times the curl coefficient plus the gradient and velocity coefficients, multiplied by the packed squared norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsChargeAux.lean#L75).

**Coordinate measurability gives a profile** · theorem. `profile_aemeasurable`: Almost everywhere strong measurability of each coordinate implies almost everywhere measurability of the packed profile. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsChargeAux.lean#L93).

**The split charge depends continuously** · theorem. `Breakdown.CertCell.AssemblyPotentialGroupsChargeAux.splitCharge_continuous`: The split charge is continuous as a function of the packed velocity-gradient vector. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsChargeAux.lean#L97).

**Finite radial energy makes charges L1** · theorem. `Breakdown.CertCell.AssemblyPotentialGroupsChargeAux.chargeY_integrable`: Nonnegative charge coefficients, measurable profile coordinates, integrable radial squared norm and almost everywhere nonnegative radius make the radial split charge integrable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsChargeAux.lean#L102).

**Nonnegative group-charge coefficients** · theorem. `Breakdown.CertCell.AssemblyPotentialGroupsChargeAux.groupCoeffs`: The potential conditions make all three coefficients of each group charge nonnegative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsChargeAux.lean#L117).

**High-part coefficients are nonnegative** · theorem. `high_nonneg`: The potential conditions make the high-part strain and gradient coefficients nonnegative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsChargeAux.lean#L128).

**The long factor is positive** · theorem. `longFactor_pos`: A positive long-balance parameter makes the long factor strictly positive at every label. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsChargeAux.lean#L134).

**Long-charge coefficients are nonnegative** · theorem. `longCoeffs`: The potential conditions make the curl, gradient and velocity coefficients of the long charge nonnegative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsChargeAux.lean#L141).

### Breakdown.CertCell.AssemblyPotentialGroupsChargeCore

This file sums the per-mode charge estimates to prove that all stage costs are covered by the allocated extra charge. Appendix B.3: the potential charge-stage conclusion.

**Source namespace `Breakdown.CertCell.Assembly.Internal`.**

**Bound a weighted nonnegative sum** · theorem. `weighted_abs_le`: The absolute value of a weighted sum of nonnegative entries is at most the sum of absolute weights times the sum of the entries. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsChargeCore.lean#L20).

**Potential conditions cover charge costs** · theorem. `chargeStage_of`: Assembly regularity, physical-field regularity and the potential conditions imply the charge-stage inequality. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsChargeCore.lean#L28).

**Source namespace `Breakdown.CertCell.Assembly`.**

**Prove the charge-stage interface** · theorem. `chargeStageHolds`: The pointwise charge bounds and their integrability establish the charge-stage interface. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsChargeCore.lean#L354).

### Breakdown.CertCell.AssemblyPotentialGroupsChargePartsCore

This file identifies charge formulas with physical mode energies, verifies the band and deactivated-mode budgets, and integrates the credit and charge contributions. Appendix B.3: support for allocating potential costs mode by mode.

**Two curl sign conventions agree** · theorem. `alternatingSymbol_eq_permSign`: The alternating symbol and the permutation-sign formula agree after conversion to complex scalars. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsChargePartsCore.lean#L20).

**Read the physical band gradient** · theorem. `gradOf_bandProfile`: The gradient extracted from the band profile consists of the physical gradient coefficients at that label. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsChargePartsCore.lean#L24).

**Read the physical band velocity** · theorem. `velOf_bandProfile`: The velocity extracted from the band profile consists of the physical velocity coefficients at that label. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsChargePartsCore.lean#L31).

**Packed curl energy equals mode energy** · theorem. `curl_bandProfile`: The squared curl norm of the packed band gradient equals the defined mode-curl energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsChargePartsCore.lean#L37).

**Packed and mode gradient energies agree** · theorem. `strain_bandProfile`: The squared norm of the packed band gradient equals the defined mode-strain energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsChargePartsCore.lean#L44).

**Packed and mode velocity energies agree** · theorem. `vel_bandProfile`: The squared norm of the packed band velocity equals the defined mode-velocity energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsChargePartsCore.lean#L51).

**Expand the high-part partner charge** · theorem. `highPartner_bandProfile`: The high-part charge on a band profile equals its prescribed linear combination of the mode-curl, gradient and velocity energies. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsChargePartsCore.lean#L57).

**Expand the band-profile split charge** · theorem. `splitCharge_bandProfile`: The split charge on a band profile is the corresponding coefficient-weighted sum of mode-curl, gradient and velocity energies. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsChargePartsCore.lean#L66).

**Split the band-profile squared norm** · theorem. `profile_sq_split`: The squared norm of all twelve band-profile coordinates is the sum of mode-strain and mode-velocity energies. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsChargePartsCore.lean#L73).

**Bound coordinate weights by block maxima** · theorem. `bandWeight_le`: The weighted band-profile energy is at most the largest gradient-coordinate weight times mode-strain energy plus the largest velocity-coordinate weight times mode-velocity energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsChargePartsCore.lean#L78).

**Mode energies are radially integrable** · theorem. `modeSq_integrable`: The physical regularity assumptions make the radius-weighted curl, gradient and velocity mode energies integrable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsChargePartsCore.lean#L104).

**Expand the long-part partner charge** · theorem. `longPartner_bandProfile`: The long-part charge on a band profile is its long factor times the prescribed curl, gradient and velocity energy combination. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsChargePartsCore.lean#L162).

**Expand the epsilon partner charge** · theorem. `epsPartner_bandProfile`: The epsilon partner charge on a band profile equals its prescribed curl, gradient and velocity energy combination. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsChargePartsCore.lean#L171).

**All three mode energies are nonnegative** · theorem. `modeSq_nonneg`: The mode-curl, gradient and velocity energies are nonnegative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsChargePartsCore.lean#L180).

**Extra charges cover band-mode costs** · theorem. `bandPointwise`: For a band label and a point in the cell, the potential conditions make the extra-charge density dominate the weighted band energy, potential partner charges, band allowances and pairing slack. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsChargePartsCore.lean#L191).

**Recognize a deactivated partner label** · theorem. `mem_deactPartners_iff`: For a label outside both the resolved and band sets, being a deactivated partner is equivalent to having its difference from some resolved label in the potential-harmonic set. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsChargePartsCore.lean#L213).

**Extra charges cover deactivated costs** · theorem. `deactivatedPointwise`: For a label outside both resolved and band sets, the potential conditions bound the leakage, group, potential, pairing-slack and credit costs by its extra-charge density. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsChargePartsCore.lean#L225).

**Combine the per-mode charge budgets** · theorem. `allPointwise`: The band and deactivated-mode cases combine into a pointwise bound of all allocated costs by the extra-charge density. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsChargePartsCore.lean#L301).

**Move a fixed condition into an integral** · theorem. `ite_setIntegral`: Selecting an integral by a fixed proposition is equivalent to integrating the selected integrand. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsChargePartsCore.lean#L346).

**Fixed zero mask preserves integrability** · theorem. `integrable_ite`: Choosing either an integrable function or zero according to a fixed proposition gives an integrable function. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsChargePartsCore.lean#L350).

**Positive azimuth order gives injectivity** · theorem. `labelHarmonic_inj`: For azimuth order at least one, equal labeled harmonics have equal labels. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsChargePartsCore.lean#L356).

**Credit-patch regions are measurable** · theorem. `region_measurable`: A credit patch satisfying its region conditions has a measurable region. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsChargePartsCore.lean#L365).

**Negating a harmonic label** · theorem. `Breakdown.CertCell.AssemblyPotentialGroupsChargePartsCore.labelHarmonic_neg`: The harmonic associated to a negated label is the negative of the original harmonic. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsChargePartsCore.lean#L369).

**Identify a harmonic up to sign** · theorem. `labelHarmonic_eq_or_neg`: For positive azimuth order and the stated harmonic representative, equality to either signed harmonic is equivalent to equality to either signed label. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsChargePartsCore.lean#L372).

**Expand weighted credit demand** · theorem. `creditDemand_mul`: Multiplying velocity-credit demand by a scalar gives the finite sum of the matching signed-harmonic patch charges, each restricted to its region. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsChargePartsCore.lean#L382).

**A patch credit term is integrable** · theorem. `creditTerm_integrable`: The regularity and patch bounds make each charge times radial mode-velocity energy integrable on the cell. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsChargePartsCore.lean#L394).

**The total velocity-credit density is L1** · theorem. `creditIntegrable`: Summing the finitely many integrable patch contributions makes the full velocity-credit density integrable on the cell. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsChargePartsCore.lean#L405).

**Write credit as a finite mode sum** · theorem. `creditAmount_eq`: For positive azimuth order, nonzero patch labels, a finite set containing both signed representatives and integrable patch terms, the total credit equals the sum of integrated velocity-credit demands. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsChargePartsCore.lean#L427).

**Enlarge a finite sum with zero terms** · theorem. `sum_eq_sum_ite`: A sum over a finite subset equals the sum over a containing finite set with zero inserted outside the subset. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsChargePartsCore.lean#L518).

**Integrate the full per-mode budget** · theorem. `perModeCharge`: Integrating the pointwise allocation and its integrable components bounds the total cost of a mode by its integrated extra charge. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsChargePartsCore.lean#L522).

### Breakdown.CertCell.AssemblyPotentialGroupsStage

This file turns grouped cross-interaction bounds into an integrated lower bound for the potential group stage. Appendix B.3: support for bounding resolved-to-deactivated model interactions.

**Source namespace `Breakdown.CertCell.Assembly.Internal`.**

**The grouped model cross-bound interface** · interface proposition. `ModelCrossBoundStatement`: The interface requires potential conditions and a disjoint group cover to bound resolved-to-remaining model interactions by balanced source and partner group charges. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsStage.lean#L19).

Proved by `Breakdown.CertCell.Assembly.Internal.groupCrossBound`. The companion records the supplying lambda or structure field.

**The real model-coupling identity** · interface proposition. `CouplingModelReStatement`: The interface identifies the real model-coupling matrix form with the model triple at the negated harmonic label under the potential conditions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsStage.lean#L39).

Proved by `Breakdown.CertCell.Assembly.Internal.sesq_couplingModel`. The companion records the supplying lambda or structure field.

**Cell radii are nonnegative** · theorem. `Breakdown.CertCell.AssemblyPotentialGroupsStage.rect_fst_nonneg`: Every point of a valid cell rectangle has a nonnegative radial coordinate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsStage.lean#L50).

**Upper-profile components are continuous** · theorem. `upperProfiles_continuous`: Each upper-profile component is continuous in the radial-height point. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsStage.lean#L54).

**Squared complex norm is nonnegative** · theorem. `Breakdown.CertCell.AssemblyPotentialGroupsStage.cnormSq_nonneg'`: The sum of squared complex-component norms is nonnegative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsStage.lean#L66).

**The alternating symbol is bounded** · theorem. `alternatingSymbol_abs_le`: Every component of the alternating symbol has absolute value at most one. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsStage.lean#L69).

**Bound curl energy by gradient energy** · theorem. `Breakdown.CertCell.AssemblyPotentialGroupsStage.curl_cnormSq_le`: The complex squared norm of the curl is at most twenty-seven times the complex squared norm of the gradient. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsStage.lean#L73).

**Packed energy splits into its two parts** · theorem. `gradOf_velOf_cnormSq`: The extracted gradient and velocity squared norms sum to the twelve-coordinate squared norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsStage.lean#L96).

**Bound split charge by packed energy** · theorem. `Breakdown.CertCell.AssemblyPotentialGroupsStage.splitCharge_le`: With nonnegative coefficients, the split charge is bounded by twenty-seven times the curl coefficient plus the gradient and velocity coefficients, multiplied by the packed squared norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsStage.lean#L101).

**Coordinate measurability gives a profile** · theorem. `groupsProfile_aemeasurable`: Almost everywhere strong measurability of each coordinate implies almost everywhere measurability of the packed profile. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsStage.lean#L119).

**The split charge depends continuously** · theorem. `Breakdown.CertCell.AssemblyPotentialGroupsStage.splitCharge_continuous`: The split charge is continuous as a function of the packed velocity-gradient vector. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsStage.lean#L123).

**Finite radial energy makes charges L1** · theorem. `Breakdown.CertCell.AssemblyPotentialGroupsStage.chargeY_integrable`: Nonnegative charge coefficients, measurable profile coordinates, integrable radial squared norm and almost everywhere nonnegative radius make the radial split charge integrable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsStage.lean#L128).

**Nonnegative group-charge coefficients** · theorem. `Breakdown.CertCell.AssemblyPotentialGroupsStage.groupCoeffs`: The potential conditions make all three coefficients of each group charge nonnegative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsStage.lean#L143).

**Group charges are nonnegative** · theorem. `groupCharge_nonneg`: The potential conditions give a nonnegative group charge for every velocity-gradient input. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsStage.lean#L154).

**Group charges depend continuously** · theorem. `groupCharge_continuous`: Each group charge is continuous as a function of the packed velocity-gradient input. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsStage.lean#L162).

**A zero second input gives zero pairing** · theorem. `sesq_zero_right`: A sesquilinear form vanishes when its second vector input is zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsStage.lean#L167).

**The zero matrix gives zero pairing** · theorem. `sesq_zero_matrix`: The sesquilinear form of the zero matrix is zero for every pair of inputs. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsStage.lean#L170).

**Rewrite a sum over an intersection** · theorem. `sum_inter_eq_ite`: A finite sum over an intersection equals the sum over the first set with zero outside the second. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsStage.lean#L173).

**A zero first field gives zero triple** · theorem. `modelTriple_zero_left`: The model triple vanishes when its first velocity-gradient pair is zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsStage.lean#L177).

**A zero second field gives zero triple** · theorem. `modelTriple_zero_right`: The model triple vanishes when its second velocity-gradient pair is zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsStage.lean#L181).

**The zero field has zero group charge** · theorem. `groupCharge_zero`: The group charge of zero velocity and zero gradient is zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsStage.lean#L185).

**Groups cover the cross interactions** · theorem. `crossCover`: The potential conditions assign every relevant resolved-to-remaining interaction to a group containing its source, partner and harmonic labels. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsStage.lean#L189).

**Group harmonics belong to the label set** · theorem. `crossSub`: Every group harmonic lies in the negated potential-harmonic label set. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsStage.lean#L201).

**Group charges bound a model pair** · theorem. `pairModelBound`: The grouped cross-bound and potential conditions bound an individual model interaction by the sum of balanced group charges on its two inputs. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsStage.lean#L207).

**Cell-polynomial evaluation is continuous** · theorem. `cellPoly_eval_continuous`: A cell polynomial evaluated in its cell coordinates is continuous on the radial-height plane. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsStage.lean#L261).

**Model matrix entries are measurable** · theorem. `matPlaneValue_measurable`: Each harmonic matrix plane-value component is measurable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsStage.lean#L265).

**Model matrix fields are measurable** · theorem. `matPlane_measurable`: The complete harmonic matrix plane-value map is measurable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsStage.lean#L272).

**The real model triple is continuous** · theorem. `modelRe_continuous`: The real model triple depends continuously on its two tensor inputs and two packed field inputs. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsStage.lean#L276).

**The model pairing density is integrable** · theorem. `modelIntegrand_integrable`: The stated profile regularity and group bounds make the radius-weighted real model-coupling density integrable on the cell. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsStage.lean#L284).

**Rewrite one model-pairing row** · theorem. `modelPair_row_rewrite`: The row sum over deactivated partners equals the real sum of model triples over the corresponding allowed harmonic shifts. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsStage.lean#L349).

**Group charges bound cross terms below** · theorem. `groupPointwise`: The resolved-to-deactivated model cross term is bounded below pointwise by the negative sum of balanced source and partner group charges. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsStage.lean#L391).

**Integrate the grouped cross bound** · theorem. `groupStage_of`: The model cross-bound and real-coupling interfaces, physical-field regularity and potential conditions imply the group-stage inequality. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsStage.lean#L449).

**Assemble the group-stage interface** · theorem. `groupStageHolds_of`: The model cross-bound and real-coupling interfaces together establish the group-stage interface. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsStage.lean#L533).

**Source namespace `Breakdown.CertCell.Assembly`.**

**Prove the group-stage interface** · theorem. `groupStageHolds`: The verified model-group estimates and integrability arguments establish the group-stage interface. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialGroupsStage.lean#L540).

### Breakdown.CertCell.AssemblyPotentialLeaf

This file compares the physical cell density with its local matrix, box penalty and Hessian floors, then separates the polynomial low part and tail. Appendix B.3: support for the resolved leaf estimate.

**Source section `Leaf`.**

**Leaf data bound the physical density** · theorem. `leaf_point`: For a valid cell and certified leaf values, the local matrix term, box penalty and two Hessian-floor terms are bounded pointwise by the resolved label density. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialLeaf.lean#L21).

**Integrate the leaf-density bound** · theorem. `leaf_key`: The integrability hypotheses turn the pointwise leaf estimate into the corresponding inequality between its four integrated contributions and the physical density integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialLeaf.lean#L56).

**Identify the polynomial leaf energy** · theorem. `leaf_low`: The sum of the low polynomial-mode matrix energies equals the local-matrix energy evaluated on the low profile extracted from the physical cell state. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialLeaf.lean#L98).

**Source namespace `Breakdown.CertCell.Assembly`.**

**Prove the low-and-tail split** · theorem. `lowTailSplit_holds`: The projection identities establish the low-tail splitting interface. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialLeaf.lean#L155).

**Prove the leaf-splitting interface** · theorem. `leafSplit_holds`: The physical leaf bound, polynomial identity and low-tail split establish the leaf-splitting interface. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialLeaf.lean#L175).

### Breakdown.CertCell.AssemblyPotentialLeafParts

This file supplies coordinate identities, projection formulas and integrability estimates for the resolved leaf calculation. Appendix B.3: analytic support for the leaf decomposition.

**Source namespace `Breakdown.CertCell.Assembly.Internal.PotentialLeaf`.**

**Split a packed field into low and tail** · theorem. `pairVec_split`: A packed velocity-gradient vector equals the packed low part plus the packed difference from that low part. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialLeafParts.lean#L25).

**Read a packed gradient coordinate** · theorem. `pairVec_grad`: The appropriate first-nine coordinate of the packed vector equals its gradient component. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialLeafParts.lean#L31).

**Read a packed velocity coordinate** · theorem. `pairVec_vel`: The appropriate last-three coordinate of the packed vector equals its velocity component. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialLeafParts.lean#L41).

**Split the packed squared norm** · theorem. `norms_pairVec`: The squared coordinate norm of a packed vector equals the gradient squared norm plus the velocity squared norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialLeafParts.lean#L48).

**A singleton mode sum has one term** · theorem. `sum_single`: A sum over a mode set consisting of one label equals the term at that label. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialLeafParts.lean#L53).

**The cell line weight is continuous** · theorem. `weight_continuous`: The line-weight function of a cell is continuous. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialLeafParts.lean#L61).

**Complex coefficients combine real parts** · theorem. `coef_lift`: The cell coefficient of a complex field formed from two real fields equals the first coefficient plus i times the second coefficient. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialLeafParts.lean#L67).

**Source section `Low`.**

**Low gradients are cell projections** · theorem. `low_grad_eq`: For a resolved label, the low gradient extracted from the physical cell state equals the cell-polynomial projection of the physical gradient coefficient. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialLeafParts.lean#L98).

**Low velocities are cell projections** · theorem. `low_vel_eq`: For a resolved label, the low velocity extracted from the physical cell state equals the cell-polynomial projection of the physical velocity coefficient at the prescribed lower degree. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialLeafParts.lean#L136).

**Source namespace `Breakdown.CertCell.Assembly.Internal.PotentialLeaf`.**

**Bound a packed quadratic matrix form** · theorem. `sesq_norm_le`: An entrywise matrix bound controls the norm of the quadratic sesquilinear form by 144 times that bound times the packed squared norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialLeafParts.lean#L181).

**The weighted matrix energy is integrable** · theorem. `sesq_integrable`: The stated matrix bounds and measurable profile square bounds make the radius-weighted complex matrix energy integrable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialLeafParts.lean#L206).

**Bound the box penalty by packed energy** · theorem. `box_bound`: The absolute box penalty is bounded by the packed squared norm times twenty-seven times the absolute curl coefficient plus the absolute gradient and velocity coefficients. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialLeafParts.lean#L224).

**Bound a real norm by signed parts** · theorem. `enorm_le_split`: The extended norm of a real number is at most the sum of the extended nonnegative values of that number and its negative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialLeafParts.lean#L244).

**Write curl using permutation signs** · theorem. `curl_as_sum`: Each curl component is the double sum of gradient entries multiplied by the corresponding permutation signs. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialLeafParts.lean#L252).

**A coordinate selector extracts one entry** · theorem. `single_sum`: The double sum weighted by a single-coordinate indicator equals the selected matrix entry. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialLeafParts.lean#L257).

**Hessian slope energies are integrable** · theorem. `slope_integrable`: The second-derivative regularity assumptions make the radius-weighted slope and curl-slope squared energies integrable on the cell. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialLeafParts.lean#L261).

**Source section `Leaf`.**

**Measurable physical derivative arrays** · theorem. `array_measurable`: The physical gradient and velocity arrays are almost everywhere strongly measurable on the cell rectangle. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialLeafParts.lean#L296).

**Curl energy depends continuously** · theorem. `curlSq_continuous`: The squared curl norm is continuous as a function of the gradient matrix. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialLeafParts.lean#L311).

**Gradient energy depends continuously** · theorem. `sumSq_continuous`: The sum of squared gradient-component norms is continuous. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialLeafParts.lean#L315).

**Velocity energy depends continuously** · theorem. `vecSq_continuous`: The sum of squared velocity-component norms is continuous. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialLeafParts.lean#L319).

**The weighted box penalty is integrable** · theorem. `box_integrable`: The radius-weighted box penalty of the physical gradient and velocity is integrable on the cell. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialLeafParts.lean#L323).

**Physical matrix pairing is integrable** · theorem. `pair_integrable`: The matrix bounds and physical-field regularity make the radius-weighted real quadratic pairing integrable on the cell. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialLeafParts.lean#L360).

**The physical label density is integrable** · theorem. `density_integrable`: Physical-field regularity, finite cell pieces and a valid cell tuple imply integrability of the radius-weighted label density on the cell. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialLeafParts.lean#L372).

### Breakdown.CertCell.AssemblyPotentialLink

This file assembles the model, sharp, epsilon, group and charge estimates into the potential-stage interface, with progressively fewer unfilled inputs. Appendix B.3: the linking step for the potential-stage estimate.

**Prove the torus long-part estimate** · theorem. `torusLongStatement_holds`: The torus calculation establishes the long-part statement used in the model comparison. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialLink.lean#L14).

**Prove the model-stage interface** · theorem. `modelStageHolds`: The pointwise comparison and its integrated form establish the model-stage interface. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialLink.lean#L18).

**Assemble all potential-stage inputs** · theorem. `potentialStageHolds_of`: The stretching-expansion, sharp, resolved-epsilon, group and charge interfaces together imply the potential-stage interface. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialLink.lean#L23).

**Potential stage from sharp parts** · theorem. `potentialStageHolds_of_sharpParts`: The stretching expansion, sharp absorption and regularity statements, resolved epsilon, group and charge interfaces imply the potential-stage interface. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialLink.lean#L28).

**Use epsilon, group and charge inputs** · theorem. `potentialStageHolds_of_epsGroupCharge`: The resolved-epsilon, group and charge interfaces suffice for the potential stage once the other component interfaces are supplied by their proofs. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialLink.lean#L33).

**The epsilon input completes the stage** · theorem. `potentialStageHolds_of_epsResolved`: The resolved-epsilon interface completes the potential stage using the already proved stretching, sharp, group and charge components. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialLink.lean#L37).

### Breakdown.CertCell.AssemblyPotentialModel

This file converts the pointwise model-versus-physical coupling comparison into the integrated model-stage estimate while tracking epsilon, long and high-frequency charges. Appendix B.3: support for replacing the physical coupling by the finite model.

**Source section `Conclusion`.**

**Scale the two-class comparison** · theorem. `scale_combo`: Multiplying the supplied two-class interaction comparison by a nonnegative scalar preserves the inequality with all six charge contributions scaled consistently. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModel.lean#L27).

**Integrate a finite double sum** · theorem. `integral_double_sum`: For integrable summands, the integral of a finite double sum equals the double sum of their integrals. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModel.lean#L41).

**A finite double sum is integrable** · theorem. `integrable_double_sum`: A finite double sum of integrable functions is integrable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModel.lean#L48).

**Integrate a finite sum term by term** · theorem. `integral_single_sum`: The integral of a finite sum of integrable functions equals the sum of their integrals. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModel.lean#L53).

**Triple-matrix entries are continuous** · theorem. `continuous_tripleMatrix_entry`: Continuous strain and vorticity-gradient inputs give continuous entries of the associated triple matrix. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModel.lean#L57).

**Integrate the two-term combination** · theorem. `integral_combo_two`: The integral of an integrable first term plus twice an integrable second term is the corresponding linear combination of their integrals. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModel.lean#L64).

**Integrate six charge contributions** · theorem. `integral_combo_six`: The integral of a sum of six integrable functions is the sum of their integrals. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModel.lean#L69).

**Add the second sesquilinear input** · theorem. `sesq12_add_right`: The twelve-component sesquilinear form is additive in its second input. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModel.lean#L79).

**Scale the second sesquilinear input** · theorem. `sesq12_smul_right`: Multiplying the second input by a complex scalar multiplies the sesquilinear form by that scalar. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModel.lean#L82).

**Merge three integrated contributions** · theorem. `merge_three`: The given pointwise decomposition and integrability hypotheses identify one integral with the first contribution plus twice each of the two cross contributions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModel.lean#L85).

**Merge two integrated contributions** · theorem. `merge_two`: The given pointwise decomposition and integrability hypotheses identify one integral with the first contribution plus twice the cross contribution. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModel.lean#L94).

**Merge the split remainder in a pairing** · theorem. `sesq_split_three`: When the two remainder inputs add to the total remainder, their twice-weighted real pairings combine with the base pairing into the pairing against the base plus twice the total remainder. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModel.lean#L100).

**Merge a doubled cross pairing** · theorem. `sesq_split_two`: A real pairing plus twice the cross pairing equals the pairing with the corresponding summed second input. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModel.lean#L108).

**Integrate three interaction terms** · theorem. `integral_combo_three`: The integral of the first term plus twice each of two cross terms equals the same linear combination of their integrals when the terms are integrable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModel.lean#L116).

**Integrate twelve charge contributions** · theorem. `integral_combo_twelve`: The integral of twelve integrable charge terms equals the sum of their integrals. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModel.lean#L124).

**Scale the three-class comparison** · theorem. `scale_combo_wide`: Multiplying the supplied resolved, band and deactivated comparison by a nonnegative scalar preserves the inequality with all twelve charge terms scaled consistently. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModel.lean#L140).

**Write the long own-charge as a form** · theorem. `longOwnCharge_chargeForm`: The long own-charge equals the packed charge form with the explicit long-factor-scaled curl, gradient and velocity coefficients. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModel.lean#L158).

**Write the long partner-charge as a form** · theorem. `longPartnerCharge_chargeForm`: The long partner-charge equals the packed charge form with its explicit long-factor-scaled curl, gradient and velocity coefficients. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModel.lean#L165).

**A full-measure mask changes nothing** · theorem. `mask_ae_eq`: The indicator restriction of a function to an almost everywhere full set equals that function almost everywhere. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModel.lean#L172).

**Mask an almost everywhere bounded field** · theorem. `boundedOnCell_mask`: Masking to a set of full cell measure turns the stated measurable, nonnegative-bound estimate into the bounded-on-cell predicate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModel.lean#L179).

**Only interacting right profiles matter** · theorem. `trueStretch_congr_right`: For a first profile supported on a finite mode set, agreement of the second profiles on all harmonic shifts of that set gives equal integrated true-stretch pairings. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModel.lean#L189).

**The pointwise model comparison interface** · interface proposition. `PointModelStatement`: The interface requires the torus and frame facts, potential and regularity conditions, mode expansions, derivative-error bounds and disjoint mode classes to bound the model interactions minus epsilon, long and high charges by the truncated physical interactions minus the resolved high-part correction. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModel.lean#L199).

Proved by `Breakdown.CertCell.Assembly.Internal.ModelPart.point_model_stage`. The companion records the supplying lambda or structure field.

**Integrate the pointwise model comparison** · theorem. `modelStage_of_point`: The pointwise model-comparison interface together with the torus and frame facts implies the model-stage interface. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModel.lean#L257).

### Breakdown.CertCell.AssemblyPotentialModelAlgebra

This file writes the stretching interaction as a matrix on nine gradient and three velocity coordinates, then prepares the polynomial and torus identities used in the model estimate. Appendix B.3: local stretching, potential forms and mode elimination, (B.25)–(B.37).

**Source namespace `Breakdown.CertCell.Assembly.Internal.ModelPart`.**

**Tensor with prescribed curl gradient** · definition. `curlGradPreimage`: This tensor contracts the prescribed curl gradient with one half of the alternating symbol. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelAlgebra.lean#L22).

**Recover the prescribed curl gradient** · theorem. `curlGradOfSecondDeriv_preimage`: Contracting the constructed second-derivative tensor recovers each entry of the original curl-gradient array. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelAlgebra.lean#L25).

**Model and tensor stretching agree** · theorem. `modelTriple_eq_stretchTriple`: The model interaction equals the tensor stretching interaction after inserting the constructed curl-gradient preimage. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelAlgebra.lean#L29).

**A radial-height monomial** · definition. `monoFn`: This function is the monomial r^i z^j with complex values. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelAlgebra.lean#L38).

**Rectangular polynomial span** · definition. `lowSpan`: This subspace consists of linear combinations of monomials whose radial and height degrees obey the two bounds. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelAlgebra.lean#L40).

**Monomials obey their degree limits** · theorem. `monoFn_mem_lowSpan`: A monomial belongs to the rectangular polynomial span when each exponent is within its corresponding bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelAlgebra.lean#L43).

**Increasing the polynomial degree limits** · theorem. `lowSpan_mono`: Increasing both degree limits enlarges the polynomial span. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelAlgebra.lean#L46).

**Multiplication adds monomial degrees** · theorem. `monoFn_mul`: Multiplying two radial-height monomials adds their radial exponents and their height exponents. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelAlgebra.lean#L51).

**Products add the two degree limits** · theorem. `mul_mem_lowSpan`: The product of two bounded-degree polynomials belongs to the span with the respective degree bounds added. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelAlgebra.lean#L56).

**Constants belong to every low span** · theorem. `const_mem_lowSpan`: Every constant complex function belongs to each rectangular polynomial span. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelAlgebra.lean#L65).

**Conjugation preserves the low span** · theorem. `star_mem_lowSpan`: Conjugating a polynomial on real radial-height coordinates preserves its two degree bounds. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelAlgebra.lean#L72).

**Degree of a radial basis polynomial** · theorem. `radialPoly_mem_lowSpan`: The radial basis polynomial of index j has radial degree at most j and height degree zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelAlgebra.lean#L101).

**Degree of a height basis polynomial** · theorem. `heightPoly_mem_lowSpan`: The height basis polynomial of index l has height degree at most l and radial degree zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelAlgebra.lean#L111).

**Degrees of the tensor-product basis** · theorem. `basisFn_mem_lowSpan`: The basis function indexed by (j,l) belongs to the polynomial span with radial bound j and height bound l. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelAlgebra.lean#L121).

**Strain coefficient of stretching** · definition. `coefS`: This coefficient is minus one half of the symmetrized product of the two curl vectors. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelAlgebra.lean#L130).

**Curl-gradient stretching coefficient** · definition. `coefG`: This coefficient combines velocity-curl products with the alternating-symbol gradient-velocity terms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelAlgebra.lean#L133).

**Separate the two coefficient arrays** · theorem. `modelTriple_eq_coef`: The model interaction is the sum of its strain entries times their coefficients and its curl-gradient entries times their coefficients. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelAlgebra.lean#L137).

**Curl preserves gradient addition** · theorem. `curlOfGrad_add_fn`: The curl of the sum of two gradient arrays is the sum of their curls. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelAlgebra.lean#L146).

**Scale the gradient before taking curl** · theorem. `curlOfGrad_smul_fn`: The curl of a complex scalar multiple of a gradient is that scalar times the original curl. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelAlgebra.lean#L150).

**Add the first strain-coefficient pair** · theorem. `coefS_add_left`: Adding the first velocity-gradient pairs adds their strain stretching coefficients while the second pair stays fixed. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelAlgebra.lean#L156).

**Add the second strain-coefficient pair** · theorem. `coefS_add_right`: Adding the second velocity-gradient pairs adds their strain stretching coefficients while the first pair stays fixed. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelAlgebra.lean#L161).

**Scale the first strain-coefficient pair** · theorem. `coefS_smul_left`: Scaling both velocity and gradient in the first pair scales the strain stretching coefficient by the same complex scalar. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelAlgebra.lean#L166).

**Scale the second strain-coefficient pair** · theorem. `coefS_smul_right`: Scaling both velocity and gradient in the second pair scales the strain stretching coefficient by the same complex scalar. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelAlgebra.lean#L171).

**Add the first curl-gradient pair** · theorem. `coefG_add_left`: Adding the first velocity-gradient pairs adds their curl-gradient stretching coefficients while the second pair stays fixed. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelAlgebra.lean#L176).

**Add the second curl-gradient pair** · theorem. `coefG_add_right`: Adding the second velocity-gradient pairs adds their curl-gradient stretching coefficients while the first pair stays fixed. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelAlgebra.lean#L181).

**Scale the first curl-gradient pair** · theorem. `coefG_smul_left`: Scaling both fields in the first pair scales the curl-gradient stretching coefficient by the same complex scalar. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelAlgebra.lean#L186).

**Scale the second curl-gradient pair** · theorem. `coefG_smul_right`: Scaling both fields in the second pair scales the curl-gradient stretching coefficient by the same complex scalar. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelAlgebra.lean#L191).

**Bilinear stretching interaction** · definition. `tripleBil`: This linear-map pair packages the stretching interaction as a bilinear function of the two velocity-gradient pairs. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelAlgebra.lean#L196).

**Read the packaged bilinear interaction** · theorem. `tripleBil_apply`: Applying the packaged bilinear map gives the original model interaction on the two velocity-gradient pairs. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelAlgebra.lean#L214).

**Matrix of the stretching interaction** · definition. `tripleMatrix`: This matrix evaluates the stretching interaction on the twelve coordinate basis vectors. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelAlgebra.lean#L218).

**Velocity-gradient coordinate pair** · definition. `vgOf`: This map reads the three velocity and nine gradient coordinates of a twelve-component vector. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelAlgebra.lean#L222).

**Conjugated velocity-gradient pair** · definition. `svgOf`: This map reads and complex-conjugates the velocity and gradient coordinates. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelAlgebra.lean#L224).

**Expand the velocity-gradient slot map** · theorem. `vgOf_eq_sum`: The velocity-gradient slot map is the sum of the original coordinates times its values on the corresponding coordinate unit vectors. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelAlgebra.lean#L226).

**Expand the conjugate slot map** · theorem. `svgOf_eq_sum`: The conjugate slot map is the sum of the conjugated original coordinates times its values on the coordinate unit vectors. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelAlgebra.lean#L233).

**Matrix pairing equals model stretching** · theorem. `sesq_tripleMatrix`: The twelve-coordinate matrix pairing equals the model interaction with the first profile conjugated. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelAlgebra.lean#L240).

**Source section `Torus`.**

**Every label phase has norm one** · theorem. `labelPhase_norm_one`: Every time-angle label phase has complex norm one. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelAlgebra.lean#L258).

**The label phase is continuous** · theorem. `labelPhase_continuous_pair`: For each fixed label and azimuth order, its complex phase depends continuously on time and angle. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelAlgebra.lean#L262).

**Multiply a conjugate label phase** · theorem. `conj_mul_labelPhase`: The conjugate phase at one label times the phase at another is the conjugate phase at their difference. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelAlgebra.lean#L266).

**Scale a torus mean** · theorem. `Breakdown.CertCell.AssemblyPotentialModelAlgebra.torusMean_const_mul`: Taking the torus mean commutes with multiplication by a fixed complex scalar. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelAlgebra.lean#L275).

**The zero function has zero mean** · theorem. `torusMean_zero`: The torus mean of the identically zero complex function is zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelAlgebra.lean#L280).

**Add torus-integrable functions** · theorem. `torusIntegrable_add`: The sum of two integrable functions on the time-angle box is integrable there. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelAlgebra.lean#L283).

**Subtract torus-integrable functions** · theorem. `torusIntegrable_sub`: The difference of two integrable functions on the time-angle box is integrable there. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelAlgebra.lean#L286).

**Scale a torus-integrable function** · theorem. `torusIntegrable_const_mul`: Multiplication by a fixed complex scalar preserves integrability on the time-angle box. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelAlgebra.lean#L289).

**Finite sums stay torus-integrable** · theorem. `torusIntegrable_finsum`: A finite sum of functions integrable on the time-angle box is integrable there. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelAlgebra.lean#L292).

**Average a finite sum term by term** · theorem. `torusMean_finsum`: The torus mean of a finite sum of integrable functions equals the sum of their torus means. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelAlgebra.lean#L298).

**Continuous functions on the torus box** · theorem. `Breakdown.CertCell.AssemblyPotentialModelAlgebra.torusIntegrable_of_continuous`: The continuous function with the stated bound is integrable on the compact time-angle box, using the supplied torus facts where required. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelAlgebra.lean#L310).

**Parseval for a finite scalar wave** · theorem. `torusMean_wave_normSq`: For positive symmetry order, the mean squared norm of a finite harmonic sum equals the sum of squared coefficient norms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelAlgebra.lean#L314).

### Breakdown.CertCell.AssemblyPotentialModelCharges

This file turns bounds on strain and vorticity gradient into separate curl, gradient and velocity charges, and averages those charges over finite harmonic sums. Appendix B.3: local stretching, potential forms and mode elimination, (B.25)–(B.37).

**Source namespace `Breakdown.CertCell.Assembly.Internal.ModelPart`.**

**Conjugation preserves coordinate energy** · theorem. `cnormSq_star_vec`: Conjugating every coordinate leaves the squared-coordinate norm unchanged. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelCharges.lean#L19).

**Curl commutes with conjugation** · theorem. `curlOfGrad_star_grad`: The curl of the conjugated gradient equals the conjugate of its curl. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelCharges.lean#L22).

**Balance a product of square roots** · theorem. `two_sqrt_mul_le`: For nonnegative x and y and positive c, twice √x√y is at most cx+y/c. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelCharges.lean#L26).

**Charge a stretching self-interaction** · theorem. `modelTriple_self_norm_le`: The strain and curl-gradient operator bounds control the self-interaction by its prescribed cross charge when the length scale is positive. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelCharges.lean#L73).

**Source section `Base`.**

**Multiply by a bounded continuous factor** · theorem. `torusIntegrable_bdd_mul`: The product of a torus-integrable function and a bounded continuous torus factor is integrable on the time-angle box. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelCharges.lean#L90).

**A finite wave sum is continuous** · theorem. `waveSum_continuous`: Every coordinate of a finite vector Fourier synthesis is continuous in time and angle. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelCharges.lean#L95).

**Bound a finite harmonic sum** · theorem. `waveSum_norm_le`: Each synthesized coordinate has norm at most the sum of the norms of its coefficients. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelCharges.lean#L100).

**Wave pairings are torus-integrable** · theorem. `pairSesq_wave_integrable`: Entrywise torus integrability of the matrix makes its pairing of two finite Fourier wave sums torus-integrable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelCharges.lean#L106).

**Add two integrable torus means** · theorem. `torusMean_add'`: The torus mean of two integrable functions added together equals the sum of their means. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelCharges.lean#L122).

**Subtract two torus means** · theorem. `torusMean_sub`: Under torus integrability and the supplied mean identities, the mean of a difference equals the difference of the means. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelCharges.lean#L125).

**Subtract matrix Fourier coefficients** · theorem. `torusCoef_sub`: For entrywise integrable matrix fields, the matrix Fourier coefficient of their difference equals the difference of their coefficients. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelCharges.lean#L138).

**Subtract model coefficient arrays** · theorem. `tripleMatrix_sub`: The triple matrix formed from the two coefficient-array differences equals the difference of the two triple matrices. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelCharges.lean#L150).

**Take coefficients before matrix assembly** · theorem. `torusCoef_tripleMatrix`: Taking a harmonic coefficient of the stretching matrix agrees with assembling the matrix from the corresponding strain and curl-gradient coefficients. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelCharges.lean#L156).

**Source section `Charges`.**

**Curl, gradient and velocity charge** · definition. `chargeForm`: This quadratic expression adds three weighted squared norms: curl, gradient and velocity. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelCharges.lean#L222).

**Read the cross charge in twelve slots** · theorem. `crossCharge_eq_chargeForm`: The cross charge equals the curl-gradient-velocity charge form with the stated strain and balanced curl-gradient constants. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelCharges.lean#L225).

**Curl agrees in the two coordinate forms** · theorem. `curlComp_strainOfVec`: The indexed curl of the gradient block equals the curl computed from its flattened coordinates. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelCharges.lean#L231).

**Curl squared norms agree** · theorem. `Breakdown.CertCell.AssemblyPotentialModelCharges.curlSq_strainOfVec`: The indexed curl squared norm equals the coordinate squared norm of the curl of the gradient block. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelCharges.lean#L236).

**Gradient squared norms agree** · theorem. `Breakdown.CertCell.AssemblyPotentialModelCharges.sumSq_strainOfVec`: The indexed sum of gradient-entry squared norms equals the flattened gradient block's squared coordinate norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelCharges.lean#L239).

**Velocity squared norms agree** · theorem. `Breakdown.CertCell.AssemblyPotentialModelCharges.vecSq_velOf`: The velocity squared norm equals the coordinate squared norm of the last three slots. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelCharges.lean#L242).

**Read the high-degree own charge** · theorem. `highOwnCharge_eq`: The high-degree own charge is the three-term charge form with its balancing factors multiplying the coefficient bounds. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelCharges.lean#L244).

**Read the high-degree partner charge** · theorem. `highPartnerCharge_eq`: The high-degree partner charge is the three-term charge form with the complementary reciprocal balancing factors. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelCharges.lean#L251).

**Curl commutes with harmonic synthesis** · theorem. `curlOfGrad_wave`: The curl of a finite linear combination of gradient arrays is the same linear combination of their curls. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelCharges.lean#L258).

**Parseval for vector-valued waves** · theorem. `torusMean_cnormSq_wave`: For positive symmetry order, the mean coordinate squared norm of a finite harmonic vector sum equals the sum of coefficient squared norms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelCharges.lean#L269).

**Expand a synthesized charge form** · theorem. `chargeForm_wave`: The charge of a synthesized profile separates into the synthesized curl, gradient and velocity squared norms with their respective weights. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelCharges.lean#L292).

**A finite-wave charge is continuous** · theorem. `chargeForm_wave_continuous`: The curl, gradient and velocity charge of a finite Fourier synthesis is continuous in time and angle. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelCharges.lean#L306).

**Average each charge coefficient** · theorem. `torusMean_chargeForm_wave`: The torus mean of the charge form of a finite wave is the sum of the charge forms of its coefficients. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelCharges.lean#L320).

### Breakdown.CertCell.AssemblyPotentialModelFrame

This file states the coordinate changes needed to compare physical derivatives with their cylindrical harmonic coefficients; its proposition definitions state the interfaces whose proofs are assembled in the neighboring files. Appendix B.3: local stretching, potential forms and mode elimination, (B.25)–(B.37).

**Cell matrix field in the rotating frame** · interface proposition. `ModelFieldFrameStatement`: This predicate requires that a valid conjugate-closed cell matrix field equals its finite label-phase expansion almost everywhere on each rectangle. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelFrame.lean#L18).

Proved by `Breakdown.CertCell.Assembly.Internal.modelFieldFrame`.

**Symmetric gradient in a rotated frame** · interface proposition. `StrainFrameStatement`: This predicate requires that the rotated symmetric part of an operator is the symmetric part of its rotated matrix. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelFrame.lean#L25).

Proved by `Breakdown.CertCell.Assembly.Internal.strainFrame`.

**Curl gradient in a rotated frame** · interface proposition. `VorticityGradFrameStatement`: This predicate requires that a symmetric second-derivative tensor gives the corresponding rotated curl-gradient contraction. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelFrame.lean#L30).

Proved by `Breakdown.CertCell.Assembly.Internal.vorticityGradFrame`.

**Rotation preserves the matrix bound** · interface proposition. `RotatedBoundStatement`: This predicate requires that the complex matrix in the rotated orthonormal frame is bounded by the physical operator norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelFrame.lean#L35).

Proved by `Breakdown.CertCell.Assembly.Internal.rotatedBound`.

**Rotating a cell point stays in its solid** · interface proposition. `OrbitSolidStatement`: This predicate requires that rotating a point of a valid cell rectangle places it inside the associated three-dimensional cell solid. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelFrame.lean#L40).

Proved by `Breakdown.CertCell.Assembly.Internal.orbitSolid`.

**Measurable gradient fibres and modes** · interface proposition. `GradSectionStatement`: This predicate requires that an almost-everywhere measurable matrix field has measurable rotated fibres and measurable harmonic coefficients on valid rectangles. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelFrame.lean#L43).

Proved by `Breakdown.CertCell.Assembly.Internal.gradSection`.

**Measurable Hessian fibres and modes** · interface proposition. `SecondDerivSectionStatement`: This predicate requires that an almost-everywhere measurable second-derivative field has measurable rotated fibres and measurable harmonic coefficients on valid rectangles. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelFrame.lean#L51).

Proved by `Breakdown.CertCell.Assembly.Internal.secondDerivSection`.

**Harmonic expansion of the given field** · interface proposition. `GivenExpansionStatement`: This predicate requires that the given gradient and weak Hessian agree with their declared finite harmonic expansions, with the Hessian identity almost everywhere. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelFrame.lean#L59).

Proved by `Breakdown.CertCell.Assembly.Internal.givenExpansion`.

**The eight rotating-frame interfaces** · structure. `FrameFacts`: This predicate requires that all eight matrix-frame, derivative-frame, orbit and section interfaces hold together. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelFrame.lean#L68).

### Breakdown.CertCell.AssemblyPotentialModelFrameFacts

This file supplies all eight frame interfaces from their algebraic, geometric and measurability proofs. Appendix B.3: local stretching, potential forms and mode elimination, (B.25)–(B.37).

**The eight rotating-frame interfaces** · theorem. `frameFacts`: Under the stated hypotheses, all eight matrix-frame, derivative-frame, orbit and section interfaces hold together. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelFrameFacts.lean#L14).

### Breakdown.CertCell.AssemblyPotentialModelFrameFactsAlgebra

This file proves the rotation identities that preserve strain, curl gradients and operator bounds when the model estimate moves into the cylindrical frame. Appendix B.3: local stretching, potential forms and mode elimination, (B.25)–(B.37).

**A rotated coordinate is an inner product** · theorem. `rot_coord_inner`: A coordinate after inverse axial rotation equals the inner product with the corresponding forward-rotated basis vector. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelFrameFactsAlgebra.lean#L19).

**Symmetric gradient in a rotated frame** · theorem. `strainFrame`: Under the stated hypotheses, the rotated symmetric part of an operator is the symmetric part of its rotated matrix. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelFrameFactsAlgebra.lean#L26).

**The axial rotation matrix is orthogonal** · theorem. `rm_orth`: The dot product of two columns of the axial rotation matrix is one when they coincide and zero otherwise. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelFrameFactsAlgebra.lean#L34).

**Curl gradient in a rotated frame** · theorem. `vorticityGradFrame`: Under the stated hypotheses, a symmetric second-derivative tensor gives the corresponding rotated curl-gradient contraction. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelFrameFactsAlgebra.lean#L39).

**Bound the rotated real matrix** · theorem. `rotated_real`: The squared norm of the rotated matrix on a real vector is bounded by the operator norm squared times the vector's squared norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelFrameFactsAlgebra.lean#L65).

**Rotation preserves the matrix bound** · theorem. `rotatedBound`: Under the stated hypotheses, the complex matrix in the rotated orthonormal frame is bounded by the physical operator norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelFrameFactsAlgebra.lean#L91).

**Coordinates of a rotated plane point** · theorem. `Breakdown.CertCell.AssemblyPotentialModelFrameFactsAlgebra.rot_plane_coords`: Rotating (r,0,z) gives (r cos φ,r sin φ,z). [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelFrameFactsAlgebra.lean#L111).

**Rotating a cell point stays in its solid** · theorem. `orbitSolid`: Under the stated hypotheses, rotating a point of a valid cell rectangle places it inside the associated three-dimensional cell solid. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelFrameFactsAlgebra.lean#L116).

### Breakdown.CertCell.AssemblyPotentialModelFrameFactsGiven

This file recovers the finite harmonic expansions of the given field's derivatives, with weak second derivatives interpreted almost everywhere. Appendix B.3: local stretching, potential forms and mode elimination, (B.25)–(B.37).

**Almost every plane radius is nonzero** · theorem. `ae_first_ne`: The first coordinate is nonzero for almost every point of the plane with respect to Lebesgue measure. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelFrameFactsGiven.lean#L20).

**Almost every plane height is nonzero** · theorem. `ae_second_ne`: The second coordinate is nonzero for almost every point of the plane with respect to Lebesgue measure. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelFrameFactsGiven.lean#L27).

**Cell measure lies in the half-plane** · theorem. `rect_ac_halfPlane`: For a valid cell, its restricted rectangle measure is absolutely continuous with respect to the restricted half-plane measure. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelFrameFactsGiven.lean#L34).

**Opposite frequencies conjugate phases** · theorem. `phase_neg_conj`: The phase at the negative harmonic is the complex conjugate of the phase at the original harmonic. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelFrameFactsGiven.lean#L41).

**Opposite Hessian modes are conjugate** · theorem. `modeSecondDeriv_neg_conj`: For a real second-derivative field, the Fourier Hessian coefficient at the negative frequency is the conjugate of the original coefficient. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelFrameFactsGiven.lean#L45).

**Nonnegative weak-field decay bound** · theorem. `decay_nonneg`: The bound in a weak second-derivative state is necessarily nonnegative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelFrameFactsGiven.lean#L50).

**Harmonic expansion of the given field** · theorem. `givenExpansion`: Under the stated hypotheses, the given gradient and weak Hessian agree with their declared finite harmonic expansions, with the Hessian identity almost everywhere. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelFrameFactsGiven.lean#L56).

### Breakdown.CertCell.AssemblyPotentialModelFrameFactsModel

This file reconstructs a cell matrix field in its moving frame and uses conjugate closure to recover the complex harmonic expansion from its real field. Appendix B.3: local stretching, potential forms and mode elimination, (B.25)–(B.37).

**Coordinates of a rotated plane point** · theorem. `rotPlane_coord`: Rotating (r,0,z) gives (r cos φ,r sin φ,z) in the three physical coordinates. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelFrameFactsModel.lean#L20).

**Rotation preserves the plane radius** · theorem. `rotPlane_radius`: For nonnegative r, the cylindrical radius of the rotated plane point is r. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelFrameFactsModel.lean#L26).

**Solid membership from a plane point** · theorem. `rotPlane_mem_solid`: For nonnegative radius and height, a rotated plane point lies in a cell solid exactly when its plane coordinates lie in the cell rectangle. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelFrameFactsModel.lean#L35).

**Return a rotated point to the plane** · theorem. `rotPlane_pointPlane`: For nonnegative radius, converting a rotated plane point back to plane coordinates recovers the original point. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelFrameFactsModel.lean#L44).

**Recover the rotation angle modulo 2π** · theorem. `rotPlane_angle`: At positive radius, the angle of the rotated plane point has the same sine and cosine as the rotation angle. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelFrameFactsModel.lean#L49).

**Equal angles give the same frame vector** · theorem. `frameUnit_of_angle`: Angles with the same sine and cosine give the same rotated coordinate frame vectors. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelFrameFactsModel.lean#L72).

**Rotated basis vectors stay orthonormal** · theorem. `inner_rot_unit`: Two rotated coordinate unit vectors have inner product one when their indices agree and zero otherwise. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelFrameFactsModel.lean#L78).

**Label phases depend only on the angle** · theorem. `labelPhase_of_angle`: Angles with equal sine and cosine give identical label phases. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelFrameFactsModel.lean#L84).

**Recover entries in the moving frame** · theorem. `frameMap_frame`: Applying the physical frame map to a rotated basis vector and rotating back recovers the original matrix entry. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelFrameFactsModel.lean#L100).

**Opposite labels conjugate phases** · theorem. `labelPhase_neg`: The label phase at the negative label is the complex conjugate of the original label phase. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelFrameFactsModel.lean#L113).

**Opposite model values are conjugate** · theorem. `planeValue_neg`: For a conjugate-closed matrix model, the plane value at the negative label is the conjugate of the original plane value. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelFrameFactsModel.lean#L121).

**Expand a model field in its own cell** · theorem. `field_frame`: At an interior non-axis point belonging to just the selected cell, the rotated field is the real part of its finite label-phase expansion. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelFrameFactsModel.lean#L133).

**Cell matrix field in the rotating frame** · theorem. `modelFieldFrame`: Under the stated hypotheses, a valid conjugate-closed cell matrix field equals its finite label-phase expansion almost everywhere on each rectangle. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelFrameFactsModel.lean#L158).

### Breakdown.CertCell.AssemblyPotentialModelFrameFactsSection

This file proves the almost-everywhere fibre measurability needed before taking gradient and Hessian coefficients on a cell rectangle. Appendix B.3: local stretching, potential forms and mode elimination, (B.25)–(B.37).

**Measurable fibres on almost every orbit** · theorem. `fiber_section`: A measurable physical field composed with the rotated cell orbit and the continuous observation is measurable on almost every time-angle fibre. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelFrameFactsSection.lean#L18).

**Measurability of an orbit Fourier mean** · theorem. `mean_section`: For an almost-everywhere measurable space-time field and continuous scalar observation, its displayed time-angle Fourier integral is almost-everywhere strongly measurable on the cell rectangle. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelFrameFactsSection.lean#L26).

**Measurable gradient fibres and modes** · theorem. `gradSection`: Under the stated hypotheses, an almost-everywhere measurable matrix field has measurable rotated fibres and measurable harmonic coefficients on valid rectangles. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelFrameFactsSection.lean#L57).

**Measurable Hessian fibres and modes** · theorem. `secondDerivSection`: Under the stated hypotheses, an almost-everywhere measurable second-derivative field has measurable rotated fibres and measurable harmonic coefficients on valid rectangles. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelFrameFactsSection.lean#L79).

### Breakdown.CertCell.AssemblyPotentialModelOrthogonal

This file makes the high-degree remainder orthogonal to low polynomial interactions, while recording the integrability needed to use those vanishing moments. Appendix B.3: local stretching, potential forms and mode elimination, (B.25)–(B.37).

**Source section `Integrability`.**

**Square-integrable cell profile** · proposition definition. `IsSqOn`: This predicate requires that each coordinate is measurable and the radius-weighted sum of squared coordinate norms is integrable on the cell. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelOrthogonal.lean#L25).

**The cell rectangle is measurable** · theorem. `Breakdown.CertCell.AssemblyPotentialModelOrthogonal.rect_measurableSet`: The closed radial-height rectangle associated with a cell box is Lebesgue measurable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelOrthogonal.lean#L29).

**The cell rectangle has finite measure** · theorem. `Breakdown.CertCell.AssemblyPotentialModelOrthogonal.rect_finite`: The cell rectangle has finite Lebesgue measure. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelOrthogonal.lean#L32).

**Radius lies within the cell bounds** · theorem. `rect_fst_bounds`: A point in a valid cell rectangle has radial coordinate between zero and the outer radius. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelOrthogonal.lean#L39).

**Radius is integrable on a cell** · theorem. `integrableOn_fst`: The radial coordinate is integrable on the cell rectangle. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelOrthogonal.lean#L43).

**An almost-everywhere bound on the cell** · theorem. `boundedOnCell_ae_bound`: The cell-boundedness hypothesis supplies a single real norm bound almost everywhere on the rectangle. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelOrthogonal.lean#L47).

**A weighted profile coordinate integrates** · theorem. `integrableOn_fst_mul_comp`: A profile with finite radial-weighted squared norm has integrable radial-weighted coordinates on the cell rectangle. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelOrthogonal.lean#L52).

**A bounded matrix-profile pairing fits** · theorem. `integrableOn_sesq`: A bounded cell matrix and bounded first profile paired with a finite-energy second profile give an integrable radial-weighted sesquilinear expression. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelOrthogonal.lean#L65).

**The real matrix-profile pairing fits** · theorem. `integrableOn_sesq_re`: The same bounded matrix and first-profile assumptions with finite energy of the second profile make the real radial-weighted sesquilinear expression integrable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelOrthogonal.lean#L86).

**Source section `Orthogonality`.**

**Tensor monomials are continuous** · theorem. `monoFn_continuous`: Each tensor monomial in the radial and axial coordinates is a continuous complex-valued function. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelOrthogonal.lean#L102).

**Orthogonality extends to the full span** · theorem. `integral_mul_lowSpan`: An integrable function orthogonal to every allowed tensor monomial has integrable product and zero integral against every polynomial in their rectangular span. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelOrthogonal.lean#L106).

**Add polynomials without raising degree** · theorem. `lowSpan_add`: The sum of two functions in the same rectangular polynomial span remains in that span. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelOrthogonal.lean#L133).

**Scaling preserves the polynomial span** · theorem. `lowSpan_const_mul`: Multiplying by a complex constant preserves both polynomial degree bounds. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelOrthogonal.lean#L136).

**Products add polynomial degree bounds** · theorem. `lowSpan_mul`: Multiplying polynomials adds their respective radial and height degree bounds. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelOrthogonal.lean#L139).

**Finite sums preserve the low span** · theorem. `lowSpan_sum`: A finite sum of functions in one rectangular polynomial span remains in that span. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelOrthogonal.lean#L142).

**Negation preserves the polynomial span** · theorem. `lowSpan_neg`: Negating a polynomial preserves its radial and height degree bounds. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelOrthogonal.lean#L149).

**Curl preserves polynomial degree bounds** · theorem. `curlOfGrad_mem_lowSpan`: Taking a curl component preserves the common degree bounds of the gradient entries. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelOrthogonal.lean#L153).

**Degree of the strain interaction term** · theorem. `coefS_mem_lowSpan`: The strain coefficient of two degree-Q profiles has degree at most 2Q in each coordinate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelOrthogonal.lean#L158).

**Degree of the curl-gradient term** · theorem. `coefG_mem_lowSpan`: The curl-gradient coefficient of two degree-Q profiles has degree at most 2Q in each coordinate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelOrthogonal.lean#L173).

**High remainders pair to zero with lows** · theorem. `highLow_vanish`: The radius-weighted high-remainder interaction of two degree-Q profiles vanishes when its moments vanish through degree at least 2Q+1. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelOrthogonal.lean#L193).

**Source section `CoefHelpers`.**

**Read a matrix entry with unit vectors** · theorem. `Breakdown.CertCell.AssemblyPotentialModelOrthogonal.sesq12_single`: Pairing the ith and jth coordinate unit vectors through the sesquilinear form returns matrix entry (i,j). [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelOrthogonal.lean#L293).

**The two matrix pairings agree** · theorem. `pairSesq_eq_sesq12`: The torus matrix pairing and the twelve-coordinate sesquilinear pairing have the same value. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelOrthogonal.lean#L297).

**Pairings determine the model matrix** · theorem. `matrix_eq_tripleMatrix_of_sesq`: A matrix with the model interaction as its pairing on every pair of coordinate vectors equals the constructed stretching matrix. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelOrthogonal.lean#L299).

**Subtract the labelled harmonic** · theorem. `conj_labelPhase_mul_phase`: Multiplying a harmonic phase by a conjugate label phase gives the harmonic phase with that label's harmonic subtracted. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelOrthogonal.lean#L307).

**Extract a harmonic from a finite sum** · theorem. `torusMean_conj_phase_sum`: Averaging a finite harmonic sum against the conjugate label phase extracts the coefficient of that label's harmonic when present and gives zero otherwise. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelOrthogonal.lean#L316).

**Extract a label from a finite sum** · theorem. `torusMean_conj_label_sum`: For positive azimuth order, averaging a finite labelled sum against a conjugate label phase extracts that label's coefficient when present and gives zero otherwise. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelOrthogonal.lean#L332).

**The fibre mean is a gradient coefficient** · theorem. `torusMean_fibGrad`: The normalized mean of the rotated gradient entry against a conjugate label phase equals its selected gradient harmonic coefficient. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelOrthogonal.lean#L349).

**The fibre mean is a Hessian coefficient** · theorem. `torusMean_frameSecond`: The normalized mean of the rotated Hessian entry against a conjugate label phase equals its selected second-derivative coefficient. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelOrthogonal.lean#L364).

### Breakdown.CertCell.AssemblyPotentialModelPoint

This file proves the model-versus-true stretching comparison at one cell point, accounting separately for approximation, high-degree and long-mode errors. Appendix B.3: local stretching, potential forms and mode elimination, (B.25)–(B.37).

**Source section `Bounded`.**

**Bounded cell functions integrate** · theorem. `integrableOn_of_boundedOnCell`: The cell boundedness predicate supplies integrability on the finite cell rectangle. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelPoint.lean#L28).

**Continuous representatives give bounds** · theorem. `boundedOnCell_of_continuous_eq`: A function equal on the cell rectangle to a continuous function satisfies the cell-boundedness predicate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelPoint.lean#L34).

**Add two bounded cell functions** · theorem. `boundedOnCell_add`: The sum of two cell-bounded functions is cell-bounded. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelPoint.lean#L43).

**Scale a bounded cell function** · theorem. `boundedOnCell_const_mul`: Multiplying a cell-bounded function by a fixed complex scalar preserves cell-boundedness. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelPoint.lean#L49).

**Scale on the right without losing bounds** · theorem. `boundedOnCell_mul_const`: Multiplying a cell-bounded function on the right by a fixed complex scalar preserves cell-boundedness. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelPoint.lean#L56).

**A finite sum remains bounded on a cell** · theorem. `boundedOnCell_sum`: A finite sum of cell-bounded functions is cell-bounded. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelPoint.lean#L61).

**Bound the assembled model matrix** · theorem. `boundedOnCell_tripleMatrix`: Cell-bounded strain and curl-gradient entries give cell-bounded entries of the model stretching matrix. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelPoint.lean#L73).

**Cell polynomial evaluation is continuous** · theorem. `Breakdown.CertCell.AssemblyPotentialModelPoint.cellPoly_eval_continuous`: Evaluating a fixed cell polynomial gives a continuous function of the radial-height point. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelPoint.lean#L81).

**An orbit bound controls gradient modes** · theorem. `labelGrad_norm_le`: A uniform operator bound on a rotated orbit bounds every harmonic gradient coefficient by the same constant. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelPoint.lean#L85).

**An orbit bound controls Hessian modes** · theorem. `labelSecond_norm_le`: A uniform Hessian operator bound on a rotated orbit bounds every second-derivative harmonic entry by the same constant. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelPoint.lean#L94).

**Uniform bounds from the weak model** · theorem. `given_bounds`: A weak second-derivative state gives a nonnegative bound controlling both the reference gradient and Hessian everywhere. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelPoint.lean#L108).

**Source section `EpsForms`.**

**Identify the own approximation charge** · theorem. `epsOwnCharge_eq`: The own approximation charge in velocity-gradient variables equals its twelve-coordinate charge form. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelPoint.lean#L127).

**The partner approximation charge** · theorem. `epsPartnerCharge_eq`: The partner approximation charge in velocity-gradient variables equals its twelve-coordinate charge form. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelPoint.lean#L132).

**Identify the cutoff-dependent own charge** · theorem. `longOwnCharge_eq`: The long-mode own charge is the approximation form times the balance factor chosen by the label cutoff. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelPoint.lean#L137).

**Identify the cutoff partner charge** · theorem. `longPartnerCharge_eq`: The long-mode partner charge is the approximation form times the balance factor chosen by the label cutoff. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelPoint.lean#L143).

**Source section `PointAt`.**

**Zero arrays give a zero triple matrix** · theorem. `tripleMatrix_zero`: When both model coefficient arrays vanish, their triple matrix is zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelPoint.lean#L156).

**The cell-point model comparison** · theorem. `point_model_stage`: At a valid non-axis cell point, the model interaction after all error charges is bounded by the true interaction minus the high-low remainder. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelPoint.lean#L162).

### Breakdown.CertCell.AssemblyPotentialModelProfiles

This file relates finite coordinate profiles, physical harmonic coefficients and their matrix pairings, so the pointwise model estimate can be integrated over a cell. Appendix B.3: local stretching, potential forms and mode elimination, (B.25)–(B.37).

**Source section `FrameBounds`.**

**Operator in the rotating frame** · definition. `rotMat`: This matrix rotates the basis into physical space, applies the operator and rotates the result back. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelProfiles.lean#L24).

**Transfer an operator bound to its matrix** · theorem. `opBound_rotMat`: An operator norm bound transfers to the complex matrix in any rotated orthonormal frame. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelProfiles.lean#L27).

**Symmetrizing does not increase the norm** · theorem. `norm_half_add_adjoint`: The norm of one half of an operator plus its adjoint is at most the norm of the operator. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelProfiles.lean#L35).

**Bound the symmetric rotated matrix** · theorem. `symOpBound_rotMat`: An operator norm bound also bounds the symmetric part of its complex rotated matrix. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelProfiles.lean#L44).

**Subtract operators in a rotating frame** · theorem. `rotMat_sub`: The rotated matrix of an operator difference equals the difference of the two rotated matrices. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelProfiles.lean#L59).

**Each rotated entry obeys the norm bound** · theorem. `rotMat_entry_le`: The norm of each rotated matrix entry is at most the operator norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelProfiles.lean#L66).

**The gradient fibre is the rotated matrix** · theorem. `fibGrad_eq_rotMat`: The gradient fibre entry equals the entry of the physical operator's matrix in the rotating frame. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelProfiles.lean#L85).

**Source section `Pairs`.**

**Coupling restricted to chosen labels** · definition. `truncCoupling`: This matrix equals the true coupling on the chosen label set and is zero outside it. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelProfiles.lean#L96).

**Zero in the first pairing slot** · theorem. `sesq12_zero_left`: A matrix sesquilinear pairing is zero when its first vector is zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelProfiles.lean#L99).

**Zero in the second pairing slot** · theorem. `sesq12_zero_right`: A matrix sesquilinear pairing is zero when its second vector is zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelProfiles.lean#L102).

**A zero matrix gives a zero pairing** · theorem. `sesq12_zero_mat`: The sesquilinear pairing through the zero matrix is zero for every pair of vectors. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelProfiles.lean#L105).

**Finite support turns stretching finite** · theorem. `trueStretch_eq_modelPair`: For profiles vanishing outside the two finite sets, the true stretching equals the finite model pairing with the truncated true coupling. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelProfiles.lean#L108).

**Source section `AssemblyLemmas`.**

**Continuity of the polynomial span** · theorem. `lowSpan_continuous`: Every function in the prescribed finite tensor-polynomial span is continuous. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelProfiles.lean#L160).

**Retained profiles add with the state** · theorem. `Breakdown.CertCell.AssemblyPotentialModelProfiles.lowProfile_add`: The retained polynomial profile of a sum of cell states equals the sum of their retained profiles. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelProfiles.lean#L171).

**Zero-extended low profiles add** · theorem. `Breakdown.CertCell.AssemblyPotentialModelProfiles.lowAt_add`: The zero-extended low profile of a sum of states equals the sum of their zero-extended low profiles at every label. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelProfiles.lean#L177).

**Split retained data into upper and band** · theorem. `Breakdown.CertCell.AssemblyPotentialModelProfiles.lowAt_split`: The low profile equals the sum of the low profiles of the upper and band coordinate parts. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelProfiles.lean#L184).

**Degree bound for the retained profile** · theorem. `lowAt_mem_lowSpan`: Under the cell-calculus conditions, each retained profile coordinate lies in the cell's specified polynomial span. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelProfiles.lean#L191).

**Read the finite coupling as an integral** · theorem. `couplingPair_eq_modelPair`: The finite coupling pair equals the resolved model-pair integral of the corresponding low profiles. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelProfiles.lean#L215).

**Basis velocity slots are real** · theorem. `Breakdown.CertCell.AssemblyPotentialModelProfiles.star_velOf_single`: The velocity projection of a complex coordinate unit vector is fixed by conjugation. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelProfiles.lean#L226).

**Basis gradient slots are real** · theorem. `Breakdown.CertCell.AssemblyPotentialModelProfiles.star_gradOf_single`: The gradient projection of a complex coordinate unit vector is fixed by conjugation. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelProfiles.lean#L231).

**Conjugate every model interaction input** · theorem. `Breakdown.CertCell.AssemblyPotentialModelProfiles.conj_modelTriple`: Conjugating the stretching model interaction equals applying it to the entrywise conjugates of its coefficient arrays and both field pairs. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelProfiles.lean#L236).

**Exchange the two profiles in stretching** · theorem. `Breakdown.CertCell.AssemblyPotentialModelProfiles.modelTriple_swap`: The symmetrized model interaction is unchanged when its two velocity-gradient arguments are exchanged. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelProfiles.lean#L244).

**Conjugate arrays give the adjoint matrix** · theorem. `tripleMatrix_conj_neg`: Replacing both coefficient arrays by their conjugates gives the conjugate transpose of the original triple matrix. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelProfiles.lean#L248).

**Conjugate model values above the plane** · theorem. `planeValue_neg_of_conj`: At nonnegative height, conjugate closure makes the matrix model's value at the negative label the conjugate of its value at the original label. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelProfiles.lean#L257).

**Negative coupling is the adjoint** · theorem. `couplingModel_neg`: At a valid cell point, the coupling matrix for the negative label is the conjugate transpose of the original coupling matrix. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelProfiles.lean#L263).

**Read the band source as model coupling** · theorem. `bandLinear_eq`: The linear band-source term is twice the model interaction of the retained upper profile with the band profile. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelProfiles.lean#L274).

**Source section `SquareIntegrable`.**

**Measurability from finitely many entries** · theorem. `aesm_of_components`: A continuous function of finitely many almost-everywhere measurable coordinates is almost-everywhere measurable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelProfiles.lean#L331).

**Profile squared norm is continuous** · theorem. `continuous_sum_normSq`: The sum of squared norms of the twelve profile coordinates depends continuously on the profile. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelProfiles.lean#L336).

**Square-integrable cell profile** · theorem. `isSqOn_of_bounded`: Under the stated hypotheses, each coordinate is measurable and the radius-weighted sum of squared coordinate norms is integrable on the cell. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelProfiles.lean#L339).

**Combine square-integrable profiles** · theorem. `isSqOn_add_smul`: The sum of one square-integrable cell profile and a scalar multiple of another remains square-integrable with radius weight. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelProfiles.lean#L352).

**Square-integrable cell profile** · theorem. `isSqOn_congr`: Under the stated hypotheses, each coordinate is measurable and the radius-weighted sum of squared coordinate norms is integrable on the cell. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelProfiles.lean#L382).

**The charge form is continuous** · theorem. `chargeForm_continuous`: For fixed real curl, gradient and velocity coefficients, the charge form depends continuously on the twelve-coordinate profile. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelProfiles.lean#L387).

**Gradient slots fit in the total norm** · theorem. `cnormSq_gradOf_le`: The gradient block's squared norm is at most the sum of squared norms of all twelve coordinates. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelProfiles.lean#L391).

**Velocity slots fit in the total norm** · theorem. `cnormSq_velOf_le`: The velocity block's squared norm is at most the sum of squared norms of all twelve coordinates. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelProfiles.lean#L396).

**Curl costs at most twice gradient energy** · theorem. `cnormSq_curl_le`: The curl's squared coordinate norm is at most twice the gradient array's squared coordinate norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelProfiles.lean#L402).

**Bound the absolute charge form** · theorem. `abs_chargeForm_le`: The absolute charge form is bounded by (2|c₁|+|c₂|+|c₃|) times the total squared coordinate norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelProfiles.lean#L417).

**Finite profile energy pays for charges** · theorem. `integrableOn_chargeForm`: A profile with finite radial-weighted squared norm has integrable radial-weighted curl, gradient and velocity charge form for any fixed real coefficients. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelProfiles.lean#L434).

### Breakdown.CertCell.AssemblyPotentialModelTorus

This file averages the model interaction over time and rotation, keeping the error, high-degree and long-mode balancing charges explicit. Appendix B.3: local stretching, potential forms and mode elimination, (B.25)–(B.37).

**Source section `Pointwise`.**

**Balance a high-degree interaction** · theorem. `high_pointwise`: Positive balancing parameters bound twice the real high-degree interaction below by minus the own and partner charge forms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorus.lean#L22).

**Charge the model-error interaction** · theorem. `rest_pointwise`: The model-error self and cross interaction is bounded below by minus the explicit own and partner approximation charges. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorus.lean#L64).

**Source section `TorusCore`.**

**Continuity gives torus integrability** · theorem. `torusIntegrable_of_cont`: A continuous function of time and angle is integrable on the compact time-angle box. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorus.lean#L87).

**Subtract matrices inside their pairing** · theorem. `pairSesq_sub_mat`: Pairing with a matrix difference equals the difference of the two matrix pairings. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorus.lean#L94).

**Add in the second matrix-pairing slot** · theorem. `pairSesq_add_right`: The matrix sesquilinear pairing is additive in its second vector argument. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorus.lean#L98).

**Scale the second pairing argument** · theorem. `pairSesq_smul_right`: Scaling the second vector of the matrix sesquilinear pairing scales the pairing by the same complex scalar. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorus.lean#L102).

**Add Fourier coefficient families** · theorem. `waveSum_add`: The finite Fourier synthesis of the sum of two coefficient families equals the sum of their syntheses. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorus.lean#L108).

**Scale every Fourier coefficient** · theorem. `waveSum_smul`: Scaling every vector coefficient in a finite Fourier synthesis scales the synthesized vector by the same complex scalar. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorus.lean#L113).

**Synthesize a disjoint union of labels** · theorem. `waveSum_union`: For disjoint label sets, synthesis of the piecewise coefficient family is the sum of the two synthesized waves. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorus.lean#L120).

**Triple-matrix entries integrate** · theorem. `tripleMatrix_entry_integrable`: Torus integrability of the strain and curl-gradient coefficient entries gives torus integrability of every triple-matrix entry. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorus.lean#L133).

**Finite-wave charge forms integrate** · theorem. `chargeForm_wave_integrable`: The curl, gradient and velocity charge form of a finite Fourier wave sum is torus-integrable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorus.lean#L142).

**Real mean of a matrix wave product** · theorem. `torusProduct_re`: The real coefficient-pair sum equals the real part of the mean of the corresponding synthesized matrix pairing. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorus.lean#L146).

**Source section `TorusMain`.**

**Own charge for the model error** · definition. `epsOwnForm`: This form assigns the model-error curl, gradient and velocity costs to the retained profile. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorus.lean#L161).

**Partner charge for the model error** · definition. `epsPartnerForm`: This form assigns the complementary model-error costs to the profile paired with the retained profile. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorus.lean#L164).

**Young-weighted self charge** · definition. `ownForm`: This self charge uses curl coefficient youngCurl times highStrain and gradient and velocity coefficients (3/(2sqrt(2))) times highGrad times their respective Young weights. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorus.lean#L167).

**High-mode partner charge** · definition. `partnerForm`: This form divides the high-mode bounds by the positive balancing weights for curl, gradient and velocity. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorus.lean#L170).

**Bound on the symmetric matrix part** · proposition definition. `IsSymOpBound`: This predicate bounds the squared norm of the symmetrized matrix on every complex three-vector by c² times its squared norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorus.lean#L173).

**Bound on a complex matrix** · proposition definition. `IsOpBound`: This predicate bounds the squared norm of the matrix on every complex three-vector by c² times its squared norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorus.lean#L176).

**Average the approximation-error bound** · theorem. `torus_core_eps`: The torus-averaged model comparison holds after the approximation and high-degree charges are subtracted, with the high-low interaction retained explicitly. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorus.lean#L179).

**Source section `TorusLong`.**

**Charge the long-mode interactions** · interface proposition. `TorusLongStatement`: This predicate requires that under the cutoff, vanishing-coefficient and operator-bound hypotheses, the long-mode interaction is bounded below by its class-dependent own and partner charges. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorus.lean#L339).

Proved by `Breakdown.CertCell.Assembly.Internal.ModelPart.torusLongStatement_holds`.

**Split a sum over two disjoint classes** · theorem. `sum_ite_two`: A sum over the disjoint union with class-selected values equals the two separate class sums. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorus.lean#L356).

**Split a sum over three disjoint classes** · theorem. `sum_ite_three`: A sum over three disjoint classes with selected values equals the three separate sums. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorus.lean#L365).

**Subtract coefficient-pairing sums** · theorem. `coefSum_of_sub`: An identity expressing every matrix coefficient as a difference passes to the finite double sum of real coefficient pairings. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorus.lean#L379).

**Split the partner coefficient sum** · theorem. `coefSum_union`: The coefficient interaction over a disjoint union of partner labels equals the sum of the two class interactions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorus.lean#L391).

**Split three partner coefficient classes** · theorem. `coefSum_union_three`: The coefficient interaction over the resolved, band and deactivated classes equals their three separate interactions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorus.lean#L400).

**Separate the doubled partner term** · theorem. `coefSum_add_smul`: Replacing the second vector family by X plus twice O splits the finite real coefficient-pairing sum into its X self term plus twice its X-O cross term. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorus.lean#L412).

**Average all model-comparison charges** · theorem. `torus_core`: The torus comparison combines approximation, high-degree and long-mode costs over the resolved, band and deactivated partner classes. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorus.lean#L424).

### Breakdown.CertCell.AssemblyPotentialModelTorusLong

This file splits harmonics at the long-mode cutoff and bounds the surviving interactions with different charges below and above that cutoff. Appendix B.3: local stretching, potential forms and mode elimination, (B.25)–(B.37).

**Source section `Pointwise`.**

**Balance a stretching cross interaction** · theorem. `young_pointwise`: Young's inequality and the operator bounds control the cross interaction by the own and reciprocal partner charge forms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorusLong.lean#L23).

**Self-interaction charge** · definition. `selfForm`: This quadratic form uses the same length scale in the gradient and reciprocal velocity charges. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorusLong.lean#L65).

**Cross-interaction charge** · definition. `crossForm`: This form assigns the cross-term curl, gradient and velocity costs to the first profile. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorusLong.lean#L68).

**Partner-interaction charge** · definition. `partForm`: This form assigns the complementary costs to the profile paired in the long-mode estimate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorusLong.lean#L71).

**Long-interaction self charge** · definition. `ownForm`: This self charge uses curl coefficient twice the long strain bound, gradient coefficient (3/(2sqrt(2))) times the long gradient bound times the sum of the two lengths, and velocity coefficient twice that factor divided by the first length. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorusLong.lean#L74).

**Split the long-mode own charge** · theorem. `ownForm_eq`: The own long-mode charge is the sum of its self-interaction charge and cross-interaction charge. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorusLong.lean#L77).

**Scale the long-mode self charge** · theorem. `self_scaled`: A positive balance parameter gives a lower bound for twice the real interaction using reciprocal multiples of the self charge. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorusLong.lean#L82).

**Scale the long-mode cross charge** · theorem. `cross_scaled`: A positive balance parameter gives a lower bound using the own cross charge and its complementary partner charge. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorusLong.lean#L100).

**Add in the first matrix-pairing slot** · theorem. `pairSesq_add_left'`: The matrix sesquilinear pairing is additive in its first vector argument. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorusLong.lean#L118).

**Add in the second matrix-pairing slot** · theorem. `pairSesq_add_right'`: The matrix sesquilinear pairing is additive in its second vector argument. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorusLong.lean#L122).

**Remove the low-low long interaction** · theorem. `long_pointwise`: The interaction remaining after its low-low block is removed is bounded below by the cutoff-dependent low and high charges. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorusLong.lean#L126).

**Source section `Torus`.**

**Continuity gives torus integrability** · theorem. `long_torusIntegrable_of_cont`: A continuous function of time and angle is integrable on the compact time-angle box. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorusLong.lean#L157).

**Triple-matrix entries integrate** · theorem. `long_entry_integrable`: Torus integrability of the strain and curl-gradient coefficient entries gives torus integrability of every triple-matrix entry. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorusLong.lean#L164).

**Weighted finite-wave charges integrate** · theorem. `long_form_integrable`: Multiplying the finite-wave charge form by a fixed real prefactor preserves torus integrability. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorusLong.lean#L173).

**Long-mode product as a coefficient sum** · theorem. `long_product_re`: The real mean of the long-mode matrix pairing equals the real sum of its difference-label coefficient interactions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorusLong.lean#L178).

**Split a wave by a label predicate** · theorem. `waveSum_filter_split`: The full finite wave is the sum of its predicate-selected and complementary waves. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorusLong.lean#L186).

**Split the cutoff-weighted charge** · theorem. `sum_class_split`: The cutoff-weighted sum separates into the low-class balance multiple and the high-class factor 1+1/β. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorusLong.lean#L193).

**Absent low shifts remove the low block** · theorem. `low_block_zero`: If all matrix Fourier coefficients with first-label magnitude at most twice N vanish, the double pairing sum restricted to two label sets of magnitude at most N vanishes. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorusLong.lean#L204).

**Source section `Main`.**

**The long-mode class estimate** · theorem. `long_class_bound`: Under the coefficient-gap and operator bounds, the total long-mode interaction is bounded below by its cutoff-weighted own and partner charges. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorusLong.lean#L225).

### Breakdown.CertCell.AssemblyPotentialModelTorusMean

This file defines the normalized time-angle mean and states its linearity, orthogonality and matrix-product interfaces. Appendix B.3: local stretching, potential forms and mode elimination, (B.25)–(B.37).

**Complex matrix pairing** · definition. `pairSesq`: This sesquilinear pairing conjugates the first coordinate vector before multiplying by the matrix and the second vector. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorusMean.lean#L17).

**Normalized time-angle mean** · definition. `torusMean`: This mean integrates over one unit of time and a full rotation and divides by 2π. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorusMean.lean#L20).

**Integrability on the time-angle box** · proposition definition. `IsTorusIntegrable`: This predicate requires integrability with respect to the product measure on the time-angle box. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorusMean.lean#L23).

**Finite harmonic synthesis** · definition. `waveSum`: This vector is the finite sum of the supplied coefficients multiplied by their label phases. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorusMean.lean#L26).

**Matrix harmonic coefficient** · definition. `torusCoef`: This matrix takes the normalized mean of each matrix entry against the conjugate label phase. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorusMean.lean#L29).

**Torus mean preserves addition** · interface proposition. `TorusMeanAddStatement`: This predicate requires that the normalized mean preserves addition of integrable functions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorusMean.lean#L32).

Proved by `Breakdown.CertCell.Assembly.Internal.TorusMean.torusMean_add`. The companion records the supplying lambda or structure field.

**Torus mean preserves finite sums** · interface proposition. `TorusMeanSumStatement`: This predicate requires that the normalized mean commutes with a finite sum of integrable harmonic functions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorusMean.lean#L36).

Proved by `Breakdown.CertCell.Assembly.Internal.TorusMean.torusMean_sum`. The companion records the supplying lambda or structure field.

**Order of real torus means** · interface proposition. `TorusMeanReMonoStatement`: This predicate requires that a pointwise inequality between real parts on the time-angle box gives the same inequality between their means. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorusMean.lean#L40).

Proved by `Breakdown.CertCell.Assembly.Internal.TorusMean.torusMean_re_mono`. The companion records the supplying lambda or structure field.

**Bounded torus functions are integrable** · interface proposition. `TorusBoundedIntegrableStatement`: This predicate requires that an almost-everywhere measurable function bounded on the time-angle box is integrable there. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorusMean.lean#L45).

Proved by `Breakdown.CertCell.Assembly.Internal.TorusMean.bounded_integrable`. The companion records the supplying lambda or structure field.

**Mean of an integer harmonic** · interface proposition. `TorusHarmonicMeanStatement`: This predicate requires that the torus mean of an integer harmonic is one at the zero frequency and zero otherwise. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorusMean.lean#L49).

Proved by `Breakdown.CertCell.Assembly.Internal.TorusMean.torusMean_phase`. The companion records the supplying lambda or structure field.

**Mean of a lattice label phase** · interface proposition. `TorusLabelMeanStatement`: This predicate requires that for positive symmetry order, the conjugate label phase has mean one only at the zero label. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorusMean.lean#L52).

Proved by `Breakdown.CertCell.Assembly.Internal.TorusMean.torusMean_label`. The companion records the supplying lambda or structure field.

**Mean of a matrix wave product** · interface proposition. `TorusProductStatement`: This predicate requires that the mean of the synthesized matrix pairing equals the double sum using matrix coefficients at the difference labels. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorusMean.lean#L55).

Proved by `Breakdown.CertCell.Assembly.Internal.TorusMean.torusMean_product`. The companion records the supplying lambda or structure field.

**The seven torus-mean interfaces** · structure. `TorusFacts`: This predicate requires that the mean's linearity, order, integrability, orthogonality and product interfaces hold together. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorusMean.lean#L61).

### Breakdown.CertCell.AssemblyPotentialModelTorusMeanFacts

This file proves the torus-mean interfaces, including harmonic orthogonality and the conversion of a physical product into a difference-label coefficient sum. Appendix B.3: local stretching, potential forms and mode elimination, (B.25)–(B.37).

**Source namespace `Breakdown.CertCell.Assembly.Internal.TorusMean`.**

**Use the product box measure for the mean** · theorem. `torusMean_eq_box`: The iterated time-angle mean equals the integral against the product box measure divided by 2π. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorusMeanFacts.lean#L19).

**Scale a torus mean** · theorem. `Breakdown.CertCell.AssemblyPotentialModelTorusMeanFacts.torusMean_const_mul`: Taking the torus mean commutes with multiplication by a fixed complex scalar. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorusMeanFacts.lean#L24).

**Add torus-integrable functions** · theorem. `isTorusIntegrable_add`: The sum of two integrable functions on the time-angle box is integrable there. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorusMeanFacts.lean#L30).

**Finite sums stay torus-integrable** · theorem. `isTorusIntegrable_sum`: A finite sum of functions integrable on the time-angle box is integrable there. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorusMeanFacts.lean#L34).

**Add two integrable torus means** · theorem. `torusMean_add`: The torus mean of two integrable functions added together equals the sum of their means. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorusMeanFacts.lean#L42).

**Average a finite sum term by term** · theorem. `torusMean_sum`: The torus mean of a finite sum of integrable functions equals the sum of their torus means. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorusMeanFacts.lean#L47).

**The box measure is supported in its box** · theorem. `ae_box`: Almost every point for the box measure lies in its stated time-angle rectangle. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorusMeanFacts.lean#L53).

**Take the real part inside the mean** · theorem. `re_torusMean`: The real part of the normalized complex mean is the normalized integral of the real part. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorusMeanFacts.lean#L58).

**The mean preserves real inequalities** · theorem. `torusMean_re_mono`: An inequality between real parts on the time-angle box passes to the real parts of their integrable means. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorusMeanFacts.lean#L66).

**Bounded measurable torus functions fit** · theorem. `bounded_integrable`: Almost-everywhere strong measurability and a uniform bound on the half-open time-angle box imply torus integrability. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorusMeanFacts.lean#L75).

**Nonzero exponential frequencies cancel** · theorem. `integral_exp_line`: Under the nonzero-frequency and full-period hypotheses, the complex exponential has integral zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorusMeanFacts.lean#L84).

**Zero frequency integrates to the length** · theorem. `integral_exp_line_zero`: The integral of the zero-frequency complex exponential equals the interval length. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorusMeanFacts.lean#L101).

**Integrate out the azimuthal phase** · theorem. `inner_phase`: Integrating an integer harmonic over the angle gives zero except at azimuthal frequency zero, where the factor is 2π. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorusMeanFacts.lean#L105).

**Only the zero harmonic has nonzero mean** · theorem. `torusMean_phase`: The normalized mean of an integer harmonic is one at frequency zero and zero at every other frequency. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorusMeanFacts.lean#L126).

**Conjugation negates the label harmonic** · theorem. `conj_labelPhase`: The conjugate label phase equals the harmonic phase at the negative of that label's harmonic. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorusMeanFacts.lean#L153).

**Split a conjugate difference phase** · theorem. `conj_labelPhase_sub`: The conjugate phase at a label difference equals the conjugate first-label phase times the second-label phase. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorusMeanFacts.lean#L162).

**Only the zero label has zero frequency** · theorem. `labelHarmonic_eq_zero_iff`: For positive symmetry order, the label's frequency pair is zero exactly when the label itself is zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorusMeanFacts.lean#L172).

**Only the zero label has mean one** · theorem. `torusMean_label`: For positive symmetry order, the mean conjugate label phase is one at label zero and zero otherwise. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorusMeanFacts.lean#L187).

**Conjugate phases preserve integrability** · theorem. `isTorusIntegrable_conj_label_mul`: Multiplying a torus-integrable function by a conjugate label phase preserves torus integrability. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorusMeanFacts.lean#L193).

**Expand the pairing of two finite waves** · theorem. `pairSesq_waveSum`: The matrix pairing of two synthesized waves expands into coefficient pairs weighted by their difference-label phase. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorusMeanFacts.lean#L204).

**Coefficient formula for a matrix product** · theorem. `torusMean_product`: The mean matrix pairing of two finite waves equals the double coefficient sum using the matrix's difference-label Fourier coefficients. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorusMeanFacts.lean#L235).

**Source namespace `Breakdown.CertCell.Assembly.Internal`.**

**The seven torus-mean interfaces** · theorem. `torusFacts`: Under the stated hypotheses, the mean's linearity, order, integrability, orthogonality and product interfaces hold together. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorusMeanFacts.lean#L267).

### Breakdown.CertCell.AssemblyPotentialParts

This file names the potential estimate's intermediate quantities and stages, then states how their proofs combine into the potential-stage interface. Appendix B.3: local stretching, potential forms and mode elimination, (B.25)–(B.37).

**Source section `PotentialParts`.**

**True stretching coefficient matrix** · definition. `trueCoupling`: This matrix is built from harmonic coefficients of the given field's symmetric gradient and curl gradient. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialParts.lean#L20).

**Restrict a profile by label** · definition. `restrictTo`: This operation keeps the profile on a chosen set of labels and assigns zero to all other labels. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialParts.lean#L28).

**Physical harmonic profiles** · definition. `trueProfiles`: This profile packs the perturbation's actual harmonic velocity and gradient into twelve coordinates. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialParts.lean#L31).

**Profile after removing the upper part** · definition. `otherProfiles`: This profile subtracts the retained upper polynomial profile from the full physical profile. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialParts.lean#L35).

**Resolved projection-tail profiles** · definition. `tailProfiles`: This profile keeps each resolved harmonic's projection tail and is zero on unresolved labels. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialParts.lean#L39).

**Labels outside resolved and band sets** · definition. `deactivatedSet`: This set contains labels in neither the resolved set nor the band set. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialParts.lean#L43).

**True integrated stretching form** · definition. `trueStretch`: This form sums radius-weighted cell pairings of the true coupling across all labels and the chosen harmonic shifts. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialParts.lean#L46).

**Finite model coupling integral** · definition. `modelPair`: This form sums radius-weighted model matrix pairings over two finite label sets. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialParts.lean#L50).

**Integrated local leaf pairing** · definition. `leafPair`: This form sums the local leaf-matrix pairing over resolved labels and integrates it with the cylindrical radius. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialParts.lean#L54).

**Integrated absorption cost** · definition. `alAmount`: This amount integrates the weighted curl, gradient and velocity absorption terms over the resolved labels. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialParts.lean#L58).

**Integrated box-pair penalty** · definition. `boxPairAmount`: This amount sums the radius-weighted box-pair penalty over resolved labels. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialParts.lean#L63).

**Integrated charge over chosen labels** · definition. `formAmount`: This amount integrates a velocity-gradient charge over the supplied finite set of harmonic labels. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialParts.lean#L67).

**Deactivated partners of resolved modes** · definition. `deactPartners`: This finite set contains resolved labels shifted by model harmonics that fall outside both the resolved and band sets. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialParts.lean#L71).

**Integrated label-dependent charge** · definition. `labelFormAmount`: This amount integrates the supplied label-dependent charge over a finite label set. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialParts.lean#L75).

**Additional omitted-mode charges** · definition. `extraChargeDensity`: This density adds the entry's curl, gradient and velocity charges multiplied by their mode squared norms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialParts.lean#L79).

**Total extra omitted-mode charge** · definition. `chargeSurplus`: This amount integrates the additional charge density over every unresolved label. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialParts.lean#L85).

**Omitted-mode stretching budget** · definition. `stretchChargeAmount`: This amount subtracts the off-mode density and extra charges from the full unresolved-mode density and integrates the remainder. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialParts.lean#L90).

**Partner cost across mode groups** · definition. `groupPartnerAmount`: This amount sums group partner charges divided by the corresponding balancing parameter. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialParts.lean#L98).

**Own cost across mode groups** · definition. `groupOwnAmount`: This amount sums resolved group charges multiplied by the corresponding balancing parameter. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialParts.lean#L102).

**Expand physical stretching in modes** · proposition definition. `StretchExpansion`: This predicate requires that the integrated physical stretching equals the true coefficient form on the full harmonic profile. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialParts.lean#L109).

**Split actual data into low part and tail** · proposition definition. `LowTailSplit`: This predicate requires that every resolved physical profile is almost everywhere the retained polynomial profile plus its projection tail. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialParts.lean#L113).

**Split stretching by profile classes** · proposition definition. `StretchSplit`: This predicate requires that the true stretching form separates into retained self-interaction, three retained cross interactions and the remainder self-interaction. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialParts.lean#L119).

**Retained leaf energy and tail budget** · proposition definition. `LeafSplit`: This predicate requires that the change from low to full leaf energy, with the box penalty, is bounded by resolved density after energy and tail credits are removed. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialParts.lean#L139).

**Sharp bound on the remainder profile** · proposition definition. `SharpStage`: This predicate requires that the remainder's leaf and stretching forms plus its omitted-mode budget cover the box penalty after absorption costs. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialParts.lean#L146).

**Compare model and true interactions** · proposition definition. `ModelStage`: This predicate requires that the model coupling after the explicit error, long-mode and high-degree charges is bounded by the corresponding true retained interactions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialParts.lean#L159).

**Charge the retained-tail interaction** · proposition definition. `TailCrossStage`: This predicate requires that the retained-tail cross interaction is bounded below by minus the port form and the balanced gradient and velocity tail costs. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialParts.lean#L206).

**Charge grouped deactivated modes** · proposition definition. `GroupStage`: This predicate requires that twice the retained interaction with deactivated partners is bounded below by minus the grouped own and partner charges. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialParts.lean#L217).

**Pay all omitted-mode charges** · proposition definition. `ChargeStage`: This predicate requires that the band, leakage, group, error and slack costs fit inside the extra omitted-mode charge surplus. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialParts.lean#L225).

**Bound high-degree costs on the tail** · proposition definition. `TailHighStage`: This predicate requires that the high-degree partner cost of the resolved tail is controlled by explicit gradient and velocity tail norms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialParts.lean#L242).

**Pay resolved approximation costs** · proposition definition. `EpsResolvedStage`: This predicate requires that the error and long-mode partner costs on the resolved remainder are covered by the corresponding box-pair penalty. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialParts.lean#L249).

**Identities for budget cancellation** · proposition definition. `SplitIdentities`: This predicate requires that the omitted budget, leaf difference and tail absorption admit the three exact decompositions used when the stage inequalities are added. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialParts.lean#L258).

**Source section `Holds`.**

**Split actual data into low part and tail** · interface proposition. `LowTailSplitHolds`: This interface requires that every resolved physical profile is almost everywhere the retained polynomial profile plus its projection tail whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialParts.lean#L278).

Proved by `Breakdown.CertCell.Assembly.lowTailSplit_holds`.

**Retained leaf energy and tail budget** · interface proposition. `LeafSplitHolds`: This interface requires that the change from low to full leaf energy, with the box penalty, is bounded by resolved density after energy and tail credits are removed whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialParts.lean#L282).

Proved by `Breakdown.CertCell.Assembly.leafSplit_holds`.

**Expand physical stretching in modes** · interface proposition. `StretchExpansionHolds`: This interface requires that the integrated physical stretching equals the true coefficient form on the full harmonic profile whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialParts.lean#L286).

Proved by `Breakdown.CertCell.Assembly.stretchExpansionHolds`.

**Split stretching by profile classes** · interface proposition. `StretchSplitHolds`: This interface requires that the true stretching form separates into retained self-interaction, three retained cross interactions and the remainder self-interaction whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialParts.lean#L292).

Proved by `Breakdown.CertCell.Assembly.stretchSplit`.

**Sharp bound on the remainder profile** · interface proposition. `SharpStageHolds`: This interface requires that the remainder's leaf and stretching forms plus its omitted-mode budget cover the box penalty after absorption costs whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialParts.lean#L298).

Proved by `Breakdown.CertCell.Assembly.Internal.Sharp.sharpStageHolds_of`, `Breakdown.CertCell.Assembly.sharpStageHolds`.

**Pay resolved approximation costs** · interface proposition. `EpsResolvedStageHolds`: This interface requires that the error and long-mode partner costs on the resolved remainder are covered by the corresponding box-pair penalty whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialParts.lean#L304).

Proved by `Breakdown.CertCell.Assembly.epsResolvedStage_holds`, `Breakdown.CertCell.Assembly.epsResolvedStage_holds_of`.

**Compare model and true interactions** · interface proposition. `ModelStageHolds`: This interface requires that the model coupling after the explicit error, long-mode and high-degree charges is bounded by the corresponding true retained interactions whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialParts.lean#L310).

Proved by `Breakdown.CertCell.Assembly.modelStageHolds`, `Breakdown.CertCell.Assembly.Internal.ModelPart.modelStage_of_point`.

**Charge the retained-tail interaction** · interface proposition. `TailCrossStageHolds`: This interface requires that the retained-tail cross interaction is bounded below by minus the port form and the balanced gradient and velocity tail costs whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialParts.lean#L316).

Proved by `Breakdown.CertCell.Assembly.tailCrossStage_holds`.

**Charge grouped deactivated modes** · interface proposition. `GroupStageHolds`: This interface requires that twice the retained interaction with deactivated partners is bounded below by minus the grouped own and partner charges whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialParts.lean#L322).

Proved by `Breakdown.CertCell.Assembly.Internal.groupStageHolds_of`, `Breakdown.CertCell.Assembly.groupStageHolds`.

**Pay all omitted-mode charges** · interface proposition. `ChargeStageHolds`: This interface requires that the band, leakage, group, error and slack costs fit inside the extra omitted-mode charge surplus whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialParts.lean#L327).

Proved by `Breakdown.CertCell.Assembly.chargeStageHolds`.

**Bound high-degree costs on the tail** · interface proposition. `TailHighStageHolds`: This interface requires that the high-degree partner cost of the resolved tail is controlled by explicit gradient and velocity tail norms whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialParts.lean#L333).

Proved by `Breakdown.CertCell.Assembly.tailHighStage_holds`.

**Identities for budget cancellation** · interface proposition. `SplitIdentitiesHolds`: This interface requires that the omitted budget, leaf difference and tail absorption admit the three exact decompositions used when the stage inequalities are added whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialParts.lean#L338).

Proved by `Breakdown.CertCell.Assembly.splitIdentities_of_tail`, `Breakdown.CertCell.Assembly.splitIdentities_holds`.

**Assemble the potential-stage bound** · interface proposition. `PotentialAssemblyHolds`: This interface requires that the full list of stretching, leaf, sharp, model, tail, group, charge and splitting stages implies the potential-stage inequality whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialParts.lean#L344).

Proved by `Breakdown.CertCell.Assembly.potentialAssembly_holds`.

**The cell potential-stage estimate** · theorem. `potentialStage_of_parts`: Under the stated hypotheses, the retained potential form and its band, leakage, credit and slack costs are covered by resolved density, omitted charge and stretching after energy credits. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialParts.lean#L355).

### Breakdown.CertCell.AssemblyPotentialSharp

This file combines the resolved leaf bounds, omitted-mode charges and the stretching symbol estimate into a nonnegative expression at almost every cell point. Appendix B.3: local stretching, potential forms and mode elimination, (B.25)–(B.37).

**Source section `Defs`.**

**Remainder for a physical cell state** · definition. `otherAt`: This is the remainder profile evaluated at the cell state supplied by the physical fields and auxiliary coordinates. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharp.lean#L27).

**Radius-weighted leaf density** · definition. `leafCore`: This density is the real self-pairing with the local leaf matrix multiplied by cylindrical radius. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharp.lean#L32).

**Radius-weighted box penalty** · definition. `boxCore`: This density is the leaf's box-pair penalty multiplied by cylindrical radius. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharp.lean#L35).

**Weighted absorption density** · definition. `absorbCore`: This density combines curl, gradient and velocity squared norms with the leaf absorption constants and line weight. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharp.lean#L38).

**Unresolved stretching charge density** · definition. `chargeTerm`: This term is zero on resolved labels and otherwise retains the full density after the off-mode and extra charges are removed. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharp.lean#L43).

**One label's stretching interaction** · definition. `stretchTerm`: This term sums radius-weighted true-coupling interactions with the selected harmonic shifts. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharp.lean#L51).

**Source namespace `Breakdown.CertCell.Assembly.Internal.Sharp`.**

**Split absorption by orthogonality** · interface proposition. `AbsorbSplitStatement`: This predicate requires that the remainder absorption equals the absorption of its band polynomial part plus the absorption of its projection tail. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharp.lean#L56).

Proved by `Breakdown.CertCell.Assembly.absorbSplitStatement`.

**Regularity of the sharp-stage sums** · interface proposition. `SharpRegularStatement`: This predicate requires that the leaf, box, absorption, charge and stretching terms have the integrability and summability needed for the sharp-stage integration. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharp.lean#L64).

Proved by `Breakdown.CertCell.Assembly.Internal.Sharp.sharpRegular`.

**Combine the three pointwise bounds** · theorem. `sum_core`: The resolved leaf lower bounds, unresolved charge bounds and total stretching lower bound give a nonnegative combined sum. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharp.lean#L85).

**Rotate plane points into space** · theorem. `cylPoint_eq`: The cylindrical point at radius r, angle φ and height z is the axial rotation of (r,0,z). [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharp.lean#L115).

**A quadratic sees the symmetric part** · theorem. `inner_strainOf`: Pairing a vector with the reference strain gives the same real value as pairing it with the reference gradient. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharp.lean#L119).

**Mean curl gradient at the zero label** · theorem. `labelGrad_zero_vort`: The zero-label curl-gradient coefficient is the zero harmonic of the weak vorticity-gradient map. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharp.lean#L127).

**Unresolved remainder equals the profile** · theorem. `other_unresolved`: On an unresolved label, subtracting the upper polynomial profile leaves the entire physical band profile unchanged. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharp.lean#L135).

**One entry of the mean curl gradient** · theorem. `labelGrad_zero_vort_apply`: Each entry of the zero-label curl gradient equals the corresponding zero-mode entry of the weak vorticity-gradient map. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharp.lean#L143).

**Line weight is positive off the axis** · theorem. `lineWeight_pos`: At a nonzero radial coordinate in the cell rectangle, the line weight is strictly positive. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharp.lean#L152).

**The sharp remainder is nonnegative** · theorem. `point_nonneg`: The assembly, field expansion and summability hypotheses make the resolved leaf-minus-box-plus-absorption terms plus all charge and stretching terms nonnegative at each non-axis cell point. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharp.lean#L162).

**Sharp bound on the remainder profile** · theorem. `sharpStageHolds_of`: Under the stated hypotheses, the remainder's leaf and stretching forms plus its omitted-mode budget cover the box penalty after absorption costs. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharp.lean#L257).

### Breakdown.CertCell.AssemblyPotentialSharpAbsorb

This file uses polynomial orthogonality to split the absorption cost of a remainder into its retained polynomial part and its tail, with the cross integral equal to zero. Appendix B.3: local stretching, potential forms and mode elimination, (B.25)–(B.37).

**Source section `SplitHelpers`.**

**Curl, gradient and velocity absorption** · definition. `absorbDensity`: This density is the weighted sum of the curl, gradient and velocity squared norms of a twelve-component vector. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpAbsorb.lean#L28).

**Polarized absorption cross term** · definition. `absorbCross`: This real bilinear expression pairs the curl, gradient and velocity blocks with their respective absorption weights. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpAbsorb.lean#L31).

**Expand the squared norm of a complex sum** · theorem. `norm_add_sq_expand`: The squared norm of a+b is the two squared norms plus twice the real part of b times the conjugate of a. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpAbsorb.lean#L36).

**Gradient slots preserve addition** · theorem. `strainOfVec_add`: The gradient matrix extracted from a sum of profiles is the sum of their extracted gradient matrices. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpAbsorb.lean#L42).

**Velocity slots preserve addition** · theorem. `velOf_add`: The velocity extracted from a sum of profiles is the sum of their extracted velocities. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpAbsorb.lean#L45).

**Matrix curls preserve addition** · theorem. `curlComp_add`: The curl of the entrywise matrix sum equals the sum of the matrix curls. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpAbsorb.lean#L47).

**Polarize the absorption density** · theorem. `absorbDensity_add`: Absorption of a sum equals the two absorption densities plus twice their absorption cross term. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpAbsorb.lean#L56).

**Integrable with zero integral** · proposition definition. `NullOn`: This predicate requires a function to be integrable on the set and to have integral zero there. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpAbsorb.lean#L72).

**Equal functions share a zero integral** · theorem. `nullOn_congr`: Replacing an integrable zero-integral function by an equal function preserves both properties. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpAbsorb.lean#L74).

**Add two zero-integral functions** · theorem. `nullOn_add`: The sum of two integrable functions with zero integral is integrable with zero integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpAbsorb.lean#L80).

**Scale a function with integral zero** · theorem. `nullOn_mul`: Multiplying an integrable zero-integral function by a real constant preserves its zero integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpAbsorb.lean#L84).

**A finite sum still has zero integral** · theorem. `nullOn_sum`: A finite sum of integrable zero-integral functions is integrable and has zero integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpAbsorb.lean#L88).

**A tail pairs with a continuous test** · theorem. `weighted_product_integrable`: A measurable profile with finite line-weighted squared norm has integrable line-weighted product with a continuous cell test function. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpAbsorb.lean#L94).

**Retained profiles add with the state** · theorem. `Breakdown.CertCell.AssemblyPotentialSharpAbsorb.lowProfile_add`: The retained polynomial profile of a sum of cell states equals the sum of their retained profiles. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpAbsorb.lean#L118).

**Read the low profile's gradient block** · theorem. `strain_lowProfile`: The gradient block of the retained profile is its retained gradient polynomial. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpAbsorb.lean#L125).

**Read the low profile's velocity block** · theorem. `vel_lowProfile`: The velocity block of the retained profile is its retained velocity polynomial. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpAbsorb.lean#L130).

**Degree of the low gradient coordinates** · theorem. `lowGrad_poly`: Each retained gradient coordinate belongs to the polynomial space at the layout's coefficient degree. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpAbsorb.lean#L135).

**Degree of the low velocity coordinates** · theorem. `lowVel_poly`: Each retained velocity coordinate belongs to the polynomial space one degree below the layout's gradient degree. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpAbsorb.lean#L143).

**Curl preserves the polynomial space** · theorem. `curl_poly`: Taking a curl component preserves the degree limits shared by the matrix entries. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpAbsorb.lean#L151).

**Expand the curl cross pairing** · theorem. `curl_cross_expand`: The real weighted curl pairing expands into the alternating-symbol sum of the gradient-entry pairings. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpAbsorb.lean#L157).

**A projection tail is orthogonal to lows** · theorem. `tail_term`: Each resolved tail coordinate pairs integrably to zero with every polynomial in its retained degree space. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpAbsorb.lean#L171).

**Absorption density is continuous** · theorem. `absorbDensity_continuous`: The curl, gradient and velocity absorption combination is a continuous function of the twelve-coordinate profile. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpAbsorb.lean#L202).

**Bound absorption by total profile energy** · theorem. `absorbDensity_abs_le`: The absolute absorption density is bounded by (2|cA|+|sA|+|vA|) times the total squared coordinate norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpAbsorb.lean#L206).

**Tail absorption density integrates** · theorem. `tail_density_integrable`: The potential conditions and cell-profile regularity make the line-weighted tail absorption density integrable for every label and fixed charge coefficients. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpAbsorb.lean#L229).

**Low-profile absorption integrates** · theorem. `low_density_integrable`: The line-weighted absorption density of each retained polynomial profile is integrable on its cell rectangle. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpAbsorb.lean#L256).

**The absorption cross term vanishes** · theorem. `cross_null`: The weighted absorption cross term between a retained polynomial profile and its projection tail is integrable and has zero integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpAbsorb.lean#L263).

**Absorption splits by orthogonality** · theorem. `mode_identity`: For orthogonal low and tail profiles, the line-weighted absorption integral is the sum of their separate absorption integrals. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpAbsorb.lean#L329).

**Source namespace `Breakdown.CertCell.Assembly.Internal.Sharp`.**

**Split total absorption** · theorem. `absorb_split`: The assembled absorption amount splits into the low-band amount and the tail amount under the stated profile orthogonality assumptions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpAbsorb.lean#L381).

### Breakdown.CertCell.AssemblyPotentialSharpFrame

This file transfers real coordinate bounds to complex harmonic slots by separating real and imaginary parts and preserving the rotated quadratic forms. Appendix B.3: local stretching, potential forms and mode elimination, (B.25)–(B.37).

**Real part of each harmonic slot** · definition. `slotRe`: This map replaces each complex slot by its real part embedded back into the complex numbers. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpFrame.lean#L20).

**Imaginary part of each harmonic slot** · definition. `slotIm`: This map replaces each complex slot by its imaginary part embedded back into the complex numbers. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpFrame.lean#L22).

**Real and imaginary pair-form split** · theorem. `pairForm_conj_split`: The sum of the two pair forms with conjugate opposite arguments equals twice the sum of the pair forms on the real and imaginary slot vectors separately. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpFrame.lean#L24).

**Two-term square-root bound** · theorem. `sqrt_cross_le`: For nonnegative a, b, c and d, the sum sqrt(a)sqrt(b) + sqrt(c)sqrt(d) is at most sqrt(a+c)sqrt(b+d). [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpFrame.lean#L78).

**Real velocity slots** · definition. `slotVelRe`: This vector reads the real parts of the three velocity slots. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpFrame.lean#L91).

**Imaginary velocity slots** · definition. `slotVelIm`: This vector reads the imaginary parts of the three velocity slots. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpFrame.lean#L93).

**Real gradient slots** · definition. `slotGradRe`: This array reads the real parts of the nine gradient slots. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpFrame.lean#L95).

**Imaginary gradient slots** · definition. `slotGradIm`: This array reads the imaginary parts of the nine gradient slots. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpFrame.lean#L97).

**Reconstruct real slots** · theorem. `slotRe_eq`: The real part of the combined velocity-gradient slot vector is reconstructed from its real velocity and gradient components. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpFrame.lean#L99).

**Reconstruct imaginary slots** · theorem. `slotIm_eq`: The imaginary part of the combined velocity-gradient slot vector is reconstructed from its imaginary velocity and gradient components. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpFrame.lean#L103).

**Split the complex curl norm** · theorem. `curl_norm_sq`: The squared norm of each complex curl component equals the sum of the squared curls of the real and imaginary gradient matrices. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpFrame.lean#L107).

**Split the complex velocity norm** · theorem. `vel_norm_sq`: The squared velocity norm equals the sum of the squared real and imaginary velocity coordinates. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpFrame.lean#L116).

**Split the complex gradient norm** · theorem. `grad_norm_sq`: The squared gradient norm equals the sum of the squared real and imaginary gradient entries. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpFrame.lean#L124).

**Rotations preserve inner products** · theorem. `rot_inner`: Applying the same axial rotation to two real vectors preserves their Euclidean inner product. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpFrame.lean#L169).

**Quadratic form in a rotated frame** · theorem. `frame_quad_eq`: The coordinate quadratic form of the rotated operator equals its Euclidean inner product on the rotated coordinate vector. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpFrame.lean#L172).

**Transfer the strain bound** · theorem. `strain_frame`: An upper quadratic bound for the operator transfers to the symmetric part of its matrix in an axially rotated orthonormal frame. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpFrame.lean#L186).

**Rotated coordinate vectors** · theorem. `frameUnit_eq`: The frame unit vector is the axial rotation of the corresponding standard coordinate vector. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpFrame.lean#L209).

**Coordinate vectors are orthonormal** · theorem. `inner_unitVector`: The Euclidean inner product of two standard coordinate vectors is one when their indices agree and zero otherwise. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpFrame.lean#L214).

**Recover the frame matrix** · theorem. `frameMap_rot_unit`: Applying the frame map to a rotated coordinate vector and rotating back recovers the corresponding matrix column. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpFrame.lean#L217).

**Transfer the wave bound** · theorem. `wave_frame`: The assumed operator error bound gives the same squared-norm bound for its matrix difference in the rotated frame. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpFrame.lean#L234).

### Breakdown.CertCell.AssemblyPotentialSharpLeaf

This file expresses the local leaf and omitted-mode inequalities in the same twelve coordinates used by the stretching symbol. Appendix B.3: local stretching, potential forms and mode elimination, (B.25)–(B.37).

**Two alternating-symbol encodings** · theorem. `permSign_eq`: The certificate permutation sign agrees with the alternating tensor after coercion to the complex numbers. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpLeaf.lean#L22).

**Match the curl encodings** · theorem. `Breakdown.CertCell.AssemblyPotentialSharpLeaf.curlComp_eq`: The certificate curl of a matrix equals the curl computed from its pair-indexed gradient array. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpLeaf.lean#L25).

**Curl squared norms agree** · theorem. `Breakdown.CertCell.AssemblyPotentialSharpLeaf.curlSq_strainOfVec`: The indexed curl squared norm equals the coordinate squared norm of the curl of the gradient block. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpLeaf.lean#L29).

**Gradient squared norms agree** · theorem. `Breakdown.CertCell.AssemblyPotentialSharpLeaf.sumSq_strainOfVec`: The indexed sum of gradient-entry squared norms equals the flattened gradient block's squared coordinate norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpLeaf.lean#L35).

**Velocity squared norms agree** · theorem. `Breakdown.CertCell.AssemblyPotentialSharpLeaf.vecSq_velOf`: The velocity squared norm equals the coordinate squared norm of the last three slots. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpLeaf.lean#L40).

**Match the point loss formulas** · theorem. `supLoss_eq`: The certificate supremum loss equals the point loss after splitting a twelve-coordinate vector into gradient and velocity slots. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpLeaf.lean#L42).

**Rejoin the twelve coordinates** · theorem. `pairVec_strainOfVec`: Recombining the gradient and velocity projections of a twelve-coordinate vector returns that vector. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpLeaf.lean#L47).

**Read the packed gradient** · theorem. `Breakdown.CertCell.AssemblyPotentialSharpLeaf.gradOf_pairVec`: The gradient projection of a packed gradient-velocity vector returns the original gradient entries. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpLeaf.lean#L51).

**Read the packed velocity** · theorem. `Breakdown.CertCell.AssemblyPotentialSharpLeaf.velOf_pairVec`: The velocity projection of a packed gradient-velocity vector returns the original velocity entries. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpLeaf.lean#L54).

**Cost of modifying stretch charges** · theorem. `quad_withStretch_diff`: Subtracting the modified allowance quadratic exposes exactly the curl, gradient, velocity and mixed-product stretch charges shown in the formula. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpLeaf.lean#L57).

**Pointwise leaf lower bound** · theorem. `leaf_point`: The leaf matrix dominates the point loss plus the box-pair penalty minus weighted absorption under the local certificate hypotheses. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpLeaf.lean#L63).

**Gradient slots of a mode profile** · theorem. `gradOf_bandProfile`: The gradient projection of a band profile is the corresponding label gradient. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpLeaf.lean#L86).

**Velocity slots of a mode profile** · theorem. `velOf_bandProfile`: The velocity projection of a band profile is the corresponding label velocity. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpLeaf.lean#L94).

**Off-mode point loss bound** · theorem. `offmode_point`: On the cell rectangle, radial-weighted point loss is bounded by label density after subtracting the off-mode allowance and extra charge density. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpLeaf.lean#L102).

**Basis velocity slots are real** · theorem. `Breakdown.CertCell.AssemblyPotentialSharpLeaf.star_velOf_single`: The velocity projection of a complex coordinate unit vector is fixed by conjugation. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpLeaf.lean#L161).

**Basis gradient slots are real** · theorem. `Breakdown.CertCell.AssemblyPotentialSharpLeaf.star_gradOf_single`: The gradient projection of a complex coordinate unit vector is fixed by conjugation. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpLeaf.lean#L166).

**True coupling as a triple matrix** · theorem. `trueCoupling_eq`: The true coupling matrix is the triple matrix formed from the given field's labelled gradient and Hessian. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpLeaf.lean#L171).

**Control point loss by profile norm** · theorem. `pointLoss_abs_le`: Uniform bounds on the loss coefficients and a positive splitting length control absolute point loss by the squared norm of the twelve-coordinate profile, with the explicit matrix constant displayed. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpLeaf.lean#L179).

### Breakdown.CertCell.AssemblyPotentialSharpLink

This file supplies the absorption-splitting interface and then closes the sharp-stage estimate. Appendix B.3: local stretching, potential forms and mode elimination, (B.25)–(B.37).

**Split absorption by orthogonality** · theorem. `absorbSplitStatement`: Under the stated hypotheses, the remainder absorption equals the absorption of its band polynomial part plus the absorption of its projection tail. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpLink.lean#L12).

**Sharp bound on the remainder profile** · theorem. `sharpStageHolds`: Under the stated hypotheses, the remainder's leaf and stretching forms plus its omitted-mode budget cover the box penalty after absorption costs. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpLink.lean#L16).

### Breakdown.CertCell.AssemblyPotentialSharpPoint

This file derives the pointwise lower bound for the sum of harmonic stretching interactions from the mean mode and the oscillatory symbol bounds. Appendix B.3: local stretching, potential forms and mode elimination, (B.25)–(B.37).

**Only the zero label is constant** · theorem. `labelHarmonic_zero_iff`: Under the azimuth-order hypothesis, a label has zero harmonic exactly when the label itself is zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpPoint.lean#L20).

**Remove a zero-index contribution** · theorem. `sum_drop_zero`: A finite sum whose zero-index term is suppressed equals the full sum minus that term when zero belongs to the index set. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpPoint.lean#L38).

**Bound a matrix quadratic loss** · theorem. `loss_bound`: The absolute real part of the matrix quadratic form is bounded by twice the sum of entry norms times the squared profile norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpPoint.lean#L48).

**Curl energy from profile energy** · theorem. `curl_le`: The squared curl norm is bounded by twice the entry-norm sum of the curl matrix times the squared profile norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpPoint.lean#L53).

**Gradient energy from profile energy** · theorem. `grad_le`: The squared gradient norm is bounded by twice the entry-norm sum of the gradient diagonal matrix times the squared profile norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpPoint.lean#L57).

**Velocity energy from profile energy** · theorem. `vel_le`: The squared velocity norm is bounded by twice the entry-norm sum of the velocity diagonal matrix times the squared profile norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpPoint.lean#L61).

**Coordinate energy is nonnegative** · theorem. `Breakdown.CertCell.AssemblyPotentialSharpPoint.cnormSq_nonneg'`: The sum of squared norms of a finite complex coordinate vector is nonnegative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpPoint.lean#L65).

**Mean second-derivative coefficient** · definition. `meanSecondDeriv`: This real array takes the real part of the zero second-derivative harmonic when that harmonic is in the chosen set, and returns zero otherwise. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpPoint.lean#L68).

**Nonzero second-derivative coefficient** · definition. `waveSecondDeriv`: This array keeps the selected second-derivative harmonic except at the zero label, where it is defined to be zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpPoint.lean#L72).

**Stretching coefficient by harmonic** · definition. `waveSymbol`: This matrix uses the full gradient harmonic together with the second-derivative harmonic whose mean mode has been removed. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpPoint.lean#L76).

**Pointwise symbol lower bound** · theorem. `symbol_point`: The wave symbol quadratic form is bounded below by the negative loss-matrix quadratic form with the specified strain, wave and length coefficients. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpPoint.lean#L80).

**Pointwise stretching loss** · definition. `pointLoss`: This quadratic loss combines the mean curl cost, the gradient-velocity product cost and the balanced oscillatory gradient cost. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpPoint.lean#L139).

**Dominate by squared profile norms** · theorem. `summable_of_cnorm`: Absolute domination by a summable squared-profile-norm sequence makes the scalar sequence summable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpPoint.lean#L144).

**Shifted pairings are summable** · theorem. `summable_shift_sesq`: Square-summability of a label-profile family makes its real pairing with any fixed shift through a fixed matrix summable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpPoint.lean#L148).

**Zero gradient and Hessian give zero** · theorem. `tripleMatrix_zero_zero`: The sharp triple matrix with zero gradient and zero Hessian arrays is the zero matrix. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpPoint.lean#L158).

**A zero matrix gives a zero pairing** · theorem. `sesq12_zero_matrix`: The sesquilinear pairing through the zero matrix is zero for every pair of vectors. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpPoint.lean#L165).

**Real curl-gradient mean** · theorem. `mean_real`: The zero harmonic of the vorticity gradient equals the complex coercion of the real curl-gradient of the averaged second derivative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpPoint.lean#L168).

**Sum the sharp mode bound** · theorem. `point_bound`: Under the symbol and summability hypotheses, the total shifted triple-matrix coupling is bounded below by the negative sum of point losses. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpPoint.lean#L182).

### Breakdown.CertCell.AssemblyPotentialSharpRegular

This file proves the summability and integrability needed to integrate the sharp pointwise estimate and interchange its harmonic sums. Appendix B.3: local stretching, potential forms and mode elimination, (B.25)–(B.37).

**Source namespace `Breakdown.CertCell.Assembly.Internal.SharpRegularity`.**

**Integrate a dominated series** · theorem. `tsum_facts`: Summable integral bounds give almost-everywhere summability, integrability of the series, and equality between its integral and the sum of termwise integrals. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpRegular.lean#L22).

**Curl energy is nonnegative** · theorem. `curlSq_nonneg`: The sum of squared norms of the matrix curl components is nonnegative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpRegular.lean#L50).

**Bound a weighted energy expression** · theorem. `quad_abs_le`: The absolute weighted sum of curl, gradient and velocity energies is bounded by (2 times the absolute curl coefficient plus the absolute gradient and velocity coefficients) times the squared profile norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpRegular.lean#L54).

**Continuous observations are measurable** · theorem. `aesm_of_continuous`: A continuous scalar function of a finite vector with almost-everywhere strongly measurable coordinates is almost-everywhere strongly measurable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpRegular.lean#L81).

**A dominated weight pays for the charge** · theorem. `weighted_quad_integrable`: Coordinate measurability, finite radial profile energy and an absolute weight bound by a constant times radius imply integrability of the weighted curl, gradient and velocity quadratic combination. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpRegular.lean#L86).

**Bound line weight by radius** · theorem. `lineWeight_abs_le`: For the permitted cell box, one constant bounds the absolute line weight by that constant times the radial coordinate throughout the rectangle. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpRegular.lean#L131).

**The line weight is measurable** · theorem. `measurable_lineWeight`: The cell line-weight function is measurable as a function of radius. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpRegular.lean#L143).

**Regularity of the leaf matrix** · theorem. `leaf_coupling`: The local leaf matrix satisfies the coupling regularity conditions on the cell rectangle for the singleton zero-shift set. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpRegular.lean#L149).

**Uniform integrable charge bound** · theorem. `charge_piece`: One constant controls every labelled charge term's integral of its norm by the radial-weighted squared profile integral, and every such term is integrable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpRegular.lean#L160).

**Source namespace `Breakdown.CertCell.Assembly.Internal.Sharp`.**

**Regularity of the sharp-stage sums** · theorem. `sharpRegular`: Under the stated hypotheses, the leaf, box, absorption, charge and stretching terms have the integrability and summability needed for the sharp-stage integration. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpRegular.lean#L210).

### Breakdown.CertCell.AssemblyPotentialSharpSymbol

This file represents stretching and its loss bounds by matrices and proves the symbol lower bound used to control all harmonic sequences. Appendix B.3: local stretching, potential forms and mode elimination, (B.25)–(B.37).

**Linear map into harmonic slots** · definition. `slotL`: This map packages the velocity and gradient coordinates linearly for the stretching form. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpSymbol.lean#L22).

**Conjugated harmonic slot vector** · definition. `slotC`: This map complex-conjugates the velocity and gradient slots obtained from the twelve-coordinate vector. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpSymbol.lean#L31).

**Expand conjugate slots in coordinates** · theorem. `slotC_sum`: The conjugate slot vector is the sum of conjugated profile coordinates times the corresponding linear slot unit vectors. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpSymbol.lean#L33).

**Expand linear slots in coordinates** · theorem. `slotL_sum`: The linear slot vector is the sum of profile coordinates times the corresponding slot unit vectors. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpSymbol.lean#L46).

**Symmetrized sharp interaction matrix** · definition. `tripleMatrix`: This matrix averages the two orders of the pair form on coordinate unit vectors, using the given gradient and Hessian arrays. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpSymbol.lean#L55).

**Expand the triple-matrix form** · theorem. `sesq12_tripleMatrix`: The triple-matrix sesquilinear form equals half the sum of the two pair-form evaluations with the corresponding conjugate and linear slots. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpSymbol.lean#L59).

**Add matrices in a sesquilinear form** · theorem. `sesq12_add`: The pairing with a sum of matrices equals the sum of the pairings with each matrix. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpSymbol.lean#L87).

**Scale the matrix in a pairing** · theorem. `sesq12_smul`: Scaling the matrix by a complex scalar scales its sesquilinear pairing by that scalar. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpSymbol.lean#L97).

**Expand a finite matrix symbol** · theorem. `sesq12_symbol`: The quadratic form of the finite weighted triple-matrix sum equals the symmetrized pair form of the weighted gradient and Hessian sums. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpSymbol.lean#L107).

**A row representing curl** · definition. `curlVecK`: This vector records the alternating-symbol coefficients of one curl component in the twelve coordinates. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpSymbol.lean#L120).

**Curl as a coordinate contraction** · theorem. `curlOfGrad_gradOf`: Each curl component of the gradient slots is the contraction of the full profile with the corresponding curl coefficient vector. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpSymbol.lean#L122).

**Rank-one Hermitian matrix** · definition. `rankOne`: This matrix is the outer product of a vector with its complex conjugate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpSymbol.lean#L149).

**Rank-one form is a square** · theorem. `re_sesq12_rankOne`: The real quadratic form of a rank-one matrix equals the squared norm of the corresponding coordinate contraction. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpSymbol.lean#L151).

**Matrix of the curl squared norm** · definition. `curlPairMatrix`: This matrix is the sum of the three rank-one matrices representing the three curl components. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpSymbol.lean#L161).

**Gradient-coordinate diagonal** · definition. `gradDiag`: This diagonal matrix selects the nine gradient coordinates. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpSymbol.lean#L163).

**Velocity-coordinate diagonal** · definition. `velDiag`: This diagonal matrix selects the three velocity coordinates. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpSymbol.lean#L165).

**Matrix formula for curl energy** · theorem. `re_sesq12_curlPairMatrix`: The real quadratic form of the curl-pair matrix equals the squared curl norm of the gradient slots. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpSymbol.lean#L167).

**Real diagonal quadratic form** · theorem. `re_sesq12_diagonal`: A real diagonal matrix has real quadratic form equal to the sum of each diagonal coefficient times the squared norm of its coordinate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpSymbol.lean#L178).

**Matrix formula for gradient energy** · theorem. `re_sesq12_gradDiag`: The real quadratic form of the gradient diagonal matrix equals the squared norm of the gradient slots. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpSymbol.lean#L190).

**Matrix formula for velocity energy** · theorem. `re_sesq12_velDiag`: The real quadratic form of the velocity diagonal matrix equals the squared norm of the velocity slots. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpSymbol.lean#L198).

**Matrix of the stretching loss** · definition. `lossMatrix`: This matrix combines the curl form and the gradient and velocity diagonals with the prescribed loss constants. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpSymbol.lean#L205).

**Matrix formula for loss energy** · theorem. `re_sesq12_lossMatrix`: The real loss-matrix quadratic form is the specified weighted sum of curl, gradient and velocity squared norms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpSymbol.lean#L208).

**Split a product with a length scale** · theorem. `sqrt_mul_le_split`: For nonnegative a and b and positive length, sqrt(a)sqrt(b) is bounded by half the sum of length times b and a divided by length. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpSymbol.lean#L216).

**Velocity slot energy** · theorem. `slot_vel_sq`: The velocity coordinates in the linear slot encoding have squared-norm sum equal to the velocity projection's squared norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpSymbol.lean#L228).

**Gradient slot energy** · theorem. `slot_grad_sq`: The gradient coordinates in the linear slot encoding have squared-norm sum equal to the gradient projection's squared norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpSymbol.lean#L230).

**Curl slot energy** · theorem. `slot_curl_sq`: Computing the curl from the linear gradient-slot encoding gives the same squared norm as computing it from the gradient projection. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpSymbol.lean#L236).

**Lower bound for a finite symbol** · theorem. `symbol_lower`: The finite triple-matrix symbol dominates the negative loss form when the real strain bound, wave error bound and positive splitting length hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpSymbol.lean#L239).

**Lower bound for mean coupling** · theorem. `mean_lower`: The mean-Hessian coupling is bounded below by minus sqrt(7/2) times its wave bound and the product of velocity and gradient norms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpSymbol.lean#L262).

**Two phase conventions agree** · theorem. `wavePhase_eq_phase`: The wave phase used for symbols agrees with the time-angle phase used in the torus formulas. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpSymbol.lean#L278).

**Continuity gives torus integrability** · theorem. `torusInt_of_cont`: A continuous function of time and angle is integrable on the compact time-angle box. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpSymbol.lean#L280).

**Mean of a finite Fourier sum** · theorem. `torusMean_trig`: The torus mean of a finite phase sum extracts its zero-frequency coefficient when that frequency is present and is zero otherwise. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpSymbol.lean#L284).

**Mean vorticity-gradient identity** · theorem. `mean_vort_identity`: The zero-frequency vorticity gradient is the alternating-tensor contraction of the zero-frequency second derivative, with the specified support convention. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpSymbol.lean#L294).

**Pass a lower bound to an infimum** · theorem. `le_iInf_mul`: If b is nonnegative and every product f(i) times b is at least a, then the infimum of f multiplied by b is at least a. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpSymbol.lean#L332).

**A unit bound gives a lower bound** · theorem. `bdd_of_unit`: The supplied unit-vector quadratic estimate gives a lower bound for the range of the scalar function. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpSymbol.lean#L342).

**Curl gradient has zero trace** · theorem. `curlGradReal_trace`: Symmetry of the underlying second derivatives makes the trace of their real curl-gradient matrix zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpSymbol.lean#L348).

**Subtract real curl gradients** · theorem. `curlGradReal_sub`: Taking the real curl-gradient commutes with subtracting the underlying third-order arrays. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpSymbol.lean#L357).

**Zero-frequency second derivative** · theorem. `modeSecondDeriv_zero_real`: The zero Fourier coefficient of a real second derivative is equal to the complex coercion of its real part. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpSymbol.lean#L361).

**Symmetry of Fourier Hessian slots** · theorem. `modeSecondDeriv_symm`: The Fourier second derivative is unchanged when its two derivative indices are interchanged under the derivative-symmetry hypotheses. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpSymbol.lean#L375).

**Symmetry in the rotating frame** · theorem. `frameSecondDeriv_symm`: The second derivative expressed in the rotating frame is symmetric in its two derivative indices under the underlying Hessian symmetry assumption. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpSymbol.lean#L381).

**Split the Hessian contribution** · theorem. `tripleMatrix_split`: Adding two Hessian arrays splits the triple matrix into its original gradient-Hessian matrix and a second matrix with zero gradient contribution. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpSymbol.lean#L387).

### Breakdown.CertCell.AssemblyPotentialSharpSymbolForm

This file passes from a pointwise matrix-symbol lower bound to a lower bound for finitely supported coefficient forms, using an exact finite Fourier grid. Appendix B.3: local stretching, potential forms and mode elimination, (B.25)–(B.37).

**Phase of a label on the torus** · definition. `wavePhase`: This is the unit complex phase attached to a harmonic label at the chosen time and angle. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpSymbolForm.lean#L18).

**Matrix symbol at a torus point** · definition. `symbolAt`: This matrix sums coefficient matrices multiplied by their harmonic phases. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpSymbolForm.lean#L21).

**Coefficient synthesis at a point** · definition. `synthAt`: This vector sums the finitely supported coefficient vectors multiplied by their harmonic phases. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpSymbolForm.lean#L25).

**Adding frequencies multiplies phases** · theorem. `wavePhase_add`: The wave phase at the sum of two frequencies equals the product of their phases. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpSymbolForm.lean#L28).

**Conjugation reverses the wave frequency** · theorem. `conj_wavePhase`: The complex conjugate of a wave phase is the phase at the negative frequency. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpSymbolForm.lean#L37).

**Constant phase at zero frequency** · theorem. `wavePhase_zero`: The wave phase of the zero frequency is identically one. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpSymbolForm.lean#L45).

**Root of unity for a finite grid** · definition. `gridRoot`: This root of unity supplies the exact discrete Fourier phases on the finite grid. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpSymbolForm.lean#L49).

**Phase values on a uniform grid** · theorem. `wavePhase_grid`: Sampling a wave phase at the uniform time-angle grid gives the product of the corresponding powers of the two grid roots. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpSymbolForm.lean#L51).

**A finite root sum detects divisibility** · theorem. `gridRoot_sum`: For a positive grid size n, the sum of the first n powers of the grid root is n when n divides the frequency and zero otherwise. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpSymbolForm.lean#L59).

**A grid sum detects zero frequency** · theorem. `grid_phase_sum`: When both frequency coordinates have magnitude below the positive grid size, the two-dimensional phase sum is the grid size squared at zero frequency and zero otherwise. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpSymbolForm.lean#L99).

**Reorder a triple finite sum** · theorem. `pull3`: A finite triple sum can move its final summation to the outside without changing its value. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpSymbolForm.lean#L117).

**Matrix-vector form of the pairing** · theorem. `sesq12_eq`: The twelve-coordinate sesquilinear form is the dot product of the conjugate first vector with the matrix applied to the second vector. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpSymbolForm.lean#L123).

**Expand a finite matrix combination** · theorem. `sesq12_smul_sum`: The sesquilinear form of a finite scalar-weighted matrix sum equals the corresponding weighted sum of matrix pairings. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpSymbolForm.lean#L130).

**Expand two finite vector combinations** · theorem. `sesq12_vec_sum`: The pairing of two finite vector combinations equals the double sum of basis pairings weighted by the conjugated first coefficients and the second coefficients. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpSymbolForm.lean#L137).

**Harmonics preserve label differences** · theorem. `Breakdown.CertCell.AssemblyPotentialSharpSymbolForm.labelHarmonic_sub`: The harmonic assigned to a label difference equals the difference of the assigned harmonics. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpSymbolForm.lean#L149).

**Expand a synthesized symbol form** · theorem. `sesq_synth`: The symbol quadratic form on a finite Fourier synthesis expands into the triple sum over symbol frequencies and two label indices, with their combined phase. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpSymbolForm.lean#L154).

**Grid size for harmonic separation** · definition. `gridBound`: This natural bound makes the grid large enough to distinguish the finite frequency differences in the form. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpSymbolForm.lean#L169).

**The sampling grid is nonempty** · theorem. `gridBound_pos`: The chosen grid bound is at least one. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpSymbolForm.lean#L172).

**Integer formula for the grid size** · theorem. `gridBound_cast`: The grid bound coerced to integers equals one plus the symbol-frequency size sum and twice the labelled-frequency size sum. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpSymbolForm.lean#L175).

**Frequency differences fit the grid** · theorem. `gridBound_lt`: For frequencies in the specified finite supports, both coordinates of every combined phase frequency have magnitude strictly below the grid bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpSymbolForm.lean#L182).

**Discrete Fourier cancellation** · theorem. `grid_total`: Summing the symbol form over the uniform grid leaves only zero combined frequencies and multiplies their total by the square of the grid size. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpSymbolForm.lean#L210).

**Reindex resonances by label shifts** · theorem. `reindex_sum`: The supplied harmonic-support correspondence converts the zero-combined-frequency triple sum into the sum over labels and shifts whose partner stays in the finite support. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpSymbolForm.lean#L247).

**Bound a mixed matrix pairing** · theorem. `re_sesq_le`: The absolute real part of a mixed matrix pairing is bounded by the entry-norm sum times the sum of the two squared profile norms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpSymbolForm.lean#L283).

**Real part of a conditional term** · theorem. `re_ite`: Taking the real part of a complex value selected by a proposition commutes with the conditional whose other branch is zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpSymbolForm.lean#L306).

**Finite-support symbol inequality** · theorem. `symbolForm_finite`: The pointwise symbol lower bound implies a finite-label coupling lower bound, retaining only shifts that remain in the chosen support. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpSymbolForm.lean#L309).

**Infinite-label symbol inequality** · theorem. `symbolForm_lower`: The pointwise symbol lower bound and square-summability assumptions imply the corresponding inequality for the full shifted-label coupling series. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialSharpSymbolForm.lean#L370).

### Breakdown.CertCell.AssemblyPotentialStage

This file cancels the intermediate budgets and combines the potential substage inequalities into the final cell potential estimate. Appendix B.3: local stretching, potential forms and mode elimination, (B.25)–(B.37).

**Source namespace `Breakdown.CertCell.Assembly.Internal`.**

**Read the packed matrix** · theorem. `strainOfVec_pairVec`: The matrix projection of a packed gradient-velocity vector returns the original matrix. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStage.lean#L18).

**Read the packed velocity** · theorem. `Breakdown.CertCell.AssemblyPotentialStage.velOf_pairVec`: The velocity projection of a packed gradient-velocity vector returns the original velocity entries. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStage.lean#L22).

**Read the packed gradient** · theorem. `Breakdown.CertCell.AssemblyPotentialStage.gradOf_pairVec`: The gradient projection of a packed gradient-velocity vector returns the original gradient entries. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStage.lean#L26).

**Cell rectangles are measurable** · theorem. `Breakdown.CertCell.AssemblyPotentialStage.rect_measurable`: The closed radial-height rectangle associated with a cell box is Lebesgue measurable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStage.lean#L31).

**Radius is nonnegative in a cell** · theorem. `fst_nonneg_of_mem`: A point in the cell rectangle has a nonnegative first coordinate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStage.lean#L34).

**Projection-tail energy is nonnegative** · theorem. `tailNormSq_nonneg`: The squared projection-tail norm on a valid cell is nonnegative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStage.lean#L38).

**Restricted and global low profiles** · theorem. `lowAt_coe`: Evaluating the globally indexed low profile at a resolved label agrees with the profile indexed by that label's subtype. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStage.lean#L48).

**Rewrite the integrated leaf term** · theorem. `leaf_term_eq`: The finite sum of radial-weighted local leaf quadratic integrals equals the leaf pairing of the low profile with itself. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStage.lean#L53).

**Rewrite the integrated absorption** · theorem. `absorb_term_eq`: The resolved-label sum of line-weighted absorption integrals equals the absorption amount of the low profile. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStage.lean#L63).

**Rewrite an unlabelled charge** · theorem. `charge_term_eq`: The sum of radial-weighted low-profile charge integrals equals the corresponding form amount on the resolved labels. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStage.lean#L72).

**Rewrite a labelled charge** · theorem. `long_term_eq`: The sum of radial-weighted label-dependent low-profile charge integrals equals the corresponding labelled form amount. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStage.lean#L82).

**Rewrite the grouped own charge** · theorem. `group_term_eq`: The group-balance-weighted low-profile charge sum equals the group own amount of the upper profiles. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStage.lean#L92).

**Expose the exact potential balance** · theorem. `potentialExact_eq`: The exact potential equals the upper self-coupling plus twice the upper-band coupling, less the band leaf and absorption terms and the port, group, epsilon and long own charges. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStage.lean#L106).

**Gradient-tail energy is nonnegative** · theorem. `tailStrainSq_nonneg`: A valid cell mesh gives nonnegative gradient projection-tail energy for every label. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStage.lean#L126).

**Velocity-tail energy is nonnegative** · theorem. `tailVelSq_nonneg`: A valid cell mesh gives nonnegative velocity projection-tail energy for every label. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStage.lean#L130).

**Curl-tail energy is nonnegative** · theorem. `tailCurlSq_nonneg`: A valid cell mesh gives nonnegative curl projection-tail energy for every label. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStage.lean#L134).

**Cover potential tail costs** · theorem. `tail_costs_le`: The block's allocated potential costs dominate the sum of absorption, balance and high-frequency tail charges under the allocation and nonnegativity hypotheses. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStage.lean#L138).

**Source namespace `Breakdown.CertCell.Assembly`.**

**The cell potential-stage estimate** · theorem. `potentialStage_of_stages`: Under the stated hypotheses, the retained potential form and its band, leakage, credit and slack costs are covered by resolved density, omitted charge and stretching after energy credits. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStage.lean#L167).

**Assemble the potential-stage bound** · theorem. `potentialAssembly_holds`: Under the stated hypotheses, the full list of stretching, leaf, sharp, model, tail, group, charge and splitting stages implies the potential-stage inequality. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStage.lean#L190).

### Breakdown.CertCell.AssemblyPotentialStageCharge

This file isolates the additional omitted-mode charges and proves that their integral splits off from the full omitted-mode budget. Appendix B.3: local stretching, potential forms and mode elimination, (B.25)–(B.37).

**Squared norm of a difference** · theorem. `Breakdown.CertCell.AssemblyPotentialStageCharge.norm_sub_sq_le`: The squared norm of a difference is at most twice the sum of the two squared norms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageCharge.lean#L18).

**Three curl components** · theorem. `curlOfGrad_apply`: The pair-indexed curl array has the three usual antisymmetric differences of gradient entries. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageCharge.lean#L22).

**Three matrix curl components** · theorem. `curlComp_apply`: The matrix curl has the three usual antisymmetric differences of matrix entries. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageCharge.lean#L27).

**Curl energy is at most twice gradient** · theorem. `cnormSq_curlOfGrad_le`: The squared norm of the curl array is at most twice the squared norm of the gradient array. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageCharge.lean#L31).

**Matrix curl energy bound** · theorem. `Breakdown.CertCell.AssemblyPotentialStageCharge.curlSq_le_two`: The curl energy of a matrix is at most twice the sum of the squared norms of all its entries. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageCharge.lean#L41).

**Energy of a packed profile** · theorem. `pairVec_sq`: The squared-coordinate sum of a packed matrix and velocity vector equals their matrix energy plus their velocity energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageCharge.lean#L51).

**Bound a reciprocal coefficient** · theorem. `inv_abs_le`: When x lies in the stated positive interval controlled by c and its reciprocal, the absolute value of its reciprocal is at most abs(c) plus abs(1/c). [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageCharge.lean#L58).

**Bound an interval coefficient** · theorem. `abs_le_of_between`: The stated interval constraints bound the absolute coefficient by abs(c) plus abs(1/c). [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageCharge.lean#L77).

**Multiply coefficient and energy bounds** · theorem. `abs_mul_term`: The absolute product a times y is bounded by A times L times S from the coefficient bound and the nonnegative energy bound in the premises. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageCharge.lean#L83).

**Squared norm of a harmonic profile** · definition. `profileSq`: This value is the sum of the squared norms of all twelve harmonic profile coordinates. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageCharge.lean#L93).

**Profile energy splits into two parts** · theorem. `profileSq_eq`: The squared band-profile norm equals the sum of gradient-matrix energy and velocity-vector energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageCharge.lean#L96).

**Matrix energy is nonnegative** · theorem. `sumSq_nonneg`: The sum of squared norms of all complex matrix entries is nonnegative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageCharge.lean#L100).

**Velocity energy is nonnegative** · theorem. `vecSq_nonneg`: The sum of squared norms of a complex velocity vector's coordinates is nonnegative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageCharge.lean#L104).

**Squared complex norm is nonnegative** · theorem. `Breakdown.CertCell.AssemblyPotentialStageCharge.cnormSq_nonneg'`: The sum of squared norms of a finite complex coordinate vector is nonnegative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageCharge.lean#L108).

**Two gradient energy encodings** · theorem. `cnormSq_labelGrad`: The squared norm of the label gradient equals the matrix squared-norm sum of the gradient array. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageCharge.lean#L112).

**Two velocity energy encodings** · theorem. `cnormSq_labelVel`: The squared norm of the label velocity equals the vector squared-norm sum of the velocity array. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageCharge.lean#L118).

**Gradient entries in a band profile** · theorem. `gradAt_eq_profile`: Each labelled gradient entry is the matching gradient coordinate of the band profile. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageCharge.lean#L121).

**Velocity entries in a band profile** · theorem. `velAt_eq_profile`: Each labelled velocity entry is the matching velocity coordinate of the band profile. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageCharge.lean#L128).

**Expanded off-mode charge difference** · definition. `chargeDiff`: This expression expands the stretching and entry-charge terms in the difference of the original and charged off-mode densities. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageCharge.lean#L135).

**Identify the remaining charge** · theorem. `chargeDiff_eq`: Subtracting the off-mode density and extra charge from the label density gives the explicit charge-difference expression. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageCharge.lean#L149).

**Curl contribution to the density** · definition. `curlPart`: This term isolates the curl squared-norm part of the mode charge. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageCharge.lean#L166).

**Gradient contribution to the density** · definition. `gradPart`: This term isolates the gradient squared-norm part of the mode charge. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageCharge.lean#L168).

**Velocity contribution to the density** · definition. `velPart`: This term isolates the velocity squared-norm part of the mode charge. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageCharge.lean#L170).

**Gradient-velocity charge product** · definition. `crossPart`: This term isolates the product of gradient and velocity norms in the mode charge. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageCharge.lean#L172).

**Curl contribution is continuous** · theorem. `continuous_curlPart`: The encoded curl contribution to the density is continuous in the full profile vector. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageCharge.lean#L174).

**Gradient contribution is continuous** · theorem. `continuous_gradPart`: The encoded gradient contribution to the density is continuous in the full profile vector. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageCharge.lean#L178).

**Velocity contribution is continuous** · theorem. `continuous_velPart`: The encoded velocity contribution to the density is continuous in the full profile vector. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageCharge.lean#L182).

**Mixed contribution is continuous** · theorem. `continuous_crossPart`: The mixed velocity-gradient norm contribution is continuous in the full profile vector. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageCharge.lean#L186).

**Packed curl energy is continuous** · theorem. `continuous_curlSqPart`: The curl squared norm of the profile's matrix block depends continuously on the profile. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageCharge.lean#L190).

**Packed gradient energy is continuous** · theorem. `continuous_sumSqPart`: The matrix-entry squared-norm sum of the profile's gradient block depends continuously on the profile. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageCharge.lean#L194).

**Packed velocity energy is continuous** · theorem. `continuous_vecSqPart`: The squared-coordinate norm of the profile's velocity block depends continuously on the profile. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageCharge.lean#L198).

**Read the labelled gradient** · theorem. `labelGrad_eq_profile`: The label gradient is the gradient projection of the corresponding band profile. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageCharge.lean#L202).

**Read the labelled velocity** · theorem. `labelVel_eq_profile`: The label velocity is the velocity projection of the corresponding band profile. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageCharge.lean#L208).

**Read the gradient matrix** · theorem. `gradArray_eq_profile`: The gradient array is the matrix projection of the corresponding band profile. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageCharge.lean#L214).

**Read the velocity array** · theorem. `velArray_eq_profile`: The velocity array is the velocity projection of the corresponding band profile. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageCharge.lean#L219).

**Expand the charge difference** · theorem. `chargeDiff_profile`: The charge difference is the displayed combination of profile curl, gradient, velocity and mixed energies, including the corrections between their two encodings. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageCharge.lean#L224).

**Expand the extra profile charge** · theorem. `extraCharge_profile`: The extra charge density is the entry curl, gradient and velocity charge coefficients multiplied by the corresponding profile energies. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageCharge.lean#L251).

**Measurable continuous profile functions** · theorem. `profile_aemeasurable`: A continuous real function of a band profile is almost-everywhere measurable whenever each profile coordinate is almost-everywhere strongly measurable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageCharge.lean#L261).

**Measurable weighted charge difference** · theorem. `chargeDiff_aemeasurable`: Entry-charge regularity and measurable profile coordinates imply almost-everywhere strong measurability of radius times the charge difference on the cell. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageCharge.lean#L266).

**The weighted extra charge is measurable** · theorem. `extraCharge_aemeasurable`: Entry-charge regularity and measurable profile coordinates imply almost-everywhere strong measurability of radius times the extra charge density on the cell. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageCharge.lean#L291).

**All profile energies fit the full norm** · theorem. `part_bounds`: The curl, gradient, velocity and mixed profile energies and their packed versions are nonnegative and bounded by the full profile squared norm, with factor two for curl terms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageCharge.lean#L312).

**Bound a product of three factors** · theorem. `coef_bound3`: When each factor is bounded by the common admissible bound B, the absolute half-product of the three factors is at most B cubed. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageCharge.lean#L361).

**Bound a product of two factors** · theorem. `coef_bound2`: The stated factor bounds and lower bound on B make the absolute two-factor product at most B cubed. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageCharge.lean#L369).

**Bound one factor by a cube** · theorem. `coef_bound1`: The stated coefficient bound and lower bound on B make its absolute value at most B cubed. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageCharge.lean#L374).

**Uniform charge-density domination** · theorem. `chargeDiff_bound`: Both the absolute charge difference and the absolute extra charge density are bounded by 14 times (abs(c)+abs(1/c)+1) cubed times the squared profile norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageCharge.lean#L382).

**Integrate a weighted domination** · theorem. `dominated_on`: Measurability and domination by M times the integrable radial-weighted energy give integrability and the same bound for the norm of the integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageCharge.lean#L438).

**Split the off-mode charge** · theorem. `offCharge_split`: The off-mode charge amount equals the stretch charge amount plus the charge surplus. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageCharge.lean#L451).

### Breakdown.CertCell.AssemblyPotentialStageLeaf

This file expands the leaf form around the retained upper profile, identifies its cross terms, and collects the identities needed for potential-stage cancellation. Appendix B.3: local stretching, potential forms and mode elimination, (B.25)–(B.37).

**Source namespace `Breakdown.CertCell.Assembly.Internal`.**

**Packing preserves paired addition** · theorem. `pairVec_add`: Packing the sum of two matrices and the sum of two velocities gives the sum of their packed profiles. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageLeaf.lean#L18).

**Add in the first sesquilinear slot** · theorem. `sesq12_add_left`: The sesquilinear matrix pairing is additive in its first vector argument. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageLeaf.lean#L24).

**Add in the second sesquilinear slot** · theorem. `sesq12_add_right`: The sesquilinear matrix pairing is additive in its second vector argument. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageLeaf.lean#L29).

**Swap a Hermitian pairing** · theorem. `sesq12_swap`: For a self-adjoint matrix, exchanging the two vectors conjugates its sesquilinear pairing. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageLeaf.lean#L34).

**Real Hermitian pairing is symmetric** · theorem. `sesq12_re_swap`: For a self-adjoint matrix, exchanging the two vectors preserves the real part of its sesquilinear pairing. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageLeaf.lean#L45).

**Expand the leaf quadratic change** · theorem. `leaf_point`: For a Hermitian leaf matrix, adding the tail to upper plus band changes its real quadratic by twice the upper-tail pairing plus the band-and-tail quadratic minus the band quadratic. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageLeaf.lean#L49).

**Retained profiles add with the state** · theorem. `Breakdown.CertCell.AssemblyPotentialStageLeaf.lowProfile_add`: The retained polynomial profile of a sum of cell states equals the sum of their retained profiles. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageLeaf.lean#L58).

**Zero-extended low profiles add** · theorem. `Breakdown.CertCell.AssemblyPotentialStageLeaf.lowAt_add`: The zero-extended low profile of a sum of states equals the sum of their zero-extended low profiles at every label. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageLeaf.lean#L68).

**Split retained data into upper and band** · theorem. `Breakdown.CertCell.AssemblyPotentialStageLeaf.lowAt_split`: The low profile equals the sum of the low profiles of the upper and band coordinate parts. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageLeaf.lean#L75).

**Retained profiles are continuous** · theorem. `continuous_lowProfile`: For fixed state and resolved label, the retained polynomial profile is continuous in the plane point. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageLeaf.lean#L83).

**Extended low profiles are continuous** · theorem. `continuous_lowAt`: For fixed state and label, the zero-extended low profile is continuous in the plane point. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageLeaf.lean#L93).

**Weighted square-integrable profile** · proposition definition. `ProfileReg`: This predicate combines coordinate measurability with integrability of the radius-weighted squared profile norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageLeaf.lean#L104).

**Continuous profiles are regular** · theorem. `profileReg_of_continuous`: Continuity on the specified compact region supplies the profile measurability and square-integrability requirements. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageLeaf.lean#L108).

**Subtract regular profiles** · theorem. `profileReg_sub`: The difference of two regular profiles satisfies the same profile regularity conditions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageLeaf.lean#L116).

**Bound a twelve-coordinate pairing** · theorem. `sesq12_norm_le`: An entrywise matrix bound controls the pairing norm by 144 times that bound's absolute value times the sum of the two squared vector norms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageLeaf.lean#L134).

**Two regular profiles can be paired** · theorem. `sesq_integrable`: On a nonnegative-radius region, a measurable uniformly bounded matrix paired with two regular profiles has integrable real radial-weighted sesquilinear form. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageLeaf.lean#L157).

**Split the true-minus-low leaf form** · theorem. `leaf_split`: The true leaf energy minus the full low energy expands into twice the upper-tail pairing plus the other-profile energy minus the band energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageLeaf.lean#L186).

**Source namespace `Breakdown.CertCell.Assembly`.**

**Tail absorption equals stored norms** · interface proposition. `TailAbsorbIdentityHolds`: This interface requires that the resolved tail absorption is the sum of the leaf curl, gradient and velocity constants times their stored squared tail norms whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageLeaf.lean#L255).

Proved by `Breakdown.CertCell.Assembly.tailAbsorbIdentity_holds`.

**Identities for budget cancellation** · theorem. `splitIdentities_of_tail`: Under the stated hypotheses, the omitted budget, leaf difference and tail absorption admit the three exact decompositions used when the stage inequalities are added. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageLeaf.lean#L265).

### Breakdown.CertCell.AssemblyPotentialStageTail

This file identifies the integrated tail absorption with the three stored tail norms, using the actual polynomial projection for each coordinate. Appendix B.3: local stretching, potential forms and mode elimination, (B.25)–(B.37).

**Source namespace `Breakdown.CertCell.Assembly.Internal`.**

**Nonnegative line-weight comparison** · theorem. `lineWeight_bound`: On the valid cell rectangle, the line weight is nonnegative and is bounded by one nonnegative constant times radius. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageTail.lean#L19).

**The line weight is continuous** · theorem. `continuous_lineWeight'`: The cell line-weight function is continuous in its radial argument. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageTail.lean#L35).

**Weighted square-integrable scalar** · proposition definition. `ScalarReg`: This predicate requires scalar measurability and integrability of its squared norm weighted by radius. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageTail.lean#L41).

**The cell rectangle is compact** · theorem. `Breakdown.CertCell.AssemblyPotentialStageTail.rect_compact`: The cell's closed and bounded radial-height rectangle is compact. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageTail.lean#L44).

**Regularity gives line-weighted energy** · theorem. `scalarReg_lw_sq`: The scalar regularity predicate implies integrability of the line-weighted squared norm on the valid cell rectangle. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageTail.lean#L46).

**Regularity gives a weighted integral** · theorem. `scalarReg_lw_mul`: The scalar regularity predicate implies integrability of the line-weighted complex profile on the valid cell rectangle. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageTail.lean#L57).

**Subtract regular scalar profiles** · theorem. `scalarReg_sub`: The difference of two scalar profiles satisfying the cell regularity conditions again satisfies those conditions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageTail.lean#L73).

**Continuous scalar profiles are regular** · theorem. `scalarReg_of_continuous`: A continuous scalar profile on the cell rectangle satisfies the required scalar measurability and weighted square-integrability conditions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageTail.lean#L86).

**Expand the tensor projection** · theorem. `proj_expand'`: The rectangular polynomial projection equals the finite sum of its coefficients times the tensor basis functions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageTail.lean#L91).

**Cell projections are continuous** · theorem. `Breakdown.CertCell.AssemblyPotentialStageTail.proj_continuous`: The cell's finite polynomial projection is a continuous function of the plane point. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageTail.lean#L97).

**Subtract regular cell coefficients** · theorem. `coef_sub`: For regular scalar profiles, the coefficient of their difference equals the difference of their coefficients. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageTail.lean#L107).

**Subtract regular cell projections** · theorem. `proj_sub`: For regular scalar profiles and a valid basis, projecting their difference equals the difference of their projections. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageTail.lean#L121).

**Projection errors have finite energy** · theorem. `tail_sq_integrable`: A regular scalar profile and valid cell basis give integrability of the line-weighted squared projection error at every degree. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageTail.lean#L133).

**Coordinates inherit profile regularity** · theorem. `scalarReg_component`: Every coordinate of a regular vector profile satisfies the corresponding scalar regularity conditions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageTail.lean#L142).

**Tail absorption in energy coordinates** · theorem. `tail_absorb_mode`: The line-weighted tail absorption integral is the curl absorption coefficient times tail curl energy plus the analogous gradient and velocity terms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageTail.lean#L156).

**Source namespace `Breakdown.CertCell.Assembly`.**

**Tail absorption equals stored norms** · theorem. `tailAbsorbIdentity_holds`: Under the stated hypotheses, the resolved tail absorption is the sum of the leaf curl, gradient and velocity constants times their stored squared tail norms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageTail.lean#L263).

**Identities for budget cancellation** · theorem. `splitIdentities_holds`: Under the stated hypotheses, the omitted budget, leaf difference and tail absorption admit the three exact decompositions used when the stage inequalities are added. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialStageTail.lean#L270).

### Breakdown.CertCell.AssemblyPotentialTails

This file bounds the interaction between retained profiles and unresolved polynomial tails and then bounds the high-degree partner cost of those tails. Appendix B.3: local stretching, potential forms and mode elimination, (B.25)–(B.37).

**Source namespace `Breakdown.CertCell.Assembly.Internal.PotentialTails`.**

**Pay for the model-tail interaction** · theorem. `tail_cross_main`: The model and leaf upper-tail cross terms are bounded below by minus the port quadratic form and the allocated gradient and velocity tail balances. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialTails.lean#L16).

**Compare radius with line weight** · theorem. `rHatMax_bound`: On the cell rectangle, radius is at most the maximum radius-ratio constant times the line weight. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialTails.lean#L114).

**Gradient part of a tail profile** · theorem. `strainOfVec_tail`: The tail profile's gradient matrix is the labelled gradient minus its degree-prescribed cell projection, entry by entry. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialTails.lean#L126).

**Velocity part of a tail profile** · theorem. `velOf_tail`: The tail profile's velocity is the labelled velocity minus its cell projection at one degree below the gradient degree. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialTails.lean#L135).

**Pay for the high partner** · theorem. `tail_high_main`: The high-partner amount on tail profiles is bounded by the explicit radius-ratio and Young-parameter combination of gradient and velocity tail energies. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialTails.lean#L144).

**Source namespace `Breakdown.CertCell.Assembly`.**

**Charge the retained-tail interaction** · theorem. `tailCrossStage_holds`: Under the stated hypotheses, the retained-tail cross interaction is bounded below by minus the port form and the balanced gradient and velocity tail costs. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialTails.lean#L283).

**Bound high-degree costs on the tail** · theorem. `tailHighStage_holds`: Under the stated hypotheses, the high-degree partner cost of the resolved tail is controlled by explicit gradient and velocity tail norms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialTails.lean#L287).

### Breakdown.CertCell.AssemblyPotentialTailsCross

This file proves the weighted projection-tail inequality underlying the potential cross estimate, including all cell-weight and integrability conditions. Appendix B.3: local stretching, potential forms and mode elimination, (B.25)–(B.37).

**Rectangular polynomials are continuous** · theorem. `polyFn_continuous`: Every function in the prescribed rectangular polynomial space is continuous. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialTailsCross.lean#L11).

**Projection lies in the polynomial space** · theorem. `proj_mem_polyFn`: The cell projection belongs to the rectangular polynomial space with the requested degrees. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialTailsCross.lean#L18).

**Cell projections are continuous** · theorem. `Breakdown.CertCell.AssemblyPotentialTailsCross.proj_continuous`: The cell's finite polynomial projection is a continuous function of the plane point. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialTailsCross.lean#L24).

**The cell rectangle is measurable** · theorem. `Breakdown.CertCell.AssemblyPotentialTailsCross.rect_measurableSet`: The closed radial-height rectangle associated with a cell box is Lebesgue measurable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialTailsCross.lean#L27).

**The cell rectangle is compact** · theorem. `Breakdown.CertCell.AssemblyPotentialTailsCross.rect_isCompact`: The cell's closed and bounded radial-height rectangle is compact. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialTailsCross.lean#L30).

**The line weight is continuous** · theorem. `lineWeight_continuous`: The cell line-weight function is continuous in its radial argument. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialTailsCross.lean#L33).

**The cell line weight is nonnegative** · theorem. `lineWeight_nonneg`: The line weight is nonnegative at every point in the valid cell rectangle. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialTailsCross.lean#L39).

**Recover radius from the weight ratio** · theorem. `lineWeight_mul_rHat`: On the cell rectangle, multiplying the line weight by the radius-ratio function gives the radial coordinate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialTailsCross.lean#L46).

**The radius-ratio function is measurable** · theorem. `rHat_measurable`: The function giving radius divided by the cell line weight is measurable on the plane. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialTailsCross.lean#L58).

**Bound the radius-ratio function** · theorem. `rHat_bound`: On the cell rectangle, the absolute radius-ratio function is at most the maximum of the outer radius and one. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialTailsCross.lean#L62).

**The cell rectangle has finite volume** · theorem. `volume_rect_ne_top`: The Lebesgue measure of the cell rectangle is not infinite. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialTailsCross.lean#L73).

**The cell rectangle has finite measure** · theorem. `Breakdown.CertCell.AssemblyPotentialTailsCross.rect_finite`: The cell rectangle has finite Lebesgue measure. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialTailsCross.lean#L76).

**Weighted two-factor estimate** · theorem. `Breakdown.CertCell.AssemblyPotentialTailsCross.two_mul_le_weighted`: For positive beta, twice a times b is at most beta times a squared plus b squared divided by beta. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialTailsCross.lean#L81).

**Bound a real complex product** · theorem. `re_conj_mul_le`: The absolute real part of conjugate(z) times w is at most the product of their norms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialTailsCross.lean#L88).

**Bound the tail cross integral below** · theorem. `tail_cross_lower`: Orthogonality of the projection error and the stated integrability and boundedness give an integrable cross term whose doubled integral is bounded below by minus the weighted sum of the two projection-tail energies. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialTailsCross.lean#L92).

**Tail regularity follows from full energy** · theorem. `tail_regular`: A measurable scalar profile with finite line-weighted energy has a measurable projection error with finite line-weighted squared norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialTailsCross.lean#L240).

**Radius is controlled by line weight** · theorem. `fst_le_lineWeight`: On a valid cell rectangle, radius is nonnegative and is at most max(outer radius,1) times the line weight. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialTailsCross.lean#L271).

**A finite-energy tail pairs with a bound** · theorem. `cross_integrable`: A measurable line-square-integrable tail and a measurable bounded coefficient have integrable real radial-weighted cross product on the cell. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialTailsCross.lean#L280).

**Integrate a finite cross-term sum** · theorem. `cross_sum`: A finite sum of bounded measurable coefficients can be moved outside the radial cross integral against a measurable finite-energy tail. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialTailsCross.lean#L314).

**Separate gradient and velocity slots** · theorem. `sum_fin12`: A sum over twelve coordinates splits into the nine matrix-entry coordinates and the three velocity coordinates. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialTailsCross.lean#L330).

### Breakdown.CertCell.AssemblyPotentialTailsModes

This file expands the model and leaf interactions against each tail coordinate, preparing the weighted tail estimate for summation over resolved harmonics. Appendix B.3: local stretching, potential forms and mode elimination, (B.25)–(B.37).

**Conjugate every model interaction input** · theorem. `Breakdown.CertCell.AssemblyPotentialTailsModes.conj_modelTriple`: Conjugating the stretching model interaction equals applying it to the entrywise conjugates of its coefficient arrays and both field pairs. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialTailsModes.lean#L15).

**Exchange the two profiles in stretching** · theorem. `Breakdown.CertCell.AssemblyPotentialTailsModes.modelTriple_swap`: The symmetrized model interaction is unchanged when its two velocity-gradient arguments are exchanged. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialTailsModes.lean#L24).

**Double conjugation restores a function** · theorem. `conj_star_fn`: Conjugating the pointwise star of a complex-valued function returns the original function. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialTailsModes.lean#L29).

**Conjugation agrees with function star** · theorem. `conj_fn_eq_star`: Applying complex conjugation coordinatewise equals the star operation on complex-valued functions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialTailsModes.lean#L33).

**Polynomial values on a cell rectangle** · theorem. `planeValue_rect`: Within the specified cell rectangle, the field's plane value equals the evaluation of its component polynomial. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialTailsModes.lean#L37).

**Cell heights are nonnegative** · theorem. `rect_snd_nonneg`: The potential conditions imply nonnegative height for every point of the cell rectangle. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialTailsModes.lean#L46).

**Opposite shifts give paired symmetry** · theorem. `model_sym`: The real model pairing at a shift equals the real pairing at the opposite shift with its two profile arguments exchanged. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialTailsModes.lean#L50).

**Symmetry from self-adjointness** · theorem. `selfAdjoint_sesq_re_symm`: The real sesquilinear pairing of a self-adjoint matrix is symmetric in its two vector arguments. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialTailsModes.lean#L69).

**Cell polynomial evaluation is continuous** · theorem. `Breakdown.CertCell.AssemblyPotentialTailsModes.cellPoly_eval_continuous`: Evaluating a fixed cell polynomial gives a continuous function of the radial-height point. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialTailsModes.lean#L83).

**Read a matrix entry with unit vectors** · theorem. `Breakdown.CertCell.AssemblyPotentialTailsModes.sesq12_single`: Pairing the ith and jth coordinate unit vectors through the sesquilinear form returns matrix entry (i,j). [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialTailsModes.lean#L87).

**Model interactions vary continuously** · theorem. `modelTriple_continuous`: Continuous strain and curl-gradient coefficient entries make their interaction with two fixed field pairs continuous in the plane point. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialTailsModes.lean#L92).

**Continuity of cell coupling models** · theorem. `coupling_continuousOn`: The potential conditions make each model coupling-matrix entry continuous on the corresponding cell rectangle. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialTailsModes.lean#L98).

**Each retained coordinate is continuous** · theorem. `lowProfile_continuous`: Every coordinate of a retained polynomial profile is continuous in the plane point. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialTailsModes.lean#L111).

**Explicit line-weight upper bound** · theorem. `lineWeight_le_mul`: On the cell rectangle, line weight is at most radius times one on an axis cell or the reciprocal inner radius on an annular cell. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialTailsModes.lean#L118).

**Projection error is orthogonal** · theorem. `proj_orth_of_sq`: Under the weighted square-integrability assumptions, the difference from the cell projection is orthogonal to every polynomial in the projection space. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialTailsModes.lean#L127).

**Projection degree of each coordinate** · definition. `tailDeg`: Gradient coordinates use the retained degree, while velocity coordinates use that degree minus one. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialTailsModes.lean#L161).

**Tail coordinates are projection errors** · theorem. `tailProfile_apply`: Every tail coordinate equals the corresponding band-profile coordinate minus its projection at the coordinate's prescribed degree. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialTailsModes.lean#L164).

**First curl component** · theorem. `curlComp_zero`: The first matrix curl component is entry (2,1) minus entry (1,2). [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialTailsModes.lean#L172).

**Second curl component** · theorem. `curlComp_one`: The second matrix curl component is entry (0,2) minus entry (2,0). [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialTailsModes.lean#L176).

**Third curl component** · theorem. `curlComp_two`: The third matrix curl component is entry (1,0) minus entry (0,1). [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialTailsModes.lean#L180).

**Squared norm of a difference** · theorem. `Breakdown.CertCell.AssemblyPotentialTailsModes.norm_sub_sq_le`: The squared norm of a difference is at most twice the sum of the two squared norms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialTailsModes.lean#L184).

**Matrix curl energy bound** · theorem. `Breakdown.CertCell.AssemblyPotentialTailsModes.curlSq_le_two`: The curl energy of a matrix is at most twice the sum of the squared norms of all its entries. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialTailsModes.lean#L189).

**Locations of the nine matrix slots** · theorem. `pairVec_grad`: Coordinate 3a+b of the packed profile is matrix entry (a,b). [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialTailsModes.lean#L198).

**Locations of the three velocity slots** · theorem. `pairVec_vel`: Coordinate 9+a of the packed profile is velocity component a. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialTailsModes.lean#L206).

**Physical profile coordinates are regular** · theorem. `component_regular`: The potential conditions and field regularity give measurability and finite line-weighted squared norm for each band-profile coordinate of a compatible cell tuple. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialTailsModes.lean#L214).

**Recover validity of the cell bases** · theorem. `bases_valid_of`: The given assembly compatibility hypotheses supply the validity conditions for the cell's polynomial bases. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialTailsModes.lean#L244).

**Each tail coordinate is regular** · theorem. `tail_component_regular`: The potential conditions and field regularity give measurability and finite line-weighted squared norm for every tail-profile coordinate of a compatible cell tuple. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialTailsModes.lean#L249).

**Model action on a retained profile** · definition. `cM`: This component applies a model coupling matrix to one retained profile. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialTailsModes.lean#L260).

**Leaf action on a retained profile** · definition. `cL`: This component applies the local leaf matrix to the retained profile of the same harmonic. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialTailsModes.lean#L264).

**Combined model and leaf action** · definition. `hvec`: This vector adds the summed model-coupling action to the local leaf action for the tail pairing. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialTailsModes.lean#L267).

**Model coefficient action is continuous** · theorem. `cM_continuousOn`: The potential conditions make the model action on the retained profile continuous on the cell rectangle for each pair of resolved labels and each coordinate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialTailsModes.lean#L271).

**Continuous cell functions are bounded** · theorem. `bounded_of_continuousOn`: A function continuous on the cell rectangle is almost-everywhere strongly measurable there and has one uniform norm bound on that rectangle. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialTailsModes.lean#L277).

**The leaf coefficient action is regular** · theorem. `cL_regular`: The potential conditions at an admissible parameter make the leaf action on a retained profile measurable and uniformly bounded on the cell rectangle. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialTailsModes.lean#L281).

**Regular combined model and leaf action** · theorem. `hvec_regular`: The potential conditions at an admissible parameter make the combined model and leaf coefficient vector measurable and uniformly bounded on the cell rectangle. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialTailsModes.lean#L300).

**Expand a matrix pairing by rows** · theorem. `sesq12_re_expand`: The real sesquilinear pairing equals the sum of the real conjugate-coordinate products with the matrix-vector product. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialTailsModes.lean#L311).

**Coupling through its coefficient vector** · theorem. `model_term_eq`: The radial-weighted model pairing can be written as the coordinate sum of the conjugate partner profile times the model coefficient vector. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialTailsModes.lean#L321).

**Leaf pairing as a coefficient sum** · theorem. `leaf_term_eq`: At a point of the cell, the radial-weighted leaf pairing of a low profile with a partner vector equals the sum of the conjugate partner coordinates times the leaf coefficient vector. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialTailsModes.lean#L328).

**Combine model and leaf coefficients** · theorem. `per_mode_identity`: For each tail label, the summed model interaction and the local leaf interaction equal the integral against their combined coefficient vector. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialTailsModes.lean#L337).

**Finite-set and subtype sums agree** · theorem. `sum_resolved`: Summing a function over the resolved finite set equals summing it over the subtype of resolved labels. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialTailsModes.lean#L397).

**Upper profile at a resolved label** · theorem. `upperProfiles_val`: The globally indexed upper profile at a resolved label is the low-profile evaluation of the upper part of the state. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialTailsModes.lean#L401).

**Tail profile at a resolved label** · theorem. `tailProfiles_val`: The globally indexed tail profile at a resolved label is its corresponding cell tail profile. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialTailsModes.lean#L407).

### Breakdown.CertCell.AssemblyPressureFlip

This file proves the reflection-conjugation identity for the recovered pressure gradient by transporting the weak pairing identities through reflection. Appendix B.3: cell forms, harmonic estimates and tree assembly.

**Source namespace `Breakdown.CertCell.Assembly.Internal.PressureFlip`.**

**Flip preserves test vectors** · theorem. `flipConj_testVector`: Applying the space-flip conjugation to a space-time test vector again gives a space-time test vector. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPressureFlip.lean#L25).

**Derivative pairing respects the flip** · theorem. `derivative_pairing_conj`: Under the symmetry assumptions on the derivative field, integrating it against a flipped test vector gives the same pairing as the original test vector. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPressureFlip.lean#L33).

**Flip preserves local integrability** · theorem. `locallyIntegrable_flipPair`: Composing with the space-time flip and flipping the vector values preserves local integrability. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPressureFlip.lean#L48).

**Derivative inherits flip symmetry** · theorem. `derivative_flip`: The weak derivative field obeys the stated spatial flip relation almost everywhere when its distributional pairing has that symmetry. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPressureFlip.lean#L62).

**Curl under the flip transform** · theorem. `curlVec_conj`: The curl vector of the transformed linear map equals the spatial flip of the original curl vector. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPressureFlip.lean#L105).

**Flip of a cross product** · theorem. `crossVec_conj`: The cross product of two flipped vectors equals the flip of their cross product. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPressureFlip.lean#L116).

**Trace under the flip transform** · theorem. `secondTrace_conj`: The vector trace of the transformed second derivative equals the flip of the original trace. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPressureFlip.lean#L122).

**Coupling respects flip symmetry** · theorem. `couplingField_conj`: The coupling field evaluated at the flipped point equals the flip of its value at the original point under the specified field symmetries. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPressureFlip.lean#L131).

**The flip average is symmetric** · theorem. `flipAverage_conj`: The flip-averaged field at the flipped point equals the flip of its value at the original point. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPressureFlip.lean#L142).

**Source namespace `Breakdown.CertCell.Assembly`.**

**Supply chosen-pressure reflection** · theorem. `chosenPressureFlip_holds`: Under the stated hypotheses, the pressure facts imply that the chosen pressure gradient commutes with reflection almost everywhere. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPressureFlip.lean#L150).

### Breakdown.CertCell.AssemblyRemainderAnnihilates

This file uses the weak equation to show that the pressure-recovery remainder annihilates compactly supported divergence-free test fields. Appendix B.3: cell forms, harmonic estimates and tree assembly.

**Source namespace `Breakdown.CertCell.Assembly.Internal.RemainderAnnihilates`.**

**Coordinate expansion of a vector** · theorem. `vec_coord`: Every real three-dimensional vector equals the sum of its coordinates times the standard coordinate vectors. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRemainderAnnihilates.lean#L17).

**Read a coordinate expansion** · theorem. `sum_unit_coord`: The ith coordinate of a linear combination of coordinate vectors is its ith coefficient. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRemainderAnnihilates.lean#L22).

**Expand a linear map by columns** · theorem. `clm_coord`: Every coordinate of a linear map applied to a vector is the sum of the vector coordinates times the corresponding matrix-column entries. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRemainderAnnihilates.lean#L25).

**Coordinate formula for inner product** · theorem. `inner_coord`: The real Euclidean inner product equals the sum of coordinatewise products. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRemainderAnnihilates.lean#L30).

**Transpose identity from the curl** · theorem. `cross_identity`: Subtracting the curl cross-product from a linear map changes its pairing into the displayed transposed matrix contraction. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRemainderAnnihilates.lean#L33).

**Coordinate evaluation is continuous** · theorem. `continuous_apply_coord`: Taking any fixed coordinate of a real three-dimensional vector is continuous. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRemainderAnnihilates.lean#L42).

**Coordinate vectors have unit norm** · theorem. `norm_unit`: Every standard coordinate vector has Euclidean norm one. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRemainderAnnihilates.lean#L45).

**Locally integrable matrix columns** · theorem. `column_loc`: Evaluating a locally integrable field of linear maps on a standard coordinate vector gives a locally integrable vector field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRemainderAnnihilates.lean#L48).

**Locally integrable vector coordinates** · theorem. `coord_loc`: Every coordinate of a locally integrable vector field is locally integrable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRemainderAnnihilates.lean#L55).

**A compact factor makes a product fit** · theorem. `int_mul`: A locally integrable scalar function multiplied by the specified continuous compactly supported factor is integrable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRemainderAnnihilates.lean#L61).

**Coordinates preserve smoothness** · theorem. `coord_contDiff`: Taking a coordinate of the given vector-valued test function preserves its differentiability order. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRemainderAnnihilates.lean#L65).

**Coordinates preserve compact support** · theorem. `coord_support`: A coordinate function of a compactly supported vector field has compact support. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRemainderAnnihilates.lean#L69).

**Differentiate a coordinate** · theorem. `fderiv_coord`: The derivative of a vector function's coordinate equals the same coordinate of its derivative applied to the direction. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRemainderAnnihilates.lean#L73).

**Coordinate weak derivative formula** · theorem. `weak_coord`: The weak derivative identity gives integration by parts for each scalar coordinate and each standard coordinate direction. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRemainderAnnihilates.lean#L80).

**Second derivatives cancel weakly** · theorem. `second_derivative_pairing`: The integral of the gradient pairing with the test derivative plus the second-derivative trace pairing with the test field is zero under the weak second-derivative hypotheses. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRemainderAnnihilates.lean#L103).

**Weak product-rule cancellation** · theorem. `product_pairing`: The two displayed matrix-gradient product terms integrate to zero under the divergence and test-function assumptions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRemainderAnnihilates.lean#L152).

**Integrability from local domination** · theorem. `integrable_of_local_bound`: A measurable function dominated on the specified compact support by a locally integrable bound is integrable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRemainderAnnihilates.lean#L223).

**Spatial derivative of a time slice** · theorem. `slice_fderiv`: The spatial derivative of a fixed-time slice is the full space-time derivative composed with the spatial inclusion. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRemainderAnnihilates.lean#L235).

**Spatial slice derivatives as a field** · theorem. `slice_fderiv_eq`: The field of spatial slice derivatives equals the full derivative field composed pointwise with the spatial inclusion. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRemainderAnnihilates.lean#L244).

**Spatial slice derivatives are continuous** · theorem. `slice_fderiv_continuous`: A C1 space-time function has spatial slice derivatives that depend continuously on time and position. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRemainderAnnihilates.lean#L251).

**Spatial derivatives keep compactness** · theorem. `slice_fderiv_support`: The space-time field of spatial derivatives of the compactly supported smooth test field has compact support. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRemainderAnnihilates.lean#L257).

**A time slice has compact support** · theorem. `slice_support`: Each fixed-time slice of the compactly supported space-time test field has compact support. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRemainderAnnihilates.lean#L265).

**A coordinate is bounded by the norm** · theorem. `coord_abs_le`: The absolute value of any real vector coordinate is at most its Euclidean norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRemainderAnnihilates.lean#L270).

**Bound a matrix column by its norm** · theorem. `unit_apply_le`: The norm of a linear map applied to a coordinate unit vector is at most the operator norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRemainderAnnihilates.lean#L274).

**Bound a matrix entry by its norm** · theorem. `entry_abs_le`: The absolute value of any coordinate entry of a linear map is at most its operator norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRemainderAnnihilates.lean#L277).

**Bound the matrix entry pairing** · theorem. `entry_pairing_abs_le`: The absolute matrix-entry pairing is at most three times the product of the two operator norms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRemainderAnnihilates.lean#L280).

**Bound the second-derivative trace** · theorem. `trace_norm_le`: The norm of the second-derivative trace is at most three times the norm of the underlying second-derivative map. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRemainderAnnihilates.lean#L290).

**Matrix-entry pairing is continuous** · theorem. `entry_pairing_continuous`: The real matrix-entry pairing depends continuously on its two linear-map arguments. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRemainderAnnihilates.lean#L298).

**Continuity of the Hessian trace** · theorem. `trace_continuous`: The vector trace is a continuous function of the second-derivative linear map. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRemainderAnnihilates.lean#L304).

**Measurable matrix pairings** · theorem. `entry_pairing_measurable`: The entrywise pairing of two almost-everywhere strongly measurable linear-map fields is almost-everywhere strongly measurable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRemainderAnnihilates.lean#L308).

**Measurable second-derivative traces** · theorem. `trace_measurable`: Taking the vector trace of an almost-everywhere strongly measurable second-derivative field preserves almost-everywhere strong measurability. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRemainderAnnihilates.lean#L314).

**The strong remainder annihilates tests** · theorem. `remainder_annihilates_of`: The weak equation and regularity hypotheses make the assembled strong remainder annihilate all admissible space-time test vectors. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRemainderAnnihilates.lean#L320).

**Source namespace `Breakdown.CertCell.Assembly`.**

**The pressure remainder annihilates tests** · theorem. `remainderAnnihilates_holds`: Under the stated hypotheses, the remainder of an admissible weak right side annihilates all space-time solenoidal test fields. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRemainderAnnihilates.lean#L484).

### Breakdown.CertCell.AssemblyRemainderRegular

This file proves local square integrability of the pressure-recovery remainder from the perturbation bounds and weak second derivatives. Appendix B.3: cell forms, harmonic estimates and tree assembly.

**Source namespace `Breakdown.CertCell.Assembly.Internal.RemainderRegular`.**

**Alternating symbols have magnitude ≤1** · theorem. `abs_alternatingSymbol_le`: Every entry of the real alternating tensor has absolute value at most one. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRemainderRegular.lean#L15).

**Coordinate vectors have norm one** · theorem. `norm_unitVector`: Every standard coordinate vector has Euclidean norm one. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRemainderRegular.lean#L18).

**Bound a three-coordinate combination** · theorem. `norm_combo_le`: If every coefficient has absolute value at most M, the norm of their coordinate-vector combination is at most three times M. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRemainderRegular.lean#L21).

**Bound an alternating contraction** · theorem. `abs_symbol_sum_le`: If the nine coefficients have absolute value at most M, their alternating-tensor contraction has absolute value at most nine times M. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRemainderRegular.lean#L31).

**A coarse cross-product norm bound** · theorem. `norm_crossVec_le`: The norm of the encoded cross product is at most 27 times the product of the two vector norms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRemainderRegular.lean#L46).

**A coarse curl-vector norm bound** · theorem. `norm_curlVec_le`: The norm of the encoded curl vector is at most 27 times the norm of its linear map. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRemainderRegular.lean#L57).

**The real cross product is continuous** · theorem. `continuous_crossVec`: The real three-vector cross product depends continuously on its two vector inputs. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRemainderRegular.lean#L67).

**The curl vector is continuous** · theorem. `Breakdown.CertCell.AssemblyRemainderRegular.continuous_curlVec`: The curl vector depends continuously on the underlying real linear map. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRemainderRegular.lean#L71).

**Continuity of the Hessian trace** · theorem. `continuous_secondDerivTrace`: The vector trace is a continuous function of the second-derivative linear map. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRemainderRegular.lean#L75).

**Spatial derivative by restriction** · theorem. `fderiv_slice_eq`: The spatial derivative of the field at fixed time equals its full space-time derivative composed with the spatial inclusion. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRemainderRegular.lean#L79).

**Spatial slice derivatives are continuous** · theorem. `continuous_slice_fderiv`: A C1 space-time function has spatial slice derivatives that depend continuously on time and position. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRemainderRegular.lean#L88).

**Iterate the slab integral** · theorem. `lintegral_slab`: For the stated measurable integrand, the nonnegative integral over the unit-time spatial slab equals the iterated time and space integrals. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRemainderRegular.lean#L97).

**A finite slab square integral gives L2** · theorem. `memLp_of_slab`: The supplied measurability and finite squared-norm slab integral imply membership in L2 on the unit-time spatial slab. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRemainderRegular.lean#L103).

**L2 gives a finite slab integral** · theorem. `slab_of_memLp`: L2 membership on the unit-time spatial slab makes the iterated nonnegative squared-norm integral finite. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRemainderRegular.lean#L116).

**A slab contributes at most one period** · theorem. `slab_le_period`: The nonnegative integral over the unit-time spatial slab is bounded by the full period integral under the stated sign and measurability assumptions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRemainderRegular.lean#L127).

**Pressure regularity of the remainder** · theorem. `remainder_regular_of`: The given weak field, perturbation, actuator and forcing hypotheses make the strong remainder measurable, time periodic and locally square-integrable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRemainderRegular.lean#L133).

**Source namespace `Breakdown.CertCell.Assembly`.**

**Regularity of the pressure remainder** · theorem. `remainderRegular_holds`: Under the stated hypotheses, the pressure remainder is measurable, periodic and locally square-integrable over one period. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRemainderRegular.lean#L241).

### Breakdown.CertCell.AssemblyResidual

This file combines the potential, pairing, row, tail and elimination estimates into the bound on the cell residual form. Appendix B.3: cell forms, harmonic estimates and tree assembly.

**Source namespace `Breakdown.CertCell.Assembly.Internal`.**

**Rearrange a residual budget with slack** · theorem. `residual_budget_with_slack`: The real and extended-nonnegative budget hypotheses imply the displayed residual inequality after moving signed terms through their positive-part encodings and adding the slack terms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyResidual.lean#L18).

**Nonnegative radius for residual terms** · theorem. `residual_rect_radius_nonneg`: Every point of the cell rectangle has a nonnegative radial coordinate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyResidual.lean#L47).

**A residual cell rectangle is measurable** · theorem. `residual_rect_measurable`: The rectangle belonging to each residual cell is Lebesgue measurable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyResidual.lean#L52).

**Pair-strain slack is nonnegative** · theorem. `residual_slack_nonneg`: The pair-strain slack amount is nonnegative under the stated nonnegative weight assumptions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyResidual.lean#L55).

**The credit share is nonnegative** · theorem. `residual_credit_nonneg`: The allocated credit share is nonnegative under the credit-weight and field hypotheses. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyResidual.lean#L64).

**Split slack across label classes** · theorem. `residual_slack_split`: When resolved and band labels are disjoint, the total pair-strain slack equals the sum of its resolved, band and deactivated-label amounts. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyResidual.lean#L78).

**Actuator energy in the cell state** · theorem. `residual_kappaSq_state`: The actuator-coordinate squared norm of the constructed cell state equals the sum of the input actuator coefficients squared. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyResidual.lean#L104).

**Source section `Rows`.**

**The cell row-stage estimate** · theorem. `rowStage_of_parts`: Under the stated hypotheses, the inverse-weighted row form and resolved pairing slack are bounded by the physical row share and the allocated tail, box, leakage, band and actuator costs. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyResidual.lean#L173).

**Source section `CellLayerBreakdown`.**

**Residual bound from assembled parts** · theorem. `cellResidual_of_parts`: The residual-parts hypotheses give, in every cell, the residual form bound for the cell form minus the energy-leaf form. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyResidual.lean#L187).

**Build all residual parts** · theorem. `residualParts_of_holds`: The finite-piece, allocation, field, potential, pairing, row, tail, top and elimination interfaces, together with assembly conditions and state-range membership, supply the residual-parts package. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyResidual.lean#L196).

**Residual bound from assembly conditions** · theorem. `cellResidual_of_conditions`: The stated assembly conditions and supporting interfaces imply the residual form bound for the cell form minus the energy-leaf form in every cell. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyResidual.lean#L222).

### Breakdown.CertCell.AssemblyRowExpansion

This file assembles the frequency, approximation, long-mode, deactivated-mode and actuator row estimates with their Gram scaling. Appendix B.3: row representation and residual bounds, especially (B.26) and (B.43).

**Source namespace `Breakdown.CertCell.Assembly.RowExpansion.Internal`.**

**Rows couple only within labels** · theorem. `rowGram_block`: The row Gram matrix has zero entries between rows carrying different labels. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansion.lean#L23).

**Scaled Gram inverse as a quadratic** · theorem. `scaled_eq`: The inverse weighted square for the scaled row Gram matrix equals the inverse unscaled Gram quadratic on the row vector multiplied by square-root label weights. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansion.lean#L28).

**Zero time label removes frequency error** · theorem. `freq_zero`: The period-mismatch row contribution is zero when the row's time label is zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansion.lean#L36).

**An inactive group contributes zero** · theorem. `deact_zero`: The deactivated-group row contribution vanishes when that group is outside the row label's active group set. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansion.lean#L41).

**Exact long fields need no allowance** · theorem. `longAllowance_zero`: The long-mode row allowance is zero when both long-field velocity and vorticity error constants are zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansion.lean#L52).

**Matching actuator rows remove the defect** · theorem. `actuator_zero`: If every physical actuator row agrees with its model row, the combined actuator error piece is zero for all actuator coefficients. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansion.lean#L58).

**Actuator norm of the cell state** · theorem. `kappaSq_cellState`: The actuator-coordinate squared norm of a constructed cell state equals the sum of its actuator coefficients squared. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansion.lean#L68).

**Compose coordinate scales on support** · theorem. `scale_match`: Two successive coordinate scales equal the target scale when their products agree at every nonzero coordinate of the input vector. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansion.lean#L76).

**Source namespace `Breakdown.CertCell.Assembly`.**

**Combine the separate row bounds** · theorem. `rowCombine`: Under the stated hypotheses, the row identity, its five bounds and the allowance split imply the row-moment expansion estimate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansion.lean#L89).

### Breakdown.CertCell.AssemblyRowExpansionActuator

This file bounds the row contribution of the actuator fields through weighted harmonic coefficients and the prescribed actuator Gram matrix. Appendix B.3: row representation and residual bounds, especially (B.26) and (B.43).

**Source namespace `Breakdown.CertCell.Assembly.Internal.ActuatorPiece`.**

**A rotated coordinate is norm bounded** · theorem. `rot_coord_abs_le`: The absolute value of a coordinate after axial rotation is at most the original vector norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionActuator.lean#L24).

**Bound a velocity Fourier coefficient** · theorem. `labelVel_norm_le`: The stated uniform orbit bound controls the norm of each labelled velocity coefficient by the same constant. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionActuator.lean#L29).

**The rectangle lies in the half-plane** · theorem. `Breakdown.CertCell.AssemblyRowExpansionActuator.rect_ae_le_halfPlane`: The cell rectangle is contained in the positive radial half-plane up to a Lebesgue-null set. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionActuator.lean#L35).

**Velocity labels are measurable on a cell** · theorem. `labelVel_aesm_rect`: An almost-everywhere strongly measurable space-time vector field has almost-everywhere strongly measurable labelled velocity coordinates on every valid cell rectangle. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionActuator.lean#L50).

**A bounded profile has radial energy** · theorem. `weighted_sq_integrableOn`: A uniformly bounded almost-everywhere measurable scalar profile has integrable radial-weighted squared norm on the cell rectangle. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionActuator.lean#L61).

**Cauchy bound for a scalar combination** · theorem. `norm_sum_smul_sq_le`: The squared norm of a finite real-coefficient complex combination is at most the coefficient square sum times the sum of the complex squared norms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionActuator.lean#L71).

**Weighted actuator combination bound** · theorem. `weighted_combo_le`: With nonnegative weight, the squared norm of the coefficient-weighted actuator differences is bounded by the coefficient energy times the sum of their weighted squared differences. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionActuator.lean#L81).

**Split a weighted difference energy** · theorem. `weighted_diff_le`: A nonnegative weighted squared difference is bounded by twice the separate weighted squared energies, summed over all indices. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionActuator.lean#L92).

**Source section `Main`.**

**Actuator approximation coefficients** · definition. `actDiff`: On the actuator row labels, this vector sums the weighted differences between true and model actuator coefficients, and it is zero elsewhere. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionActuator.lean#L106).

**Actuator row as an error pairing** · theorem. `piece_eq`: The actuator row piece equals the radial-weighted integral of the combined actuator model error paired with the conjugate row test. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionActuator.lean#L112).

**Actuator model error bound** · theorem. `actDiff_weighted_le`: The radial-weighted combined actuator error energy is bounded by the coefficient square sum times the summed actuator-model difference energies. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionActuator.lean#L208).

**Source namespace `Breakdown.CertCell.Assembly`.**

**Bound the actuator row error** · theorem. `actuatorPieceBound_holds`: Under the stated hypotheses, the scaled inverse-Gram squared actuator error is bounded by the actuator cost, error constant and squared κ norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionActuator.lean#L235).
<!-- /passage:front -->

