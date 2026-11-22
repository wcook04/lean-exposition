
<!-- passage:front -->
# Library guide 14: Breakdown/Frac

**Navier–Stokes pages:** [the paper](../navier-stokes-paper/paper.pdf) · [proof routes](../navier-stokes-routes/paper.md) · [routes in detail](../navier-stokes-route-details/paper.md) · library guide: [1](../navier-stokes-library-01/paper.md) [2](../navier-stokes-library-02/paper.md) [3](../navier-stokes-library-03/paper.md) [4](../navier-stokes-library-04/paper.md) [5](../navier-stokes-library-05/paper.md) [6](../navier-stokes-library-06/paper.md) [7](../navier-stokes-library-07/paper.md) [8](../navier-stokes-library-08/paper.md) [9](../navier-stokes-library-09/paper.md) [10](../navier-stokes-library-10/paper.md) [11](../navier-stokes-library-11/paper.md) [12](../navier-stokes-library-12/paper.md) [13](../navier-stokes-library-13/paper.md) **14** [15](../navier-stokes-library-15/paper.md) [16](../navier-stokes-library-16/paper.md) [17](../navier-stokes-library-17/paper.md) [18](../navier-stokes-library-18/paper.md) [19](../navier-stokes-library-19/paper.md) [20](../navier-stokes-library-20/paper.md) [21](../navier-stokes-library-21/paper.md) [22](../navier-stokes-library-22/paper.md) [23](../navier-stokes-library-23/paper.md) [24](../navier-stokes-library-24/paper.md) [25](../navier-stokes-library-25/paper.md) [26](../navier-stokes-library-26/paper.md) [27](../navier-stokes-library-27/paper.md) [28](../navier-stokes-library-28/paper.md) [29](../navier-stokes-library-29/paper.md) [30](../navier-stokes-library-30/paper.md)

*A plain title and a sentence for each declaration in `Breakdown.Frac.Defs` to `Breakdown.Frac.StProfile` of Alpöge and Buckmaster's Lean at `ad53419de079eb8f95f60313473374624a348546`, in the authors' file order. Prepared with AI assistance. The authors have not reviewed it.*

Each paragraph names one declaration and says whether it is a definition, a proposition that the library defines (its name usually ends in `Holds` or `Statement`) or a proved result, then what it states. Click a paragraph to open its Lean on the right.

### Breakdown.Frac.Defs

This file defines the fractional equation and rotating-profile hypotheses for separate Lean fractional conclusions, beyond the ordinary paper endpoint statements.

**Second-order Taylor remainder.** The remainder subtracts the value, first derivative and half the repeated second derivative from the shifted field value. (`Breakdown.secondOrderRemainder`)

**Fractional normalization integral.** The normalization integrates the inverse-(3 + 2α) radial weight against cos(z₀) − 1 + z₀²/2. (`Breakdown.fractionalNormalizer`)

**Fractional power of a vector field.** The fractional power is the weighted integral of the second-order Taylor remainder divided by its normalization. (`Breakdown.fractionalPowerAt`)

**Smooth fractional solution.** This proposition packages smooth velocity and pressure on nonnegative time, the initial condition, the fractional momentum equation and zero divergence for positive time. (`Breakdown.IsFractionalSolution`)

**Fractional breakdown on space.** This proposition asks, for every positive viscosity, for smooth compactly supported solenoidal data admitting no global smooth fractional solution with one uniform energy bound. (`Breakdown.FractionalBreakdownOnSpace`)

**Fractional breakdown on the torus.** This proposition asks, for every positive viscosity, for smooth periodic solenoidal data admitting no global smooth fractional solution with periodic velocity. (`Breakdown.FractionalBreakdownOnTorus`)

**Infinitesimal axial rotation.** The axial turn sends the first two coordinates to their quarter-turn rotation and has zero third coordinate. (`Breakdown.axialTurn`)

**Rotating fractional profile residual.** The residual adds similarity drift, axial rotation, fractional dissipation, advection and the pressure gradient with the stated coefficients. (`Breakdown.rotatingProfileResidual`)

**Decaying rotating fractional profile.** This proposition requires a nonzero smooth solenoidal rotating profile at positive viscosity with smooth fractional power and the stated all-order velocity, pressure and fractional-power decay. (`Breakdown.RotatingFractionalProfileExists`)

### Breakdown.Frac.Main

This file closes the separate fractional breakdown conclusions from a rotating fractional profile for 1 < α < 5/4; these are Lean-only extensions.

**Fractional profile gives space breakdown.** For 1 < α < 5/4, the existence of the stated rotating fractional profile implies fractional breakdown on space. (`Breakdown.fractional_breakdown_on_space_proved`)

**Fractional profile gives torus breakdown.** For 1 < α < 5/4, the existence of the stated rotating fractional profile implies fractional breakdown on the torus. (`Breakdown.fractional_breakdown_on_torus_proved`)

### Breakdown.Frac.NNiceDense

This file constructs smooth Fourier approximants in the graph norm of fractional dissipation for the fractional weak-solution machinery.

**Smooth weighted symbol away from zero.** Multiplying a smooth symbol that vanishes near zero by any stated radial frequency power preserves smoothness. (`_private.Breakdown.Frac.NNiceDense.0.Breakdown.Freq.contDiff_weight_smul`)

**Frequency weights preserve nice symbols.** Multiplication by a radial frequency power preserves the nice-symbol conditions. (`_private.Breakdown.Frac.NNiceDense.0.Breakdown.Freq.nice_weight`)

**Bound a compact-frequency power.** For positive α and the stated support radius, the weighted L² norm is bounded by the maximum frequency factor times the original L² norm. (`_private.Breakdown.Frac.NNiceDense.0.Breakdown.Freq.eLpNorm_weight_le`)

**Continuous positive fractional weight.** The fractional frequency weight is continuous when α is positive. (`_private.Breakdown.Frac.NNiceDense.0.Breakdown.Freq.continuous_weight`)

**Approximate both sides of the graph.** For positive α, a fractional derivative pair can be approximated arbitrarily closely in both L² components by a nice symbol and its weighted symbol. (`_private.Breakdown.Frac.NNiceDense.0.Breakdown.Freq.symbolDense`)

**Dense nice fractional graph.** For 1 < α < 3/2, the stated embedding and multiplier identities imply density of the nice fractional graph. (`Breakdown.Freq.fracNiceGraphDense`)

### Breakdown.Frac.NNiceEmbed

This file checks compatibility of nice physical fields with energy-space embeddings, Laplacians and fractional powers.

**Real part after complexification.** Taking the real-part vector after complexifying a real spatial vector returns it. (`Breakdown.Freq.FracInternal.NiceEmbed.realVec_complexifyVec_eq`)

**Even multipliers preserve nice symbols.** An even real multiplier smooth off the origin preserves the nice-symbol conditions. (`Breakdown.Freq.FracInternal.NiceEmbed.isNiceSymbol_smul`)

**Laplacian weights preserve nice symbols.** Multiplying by the stated Laplacian factor preserves the nice-symbol conditions. (`Breakdown.Freq.FracInternal.NiceEmbed.isNiceSymbol_traceSecondDeriv`)

**Fractional weights preserve nice symbols.** Multiplication by the fractional radial weight preserves the nice-symbol conditions. (`Breakdown.Freq.FracInternal.NiceEmbed.isNiceSymbol_frac`)

**Negative Laplacian of a nice field.** The negative Laplacian of a nice field is the nice field of its Laplacian-weighted symbol. (`Breakdown.Freq.FracInternal.NiceEmbed.negTraceSecondDeriv_niceField`)

**Embed a nice fractional power.** For 1 < α < 3/2, the nice-field embedding-symbol identity and fractional multiplier identity identify embedding the negative Laplacian and fractional power of every nice field with the corresponding energy-space operators. (`Breakdown.Freq.fracNiceEmbedPower`)

### Breakdown.Frac.NNiceField

This file realizes nice Fourier symbols as solenoidal Schwartz fields and proves the physical fractional-power multiplier identity.

**Nice symbol as a Schwartz function.** A nice symbol is packaged as a Schwartz function using its smoothness and compact support. (`Breakdown.FracInternal.NiceField.symbolS`)

**Underlying Schwartz symbol.** The packaged Schwartz symbol has the original symbol as its underlying function. (`Breakdown.FracInternal.NiceField.symbolS_coe`)

**Nice field as a Schwartz function.** The real part of the inverse Fourier transform of a nice symbol is packaged as a real Schwartz field. (`Breakdown.FracInternal.NiceField.fieldS`)

**Underlying Schwartz field.** The packaged Schwartz field is the nice physical field defined from the symbol. (`Breakdown.FracInternal.NiceField.fieldS_coe`)

**Complexify the inverse Fourier field.** Complexifying the real Schwartz field recovers the complex inverse Fourier transform of its nice symbol. (`Breakdown.FracInternal.NiceField.complexify_fieldS`)

**Fourier transform of a nice field.** The Fourier transform of the complexified Schwartz field is the original nice symbol. (`Breakdown.FracInternal.NiceField.transform_fieldS`)

**Identify a field by its transform.** A continuous integrable real field whose complexified Fourier transform is a nice symbol equals that symbol's nice field. (`Breakdown.FracInternal.NiceField.eq_niceField_of_transform`)

**Norm of the fractional kernel factor.** The norm of the radial fractional weight times a vector is the weight times the vector norm. (`Breakdown.FracInternal.NiceField.kernel_smul_norm`)

**Integrable Schwartz fractional power.** For 1 < α < 3/2, the fractional power of a Schwartz field is integrable. (`Breakdown.FracInternal.NiceField.integrable_fracPower`)

**Taylor-remainder bound far from zero.** For ‖z‖ ≥ 1, the remainder is bounded by the shifted field norm plus the displayed quadratic bound on the value and first two derivatives at x. (`Breakdown.FracInternal.NiceField.remainder_far_bound`)

**Continuous Schwartz fractional power.** For 1 < α < 3/2, the fractional power of a Schwartz field is continuous. (`Breakdown.FracInternal.NiceField.continuous_fracPower`)

**Fourier transform through a linear map.** A continuous complex-linear map commutes with the Fourier transform of a Schwartz field. (`Breakdown.FracInternal.NiceField.transform_clm_apply`)

**Nice fields are divergence-free.** The Schwartz field reconstructed from a nice symbol has zero divergence. (`Breakdown.FracInternal.NiceField.divergence_fieldS`)

**Fractional multiplier for a nice field.** For 1 < α < 3/2, the fractional power of a nice field is the nice field obtained by multiplying its symbol by (2π‖ξ‖)²ᵅ. (`Breakdown.Freq.fracPower_niceField`)

**Properties of nice fractional fields.** For 1 < α < 3/2, every nice field has a Schwartz representative and the required decay, stays nice under the negative Laplacian and fractional power, and these two operators commute on it. (`Breakdown.Freq.niceFieldProps`)

### Breakdown.Frac.NNicePairing

This file proves integration-by-parts identities for nice solenoidal Fourier fields, shared by the fractional weak formulation and its energy-space realization.

**Zero Fourier divergence sum.** For a nice symbol, the sum of the indicated inverse-transformed coordinate derivatives is zero. (`Breakdown.Freq.Internal.NicePairing.coord_sum_zero`)

**Schwartz realization of a nice symbol.** Every nice symbol is the transform of a solenoidal real Schwartz field equal to its nice-field reconstruction. (`Breakdown.Freq.Internal.NicePairing.rapid_of_symbol`)

**Pair bounded data with Schwartz data.** A continuous bounded field has integrable scalar pairing with every Schwartz field. (`Breakdown.Freq.Internal.NicePairing.integrable_inner_rapid`)

**Uniform bounds for a decay field.** A decay field and its first spatial derivative admit one uniform bound of the stated form. (`Breakdown.Freq.Internal.NicePairing.decay_bounds`)

**Nice fields are Schwartz functions.** Every nice field has a real Schwartz representative equal to it pointwise. (`Breakdown.Freq.Internal.NicePairing.rapid_of_nice`)

**Repeated directional derivative.** For a smooth field, the repeated second derivative in v equals differentiating its directional derivative again in v. (`Breakdown.Freq.Internal.NicePairing.iteratedFDeriv_two_diag`)

**Directional derivative as Schwartz data.** A directional derivative of a Schwartz field equals its packaged Schwartz line derivative. (`Breakdown.Freq.Internal.NicePairing.dir_eq`)

**Second directional Schwartz derivative.** A repeated directional derivative equals the underlying function of the twice-applied Schwartz line-derivative operator. (`Breakdown.Freq.Internal.NicePairing.dir_dir_eq`)

**Integration by parts against Schwartz.** A smooth field with the stated value and derivative bounds pairs its first derivative against a Schwartz derivative as minus the pairing with the second derivative. (`Breakdown.Freq.Internal.NicePairing.coord_ibp`)

**Coordinates reconstruct a direction.** Summing the coordinate coefficients of v times the indicated pairings equals the pairing with the linear map applied to v. (`Breakdown.Freq.Internal.NicePairing.sum_coord_inner`)

**Nice-field embedding identity.** For a nice Fourier symbol, embedding its reconstructed nice field in the energy space equals 2π times frequency length times that symbol almost everywhere. (`Breakdown.Freq.niceEmbedSymbol`)

**Nice-field integration by parts.** For a decay field and a nice test field, their gradient pairing equals pairing the decay field with the negative Laplacian of the test field. (`Breakdown.Freq.nicePairingByParts`)

**Nice-field advection pairing.** For a decay field and a nice test field, the advection pairing equals the trilinear form with the embedded decay field in its first two entries. (`Breakdown.Freq.niceAdvectionTrilinear`)

### Breakdown.Frac.OpCovariance

This file proves translation, rotation and dilation laws for the physical fractional operator, together with its additivity.

**Taylor remainder under dilation.** For a C² field, spatial dilation sends the Taylor remainder to the remainder at the dilated point and increment. (`Breakdown.FracInternal.secondOrderRemainder_comp_smul`)

**Scale the fractional power.** For a C² field and positive scale l, spatial dilation multiplies its fractional power by l²ᵅ at the dilated point. (`Breakdown.FracInternal.fractionalPowerAt_comp_smul`)

**Scale the field amplitude.** The fractional power of a scalar multiple of a C² field is the same scalar multiple of its fractional power. (`Breakdown.FracInternal.fractionalPowerAt_const_smul`)

**Rotate the Taylor remainder.** For a C² field, rotating both its input coordinates and vector values rotates the remainder at inverse-rotated point and increment. (`Breakdown.FracInternal.secondOrderRemainder_comp_isometry`)

**Rotate the fractional power.** The fractional power of a rotated C² field is the rotated fractional power at the inverse-rotated point. (`Breakdown.FracInternal.fractionalPowerAt_comp_isometry`)

**Translate the fractional power.** Translating a field's input translates its fractional power by the same amount. (`Breakdown.FracInternal.fractionalPowerAt_comp_add`)

**Fractional covariance laws.** For every twice continuously differentiable vector field and every α, the fractional operator commutes with translations, scalar multiplication and rotations, and acquires the factor l to the power 2α under a positive spatial dilation l. (`Breakdown.covariance`)

**Additivity of fractional powers.** At a point where two fields are twice continuously differentiable and their weighted second-order remainders are integrable, the fractional power of their sum equals the sum of their fractional powers. (`Breakdown.additivity`)

### Breakdown.Frac.OpExports

This file collects the proved analytic interfaces for the fractional remainder integral, Fourier multiplier and symmetry identities.

**Integrability of the remainder kernel.** For 1 < α < 3/2, a smooth vector field that is square integrable or uniformly bounded has an integrable second-order remainder weighted by the inverse power 3 + 2α of the increment length at every base point. (`Breakdown.remainderIntegrable`)

**Exchange Fourier and remainder integrals.** For 1 < α < 3/2 and a Schwartz field, the Fourier transform of its fractional power equals its Fourier transform multiplied by the integrated symbol kernel divided by the fractional normalizer. (`Breakdown.symbolExchange`)

**Fractional Fourier-multiplier identity.** For 1 < α < 3/2 and a Schwartz field, the fractional power is the Fourier multiplier (2π times frequency length) to the power 2α. (`Breakdown.symbol`)

**Symmetry against compact test fields.** For 1 < α < 3/2, a smooth square integrable or bounded field and a smooth compactly supported test field give integrable pairings with equal integrals when the fractional operator is moved from one factor to the other. (`Breakdown.symmetryCompact`)

**Symmetry against rapidly decaying tests.** For 1 < α < 3/2, a smooth field with bounded derivatives through order three and a Schwartz test field give integrable pairings with equal integrals when the fractional operator is moved from one factor to the other. (`Breakdown.symmetryRapid`)

### Breakdown.Frac.OpIntegrable

This file combines near-origin and far-field power integrability to justify the fractional remainder integral.

**Integrable powers inside the unit ball.** A radial power of exponent greater than −3 is integrable inside the unit ball in space. (`Breakdown.FracInternal.integrableOn_ball_norm_rpow`)

**Integrable powers outside the unit ball.** A radial power of exponent less than −3 is integrable outside the unit ball in space. (`Breakdown.FracInternal.integrableOn_compl_ball_norm_rpow`)

**Remainder integrability from its bound.** The Taylor-remainder bound makes the second-order remainder of every smooth square integrable or uniformly bounded field integrable against increment length to the power −(3 + 2α) at each base point when 1 < α < 3/2. (`Breakdown.remainderIntegrable_of`)

### Breakdown.Frac.OpNormalizer

This file proves integrability and the required properties of the normalization constant in the fractional operator.

**Piecewise radial majorant.** The radial majorant uses exponent 1 − 2α below radius one and exponent −1 − 2α outside. (`Breakdown.FracInternal.radialBound`)

**Integrability of the radial majorant.** For 1 < α < 2, the piecewise radial majorant is integrable over space. (`Breakdown.FracInternal.radialBound_integrable`)

**Continuous first coordinate.** The first spatial coordinate is continuous. (`Breakdown.FracInternal.coord_continuous`)

**Nonnegative normalization integrand.** The weighted cosine remainder in the fractional normalization is nonnegative. (`Breakdown.FracInternal.integrand_nonneg`)

**Bound the normalization integrand.** For α > 1, the normalization integrand is bounded above by the piecewise radial majorant. (`Breakdown.FracInternal.integrand_le`)

**Integrable normalization integrand.** For 1 < α < 2, the normalization integrand is integrable. (`Breakdown.FracInternal.integrand_integrable`)

**Fractional normalization properties.** For 1 < α < 2, the weighted cosine remainder defining the fractional normalizer is integrable and the normalizer is positive. (`Breakdown.normalizer`)

### Breakdown.Frac.OpRemainder

This file proves the Taylor-remainder estimate that controls the singular fractional kernel near the origin.

**Differentiate along the Taylor line.** For a C³ field and k < 3, the kth derivative evaluated repeatedly in z along x + sz differentiates to the next iterated derivative. (`_private.Breakdown.Frac.OpRemainder.0.Breakdown.lineValue_hasDerivAt`)

**Bound a curve from its derivative.** A differentiable curve starting at zero whose derivative norm is bounded by nonnegative B on [0, 1] has norm at most B there. (`_private.Breakdown.Frac.OpRemainder.0.Breakdown.unitInterval_bound`)

**Taylor-remainder estimate.** For a three-times continuously differentiable field whose third derivative is bounded by C on the closed ball spanning an increment, its second-order Taylor remainder is at most C times the cube of the increment length. (`Breakdown.remainderBound`)

### Breakdown.Frac.OpRemainderProduct

This file supplies product-space integrability for the Fourier transform of the fractional remainder operator on Schwartz data.

**One decay bound through order three.** A Schwartz field has one nonnegative fourth-power decay bound for all derivatives through order three. (`Breakdown.FracInternal.rapidDecay_three`)

**Divide out the radial weight.** A bound on (1 + ‖x‖)⁴a gives the corresponding fourth-power decay bound on a. (`Breakdown.FracInternal.le_mul_weight`)

**Integrable fourth-power weight.** The radial weight (1 + ‖x‖)⁻⁴ is integrable on space. (`Breakdown.FracInternal.integrable_weight`)

**Integrability in both spatial variables.** For 1 < α < 3/2 and a Schwartz field, the norm of its second-order remainder weighted by the inverse power 3 + 2α of the increment length is jointly integrable in the base point and increment. (`Breakdown.remainderProductIntegrable`)

### Breakdown.Frac.OpRemainderTransform

This file computes the Fourier transform of the second-order Taylor remainder before integrating its fractional kernel.

**Complex lift of a Schwartz field.** The lift complexifies a real Schwartz field by postcomposing with the continuous complexification map. (`Breakdown.FracInternal.RemainderTransform.lift`)

**Evaluate the complex lift.** The complex lift evaluates to pointwise complexification of the original field. (`Breakdown.FracInternal.RemainderTransform.lift_apply`)

**Underlying complex lift.** The underlying lifted function is complexification composed with the original Schwartz function. (`Breakdown.FracInternal.RemainderTransform.coe_lift`)

**Differentiate the complex lift.** The derivative of the lifted field is the complexification of the original derivative. (`Breakdown.FracInternal.RemainderTransform.fderiv_lift`)

**Second derivative of the complex lift.** The repeated second derivative of the lift equals the complexification of the original repeated second derivative. (`Breakdown.FracInternal.RemainderTransform.iteratedFDeriv_lift`)

**Schwartz and iterated second derivatives.** Applying the Schwartz directional-derivative operator twice equals the repeated second iterated derivative. (`Breakdown.FracInternal.RemainderTransform.second_eq`)

**Complexify the Taylor remainder.** The complexified remainder is the translated lifted field minus its value, first derivative and half the repeated second derivative. (`Breakdown.FracInternal.RemainderTransform.pointwise`)

**Fourier transform of a positive shift.** Shifting a Schwartz field by +z multiplies its Fourier transform by the corresponding Fourier character. (`Breakdown.FracInternal.RemainderTransform.transform_translate`)

**Transform a directional derivative.** A Schwartz directional derivative transforms to the stated factor 2πi〈ξ, z〉 times the original Fourier transform. (`Breakdown.FracInternal.RemainderTransform.transform_deriv_apply`)

**Transform the quadratic Taylor part.** The Fourier transform of the value-plus-linear-plus-quadratic Taylor expression is the displayed three-term Fourier polynomial. (`Breakdown.FracInternal.RemainderTransform.transform_lincomb`)

**The phase Taylor remainder.** Subtracting the second-order Fourier polynomial from the Fourier character gives the defined phase remainder times the vector. (`Breakdown.FracInternal.RemainderTransform.scalar_identity`)

**Transform the Taylor remainder.** The Fourier transform in the base point of a Schwartz field’s second-order remainder equals the original Fourier transform multiplied by the corresponding phase remainder. (`Breakdown.remainderTransform`)

### Breakdown.Frac.OpSymbol

This file assembles the scalar kernel calculation and integral exchange into the fractional Fourier-multiplier identity.

**Split real and imaginary symbol parts.** The symbol integrand splits into its weighted cosine remainder plus i times its weighted sine remainder. (`Breakdown.FracInternal.symbolIntegrand_split`)

**Evaluate the symbol integral.** For 1 < α < 3/2, the scalar-symbol interface identifies the integrated symbol with ‖2πξ‖²ᵅ times the fractional normalizer. (`Breakdown.FracInternal.symbolIntegral_eq`)

**Assemble the fractional symbol identity.** The Fourier integral-exchange, scalar-symbol and normalization statements identify the fractional operator on every Schwartz field with Fourier multiplication by (2π times frequency length) to the power 2α when 1 < α < 3/2. (`Breakdown.symbol_of`)

### Breakdown.Frac.OpSymbolExchange

This file justifies exchanging the Fourier integral with the singular remainder integral using product-space integrability.

**Complexification preserves the norm.** Complexifying a real spatial vector preserves its norm. (`Breakdown.FracInternal.norm_complexifyVec_eq`)

**Complexification as a real isometry.** The complexification map is packaged as a real linear isometry. (`Breakdown.FracInternal.complexifyIsom`)

**Evaluate the complexification isometry.** The packaged isometry acts as the complexification map. (`Breakdown.FracInternal.complexifyIsom_apply`)

**Joint continuity of the remainder.** The Taylor remainder of a Schwartz field is continuous jointly in its base point and increment. (`Breakdown.FracInternal.continuous_remainder`)

**Integrable modulated remainder product.** The stated weighted norm integrability makes the Fourier-modulated complex remainder integrable on the product of the two spatial variables. (`Breakdown.FracInternal.integrable_product`)

**Transform the inner remainder integral.** The remainder-transform interface identifies the inner Fourier integral with the symbol integrand times the field's Fourier transform. (`Breakdown.FracInternal.inner_step`)

**Exchange the symbol integrals.** The remainder-transform and product-integrability interfaces imply the Fourier-symbol integral exchange. (`Breakdown.symbolExchange_of`)

### Breakdown.Frac.OpSymbolScalar

This file evaluates the scalar fractional symbol by rotation, scaling and cancellation of the odd sine part.

**Align a frequency with one coordinate.** For a nonzero frequency, some spatial isometry expresses the frequency pairing as its norm times the first transformed coordinate. (`_private.Breakdown.Frac.OpSymbolScalar.0.Breakdown.FracInternal.scalarCoordIsometry`)

**Rescale the cosine remainder.** A nonzero frequency admits a rotation and dilation that express its weighted cosine remainder as the stated power of its norm times the coordinate remainder. (`_private.Breakdown.Frac.OpSymbolScalar.0.Breakdown.FracInternal.scalarCosRescale`)

**Integrate the cosine contribution.** For 1 < α < 3/2, normalization gives integrability of the cosine contribution and its integral as ‖ξ‖²ᵅ times the normalizer. (`_private.Breakdown.Frac.OpSymbolScalar.0.Breakdown.FracInternal.scalarCosPart`)

**Cubic bound on the sine remainder.** The absolute sine remainder |sin t − t| is at most 2|t|³. (`_private.Breakdown.Frac.OpSymbolScalar.0.Breakdown.FracInternal.scalarSinCube`)

**Linear bound on the sine remainder.** The absolute sine remainder |sin t − t| is at most 2|t|. (`_private.Breakdown.Frac.OpSymbolScalar.0.Breakdown.FracInternal.scalarSinLin`)

**Compare far radial decay factors.** For x ≥ 1 and nonnegative r, x⁻ʳ is at most 2ʳ(1 + x)⁻ʳ. (`_private.Breakdown.Frac.OpSymbolScalar.0.Breakdown.FracInternal.scalarFarBound`)

**Integrable weighted sine contribution.** For 1 < α < 3/2, the weighted sine remainder is integrable over space. (`_private.Breakdown.Frac.OpSymbolScalar.0.Breakdown.FracInternal.scalarSinIntegrable`)

**The sine contribution integrates to zero.** The weighted sine remainder has integral zero. (`_private.Breakdown.Frac.OpSymbolScalar.0.Breakdown.FracInternal.scalarSinIntegral`)

**Scalar symbol from normalization.** For 1 < α < 3/2, the normalization statement gives integrability of the weighted cosine and sine remainders, with the cosine integral equal to frequency length to the power 2α times the normalizer and the sine integral equal to zero. (`Breakdown.symbolScalar`)

### Breakdown.Frac.OpSymmetry

This file proves symmetry of the fractional operator when paired against smooth compactly supported test fields.

**Far-field Taylor-remainder bound.** For ‖z‖ ≥ 1, the remainder is bounded by the shifted value plus the stated quadratic expression in the base value and its first two derivatives. (`_private.Breakdown.Frac.OpSymmetry.0.Breakdown.FracInternal.norm_remainder_le_far`)

**Integrability from two radial bounds.** An almost everywhere measurable scalar function with near exponent below three and far exponent above three is integrable under the stated bounds. (`_private.Breakdown.Frac.OpSymmetry.0.Breakdown.FracInternal.integrable_of_near_far`)

**Uniform translated compact pairing.** A continuous field that is L² or uniformly bounded has a uniformly integrable norm pairing with all translates of a continuous compactly supported field. (`_private.Breakdown.Frac.OpSymmetry.0.Breakdown.FracInternal.exists_bound_translate`)

**Integrable compactly supported pairing.** The scalar pairing of two continuous fields is integrable when the second has compact support. (`_private.Breakdown.Frac.OpSymmetry.0.Breakdown.FracInternal.integrable_inner_compact_right`)

**Support of a directional derivative.** A directional derivative of a compactly supported field has compact support. (`_private.Breakdown.Frac.OpSymmetry.0.Breakdown.FracInternal.hasCompactSupport_fderiv_apply`)

**One integration by parts.** Pairing a directional derivative of a smooth field with a smooth compactly supported field equals minus the pairing with the test derivative. (`_private.Breakdown.Frac.OpSymmetry.0.Breakdown.FracInternal.integral_inner_fderiv_eq_neg`)

**Repeated directional derivative formula.** For a smooth field, the second iterated derivative on two copies of z is its twice-taken directional derivative. (`_private.Breakdown.Frac.OpSymmetry.0.Breakdown.FracInternal.iteratedFDeriv_two_eq_fderiv_apply`)

**Move a Taylor remainder to the test.** For smooth fields with compactly supported test, the remainder pairing transfers to the test remainder with increment −z. (`_private.Breakdown.Frac.OpSymmetry.0.Breakdown.FracInternal.integral_inner_remainder_eq`)

**Combine real and natural powers.** For nonnegative t and the stated nonzero exponents, multiplying tʳ by tⁿ gives tʳ⁺ⁿ. (`_private.Breakdown.Frac.OpSymmetry.0.Breakdown.FracInternal.rpow_mul_pow_eq_aux`)

**Jointly continuous Taylor remainder.** The Taylor remainder of a smooth field is jointly continuous in point and increment. (`_private.Breakdown.Frac.OpSymmetry.0.Breakdown.FracInternal.continuous_remainder_pair`)

**Continuous remainder at fixed increment.** At fixed increment, the Taylor remainder of a smooth field is continuous in its base point. (`_private.Breakdown.Frac.OpSymmetry.0.Breakdown.FracInternal.continuous_remainder_section`)

**Integrable left remainder pairing.** For 1 < α < 3/2, the remainder bound makes the stated smooth L²-or-bounded field pairing with a compact test integrable on product space. (`_private.Breakdown.Frac.OpSymmetry.0.Breakdown.FracInternal.integrable_prod_left_side`)

**The remainder vanishes outside support.** An increment of norm at most r gives zero test remainder outside the closed r-thickening of the test support. (`_private.Breakdown.Frac.OpSymmetry.0.Breakdown.FracInternal.remainder_eq_zero_of_far`)

**Integrable right remainder pairing.** For 1 < α < 3/2, the remainder bound makes the field paired with the compact test's remainder integrable on product space under the stated hypotheses. (`_private.Breakdown.Frac.OpSymmetry.0.Breakdown.FracInternal.integrable_prod_right_side`)

**Fractional symmetry for compact tests.** The remainder-bound and remainder-integrability interfaces imply fractional symmetry against compact test fields. (`Breakdown.symmetryCompact_of`)

### Breakdown.Frac.OpSymmetryRapid

This file extends the fractional symmetry identity from compactly supported tests to rapidly decaying Schwartz tests.

**Far bound for the Taylor remainder.** For ‖z‖ ≥ 1, the Taylor remainder has the stated shifted-value and quadratic bound. (`_private.Breakdown.Frac.OpSymmetryRapid.0.Breakdown.FracInternal.rapid_norm_remainder_le_far`)

**Integrability from near and far decay.** An almost everywhere measurable scalar with the stated near exponent below three and far exponent above three is integrable. (`_private.Breakdown.Frac.OpSymmetryRapid.0.Breakdown.FracInternal.rapid_integrable_of_near_far`)

**Combine radial powers.** For nonnegative t and the stated nonzero exponents, tʳ times tⁿ equals tʳ⁺ⁿ. (`_private.Breakdown.Frac.OpSymmetryRapid.0.Breakdown.FracInternal.rapid_rpow_mul_pow`)

**Continuity of a smooth remainder.** A smooth field has a jointly continuous Taylor remainder. (`_private.Breakdown.Frac.OpSymmetryRapid.0.Breakdown.FracInternal.rapid_continuous_remainder`)

**Norm bound for the second derivative.** The repeated second derivative in z is bounded by its operator norm times ‖z‖². (`_private.Breakdown.Frac.OpSymmetryRapid.0.Breakdown.FracInternal.rapid_norm_second_le`)

**Second derivative along a line.** For a smooth field, the repeated second iterated derivative equals the twice-taken directional derivative. (`_private.Breakdown.Frac.OpSymmetryRapid.0.Breakdown.FracInternal.rapid_second_eq`)

**Integrable pairing with bounded data.** A continuous bounded field has integrable scalar pairing with any integrable field. (`_private.Breakdown.Frac.OpSymmetryRapid.0.Breakdown.FracInternal.rapid_integrable_inner`)

**Integrable directional derivative.** For a smooth field, integrability of the derivative norm implies integrability of each fixed directional derivative. (`_private.Breakdown.Frac.OpSymmetryRapid.0.Breakdown.FracInternal.rapid_integrable_fderiv_apply`)

**Integrable second directional derivative.** For a smooth field, integrability of the second-derivative norm implies integrability of each repeated directional derivative. (`_private.Breakdown.Frac.OpSymmetryRapid.0.Breakdown.FracInternal.rapid_integrable_second`)

**Integrable-test integration by parts.** Under the stated value and directional-derivative bounds and test integrability, one directional derivative transfers to the test with a minus sign. (`_private.Breakdown.Frac.OpSymmetryRapid.0.Breakdown.FracInternal.rapid_ibp`)

**Move the remainder to an integrable test.** With the stated smoothness, bounded derivatives and integrable test derivatives, the remainder pairing transfers to the test with the opposite increment. (`_private.Breakdown.Frac.OpSymmetryRapid.0.Breakdown.FracInternal.rapid_shift_identity`)

**Weighted product-space integrability.** For 1 < α < 3/2, the stated cubic near bound, quadratic far bound and integrable nonnegative majorant make the weighted product-space integrand integrable. (`_private.Breakdown.Frac.OpSymmetryRapid.0.Breakdown.FracInternal.rapid_integrable_prod`)

**Local third-derivative majorant.** A Schwartz field admits an integrable nonnegative majorant for its third derivative throughout every unit neighbourhood. (`_private.Breakdown.Frac.OpSymmetryRapid.0.Breakdown.FracInternal.rapid_third_decay`)

**One bound for four derivative orders.** Separate uniform derivative bounds through order three combine into one nonnegative bound for the field and its first three derivatives. (`_private.Breakdown.Frac.OpSymmetryRapid.0.Breakdown.FracInternal.rapid_uniform_bounds`)

**Integrable bounded remainder pairing.** For 1 < α < 3/2, the stated bounds through order three and remainder interface make the weighted remainder pairing with a continuous integrable test integrable. (`_private.Breakdown.Frac.OpSymmetryRapid.0.Breakdown.FracInternal.rapid_left_prod`)

**Integrable Schwartz remainder pairing.** For 1 < α < 3/2, a continuous bounded field paired with a Schwartz remainder gives an integrable weighted product under the remainder bound. (`_private.Breakdown.Frac.OpSymmetryRapid.0.Breakdown.FracInternal.rapid_right_prod`)

**Fractional symmetry for Schwartz tests.** The remainder-bound and integrability interfaces imply fractional symmetry against rapidly decaying test fields. (`Breakdown.symmetryRapid_of`)

### Breakdown.Frac.PAxial

This file gives the explicit axial rotations and their derivatives used to turn a rotating fractional profile into a physical solution.

**First coordinate of axial rotation.** The first rotated coordinate is cos θ times y₀ minus sin θ times y₁. (`Breakdown.FracInternal.Axial.axialFormula_zero_coord`)

**Second coordinate of axial rotation.** The second rotated coordinate is sin θ times y₀ plus cos θ times y₁. (`Breakdown.FracInternal.Axial.axialFormula_one_coord`)

**Third coordinate of axial rotation.** Axial rotation leaves the third coordinate unchanged. (`Breakdown.FracInternal.Axial.axialFormula_two_coord`)

**First coordinate of the axial turn.** The first axial-turn coordinate is −y₁. (`Breakdown.FracInternal.Axial.turn_zero_coord`)

**Second coordinate of the axial turn.** The second axial-turn coordinate is y₀. (`Breakdown.FracInternal.Axial.turn_one_coord`)

**Third coordinate of the axial turn.** The third axial-turn coordinate is zero. (`Breakdown.FracInternal.Axial.turn_two_coord`)

**Equality from three coordinates.** Equality of all three coordinates implies equality of spatial vectors. (`Breakdown.FracInternal.Axial.space_coord_ext`)

**Add rotation angles.** Rotation by θ + θ′ equals rotation by θ after rotation by θ′. (`Breakdown.FracInternal.Axial.axialFormula_add`)

**Zero-angle rotation.** Axial rotation through angle zero is the identity. (`Breakdown.FracInternal.Axial.axialFormula_zero`)

**Rotate a sum.** The axial-rotation formula preserves vector addition. (`Breakdown.FracInternal.Axial.axialFormula_map_add`)

**Rotate a scalar multiple.** The axial-rotation formula preserves real scalar multiplication. (`Breakdown.FracInternal.Axial.axialFormula_map_smul`)

**Cancel the rotation on the left.** Rotation by −θ after rotation by θ returns the original vector. (`Breakdown.FracInternal.Axial.axialFormula_neg_self`)

**Cancel the rotation on the right.** Rotation by θ after rotation by −θ returns the original vector. (`Breakdown.FracInternal.Axial.axialFormula_self_neg`)

**Rotation preserves the spatial norm.** The axial-rotation formula preserves the spatial vector norm. (`Breakdown.FracInternal.Axial.axialFormula_norm`)

**Axial rotation as a linear map.** The axial-rotation formula is packaged as a real linear map. (`Breakdown.FracInternal.Axial.axialFormulaLinear`)

**Axial rotation as an isometry.** The axial-rotation formula is packaged as a linear isometry with inverse angle −θ. (`Breakdown.FracInternal.Axial.axialFormulaEquiv`)

**Chosen rotation equals its formula.** The chosen axial rotation agrees with the explicit coordinate formula. (`Breakdown.FracInternal.Axial.axialRotation_eq_formula`)

**Planar cosine component.** The cosine component retains the first two coordinates and sets the third to zero. (`Breakdown.FracInternal.Axial.axialCosPart`)

**Planar sine component.** The sine component sends the first two coordinates to their quarter-turn rotation and sets the third to zero. (`Breakdown.FracInternal.Axial.axialSinPart`)

**Split an axial rotation.** The rotated vector is its cosine component times cos θ plus its sine component times sin θ, with the original third coordinate added. (`Breakdown.FracInternal.Axial.axialFormula_split`)

**Differentiate the rotation angle.** Differentiating axial rotation in its angle gives the axial turn of the rotated vector. (`Breakdown.FracInternal.Axial.axialRotation_hasDerivAt`)

**Axial-rotation specification.** Axial rotations satisfy their explicit coordinate formula, compose by angle addition, have inverse at the negative angle, equal the identity at zero and depend continuously and differentiably on angle with derivative given by the axial turn. (`Breakdown.axialRotationSpec`)

### Breakdown.Frac.PBlowup

This file passes from a rotating fractional profile to mild blow-up through the scaled abstract framework; it belongs to the Lean fractional extension.

**Rotating slice at time zero.** The rotating slice at similarity time zero equals the original profile. (`_private.Breakdown.Frac.PBlowup.0.Breakdown.FracInternal.rotatingSlice_zero`)

**Positive dilation exponent.** The dilation exponent is positive when α > 1. (`_private.Breakdown.Frac.PBlowup.0.Breakdown.FracInternal.dilExponent_pos`)

**Mild blow-up from the profile route.** The stated scaled-transfer, orbit, viscosity, profile-equivalence and decay interfaces imply fractional mild blow-up. (`Breakdown.fracMildBlowup_of`)

### Breakdown.Frac.PFlow

This file adapts the relation between physical mild solutions and similarity-time flows to the fractional scaling framework.

**Joint continuity of scaled dilation.** In a scaled mild framework on a real Hilbert space, dilation depends jointly continuously on its positive scale and input vector. (`Breakdown.scaledDilateJointContinuous`)

**Rescale the abstract bilinear kernel.** In a scaled mild framework, positive a, b and τ give the displayed covariance identity for the kernel and two inverse-dilated inputs. (`_private.Breakdown.Frac.PFlow.0.Breakdown.scaledKernelDilate`)

**Scaled flow from a mild solution.** In a scaled mild framework, a mild solution on the corresponding physical interval related to an orbit by the stated logarithmic time change and dilation yields an interval-integrable nonlinear term and the scaled variation-of-constants formula between any two ordered orbit times. (`Breakdown.scaledFlowOfMild`)

### Breakdown.Frac.PMomentum

This file differentiates the rotating self-similar field and verifies its fractional momentum equation using the profile residual.

**Axial turns commute with rotation.** Under the axial-rotation specification, axial turning commutes with axial rotation. (`Breakdown.FracInternal.Momentum.turn_rot_comm`)

**Rotation as a continuous linear map.** The rotation map is the continuous linear map underlying axial rotation. (`Breakdown.FracInternal.Momentum.rotMap`)

**Evaluate the linear rotation map.** The continuous linear rotation map acts as axial rotation. (`Breakdown.FracInternal.Momentum.rotMap_apply`)

**Projection onto the rotation axis.** The axis component is half the sum of rotation by zero and rotation by π. (`Breakdown.FracInternal.Momentum.axisPart`)

**Planar cosine map.** The cosine component is rotation by zero minus the axis component. (`Breakdown.FracInternal.Momentum.cosPart`)

**Planar sine map.** The sine component is rotation by π/2 minus the axis component. (`Breakdown.FracInternal.Momentum.sinPart`)

**Decompose the rotation operator.** Under the rotation specification, the rotation operator is cos θ times the cosine map plus sin θ times the sine map plus the axis map. (`Breakdown.FracInternal.Momentum.rotMap_split`)

**Differentiate a rotating vector curve.** Under the rotation specification, differentiating a vector curve with varying angle gives the angle derivative times the axial turn plus the rotated vector derivative. (`Breakdown.FracInternal.Momentum.rot_hasDerivAt`)

**Expand in the coordinate basis.** Every spatial vector is the sum of its coordinate multiples of unit vectors. (`Breakdown.FracInternal.Momentum.vec_sum`)

**Vector of a linear functional.** A real linear functional equals the inner product with the vector formed from its basis values. (`Breakdown.FracInternal.Momentum.apply_inner_sum`)

**Gradient under an inverse rotation.** The gradient of a differentiable scalar composed with an inverse isometry is the rotated gradient at the inverse-rotated point. (`Breakdown.FracInternal.Momentum.gradientAt_comp_isometry`)

**Gradient under scaling.** Scaling a scalar field's amplitude by k and argument by m scales its gradient by km at the scaled point. (`Breakdown.FracInternal.Momentum.gradientAt_scaled`)

**Derivative under two scalings.** Scaling a differentiable vector field's amplitude by c and argument by m multiplies its directional derivative by cm at the scaled point. (`Breakdown.FracInternal.Momentum.fderiv_scaled_apply`)

**Derivative of a pushed-forward field.** The derivative of a pushed-forward differentiable field is the rotated original derivative on the inverse-rotated direction. (`Breakdown.FracInternal.Momentum.fderiv_pushForward_apply`)

**Match the fractional scaling powers.** For nonzero α and positive l, the three displayed dissipation, advection and pressure scaling factors equal the common factor l¹⁻¹ᐟ²ᵅl. (`Breakdown.FracInternal.Momentum.scalar_facts`)

**Close the rescaled momentum algebra.** The stated profile residual, commutation and common-factor identities give the displayed rescaled balance of dissipation, advection and pressure. (`Breakdown.FracInternal.Momentum.final_alg`)

**Differentiate the self-similar field.** Under the rotation specification and profile differentiability, the self-similar field has the displayed time derivative for t < 1. (`Breakdown.FracInternal.Momentum.selfSimilar_hasDerivAt`)

**Self-similar fractional momentum.** The axial-rotation specification makes the self-similar field of each unit-viscosity rotating profile satisfy the pointwise momentum equation before time one for 1 < α < 5/4, with time derivative equal to minus fractional dissipation, advection and pressure gradient. (`Breakdown.selfSimilarMomentum`)

### Breakdown.Frac.POrbit

This file constructs an energy-space orbit from a rotating fractional profile by passing through the physical weak and mild equations.

**Advance a rotating slice.** Under the rotation specification, advancing similarity time by P′ rotates the earlier slice by angle −aP′. (`_private.Breakdown.Frac.POrbit.0.Breakdown.rotatingSlice_add_period`)

**Profile orbit from weak evolution.** The self-similar weak equation, weak-to-mild conversion, scaled-flow, rotating-slice continuity and axial-rotation statements turn each unit-viscosity rotating profile for 1 < α < 5/4 into a rotating orbit of every matching fractional scaled mild framework at every positive period. (`Breakdown.fracProfileOrbit_of`)

**Profile orbit with standard bridges.** The self-similar weak equation and weak-to-mild conversion turn each unit-viscosity rotating profile for 1 < α < 5/4 into a rotating orbit of every matching fractional scaled mild framework at every positive period. (`Breakdown.fracProfileOrbit_of_weak`)

### Breakdown.Frac.PProfileIff

This file aligns the two encodings of a rotating fractional profile used by the analytic and abstract orbit routes.

**Equivalent fractional-profile encodings.** For every α, the rotating fractional profile existence assertion is equivalent to the existence of velocity, pressure, rotation-rate and viscosity data satisfying the rotating-profile condition. (`Breakdown.profileExistsIff`)

### Breakdown.Frac.PSlice

This file proves decay and time continuity of rotating fractional-profile slices before embedding them into the orbit framework.

**Derivative norms under rotation.** Every iterated derivative norm of a pushed-forward field equals the original norm at the inverse-rotated point. (`Breakdown.FracInternal.SliceBounds.norm_iteratedFDeriv_pushForward`)

**Weaken a radial power to an integer.** For t ≥ 1 and r at least n, t⁻ʳ is bounded by 1/tⁿ. (`Breakdown.FracInternal.SliceBounds.rpow_le_inv_pow`)

**Basic decay of a fractional profile.** A unit-viscosity rotating profile with α > 1 has a common inverse-linear value bound and inverse-quadratic derivative bound. (`Breakdown.FracInternal.SliceBounds.profile_bounds`)

**Uniform decay of rotating slices.** Every rotating slice of such a profile has the same uniform value and first-derivative decay bounds. (`Breakdown.FracInternal.SliceBounds.slice_bounds`)

**Derivative of a rotated field.** The derivative of a pushed-forward differentiable field is its rotated derivative at inverse-rotated point and direction. (`Breakdown.FracInternal.SliceBounds.fderiv_pushForward_apply`)

**Rotation preserves zero divergence.** Pushing forward a smooth divergence-free field by a spatial isometry preserves zero divergence. (`Breakdown.FracInternal.SliceBounds.divergence_pushForward`)

**Rotating slices are decay fields.** Every rotating slice of a unit-viscosity profile with α > 1 satisfies the decay-field conditions. (`Breakdown.FracInternal.SliceBounds.slice_decayField`)

**Subtract two decay fields.** The difference of two decay fields is again a decay field. (`Breakdown.FracInternal.SliceBounds.decay_sub`)

**Continuity of a rotating vector curve.** Under the rotation specification, continuous angle and vector curves give a continuous rotated curve. (`Breakdown.FracInternal.SliceBounds.rot_apply_continuous`)

**Continuity of slice derivatives in time.** Under the rotation specification, the fixed directional spatial derivative of a smooth rotating slice is continuous in time. (`Breakdown.FracInternal.SliceBounds.slice_fderiv_continuous`)

**Decay of rotating profile slices.** For 1 < α < 5/4, every time slice of a unit-viscosity rotating profile is a decay field with spatial derivatives bounded through order three. (`Breakdown.rotatingSliceDecay`)

**Slice continuity from rotations.** The axial-rotation specification makes the embedded rotating slices of every unit-viscosity profile a continuous energy-space curve when 1 < α < 5/4. (`Breakdown.rotatingSliceContinuous`)

**Continuity of rotating profile slices.** For 1 < α < 5/4, embedding the time slices of a unit-viscosity rotating profile in the energy space gives a continuous curve. (`Breakdown.rotatingSliceContinuous_holds`)

### Breakdown.Frac.PTimeBound

This file bounds the physical time derivative of the self-similar fractional field by rescaling its profile decay estimates.

**Fractional power under rigid scaling.** For a C² field and positive spatial scale, the fractional power of the rotated scaled field acquires the stated amplitude times l²ᵅ factor. (`Breakdown.FracInternal.rigidScale_power`)

**Derivative under rigid scaling.** The derivative of a rotated and scaled differentiable vector field has the displayed amplitude and transformed-direction factors. (`Breakdown.FracInternal.rigidScale_fderiv_apply`)

**Scalar derivative under rigid scaling.** The derivative of a scaled scalar field composed with an isometry has the displayed amplitude and direction transformation. (`Breakdown.FracInternal.rigidScale_scalar_fderiv_apply`)

**Gradient bounded by coordinate partials.** The scalar gradient norm is bounded by the sum of the absolute coordinate directional derivatives. (`_private.Breakdown.Frac.PTimeBound.0.Breakdown.FracInternal.gradientAt_norm_le_sum`)

**Bound the rescaled PDE residual.** For α > 1 and μ ≥ 1, the stated profile decay bounds give the displayed μ²⁻¹ᐟ²ᵅ spatial-decay bound on the combined fractional, advection and pressure terms. (`Breakdown.FracInternal.rigidScale_residual_bound`)

**Self-similar time-derivative bound.** The axial-rotation and self-similar momentum statements bound differences between two self-similar times in [0, T], with T less than one, by a constant times their time difference times (1 + distance) to the power −(4α − 1) for each unit-viscosity profile with 1 < α < 5/4. (`Breakdown.selfSimilarTimeBound`)

### Breakdown.Frac.PUnitViscosity

This file normalizes the viscosity of a rotating fractional profile by amplitude and spatial scaling.

**Scale an axial turn.** Axial turning commutes with scalar multiplication. (`_private.Breakdown.Frac.PUnitViscosity.0.Breakdown.FracInternal.axialTurn_smul`)

**Scale a spatial derivative.** For a differentiable field, scaling amplitude by c and position by l multiplies its derivative by cl at the scaled point. (`_private.Breakdown.Frac.PUnitViscosity.0.Breakdown.FracInternal.fderiv_scaled`)

**Scale an iterated-derivative norm.** For a smooth field, the order-j derivative norm scales by |c||l|ʲ under amplitude and spatial rescaling. (`_private.Breakdown.Frac.PUnitViscosity.0.Breakdown.FracInternal.norm_iteratedFDeriv_scaled`)

**Transfer decay under positive scaling.** At positive l and nonnegative decay exponent, the scaled decay weight is bounded by the unscaled weight times min(1, l) raised to the negative exponent. (`_private.Breakdown.Frac.PUnitViscosity.0.Breakdown.FracInternal.decay_scaled`)

**Rescale a profile to viscosity one.** For α > 1, the stated positive scale and scalar identities turn a viscosity-ν rotating profile into a unit-viscosity profile. (`_private.Breakdown.Frac.PUnitViscosity.0.Breakdown.FracInternal.profile_scaled`)

**Normalize fractional-profile viscosity.** For 1 < α < 5/4, rescaling space by ν to the power 1/(2α), velocity by its reciprocal and pressure by ν to the power −1/α turns a rotating profile at viscosity ν into a rotating profile at unit viscosity. (`Breakdown.unitViscosity`)

### Breakdown.Frac.PWeak

This file turns the self-similar fractional momentum equation into its weak form by canceling pressure against solenoidal Schwartz tests.

**Scale all derivative norms.** A smooth field's order-j derivative norm scales by |c||l|ʲ under amplitude and spatial scaling. (`Breakdown.FracInternal.WeakProfile.norm_iteratedFDeriv_scaled`)

**Scaling preserves bounded derivatives.** Fractional scaling preserves the existence of uniform derivative bounds through order three. (`Breakdown.FracInternal.WeakProfile.scale_bounded`)

**Uniform bounds from decay.** A decay field and its first derivative admit a common uniform bound. (`Breakdown.FracInternal.WeakProfile.decay_bdd`)

**Uniform advection bound.** Uniform value and first-derivative bounds by B give an advection norm bound of B². (`Breakdown.FracInternal.WeakProfile.adv_bdd`)

**Continuous smooth advection.** The advection term of a smooth field is continuous. (`Breakdown.FracInternal.WeakProfile.continuous_advection`)

**Integrable bounded-Schwartz pairing.** A continuous bounded field has integrable scalar pairing with a Schwartz field. (`Breakdown.FracInternal.WeakProfile.integrable_inner_bdd`)

**Drop the fractional decay weight.** For α > 1, the stated weighted norm bound implies the uniform bound |K||d|. (`Breakdown.FracInternal.WeakProfile.weighted_norm_le_abs`)

**Square a weighted norm bound.** Squaring a pointwise decay bound squares its constant and doubles its exponent. (`Breakdown.FracInternal.WeakProfile.sq_le_of_le`)

**Integrable squared fractional weight.** For α > 1, the weight with exponent −2(4α − 1) is integrable over space. (`Breakdown.FracInternal.WeakProfile.integrable_weight`)

**Smooth scalar directional derivative.** Every directional derivative of a smooth scalar field is smooth. (`Breakdown.FracInternal.WeakProfile.smooth_dir_scalar`)

**Smooth vector components.** Each coordinate component of a smooth vector field is smooth. (`Breakdown.FracInternal.WeakProfile.coord_smooth`)

**Derivative of a vector coordinate.** Differentiating a component equals taking that component of the vector derivative. (`Breakdown.FracInternal.WeakProfile.coord_dir`)

**Expand a gradient pairing.** Pairing a gradient with a vector equals the sum of the scalar coordinate derivatives times that vector's coordinates. (`Breakdown.FracInternal.WeakProfile.gradient_inner`)

**Coordinate controlled by vector norm.** Each absolute coordinate is at most the spatial norm. (`Breakdown.FracInternal.WeakProfile.coord_le`)

**Norm of a coordinate unit vector.** Every coordinate unit vector has norm one. (`Breakdown.FracInternal.WeakProfile.unit_norm`)

**Pressure cancellation against tests.** A smooth globally Lipschitz pressure has an integrable gradient pairing with every divergence-free Schwartz test, and that pairing integrates to zero. (`Breakdown.FracInternal.WeakProfile.gradient_pairing_zero`)

**Lipschitz bound under rigid scaling.** A scalar increment bound with constant M becomes the displayed |k|M|l| bound after amplitude, isometry and spatial scaling. (`Breakdown.FracInternal.WeakProfile.comp_increment`)

**Self-similar pressure is Lipschitz.** A unit-viscosity rotating profile with α > 1 gives a finite nonnegative global Lipschitz constant for each self-similar pressure slice. (`Breakdown.FracInternal.WeakProfile.pressure_increment`)

**Smooth self-similar pressure slices.** Every self-similar pressure slice of a rotating profile is smooth in space. (`Breakdown.FracInternal.WeakProfile.pressure_smooth`)

**Weak equation from the profile.** The stated momentum, time-bound, slice-decay and nice-field interfaces imply the self-similar weak equation. (`Breakdown.selfSimilarWeak_of`)

### Breakdown.Frac.RBilin

This file constructs and bounds the fractional bilinear evolution in the energy space from its trilinear pairing.

**Integrable fractional trilinear density.** At positive time, the fractional test-field bounds make the trilinear density integrable. (`_private.Breakdown.Frac.RBilin.0.Breakdown.Freq.FracInternal.BilinBound.integrable_density`)

**Add fractional test arguments.** Under the fractional test-field bounds, the trilinear pairing preserves addition in its positive-time test argument. (`_private.Breakdown.Frac.RBilin.0.Breakdown.Freq.FracInternal.BilinBound.tri_phi_add`)

**Scale the fractional test argument.** Scaling the test state scales the trilinear pairing by the same real scalar. (`_private.Breakdown.Frac.RBilin.0.Breakdown.Freq.FracInternal.BilinBound.tri_phi_smul`)

**Symmetry of the fractional bilinear form.** Exchanging the two state inputs leaves the fractional bilinear form unchanged. (`_private.Breakdown.Frac.RBilin.0.Breakdown.Freq.FracInternal.BilinBound.form_symm`)

**Add the first bilinear-form input.** Under the fractional test bounds and positive time, the form preserves addition in its first input. (`_private.Breakdown.Frac.RBilin.0.Breakdown.Freq.FracInternal.BilinBound.form_add_left`)

**Scale the first bilinear-form input.** Scaling the first state input scales the fractional form by that scalar. (`_private.Breakdown.Frac.RBilin.0.Breakdown.Freq.FracInternal.BilinBound.form_smul_left`)

**Add the bilinear-form test input.** Under the fractional test bounds and positive time, the form preserves addition in its test input. (`_private.Breakdown.Frac.RBilin.0.Breakdown.Freq.FracInternal.BilinBound.form_add_right`)

**Scale the bilinear-form test input.** Scaling the test input scales the fractional form by that scalar. (`_private.Breakdown.Frac.RBilin.0.Breakdown.Freq.FracInternal.BilinBound.form_smul_right`)

**Bound the mixed L²-L⁶ test norm.** For α > 1, the test-field bounds control the geometric mean of its L² and L⁶ norms by Dτ⁻³ᐟ⁴ᵅ times the state norm. (`_private.Breakdown.Frac.RBilin.0.Breakdown.Freq.FracInternal.BilinBound.sqrt_le`)

**Bound the fractional trilinear form.** For α > 1, the fractional test bounds give a nonnegative constant controlling the form by τ⁻³ᐟ⁴ᵅ times all three state norms. (`_private.Breakdown.Frac.RBilin.0.Breakdown.Freq.FracInternal.BilinBound.form_bound`)

**Construct the fractional bilinear map.** For α > 1, the fractional test-field bounds imply existence and the norm bound of the fractional bilinear map. (`Breakdown.Freq.fracBilinExistsBound`)

### Breakdown.Frac.RBilinDilate

This file proves the dilation covariance of the fractional bilinear map through its Fourier test operator and physical trilinear form.

**Cube of the fractional spatial scale.** For positive μ, μ³ᐟ²ᵅ equals the cube of μ¹ᐟ²ᵅ. (`Breakdown.FracInternal.BilinDilate.pow_three_eq`)

**Inverse fractional spatial scale.** For positive μ, μ⁻¹ᐟ²ᵅ equals the reciprocal of μ¹ᐟ²ᵅ. (`Breakdown.FracInternal.BilinDilate.pw_neg`)

**Separate the dilation volume factor.** For positive μ, μ¹⁻³ᐟ²ᵅ equals μ divided by the cube of the fractional spatial scale. (`Breakdown.FracInternal.BilinDilate.pw_main`)

**Invert the inverse-scale exponent.** For positive μ, applying the negative fractional exponent to μ⁻¹ gives the positive fractional scale. (`Breakdown.FracInternal.BilinDilate.pw_inv_neg`)

**Volume factor for inverse dilation.** For positive μ, the inverse dilation amplitude equals μ⁻¹ times the cube of the fractional spatial scale. (`Breakdown.FracInternal.BilinDilate.pw_inv_main`)

**Separate the velocity scale factor.** For positive μ, μ¹⁻¹ᐟ²ᵅ equals μ divided by the fractional spatial scale. (`Breakdown.FracInternal.BilinDilate.pw_vel`)

**Recover the original scale.** For positive μ and nonzero α, raising μ¹ᐟ²ᵅ to power 2α gives μ. (`Breakdown.FracInternal.BilinDilate.pw_back`)

**Underlying L² fractional dilation.** The fractional-dilation algebra identifies the underlying L² class with the stated amplitude times Fourier-space scaling at positive μ. (`Breakdown.FracInternal.BilinDilate.fracDilX_coe`)

**Dilation in volume-factor notation.** The underlying fractional-dilation class equals μ divided by the cubed spatial scale times the inverse Fourier scaling operator. (`Breakdown.FracInternal.BilinDilate.fracDilX_coe'`)

**Underlying inverse dilation.** Under the dilation algebra, inverse fractional dilation has the stated inverse amplitude and forward Fourier scaling. (`Breakdown.FracInternal.BilinDilate.fracDilX_inv_coe`)

**Nonnegative fractional test factor.** The fractional smoothing-test factor is nonnegative. (`Breakdown.FracInternal.BilinDilate.fracPhiFactor_nonneg`)

**Bound the fractional test factor.** For α > 1 and positive τ, the fractional test factor is at most 1 + τ⁻¹. (`Breakdown.FracInternal.BilinDilate.fracPhiFactor_le`)

**Measurable fractional test multiplier.** The fractional test-factor multiplier is almost everywhere strongly measurable. (`Breakdown.FracInternal.BilinDilate.aesm_fracPhiOp`)

**Operator norm of the test multiplier.** For α > 1 and positive τ, the fractional test multiplier has operator norm at most 1 + τ⁻¹. (`Breakdown.FracInternal.BilinDilate.norm_fracPhiOp_le`)

**Scale the fractional test factor.** For positive c, scaling time by c²ᵅ equals scaling frequency by c with the stated additional factor c⁻¹. (`Breakdown.FracInternal.BilinDilate.fracPhiFactor_scale`)

**Physical form of the test operator.** The fractional test field is the physical representative of its stated Fourier multiplier. (`Breakdown.FracInternal.BilinDilate.fracPhiX_eq`)

**Dilate a physical partial field.** Under fractional dilation algebra and positive μ, the partial field scales in amplitude by μ and in position by μ¹ᐟ²ᵅ almost everywhere. (`Breakdown.FracInternal.BilinDilate.partialX_fracDilX`)

**Dilate the fractional test field.** For α > 1 and positive μ and τ, the inverse-dilated test field at time μτ obeys the stated inverse-space and amplitude scaling almost everywhere. (`Breakdown.FracInternal.BilinDilate.fracPhiX_dil_inv`)

**Adjoint relation for fractional dilation.** Under the dilation algebra, moving positive fractional dilation across the inner product introduces the stated squared-amplitude over volume factor and inverse dilation. (`Breakdown.FracInternal.BilinDilate.fracDilX_adjoint`)

**Scale one trilinear summand.** Scaling the three factors in a trilinear summand multiplies it by the product of their scalars. (`Breakdown.FracInternal.BilinDilate.summand_scale'`)

**Substitute scaled trilinear factors.** The three stated scalar identities give the displayed common factor in one trilinear summand. (`Breakdown.FracInternal.BilinDilate.summand_eq`)

**Scale a spatial integral.** At positive spatial scale c, the integral of kG(cx) equals k/c³ times the original integral. (`Breakdown.FracInternal.BilinDilate.integral_scale'`)

**Scale the fractional trilinear pairing.** Under the stated fractional dilation and velocity interfaces, the positive-time trilinear pairing satisfies the displayed scaling relation. (`Breakdown.FracInternal.BilinDilate.trilinear_fracDilX`)

**Chosen bilinear map specification.** Existence of the fractional bilinear map ensures that the chosen positive-time map satisfies its specification. (`Breakdown.FracInternal.BilinDilate.fracBilinX_spec`)

**Fractional bilinear dilation law.** For α > 1, the stated existence, dilation, velocity and heat interfaces imply fractional bilinear dilation covariance. (`Breakdown.Freq.fracBilinDilate`)

### Breakdown.Frac.RBilinH1

This file identifies the abstract fractional bilinear map with heat-projected physical advection for bounded H¹ fields.

**Representative of an Lᵖ class.** For Lᵖ data, the chosen Lᵖ-or-zero class agrees almost everywhere with the input function. (`_private.Breakdown.Frac.RBilinH1.0.Breakdown.FracInternal.BilinH1.toLpOrZero_ae`)

**Specification from bilinear existence.** Existence of the fractional bilinear map gives the specification of the chosen map at positive time. (`_private.Breakdown.Frac.RBilinH1.0.Breakdown.FracInternal.BilinH1.spec_of_exists`)

**Pointwise representative of a multiplier.** A bounded almost everywhere measurable field multiplier acts pointwise on an L² representative almost everywhere. (`_private.Breakdown.Frac.RBilinH1.0.Breakdown.FracInternal.BilinH1.fieldOp_id_ae`)

**Pair complexified and complex vectors.** Pairing a complexified real vector with a complex vector equals pairing the original vector with its real part. (`_private.Breakdown.Frac.RBilinH1.0.Breakdown.FracInternal.BilinH1.inner_complexifyVec`)

**Pair complexified L² fields.** The real L² inner product with a complexified field equals the pairing with the other field's real part. (`_private.Breakdown.Frac.RBilinH1.0.Breakdown.FracInternal.BilinH1.inner_complexify`)

**Fourier transform as a real isometry.** The L² Fourier transform is packaged as a real linear isometric equivalence. (`_private.Breakdown.Frac.RBilinH1.0.Breakdown.FracInternal.BilinH1.transformIsometry`)

**Move Fourier across the inner product.** The real pairing with a Fourier-transformed field equals the pairing with the inverse transform on the other argument. (`_private.Breakdown.Frac.RBilinH1.0.Breakdown.FracInternal.BilinH1.inner_transform`)

**Nonnegative fractional test factor.** The fractional test factor is nonnegative. (`_private.Breakdown.Frac.RBilinH1.0.Breakdown.FracInternal.BilinH1.factor_nonneg`)

**Bound the fractional test factor.** For α > 1 and positive time, the fractional test factor is at most 1 + τ⁻¹. (`_private.Breakdown.Frac.RBilinH1.0.Breakdown.FracInternal.BilinH1.factor_le`)

**Bound the test-multiplier operator.** For α > 1 and positive time, the test multiplier has operator norm at most 1 + τ⁻¹. (`_private.Breakdown.Frac.RBilinH1.0.Breakdown.FracInternal.BilinH1.norm_factor_smul_le`)

**Measurable test-multiplier operator.** The fractional test multiplier is almost everywhere strongly measurable. (`_private.Breakdown.Frac.RBilinH1.0.Breakdown.FracInternal.BilinH1.aesm_factor`)

**Adjoint of projected fractional heat.** For α > 1 and positive time, pairing solenoidal fractional heat with a state equals pairing its real L² input with the fractional test field. (`_private.Breakdown.Frac.RBilinH1.0.Breakdown.FracInternal.BilinH1.proj_inner`)

**Advection as a coordinate sum.** The advection term is the sum of velocity coordinates times the corresponding partial fields. (`_private.Breakdown.Frac.RBilinH1.0.Breakdown.FracInternal.BilinH1.advectionAt_eq_sum`)

**Square-integrable bounded H¹ advection.** An H¹ field with the stated uniform value and derivative bounds has L² advection. (`_private.Breakdown.Frac.RBilinH1.0.Breakdown.FracInternal.BilinH1.advection_memLp`)

**Physical H¹ bilinear formula.** For α > 1, existence of the fractional bilinear map implies its H¹ physical formula. (`Breakdown.FracInternal.BilinH1.formula`)

**Export the H¹ bilinear formula.** For α > 1, existence of the fractional bilinear map gives the exported H¹ formula interface. (`Breakdown.Freq.fracBilinH1Formula`)

### Breakdown.Frac.RBilinRotate

This file proves rotation covariance of fractional bilinear evolution using radial Fourier multipliers.

**Radial multipliers commute with rotation.** A field multiplier invariant under every spatial rotation commutes with rotation on complex L². (`_private.Breakdown.Frac.RBilinRotate.0.Breakdown.Freq.radialOp_rot`)

**Rotationally invariant test factor.** The fractional test factor is unchanged by inverse rotation of its frequency. (`_private.Breakdown.Frac.RBilinRotate.0.Breakdown.Freq.fracPhiFactor_rot`)

**Rotate the fractional test field.** Applying the fractional test operator to a rotated state rotates the original test field almost everywhere. (`_private.Breakdown.Frac.RBilinRotate.0.Breakdown.Freq.fracPhiX_rot`)

**Rotation preserves the bilinear form.** Simultaneously rotating the two state inputs and the test state leaves the fractional bilinear form unchanged. (`_private.Breakdown.Frac.RBilinRotate.0.Breakdown.Freq.fracBilinForm_rot`)

**Rotate the fractional bilinear map.** The stated fractional bilinear existence and rotation-algebra interfaces imply fractional bilinear rotation covariance. (`Breakdown.Freq.fracBilinRotate`)

### Breakdown.Frac.RBilinShiftCont

This file proves heat-time shifts and continuity of the fractional bilinear map, including a careful realization of its smoothing multiplier.

**Scalar Fourier multiplier family.** The scalar-multiplier family scales the identity map at each frequency by m(ξ). (`Breakdown.Freq.FracInternal.BilinShiftCont.scalarMul`)

**Realization gives pointwise action.** An operator realized by the stated multiplier acts as m(ξ) times its input representative almost everywhere. (`Breakdown.Freq.FracInternal.BilinShiftCont.realized_ae`)

**Pointwise action gives realization.** An operator with the stated almost-everywhere multiplier formula satisfies that realization relation. (`Breakdown.Freq.FracInternal.BilinShiftCont.realized_of_ae`)

**Realize a bounded scalar multiplier.** A bounded measurable scalar factor realizes its chosen field operator. (`Breakdown.Freq.FracInternal.BilinShiftCont.bounded_realized`)

**Fractional heat as a field operator.** Fractional L² heat evolution is the field operator for its scalar heat factor. (`Breakdown.Freq.FracInternal.BilinShiftCont.heat_eq`)

**Realized fractional heat.** Fractional L² heat evolution satisfies the realization relation for its heat factor. (`Breakdown.Freq.FracInternal.BilinShiftCont.heat_realized`)

**Measurable fractional test factor.** The fractional test factor is measurable. (`Breakdown.Freq.FracInternal.BilinShiftCont.phi_measurable`)

**Combine heat and test time.** At nonnegative heat time s, multiplying the test factor at τ by the heat factor at s gives the test factor at s + τ. (`Breakdown.Freq.FracInternal.BilinShiftCont.phi_mul_heat`)

**General positive-order test-factor bound.** For positive α and τ, the test factor has the stated factorial and inverse-power upper bound. (`Breakdown.Freq.FracInternal.BilinShiftCont.phi_bound`)

**Low-frequency part of the test factor.** The low part retains the test factor on frequencies satisfying 2π‖ξ‖ ≤ 1 and is zero elsewhere. (`Breakdown.Freq.FracInternal.BilinShiftCont.lowPart`)

**High-frequency compensating factor.** The high part is the positive exponential factor on frequencies with 2π‖ξ‖ > 1 and zero on the low-frequency region. (`Breakdown.Freq.FracInternal.BilinShiftCont.highPart`)

**Measurable frequency cutoff.** The indicator of 2π‖ξ‖ ≤ 1 is measurable. (`Breakdown.Freq.FracInternal.BilinShiftCont.cut_measurable`)

**Measurable low-frequency factor.** The low-frequency test factor is measurable. (`Breakdown.Freq.FracInternal.BilinShiftCont.lowPart_measurable`)

**Measurable high-frequency factor.** The high-frequency compensating factor is measurable. (`Breakdown.Freq.FracInternal.BilinShiftCont.highPart_measurable`)

**Low-frequency factor at most one.** At nonnegative time, the low-frequency test factor has absolute value at most one. (`Breakdown.Freq.FracInternal.BilinShiftCont.lowPart_bound`)

**High-frequency bound for α ≤ 0.** For α ≤ 0 and s ≥ 0, the high-frequency factor has absolute value at most exp(s). (`Breakdown.Freq.FracInternal.BilinShiftCont.highPart_bound`)

**Split the test multiplier.** The test factor at τ is its low part plus the test factor at s + τ times the high-frequency compensating factor. (`Breakdown.Freq.FracInternal.BilinShiftCont.split_eq`)

**Recover realization at an earlier time.** If the test multiplier at s + τ is realized, it is also realized at positive τ when s is nonnegative. (`Breakdown.Freq.FracInternal.BilinShiftCont.realized_of_shift`)

**Compose heat and test multipliers.** At nonnegative s and positive τ, applying the test multiplier after fractional heat equals the test multiplier at s + τ. (`Breakdown.Freq.FracInternal.BilinShiftCont.phi_heat`)

**Compose physical heat and test fields.** The fractional heat-semigroup interface identifies the test field of a heat-evolved state with the test field at the summed time. (`Breakdown.Freq.FracInternal.BilinShiftCont.phiX_heatX`)

**Fractional bilinear specification.** Fractional bilinear existence gives the specification of the chosen map at positive time. (`Breakdown.Freq.FracInternal.BilinShiftCont.bilinX_spec`)

**Fractional bilinear heat-time shift.** Fractional bilinear existence and the heat-semigroup statement identify heat evolution for a nonnegative duration after a positive-time bilinear output with the bilinear output at the sum of the two times. (`Breakdown.Freq.fracBilinShift`)

**Continuous fractional bilinear evolution.** The stated fractional existence, bounds, test-field and heat interfaces imply continuity of the bilinear evolution for α > 1. (`Breakdown.Freq.fracBilinContinuous`)

### Breakdown.Frac.RBilinTestCompact

This file proves compactness of the fractional bilinear test operator by splitting its Fourier output into a bounded-frequency part and a small tail.

**Nonnegative test factor.** The fractional test factor is nonnegative. (`Breakdown.FracInternal.fracPhiFactor_nonneg`)

**Small high-frequency test factor.** For α > 1, τ > 0 and frequencies beyond R ≥ 1, the test factor is at most 1/(τR). (`Breakdown.FracInternal.fracPhiFactor_tail`)

**Uniform fractional test-factor bound.** For α > 1 and τ > 0, the test factor is at most 2π + 1/τ. (`Breakdown.FracInternal.fracPhiFactor_le`)

**Continuous fractional test factor.** For α > 1, the test factor is continuous in frequency. (`Breakdown.FracInternal.continuous_fracPhiFactor`)

**Test multiplier on L².** The L² test multiplier is the field operator formed from the scalar fractional test factor. (`Breakdown.FracInternal.fracPhiMul`)

**Bound the test multiplier pointwise.** For α > 1 and τ > 0, the pointwise test operator has norm at most 2π + 1/τ. (`Breakdown.FracInternal.norm_fracPhiFactor_smul_le`)

**Representative of the L² test multiplier.** For α > 1 and positive time, the L² test multiplier acts by its scalar factor almost everywhere. (`Breakdown.FracInternal.fracPhiMul_ae`)

**Pair complexification with a vector.** A real vector complexified in the first slot pairs with the real part of the complex vector in the second slot. (`Breakdown.FracInternal.inner_complexifyVec_real`)

**Pair complexification with an L² class.** Complexifying a real L² field moves the real-part operation to the other field in the real inner product. (`Breakdown.FracInternal.inner_complexify_real`)

**Real isometry of the Fourier transform.** The L² Fourier transform is packaged as a real linear isometric equivalence. (`Breakdown.FracInternal.transformRealIsometry`)

**Fourier adjoint identity.** Moving the real Fourier transform across the inner product replaces it by the inverse transform. (`Breakdown.FracInternal.inner_transformR`)

**Projected heat and test pairing.** For α > 1 and positive time, the projected fractional heat pairing equals the real-data pairing with the fractional test field. (`Breakdown.FracInternal.fracHeatProject_inner`)

**Choose a specified bilinear map.** The chosen positive-time fractional bilinear map satisfies its specification when such maps exist. (`Breakdown.FracInternal.fracBilinX_spec`)

**Bilinear formula for test fields.** For α > 1, fractional bilinear existence implies the physical test-field formula. (`Breakdown.Freq.fracBilinTestFormula`)

**Extend a cut-off Fourier function.** The extension multiplies bounded continuous data on the frequency ball by the test factor and is zero outside the ball. (`Breakdown.FracInternal.fracExtend`)

**Support of the Fourier extension.** The Fourier extension equals its own indicator restriction to the frequency ball. (`Breakdown.FracInternal.fracExtend_eq`)

**Continuity inside the cutoff ball.** For α > 1, the Fourier extension is continuous on its frequency ball. (`Breakdown.FracInternal.continuousOn_fracExtend`)

**Uniform bound for the extension.** At α > 1 and positive time, the extension norm is bounded by (2π + 1/τ) times the bounded-function norm. (`Breakdown.FracInternal.norm_fracExtend_le`)

**Square-integrable Fourier extension.** For α > 1 and positive time, the cutoff Fourier extension belongs to L². (`Breakdown.FracInternal.memLp_fracExtend`)

**L² class of the Fourier cutoff.** The cutoff L² field is the L²-or-zero class of the extended Fourier function. (`Breakdown.FracInternal.fracCutLp`)

**Representative of the cutoff L² field.** For α > 1 and positive time, the cutoff class agrees almost everywhere with its extension. (`Breakdown.FracInternal.fracCutLp_ae`)

**Lipschitz dependence of the cutoff.** For α > 1 and positive time, forming the cutoff L² field is Lipschitz in the bounded continuous input. (`Breakdown.FracInternal.dist_fracCutLp_le`)

**Bound the discarded Fourier tail.** For compactly supported real L² input, α > 1, positive time and R ≥ 1, the discarded test-multiplier tail has norm at most 1/(τR) times the Fourier L² norm. (`Breakdown.FracInternal.fracTail_le`)

**Totally bounded smoothing image.** For α > 1 and positive time, the test multiplier sends the stated compact-support bounded family to a totally bounded L² set. (`Breakdown.FracInternal.fracTotallyBounded_image`)

**Compact fractional bilinear map.** For α greater than one, the fractional test formula and bilinear bound make the bilinear operator compact in its second input whenever its first input lies in the test span and time is positive. (`Breakdown.Freq.fracBilinCompact`)

### Breakdown.Frac.RDecayEmbed

This file checks that decay-field scaling agrees with fractional dilation after embedding in the energy space.

**Derivative of an amplitude-scaled field.** A differentiable field scaled in amplitude by a and in position by s has derivative as times the original derivative at sy. (`Breakdown.FracInternal.hasFDerivAt_ampScaled`)

**Compare radial weights under scaling.** For positive s and nonnegative r, 1 + r is at most (1 + s⁻¹)(1 + sr). (`Breakdown.FracInternal.one_add_le`)

**Common bound after two scalings.** The stated positive amplitudes and scales give one displayed constant controlling both the rescaled inverse-linear and inverse-quadratic bounds. (`Breakdown.FracInternal.ampScaled_bound`)

**Positive scaling preserves decay fields.** Positive amplitude and spatial scaling preserve the decay-field conditions. (`Breakdown.FracInternal.isDecayField_ampScaled`)

**Scale a coordinate partial field.** A coordinate partial of an amplitude-scaled decay field is as times the original partial at the scaled point. (`Breakdown.FracInternal.partialField_ampScaled`)

**Scale the complexified partial class.** For positive amplitude and scale, the complexified L² partial class transforms by the displayed as factor and physical scaling operator. (`Breakdown.FracInternal.complexify_ampScaled`)

**Scale the Fourier gradient component.** For positive amplitude and scale, the gradient Fourier component acquires the factor as⁻² and inverse-frequency scaling. (`Breakdown.FracInternal.gradHat_ampScaled`)

**Scale the full gradient representative.** For positive amplitude and scale, the full gradient representative acquires the factor as⁻² and inverse-frequency scaling. (`Breakdown.FracInternal.ofGrad_ampScaled`)

**Dilation as ordinary Fourier pullback.** At positive μ, fractional L² dilation equals μ^(1 − 3/(2α)) times the pullback f(ξ) ↦ f(cξ), where c = μ^(−1/(2α)). (`Breakdown.FracInternal.fracDilL2_eq`)

**Embed fractional scaling in the gradient.** The gradient representation of a positive fractional scaling equals fractional L² dilation of the original gradient representation. (`Breakdown.FracInternal.ofGrad_scaleField`)

**Fractional scaling of decay fields.** For positive α and positive scale, fractional scaling preserves the decay-field condition. (`Breakdown.Freq.decayFieldScale`)

**Dilation commutes with the embedding.** For positive α, fractional dilation algebra and preservation of decay under scaling make positive dilation of an embedded decay field equal embedding its fractionally scaled physical field. (`Breakdown.Freq.fracEmbedDilate`)

### Breakdown.Frac.RDilation

This file proves norm, algebra and continuity laws for fractional dilation on the energy space, using a frequency pullback with an extra amplitude factor.

**Pointwise fractional L² dilation.** At positive μ, fractional L² dilation is represented almost everywhere by μ¹⁻³ᐟ²ᵅ times the original field at the inverse fractional frequency scale. (`Breakdown.Freq.FracInternal.Dilation.fracDilL2_ae`)

**Dilation as scaled Fourier pullback.** For nonzero α and positive μ, fractional L² dilation equals μ^(1 − 1/α) times the operator f(ξ) ↦ c f(cξ), where c = μ^(−1/(2α)). (`Breakdown.Freq.FracInternal.Dilation.fracDilL2_eq`)

**Norm of fractional dilation.** For nonzero α and positive μ, the L² norm scales by μ raised to the dilation exponent. (`Breakdown.Freq.FracInternal.Dilation.norm_fracDilL2`)

**Fractional heat factor bounded by one.** The absolute fractional heat factor is at most one for every parameter value. (`Breakdown.Freq.FracInternal.Dilation.fracHeatFactor_le_one`)

**Pointwise fractional heat evolution.** For positive α, fractional L² heat is represented almost everywhere by multiplying by the fractional heat factor. (`Breakdown.Freq.FracInternal.Dilation.fracHeatL2_ae`)

**Scaling preserves admissible symbols.** An operator with the stated real-amplitude nonzero-frequency scaling formula preserves the admissible symbol subspace. (`Breakdown.Freq.FracInternal.Dilation.mem_sig_of_ae`)

**Underlying energy-space dilation.** At positive μ, the underlying L² class of the fractional energy-space dilation is its fractional L² dilation. (`Breakdown.Freq.FracInternal.Dilation.fracDilX_coe`)

**Heat factor and fractional dilation.** For positive α and μ and nonnegative t, the heat factor at time μt and inverse-scaled frequency equals its original value at t. (`Breakdown.Freq.FracInternal.Dilation.fracHeatFactor_dil`)

**Fractional dilation algebra.** For positive α, the heat-semigroup statement gives fractional dilation its norm-scaling formula, identity at scale one, multiplicative composition, compatibility with rescaled heat time and agreement with its L² realization. (`Breakdown.Freq.fracDilationAlgebra`)

**Continuity of fractional dilation.** For positive α, the dilation algebra implies continuity of fractional dilation. (`Breakdown.Freq.fracDilationContinuous`)

### Breakdown.Frac.RExports

This file exports the established realization interfaces used to assemble the fractional mild framework.

**Fractional dilation algebra.** For α greater than one, fractional dilation satisfies its norm-scaling formula, identity at scale one, multiplicative composition, compatibility with rescaled heat time and agreement with its L² realization. (`Breakdown.Freq.fracDilationAlgebra_holds`)

**Test-field bounds and velocity.** For α greater than one, the fractional test field has L² and L⁶ bounds proportional to positive time to the powers −1/(2α) and −1/α times the input norm, and equals almost everywhere the velocity of the negative Laplacian of the heat-evolved input. (`Breakdown.Freq.fracPhi_holds`)

**Fractional bilinear existence and bound.** For α > 1, the fractional bilinear map exists and satisfies its norm bound. (`Breakdown.Freq.fracBilin_holds`)

**Fractional velocity dilation.** For α greater than one and positive scale, the velocity representative of a fractionally dilated energy-space state equals the fractionally scaled original representative almost everywhere. (`Breakdown.Freq.fracVelocityDilate_holds`)

**Fractional framework and symmetries.** For α greater than one, the fractional heat, bilinear and dilation operators form a scaled mild framework, and every matching framework commutes with all spatial orthogonal transformations. (`Breakdown.Freq.fracFramework_holds`)

**Fractional H¹ bilinear formula.** For α greater than one and positive time, the fractional bilinear map applied twice to the embedding of an H¹ field with bounded value and gradient equals minus the solenoidal fractional heat evolution of its advection field. (`Breakdown.Freq.fracBilinH1_holds`)

### Breakdown.Frac.RFrame

This file assembles heat, dilation and bilinear evolution into the scaled mild framework used for the separate fractional blow-up route.

**Symmetric fractional bilinear evolution.** Exchanging the two inputs of fractional bilinear evolution leaves its value unchanged. (`Breakdown.Freq.fracBilinX_symm`)

**Small-time bilinear operator bound.** For α > 1 and 0 < τ ≤ 1, the fractional bilinear bound implies the displayed ordinary three-quarter-power operator estimate. (`Breakdown.Freq.fracBilinX_opNorm_le`)

**Construct the scaled mild framework.** The stated heat, dilation, bilinear continuity, shift, scaling and compactness interfaces define a scaled mild framework with the fractional dilation exponent. (`Breakdown.Freq.fracFrameOf`)

**Assemble the fractional framework.** For α > 1, the listed analytic and rotation interfaces give both the fractional framework specification and its symmetry commutation interface. (`Breakdown.Freq.fracFramework_of`)

### Breakdown.Frac.RHeat

This file proves the fractional heat-semigroup properties on L² and the admissible energy-space subspace.

**Positive fractional heat factor.** The fractional heat factor is strictly positive. (`Breakdown.FracInternal.RHeat.factor_pos`)

**Fractional heat factor at most one.** The fractional heat factor is at most one. (`Breakdown.FracInternal.RHeat.factor_le_one`)

**Measurable fractional heat factor.** The fractional heat factor is measurable in frequency. (`Breakdown.FracInternal.RHeat.measurable_factor`)

**Continuous heat factor in time.** At fixed frequency, the fractional heat factor is continuous in time. (`Breakdown.FracInternal.RHeat.continuous_factor_time`)

**Multiply fractional heat times.** At nonnegative s and t, the heat factor at s + t is the product of the two heat factors. (`Breakdown.FracInternal.RHeat.factor_add`)

**Even fractional heat factor.** The fractional heat factor is unchanged by negating frequency. (`Breakdown.FracInternal.RHeat.factor_neg`)

**Realization of fractional heat.** Fractional L² heat is realized by its scalar frequency multiplier. (`Breakdown.FracInternal.RHeat.realized`)

**Pointwise fractional heat multiplier.** Fractional heat acts on an L² representative by its frequency factor almost everywhere. (`Breakdown.FracInternal.RHeat.op_ae`)

**Heat commutes with invariant multipliers.** A quasi-measure-preserving frequency map that preserves the heat factor makes the stated field operator commute with fractional heat. (`Breakdown.FracInternal.RHeat.op_comm`)

**Reflection preserves null sets.** Frequency negation is quasi-measure-preserving for volume. (`Breakdown.FracInternal.RHeat.qmp_neg`)

**Heat preserves admissible symbols.** Fractional heat preserves the admissible symbol subspace. (`Breakdown.FracInternal.RHeat.op_mem`)

**Underlying L² heat action.** The underlying L² class of fractional heat on X is fractional L² heat applied to the state. (`Breakdown.FracInternal.RHeat.opX_coe`)

**Continuous L² heat evolution.** For each L² input, fractional heat evolution is continuous in time. (`Breakdown.FracInternal.RHeat.op_continuous`)

**Fractional heat semigroup.** For every α, fractional heat is a self-adjoint contraction semigroup on the energy space for nonnegative times, is continuous in nonnegative time on each input, equals the identity at zero and agrees with its L² realization. (`Breakdown.Freq.fracHeatSemigroup`)

### Breakdown.Frac.RMildOfWeak

This file converts the fractional weak equation into the mild integral equation by testing against heat-evolved energy-space states.

**Extend the weak fractional identity.** For α ≥ 1 and the stated density and embedding interfaces, the weak equation extends to the displayed energy-space test identity for a compatible Laplacian and fractional derivative pair. (`Breakdown.FracInternal.MildWeak.frac_weak_ext`)

**Differentiate the weak pairing.** Under the same interfaces, the weak energy-space pairing has the displayed negative dissipation-plus-advection derivative in the interval interior. (`Breakdown.FracInternal.MildWeak.frac_weak_deriv`)

**Continuous fractional bilinear curve.** The bilinear bound and continuity interfaces make the bilinear term continuous along continuous state and strictly positive time curves. (`Breakdown.FracInternal.MildWeak.frac_bilin_cont`)

**Integrable fractional bilinear time term.** For α ≥ 1, the stated bilinear interfaces make the time term interval integrable along a continuous state curve. (`Breakdown.FracInternal.MildWeak.frac_bilin_int`)

**Recover the fractional bilinear form.** Fractional bilinear existence identifies the inner product of the chosen positive-time map with its defining form. (`Breakdown.FracInternal.MildWeak.inner_fracBilinX`)

**Heat-regularized weak integral identity.** The listed weak, density, heat and bilinear interfaces yield the displayed ε-regularized Duhamel pairing identity for positive ε. (`Breakdown.FracInternal.MildWeak.frac_integral_identity`)

**Fractional weak solutions are mild.** For 1 < α < 3/2, the weak energy-space equation, nice-field graph density and power embedding, heat-semigroup, bilinear existence, bound, continuity and shift, test-field velocity and bounds, and nice-field properties turn every weak solution on a positive-length interval into a mild energy-space solution. (`Breakdown.Freq.fracMildOfWeak_of`)

### Breakdown.Frac.RMildOfWeakHeat

This file supplies heat smoothing and time differentiation needed to turn the fractional weak equation into a mild equation.

**Fractional dissipation multiplier.** The fractional dissipation multiplier is (2π‖ξ‖)^(2α). (`Breakdown.FracInternal.MildWeak.powNorm`)

**Nonnegative dissipation multiplier.** The fractional dissipation multiplier is nonnegative at every frequency. (`Breakdown.FracInternal.MildWeak.powNorm_nonneg`)

**Continuous dissipation multiplier.** For α > 0, the fractional dissipation multiplier is continuous in frequency. (`Breakdown.FracInternal.MildWeak.continuous_powNorm`)

**Even dissipation multiplier.** Negating frequency leaves the fractional dissipation multiplier unchanged. (`Breakdown.FracInternal.MildWeak.powNorm_neg`)

**Control the ordinary Laplacian weight.** For α ≥ 1, the ordinary squared-frequency weight is at most one plus the fractional dissipation multiplier. (`Breakdown.FracInternal.MildWeak.sqFactor_le_powNorm`)

**Positive shifted dissipation weight.** One plus the fractional dissipation multiplier is strictly positive. (`Breakdown.FracInternal.MildWeak.one_add_powNorm_pos`)

**Compare two dissipation weights.** The comparison factor divides the ordinary squared-frequency weight by one plus the fractional dissipation multiplier. (`Breakdown.FracInternal.MildWeak.cmpFactor`)

**Continuous squared-frequency weight.** The ordinary squared-frequency weight is continuous in frequency. (`Breakdown.FracInternal.MildWeak.continuous_sqFactor`)

**Continuous comparison factor.** For α > 0, the comparison factor between the two dissipation weights is continuous. (`Breakdown.FracInternal.MildWeak.continuous_cmpFactor`)

**Bound the comparison factor.** For α ≥ 1, the absolute value of the comparison factor is at most one. (`Breakdown.FracInternal.MildWeak.abs_cmpFactor_le`)

**Laplacian controlled by fractional power.** For α ≥ 1, compatible ordinary and fractional derivative states satisfy ‖d‖ ≤ ‖c‖ + ‖e‖. (`Breakdown.FracInternal.MildWeak.sq_norm_le`)

**Subtract fractional derivative pairs.** Subtracting two compatible fractional derivative pairs gives a compatible fractional derivative pair. (`Breakdown.FracInternal.MildWeak.isFracOf_sub`)

**Velocity of the second derivative.** The nice-field interface identifies the velocity of the embedded negative second-order operator on a nice field with that field's negative second-order image almost everywhere. (`Breakdown.FracInternal.MildWeak.velocity_second_nice`)

**Fractional derivative after heat.** This continuous linear operator on X restricts the product of the fractional dissipation and heat multipliers. (`Breakdown.FracInternal.MildWeak.aHeatX`)

**Ordinary Laplacian after heat.** This continuous linear operator on X restricts the product of the squared-frequency and fractional heat multipliers. (`Breakdown.FracInternal.MildWeak.sqHeatX`)

**Expand the fractional heat factor.** The fractional heat factor equals exp(−max(τ,0) times the dissipation multiplier). (`Breakdown.FracInternal.MildWeak.heatF_eq`)

**Heat factor at positive time.** At positive time τ, the fractional heat factor equals exp(−τ times the dissipation multiplier). (`Breakdown.FracInternal.MildWeak.heatF_pos_eq`)

**Continuous fractional heat multiplier.** For α > 0 and any time, the fractional heat factor is continuous in frequency. (`Breakdown.FracInternal.MildWeak.continuous_heatF`)

**Heat multiplier has size at most one.** The absolute value of the fractional heat multiplier is at most one. (`Breakdown.FracInternal.MildWeak.heatF_le`)

**Nonnegative fractional heat multiplier.** The fractional heat multiplier is nonnegative at every frequency. (`Breakdown.FracInternal.MildWeak.heatF_nonneg`)

**Even fractional heat multiplier.** Negating frequency leaves the fractional heat multiplier unchanged. (`Breakdown.FracInternal.MildWeak.heatF_neg`)

**Bound dissipation after heat.** At positive time τ, the dissipation-times-heat multiplier has absolute value at most τ⁻¹. (`Breakdown.FracInternal.MildWeak.aHeat_le`)

**Bound the Laplacian after heat.** For α ≥ 1 and positive τ, the squared-frequency-times-heat multiplier has absolute value at most 1 + τ⁻¹. (`Breakdown.FracInternal.MildWeak.sqHeat_le`)

**Even dissipation after heat.** Negating frequency preserves the product of the fractional dissipation and heat multipliers. (`Breakdown.FracInternal.MildWeak.aHeat_neg`)

**Even Laplacian after heat.** Negating frequency preserves the product of the squared-frequency and fractional heat multipliers. (`Breakdown.FracInternal.MildWeak.sqHeat_neg`)

**Continuous dissipation after heat.** For α > 0, the product of the fractional dissipation and heat multipliers is continuous in frequency. (`Breakdown.FracInternal.MildWeak.continuous_aHeat`)

**Continuous Laplacian after heat.** For α > 0, the product of the squared-frequency and fractional heat multipliers is continuous in frequency. (`Breakdown.FracInternal.MildWeak.continuous_sqHeat`)

**Underlying fractional heat derivative.** For α > 0 and positive time, the underlying L² class of the heat derivative operator equals its stated Fourier multiplier action. (`Breakdown.FracInternal.MildWeak.aHeatX_coe`)

**Underlying Laplacian of heat.** For α ≥ 1 and positive time, the underlying L² class of the Laplacian-after-heat operator equals its stated Fourier multiplier action. (`Breakdown.FracInternal.MildWeak.sqHeatX_coe`)

**Heat has a fractional derivative.** For α > 0, the heat-semigroup interface gives the fractional derivative of a positive-time heat state as the dissipation-after-heat operator. (`Breakdown.FracInternal.MildWeak.isFracOf_heat`)

**Heat has an ordinary Laplacian.** For α ≥ 1, the heat-semigroup interface gives the ordinary second-order image of a positive-time heat state as the Laplacian-after-heat operator. (`Breakdown.FracInternal.MildWeak.sq_heat_rel`)

**Quadratic heat expansion error.** For α > 0 and |r − τ| ≤ τ/2 with τ > 0, the heat-semigroup interface bounds the first-order expansion error by 16τ⁻²(r − τ)²‖ψ‖. (`Breakdown.FracInternal.MildWeak.frac_heat_expansion_norm`)

**Differentiate fractional heat in time.** For α > 0 and positive time, the heat-semigroup interface identifies the time derivative with minus the dissipation-after-heat operator. (`Breakdown.FracInternal.MildWeak.frac_heat_hasDerivAt`)

### Breakdown.Frac.RPhi

This file establishes scalar multiplier estimates used in the fractional test-field bounds and velocity identity.

**Bound a power by one plus its base.** For nonnegative s and 0 ≤ g ≤ 1, s^g is at most 1 + s. (`Breakdown.FracInternal.PhiBound.rpow_le_one_add`)

**Power times exponential is bounded.** For nonnegative s and 0 ≤ g ≤ 1, s^g exp(−s) is at most one. (`Breakdown.FracInternal.PhiBound.rpow_mul_exp_neg_le_one`)

**Scaled power times exponential.** For y ≥ 0, τ > 0 and 0 ≤ g ≤ 1, y^g exp(−τy) is at most τ^(−g). (`Breakdown.FracInternal.PhiBound.rpow_mul_exp_le`)

**Continuous frequency power.** For α ≥ 0, the function ξ ↦ (2π‖ξ‖)^(2α) is continuous. (`Breakdown.FracInternal.PhiBound.continuous_rpowNorm`)

**Nonnegative test-field multiplier.** The fractional test-field multiplier is nonnegative. (`Breakdown.FracInternal.PhiBound.fracPhiFactor_nonneg`)

**Bound the test-field multiplier.** For α > 1 and τ > 0, the absolute value of the fractional test-field multiplier is at most τ^(−1/(2α)). (`Breakdown.FracInternal.PhiBound.fracPhiFactor_le`)

**Nonnegative Laplacian heat multiplier.** The product of the squared-frequency and fractional heat multipliers is nonnegative. (`Breakdown.FracInternal.PhiBound.sqFracHeat_nonneg`)

**Fractional Laplacian heat estimate.** For α > 1 and τ > 0, the absolute value of the squared-frequency-times-heat multiplier is at most τ^(−1/α). (`Breakdown.FracInternal.PhiBound.sqFracHeat_le`)

**Fractional heat multiplier bound.** The absolute value of the fractional heat multiplier is at most one. (`Breakdown.FracInternal.PhiBound.fracHeatFactor_le`)

**Continuous test-field multiplier.** For α ≥ 0, the fractional test-field multiplier is continuous in frequency at every time. (`Breakdown.FracInternal.PhiBound.continuous_fracPhiFactor`)

**Continuous fractional heat factor.** For α ≥ 0, the fractional heat multiplier is continuous in frequency at every time. (`Breakdown.FracInternal.PhiBound.continuous_fracHeatFactor`)

**Continuous squared-frequency heat.** For α ≥ 0, the squared-frequency-times-heat multiplier is continuous in frequency at every time. (`Breakdown.FracInternal.PhiBound.continuous_sqFracHeat`)

**Test-field bounds and velocity identity.** For α greater than one, the heat-semigroup statement bounds the fractional test field in L² and L⁶ by time to the powers −1/(2α) and −1/α times the input norm, and identifies it almost everywhere with the velocity of the negative Laplacian of the heat-evolved input. (`Breakdown.Freq.fracPhiBoundsVelocity`)

### Breakdown.Frac.RRotation

This file proves rotation commutation for fractional heat and dilation and assembles their rotation interface.

**Rotation commutes with fractional heat.** Orthogonal spatial rotation commutes with fractional L² heat at every time and exponent. (`Breakdown.Freq.FracInternal.Rotation.rotL2_fracHeatL2`)

**Rotation commutes with dilation.** At a positive dilation scale, orthogonal rotation commutes with fractional L² dilation. (`Breakdown.Freq.FracInternal.Rotation.rotL2_fracDilL2`)

**Assemble fractional rotation identities.** For α > 0, the heat-semigroup and dilation interfaces imply the fractional rotation algebra. (`Breakdown.Freq.fracRotationAlgebra`)

### Breakdown.Frac.RVelocityDilate

This file identifies the velocity of a fractional dilation by scaling test fields and using the embedding identity.

**Scaling preserves test fields.** Multiplying a test field by any amplitude and precomposing with a nonzero spatial scale gives another test field. (`Breakdown.Freq.FracInternal.VelocityScale.test_scale`)

**Velocity commutes with dilation.** For positive α, fractional dilation algebra, embedding-dilation compatibility and preservation of decay under scaling identify the velocity of every positively dilated energy-space state almost everywhere with the fractionally scaled original velocity. (`Breakdown.Freq.fracVelocityDilate`)

### Breakdown.Frac.RWeakInX

This file transfers the fractional weak equation to the energy-space formulation through the nice-field pairing identities.

**Obtain the weak energy-space equation.** For 1 < α < 3/2, the nice-field, integration-by-parts and advection-trilinearity interfaces imply the fractional weak equation in X. (`Breakdown.Freq.fracWeakInX_of`)

### Breakdown.Frac.RegPowerApriori

This file derives the fractional regularity route’s a priori bound from dissipation and Sobolev mild evolution.

**Fourth power cancels quarter power.** Raising the one-quarter real power of an extended nonnegative real number to the fourth power recovers the number. (`_private.Breakdown.Frac.RegPowerApriori.0.Breakdown.SmoothFlow.PowerInternal.rpow_quarter_pow_four`)

**Square cancels half power.** Squaring the one-half real power of an extended nonnegative real number recovers the number. (`_private.Breakdown.Frac.RegPowerApriori.0.Breakdown.SmoothFlow.PowerInternal.rpow_half_sq`)

**Compare two singular time kernels.** For α > 1 and 0 < r ≤ T, the fractional time kernel is bounded by max(T,1)^(1/2 − 1/(2α)) times r^(−1/2). (`_private.Breakdown.Frac.RegPowerApriori.0.Breakdown.SmoothFlow.PowerInternal.kernel_le`)

**Derive the fractional a priori bound.** For α greater than one, the dissipation and Sobolev mild-equation statements bound every Sobolev norm of order at least three along a solenoidal mild symbol curve from its initial bound, a uniform first-order homogeneous bound and a fixed upper time limit. (`Breakdown.SmoothFlow.powerApriori_of`)

### Breakdown.Frac.RegPowerBilinIntegral

This file commutes fractional bilinear evolution with time integration using its physical representation and heat realization.

**Move frequency weight outside integral.** The interval integral of the fractional test-field multiplier times a vector curve equals 2π‖ξ‖ times the interval integral with the power-heat symbol. (`_private.Breakdown.Frac.RegPowerBilinIntegral.0.Breakdown.SmoothFlow.integral_fracPhiFactor_smul`)

**Joint continuity of test-field factor.** For α > 1, the fractional test-field multiplier at time t − s is jointly continuous in s and frequency. (`_private.Breakdown.Frac.RegPowerBilinIntegral.0.Breakdown.SmoothFlow.continuous_fracPhiFactor_joint`)

**Integrate the fractional bilinear term.** For α greater than one, the physical bilinear formula, bilinear continuity and energy-space heat statements give interval integrability of the nonlinear term for an all-orders Sobolev mild solenoidal symbol curve and identify its integral almost everywhere with the corresponding heat-weighted Fourier nonlinear integral. (`Breakdown.SmoothFlow.powerBilinIntegral_of`)

### Breakdown.Frac.RegPowerBilinPhys

This file obtains the fractional bilinear formula in physical space and the continuity and time-singularity bounds needed for mild evolution.

**Physical fractional bilinear formula.** For α greater than one, the fractional H¹ bilinear formula and solenoidal-symbol statement identify the positive-time bilinear output of a solenoidal symbol with finite Sobolev energies of every order almost everywhere as the fractional heat factor times its Fourier nonlinearity. (`Breakdown.SmoothFlow.powerBilinPhys_of`)

**Nonnegative fractional test multiplier.** The fractional test-field multiplier is nonnegative at every time and frequency. (`_private.Breakdown.Frac.RegPowerBilinPhys.0.Breakdown.SmoothFlow.phi_nonneg`)

**Exponential dominates a nonnegative base.** For α > 1 and y ≥ 0, y is at most exp(y^(2α)). (`_private.Breakdown.Frac.RegPowerBilinPhys.0.Breakdown.SmoothFlow.le_exp_rpow`)

**Fractional test multiplier estimate.** For α > 1 and positive τ, the fractional test-field multiplier is at most τ^(−1/(2α)). (`_private.Breakdown.Frac.RegPowerBilinPhys.0.Breakdown.SmoothFlow.phi_le_rpow`)

**Gaussian bound beyond a positive time.** For α > 1 and 0 < τ₀ ≤ τ, the square of the fractional test-field multiplier is bounded by exp(2τ₀)τ₀⁻¹ exp(−4π²τ₀‖ξ‖²). (`_private.Breakdown.Frac.RegPowerBilinPhys.0.Breakdown.SmoothFlow.phi_sq_le`)

**Integrable Gaussian on space.** For a > 0, the function ξ ↦ exp(−a‖ξ‖²) is integrable over space. (`_private.Breakdown.Frac.RegPowerBilinPhys.0.Breakdown.SmoothFlow.integrable_exp_neg_sq`)

**Sobolev weight increases with order.** If m ≤ n, the squared order-m Sobolev norm of a symbol is at most its squared order-n norm. (`_private.Breakdown.Frac.RegPowerBilinPhys.0.Breakdown.SmoothFlow.hsNormSq_le_of_le`)

**L² norm as zero-order Sobolev norm.** The extended L² norm of a symbol equals the one-half power of its squared zero-order Sobolev norm. (`_private.Breakdown.Frac.RegPowerBilinPhys.0.Breakdown.SmoothFlow.eLpNorm_two_eq_hs`)

**Uniform pointwise nonlinear bound.** A third-order Sobolev curve on [0,T] has a nonnegative uniform bound for its nonlinear symbol at every time and frequency. (`_private.Breakdown.Frac.RegPowerBilinPhys.0.Breakdown.SmoothFlow.nonlin_pointwise_bound`)

**Uniform L² nonlinear bound.** A third-order Sobolev curve on [0,T] has a finite uniform extended L² bound for its nonlinear symbol. (`_private.Breakdown.Frac.RegPowerBilinPhys.0.Breakdown.SmoothFlow.nonlin_l2_bound`)

**Bound a squared weighted sum.** If a² and b² are at most D, then (aM + bM)² is at most 4M²D. (`_private.Breakdown.Frac.RegPowerBilinPhys.0.Breakdown.SmoothFlow.sq_sum_le`)

**Continuous fractional bilinear curve.** For α > 1 and a solenoidal curve of every Sobolev order, the physical bilinear formula implies continuity of the displayed backward-time bilinear term on [0,t). (`_private.Breakdown.Frac.RegPowerBilinPhys.0.Breakdown.SmoothFlow.continuousOn_power_bilin`)

**Uniform fractional bilinear time bound.** Under the physical bilinear formula, a solenoidal curve of every Sobolev order has a uniform bilinear norm bound Cτ^(−1/(2α)) for positive τ and α > 1. (`_private.Breakdown.Frac.RegPowerBilinPhys.0.Breakdown.SmoothFlow.norm_power_bilin_le`)

**Derive fractional bilinear continuity.** For α greater than one, the physical bilinear formula and solenoidal-symbol statement give continuity of the bilinear time integrand before its upper endpoint and a uniform time to the power −1/(2α) bound along every all-orders Sobolev solenoidal curve. (`Breakdown.SmoothFlow.powerBilinContinuous_of`)

### Breakdown.Frac.RegPowerConcat

On the fractional whole space regularity route, this file joins symbol solutions on adjacent time intervals so that local constructions can continue forward.

**Continuous heat multiplier in time.** The fractional heat multiplier is continuous as the starting time varies. (`_private.Breakdown.Frac.RegPowerConcat.0.Breakdown.SmoothFlow.PowerInternal.continuous_powerHeatFactor`)

**Compose two heat multipliers.** Multiplying the two heat factors over adjacent time increments gives the heat factor over their sum. (`_private.Breakdown.Frac.RegPowerConcat.0.Breakdown.SmoothFlow.PowerInternal.powerHeatSymbol_mul`)

**Join mild symbol solutions.** Two mild symbol solutions with matching endpoint values and the stated Sobolev continuity join to a mild solution on the combined interval. (`_private.Breakdown.Frac.RegPowerConcat.0.Breakdown.SmoothFlow.PowerInternal.isPowerMildSymbol_concat`)

**Restrict a mild symbol solution.** Restricting the final time preserves the mild symbol equation. (`_private.Breakdown.Frac.RegPowerConcat.0.Breakdown.SmoothFlow.PowerInternal.isPowerMildSymbol_restrict`)

**Concatenate fractional mild flows.** For α > 1, two H³ fractional mild symbol curves that agree at the common endpoint concatenate to a mild symbol curve, and restricting its right endpoint preserves the mild identity. (`Breakdown.SmoothFlow.powerConcat`)

### Breakdown.Frac.RegPowerDissipation

This file supplies the Fourier dissipation estimates used to turn the fractional symbol equation into energy and continuation bounds on the whole space route.

**Weighted dissipation integral.** The dissipation quantity integrates the symbol square against the gradient weight and the fractional heat rate. (`_private.Breakdown.Frac.RegPowerDissipation.0.Breakdown.SmoothFlow.dissipSq`)

**Control the quartic frequency weight.** For nonnegative frequency and α at least one, the fourth power is bounded by the gradient and dissipation weights. (`_private.Breakdown.Frac.RegPowerDissipation.0.Breakdown.SmoothFlow.quartic_le_sum`)

**Dissipation below the H³ weight.** For α between zero and two, the dissipation weight is bounded by a fixed multiple of the H³ weight. (`_private.Breakdown.Frac.RegPowerDissipation.0.Breakdown.SmoothFlow.weight_le_hsWeight`)

**Absorb a three-quarter power.** A nonnegative coefficient times the three-quarter power of an extended nonnegative number is bounded by that number plus the coefficient's fourth power. (`_private.Breakdown.Frac.RegPowerDissipation.0.Breakdown.SmoothFlow.ofReal_mul_rpow_three_quarters_le_self`)

**Derive the dissipation estimate.** For 1 < α < 3/2, the energy inequality and joint measurability hypotheses give a uniform time integral bound on the homogeneous H² norm squared of every solenoidal Hᵐ mild curve with m ≥ 3 and a uniform homogeneous H¹ bound, over intervals of bounded length. (`Breakdown.SmoothFlow.powerDissipation_of`)

### Breakdown.Frac.RegPowerEnergy

This file supplies the fractional symbol energy inequality needed by the whole space smooth solution construction.

**Derive the energy inequality.** For α > 1, the pointwise derivative hypothesis bounds twice the frequencywise time integral of fractional dissipation weighted by the squared frequency norm by the initial weighted energy plus twice the corresponding velocity–nonlinearity pairing bound for every H¹ mild symbol curve on [0,T] with T > 0. (`Breakdown.SmoothFlow.powerEnergyInequality_of`)

### Breakdown.Frac.RegPowerFlow

This file assembles the regular symbol flow and its continuation properties, connecting the local Fourier construction to the whole space fractional solution route.

**A flow on the initial instant.** A measurable solenoidal symbol with finite Sobolev norm gives a constant flow on the interval consisting of its initial instant. (`Breakdown.SmoothFlow.PowerInternal.flow_const`)

**Propagate all Sobolev orders.** The persistence interface upgrades an H³ symbol flow with smooth initial data to a curve at every Sobolev order. (`Breakdown.SmoothFlow.PowerInternal.flow_regular`)

**Extend a flow using its H¹ bound.** Local existence, concatenation and a priori estimates extend the symbol flow to the target time when every earlier flow obeys the prescribed homogeneous H¹ bound. (`Breakdown.SmoothFlow.PowerInternal.flow_exists`)

**Assemble the symbol flow.** For α > 1, local existence, concatenation, persistence, and a priori estimates propagate every finite initial Sobolev order along an H³ symbol flow and extend measurable solenoidal H³ data to any positive time T whenever all shorter flows have a common homogeneous H¹ bound. (`Breakdown.SmoothFlow.powerFlow_of`)

### Breakdown.Frac.RegPowerGlue

This file identifies overlapping regular and abstract mild trajectories so that the whole space fractional construction can extend a trajectory consistently.

**Identify the physical mild flow.** The symbol-flow and identification interfaces make the reconstructed velocity agree in X with the prescribed mild trajectory at every time in the interval. (`_private.Breakdown.Frac.RegPowerGlue.0.Breakdown.embedX_physField_eq_of_powerFlow`)

**Recover fractional mild regularity.** For 1 < α < 3/2, the symbol flow, identification, physical solution, and bilinear bound hypotheses turn a mild trajectory in the matching fractional framework, starting from a test field on [0,T] with T > 0, into a smooth fractional velocity–pressure solution with that datum, bounded energy and gradient, and the same velocity almost everywhere at every time. (`Breakdown.fracMildRegular_of`)

### Breakdown.Frac.RegPowerHeatBasic

This file establishes the elementary fractional heat multiplier and time integral bounds used by the symbol mild equation.

**Integrate exponential decay.** For a positive rate, the exponential integral equals the difference of its endpoint values divided by that rate. (`_private.Breakdown.Frac.RegPowerHeatBasic.0.Breakdown.SmoothFlow.PowerInternal.integral_exp_neg_mul_le`)

**Bound the short-time heat rate.** For positive frequency and time and α greater than one, the truncated heat-rate expression is bounded by a constant times the stated fractional power of time. (`_private.Breakdown.Frac.RegPowerHeatBasic.0.Breakdown.SmoothFlow.PowerInternal.rate_min_bound`)

**Basic fractional heat estimate.** For α > 1, the fractional heat symbol is nonnegative and continuous in time, and its integral over a nonnegative time interval, multiplied by one plus the frequency norm, is bounded by the interval length plus C times that length raised to 1 − 1/(2α). (`Breakdown.SmoothFlow.powerHeatBasic`)

### Breakdown.Frac.RegPowerHeatGain

This file proves the fractional heat smoothing estimate that gains frequency regularity in the whole space symbol construction.

**Absorb a power into an exponential.** A nonnegative number to a positive power is bounded by that power to itself times the exponential of the number. (`Breakdown.SmoothFlow.PowerInternal.gainRpowLeMulExp`)

**Cubic gain from heat decay.** When twice α times q equals three, the heat-damped cubic frequency weight is bounded by q to itself times the negative q-th power of time. (`Breakdown.SmoothFlow.PowerInternal.gainCubeMulExpLe`)

**Fractional heat smoothing gain.** For α > 1 and each upper time bound T, the squared fractional heat symbol multiplied by the squared frequency norm and the square root of one plus that norm squared is bounded by C times τ raised to −3/(2α), uniformly for 0 < τ ≤ T. (`Breakdown.SmoothFlow.powerHeatGain`)

### Breakdown.Frac.RegPowerHeatPart

This file controls measurability, norms, and continuity of the free heat part of a fractional symbol solution.

**Heat multiplier has norm at most one.** At nonnegative elapsed time, the complex heat multiplier has extended norm at most one. (`_private.Breakdown.Frac.RegPowerHeatPart.0.Breakdown.SmoothFlow.powerHeatSymbol_enorm_le_one`)

**Heat evolution contracts each value.** At nonnegative elapsed time, the heat part has extended norm no greater than the initial symbol at each frequency. (`_private.Breakdown.Frac.RegPowerHeatPart.0.Breakdown.SmoothFlow.powerHeatPart_enorm_le`)

**Measurable heat evolution.** A measurable initial symbol gives a measurable heat part at every time. (`_private.Breakdown.Frac.RegPowerHeatPart.0.Breakdown.SmoothFlow.aestronglyMeasurable_powerHeatPart`)

**Heat contracts fractional norms.** At nonnegative elapsed time, the heat part does not increase the fractional Sobolev norm square. (`_private.Breakdown.Frac.RegPowerHeatPart.0.Breakdown.SmoothFlow.fracNormSq_powerHeatPart_le`)

**Heat continuity in Sobolev norm.** A measurable symbol of finite Sobolev norm has heat evolution continuous in that norm along the stated closed time interval. (`_private.Breakdown.Frac.RegPowerHeatPart.0.Breakdown.SmoothFlow.tendsto_hsNormSq_powerHeatPart`)

**Supply the heat-part interface.** For α > 1, free fractional heat preserves almost everywhere strong measurability, contracts every fractional weighted norm at forward times, and is continuous in each finite Sobolev norm on a closed forward time interval. (`Breakdown.SmoothFlow.powerHeatPart_holds`)

### Breakdown.Frac.RegPowerHeatSolenoidal

This file relates the fractional heat evolution of solenoidal symbols to the corresponding whole space state operators.

**Nonnegative projected heat factor.** The fractional projected heat factor is nonnegative. (`Breakdown.SmoothFlow.PowerInternal.HeatProj.powerPhi_nonneg`)

**Projected heat factor bound.** For α greater than one and positive time, the projected heat factor is at most one plus the inverse time. (`Breakdown.SmoothFlow.PowerInternal.HeatProj.powerPhi_le`)

**Continuous projected heat factor.** For α greater than one, the projected heat factor is continuous in frequency. (`Breakdown.SmoothFlow.PowerInternal.HeatProj.powerPhi_continuous`)

**Even projected heat factor.** Negating frequency leaves the projected heat factor unchanged. (`Breakdown.SmoothFlow.PowerInternal.HeatProj.powerPhi_neg`)

**Norm bound for projected heat.** For α greater than one and positive time, the norm of the projected heat factor is at most one plus the inverse time. (`Breakdown.SmoothFlow.PowerInternal.HeatProj.powerPhi_norm_le`)

**Heat evolution on X.** For every α and time t, the fractional heat operator on X is almost everywhere multiplication of the state's Fourier representative by its scalar heat factor. (`Breakdown.SmoothFlow.powerHeatX`)

**Fourier formula for projected heat.** Under the integrability and conjugate-symmetry assumptions, the projected physical heat field has almost everywhere the stated projected Fourier symbol. (`_private.Breakdown.Frac.RegPowerHeatSolenoidal.0.Breakdown.SmoothFlow.coe_powerProj_physField`)

**Supply solenoidal heat evolution.** For α > 1, the source heat factor is continuous, even, and bounded by C(1 + τ inverse) at positive times, and a conjugate symmetric Fourier field in L¹ and L² yields a solenoidal heat state equal almost everywhere to that factor times its Leray projection. (`Breakdown.SmoothFlow.powerSolenoidal`)

### Breakdown.Frac.RegPowerHeatWeight

This file bounds weighted heat integrals, supplying a frequency derivative gain for the fractional Duhamel term.

**Square the heat multiplier.** The square of the heat multiplier is the exponential with twice the fractional dissipation rate. (`_private.Breakdown.Frac.RegPowerHeatWeight.0.Breakdown.SmoothFlow.weightSymbol_sq`)

**Nonnegative heat multiplier.** The fractional heat multiplier is nonnegative for every time and frequency. (`_private.Breakdown.Frac.RegPowerHeatWeight.0.Breakdown.SmoothFlow.weightSymbol_nonneg`)

**Integrate a shifted exponential.** For a nonzero rate, the shifted exponential integral has the stated endpoint formula. (`_private.Breakdown.Frac.RegPowerHeatWeight.0.Breakdown.SmoothFlow.integral_expDecayWeight`)

**Supply the heat-weight estimate.** For α > 1, the time integral of the squared heat symbol multiplied by one plus the frequency norm squared has a uniform bound over all frequencies and forward intervals of length at most one. (`Breakdown.SmoothFlow.powerHeatWeight`)

**Square an extended square root.** Squaring the one-half real power of an extended nonnegative number recovers the number. (`_private.Breakdown.Frac.RegPowerHeatWeight.0.Breakdown.SmoothFlow.rpow_half_sq_weight`)

**Derive the heat-integral estimate.** For α > 1, the weighted heat hypothesis makes convolution of a jointly measurable source bounded in Hⁿ on a forward interval of length at most one gain one Sobolev derivative, with squared Hⁿ⁺¹ norm at most C times the interval length times the source bound. (`Breakdown.SmoothFlow.powerHeatIntegral_of`)

### Breakdown.Frac.RegPowerIdentify

This file identifies regular physical Fourier solutions with the abstract fractional mild trajectory used in the profile to breakdown route.

**Extract the frequency factor.** The time integral with the projected heat factor equals the heat integral multiplied by twice pi times the frequency norm. (`_private.Breakdown.Frac.RegPowerIdentify.0.Breakdown.SmoothFlow.integral_phi_smul_eq`)

**Identify the fractional mild equation.** For 1 < α < 3/2, the bilinear integral and X heat realization hypotheses make the embedded physical field of an all order Sobolev, solenoidal mild symbol curve into a fractional X-valued mild curve on the same positive interval. (`Breakdown.SmoothFlow.powerIdentify_of`)

### Breakdown.Frac.RegPowerLocal

This file constructs the local fractional symbol solution by iteration and packages the resulting existence and solenoidality properties.

**Iterate the fractional mild map.** The iteration starts with the constant initial symbol and repeatedly applies the fractional mild map. (`_private.Breakdown.Frac.RegPowerLocal.0.Breakdown.SmoothFlow.PowerInternal.iter`)

**Sobolev norm ignores a sign.** Negating a symbol leaves its Sobolev norm square unchanged. (`_private.Breakdown.Frac.RegPowerLocal.0.Breakdown.SmoothFlow.PowerInternal.hsNormSq_neg`)

**Symmetry of the Sobolev difference.** The Sobolev norm square of a difference is unchanged when its two arguments are exchanged. (`_private.Breakdown.Frac.RegPowerLocal.0.Breakdown.SmoothFlow.PowerInternal.hsNormSq_sub_comm`)

**Double a nonnegative-real conversion.** Multiplying the nonnegative-real conversion by two agrees with converting twice the real number. (`_private.Breakdown.Frac.RegPowerLocal.0.Breakdown.SmoothFlow.PowerInternal.two_mul_ofReal`)

**Construct the fractional fixed point.** For α > 1, the mild map's basic, norm, and curve hypotheses give every m ≥ 3 and Sobolev size bound a common positive existence time on which each admissible measurable solenoidal datum has an Hᵐ fixed point almost everywhere that retains Fourier conjugate symmetry. (`Breakdown.SmoothFlow.powerFixedPoint_of`)

**Obtain local fractional existence.** For α > 1, the fixed point and basic mild map hypotheses give every m ≥ 3 and Sobolev size bound a common positive time interval on which each measurable solenoidal datum has an Hᵐ fractional mild symbol solution with the prescribed initial value and solenoidality at every time. (`Breakdown.SmoothFlow.powerLocal_of`)

### Breakdown.Frac.RegPowerMild

This file derives pointwise and Sobolev norm estimates from the fractional mild symbol equation for the whole space continuation argument.

**Heat multiplier is nonnegative.** The fractional heat multiplier is nonnegative at every frequency. (`_private.Breakdown.Frac.RegPowerMild.0.Breakdown.SmoothFlow.pm_powerHeat_nonneg`)

**Heat multiplier is contractive.** At nonnegative time, the fractional heat multiplier is at most one. (`_private.Breakdown.Frac.RegPowerMild.0.Breakdown.SmoothFlow.pm_powerHeat_le_one`)

**Sublinear powers below the exponential.** For a nonnegative number and an exponent between zero and one, the power is bounded by the exponential. (`_private.Breakdown.Frac.RegPowerMild.0.Breakdown.SmoothFlow.pm_rpow_le_exp`)

**One derivative from heat decay.** For α greater than one and positive time, the heat multiplier times the frequency norm is bounded by the stated negative power of time. (`_private.Breakdown.Frac.RegPowerMild.0.Breakdown.SmoothFlow.pm_powerHeat_mul_le`)

**Bound a vector by its coordinates.** The norm of a complex three-vector is bounded by the sum of its coordinate norms. (`_private.Breakdown.Frac.RegPowerMild.0.Breakdown.SmoothFlow.pm_norm_sum_le`)

**Monotonicity of Sobolev orders.** A lower Sobolev norm square is bounded by a higher one. (`_private.Breakdown.Frac.RegPowerMild.0.Breakdown.SmoothFlow.pm_hsNormSq_mono`)

**Complex frequency coordinates.** Each coordinate of the complex frequency vector is the corresponding real frequency coordinate cast to the complex numbers. (`_private.Breakdown.Frac.RegPowerMild.0.Breakdown.SmoothFlow.pm_freqVec_apply`)

**Expand the frequency pairing.** Pairing the complex frequency vector with a complex vector gives the sum of frequency-coordinate products. (`_private.Breakdown.Frac.RegPowerMild.0.Breakdown.SmoothFlow.pm_inner_freqVec`)

**Frequency squares give norm square.** The sum of the squared complexified frequency coordinates equals the complexification of the real norm square. (`_private.Breakdown.Frac.RegPowerMild.0.Breakdown.SmoothFlow.pm_sum_sq_ofReal`)

**Projection removes frequency pairing.** The solenoidal projection has zero inner product with the frequency vector. (`_private.Breakdown.Frac.RegPowerMild.0.Breakdown.SmoothFlow.pm_inner_freqVec_projC`)

**Solenoidal projection contracts norm.** The solenoidal projection does not increase the vector norm. (`_private.Breakdown.Frac.RegPowerMild.0.Breakdown.SmoothFlow.pm_norm_projC_le`)

**Bound the advection symbol.** For a measurable solenoidal symbol with the stated finite norms, the advection symbol is bounded by the frequency factor times the convolution norm sum. (`_private.Breakdown.Frac.RegPowerMild.0.Breakdown.SmoothFlow.pm_enorm_advectionSymbol_le`)

**Mild equation bounds each frequency.** A mild symbol solution is bounded by its initial value plus the heat-weighted time integral of the nonlinear symbol. (`_private.Breakdown.Frac.RegPowerMild.0.Breakdown.SmoothFlow.pm_enorm_mild_le`)

**Supply the pointwise mild bound.** For α > 1 and m ≥ 3, every solenoidal Hᵐ fractional mild symbol curve is bounded pointwise in extended norm by its initial norm plus the time convolution of its nonlinear convolution norm sum with c times (t − s) raised to −1/(2α). (`Breakdown.SmoothFlow.powerEnormMild`)

**Extract a constant from a norm.** A finite nonnegative constant factors out of the square root of the weighted square integral. (`_private.Breakdown.Frac.RegPowerMild.0.Breakdown.SmoothFlow.pm_lintegral_weighted_const_mul_sq`)

**Derive the Sobolev mild bound.** For α > 1, the extended norm mild bound implies that each solenoidal Hᵐ mild curve with m ≥ 3 has Hᵐ norm bounded by its initial norm plus C times the convolution of its Fourier L¹ norm and Hᵐ norm with the kernel (t − s) raised to −1/(2α). (`Breakdown.SmoothFlow.powerHsMild_of`)

### Breakdown.Frac.RegPowerMildGain

This file shows that the nonlinear part of a fractional mild symbol gains regularity beyond its free heat part.

**Cauchy–Schwarz for nonnegative integrals.** The square of the integral of two measurable nonnegative functions is bounded by the product of their square integrals. (`_private.Breakdown.Frac.RegPowerMildGain.0.Breakdown.SmoothFlow.lintegral_mul_sq_le_of_aemeasurable`)

**Integrate an endpoint singularity.** For an exponent below one, the singular time integral is bounded by the interval length to the complementary power divided by that power. (`_private.Breakdown.Frac.RegPowerMildGain.0.Breakdown.SmoothFlow.lintegral_Ioo_sub_rpow_le_of_lt`)

**Gain regularity in the mild term.** For 1 < α < 3/2, the heat gain and heat part hypotheses imply that an H³ solenoidal mild symbol curve uniformly bounded in fractional order r ≥ 0 has its nonlinear remainder uniformly bounded at order r + 1/2. (`Breakdown.SmoothFlow.powerMildGain_of`)

### Breakdown.Frac.RegPowerMildIntegralCurve

This file proves the curve regularity of the fractional time integral, supporting the local fixed point and continuation construction.

**Real square equals natural square.** The real second power of an extended nonnegative number equals its natural second power. (`_private.Breakdown.Frac.RegPowerMildIntegralCurve.0.Breakdown.SmoothFlow.rpow_two_eq'`)

**Nonnegative fractional heat rate.** The fractional dissipation rate is nonnegative at every frequency. (`_private.Breakdown.Frac.RegPowerMildIntegralCurve.0.Breakdown.SmoothFlow.power_rate_nonneg`)

**Split the heat time difference.** The heat multiplier at a time difference factors into the multiplier at the final time and at the negative starting time. (`_private.Breakdown.Frac.RegPowerMildIntegralCurve.0.Breakdown.SmoothFlow.powerHeat_mul`)

**Heat multiplier decreases in time.** Increasing the elapsed time decreases the fractional heat multiplier. (`_private.Breakdown.Frac.RegPowerMildIntegralCurve.0.Breakdown.SmoothFlow.powerHeat_anti`)

**Continuous heat multiplier.** At fixed frequency, the complex heat multiplier is continuous in time. (`_private.Breakdown.Frac.RegPowerMildIntegralCurve.0.Breakdown.SmoothFlow.powerHeat_continuous_time`)

**Continuous reversed heat time.** At fixed frequency, the heat multiplier evaluated at negative time is continuous. (`_private.Breakdown.Frac.RegPowerMildIntegralCurve.0.Breakdown.SmoothFlow.powerHeat_continuous_neg`)

**Continuous shifted heat time.** At fixed frequency and final time, the heat multiplier is continuous in the starting time. (`_private.Breakdown.Frac.RegPowerMildIntegralCurve.0.Breakdown.SmoothFlow.powerHeat_continuous_sub`)

**Joint continuity of the heat factor.** For nonnegative α, the heat multiplier is jointly continuous in frequency and starting time. (`_private.Breakdown.Frac.RegPowerMildIntegralCurve.0.Breakdown.SmoothFlow.powerHeat_continuous_joint`)

**Extend a unit-interval heat bound.** A uniform heat-weight bound on intervals of length at most one extends to length at most k plus one with that multiplicative factor. (`_private.Breakdown.Frac.RegPowerMildIntegralCurve.0.Breakdown.SmoothFlow.weight_chunks`)

**Uniform heat weight on an interval.** A unit-interval bound controls the heat square integral over the whole interval by one plus the rounded-up interval length. (`_private.Breakdown.Frac.RegPowerMildIntegralCurve.0.Breakdown.SmoothFlow.weight_uniform`)

**Square bound for the memory integral.** The square of the mild memory integral is bounded by the heat square integral times the forcing square integral. (`_private.Breakdown.Frac.RegPowerMildIntegralCurve.0.Breakdown.SmoothFlow.enorm_memoryIntegral_sq_le`)

**Successor Sobolev weight.** Increasing the Sobolev order by one multiplies the weight by one plus the frequency norm square. (`_private.Breakdown.Frac.RegPowerMildIntegralCurve.0.Breakdown.SmoothFlow.hsWeight_succ'`)

**One-weight gain for the memory term.** A uniform weighted heat bound controls the next-order memory square by the time integral of the preceding-order forcing square. (`_private.Breakdown.Frac.RegPowerMildIntegralCurve.0.Breakdown.SmoothFlow.memoryIntegral_weight_le`)

**Square bound for a difference.** The square norm of a vector difference is at most twice the sum of the two norm squares. (`_private.Breakdown.Frac.RegPowerMildIntegralCurve.0.Breakdown.SmoothFlow.enorm_sub_sq_le'`)

**Sobolev weights are at least one.** Every converted Sobolev weight is at least one. (`_private.Breakdown.Frac.RegPowerMildIntegralCurve.0.Breakdown.SmoothFlow.one_le_hsWeight'`)

**Measurable Sobolev weight.** The converted Sobolev weight is measurable in frequency. (`_private.Breakdown.Frac.RegPowerMildIntegralCurve.0.Breakdown.SmoothFlow.measurable_hsWeight'`)

**Continuity of the memory curve.** For α > 1, the basic and weighted heat hypotheses make the fractional Duhamel integral of a source jointly measurable in space and time and uniformly bounded in Hⁿ into an Hⁿ⁺¹ curve on the same closed interval. (`Breakdown.SmoothFlow.powerMildIntegralCurve`)

### Breakdown.Frac.RegPowerMildMapBasic

This file establishes the initial value and solenoidality properties of the fractional mild map used in local existence.

**Conjugate each coordinate.** Vector conjugation acts by complex conjugation on every coordinate. (`_private.Breakdown.Frac.RegPowerMildMapBasic.0.Breakdown.SmoothFlow.PowerInternal.conjVec_apply'`)

**Coordinates of the frequency vector.** The complex frequency vector has the real frequency coordinates cast to complex numbers. (`_private.Breakdown.Frac.RegPowerMildMapBasic.0.Breakdown.SmoothFlow.PowerInternal.freqVec_apply'`)

**Conjugation as a real isometry.** Complex vector conjugation is packaged as a real linear isometry. (`_private.Breakdown.Frac.RegPowerMildMapBasic.0.Breakdown.SmoothFlow.PowerInternal.conjVecIsom`)

**Coordinate frequency pairing.** The inner product with the frequency vector equals the sum of frequency-coordinate products. (`_private.Breakdown.Frac.RegPowerMildMapBasic.0.Breakdown.SmoothFlow.PowerInternal.inner_freqVec'`)

**Even fractional heat symbol.** The heat symbol is unchanged by negating frequency. (`_private.Breakdown.Frac.RegPowerMildMapBasic.0.Breakdown.SmoothFlow.PowerInternal.powerHeatSymbol_neg`)

**The mild map starts at the datum.** At its starting time, the fractional mild map equals the prescribed initial symbol. (`Breakdown.SmoothFlow.powerMildMap_self`)

**The mild map preserves solenoidality.** A solenoidal initial symbol and the stated conjugate symmetry of the input curve make the mild-map output solenoidal. (`Breakdown.SmoothFlow.powerMildMap_solenoidal`)

**Basic properties of the mild map.** For every α, the fractional mild map equals its prescribed datum at the initial time and is solenoidal whenever that datum is solenoidal and the input curve has Fourier conjugate symmetry almost everywhere throughout the intervening time interval. (`Breakdown.SmoothFlow.powerMildMapBasic`)

### Breakdown.Frac.RegPowerMildMapCurve

This file shows that the fractional mild map preserves the required Sobolev curve space.

**Add Sobolev-continuous curves.** Adding two curves of the same Sobolev order gives another curve of that order on the same interval. (`_private.Breakdown.Frac.RegPowerMildMapCurve.0.Breakdown.SmoothFlow.powerMapCurve_add`)

**Heat evolution is a Sobolev curve.** The heat-part interface makes the heat evolution of measurable finite-norm data a Sobolev curve. (`_private.Breakdown.Frac.RegPowerMildMapCurve.0.Breakdown.SmoothFlow.powerMapCurve_heat`)

**Continuity of the fractional mild map.** For α > 1, the mild integral curve and heat part hypotheses ensure that the fractional mild map takes an Hᵐ input curve to an Hᵐ curve for m ≥ 3, provided the initial datum is measurable with finite Hᵐ norm and the time length is positive. (`Breakdown.SmoothFlow.powerMildMapCurve_of`)

### Breakdown.Frac.RegPowerMildMapEst

This file gives the boundedness and difference estimates for the fractional mild map that support the local contraction argument.

**Square bound for a sum.** The square norm of a vector sum is at most twice the sum of the two norm squares. (`_private.Breakdown.Frac.RegPowerMildMapEst.0.Breakdown.SmoothFlow.pmap_enorm_add_sq_le`)

**Measurability of the Sobolev weight.** The converted Sobolev weight is measurable in frequency. (`_private.Breakdown.Frac.RegPowerMildMapEst.0.Breakdown.SmoothFlow.pmap_measurable_weight`)

**Sobolev square bound for a sum.** For a measurable first summand, the Sobolev norm square of a sum is at most twice the sum of the separate squares. (`_private.Breakdown.Frac.RegPowerMildMapEst.0.Breakdown.SmoothFlow.pmap_hsNormSq_add_le`)

**Contractive heat symbol.** At nonnegative time, the heat symbol is at most one. (`_private.Breakdown.Frac.RegPowerMildMapEst.0.Breakdown.SmoothFlow.pmap_symbol_le_one`)

**Heat multiplication contracts Hᵐ.** At nonnegative time, multiplication by the heat symbol does not increase the Sobolev norm square. (`_private.Breakdown.Frac.RegPowerMildMapEst.0.Breakdown.SmoothFlow.pmap_hsNormSq_smul_le`)

**Square after nonnegative conversion.** The square of the nonnegative-real conversion is bounded by the conversion of the real square. (`_private.Breakdown.Frac.RegPowerMildMapEst.0.Breakdown.SmoothFlow.pmap_ofReal_sq_le`)

**Measurable heat multiplier.** The complex fractional heat multiplier is measurable in frequency. (`_private.Breakdown.Frac.RegPowerMildMapEst.0.Breakdown.SmoothFlow.pmap_measurable_symbol`)

**Enlarge a real coefficient safely.** With a nonnegative middle factor, the product of three nonnegative-real conversions is bounded by converting the stated enlarged real product. (`_private.Breakdown.Frac.RegPowerMildMapEst.0.Breakdown.SmoothFlow.pmap_const_le`)

**Supply estimates for the mild map.** For α > 1, the heat integral and basic heat hypotheses give the mild map on Hᵐ curves with m ≥ 3 and squared norm bound B an output bound 2 times the initial squared norm plus CδB², and a squared difference bound CδB times the supremum input squared difference, when 0 < δ ≤ 1. (`Breakdown.SmoothFlow.powerMildMapEst_of`)

### Breakdown.Frac.RegPowerPersist

This file propagates higher Sobolev regularity along a fractional mild symbol trajectory from regular initial data.

**Control the Sobolev norm of a sum.** For measurable symbols, the Sobolev norm square of their sum is at most twice the sum of their norm squares. (`_private.Breakdown.Frac.RegPowerPersist.0.Breakdown.SmoothFlow.PowerInternal.persistHs_add_le`)

**Control the Sobolev difference.** For measurable symbols, the Sobolev norm square of their difference is at most twice the sum of their norm squares. (`_private.Breakdown.Frac.RegPowerPersist.0.Breakdown.SmoothFlow.PowerInternal.persistHs_sub_le`)

**Pass convergence through a bound.** An extended nonnegative function bounded eventually by twice two functions tending to zero also tends to zero. (`_private.Breakdown.Frac.RegPowerPersist.0.Breakdown.SmoothFlow.PowerInternal.persistTendsto_of_le`)

**Bootstrap in half-order steps.** The heat-part and mild-gain interfaces bound successive half-order Sobolev norms up to the initial regularity order. (`_private.Breakdown.Frac.RegPowerPersist.0.Breakdown.SmoothFlow.PowerInternal.persistHalfStep_bound`)

**Preserve higher Sobolev continuity.** The stated gain and heat-part interfaces preserve every higher Sobolev order already finite at the initial time. (`_private.Breakdown.Frac.RegPowerPersist.0.Breakdown.SmoothFlow.PowerInternal.persistCurve`)

**Supply persistence of regularity.** For α > 1, the mild gain and heat part hypotheses propagate any finite initial Hᵐ norm with m ≥ 3 along a solenoidal H³ fractional mild symbol curve, yielding an Hᵐ curve on the entire interval. (`Breakdown.SmoothFlow.powerPersist_of`)

### Breakdown.Frac.RegPowerPhysCurve

This file turns regular fractional symbol curves into smooth physical velocity curves on the whole space route.

**Norm of the complex frequency vector.** Complexifying a frequency vector leaves its norm unchanged. (`Breakdown.SmoothFlow.PowerInternal.norm_freqVec_eq'`)

**Move a polynomial weight to the field.** Integrability with weight k plus j gives integrability with weight k after multiplying the field by the j-th polynomial weight. (`Breakdown.SmoothFlow.PowerInternal.memLp_weight_shift'`)

**The first complex unit vector.** The chosen complex unit vector has value one in coordinate zero and zero in the other coordinates. (`Breakdown.SmoothFlow.PowerInternal.unitVec`)

**Fourier inversion along a unit vector.** Inverse Fourier transformation commutes with multiplying a scalar symbol by the chosen fixed unit vector. (`Breakdown.SmoothFlow.PowerInternal.inverseTransform_smul_unitVec`)

**Recover the scalar coefficient.** The first coordinate of a scalar multiple of the chosen unit vector is that scalar. (`Breakdown.SmoothFlow.PowerInternal.unitVec_apply_zero`)

**Recover scalar measurability.** Measurability of a scalar symbol multiplied by the fixed unit vector implies measurability of the scalar symbol. (`Breakdown.SmoothFlow.PowerInternal.aesm_of_unitVec`)

**First real coordinate as a linear map.** The first real-coordinate map takes the real part of coordinate zero as a continuous real linear map. (`Breakdown.SmoothFlow.PowerInternal.firstReal`)

**Recover a scalar physical field.** The scalar inverse transform is the first real coordinate of the vector inverse transform along the chosen unit vector. (`Breakdown.SmoothFlow.PowerInternal.physScalar_eq_firstReal`)

**Unit-vector multiplication is isometric.** Multiplying the chosen unit vector by a complex scalar gives a vector with the scalar's norm. (`Breakdown.SmoothFlow.PowerInternal.norm_smul_unitVec`)

**Bound fractional power by cubic growth.** For zero at most α less than three halves, the fractional multiplier is bounded by the stated cubic polynomial weight. (`Breakdown.SmoothFlow.PowerInternal.power_weight_le`)

**Fractional power loses three weights.** Under the stated range of α, applying the fractional multiplier maps integrability with k plus three weights to integrability with k weights. (`Breakdown.SmoothFlow.PowerInternal.memLp_powerSymbol'`)

**Weighted integrability of pressure.** For a solenoidal symbol curve of every Sobolev order, the pressure symbol along the unit vector is integrable with each polynomial weight. (`Breakdown.SmoothFlow.PowerInternal.memLp_pressure_unitVec`)

**Weighted pressure-gradient symbols.** For a solenoidal curve of every Sobolev order, both pressure-gradient symbol forms have every polynomial integrability weight. (`Breakdown.SmoothFlow.PowerInternal.memLp_gradPressure'`)

**Integrable pressure symbol.** For a solenoidal curve of every Sobolev order, the pressure symbol is integrable at every time in the interval. (`Breakdown.SmoothFlow.PowerInternal.integrable_pressure'`)

**Split the nonlinear symbol.** The nonlinear symbol is minus the pressure-gradient symbol minus the advection symbol. (`Breakdown.SmoothFlow.PowerInternal.nonlinSymbol_eq'`)

**Weighted nonlinear symbol.** For a solenoidal curve of every Sobolev order, the nonlinear symbol is integrable with each polynomial weight. (`Breakdown.SmoothFlow.PowerInternal.memLp_nonlin'`)

**Weighted time-derivative symbol.** For the stated range of α and a solenoidal curve of every Sobolev order, the time-derivative symbol has every polynomial integrability weight. (`Breakdown.SmoothFlow.PowerInternal.memLp_powerTimeDeriv'`)

**Assemble physical regularity.** For 1 < α < 3/2, the weighted curve, pressure curve, and physical power hypotheses give an all order Sobolev solenoidal mild symbol curve jointly smooth physical velocity and pressure, the stated interior time derivative, integrable equation symbols, and physical realizations of its fractional power and pressure gradient. (`Breakdown.SmoothFlow.powerPhysCurve_of`)

### Breakdown.Frac.RegPowerPhysPower

This file identifies the physical fractional power of regular Fourier fields and controls the resulting weighted curves.

**Plane-wave Taylor remainder.** The wave remainder subtracts the constant, linear and quadratic Taylor terms from the complex plane wave. (`_private.Breakdown.Frac.RegPowerPhysPower.0.Breakdown.SmoothFlow.PowerInternal.waveRem`)

**Norm of an imaginary real scalar.** The norm of a real scalar multiplied by the imaginary unit is the scalar's absolute value. (`_private.Breakdown.Frac.RegPowerPhysPower.0.Breakdown.SmoothFlow.PowerInternal.norm_ofReal_mul_I`)

**Quadratic plane-wave remainder bound.** The norm of the stated plane-wave remainder is bounded by three times the phase square. (`_private.Breakdown.Frac.RegPowerPhysPower.0.Breakdown.SmoothFlow.PowerInternal.wave_quad`)

**Cubic plane-wave remainder bound.** The norm of the stated plane-wave remainder is bounded by three times the absolute phase cubed. (`_private.Breakdown.Frac.RegPowerPhysPower.0.Breakdown.SmoothFlow.PowerInternal.wave_cube`)

**Quadratic bound for the wave remainder.** The wave remainder is bounded by three times the square of twice pi times its argument. (`_private.Breakdown.Frac.RegPowerPhysPower.0.Breakdown.SmoothFlow.PowerInternal.waveRem_sq`)

**Cubic bound for the wave remainder.** The wave remainder is bounded by three times the absolute cube of twice pi times its argument. (`_private.Breakdown.Frac.RegPowerPhysPower.0.Breakdown.SmoothFlow.PowerInternal.waveRem_cube`)

**Trigonometric form of the remainder.** The wave remainder has the stated cosine remainder as its real part and sine remainder as its imaginary part. (`_private.Breakdown.Frac.RegPowerPhysPower.0.Breakdown.SmoothFlow.PowerInternal.waveRem_eq_trig`)

**Integrate the wave remainder.** For one less than α less than three halves, the singularly weighted wave remainder is integrable and its integral gives the normalized fractional Fourier multiplier. (`_private.Breakdown.Frac.RegPowerPhysPower.0.Breakdown.SmoothFlow.PowerInternal.integral_waveRem`)

**Physical field by Fourier characters.** The physical field is the real vector part of the integral of Fourier characters against the symbol. (`_private.Breakdown.Frac.RegPowerPhysPower.0.Breakdown.SmoothFlow.PowerInternal.physField_eq_char`)

**Write a Fourier character exponentially.** Scalar multiplication by a Fourier character equals multiplication by the corresponding complex exponential. (`_private.Breakdown.Frac.RegPowerPhysPower.0.Breakdown.SmoothFlow.PowerInternal.char_smul_eq`)

**Lower the polynomial integration order.** A larger polynomial integrability weight implies every smaller natural weight. (`_private.Breakdown.Frac.RegPowerPhysPower.0.Breakdown.SmoothFlow.PowerInternal.memLp_weight_mono`)

**Translate a reconstructed field.** Translating the physical field multiplies its Fourier symbol by the character of the translation. (`_private.Breakdown.Frac.RegPowerPhysPower.0.Breakdown.SmoothFlow.PowerInternal.physField_translate`)

**Second directional derivative formula.** With three polynomial integrability weights, the second directional derivative of the physical field is reconstructed from the stated quadratic frequency multiplier. (`_private.Breakdown.Frac.RegPowerPhysPower.0.Breakdown.SmoothFlow.PowerInternal.second_physField`)

**Integrability under cubic growth.** A continuous multiplier of at most cubic growth preserves integrability of a symbol with three polynomial weights. (`_private.Breakdown.Frac.RegPowerPhysPower.0.Breakdown.SmoothFlow.PowerInternal.integrable_smul_of_bound`)

**Reconstruct the Taylor remainder.** For a symbol with three polynomial integrability weights, the physical second-order remainder is reconstructed by multiplying the symbol by the wave remainder. (`_private.Breakdown.Frac.RegPowerPhysPower.0.Breakdown.SmoothFlow.PowerInternal.remainder_physField`)

**Two-variable fractional kernel term.** The kernel term combines the singular spatial weight, the Fourier character and the wave remainder acting on the symbol. (`_private.Breakdown.Frac.RegPowerPhysPower.0.Breakdown.SmoothFlow.PowerInternal.kernelTerm`)

**Split the singular remainder bound.** For α greater than one, the kernel remainder is bounded by separate near-origin and far-field powers times a cubic frequency weight. (`_private.Breakdown.Frac.RegPowerPhysPower.0.Breakdown.SmoothFlow.PowerInternal.kernel_bound`)

**Joint integrability of the kernel term.** For one less than α less than three halves and the stated weighted symbol integrability, the two-variable kernel term is integrable. (`_private.Breakdown.Frac.RegPowerPhysPower.0.Breakdown.SmoothFlow.PowerInternal.integrable_kernelTerm`)

**Identify the physical fractional power.** For 1 < α < 3/2, the plane wave eigenvalue hypothesis identifies the fractional power of a physical Fourier field with the inverse transform of its fractional multiplier whenever the symbol belongs to the stated order three weighted L¹ space. (`Breakdown.SmoothFlow.powerPhysPower_of`)

### Breakdown.Frac.RegPowerPointwise

This file differentiates the fractional mild symbol equation pointwise in time, preparing the physical momentum equation.

**Differentiate each frequency in time.** A mild symbol solution with continuous nonlinear symbol has the stated time derivative within its closed time interval. (`_private.Breakdown.Frac.RegPowerPointwise.0.Breakdown.SmoothFlow.power_hasDerivWithinAt_apply`)

**Supply pointwise time derivatives.** For α > 1 and T > 0, a fractional mild symbol curve whose nonlinear symbol is continuous at each frequency has a derivative within [0,T] at every time and frequency equal to minus its fractional multiplier plus its nonlinear symbol. (`Breakdown.SmoothFlow.powerPointwiseDeriv`)

**Joint measurability from time continuity.** Frequencywise continuity in time and slicewise measurability give joint almost-everywhere strong measurability on the stated interval. (`_private.Breakdown.Frac.RegPowerPointwise.0.Breakdown.SmoothFlow.power_aesm_uncurry_of_continuousOn`)

**Supply joint symbol measurability.** For α > 1, the pointwise derivative hypothesis makes the extended norm of an H¹ fractional mild symbol curve jointly almost everywhere measurable for the product of time measure on [0,T] and spatial measure when T > 0. (`Breakdown.SmoothFlow.powerAEMeas_of`)

### Breakdown.Frac.RegPowerPressure

This file supplies smooth pressure curves for the whole space fractional symbol solution construction.

**Construct the pressure curve.** For α > 1, the weighted curve hypothesis makes the pressure symbol of an all order Sobolev solenoidal mild curve a curve of every finite differentiability order in every natural weighted L¹ space on its positive closed time interval. (`Breakdown.SmoothFlow.powerPressureCurve_of`)

### Breakdown.Frac.RegPowerSolution

This file assembles the smooth physical fractional solution from the symbol trajectory and pressure interfaces.

**Reconstruction commutes with negation.** Negating the Fourier symbol negates the reconstructed physical field. (`_private.Breakdown.Frac.RegPowerSolution.0.Breakdown.SmoothFlow.physField_neg_apply`)

**Advection leaves the pressure gradient.** Adding the advection symbol to the nonlinear symbol gives minus the pressure-gradient symbol. (`_private.Breakdown.Frac.RegPowerSolution.0.Breakdown.SmoothFlow.nonlin_add_advection`)

**Fourier momentum identity.** The time derivative, advection and fractional dissipation symbols sum to minus the pressure-gradient symbol. (`_private.Breakdown.Frac.RegPowerSolution.0.Breakdown.SmoothFlow.powerTimeDeriv_add_advection_add_power`)

**Recover the physical solution.** For α > 1, the physical curve hypothesis turns an all order Sobolev solenoidal mild symbol curve on [0,T] with T > 0 into a smooth fractional velocity–pressure solution with zero divergence and the momentum equation at interior times. (`Breakdown.SmoothFlow.powerSolutionOn_of`)

### Breakdown.Frac.RegPowerWeightCurve

This file proves weighted curve regularity for Fourier symbols, supporting physical velocity, pressure, and fractional power realization.

**Identify the weighted L¹ representative.** For an integrable symbol, its chosen weighted L¹ representative equals the representative supplied by its integrability proof. (`_private.Breakdown.Frac.RegPowerWeightCurve.0.Breakdown.SmoothFlow.PowerInternal.weightL1_toLp`)

**All polynomial L¹ weights are finite.** A curve continuous at every Sobolev order has every polynomial L¹ weight at each time in the interval. (`_private.Breakdown.Frac.RegPowerWeightCurve.0.Breakdown.SmoothFlow.PowerInternal.memLp_weight_of_allCurve`)

**Continuity in weighted L¹.** A curve continuous at every Sobolev order is continuous in each weighted L¹ space on the same interval. (`_private.Breakdown.Frac.RegPowerWeightCurve.0.Breakdown.SmoothFlow.PowerInternal.continuousOn_weight_allCurve`)

**Cubic control of the power multiplier.** For one less than α less than three halves, the fractional multiplier is bounded by its stated constant times the cubic polynomial weight. (`_private.Breakdown.Frac.RegPowerWeightCurve.0.Breakdown.SmoothFlow.PowerInternal.powerFactor_le`)

**Fractional power as a continuous map.** For the stated range of α, negative fractional multiplication is a continuous linear map from k plus three weighted L¹ orders to k orders. (`_private.Breakdown.Frac.RegPowerWeightCurve.0.Breakdown.SmoothFlow.PowerInternal.exists_clm_power`)

**Smooth weighted time-derivative map.** For the stated range of α, the time-derivative symbol is represented by a smooth map between the indicated weighted L¹ spaces. (`_private.Breakdown.Frac.RegPowerWeightCurve.0.Breakdown.SmoothFlow.PowerInternal.powerTimeDeriv_repr`)

**Continuous fixed-frequency projection.** At a fixed frequency, the solenoidal projection is continuous in the vector being projected. (`_private.Breakdown.Frac.RegPowerWeightCurve.0.Breakdown.SmoothFlow.continuous_projC_fixed`)

**Supply weighted time regularity.** For 1 < α < 3/2, the pointwise derivative hypothesis makes an all order Sobolev solenoidal mild curve smooth in every natural weighted L¹ space, with derivative within the time interval represented by its fractional time derivative symbol. (`Breakdown.SmoothFlow.powerWeightCurve_of`)

### Breakdown.Frac.ScaledDefs

This file defines the abstract scaled mild framework, recurrent orbit, step pieces, and gluing operations shared by the fractional transfer argument.

**Scaled heat and bilinear framework.** The framework packages the heat semigroup, symmetric bilinear kernel, dilation laws, bounds, continuity and compactness needed for a scaled mild evolution. (`Breakdown.ScaledMildFramework`)

**Forget the dilation structure.** The scaled framework supplies the underlying heat-and-bilinear framework by retaining its heat and kernel data. (`Breakdown.ScaledMildFramework.toHeatBilinear`)

**Mild solution before the endpoint.** The half-open mild-solution predicate requires continuity, time-integrability of the bilinear term and the mild equation before the final endpoint. (`Breakdown.ScaledMildFramework.IsMildOn`)

**Mild solution including the endpoint.** The closed-interval mild predicate requires continuity, time-integrability of the bilinear term and the mild equation at every point of the interval. (`Breakdown.ScaledMildFramework.IsMildOnIcc`)

**Heat evolution in similarity time.** The similarity-time heat operator first applies the heat semigroup and then the prescribed exponential dilation. (`Breakdown.ScaledMildFramework.S`)

**Bilinear kernel in similarity time.** The similarity-time bilinear kernel applies the physical kernel at transformed time and then dilates its output. (`Breakdown.ScaledMildFramework.Ks`)

**Symmetry of the scaled framework.** The commutation predicate requires the isometry to commute with heat evolution, the bilinear kernel and dilations. (`Breakdown.ScaledMildFramework.Commutes`)

**A recurrent similarity orbit.** The orbit predicate requires a continuous nonzero profile, positive recurrence period, recurrence up to the isometry and the similarity-time mild equation. (`Breakdown.ScaledMildFramework.IsOrbit`)

**Return an orbit to physical time.** The self-similar trajectory dilates the orbit evaluated at logarithmic similarity time. (`Breakdown.ScaledMildFramework.selfSimilar`)

**A single profile time piece.** The profile piece restricts the self-similar trajectory from its chosen phase to one step interval. (`Breakdown.ScaledMildFramework.profilePiece`)

**Linearized operator on a time piece.** The step operator is twice the bilinear piece map with one argument fixed to the profile piece. (`Breakdown.ScaledMildFramework.stepOp`)

**Free evolution on one time piece.** The free step map sends initial data through the heat piece map on the chosen interval. (`Breakdown.ScaledMildFramework.stepFree`)

**Rescaled endpoint of a time piece.** The step-end map evaluates the piece at its endpoint and applies the exponential dilation. (`Breakdown.ScaledMildFramework.stepEnd`)

**Half-open mild predicates agree.** The scaled and underlying heat-and-bilinear frameworks have identical half-open mild-solution predicates. (`Breakdown.ScaledMildFramework.isMildOn_iff`)

**Closed mild predicates agree.** The scaled and underlying heat-and-bilinear frameworks have identical closed-interval mild-solution predicates. (`Breakdown.ScaledMildFramework.isMildOnIcc_iff`)

**The underlying kernel is compact.** The heat-and-bilinear framework inherited from a scaled framework satisfies the compact-kernel condition. (`Breakdown.ScaledMildFramework.hasCompactKernel`)

**Glue geometrically scaled pieces.** The glued trajectory selects its geometric time interval, reads the matching piece at local time and applies the inverse interval dilation. (`Breakdown.ScaledMildFramework.gluePieces`)

### Breakdown.Frac.ScaledExports

This file gathers providers for the scaled orbit and step interfaces, exposing the abstract transfer construction to the profile route.

**Export the scaling theorem.** In a scaled mild framework, if μ > 0 and T ≥ 0, a path mild on [0,μT] remains mild on [0,T] after replacing its value at s by the μ dilation of its value at μs. (`Breakdown.scaledScale`)

**Export the physical-orbit theorem.** In a scaled mild framework with positive exponent, every continuous path satisfying the similarity time variation of constants equation gives, at each initial phase, a physical mild trajectory on [0,1). (`Breakdown.scaledOrbitPhysical`)

**Export the orbit lower bound.** The scaled orbit-norm interface supplies the positive uniform norm lower bound under its declared hypotheses. (`Breakdown.scaledOrbitNorm`)

**Export profile-piece properties.** The profile-piece interface supplies the mild equation, matching, recurrence and norm bounds for the scaled pieces. (`Breakdown.scaledProfilePiece`)

**Export scaled gluing.** The scaled gluing interface supplies a mild trajectory from matching geometrically scaled pieces. (`Breakdown.scaledGlue`)

**Export scaled monodromy.** The scaled monodromy interface supplies inverse bounds, recurrence and the compact-perturbation comparison. (`Breakdown.scaledMonodromy`)

**Export the scaled step data.** The scaled step-data interface supplies the finite-dimensional correction and right inverse required for the piece construction. (`Breakdown.scaledStepData`)

**Export transfer to dense data.** The scaled transfer interface produces a mild trajectory from nearby dense-subspace data with quantified convergence to the recurrent orbit. (`Breakdown.scaledTransferHolds`)

### Breakdown.Frac.ScaledGlue

This file proves that matching scaled mild pieces glue into a single mild trajectory, a step in transferring a recurrent orbit to a physical flow.

**One rescaled piece in global time.** The local glue piece applies the inverse geometric dilation to a time-translated and rescaled piece. (`Breakdown.FracInternal.scaledGluePiece`)

**Continuity of a rescaled piece.** Every rescaled glue piece is continuous in global time. (`Breakdown.FracInternal.scaledGluePiece_continuous`)

**The glued curve agrees with each piece.** For a scaling ratio between zero and one and matching endpoints, the glued trajectory agrees with the rescaled piece on its closed interval. (`Breakdown.FracInternal.scaledGlue_eq`)

**Mild identity on a rescaled piece.** The scaling and time-shift interfaces transfer the mild identity of each piece to its global time interval. (`Breakdown.FracInternal.scaledPiece_mildIdentity`)

**Glue finitely many time pieces.** The scaling, concatenation and shift interfaces give continuity and the variation-of-constants identity through every finite collection of matching pieces. (`Breakdown.FracInternal.scaledGlue_upto`)

**Derive the scaled gluing interface.** The scaling, concatenation, and time shift hypotheses glue mild pieces with 0 < μ < 1 and dilation matched endpoints into a mild path on [0,1), whose value at every time has the stated equality with a rescaled value inside one piece. (`Breakdown.scaledGlue_of`)

### Breakdown.Frac.ScaledMain

This file assembles the scaled transfer theorem from the orbit, step, gluing, and monodromy interfaces.

**Derive transfer to dense initial data.** The step data, contraction, piece perturbation, profile piece, and gluing hypotheses give every commuting recurrent orbit in a scaled framework with positive exponent a mild path starting arbitrarily close in any prescribed dense subspace and approaching that orbit after dilation at a positive power rate as t tends to one. (`Breakdown.scaledTransferHolds_of`)

### Breakdown.Frac.ScaledMonodromy

This file relates the linearized step operators around a recurrent orbit to the monodromy construction used in the scaled transfer theorem.

**Lift an isometry to a time piece.** The lifted operator applies the given real linear isometry pointwise to a continuous time piece. (`_private.Breakdown.Frac.ScaledMonodromy.0.Breakdown.liftPiece`)

**Evaluate the lifted isometry.** Evaluating the lifted isometry at a time equals applying the isometry to the original piece value. (`_private.Breakdown.Frac.ScaledMonodromy.0.Breakdown.liftPiece_apply`)

**Extend a lifted time piece.** For a nonnegative interval length, extending a lifted piece commutes with its isometry. (`_private.Breakdown.Frac.ScaledMonodromy.0.Breakdown.extendPiece_liftPiece`)

**Evaluate the piece endpoint.** For a nonnegative interval length, the endpoint map is evaluation at the right endpoint. (`_private.Breakdown.Frac.ScaledMonodromy.0.Breakdown.pieceEnd_apply`)

**Cancel a lifted inverse on the right.** Lifting an isometry and then its inverse gives the identity operator on pieces. (`_private.Breakdown.Frac.ScaledMonodromy.0.Breakdown.liftPiece_mul_symm`)

**Cancel a lifted inverse on the left.** Lifting the inverse isometry and then the original isometry gives the identity operator on pieces. (`_private.Breakdown.Frac.ScaledMonodromy.0.Breakdown.liftPiece_symm_mul`)

**Neumann inverse bound.** If one minus an operator is a unit and the operator norm is at most one quarter, its inverse norm is at most four thirds. (`_private.Breakdown.Frac.ScaledMonodromy.0.Breakdown.norm_inverse_one_sub_le`)

**Identify an inverse by multiplication.** A right inverse of a unit equals its ring inverse. (`_private.Breakdown.Frac.ScaledMonodromy.0.Breakdown.inverse_eq_of_mul_eq_one`)

**Invert a conjugated operator.** Conjugating a unit by mutually inverse elements conjugates its inverse by the same elements. (`_private.Breakdown.Frac.ScaledMonodromy.0.Breakdown.inverse_conj`)

**Products preserve compact errors.** If each step differs compactly from one fixed operator, the iterated product differs compactly from the corresponding power of that operator. (`_private.Breakdown.Frac.ScaledMonodromy.0.Breakdown.iterProd_sub_pow_compact`)

**Derive scaled monodromy.** The piece operator, compact piece, and profile piece hypotheses make step perturbations of norm at most one quarter invertible with inverse norm at most four thirds, yield recurrence by conjugation with the orbit symmetry, and identify the monodromy as a compact perturbation of an operator bounded by exp(−κP) for positive κ and a positive subdivision count. (`Breakdown.scaledMonodromy_of`)

### Breakdown.Frac.ScaledOrbitNorm

This file controls the norm of a recurrent scaled orbit, including the positive lower bounds needed to retain its nontrivial size.

**The orbit norm is periodic.** An orbit recurring by an isometry has a periodic norm with the same period. (`Breakdown.FracInternal.scaledOrbit_norm_periodic`)

**Norm after whole recurrence periods.** Adding a natural multiple of the orbit period leaves its norm unchanged. (`Breakdown.FracInternal.scaledOrbit_norm_add_nat_mul`)

**Bound the orbit from a physical bound.** A uniformly bounded physical self-similar trajectory gives the stated exponentially weighted upper bound on its similarity orbit. (`Breakdown.FracInternal.scaledOrbit_decay`)

**Choose a decaying recurrence iterate.** For positive scaling exponent and period, some natural recurrence iterate makes twice the exponential scaling factor less than one. (`Breakdown.FracInternal.exp_pow_small`)

**Uniform upper bound for the orbit.** Every recurrent orbit in a scaled mild framework with positive scaling exponent has a single uniform norm bound over all similarity times. (`Breakdown.scaledOrbitBound`)

**Derive the positive orbit lower bound.** The physical orbit, uniqueness, and small data hypotheses give every recurrent orbit with a commuting symmetry in a scaled framework of positive exponent a strictly positive norm lower bound uniform in similarity time. (`Breakdown.scaledOrbitNorm_of`)

### Breakdown.Frac.ScaledOrbitPhysical

This file converts the abstract recurrent orbit into its physical time representation for the fractional profile route.

**Inverse dilations cancel.** For a positive dilation parameter, applying its inverse dilation after it recovers the original vector. (`Breakdown.ScaledMildFramework.D_inv_apply`)

**Continuity of the physical orbit.** A continuous similarity profile gives a continuous physical self-similar trajectory before time one. (`Breakdown.ScaledMildFramework.selfSimilar_continuousOn`)

**Physical mild equation from the orbit.** The similarity-time variation-of-constants identity transforms into the physical mild equation before time one. (`Breakdown.ScaledMildFramework.selfSimilar_eq`)

**Derive the physical-orbit interface.** The variation of constants integral hypothesis turns every continuous solution of the similarity time equation in a scaled framework of positive exponent into a physical mild trajectory on [0,1) for each initial phase. (`Breakdown.scaledOrbitPhysical_of`)

### Breakdown.Frac.ScaledProfilePiece

This file proves the mild evolution and endpoint relations for the orbit pieces used in the scaled step construction.

**Evaluate a profile time piece.** Under the physical-orbit interface and the stated orbit assumptions, each profile piece evaluates to the self-similar trajectory at its selected phase. (`Breakdown.FracInternal.scaledProfilePiece_apply`)

**Extend the profile piece correctly.** Under the stated orbit hypotheses and a positive step count, extending the profile piece agrees with the self-similar trajectory throughout the step interval. (`Breakdown.FracInternal.scaledExtendPiece_profilePiece`)

**Derive the profile-piece interface.** The physical orbit hypothesis makes the pieces of a commuting recurrent orbit with positive scaling exponent and positive subdivision count equal its phase shifted similarity trajectory, mild on each step, matched by dilation at endpoints, recurrent under the symmetry, and bounded by exp(κP/k) times any orbit norm bound. (`Breakdown.scaledProfilePiece_of`)

### Breakdown.Frac.ScaledScale

This file proves the time and amplitude scaling law for mild trajectories in the abstract scaled framework.

**Scale the bilinear kernel.** For a positive scale and an earlier integration time, dilating the rescaled bilinear kernel gives the kernel of the dilated arguments with the stated time factor. (`Breakdown.FracInternal.scaled_kernel_eq_of_framework`)

**Derive the scaling interface.** The variation of constants integral hypothesis proves that a path mild on [0,μT], with μ > 0 and T ≥ 0, remains mild on [0,T] after composing time with multiplication by μ and applying dilation by μ. (`Breakdown.scaledScale_of`)

### Breakdown.Frac.ScaledStatements

This file declares the interfaces for orbit bounds, physical scaling, step data, gluing, monodromy, and the final scaled transfer construction.

**Scaling of a mild solution.** The scaling proposition requires positive dilation to turn a mild solution on a rescaled interval into a mild solution on the original interval. (`Breakdown.ScaledScaleStatement`)

Proved by `Breakdown.scaledScale`. Also proved from further statements by `Breakdown.scaledScale_of`.

**Physical evolution from similarity time.** The physical-orbit proposition requires a continuous similarity-time mild trajectory with positive scaling exponent to yield a physical mild solution before time one. (`Breakdown.ScaledOrbitPhysicalStatement`)

Proved by `Breakdown.scaledOrbitPhysical`. Also proved from further statements by `Breakdown.scaledOrbitPhysical_of`.

**Bounded recurrent orbit.** The orbit-bound proposition requires every recurrent orbit with positive scaling exponent to have a uniform norm bound. (`Breakdown.ScaledOrbitBoundStatement`)

Proved by `Breakdown.scaledOrbitBound`.

**Orbit norm bounded away from zero.** The orbit-norm proposition requires a recurrent nonzero orbit in a commuting scaled framework to have a positive uniform norm lower bound. (`Breakdown.ScaledOrbitNormStatement`)

Proved by `Breakdown.scaledOrbitNorm`. Also proved from further statements by `Breakdown.scaledOrbitNorm_of`.

**Matching and bounds for profile pieces.** The profile-piece proposition records the pieces' mild equation, endpoint matching, recurrence by isometry and exponential norm bound under its orbit hypotheses. (`Breakdown.ScaledProfilePieceStatement`)

Proved by `Breakdown.scaledProfilePiece`. Also proved from further statements by `Breakdown.scaledProfilePiece_of`.

**Gluing geometrically shrinking pieces.** The gluing proposition requires matching mild pieces with ratio between zero and one to form a mild solution with the stated rescaled-value identity. (`Breakdown.ScaledGlueStatement`)

Proved by `Breakdown.scaledGlue`. Also proved from further statements by `Breakdown.scaledGlue_of`.

**Finite-dimensional step correction.** The step-data proposition requests a sufficiently short step, a contraction weight, a finite-dimensional correction and a bounded right inverse for the piece recurrence. (`Breakdown.ScaledStepDataStatement`)

Proved by `Breakdown.scaledStepData`. Also proved from further statements by `Breakdown.scaledStepData_of`.

**Monodromy as a compact perturbation.** The monodromy proposition records uniformly bounded step inverses, recurrence by conjugation and a compact difference from a decaying free period map. (`Breakdown.ScaledMonodromyStatement`)

Proved by `Breakdown.scaledMonodromy`. Also proved from further statements by `Breakdown.scaledMonodromy_of`.

**Transfer the orbit to dense data.** The transfer proposition requests arbitrarily close initial data from a dense subspace and a mild solution converging to the orbit at a positive power rate in similarity variables. (`Breakdown.ScaledTransferHolds`)

Proved by `Breakdown.scaledTransferHolds`. Also proved from further statements by `Breakdown.scaledTransferHolds_of`.

### Breakdown.Frac.ScaledStepData

This file packages a recurrent orbit into the scaled step data required by the abstract transfer argument.

**Choose sufficiently small time steps.** For any positive target time, a positive step count makes both the step length and the displayed bilinear size expression small enough. (`Breakdown.FracInternal.exists_scaled_step_count`)

**Assemble scaled step data.** The monodromy, profile piece, orbit bound, piece operator, periodic inverse, section, and dichotomy hypotheses give a commuting recurrent orbit in a positive exponent framework arbitrarily short steps, a weight θ below one and above both prescribed scale powers, and a bounded recurrence right inverse with a finite dimensional initial correction mapped into the prescribed dense subspace. (`Breakdown.scaledStepData_of`)

### Breakdown.Frac.SpaceDecay

This file establishes compact field decay needed when realizing fractional operators in the whole space uniqueness route.

**Far-field Taylor remainder bound.** For increments of norm at least one, the second-order remainder is bounded by the translated value and local derivative norms times the increment square. (`_private.Breakdown.Frac.SpaceDecay.0.Breakdown.FracInternal.decayRemainderFar`)

**Remainder outside the support.** Outside a closed ball containing the support, the second-order remainder equals the translated field value. (`_private.Breakdown.Frac.SpaceDecay.0.Breakdown.FracInternal.decayRemainderOff`)

**Decay of a compact fractional image.** For 1 < α < 3/2, the fractional power of every smooth compactly supported vector field is continuous and bounded by a constant times (1 + radius) raised to −(3 + 2α). (`Breakdown.fracCompactDecay`)

### Breakdown.Frac.SpaceDifference

This file derives the localized difference estimates that compare two smooth whole space fractional solutions.

**Absorb a cubic product.** For nonnegative factors, the coefficient times a cubic power times another factor is bounded by the stated two fourth powers. (`Breakdown.FracDifferenceInternal.cube_mul_le_fourth`)

**Cubic power between quadratic and sixth.** Every real cubic power is bounded by the sum of the corresponding second and sixth powers. (`Breakdown.FracDifferenceInternal.pow_three_le_sum`)

**Fourth power between second and sixth.** Every real fourth power is bounded by the sum of the corresponding second and sixth powers. (`Breakdown.FracDifferenceInternal.pow_four_le_sum`)

**Three-halves power via a square root.** For a nonnegative real number, its three-halves power equals the cube of its square root. (`Breakdown.FracDifferenceInternal.rpow_three_halves_eq`)

**Absorb the cubic cutoff error.** Under the stated nonnegativity and Sobolev-size bound, the cubic cutoff term is absorbed into one eighth of dissipation plus the displayed inverse-radius error. (`Breakdown.FracDifferenceInternal.cubic_absorb`)

**Absorb the quadratic cutoff error.** Under the stated sign, radius and Sobolev-size bounds, the quadratic cutoff term is absorbed into one eighth of dissipation plus the displayed remainder. (`Breakdown.FracDifferenceInternal.quad_absorb`)

**Integrable cutoff transport term.** For positive radius and continuous fields, the cutoff transport integrand is integrable. (`Breakdown.FracDifferenceInternal.integrable_transport`)

**Combine localized energy estimates.** The stated lower, transport, stretching and pressure estimates combine into the displayed localized energy upper bound with inverse-radius error. (`Breakdown.FracDifferenceInternal.combine_bounds`)

**Derive the difference estimate.** The cutoff dissipation lower bound, L⁶ bound, and gradient bound hypotheses imply that, for 1 < α < 5/4 and admissible difference data, the localized difference expression is at most twice the reference gradient bound times cutoff energy plus K(1 + U₀)(A² + A⁶)/r for all sufficiently large radii. (`Breakdown.fracDifference_of`)

### Breakdown.Frac.SpaceEnergy

This file supplies the local energy identity for whole space forced solutions, feeding the fractional difference argument.

**Continuous localized energy.** For two smooth fields on the closed time interval and positive cutoff radius, their localized difference energy is continuous in time. (`_private.Breakdown.Frac.SpaceEnergy.0.Breakdown.FracInternal.SpaceEnergy.continuousOn_energy_of_smooth`)

**Differentiate localized energy.** At an interior time, the localized difference energy has derivative given by its cutoff-weighted pairing with the difference of time derivatives. (`_private.Breakdown.Frac.SpaceEnergy.0.Breakdown.FracInternal.SpaceEnergy.hasDerivAt_energy_of_smooth`)

**Supply the local energy identity.** For two forced solutions and any positive cutoff radius, their difference cutoff energy is continuous on the closed time interval and has the stated interior derivative comprising the force difference, cutoff transport, reference velocity gradient, and pressure difference pairings. (`Breakdown.forcedLocalEnergy`)

### Breakdown.Frac.SpaceExports

This file assembles the whole space fractional energy, pressure, uniqueness, and final obstruction interfaces from their analytic providers.

**Supply the pressure difference.** For two energy bounded forced solutions, the cutoff pairing of their pressure gradient difference with the velocity difference equals the sum of the quadratic difference and two mixed stress pairings against the Newtonian potential of the cutoff divergence source at every interior time and positive radius. (`Breakdown.FracInternal.SpaceAssembly.pressureDifference`)

**Supply the fractional forced identity.** For 1 < α < 3/2, an energy bounded smooth fractional solution on a finite interval also satisfies the forced solution conditions with forcing equal to its fractional power. (`Breakdown.FracInternal.SpaceAssembly.forced`)

**Supply the gradient bound.** For 1 < α < 3/2 and a smooth compactly supported field, fractional dissipation is nonnegative and its total squared gradient integral is bounded by its squared L² mass plus that dissipation. (`Breakdown.FracInternal.SpaceAssembly.gradientBound`)

**Supply the difference estimate.** For 1 < α < 5/4 and admissible difference data, the localized difference expression is bounded by twice the reference gradient bound times cutoff energy plus K(1 + U₀)(A² + A⁶)/r for all sufficiently large cutoff radii. (`Breakdown.FracInternal.SpaceAssembly.difference`)

**Supply fractional uniqueness.** For 1 < α < 5/4, two energy bounded smooth fractional solutions on the same closed interval with identical initial velocity agree at every time whenever one solution has a uniform gradient bound. (`Breakdown.FracInternal.SpaceAssembly.uniqueness`)

**Assemble the heat-integral estimate.** For α > 1, the fractional heat convolution of a jointly measurable source uniformly bounded in Hⁿ gains one derivative on every forward interval of length at most one, with squared Hⁿ⁺¹ norm bounded by C times the interval length times the source bound. (`Breakdown.FracInternal.SpaceAssembly.heatIntegral`)

**Assemble the symbol fixed point.** For α > 1, each m ≥ 3 and Sobolev size bound admit a common positive time on which every measurable solenoidal datum has an Hᵐ fixed point of the fractional mild map almost everywhere that retains Fourier conjugate symmetry. (`Breakdown.FracInternal.SpaceAssembly.fixedPoint`)

**Assemble local symbol existence.** For α > 1, every m ≥ 3 and Sobolev size bound admit a common positive time on which each measurable solenoidal datum has an Hᵐ fractional mild symbol solution with the exact initial value and solenoidality at every time. (`Breakdown.FracInternal.SpaceAssembly.localExistence`)

**Assemble persistence of regularity.** For 1 < α < 3/2, every finite initial Hᵐ norm with m ≥ 3 persists along a solenoidal H³ fractional mild symbol curve, which is therefore an Hᵐ curve on the same interval. (`Breakdown.FracInternal.SpaceAssembly.persist`)

**Assemble the a priori symbol bound.** For 1 < α < 3/2 and m ≥ 3, a bound on initial Hᵐ norm squared and a uniform homogeneous H¹ bound give a uniform Hᵐ bound for all solenoidal mild symbol curves whose time intervals have a fixed upper length bound. (`Breakdown.FracInternal.SpaceAssembly.apriori`)

**Assemble the fractional symbol flow.** For 1 < α < 3/2, an H³ fractional symbol flow propagates every finite initial Sobolev order and extends measurable solenoidal H³ data to any T > 0 whenever all shorter flows share a homogeneous H¹ bound. (`Breakdown.FracInternal.SpaceAssembly.flow`)

**Assemble physical bilinear identity.** For α > 1 and a measurable solenoidal symbol finite in every Sobolev order, the fractional bilinear operator applied twice to its embedded physical field equals almost everywhere the source heat factor times its nonlinear symbol at every positive heat time. (`Breakdown.FracInternal.SpaceAssembly.bilinPhys`)

**Assemble mild-symbol identification.** For 1 < α < 3/2, embedding the physical field of an all order Sobolev solenoidal fractional mild symbol curve gives a fractional X-valued mild trajectory on the same positive interval. (`Breakdown.FracInternal.SpaceAssembly.identify`)

**Assemble weighted curve regularity.** For 1 < α < 3/2, every all order Sobolev solenoidal fractional mild symbol curve is smooth in each natural weighted L¹ space, with derivative within its positive closed time interval represented by the fractional time derivative symbol. (`Breakdown.FracInternal.SpaceAssembly.weightCurve`)

**Assemble the physical solution.** For 1 < α < 3/2, the physical velocity and pressure reconstructed from an all order Sobolev solenoidal mild symbol curve form a smooth fractional solution with zero divergence and the momentum equation at interior times of its positive closed interval. (`Breakdown.FracInternal.SpaceAssembly.solutionOn`)

**Assemble fractional mild regularity.** For 1 < α < 3/2, a mild trajectory in the matching fractional framework starting from a test field on [0,T], T > 0, has a smooth fractional velocity–pressure realization with that initial datum, bounded energy and gradient, and velocity agreeing almost everywhere with the trajectory at every time. (`Breakdown.FracInternal.SpaceAssembly.mildRegular`)

**Supply the self-similar weak equation.** For 1 < α < 5/4, each unit viscosity rotating fractional profile gives a physical self similar field satisfying the fractional weak equation on every interval [0,T] with 0 < T < 1, for every initial similarity phase. (`Breakdown.FracInternal.SpaceAssembly.selfSimilarWeak`)

**Obtain the fractional profile orbit.** Assuming weak fractional solutions yield mild X trajectories for every 1 < α < 5/4, the embedded rotating slices of any unit viscosity profile form a recurrent orbit of every matching fractional framework, with arbitrary positive period P′ and symmetry given by axial rotation through −aP′. (`Breakdown.FracInternal.SpaceAssembly.profileOrbit_of_mild`)

**Obtain a fractional mild blow-up flow.** Assuming weak fractional solutions yield mild X trajectories throughout 1 < α < 5/4, a rotating profile provides a matching scaled framework and, arbitrarily close to its embedded velocity, compact test initial data whose mild trajectories approach its rotating slices after dilation at a positive power rate as t tends to one. (`Breakdown.FracInternal.SpaceAssembly.mildBlowup_of_mild`)

**Unit-viscosity breakdown from mildness.** For 1 < α < 5/4, assuming the weak to mild implication throughout that exponent range, existence of a rotating fractional profile gives smooth compactly supported divergence free initial data admitting no global unit viscosity smooth fractional solution with one energy bound uniform over all nonnegative times. (`Breakdown.FracInternal.SpaceAssembly.unitBreakdown_of_mild`)

**Space breakdown from a profile.** For one less than α less than five quarters, a rotating fractional profile and the stated weak-to-mild implication yield fractional whole-space breakdown. (`Breakdown.FracInternal.SpaceAssembly.breakdownOnSpace_of_mild`)

**Supply the weak-to-mild implication.** For 1 < α < 3/2 and a < b, embedding each time slice of a weak fractional solution produces an X-valued fractional mild trajectory on [a,b]. (`Breakdown.FracInternal.SpaceAssembly.mildOfWeak`)

### Breakdown.Frac.SpaceForced

This file places a fractional solution into the forced solution framework used to analyze pressure and localized energy.

**Finite energy gives L² membership.** A continuous field with the stated finite square-integral bound belongs to L². (`Breakdown.FracInternal.Forced.memLp_of_energy`)

**Smoothness of the time derivative.** The time derivative of a jointly smooth field is spatially smooth at each interior time. (`Breakdown.FracInternal.Forced.contDiff_timeDeriv`)

**Smoothness of the pressure gradient.** The gradient of a smooth scalar field is smooth. (`Breakdown.FracInternal.Forced.contDiff_gradient`)

**Smoothness of the advection field.** The self-advection of a smooth vector field is smooth. (`Breakdown.FracInternal.Forced.contDiff_advection`)

**Integrate a gradient pairing by parts.** Pairing a smooth vector field with the gradient of a compactly supported smooth scalar equals minus its divergence paired with the scalar. (`Breakdown.FracInternal.Forced.integral_inner_gradient_test`)

**Turn weak divergence into zero.** A smooth field whose pairing with every compactly supported smooth gradient vanishes has pointwise zero divergence. (`Breakdown.FracInternal.Forced.divergence_eq_zero_of_weak`)

**Recover the fractional forced equation.** The compact symmetry, weak solenoidality, weak continuity, mollifier pairing, and remainder integrability hypotheses imply that every energy bounded smooth fractional solution with 1 < α < 3/2 satisfies the forced solution conditions with its fractional power as forcing. (`Breakdown.fracForced_of`)

### Breakdown.Frac.SpaceGradient

This file bounds whole space gradient energy using fractional dissipation and the interpolation estimates needed by uniqueness.

**Complexification preserves the norm.** The norm of a real vector equals the norm of its complexification. (`Breakdown.FracInternal.SpaceGradient.norm_cvec`)

**Complexification preserves pairing.** The complex inner product of two complexified real vectors equals the complexification of their real inner product. (`Breakdown.FracInternal.SpaceGradient.inner_cvec`)

**Complex Schwartz test field.** A smooth compactly supported real field is complexified and packaged as a Schwartz map. (`Breakdown.FracInternal.SpaceGradient.complexTest`)

**Underlying complex test function.** The underlying Schwartz test function is the pointwise complexification of the original field. (`Breakdown.FracInternal.SpaceGradient.coe_complexTest`)

**Integrable Schwartz norm square.** The square norm of a complex Schwartz field is integrable. (`Breakdown.FracInternal.SpaceGradient.integrable_norm_sq`)

**Coordinate squares give the norm.** The sum of the three coordinate squares equals the real vector's norm square. (`Breakdown.FracInternal.SpaceGradient.sum_sq_coord`)

**Fourier norm of a partial derivative.** The squared Fourier norm of a coordinate derivative equals the symbol norm square times the squared coordinate frequency and the Fourier normalization factor. (`Breakdown.FracInternal.SpaceGradient.norm_sq_transform_pd`)

**Fourier formula for gradient energy.** For a smooth compactly supported field, its total gradient square integral equals the frequency-square-weighted Fourier norm integral. (`Breakdown.FracInternal.SpaceGradient.integral_grad_eq`)

**Fourier formula for field energy.** For a smooth compactly supported field, the physical and Fourier square integrals agree. (`Breakdown.FracInternal.SpaceGradient.integral_norm_eq`)

**Almost every frequency is nonzero.** The frequency vector is nonzero almost everywhere for spatial volume measure. (`Breakdown.FracInternal.SpaceGradient.ae_ne_zero`)

**Control fractional growth cubically.** For one less than α less than three halves and nonnegative frequency, the fractional power is bounded by one plus the frequency cube. (`Breakdown.FracInternal.SpaceGradient.rpow_le_cube`)

**Control the gradient by dissipation.** For α greater than one and nonnegative frequency, its square is bounded by one plus its fractional dissipation power. (`Breakdown.FracInternal.SpaceGradient.sq_le_rpow`)

**Fourier pairing against a Schwartz map.** Pairing the Fourier transform of an integrable field with a transformed Schwartz map equals their physical-space pairing. (`Breakdown.FracInternal.SpaceGradient.sesq_swap`)

**Fourier integral default is zero.** The integral-defined Fourier transform of a nonintegrable function is zero at every frequency. (`Breakdown.FracInternal.SpaceGradient.transform_undef`)

**Fourier symbol of the fractional image.** Under the symbol interface and the stated exponent and test-field assumptions, the fractional image has the prescribed Fourier multiplier. (`Breakdown.FracInternal.SpaceGradient.symbol_apply`)

**Fractional energy in Fourier variables.** Under the symbol interface and stated test-field assumptions, the field's fractional pairing equals its dissipation-weighted Fourier norm square integral. (`Breakdown.FracInternal.SpaceGradient.pairing_eq`)

**Integrable fractional Schwartz weight.** For one less than α less than three halves, a Schwartz symbol's fractional weighted norm square is integrable. (`Breakdown.FracInternal.SpaceGradient.integrable_weight`)

**Derive the fractional gradient bound.** The Fourier symbol hypothesis implies that, for 1 < α < 3/2 and every smooth compactly supported field, fractional dissipation is nonnegative and controls the total squared gradient integral up to the field's squared L² mass. (`Breakdown.fracGradientBound_of`)

### Breakdown.Frac.SpaceLocalization

This file develops the truncated remainder and kernel identities used to localize fractional dissipation in the whole space energy argument.

**Add scalar Taylor remainders.** For twice differentiable scalar fields, the remainder of a sum equals the sum of the remainders. (`Breakdown.FracInternal.Localization.remS_add`)

**Scale a scalar Taylor remainder.** For a twice differentiable scalar field, multiplying by a constant multiplies its remainder by that constant. (`Breakdown.FracInternal.Localization.remS_const_mul`)

**The remainder of a constant vanishes.** A constant scalar field has zero second-order remainder. (`Breakdown.FracInternal.Localization.remS_const`)

**Move a linear map through a remainder.** Applying a continuous linear functional to a twice differentiable vector field commutes with its second-order remainder. (`Breakdown.FracInternal.Localization.remS_comp`)

**Remainder of an affine combination.** The second-order remainder of the displayed affine combination is the corresponding linear combination of the four remainders. (`Breakdown.FracInternal.Localization.remS_comb`)

**Pair term for localization.** The pair term combines cutoff differences and vector pairings with the compensating cutoff-square contribution. (`Breakdown.FracInternal.Localization.pairTerm`)

**Integrate the pair remainder.** The pair remainder integral applies the singular fractional kernel to the scalar second-order remainder of the localization pair term. (`Breakdown.FracInternal.Localization.pairRemainderIntegral`)

**Smoothness includes two derivatives.** The finite smoothness order two lies below the smooth order used here. (`Breakdown.FracInternal.Localization.two_le_top`)

**Integrable scalar fractional remainder.** For one less than α less than three halves, a smooth compactly supported scalar field has an integrable singularly weighted remainder. (`Breakdown.FracInternal.Localization.scalar_integrable`)

**Integrable paired vector remainder.** For the stated exponent range, a smooth L² vector field paired with a fixed vector has an integrable singularly weighted scalar remainder. (`Breakdown.FracInternal.Localization.vector_scalar_integrable`)

**Pair the fractional image with a vector.** For a smooth L² field in the stated exponent range, pairing its fractional image with a fixed vector equals the normalized scalar remainder integral. (`Breakdown.FracInternal.Localization.vector_pairing`)

**Pointwise localization identity.** For the stated smooth fields, cutoff and exponent range, the difference of localized fractional pairings equals the normalized pair remainder integral. (`Breakdown.FracInternal.Localization.pointwise_split`)

**Integrable localization pair remainder.** For the stated smoothness, compact-cutoff and exponent assumptions, the weighted pair remainder is integrable at each base point. (`Breakdown.FracInternal.Localization.pair_integrable`)

**Nonnegative localization square.** The pair square multiplies the squared cutoff difference and squared field difference by the singular distance kernel. (`Breakdown.FracInternal.Localization.pairSquare`)

**Increments away from the origin.** The far-increment set contains vectors whose norm exceeds the cutoff distance. (`Breakdown.FracInternal.Localization.farSet`)

**Pairs away from the diagonal.** The far-pair set contains pairs whose separation exceeds the cutoff distance. (`Breakdown.FracInternal.Localization.farPairs`)

**Truncated pair remainder integral.** The tail integral restricts the weighted pair remainder to increments beyond the cutoff distance. (`Breakdown.FracInternal.Localization.tailIntegral`)

**Measurability of far increments.** The far-increment set is measurable. (`Breakdown.FracInternal.Localization.farSet_measurable`)

**Measurability of separated pairs.** The set of pairs separated beyond the cutoff distance is measurable. (`Breakdown.FracInternal.Localization.farPairs_measurable`)

**Integrable far-field power.** A radial power with exponent below minus three is integrable outside any positive radius. (`Breakdown.FracInternal.Localization.farSet_rpow_integrable`)

**Linear part of the pair term.** The linear pair term is its first derivative at the base point applied to the increment. (`Breakdown.FracInternal.Localization.linPart`)

**Quadratic part of the pair term.** The quadratic pair term is half its second derivative applied twice to the increment. (`Breakdown.FracInternal.Localization.quadPart`)

**Integrable linear tail term.** For α greater than one and positive truncation radius, the weighted linear pair term is integrable in the far region. (`Breakdown.FracInternal.Localization.lin_far_integrable`)

**Integrable quadratic tail term.** For α greater than one and positive truncation radius, the weighted quadratic pair term is integrable in the far region. (`Breakdown.FracInternal.Localization.quad_far_integrable`)

**The linear tail integral vanishes.** For α greater than one and positive truncation radius, the weighted linear term integrates to zero over the far region. (`Breakdown.FracInternal.Localization.lin_vanish`)

**The pair term vanishes on the diagonal.** At equal arguments, the localization pair term is zero. (`Breakdown.FracInternal.Localization.pairTerm_self`)

**Symmetrize the localization pair.** Adding the pair term in both orders gives minus one half of the product of the cutoff-difference square and the field-difference square. (`Breakdown.FracInternal.Localization.pairTerm_symm`)

**Bound the localization pair term.** A uniform cutoff bound controls the absolute pair term by three times the squared cutoff bound times the two field norm squares. (`Breakdown.FracInternal.Localization.pairTerm_bound`)

**Integrability of the separated pair term.** A smooth L² field and compact smooth cutoff give an integrable weighted pair term away from the diagonal in the stated exponent range. (`Breakdown.FracInternal.Localization.far_pair_integrable`)

**Expanded quadratic pair term.** The expanded quadratic term records the cutoff gradient square, cutoff Hessian and derivative of the field norm square. (`Breakdown.FracInternal.Localization.quadExplicit`)

**Expand the pair's quadratic part.** For smooth field and cutoff, the quadratic pair term equals the displayed derivative expansion. (`Breakdown.FracInternal.Localization.quad_formula`)

**A primitive for the quadratic term.** The quadratic auxiliary field is the cutoff times its directional derivative times the field norm square. (`Breakdown.FracInternal.Localization.quadField`)

**Write the quadratic term as a derivative.** For smooth inputs, the expanded quadratic term is half the directional derivative of the auxiliary field. (`Breakdown.FracInternal.Localization.quadField_deriv`)

**The integrated quadratic tail vanishes.** Under the stated smoothness, energy, support and exponent assumptions, the integrated quadratic tail is integrable and has zero integral. (`Breakdown.FracInternal.Localization.quad_vanish`)

**Uniform Taylor remainder bounds.** A smooth compactly supported vector field has uniform cubic and quadratic-growth bounds for its second-order remainder. (`Breakdown.FracInternal.Localization.rem_uniform`)

**Near and far domination kernel.** The kernel profile uses the cubic remainder power inside the unit ball and three times the quadratic remainder power outside it. (`Breakdown.FracInternal.Localization.kernelProfile`)

**The domination kernel is integrable.** For one less than α less than three halves, the near-and-far kernel profile is integrable. (`Breakdown.FracInternal.Localization.kernelProfile_integrable`)

**Dominate the weighted remainder.** The stated cubic and quadratic-growth bounds imply domination of the singularly weighted quantity by the kernel profile. (`Breakdown.FracInternal.Localization.kernel_le_profile`)

**An integrable bound for pair remainders.** Under the stated assumptions, the absolute pair remainder integral is bounded at every base point by an integrable function. (`Breakdown.FracInternal.Localization.remainder_dominated`)

**Truncated localization identity.** For positive truncation radius and the stated field and cutoff assumptions, the truncated pair integral equals minus one quarter of the separated pair-square integral. (`Breakdown.FracInternal.Localization.truncated_identity`)

**Cutoff radii tend to zero.** The reciprocal sequence one over n plus one eventually falls below every positive radius. (`Breakdown.FracInternal.Localization.eventually_far`)

**Remove the small-distance truncation.** For the stated smooth inputs and exponent range, the truncated pair integral converges pointwise to the full remainder integral. (`Breakdown.FracInternal.Localization.tail_tendsto`)

**Global localization square identity.** Under the stated assumptions, the global pair remainder integral equals minus one quarter of the integrable pair-square integral. (`Breakdown.FracInternal.Localization.global_split`)

**Supply fractional localization.** For 1 < α < 3/2, a smooth L² field and a smooth compact cutoff satisfy the stated localization identity: the pairing with the fractional image of the squared cutoff field equals the cutoff field's dissipation plus the scalar cutoff correction minus the normalized, integrable double integral of squared cutoff and field differences. (`Breakdown.fracLocalization`)

### Breakdown.Frac.SpaceLowerBound

This file proves a lower bound for localized fractional dissipation, connecting cutoff errors to the whole space difference estimate.

**Extract two derivatives from smoothness.** A smooth scalar field is twice continuously differentiable. (`Breakdown.SpaceLowerBound.Internal.contDiff_two_of`)

**The first coordinate vector is nonzero.** The first standard coordinate vector is nonzero. (`Breakdown.SpaceLowerBound.Internal.unitVector_zero_ne`)

**The first coordinate vector has norm one.** The first standard coordinate vector has norm one. (`Breakdown.SpaceLowerBound.Internal.norm_unitVector_zero`)

**Remainder along a constant vector.** For a twice differentiable scalar field, its product with a fixed vector has that vector times the scalar remainder. (`Breakdown.SpaceLowerBound.Internal.remainder_smul_const`)

**Fractional power along a constant vector.** The fractional operator on a scalar field times a fixed vector equals the scalar fractional operator times that vector. (`Breakdown.SpaceLowerBound.Internal.power_smul_const`)

**Scalar dilation covariance.** The covariance interface gives the stated fractional scaling law for a twice differentiable scalar field under positive spatial dilation. (`Breakdown.SpaceLowerBound.Internal.scalar_comp_smul`)

**Bound the scalar fractional image.** The compact-decay interface bounds the fractional image of a smooth compactly supported scalar field in the stated exponent range. (`Breakdown.SpaceLowerBound.Internal.scalar_bounded`)

**Rescale the radial cutoff.** For positive radius, the radial cutoff is the unit cutoff evaluated at the inverse-radius dilation. (`Breakdown.SpaceLowerBound.Internal.radialCutoff_eq_scale`)

**Bound the scalar cutoff commutator.** The compact-decay and covariance interfaces bound the scalar cutoff commutator by a constant divided by the radius square. (`Breakdown.SpaceLowerBound.Internal.scalar_term_bound`)

**Near-and-far radial error kernel.** The radial error kernel uses its specified singular power below unit distance and its specified decay power above unit distance. (`Breakdown.SpaceLowerBound.Internal.nearFarKernel`)

**Truncated fourth-power kernel.** The near kernel is the inverse fourth power below unit distance and zero elsewhere. (`Breakdown.SpaceLowerBound.Internal.nearKernel`)

**Nonnegative radial error kernel.** At nonnegative distance, the near-and-far radial error kernel is nonnegative. (`Breakdown.SpaceLowerBound.Internal.nearFarKernel_nonneg`)

**Nonnegative near kernel.** At nonnegative distance, the truncated near kernel is nonnegative. (`Breakdown.SpaceLowerBound.Internal.nearKernel_nonneg`)

**Weighted arithmetic–geometric bound.** If the square of one factor equals the product of a positive weight and a second factor, the displayed cross term is bounded by the weighted square plus that factor. (`Breakdown.SpaceLowerBound.Internal.amgm_step`)

**Bound a squared vector difference.** The squared norm of a vector difference is at most twice the sum of the separate squared norms. (`Breakdown.SpaceLowerBound.Internal.sq_norm_sub_le`)

**Pointwise cutoff-pair estimate.** For one less than α less than five quarters, the stated Lipschitz cutoff bound controls the localization pair square by the near gradient term and far energy term. (`Breakdown.SpaceLowerBound.Internal.pointwise_bound`)

**Square of an interval average.** For a continuous scalar function on the unit interval, the square of its integral is bounded by its square integral. (`Breakdown.SpaceLowerBound.Internal.sq_integral_le`)

**Control a linear map by its columns.** A linear map's value square is bounded by the input norm square times the sum of the coordinate-column norm squares. (`Breakdown.SpaceLowerBound.Internal.norm_apply_sq_le`)

**Translation difference by gradients.** The squared difference of a smooth field across a translation is bounded by the translation square times the gradient-square average along the segment. (`Breakdown.SpaceLowerBound.Internal.pointwise_translation`)

**Integrated translation estimate.** For a smooth compactly supported field, the square integral of a translation difference is bounded by the translation norm square times total gradient energy. (`Breakdown.SpaceLowerBound.Internal.translation_bound`)

**Measurable near kernel.** The truncated near kernel is measurable. (`Breakdown.SpaceLowerBound.Internal.measurable_nearKernel`)

**Measurable near-and-far kernel.** The near-and-far radial error kernel is measurable. (`Breakdown.SpaceLowerBound.Internal.measurable_nearFarKernel`)

**Integrable radial error kernel.** For one less than α less than five quarters, the radial near-and-far error kernel is integrable in space. (`Breakdown.SpaceLowerBound.Internal.integrable_nearFarKernel`)

**Integrable compensated near kernel.** Multiplying the near kernel by distance squared gives an integrable spatial kernel. (`Breakdown.SpaceLowerBound.Internal.integrable_nearKernel_sq`)

**Bound the first far-field energy term.** For a continuous field with the stated energy bound, the two-variable far term using its first value is controlled by the kernel integral times that bound. (`Breakdown.SpaceLowerBound.Internal.far_term_left`)

**Bound the second far-field energy term.** For a continuous field with the stated energy bound, the two-variable far term using its second value is controlled by the kernel integral times that bound. (`Breakdown.SpaceLowerBound.Internal.far_term_right`)

**Bound the near difference term.** For a smooth compactly supported field, the near-kernel difference square integral is bounded by the compensated kernel integral times gradient energy. (`Breakdown.SpaceLowerBound.Internal.near_term`)

**Integrated cutoff-pair estimate.** For one less than α less than five quarters, the localized pair-square integral is bounded by an inverse-radius-square multiple of energy and localized gradient energy. (`Breakdown.SpaceLowerBound.Internal.pair_term_bound`)

**Bound the squared norm integral.** A continuous field with the stated nonnegative square-integral bound has an integrable norm square with the same real integral bound. (`Breakdown.SpaceLowerBound.Internal.integrable_sq_of_lintegral`)

**Derive the cutoff lower bound.** The localization, gradient control, compact decay, and covariance hypotheses imply that, for 1 < α < 5/4, a smooth field with L² mass at most a² has its cutoff fractional pairing bounded below by three quarters of the cutoff dissipation minus Ca²/r² once the radius is sufficiently large. (`Breakdown.fracCutoffLowerBound_of`)

### Breakdown.Frac.SpaceMollify

This file controls mollified test pairings for the fractional power, supporting the forced pressure and uniqueness analysis.

**Third derivative of a broad mollifier.** A compact smooth test field has mollifications whose third derivatives are uniformly bounded by a constant times the inverse sixth power of the scale. (`_private.Breakdown.Frac.SpaceMollify.0.Breakdown.FracInternal.mollifyPairing_third_bound`)

**Norm of the singular kernel action.** The norm of the singular radial weight acting on a vector is that nonnegative weight times the vector norm. (`_private.Breakdown.Frac.SpaceMollify.0.Breakdown.FracInternal.mollifyPairing_norm_kernel_smul`)

**Far-field remainder estimate.** For increments of norm at least one, the second-order remainder is bounded by the translated value and local derivatives times the increment square. (`_private.Breakdown.Frac.SpaceMollify.0.Breakdown.FracInternal.mollifyPairing_remainder_far`)

**Uniform fractional bound for mollifiers.** For the stated exponent range, the fractional image of a large-scale mollification is bounded uniformly by a constant times the inverse scale cubed. (`_private.Breakdown.Frac.SpaceMollify.0.Breakdown.FracInternal.mollifyPairing_uniform`)

**Far decay of mollified fractional images.** For α greater than one, the fractional image of a sufficiently large mollification has the stated radial decay beyond the enlarged support region. (`_private.Breakdown.Frac.SpaceMollify.0.Breakdown.FracInternal.mollifyPairing_far`)

**Bound an integral pairing by squares.** An integrable square bound on each field gives the displayed pairing bound with any positive balancing parameter. (`_private.Breakdown.Frac.SpaceMollify.0.Breakdown.FracInternal.mollifyPairing_abs_le`)

**An integrable bound for mollifiers.** For sufficiently large mollification scale and the stated exponent range, the fractional image has an integrable square majorant whose integral decays inversely with scale. (`_private.Breakdown.Frac.SpaceMollify.0.Breakdown.FracInternal.mollifyPairing_sq_bound`)

**Supply the mollifier-pairing limit.** For 1 < α < 3/2, a smooth compact test field, an L² mass bound A, and ε > 0, sufficiently broad mollification makes the absolute pairing of its fractional power with every continuous field of mass at most A no larger than ε. (`Breakdown.fracMollifyPairing`)

### Breakdown.Frac.SpaceOrbitRate

This file turns the size and scaling of a recurrent fractional orbit into an obstruction to a continuous physical extension through the terminal time.

**A rotation preserves a centered ball.** The inverse image of a centered ball under a linear isometry is the same ball. (`_private.Breakdown.Frac.SpaceOrbitRate.0.Breakdown.ballPreimageRot`)

**Rotations preserve local L⁶ norms.** For a measurable field, pushforward by a linear isometry preserves its L⁶ norm on a centered ball. (`_private.Breakdown.Frac.SpaceOrbitRate.0.Breakdown.ballNormRot`)

**Rotations preserve velocity ball norms.** Rotating an element of X preserves the reconstructed velocity's L⁶ norm on each centered ball. (`_private.Breakdown.Frac.SpaceOrbitRate.0.Breakdown.ballNormVelRot`)

**A nonzero field is detected on a ball.** A measurable field that is not almost everywhere zero has nonzero L⁶ norm on some ball of natural radius. (`_private.Breakdown.Frac.SpaceOrbitRate.0.Breakdown.someBallNormNeZero`)

**Scale almost everywhere equality.** Positive fractional scaling preserves almost-everywhere equality of fields. (`_private.Breakdown.Frac.SpaceOrbitRate.0.Breakdown.scaleFieldAeCongr`)

**A local bound after fractional scaling.** For positive α and scale at most one, a bound on a centered closed ball yields the stated power-scaled bound on the open ball. (`_private.Breakdown.Frac.SpaceOrbitRate.0.Breakdown.scaleFieldNormLe`)

**Control an orbit value on a ball.** The dilation and velocity-norm bounds control a target velocity's local L⁶ norm by the X approximation error plus the scaled physical bound. (`_private.Breakdown.Frac.SpaceOrbitRate.0.Breakdown.ballNormStep`)

**Local L⁶ norm after recurrence.** Recurrence by rotation preserves the velocity's local L⁶ norm after every natural number of periods. (`_private.Breakdown.Frac.SpaceOrbitRate.0.Breakdown.periodicBallNorm`)

**Exponential decay forces zero.** A fixed extended nonnegative quantity bounded at every recurrence step by the stated two decaying terms must be zero. (`_private.Breakdown.Frac.SpaceOrbitRate.0.Breakdown.limitForcesZero`)

**Exclude the bounded orbit-rate scenario.** For 1 < α < 5/4, the velocity dilation hypothesis rules out any jointly continuous physical velocity on [0,1] whose slices agree almost everywhere with an X trajectory that approaches a nonzero recurrent orbit after dilation at a positive power rate as t tends to one. (`Breakdown.fracOrbitRateFalse`)

### Breakdown.Frac.SpacePressureAverage

This file removes the remaining pressure defect by spatial averaging in the whole space forced solution argument.

**Absolute value of three terms.** The absolute value of two terms added and a third subtracted is bounded by the sum of their absolute values. (`_private.Breakdown.Frac.SpacePressureAverage.0.Breakdown.FracInternal.SpacePressureAverage.abs_add_sub_le_three`)

**Uniform energy bound on the interval.** A jointly smooth field with bounded energy has a nonnegative uniform bound on the integrable norm squares of all time slices. (`_private.Breakdown.Frac.SpacePressureAverage.0.Breakdown.FracInternal.SpacePressureAverage.energy_bound`)

**Bound the integrated pressure defect.** The forced time identity and the stated pairing bounds control the time-integrated pressure defect by twice the endpoint bound plus the interval length times the forcing bound. (`_private.Breakdown.Frac.SpacePressureAverage.0.Breakdown.FracInternal.SpacePressureAverage.abs_integral_le`)

**Derive pressure-average control.** The forced time identity and pressure continuity hypotheses imply that, for an energy bounded forced solution and a smooth compact test field, the pressure defect paired with increasingly broad mollifications has time integral tending to zero on every closed subinterval. (`Breakdown.forcedPressureAverage_of`)

### Breakdown.Frac.SpacePressureCont

This file proves continuity properties of the pressure defect needed to pass between its time integrated and pointwise forms.

**Smooth divergence of a smooth field.** The divergence of a smooth vector field is smooth. (`_private.Breakdown.Frac.SpacePressureCont.0.Breakdown.contDiff_divergence_field`)

**Divergence preserves compact support.** The divergence of a compactly supported vector field is compactly supported. (`_private.Breakdown.Frac.SpacePressureCont.0.Breakdown.hasCompactSupport_divergence_field`)

**Relate slice and joint derivatives.** For a jointly smooth scalar field, its spatial slice derivative equals the joint derivative within the time slab applied to a spatial direction. (`_private.Breakdown.Frac.SpacePressureCont.0.Breakdown.fderiv_slice_eq_fderivWithin`)

**Continuous pressure-gradient pairing.** For a positive time interval, a jointly smooth pressure has continuous pairings of its gradient with a continuous compactly supported test field. (`_private.Breakdown.Frac.SpacePressureCont.0.Breakdown.continuousOn_integral_inner_gradient`)

**Quadratic stress against a potential.** The quadratic stress sums velocity-coordinate products against the second partial derivatives of the test potential. (`_private.Breakdown.Frac.SpacePressureCont.0.Breakdown.quadraticStress`)

**Bound a quadratic matrix expression.** A uniform bound on all nine matrix entries bounds the associated quadratic expression by nine times that bound times the vector norm square. (`_private.Breakdown.Frac.SpacePressureCont.0.Breakdown.abs_quadratic_form_le`)

**Decay bound for a second partial.** The stated cubic Hessian decay implies the displayed weaker inverse-radius bound on every second partial. (`_private.Breakdown.Frac.SpacePressureCont.0.Breakdown.abs_secondPartial_le_decay`)

**Continuous second partials.** Every second partial of a smooth scalar field is continuous. (`_private.Breakdown.Frac.SpacePressureCont.0.Breakdown.continuous_secondPartial_of_smooth`)

**Continuity of quadratic stress pairing.** Joint continuity, uniform energy and the stated potential decay make the quadratic stress pairing continuous in time. (`_private.Breakdown.Frac.SpacePressureCont.0.Breakdown.continuousOn_stressPairing_self`)

**Supply pressure-defect continuity.** For an energy bounded forced solution, its pressure defect paired with any smooth compactly supported vector field is continuous throughout the closed time interval. (`Breakdown.forcedPressureContinuity`)

### Breakdown.Frac.SpacePressureDiff

This file compares pressure terms for two whole space flows, preparing the localized energy identity for their difference.

**Smoothness of time slices.** A jointly smooth function on a closed time slab has smooth spatial slices at every time in the slab. (`_private.Breakdown.Frac.SpacePressureDiff.0.Breakdown.slice_contDiff_of_contDiffOn`)

**Bilinear stress integrand.** The bilinear stress integrand contracts two vector fields against the second derivatives of the scalar potential. (`_private.Breakdown.Frac.SpacePressureDiff.0.Breakdown.pairStress`)

**Smooth divergence.** The divergence of a smooth vector field is smooth. (`_private.Breakdown.Frac.SpacePressureDiff.0.Breakdown.contDiff_divergenceAt_field`)

**Compact support of divergence.** The divergence of a compactly supported field has compact support. (`_private.Breakdown.Frac.SpacePressureDiff.0.Breakdown.hasCompactSupport_divergenceAt_field`)

**Continuous scalar gradient.** The gradient of a smooth scalar field is continuous. (`_private.Breakdown.Frac.SpacePressureDiff.0.Breakdown.continuous_gradientAt_field`)

**Integrable gradient-test pairing.** A smooth gradient paired with a continuous compactly supported vector field is integrable. (`_private.Breakdown.Frac.SpacePressureDiff.0.Breakdown.integrable_inner_gradientAt`)

**Bound the potential Hessian entries.** The potential of a smooth compactly supported scalar field has uniformly bounded second partials. (`_private.Breakdown.Frac.SpacePressureDiff.0.Breakdown.abs_secondPartial_potential_le`)

**Integrability from finite square mass.** A continuous field with finite nonnegative square integral has an integrable norm square. (`_private.Breakdown.Frac.SpacePressureDiff.0.Breakdown.integrable_sq_of_lintegral_le`)

**Integrable difference energy.** The difference of two continuous fields with integrable norm squares also has an integrable norm square. (`_private.Breakdown.Frac.SpacePressureDiff.0.Breakdown.integrable_sq_sub_field`)

**Integrability of bilinear stress.** Continuous finite-energy fields paired against a bounded continuous Hessian give an integrable stress integrand. (`_private.Breakdown.Frac.SpacePressureDiff.0.Breakdown.integrable_pairStress`)

**Expand the stress difference pointwise.** Subtracting two quadratic stress integrands gives the difference-field quadratic term and its two cross terms. (`_private.Breakdown.Frac.SpacePressureDiff.0.Breakdown.pairStress_self_sub`)

**Expand the integrated stress difference.** Under the stated integrability and Hessian bounds, the difference of quadratic stress pairings equals the difference-field pairing and its two cross pairings. (`_private.Breakdown.Frac.SpacePressureDiff.0.Breakdown.stressPairing_self_sub`)

**Derive the pressure difference identity.** The forced pressure identity hypothesis expresses the cutoff pressure difference pairing of two energy bounded forced solutions as the quadratic and two mixed stress pairings against the Newtonian potential of the cutoff divergence source at every interior time and positive cutoff radius. (`Breakdown.forcedPressureDifference_of`)

### Breakdown.Frac.SpacePressureIdentity

This file assembles the whole space pressure identity from the continuity, time identity, and averaging interfaces.

**Integrated pressure defect vanishes.** For an energy-bounded forced solution, the mollification and average interfaces make the pressure defect integrate to zero over every subinterval. (`_private.Breakdown.Frac.SpacePressureIdentity.0.Breakdown.forced_integral_pressureDefect_eq_zero`)

**Derive the pressure identity.** The pressure continuity, mollification, and averaging hypotheses force the pressure defect of an energy bounded forced solution to vanish against every smooth compact test field at each interior time. (`Breakdown.forcedPressureIdentity_of`)

### Breakdown.Frac.SpacePressureMollify

This file proves that the whole space pressure defect is unchanged by the prescribed mollification procedure.

**Smooth spatial slices.** A jointly smooth function on the closed time slab has smooth spatial slices. (`_private.Breakdown.Frac.SpacePressureMollify.0.Breakdown.contDiff_slice_of_contDiffOn'`)

**Integrate a finite double sum.** An integrable three-by-three family can be summed before or after integration. (`_private.Breakdown.Frac.SpacePressureMollify.0.Breakdown.integral_sum_sum`)

**Move the scalar Laplacian in a pairing.** For smooth scalar fields with compact support in the tested factor, the scalar sum of second partials moves between factors under integration. (`_private.Breakdown.Frac.SpacePressureMollify.0.Breakdown.integral_mul_scalarTraceSecondDeriv`)

**Stress change from a potential change.** Under the stated pressure equation and support bounds, changing the test potential changes the stress pairing by the displayed pressure-Laplacian integral. (`_private.Breakdown.Frac.SpacePressureMollify.0.Breakdown.stress_difference`)

**Pressure defect is unchanged.** At an interior time, the stated pressure-trace interface makes the pressure defect invariant under the specified compactly supported potential difference. (`_private.Breakdown.Frac.SpacePressureMollify.0.Breakdown.forcedPressureDefect_eq`)

**Derive pressure mollification invariance.** The scalar pressure trace hypothesis makes the pressure defect of an energy bounded forced solution unchanged by mollifying a smooth compact test field at any positive scale, at every interior time. (`Breakdown.forcedPressureMollify_of`)

### Breakdown.Frac.SpacePressureTime

This file derives the time integrated pressure identity for the whole space forced solution analysis.

**Smoothness gives differentiability.** A smooth function is differentiable. (`_private.Breakdown.Frac.SpacePressureTime.0.Breakdown.FracInternal.TimeIdentity.differentiable_of`)

**Smooth directional derivatives.** Applying the derivative of a smooth function to a fixed direction gives a smooth function. (`_private.Breakdown.Frac.SpacePressureTime.0.Breakdown.FracInternal.TimeIdentity.contDiff_fderiv_apply_of`)

**Reconstruct a vector from coordinates.** A real three-vector equals the sum of its coordinates times the standard basis vectors. (`_private.Breakdown.Frac.SpacePressureTime.0.Breakdown.FracInternal.TimeIdentity.sum_coord`)

**Integrability from compact vanishing.** A continuous scalar function vanishing outside the support of a compactly supported field is integrable. (`_private.Breakdown.Frac.SpacePressureTime.0.Breakdown.FracInternal.TimeIdentity.integrable_of_vanish`)

**A compact derivative integrates to zero.** The directional derivative of a smooth compactly supported scalar field has zero integral. (`_private.Breakdown.Frac.SpacePressureTime.0.Breakdown.FracInternal.TimeIdentity.integral_fderiv_eq_zero`)

**A compact divergence integrates to zero.** The integral of the sum of coordinate derivatives of compactly supported smooth scalar fields vanishes. (`_private.Breakdown.Frac.SpacePressureTime.0.Breakdown.FracInternal.TimeIdentity.integral_sum_fderiv_eq_zero`)

**Vanishing outside the support.** Outside a field's topological support, both the field value and its derivative are zero. (`_private.Breakdown.Frac.SpacePressureTime.0.Breakdown.FracInternal.TimeIdentity.vanish_off`)

**Integrate advection by parts.** For a smooth divergence-free velocity and a compact smooth test field, the advection pairing equals the negative quadratic velocity pairing with the test derivative. (`_private.Breakdown.Frac.SpacePressureTime.0.Breakdown.FracInternal.TimeIdentity.advection_identity`)

**Time identity for a forced solution.** A smooth compact test field gives the displayed identity relating the velocity time derivative, pressure defect, forcing and quadratic stress at interior times. (`Breakdown.FracInternal.TimeIdentity.time_identity`)

**Supply the forced time identity.** For a forced solution, pairing the interior time derivative with a smooth compact test field and adding its pressure defect equals the negative force pairing plus the quadratic velocity pairing with the test derivative minus the stress pairing against the Newtonian potential of the test divergence. (`Breakdown.forcedTimeIdentity`)

### Breakdown.Frac.SpacePressureTraceSecondDeriv

This file controls the second derivative trace of the pressure defect using the forced momentum and incompressibility equations.

**Differentiate a linear image.** A continuous linear map passes through the derivative of a differentiable function. (`Breakdown.FracInternal.SpacePressureTraceSecondDeriv.fderiv_clm_comp_apply`)

**Differentiate one vector coordinate.** Differentiating a coordinate of a differentiable vector field equals taking that coordinate of its derivative. (`Breakdown.FracInternal.SpacePressureTraceSecondDeriv.fderiv_component_apply`)

**Spatial slice derivative.** The derivative of a spatial slice is the joint derivative applied in the corresponding spatial direction. (`Breakdown.FracInternal.SpacePressureTraceSecondDeriv.fderiv_slice_right_apply`)

**Time slice derivative.** The time derivative of a differentiable joint function is its derivative applied to the unit time direction. (`Breakdown.FracInternal.SpacePressureTraceSecondDeriv.hasDerivAt_slice_left`)

**Directional scalar partial.** The directional partial evaluates the scalar derivative in one fixed spatial direction. (`Breakdown.FracInternal.SpacePressureTraceSecondDeriv.dirPartial`)

**Smooth directional partial.** A directional partial of a smooth scalar function is smooth. (`Breakdown.FracInternal.SpacePressureTraceSecondDeriv.dirPartial_smooth`)

**Directional partial of a sum.** The directional derivative of the three-term smooth sum equals the sum of the directional derivatives. (`Breakdown.FracInternal.SpacePressureTraceSecondDeriv.dirPartial_sum`)

**Directional product rule.** The directional derivative of a product of smooth scalar functions obeys the product rule. (`Breakdown.FracInternal.SpacePressureTraceSecondDeriv.dirPartial_mul`)

**Iterate directional derivatives.** Two directional derivatives of a smooth scalar field equal its second derivative applied to the two directions. (`Breakdown.FracInternal.SpacePressureTraceSecondDeriv.dirPartial_dirPartial`)

**Coordinate second partial as iteration.** The potential's coordinate second partial equals the corresponding iterated directional partial. (`Breakdown.FracInternal.SpacePressureTraceSecondDeriv.secondPartial_eq_dirPartial`)

**Smooth vector coordinates.** Each coordinate of a smooth vector field is smooth. (`Breakdown.FracInternal.SpacePressureTraceSecondDeriv.component_smooth`)

**Directional derivative of a coordinate.** A coordinate's directional derivative equals that coordinate of the vector derivative. (`Breakdown.FracInternal.SpacePressureTraceSecondDeriv.dirPartial_component`)

**Divergence as directional partials.** The divergence of a smooth field is the sum of its coordinate directional partials. (`Breakdown.FracInternal.SpacePressureTraceSecondDeriv.divergence_eq_sum_dirPartial`)

**Basis expansion of a vector.** A vector equals its standard-basis coordinate expansion. (`Breakdown.FracInternal.SpacePressureTraceSecondDeriv.space_eq_sum`)

**Coordinate formula for advection.** Each coordinate of self-advection is the sum of velocity coordinates times the corresponding directional partials. (`Breakdown.FracInternal.SpacePressureTraceSecondDeriv.advection_component`)

**Advection as divergence of products.** For a smooth divergence-free field, each advection coordinate is the sum of derivatives of the corresponding velocity products. (`Breakdown.FracInternal.SpacePressureTraceSecondDeriv.advection_component_eq`)

**Divergence of advection.** For a smooth divergence-free field, the divergence of advection equals the double sum of second partials of velocity-coordinate products. (`Breakdown.FracInternal.SpacePressureTraceSecondDeriv.advection_term`)

**Divergence of the gradient.** For a smooth scalar pressure, the sum of its coordinate second partials equals the divergence of its gradient. (`Breakdown.FracInternal.SpacePressureTraceSecondDeriv.gradient_term`)

**Time derivative remains divergence-free.** For the stated smooth divergence-free time-dependent field, the time derivative has differentiable spatial coordinates and zero divergence. (`Breakdown.FracInternal.SpacePressureTraceSecondDeriv.time_term`)

**Derivative of a negative difference.** The directional derivative distributes over the displayed negative sum of three differentiable functions. (`Breakdown.FracInternal.SpacePressureTraceSecondDeriv.dirPartial_neg_sub_sub`)

**Supply the scalar pressure equation.** At every interior time of a forced solution, the sum of the pressure's second coordinate derivatives equals minus the double sum of the mixed second derivatives of the velocity component products. (`Breakdown.forcedScalarTraceSecondDeriv`)

### Breakdown.Frac.SpaceRestrict

This file restricts a global fractional solution to a finite time interval so it can enter the whole space uniqueness framework.

**Restrict a fractional solution.** A global unit viscosity fractional solution with divergence free initial data satisfies the smooth finite interval fractional solution conditions on every interval [0,T]. (`Breakdown.fracRestrict`)

### Breakdown.Frac.SpaceScaling

This file normalizes viscosity and tracks the corresponding scaling of fractional solutions and their energy bounds.

**Smooth slices at nonnegative times.** A function smooth on the nonnegative time slab has smooth spatial slices at every nonnegative time. (`Breakdown.FracSpaceScalingInternal.contDiff_slice_of_contDiffOn`)

**Time differentiability after zero.** A function smooth on the nonnegative time slab is differentiable in time at every positive time. (`Breakdown.FracSpaceScalingInternal.differentiableAt_time_of_contDiffOn`)

**Smoothness under viscosity rescaling.** Positive time rescaling and constant multiplication preserve smoothness on the nonnegative time slab. (`Breakdown.FracSpaceScalingInternal.contDiffOn_rescale`)

**Divergence under amplitude scaling.** Multiplying a differentiable vector field by a scalar multiplies its divergence by that scalar. (`Breakdown.FracSpaceScalingInternal.divergenceAt_const_smul`)

**Advection under amplitude scaling.** Multiplying a differentiable field by a scalar multiplies its self-advection by the scalar square. (`Breakdown.FracSpaceScalingInternal.advectionAt_const_smul`)

**Gradient under scalar multiplication.** Multiplying a differentiable scalar field by a constant multiplies its gradient by that constant. (`Breakdown.FracSpaceScalingInternal.gradientAt_const_mul`)

**Time derivative after rescaling.** The derivative of the amplitude-scaled, time-rescaled curve is the stated product of amplitude, inverse time scale and original derivative. (`Breakdown.FracSpaceScalingInternal.hasDerivAt_rescale_time`)

**Supply viscosity scaling.** If smooth compactly supported divergence free data obstruct a global unit viscosity fractional solution with a uniform energy bound, then for every positive viscosity there are data of the same class obstructing a global fractional solution with such a bound. (`Breakdown.fracScaling`)

### Breakdown.Frac.SpaceSixth

This file supplies the spatial L⁶ bound used to control nonlinear terms in the whole space fractional difference estimate.

**Three spatial dimensions.** The real dimension of the spatial vector space is three. (`_private.Breakdown.Frac.SpaceSixth.0.Breakdown.sixth_finrank`)

**Sobolev embedding into L⁶.** A universal constant bounds the L⁶ norm of each continuously differentiable compactly supported field by the L² norm of its derivative. (`_private.Breakdown.Frac.SpaceSixth.0.Breakdown.sixth_embedding`)

**Operator norm from coordinate columns.** A real linear map's operator norm is bounded by the square root of the sum of its coordinate-column norm squares. (`_private.Breakdown.Frac.SpaceSixth.0.Breakdown.sixth_opNorm_le`)

**Lp norm as a power integral.** For a continuous compactly supported nonnegative function and positive natural exponent, its Lp norm equals the corresponding root of its power integral. (`_private.Breakdown.Frac.SpaceSixth.0.Breakdown.sixth_eLpNorm_nat_eq`)

**Distance outside a closed ball.** A point outside the closed ball of radius twice r has norm at least twice r. (`_private.Breakdown.Frac.SpaceSixth.0.Breakdown.sixth_outside`)

**Split a square-root bound.** If E is bounded by a nonnegative square plus a nonnegative number, its square root is bounded by the first factor plus the second square root. (`_private.Breakdown.Frac.SpaceSixth.0.Breakdown.sixth_sqrt_le`)

**Derive the sixth-norm estimate.** The fractional gradient bound hypothesis gives, for 1 < α < 3/2 and every finite energy field with size bound A, a cutoff L⁶ bound of S times the sum of A and the square root of its cutoff fractional dissipation whenever the cutoff radius is at least one. (`Breakdown.fracSixthNorm_of`)

### Breakdown.Frac.SpaceSolenoidal

This file proves that the fractional power preserves the weak divergence condition required by the forced whole space framework.

**Far-increment remainder bound.** For increments of norm at least one, the second-order remainder is bounded by the translated field and local derivative norms times the increment square. (`_private.Breakdown.Frac.SpaceSolenoidal.0.Breakdown.FracInternal.norm_remainder_le_far`)

**Integrability from near and far powers.** A measurable scalar function with singularity exponent below three and decay exponent above three is integrable under the stated bounds. (`_private.Breakdown.Frac.SpaceSolenoidal.0.Breakdown.FracInternal.integrable_of_near_far`)

**Uniform translated test pairing bound.** A continuous L² or bounded field has uniformly bounded norm pairings with every translate of a continuous compactly supported test field. (`_private.Breakdown.Frac.SpaceSolenoidal.0.Breakdown.FracInternal.exists_bound_translate`)

**Integrable pairing with a compact test.** The pairing of two continuous fields is integrable when the tested field has compact support. (`_private.Breakdown.Frac.SpaceSolenoidal.0.Breakdown.FracInternal.integrable_inner_compact_right`)

**Second derivative along one direction.** The second iterated derivative of a smooth field in a repeated direction equals the derivative of its first directional derivative. (`_private.Breakdown.Frac.SpaceSolenoidal.0.Breakdown.FracInternal.iteratedFDeriv_two_eq_fderiv_apply`)

**Combine a real and natural power.** For the stated nonnegative base and nonzero exponents, multiplying its real power by its natural power adds the exponents. (`_private.Breakdown.Frac.SpaceSolenoidal.0.Breakdown.FracInternal.rpow_mul_pow_eq_aux`)

**Joint continuity of the remainder.** The second-order remainder of a smooth field is jointly continuous in base point and increment. (`_private.Breakdown.Frac.SpaceSolenoidal.0.Breakdown.FracInternal.continuous_remainder_pair`)

**Continuity in the remainder's base point.** At fixed increment, the remainder of a smooth field is continuous in the base point. (`_private.Breakdown.Frac.SpaceSolenoidal.0.Breakdown.FracInternal.continuous_remainder_section`)

**The remainder vanishes far from support.** An increment shorter than r gives zero remainder when its base point lies outside the r-thickening of the support. (`_private.Breakdown.Frac.SpaceSolenoidal.0.Breakdown.FracInternal.remainder_eq_zero_of_far`)

**Integrate the weak remainder pairing.** For the stated exponent range and smooth L²-or-bounded field, its pairing with the compact test remainder is jointly integrable against the singular kernel. (`_private.Breakdown.Frac.SpaceSolenoidal.0.Breakdown.FracInternal.integrable_prod_right_side`)

**Smoothness of a gradient field.** The gradient field of a smooth scalar is smooth. (`_private.Breakdown.Frac.SpaceSolenoidal.0.Breakdown.FracInternal.gradField_contDiff`)

**Compact support of a gradient field.** The gradient of a compactly supported scalar field has compact support. (`_private.Breakdown.Frac.SpaceSolenoidal.0.Breakdown.FracInternal.gradField_hasCompactSupport`)

**Commute scalar directional derivatives.** The two iterated directional derivatives of a smooth scalar field agree after exchanging directions. (`_private.Breakdown.Frac.SpaceSolenoidal.0.Breakdown.FracInternal.fderiv_apply_swap`)

**Differentiate a gradient field.** A directional derivative of a smooth gradient equals the gradient of the corresponding directional derivative. (`_private.Breakdown.Frac.SpaceSolenoidal.0.Breakdown.FracInternal.fderiv_gradField`)

**Solenoidal fields annihilate gradients.** A smooth divergence-free field pairs to zero with the gradient of every compact smooth scalar test. (`_private.Breakdown.Frac.SpaceSolenoidal.0.Breakdown.FracInternal.integral_inner_gradField_eq_zero`)

**Pair a gradient remainder with a field.** A smooth divergence-free field pairs to zero with the second-order remainder of every compact smooth gradient field. (`_private.Breakdown.Frac.SpaceSolenoidal.0.Breakdown.FracInternal.integral_inner_remainder_gradField`)

**Derive weak fractional solenoidality.** The compact symmetry, compact decay, and covariance hypotheses imply that, for 1 < α < 3/2, the fractional power of a smooth divergence free L² field pairs to zero with the gradient of every smooth compact scalar test function. (`Breakdown.fracWeakSolenoidal_of`)

### Breakdown.Frac.SpaceUniqueness

This file closes the whole space fractional uniqueness argument from localized difference and dissipation estimates.

**Energy bound for a field difference.** The stated separate energy bounds control the square integral of the difference by twice the sum of their absolute bounds. (`Breakdown.FracInternal.SpaceUniqueness.lintegral_norm_sub_sq_le`)

**A linear differential upper bound.** A continuous zero-initial function with the stated derivative inequality satisfies the displayed exponential upper bound on the interval. (`Breakdown.FracInternal.SpaceUniqueness.le_of_hasDerivAt_le_linear`)

**Larger radii enlarge the cutoff weight.** Increasing a positive cutoff radius increases its cutoff weight pointwise. (`Breakdown.FracInternal.SpaceUniqueness.cutoffPow_mono`)

**L² membership from finite energy.** A continuous field with the stated finite square-integral bound belongs to L². (`Breakdown.FracInternal.SpaceUniqueness.memLp_two_of_lintegral`)

**Fractional power of a difference.** The additivity and remainder interfaces make the fractional operator distribute over the difference of smooth L² fields in the stated exponent range. (`Breakdown.FracInternal.SpaceUniqueness.power_sub_eq`)

**Move dissipation to the cutoff field.** The compact symmetry interface transfers the fractional operator from a smooth L² field to its cutoff-weighted version in the energy pairing. (`Breakdown.FracInternal.SpaceUniqueness.dissipation_eq`)

**Derive whole-space fractional uniqueness.** The local energy, pressure difference, forced solution, localized difference, compact symmetry, additivity, and remainder integrability hypotheses imply uniqueness on [0,T] for energy bounded smooth fractional solutions with 1 < α < 5/4, equal initial velocities, and a uniform gradient bound on one solution. (`Breakdown.fracUniqueness_of`)

### Breakdown.Frac.SpaceUnitBreakdown

This file derives the unit viscosity whole space obstruction from a rotating fractional profile and the mild flow, uniqueness, and orbit rate interfaces.

**Restrict a half-open mild solution.** A mild solution on a half-open interval is mild on every closed subinterval ending strictly before its final time. (`Breakdown.FracSpaceUnitBreakdown.isMildOnIcc_of_isMildOn`)

**Derive unit-viscosity space breakdown.** For 1 < α < 5/4, the mild blowup, profile orbit, mild regularity, restriction, uniqueness, and orbit nonextension hypotheses turn rotating profile existence into smooth compactly supported divergence free data that admit no global unit viscosity fractional solution with one uniform energy bound. (`Breakdown.fracSpaceUnitBreakdown_of`)

### Breakdown.Frac.SpaceWeakCont

This file proves weak time continuity of the fractional power pairings needed by the forced solution framework.

**Weighted product bound.** For a positive balancing parameter, a scalar product is bounded by the weighted first square plus the reciprocal-weighted second square. (`_private.Breakdown.Frac.SpaceWeakCont.0.Breakdown.weakCont_amgm`)

**Weighted vector pairing bound.** For a positive balancing parameter, the norm of a vector pairing is bounded by the displayed two weighted norm squares. (`_private.Breakdown.Frac.SpaceWeakCont.0.Breakdown.weakCont_pair_bound`)

**Decay gives square integrability.** A continuous field with the stated decay of order three plus twice positive α has an integrable norm square. (`_private.Breakdown.Frac.SpaceWeakCont.0.Breakdown.weakCont_sq_integrable`)

**Write the energy bound as an integral.** A continuous field under the stated energy bound has integrable norm square and real integral bounded by the nonnegative part of that bound. (`_private.Breakdown.Frac.SpaceWeakCont.0.Breakdown.weakCont_energy`)

**Derive weak continuity.** The compact decay hypothesis implies that, for 1 < α < 3/2, pairing an energy bounded jointly smooth velocity field with the fractional power of a smooth compact test field is continuous on the closed time interval. (`Breakdown.fracWeakContinuity_of`)

### Breakdown.Frac.StBilinH1

This file declares the gradient level physical formula for the fractional bilinear operator, linking abstract mild states to advection.

**H¹ formula for the bilinear term.** The proposition identifies the fractional bilinear map on an H¹ field with bounded value and derivative as minus the projected heat evolution of its advection. (`Breakdown.Freq.FracBilinH1Formula`)

### Breakdown.Frac.StNiceEmbed

This file declares the compatibility between nice physical fields, their embedded states, and the fractional power.

**Embedding respects differential powers.** The proposition requires embedding a nice field to preserve both the ordinary and fractional differential-power relations. (`Breakdown.Freq.FracNiceEmbedPower`)

### Breakdown.Frac.StOperator

This file declares the integral, Fourier symbol, symmetry, and covariance interfaces for the fractional power operator.

**Third-derivative remainder estimate.** The remainder proposition requests a cubic bound controlled by the third derivative on the closed ball covering the increment. (`Breakdown.RemainderBoundStatement`)

Proved by `Breakdown.remainderBound`.

**Positive fractional normalization.** For one less than α less than two, the normalizer proposition requests integrability of its cosine remainder kernel and positivity of the normalizing constant. (`Breakdown.NormalizerStatement`)

Proved by `Breakdown.normalizer`.

**Integrability of fractional remainders.** For one less than α less than three halves, the proposition requests remainder-kernel integrability for every smooth L² or bounded field. (`Breakdown.RemainderIntegrableStatement`)

Proved by `Breakdown.remainderIntegrable`. Also proved from further statements by `Breakdown.remainderIntegrable_of`.

**Scalar Fourier kernel identities.** The scalar-symbol proposition records the normalized cosine remainder integral and the vanishing sine remainder integral in the stated exponent range. (`Breakdown.SymbolScalarStatement`)

Proved from further statements by `Breakdown.symbolScalar`.

**Complex fractional-symbol integrand.** The symbol integrand multiplies the singular radial kernel by the complex plane wave after subtracting its Taylor terms through order two. (`Breakdown.symbolIntegrand`)

**Exchange Fourier and kernel integrals.** The exchange proposition identifies a Schwartz field's fractional Fourier transform with its original transform times the normalized kernel integral. (`Breakdown.SymbolExchangeStatement`)

Proved by `Breakdown.symbolExchange`. Also proved from further statements by `Breakdown.symbolExchange_of`.

**The fractional Fourier multiplier.** The symbol proposition requires the fractional operator on a Schwartz field to have multiplier twice pi times frequency norm raised to twice α. (`Breakdown.SymbolStatement`)

Proved by `Breakdown.symbol`. Also proved from further statements by `Breakdown.symbol_of`.

**Symmetry against compact test fields.** In the stated exponent range, the compact-symmetry proposition moves the fractional operator between a smooth L²-or-bounded field and a compact smooth test in their integrable pairing. (`Breakdown.SymmetryCompactStatement`)

Proved by `Breakdown.symmetryCompact`. Also proved from further statements by `Breakdown.symmetryCompact_of`.

**Symmetry against Schwartz test fields.** The rapid-test symmetry proposition moves the fractional operator across a Schwartz pairing when the tested field's derivatives through order three are uniformly bounded. (`Breakdown.SymmetryRapidStatement`)

Proved by `Breakdown.symmetryRapid`. Also proved from further statements by `Breakdown.symmetryRapid_of`.

**Covariance of the fractional operator.** The covariance proposition records positive dilation, scalar multiplication, rotation and translation laws for twice differentiable fields. (`Breakdown.CovarianceStatement`)

Proved by `Breakdown.covariance`.

**Additivity of the fractional operator.** The additivity proposition requires the stated remainder integrability and twice differentiable germs before distributing the fractional operator over a sum. (`Breakdown.AdditivityStatement`)

Proved by `Breakdown.additivity`.

### Breakdown.Frac.StProfile

This file defines rotating fractional profiles and their physical similarity fields, and declares the route from a profile to a recurrent mild orbit and blowup trajectory.

**Coordinate formula for axial rotation.** The axial rotation formula rotates the first two coordinates by the given angle and preserves the third. (`Breakdown.axialRotationFormula`)

**Choose the axial rotation isometry.** The axial rotation selects an isometry realizing the coordinate formula when one exists and otherwise returns the identity isometry. (`Breakdown.axialRotation`)

**Properties of axial rotation.** The axial-rotation proposition records the coordinate formula, identity, composition, inverse, continuity and angular derivative laws. (`Breakdown.AxialRotationSpec`)

**A smooth rotating fractional profile.** The profile predicate requires positive viscosity, smooth velocity, pressure and fractional image, zero residual and divergence, nonzero velocity and the stated derivative decay at every order. (`Breakdown.IsRotatingProfile`)

**Profile existence in bundled form.** The proposition identifies the external rotating-profile existence predicate with the existence of the bundled smooth profile data. (`Breakdown.ProfileExistsIff`)

**Normalize the profile viscosity.** For one less than α less than five quarters, the proposition requires the displayed space and amplitude rescaling to turn any positive-viscosity profile into a unit-viscosity profile. (`Breakdown.UnitViscosity`)

**A rotating profile time slice.** The rotating slice pushes the fixed profile forward by the axial rotation through minus its angular speed times similarity time. (`Breakdown.rotatingSlice`)

**Self-similar physical velocity.** The physical velocity applies fractional dilation to the rotating slice evaluated at logarithmic similarity time. (`Breakdown.selfSimilarField`)

**Self-similar physical pressure.** The physical pressure combines its prescribed time-dependent amplitude, spatial dilation and axial rotation. (`Breakdown.selfSimilarPressure`)

**Decay of each rotating slice.** For the stated exponent range and unit-viscosity profile, the slice-decay proposition requires decay-field membership and uniform spatial derivative bounds through order three. (`Breakdown.RotatingSliceDecay`)

**Continuity of the rotating state.** For the stated unit-viscosity profile, the slice-continuity proposition requests continuity of its embedded rotating orbit in X. (`Breakdown.RotatingSliceContinuous`)

**Momentum of the self similar field.** The momentum proposition requires the self-similar velocity's time derivative to equal minus dissipation, advection and pressure gradient before time one. (`Breakdown.SelfSimilarMomentum`)

**Time control of the self-similar field.** Before any terminal time below one, the proposition requests a Lipschitz-in-time velocity bound with the stated spatial decay. (`Breakdown.SelfSimilarTimeBound`)

**Weak self-similar fractional solution.** For the stated profile and exponent range, the proposition requires the self-similar field to solve the weak fractional equation on every positive interval ending before time one. (`Breakdown.SelfSimilarWeak`)

**Joint continuity of dilation.** The dilation proposition requires joint continuity in the positive scale and the vector being dilated. (`Breakdown.ScaledDilateJointContinuous`)

**Recover similarity flow from mildness.** The proposition requires a physical mild solution represented by the scaled orbit to satisfy the similarity-time integral equation. (`Breakdown.ScaledFlowOfMild`)

**A profile gives a recurrent orbit.** For the stated exponent range and matching concrete scaled framework, the profile-orbit proposition requests recurrence and the mild orbit equation for every positive recurrence period. (`Breakdown.FracProfileOrbit`)

**Mild blow-up from nearby test data.** For the stated exponent range, the proposition turns profile existence into arbitrarily close compact test data and a mild trajectory approaching the chosen profile at a positive similarity-time rate. (`Breakdown.FracMildBlowup`)
<!-- /passage:front -->

