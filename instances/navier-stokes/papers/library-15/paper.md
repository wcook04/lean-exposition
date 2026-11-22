
<!-- passage:front -->
# Library guide 15: Breakdown/Frac

**Navier–Stokes pages:** [the paper](../navier-stokes-paper/paper.pdf) · [proof routes](../navier-stokes-routes/paper.md) · [routes in detail](../navier-stokes-route-details/paper.md) · library guide: [1](../navier-stokes-library-01/paper.md) [2](../navier-stokes-library-02/paper.md) [3](../navier-stokes-library-03/paper.md) [4](../navier-stokes-library-04/paper.md) [5](../navier-stokes-library-05/paper.md) [6](../navier-stokes-library-06/paper.md) [7](../navier-stokes-library-07/paper.md) [8](../navier-stokes-library-08/paper.md) [9](../navier-stokes-library-09/paper.md) [10](../navier-stokes-library-10/paper.md) [11](../navier-stokes-library-11/paper.md) [12](../navier-stokes-library-12/paper.md) [13](../navier-stokes-library-13/paper.md) [14](../navier-stokes-library-14/paper.md) **15** [16](../navier-stokes-library-16/paper.md) [17](../navier-stokes-library-17/paper.md) [18](../navier-stokes-library-18/paper.md) [19](../navier-stokes-library-19/paper.md) [20](../navier-stokes-library-20/paper.md) [21](../navier-stokes-library-21/paper.md) [22](../navier-stokes-library-22/paper.md) [23](../navier-stokes-library-23/paper.md) [24](../navier-stokes-library-24/paper.md) [25](../navier-stokes-library-25/paper.md) [26](../navier-stokes-library-26/paper.md) [27](../navier-stokes-library-27/paper.md) [28](../navier-stokes-library-28/paper.md) [29](../navier-stokes-library-29/paper.md) [30](../navier-stokes-library-30/paper.md)

*A plain title and a sentence for each declaration in `Breakdown.Frac.StRealize` to `Breakdown.Frac.TorusUnique` of Alpöge and Buckmaster's Lean at `ad53419de079eb8f95f60313473374624a348546`, in the authors' file order. Prepared with AI assistance. The authors have not reviewed it.*

Each paragraph names one declaration and says whether it is a definition, a proposition that the library defines (its name usually ends in `Holds` or `Statement`) or a proved result, then what it states. Click a paragraph to open its Lean on the right.

### Breakdown.Frac.StRealize

This file defines the whole space fractional heat, dilation, and bilinear operators and declares the interfaces needed to realize them as a scaled mild framework.

**Fractional physical scaling.** The scaled field multiplies its amplitude by the stated power of the scale and evaluates at the corresponding fractional spatial dilation. (`Breakdown.scaleField`)

**The X-space dilation exponent.** The dilation exponent is one minus three divided by four times α. (`Breakdown.dilExponent`)

**Fractional heat multiplier.** The heat factor is the exponential of minus the nonnegative part of time times the fractional frequency rate. (`Breakdown.Freq.fracHeatFactor`)

**Fractional heat on Fourier L².** The Fourier L² heat operator multiplies each frequency by the fractional heat factor. (`Breakdown.Freq.fracHeatL2`)

**Restrict fractional heat to X.** The X-space heat operator is the restriction of the Fourier L² heat operator. (`Breakdown.Freq.fracHeatX`)

**Fractional dilation on Fourier L².** The Fourier L² dilation combines the specified frequency rescaling and amplitude factor. (`Breakdown.Freq.fracDilL2`)

**Fractional dilation on X.** For positive scale, the X-space dilation restricts the Fourier dilation; at other scales it is defined to be zero. (`Breakdown.Freq.fracDilX`)

**Projected heat frequency factor.** The projected heat factor is twice pi times frequency norm multiplied by fractional heat decay. (`Breakdown.Freq.fracPhiFactor`)

**Projected heat field from X.** The projected heat-field map multiplies a symbol by the projected heat factor and reconstructs its physical field. (`Breakdown.Freq.fracPhiX`)

**Symmetric fractional bilinear pairing.** The bilinear form is minus one half of the sum of the two trilinear pairings with the projected heat test field. (`Breakdown.Freq.fracBilinForm`)

**Specification of the bilinear operator.** The bilinear specification requires the operator's inner product with every test vector to equal the prescribed symmetric bilinear form. (`Breakdown.Freq.FracBilinSpec`)

**Choose the fractional bilinear operator.** At positive time, the bilinear operator chooses a realization of its pairing specification when one exists; otherwise it is zero. (`Breakdown.Freq.fracBilinX`)

**Projected heat for a physical L² field.** The solenoidal heat map Fourier-transforms a complexified physical field, multiplies by the projected heat factor and projects into X. (`Breakdown.Freq.fracHeatSolenoidal`)

**Physical field from a nice symbol.** The nice physical field is the real vector part of the symbol's inverse Fourier transform. (`Breakdown.Freq.niceField`)

**Fields represented by nice symbols.** The nice-field predicate requires a field to be the reconstruction of a nice symbol. (`Breakdown.Freq.IsNiceField`)

**Graph of the fractional multiplier.** The fractional graph relation requires the output Fourier representative to equal the input multiplied by the fractional rate almost everywhere. (`Breakdown.Freq.IsFracOf`)

**Fractional heat-semigroup laws.** The heat-semigroup proposition requests identity, composition, contraction, continuity, symmetry in the inner product and agreement with the L² operator. (`Breakdown.Freq.FracHeatSemigroup`)

**Fractional dilation algebra.** The dilation proposition records the exact norm scaling, identity, composition, heat covariance and agreement with the L² realization at positive scales. (`Breakdown.Freq.FracDilationAlgebra`)

**Continuity of fractional dilation.** The dilation-continuity proposition requests continuity in the positive scale for each element of X. (`Breakdown.Freq.FracDilationContinuous`)

**Rotations commute with heat and dilation.** The rotation proposition requires rotations of X to commute with fractional heat and dilation. (`Breakdown.Freq.FracRotationAlgebra`)

**Scaling preserves decay fields.** The decay-scaling proposition requires positive fractional scaling to preserve decay-field membership. (`Breakdown.Freq.DecayFieldScale`)

**Embedding commutes with dilation.** For positive scale and a decay field, the proposition identifies dilation of its embedding with embedding its physically scaled field. (`Breakdown.Freq.FracEmbedDilate`)

**Velocity commutes with dilation.** For positive scale, the proposition identifies reconstructed dilated velocity with the physically scaled velocity almost everywhere. (`Breakdown.Freq.FracVelocityDilate`)

**Projected heat bounds in L² and L⁶.** The projected-heat bound proposition gives L⁶ membership and the stated time-decay bounds for both L² and L⁶ norms. (`Breakdown.Freq.FracPhiBounds`)

**Projected heat as a velocity field.** The proposition identifies the projected heat field with the velocity associated to the specified differential-power relation. (`Breakdown.Freq.FracPhiVelocity`)

**Existence of the bilinear operator.** The existence proposition requires a continuous bilinear operator realizing its pairing specification at every positive time. (`Breakdown.Freq.FracBilinExists`)

**Fractional bilinear operator bound.** The bound proposition requests a nonnegative constant controlling the bilinear map by the stated singular time power times its two input norms. (`Breakdown.Freq.FracBilinBound`)

**Shift heat through the bilinear kernel.** The shift proposition requires heat evolution after the bilinear map to add its time to the kernel time. (`Breakdown.Freq.FracBilinShift`)

**Continuity of the bilinear kernel.** The continuity proposition requests that the bilinear output vary continuously at positive kernel times for fixed inputs. (`Breakdown.Freq.FracBilinContinuous`)

**Dilation covariance of the bilinear map.** The proposition records the scaled-time bilinear identity with the extra scale factor on the dilated output. (`Breakdown.Freq.FracBilinDilate`)

**Rotation covariance of the bilinear map.** The proposition requires rotation of the bilinear output to equal the bilinear map of the rotated inputs. (`Breakdown.Freq.FracBilinRotate`)

**Bilinear formula with a test field.** With a compact test field in one slot, the proposition identifies the bilinear map with minus one half of projected heat acting on the test-advection expression. (`Breakdown.Freq.FracBilinTestFormula`)

**Compactness with test-span data.** The compactness proposition requires the bilinear map with its first input in the test span to be compact at every positive time. (`Breakdown.Freq.FracBilinCompact`)

**Concrete scaled fractional framework.** The framework proposition requires a scaled mild framework whose heat, bilinear and dilation operators are the concrete fractional operators. (`Breakdown.Freq.FracFrameworkSpec`)

**Rotations commute with the framework.** The commutation proposition requires every spatial isometry to act as a commuting symmetry of any matching concrete fractional framework. (`Breakdown.Freq.FracCommutes`)

**Closure properties of nice fields.** The nice-field proposition requests Schwartz representation, decay, closure under ordinary and fractional powers and commutation of those powers. (`Breakdown.Freq.NiceFieldProps`)

**Fourier symbol of the nice embedding.** The embedding proposition identifies a nice field's embedded symbol with its original symbol times twice pi times frequency norm almost everywhere. (`Breakdown.Freq.NiceEmbedSymbol`)

**Gradient pairing by parts.** The proposition identifies the gradient pairing of a decay field and a nice field with the field pairing against the nice field's negative Laplacian. (`Breakdown.Freq.NicePairingByParts`)

**Advection as a trilinear pairing.** The proposition identifies advection paired with a nice field with the corresponding trilinear form on embeddings. (`Breakdown.Freq.NiceAdvectionTrilinear`)

**Nice fields are graph-dense.** The graph-density proposition requests nice fields approximating both an element of the fractional graph and its image to any positive tolerance. (`Breakdown.Freq.FracNiceGraphDense`)

**A weak fractional solution.** The weak-solution predicate records decay, X continuity, L² continuity of time differences and the tested fractional momentum identity. (`Breakdown.Freq.FracIsWeakSolution`)

**Weak equation after embedding in X.** The weak-in-X proposition requires a weak physical solution to satisfy the integrated X-space pairing identity against every nice field. (`Breakdown.Freq.FracWeakInX`)

**A fractional mild trajectory in X.** The mild predicate requires a continuous X-valued curve satisfying the integrable heat-plus-bilinear formula on its closed interval. (`Breakdown.Freq.IsFracMildX`)

**Weak solutions give mild trajectories.** The proposition requires embedding a weak solution on a positive-length interval to produce an X-valued mild solution. (`Breakdown.Freq.FracMildOfWeak`)

### Breakdown.Frac.StSpace

This file defines finite interval whole space fractional solutions and the pressure, energy, uniqueness, regularity, and breakdown interfaces used on that route.

**Smooth fractional flow on an interval.** The solution predicate records smooth velocity and pressure, the interior fractional momentum equation and incompressibility throughout the closed interval. (`Breakdown.FracSolutionOn`)

**Smooth solution with admissible forcing.** The forced-solution predicate records smooth velocity and pressure, momentum, solenoidality, smooth solenoidal forcing and its weak continuity and large-mollifier vanishing. (`Breakdown.IsForcedSolutionOn`)

**Scalar second-order remainder.** The scalar remainder subtracts the field value, first directional derivative and half the repeated second derivative from the translated value. (`Breakdown.scalarSecondOrderRemainder`)

**Scalar fractional operator.** The scalar fractional operator is the normalized singular integral of the scalar second-order remainder. (`Breakdown.scalarPowerAt`)

**Localized difference-energy expression.** The difference expression combines fractional dissipation, cutoff transport, stretching and the three pressure-stress pairings. (`Breakdown.fracDifferenceRHS`)

**No global energy-bounded solution.** The obstruction predicate excludes a global unit-viscosity fractional solution whose energy is bounded uniformly over all nonnegative times. (`Breakdown.FracNoBoundedSolution`)

**Restrict a global fractional solution.** The restriction proposition requires a global unit-viscosity solution with divergence-free initial data to satisfy the finite-interval solution predicate. (`Breakdown.FracRestrictStatement`)

Proved by `Breakdown.fracRestrict`.

**Extend unit-viscosity breakdown.** The scaling proposition turns a smooth compact divergence-free datum with no global energy-bounded unit-viscosity solution into the full space-breakdown conclusion. (`Breakdown.FracScalingStatement`)

Proved by `Breakdown.fracScaling`.

**Decay of a compact fractional image.** In the stated exponent range, the compact-decay proposition requests continuity and decay of order three plus twice α for the fractional image of a compact smooth test. (`Breakdown.FracCompactDecayStatement`)

Proved by `Breakdown.fracCompactDecay`.

**Weak divergence of the fractional image.** In the stated exponent range, the proposition requires the fractional image of a smooth divergence-free L² field to annihilate all compact smooth gradients. (`Breakdown.FracWeakSolenoidalStatement`)

Proved from further statements by `Breakdown.fracWeakSolenoidal_of`.

**Weak continuity of fractional pairings.** In the stated exponent range, smooth energy-bounded time-dependent fields must pair continuously with the fractional image of every compact smooth test. (`Breakdown.FracWeakContinuityStatement`)

Proved from further statements by `Breakdown.fracWeakContinuity_of`.

**Large mollifiers give small pairings.** The proposition makes fractional-image pairings with large mollifications uniformly small over continuous fields obeying a fixed energy bound. (`Breakdown.FracMollifyPairingStatement`)

Proved by `Breakdown.fracMollifyPairing`.

**Treat dissipation as an admissible force.** In the stated exponent range, the proposition requires an energy-bounded fractional solution to satisfy the forced-solution predicate with its fractional image as forcing. (`Breakdown.FracForcedStatement`)

Proved by `Breakdown.FracInternal.SpaceAssembly.forced`. Also proved from further statements by `Breakdown.fracForced_of`.

**Scalar pressure equation.** The proposition requires the pressure Laplacian of a forced solution to equal minus the double divergence of its quadratic velocity products at interior times. (`Breakdown.ForcedScalarTraceSecondDerivStatement`)

Proved by `Breakdown.forcedScalarTraceSecondDeriv`.

**Mollify the pressure defect.** For an energy-bounded forced solution, the proposition requires every positive-scale mollification of a compact test to leave the pressure defect unchanged. (`Breakdown.ForcedPressureMollifyStatement`)

Proved from further statements by `Breakdown.forcedPressureMollify_of`.

**Continuity of the pressure defect.** For an energy-bounded forced solution, the pressure defect against each compact smooth test must vary continuously on the closed time interval. (`Breakdown.ForcedPressureContinuityStatement`)

Proved by `Breakdown.forcedPressureContinuity`.

**Tested forced time identity.** The time-identity proposition records the equality between the tested time derivative plus pressure defect and the forcing, quadratic transport and stress terms. (`Breakdown.ForcedTimeIdentityStatement`)

Proved by `Breakdown.forcedTimeIdentity`.

**Pressure defect averages vanish at scale.** For an energy-bounded forced solution, the average proposition requires the time-integrated pressure defect of large mollifications to tend to zero. (`Breakdown.ForcedPressureAverageStatement`)

Proved from further statements by `Breakdown.forcedPressureAverage_of`.

**The pressure defect vanishes.** For an energy-bounded forced solution, the pressure-identity proposition requires the defect against every compact smooth test to vanish at interior times. (`Breakdown.ForcedPressureIdentityStatement`)

Proved from further statements by `Breakdown.forcedPressureIdentity_of`.

**Pressure difference through stresses.** For two energy-bounded forced solutions, the proposition expresses the localized pressure-gradient difference as the difference-field stress and its two cross stresses. (`Breakdown.ForcedPressureDifferenceStatement`)

Proved by `Breakdown.FracInternal.SpaceAssembly.pressureDifference`. Also proved from further statements by `Breakdown.forcedPressureDifference_of`.

**Local energy identity for differences.** For two forced solutions, the proposition gives continuity and the interior derivative formula for their localized difference energy. (`Breakdown.ForcedLocalEnergyStatement`)

Proved by `Breakdown.forcedLocalEnergy`.

**Fractional localization identity.** For a smooth L² field and compact smooth cutoff, the proposition gives the localized fractional pairing as cutoff dissipation, a scalar correction and a negative pair-square integral. (`Breakdown.FracLocalizationStatement`)

Proved by `Breakdown.fracLocalization`.

**Bound gradient energy by dissipation.** In the stated exponent range, the proposition requires nonnegative fractional energy and bounds gradient energy by ordinary plus fractional energy for compact smooth fields. (`Breakdown.FracGradientBoundStatement`)

Proved by `Breakdown.FracInternal.SpaceAssembly.gradientBound`. Also proved from further statements by `Breakdown.fracGradientBound_of`.

**Fractional energy of the cutoff field.** The cutoff dissipation is the fractional energy pairing of the field multiplied by the squared radial cutoff. (`Breakdown.cutoffFracDissipation`)

**Lower bound after localization.** For one less than α less than five quarters, the proposition bounds localized dissipation below by three quarters of cutoff dissipation minus an inverse-radius-square energy error. (`Breakdown.FracCutoffLowerBoundStatement`)

Proved from further statements by `Breakdown.fracCutoffLowerBound_of`.

**Cutoff L⁶ bound from fractional energy.** The sixth-norm proposition bounds a finite-energy field's cutoff L⁶ norm by its energy size plus the square root of cutoff fractional dissipation. (`Breakdown.FracSixthNormStatement`)

Proved from further statements by `Breakdown.fracSixthNorm_of`.

**Bound the difference-energy expression.** For the stated exponent range and difference data, the proposition controls the localized energy expression by the gradient bound times energy plus an inverse-radius error. (`Breakdown.FracDifferenceStatement`)

Proved by `Breakdown.FracInternal.SpaceAssembly.difference`. Also proved from further statements by `Breakdown.fracDifference_of`.

**Uniqueness with one bounded gradient.** For one less than α less than five quarters, two energy-bounded smooth solutions with identical initial velocity agree when one also has a bounded gradient. (`Breakdown.FracUniquenessStatement`)

Proved by `Breakdown.FracInternal.SpaceAssembly.uniqueness`. Also proved from further statements by `Breakdown.fracUniqueness_of`.

### Breakdown.Frac.StSpaceBlowup

This file declares the regularity and nonextension interfaces that connect the whole space mild trajectory to the final fractional obstruction.

**Smooth realization of a mild trajectory.** The regularity proposition requires a matching mild trajectory from compact test data to have a smooth physical solution with bounded energy and gradient and the same velocity almost everywhere. (`Breakdown.FracMildRegularStatement`)

Proved from further statements by `Breakdown.fracMildRegular_of`, `Breakdown.FracInternal.SpaceAssembly.mildRegular`.

**Obstruct an extension of the orbit.** The orbit-rate proposition excludes a continuous physical extension through time one for a trajectory approaching a nonzero recurrent orbit at the stated positive power rate. (`Breakdown.FracOrbitRateFalseStatement`)

Proved from further statements by `Breakdown.fracOrbitRateFalse`.

**Unit viscosity breakdown from a profile.** The unit-breakdown proposition turns rotating-profile existence into smooth compact divergence-free data with no global uniformly energy-bounded unit-viscosity solution. (`Breakdown.FracSpaceUnitBreakdownStatement`)

Proved from further statements by `Breakdown.FracInternal.SpaceAssembly.unitBreakdown_of_mild`, `Breakdown.fracSpaceUnitBreakdown_of`.

### Breakdown.Frac.StSpaceReg

This file defines the fractional mild symbol equation and declares the heat, local existence, persistence, energy, and physical realization interfaces for whole space regularity.

**Fractional heat symbol without clamping.** The symbol is the exponential of minus time times the fractional frequency rate. (`Breakdown.SmoothFlow.powerHeatSymbol`)

**Pointwise mild equation for symbols.** The mild-symbol predicate requires the heat evolution of the initial symbol plus the nonlinear memory integral to equal each frequency value on the interval. (`Breakdown.SmoothFlow.IsPowerMildSymbol`)

**The homogeneous heat part.** The heat part multiplies the initial symbol by the heat factor for the elapsed time. (`Breakdown.SmoothFlow.powerHeatPart`)

**The fractional mild fixed-point map.** The mild map adds the homogeneous heat part to the heat-weighted nonlinear integral of its input curve. (`Breakdown.SmoothFlow.powerMildMap`)

**The heat-weighted memory integral.** The mild integral convolves the forcing symbol with the fractional heat factor in time. (`Breakdown.SmoothFlow.powerMildIntegral`)

**A solenoidal symbol flow.** The symbol-flow predicate combines Sobolev continuity, the mild-symbol equation, solenoidality of every slice and the prescribed initial value. (`Breakdown.SmoothFlow.IsPowerSymbolFlow`)

**The fractional dissipation symbol.** The power symbol multiplies the input by twice pi times frequency norm raised to twice α. (`Breakdown.SmoothFlow.powerSymbol`)

**The time-derivative symbol.** The time-derivative symbol is minus the dissipation symbol plus the nonlinear symbol. (`Breakdown.SmoothFlow.powerTimeDerivSymbol`)

**Heat smoothing with a cubic weight.** The heat-gain proposition bounds the stated weighted heat square by a constant times the negative three-over-twice-α time power on bounded time ranges. (`Breakdown.SmoothFlow.PowerHeatGainStatement`)

Proved from further statements by `Breakdown.SmoothFlow.powerHeatGain`.

**Measurability and continuity of heat.** The heat-part proposition records measurability, contraction of all fractional norm squares and continuity in each finite Sobolev norm. (`Breakdown.SmoothFlow.PowerHeatPartStatement`)

Proved from further statements by `Breakdown.SmoothFlow.powerHeatPart_holds`.

**Gain half an order in the nonlinear part.** For a solenoidal mild H³ curve with a uniform fractional norm bound, the gain proposition requests a uniform half-order stronger bound after subtracting its heat part. (`Breakdown.SmoothFlow.PowerMildGainStatement`)

Proved from further statements by `Breakdown.SmoothFlow.powerMildGain_of`.

**Persistence of higher regularity.** The persistence proposition requires any Sobolev order at least three finite initially to remain a continuous Sobolev curve along the solenoidal mild H³ flow. (`Breakdown.SmoothFlow.PowerPersistStatement`)

Proved from further statements by `Breakdown.SmoothFlow.powerPersist_of`, `Breakdown.FracInternal.SpaceAssembly.persist`.

**Heat factors and their time integrals.** The basic-heat proposition records positivity, continuity in starting time and the displayed frequency-weighted time-integral bound. (`Breakdown.SmoothFlow.PowerHeatBasicStatement`)

Proved from further statements by `Breakdown.SmoothFlow.powerHeatBasic`.

**Bound a delayed memory integral.** The mild-bound proposition controls a heat-weighted forcing integral that vanishes before a chosen time by its later uniform bound and elapsed-time powers. (`Breakdown.SmoothFlow.PowerMildBoundStatement`)

No theorem in the library states this proposition as its result or names it.

**Subtract two mild symbol equations.** The mild-subtraction proposition expresses the difference of two same-initial-data mild curves as the heat integral of their nonlinear difference. (`Breakdown.SmoothFlow.PowerMildSubStatement`)

No theorem in the library states this proposition as its result or names it.

**Uniqueness of solenoidal mild symbols.** Two solenoidal mild H³ curves with the same initial symbol must agree throughout the interval under the uniqueness proposition. (`Breakdown.SmoothFlow.PowerMildUniqueStatement`)

No theorem in the library states this proposition as its result or names it.

**Weighted heat square integral bound.** The heat-weight proposition requests a uniform bound on the frequency-weighted heat square integral over intervals of length at most one. (`Breakdown.SmoothFlow.PowerHeatWeightStatement`)

Proved from further statements by `Breakdown.SmoothFlow.powerHeatWeight`.

**One-order gain in the heat integral.** The heat-integral proposition bounds the next Sobolev order of a measurable memory term by interval length times a uniform preceding-order forcing bound. (`Breakdown.SmoothFlow.PowerHeatIntegralStatement`)

Proved from further statements by `Breakdown.SmoothFlow.powerHeatIntegral_of`, `Breakdown.FracInternal.SpaceAssembly.heatIntegral`.

**Initial value and zero divergence.** The basic mild-map proposition records the exact initial value and preservation of solenoidality under the stated conjugate-symmetry assumptions. (`Breakdown.SmoothFlow.PowerMildMapBasicStatement`)

Proved by `Breakdown.SmoothFlow.powerMildMapBasic`.

**Size and difference bounds for the map.** For orders at least three and short intervals, the estimate proposition requests a quadratic size bound and the stated Lipschitz difference bound for the mild map. (`Breakdown.SmoothFlow.PowerMildMapEstStatement`)

Proved from further statements by `Breakdown.SmoothFlow.powerMildMapEst_of`.

**The memory integral is a Sobolev curve.** Joint measurability and a uniform order-n Sobolev bound must make the heat-weighted memory term a continuous curve of order n plus one. (`Breakdown.SmoothFlow.PowerMildIntegralCurveStatement`)

Proved from further statements by `Breakdown.SmoothFlow.powerMildIntegralCurve`.

**The mild map preserves curve regularity.** For order at least three, the proposition requires the mild map of a Sobolev curve with finite measurable initial data to remain a curve of that order. (`Breakdown.SmoothFlow.PowerMildMapCurveStatement`)

Proved from further statements by `Breakdown.SmoothFlow.powerMildMapCurve_of`.

**Existence of a mild-map fixed point.** For every bounded set of solenoidal initial symbols of order at least three, the fixed-point proposition requests a uniform positive lifespan and a conjugate-symmetric almost-everywhere fixed point. (`Breakdown.SmoothFlow.PowerFixedPointStatement`)

Proved from further statements by `Breakdown.SmoothFlow.powerFixedPoint_of`, `Breakdown.FracInternal.SpaceAssembly.fixedPoint`.

**Local existence of mild symbols.** The local-existence proposition requests a uniform positive lifespan for bounded initial Sobolev data, with exact initial value and the pointwise mild equation. (`Breakdown.SmoothFlow.PowerLocalStatement`)

Proved from further statements by `Breakdown.SmoothFlow.powerLocal_of`, `Breakdown.FracInternal.SpaceAssembly.localExistence`.

**Concatenate or restrict mild symbols.** The concatenation proposition permits joining matching H³ mild curves and restricting the final time of a mild-symbol solution. (`Breakdown.SmoothFlow.PowerConcatStatement`)

Proved from further statements by `Breakdown.SmoothFlow.powerConcat`.

**Pointwise bound on a mild symbol.** For each order at least three, the proposition bounds a solenoidal mild symbol by its initial norm plus a singular time integral of the convolution norm sum. (`Breakdown.SmoothFlow.PowerEnormMildStatement`)

Proved from further statements by `Breakdown.SmoothFlow.powerEnormMild`.

**Sobolev bound on a mild curve.** The Sobolev mild proposition bounds the norm by its initial value plus the stated heat-singular integral of the frequency L¹ norm times the Sobolev norm. (`Breakdown.SmoothFlow.PowerHsMildStatement`)

Proved from further statements by `Breakdown.SmoothFlow.powerHsMild_of`.

**Joint measurability of the symbol norm.** A mild H¹ symbol curve on a positive interval must have a jointly measurable extended norm under the measurability proposition. (`Breakdown.SmoothFlow.PowerAEMeasStatement`)

Proved from further statements by `Breakdown.SmoothFlow.powerAEMeas_of`.

**Differentiate a mild symbol in time.** When the nonlinear symbol is continuous in time at a fixed frequency, the proposition identifies the mild curve's derivative within the closed interval. (`Breakdown.SmoothFlow.PowerPointwiseDerivStatement`)

Proved from further statements by `Breakdown.SmoothFlow.powerPointwiseDeriv`.

**Frequencywise energy inequality.** The energy proposition bounds twice the time-integrated weighted dissipation by initial gradient energy plus the weighted nonlinear pairing bound at each frequency. (`Breakdown.SmoothFlow.PowerEnergyInequalityStatement`)

Proved from further statements by `Breakdown.SmoothFlow.powerEnergyInequality_of`.

**Integrated H² control from H¹.** The dissipation proposition gives uniform time-integrated homogeneous H² control for solenoidal mild curves with a uniform homogeneous H¹ bound. (`Breakdown.SmoothFlow.PowerDissipationStatement`)

Proved from further statements by `Breakdown.SmoothFlow.powerDissipation_of`.

**Higher Sobolev control from H¹.** The a priori proposition bounds each Sobolev norm of order at least three by its initial bound, time range and a uniform homogeneous H¹ bound. (`Breakdown.SmoothFlow.PowerAprioriStatement`)

Proved from further statements by `Breakdown.SmoothFlow.powerApriori_of`, `Breakdown.FracInternal.SpaceAssembly.apriori`.

**Smoothness of weighted symbol curves.** For a solenoidal mild curve of every Sobolev order, the weighted-curve proposition gives the stated derivative and every finite time-smoothness order in each weighted L¹ space. (`Breakdown.SmoothFlow.PowerWeightCurveStatement`)

Proved from further statements by `Breakdown.SmoothFlow.powerWeightCurve_of`, `Breakdown.FracInternal.SpaceAssembly.weightCurve`.

**Reconstruct the fractional image.** For a symbol integrable with three polynomial weights, the physical-power proposition identifies the fractional image of its reconstructed field with reconstruction of the multiplied symbol. (`Breakdown.SmoothFlow.PowerPhysPowerStatement`)

Proved from further statements by `Breakdown.SmoothFlow.powerPhysPower_of`.

**Smoothness of weighted pressure.** For a solenoidal mild curve of every Sobolev order, the pressure-curve proposition requests all time-smoothness orders in every weighted L¹ space. (`Breakdown.SmoothFlow.PowerPressureCurveStatement`)

Proved from further statements by `Breakdown.SmoothFlow.powerPressureCurve_of`.

**Smooth physical velocity and pressure.** The physical-curve proposition records joint smoothness, the time-derivative formula, symbol integrability and reconstruction formulas for dissipation and pressure gradient. (`Breakdown.SmoothFlow.PowerPhysCurveStatement`)

Proved from further statements by `Breakdown.SmoothFlow.powerPhysCurve_of`.

**Build a smooth fractional solution.** The solution proposition requires every solenoidal mild symbol curve of all Sobolev orders to reconstruct a finite-interval fractional solution. (`Breakdown.SmoothFlow.PowerSolutionOnStatement`)

Proved from further statements by `Breakdown.SmoothFlow.powerSolutionOn_of`, `Breakdown.FracInternal.SpaceAssembly.solutionOn`.

**Fourier representative of X-space heat.** The X-heat proposition identifies the heat operator's representative with pointwise multiplication by the clamped heat factor almost everywhere. (`Breakdown.SmoothFlow.PowerHeatXStatement`)

Proved by `Breakdown.SmoothFlow.powerHeatX`.

**Projected heat symbol and regularity.** The solenoidal-heat proposition records continuity, frequency symmetry, a uniform time bound and the projected Fourier representative of reconstructed integrable symbols. (`Breakdown.SmoothFlow.PowerSolenoidalStatement`)

Proved from further statements by `Breakdown.SmoothFlow.powerSolenoidal`.

**Physical form of the bilinear map.** For a measurable solenoidal symbol of every Sobolev order, the proposition identifies the concrete bilinear map's Fourier representative with the heat factor times the nonlinear symbol. (`Breakdown.SmoothFlow.PowerBilinPhysStatement`)

Proved from further statements by `Breakdown.SmoothFlow.powerBilinPhys_of`, `Breakdown.FracInternal.SpaceAssembly.bilinPhys`.

**Bounds for the continuous bilinear path.** For a solenoidal curve of every Sobolev order, the proposition requests time continuity before the endpoint and the stated singular-time bound on the bilinear term. (`Breakdown.SmoothFlow.PowerBilinContinuousStatement`)

Proved from further statements by `Breakdown.SmoothFlow.powerBilinContinuous_of`.

**Fourier form of the bilinear integral.** For a solenoidal smooth-symbol mild curve, the proposition records integrability of the X-valued bilinear term and its almost-everywhere Fourier integral formula. (`Breakdown.SmoothFlow.PowerBilinIntegralStatement`)

Proved from further statements by `Breakdown.SmoothFlow.powerBilinIntegral_of`.

**Identify the reconstructed mild curve.** The identification proposition requires the embedding of a reconstructed solenoidal mild curve of all Sobolev orders to satisfy the X-space mild equation. (`Breakdown.SmoothFlow.PowerIdentifyStatement`)

Proved from further statements by `Breakdown.SmoothFlow.powerIdentify_of`, `Breakdown.FracInternal.SpaceAssembly.identify`.

**Continue a regular symbol flow.** The flow proposition preserves every initial Sobolev order and supplies continuation to a target time when all partial H³ flows obey a common homogeneous H¹ bound. (`Breakdown.SmoothFlow.PowerFlowStatement`)

Proved from further statements by `Breakdown.SmoothFlow.powerFlow_of`, `Breakdown.FracInternal.SpaceAssembly.flow`.

### Breakdown.Frac.StSymbol

This file declares the Fourier transform and joint integrability identities for the fractional Taylor remainder.

**Plane-wave phase remainder.** The phase remainder is the complex Fourier character with its Taylor terms through order two subtracted. (`Breakdown.phaseRemainder`)

**Transform the Taylor remainder.** The remainder-transform proposition identifies a Schwartz field's translated second-order remainder transform with its original transform multiplied by the phase remainder. (`Breakdown.RemainderTransformStatement`)

Proved by `Breakdown.remainderTransform`.

**Integrate the joint remainder kernel.** For one less than α less than three halves, the proposition requests joint integrability of the singularly weighted norm of every Schwartz field's second-order remainder. (`Breakdown.RemainderProductIntegrableStatement`)

Proved by `Breakdown.remainderProductIntegrable`.

### Breakdown.Frac.StTorusApprox

This file defines the localized and periodized fractional profile approximation and its residual, and declares the decay and forced equation interfaces used in the torus route.

**Periodize over the integer lattice.** Lattice periodization sums the field over every integer-lattice translate of the evaluation point. (`Breakdown.Periodic.latticePeriodize`)

**Centered self-similar velocity.** The centered fractional self-similar field applies the prescribed shrinking spatial scale and amplitude to the rotating profile at similarity time. (`Breakdown.Periodic.fracSelfSimilar`)

**Centered self-similar pressure.** The centered fractional pressure applies the stated pressure amplitude, spatial scale and axial rotation at similarity time. (`Breakdown.Periodic.fracSelfSimilarPressure`)

**Localized self-similar velocity.** The approximate field applies the divergence-preserving central cutoff to the centered self-similar velocity. (`Breakdown.Periodic.fracApproxField`)

**Localize pressure relative to an anchor.** The approximate pressure multiplies the central cutoff by the self-similar pressure after subtracting its value at the pressure anchor. (`Breakdown.Periodic.fracApproxPressure`)

**Whole space approximation residual.** The space residual sums the localized velocity's time derivative, advection, fractional image and localized pressure gradient. (`Breakdown.Periodic.fracSpaceResidual`)

**Residual after periodization.** The periodic residual applies the same momentum expression to the periodized approximate velocity and pressure. (`Breakdown.Periodic.fracApproxResidual`)

**The centered profile solves the equation.** The proposition requires a unit-viscosity rotating profile to produce smooth centered velocity and pressure satisfying incompressibility and fractional momentum before the terminal time. (`Breakdown.Periodic.FracSelfSimilarSolves`)

**Decay of the centered self-similar field.** For a unit-viscosity profile and terminal time at most one, the decay proposition gives uniform bounds on three spatial derivatives, the time derivative and pressure gradient. (`Breakdown.Periodic.FracSelfSimilarDecay`)

**Support of the approximate field.** The approximate-field proposition records smoothness, incompressibility, vanishing beyond the outer cutoff and agreement with the self-similar velocity in the core. (`Breakdown.Periodic.FracApproxFieldProperties`)

**Bound the fractional power pointwise.** The pointwise proposition bounds the fractional image using a local third-derivative bound, lower derivatives at the point and a weighted far-field integral. (`Breakdown.Periodic.FracPointwiseBound`)

**Bound the fractional periodization tail.** For a smooth centrally supported field, the proposition bounds the difference between fractional images before and after periodization on the unit cell by its L¹ size. (`Breakdown.Periodic.FracPeriodizationTail`)

**Whole-space approximate residual bound.** The space-residual proposition bounds the localized residual by a profile-dependent constant times the stated singular power of remaining time. (`Breakdown.Periodic.FracSpaceResidualBound`)

**Residual bound on a specified region.** The regional residual proposition requests the same remaining-time bound restricted to the chosen spatial region. (`Breakdown.Periodic.FracResidualRegionBound`)

**The inner core region.** The core consists of points at most one quarter of the central radius from the center. (`Breakdown.Periodic.coreRegion`)

**The cutoff transition shell.** The shell consists of points between one quarter and one half of the central radius from the center. (`Breakdown.Periodic.shellRegion`)

**The exterior region.** The exterior consists of points at least one half of the central radius from the center. (`Breakdown.Periodic.outerRegion`)

**Periodic approximate residual bound.** The periodic residual proposition bounds the fully periodized momentum residual by the stated remaining-time power. (`Breakdown.Periodic.FracApproxResidualBound`)

**A forced equation for the approximation.** For every closed interval before the terminal time, the proposition requires the periodized approximate velocity and pressure to solve the fractional forced periodic equation with their own residual. (`Breakdown.Periodic.FracApproxForcedSolution`)

### Breakdown.Frac.StTorusBasic

This file defines fractional torus heat and nonlinear kernel realizations and declares their algebra, sharp bound, and mild uniqueness interfaces.

**Fractional heat factor on lattice modes.** The lattice heat factor is the exponential of minus the fractional lattice rate times the nonnegative part of time. (`Breakdown.Periodic.fracLatticeFactor`)

**Specification of torus heat evolution.** The torus heat specification requires each output Fourier coefficient to be the input coefficient multiplied by the lattice heat factor. (`Breakdown.Periodic.FracTorusHeatSpec`)

**Choose the fractional torus heat map.** The torus heat operator chooses a continuous linear realization of its coefficient specification when one exists and otherwise is zero. (`Breakdown.Periodic.fracTorusHeat`)

**Torus kernel Fourier coefficients.** At positive time, the kernel coefficients are the projected symmetric advection coefficients multiplied by minus one half of the heat factor; otherwise they are zero. (`Breakdown.Periodic.fracTorusKernelCoef`)

**Specification of the torus kernel.** The torus kernel specification requires its continuous bilinear operator to have the prescribed coefficient formula at every lattice mode. (`Breakdown.Periodic.FracTorusKernelSpec`)

**Choose the fractional torus kernel.** The torus bilinear kernel chooses a continuous realization of its coefficient specification when one exists and otherwise is zero. (`Breakdown.Periodic.fracTorusKernel`)

**Torus mild solution before the endpoint.** The half-open torus mild predicate requires continuity and an integrable heat-plus-bilinear formula before the final time. (`Breakdown.Periodic.IsFracTorusMildOn`)

**Closed-interval torus mild solution.** The closed torus mild predicate requires continuity and an integrable heat-plus-bilinear formula including both endpoints. (`Breakdown.Periodic.IsFracTorusMildOnIcc`)

**Existence of the torus heat operator.** The heat-existence proposition requests an operator with the prescribed lattice coefficients at every time. (`Breakdown.Periodic.FracTorusHeatExists`)

**Existence of the torus bilinear kernel.** The kernel-existence proposition requests a continuous bilinear operator with the prescribed coefficients at every time. (`Breakdown.Periodic.FracTorusKernelExists`)

**Fractional torus heat laws.** The heat-algebra proposition records the coefficient formula, identity, nonnegative-time composition, contraction, time clamping and strong continuity. (`Breakdown.Periodic.FracTorusHeatAlgebra`)

**Fractional torus kernel laws.** The kernel-algebra proposition records its coefficient formula, symmetry, positive-time continuity and compatibility with later heat evolution. (`Breakdown.Periodic.FracTorusKernelAlgebra`)

**Sharp short-time torus kernel bound.** The sharp-bound proposition controls the torus kernel norm by a positive constant times the negative three-over-four-α power of time up to time one. (`Breakdown.Periodic.FracTorusKernelSharpBound`)

**Uniqueness of torus mild solutions.** A half-open and a closed-interval torus mild solution with the same initial value must agree before the endpoint. (`Breakdown.Periodic.FracTorusMildUniqueness`)

### Breakdown.Frac.StTorusCoef

This file declares the plane wave, symmetry, and Fourier coefficient identities that connect the periodic fractional power to the torus evolution.

**Plane waves are fractional eigenfields.** The plane-wave proposition requires a cosine wave times a constant vector to have fractional eigenvalue equal to frequency norm raised to twice α. (`Breakdown.Periodic.PlaneWaveEigen`)

**Fractional symmetry on the torus.** For smooth periodic fields, the proposition requires integrability of the fractional image on the cell and symmetry of the cell integral pairing. (`Breakdown.Periodic.PeriodicSymmetry`)

**Fractional action on Fourier modes.** The coefficient proposition requires the fractional image of a smooth periodic field to multiply each Fourier coefficient by the fractional lattice rate. (`Breakdown.Periodic.CoefFractional`)

### Breakdown.Frac.StTorusForce

This file defines periodic fractional forcing and forced solution notions, and declares their Fourier, smoothing, and mild representation interfaces.

**Projected forcing coefficients.** At positive time, the forcing coefficients are the solenoidal projection of the field coefficients times the heat factor; otherwise they are zero. (`Breakdown.Periodic.fracTorusForceCoef`)

**Specification of the torus forcing field.** The forcing specification requires the torus vector to have the prescribed heat-weighted projected coefficients. (`Breakdown.Periodic.FracTorusForceSpec`)

**Choose the torus forcing state.** The forcing field chooses a torus vector realizing its coefficient specification when one exists and otherwise is zero. (`Breakdown.Periodic.fracTorusForce`)

**Existence of the torus forcing field.** The forcing-existence proposition requests a realization of the coefficient specification for every field and time. (`Breakdown.Periodic.FracTorusForceExists`)

**Algebra and continuity of torus forcing.** The forcing-algebra proposition records its coefficient formula, positive-time heat factorization and continuity. (`Breakdown.Periodic.FracTorusForceAlgebra`)

**Fractional smoothing of periodic forcing.** The smoothing proposition controls the torus norm of a continuous periodic force by the stated time power times its cell L² norm. (`Breakdown.Periodic.FracForceSmoothing`)

**Forced mild equation on the torus.** The forced mild predicate adds an integrable projected-forcing memory term to the continuous torus heat-plus-bilinear equation. (`Breakdown.Periodic.IsFracTorusForcedMildOnIcc`)

**A smooth forced periodic solution.** The periodic solution predicate records smooth velocity and pressure, continuous forcing, periodicity, incompressibility and the forced fractional momentum equation. (`Breakdown.Periodic.IsFracForcedPeriodicSolution`)

**Smooth forced solutions are mild.** On a positive-length interval, the proposition requires a smooth forced periodic solution to satisfy the closed-interval forced mild equation after conversion to V. (`Breakdown.Periodic.FracForcedPeriodicIsMild`)

### Breakdown.Frac.StTorusInverse

This file defines the whole space and torus sequence operators whose right inverses are compared in the periodic transfer construction.

**Whole-space shell-to-sequence map.** The whole-space Lambda operator sums weighted piece convolutions of the shell response for each approximant entry. (`Breakdown.Periodic.fracR3Lambda`)

**Torus shell-to-sequence map.** The torus Lambda operator sums the corresponding weighted shell convolutions using the scale of each geometric time step. (`Breakdown.Periodic.fracTorusLambda`)

**Restrict the torus sequence to shells.** The torus restriction applies the scaled spatial restriction to every time piece in the sequence. (`Breakdown.Periodic.fracTorusRestrict`)

**Shift the whole-space recurrence.** The whole-space shift sends the preceding endpoint through the free step map with the inverse recurrence weight. (`Breakdown.Periodic.fracR3Shift`)

**Shift the torus recurrence.** The torus shift propagates each preceding endpoint through the next step's heat map with the stated scale-to-weight factor. (`Breakdown.Periodic.fracTorusShift`)

**Seed the whole-space sequence.** The whole-space seed puts the free evolution of the chosen initial-data map in the first sequence position. (`Breakdown.Periodic.fracR3Seed`)

**Seed the torus sequence.** The torus seed puts the first scaled heat evolution of its initial-data map in the first sequence position. (`Breakdown.Periodic.fracTorusSeed`)

**Whole-space correction operator.** The whole-space operator subtracts the recurrence shift, initial seed and profile-linearized bilinear term from the correction sequence. (`Breakdown.Periodic.fracR3Op`)

**Torus correction operator.** The torus operator subtracts the scaled recurrence shift, initial seed and stepwise linearized bilinear term from the correction sequence. (`Breakdown.Periodic.fracTorusOp`)

**Right inverse for the base recurrence.** The base-inverse proposition requests a short-step weighted recurrence with finite-dimensional initial correction and a continuous right inverse. (`Breakdown.Periodic.FracBaseInverse`)

**Whole-space chain factorization.** For a matching bilinear framework and an admissible step interval, the proposition identifies the shell-factorized chain operator with the whole-space correction operator. (`Breakdown.Periodic.FracR3ChainEq`)

**Torus chain factorization.** Under the stated time, scale and shell-support conditions, the proposition identifies the shell-factorized torus chain with its correction operator. (`Breakdown.Periodic.FracTorusChainEq`)

**Operator stability under profile changes.** The difference-bound proposition controls changes in whole-space and torus correction operators by the uniform profile-piece error times the stated quarter-power step bound. (`Breakdown.Periodic.FracOpDiffBounds`)

**Uniform bounds for the chain components.** The operator-bound proposition controls both Lambda maps, both restrictions and both recurrence shifts under their stated scale and support conditions. (`Breakdown.Periodic.FracOperatorNormBounds`)

**Small comparison of inverse chains.** For fixed finite-dimensional test data and approximants, the proposition makes the restricted torus inverse-chain Lambda and seed terms arbitrarily close to their whole-space counterparts at small terminal time. (`Breakdown.Periodic.FracComparisonSmall`)

### Breakdown.Frac.StTorusReduce

This file declares the smooth to mild, pressure drift, and torus blowup interfaces used to derive the final periodic fractional obstruction.

**Periodic smooth solutions are mild.** The proposition requires every global fractional solution with periodic velocity and pressure to satisfy the torus mild equation on each positive finite interval. (`Breakdown.Periodic.FracTorusSmoothIsMild`)

**Recover periodic pressure by a drift.** The drift proposition turns a solution with periodic velocity into another with the same initial datum and both periodic velocity and pressure. (`Breakdown.Periodic.FracTorusDrift`)

**An unbounded torus mild trajectory.** The blow-up predicate requests smooth periodic divergence-free initial data and a mild trajectory whose V norm is unbounded before a positive terminal time. (`Breakdown.Periodic.FracTorusBlowup`)

### Breakdown.Frac.StTorusShell

This file defines the similarity scale, source operators, and Fourier densities for comparing localized whole space and torus heat evolutions.

**Fractional similarity scale.** The similarity scale is the positive-time scale raised to the reciprocal of α. (`Breakdown.Periodic.simScale`)

**A rescaled torus source field.** At positive scale, the source field applies torus forcing at rescaled time to the physically rescaled L² input; at other scales it is zero. (`Breakdown.Periodic.fracSourceFun`)

**Specification of the source operator.** The source-operator specification requires a continuous linear map to agree with the rescaled source field for every L² input. (`Breakdown.Periodic.FracSourceOpSpec`)

**Choose the rescaled source operator.** The source operator chooses a continuous linear realization of its specification when one exists and otherwise is zero. (`Breakdown.Periodic.fracSourceOp`)

**Existence of the source operator.** The source-existence proposition requests a continuous linear realization for every scale and time. (`Breakdown.Periodic.FracSourceOpExists`)

**Continuity of the source response.** For positive scale, the source-continuity proposition requires the response to each fixed L² input to be continuous at positive times. (`Breakdown.Periodic.FracSourceOpContinuous`)

**Continuity of projected physical heat.** The proposition requires the projected fractional heat response to every L² input to be continuous at positive times. (`Breakdown.Periodic.FracHeatSolenoidalContinuous`)

**Whole-space response to shell advection.** The whole-space shell response is minus projected fractional heat applied to the test-field shell-advection map. (`Breakdown.Periodic.fracLambdaR3`)

**Torus response to shell advection.** The torus shell response is the negative rescaled source operator applied to shell advection, with the specified fractional scale factor. (`Breakdown.Periodic.fracLambdaTorus`)

**Factor the whole-space bilinear map.** For a test field supported in the shell radius, the proposition factors twice the bilinear map through shell restriction and the whole-space shell response. (`Breakdown.Periodic.FracR3Factor`)

**Bound the whole-space shell response.** The shell-response proposition bounds its norm by the test-field X norm, shell-data norm and the stated singular time power. (`Breakdown.Periodic.FracR3LambdaBound`)

**Factor the rescaled torus bilinear map.** Under the stated scale and support conditions, the proposition factors the normalized torus bilinear action through shell restriction and the torus response. (`Breakdown.Periodic.FracTorusFactor`)

**Bound the torus shell response.** Under the stated scale, shell and time conditions, the torus shell response obeys the same singular-time norm bound as the whole-space response. (`Breakdown.Periodic.FracTorusLambdaBound`)

**Compare localized solenoidal heat.** For supported L² inputs and times bounded away from zero, sufficiently small spatial scaling makes the two restricted projected-heat responses close relative to the input L³ᐟ² size. (`Breakdown.Periodic.FracHeatSolenoidalComparison`)

**Compare free heat after localization.** For compact test data and a bounded nonnegative time range, sufficiently small scaling makes the restricted transplanted torus heat field close to the whole-space heat field. (`Breakdown.Periodic.FracFreeHeatComparison`)

**Fourier density for projected velocity.** The projected value density multiplies the Fourier transform's solenoidal projection by the heat factor and spatial Fourier character. (`Breakdown.Periodic.fracValueDensity`)

**Fourier density for a projected gradient.** The projected gradient density multiplies the value density by the corresponding imaginary coordinate-frequency factor. (`Breakdown.Periodic.fracGradDensity`)

**Fourier density for free heat.** The free heat density multiplies the test field's Fourier transform by the heat factor and spatial Fourier character. (`Breakdown.Periodic.fracFreeDensity`)

**Fourier density for the free gradient.** The free gradient density multiplies the free heat density by the corresponding imaginary coordinate-frequency factor. (`Breakdown.Periodic.fracFreeGradDensity`)

**Lattice-series formula for the source.** Under the stated scale and support assumptions, the source-series proposition identifies rescaled torus velocity and gradients with lattice sums of their projected heat densities. (`Breakdown.Periodic.FracTorusSourceSeries`)

**Lattice-series formula for free heat.** Under the stated scale and test-support assumptions, the free-series proposition identifies rescaled torus heat values and gradients with lattice sums of their densities. (`Breakdown.Periodic.FracTorusFreeSeries`)

**Factor the solenoidal heat operator.** For a compactly supported L² input at positive time, the factor proposition requests a projected heat symbol whose half-power image is the solenoidal heat field. (`Breakdown.Periodic.FracHeatSolenoidalFactor`)

**Whole-space projected heat formulas.** For a supported L² input at positive time, the proposition gives almost-everywhere velocity and partial-derivative formulas by integration of their projected densities. (`Breakdown.Periodic.FracR3ValueFormula`)

**Whole-space free heat formulas.** For a compact test field at nonnegative time, the proposition gives almost-everywhere velocity and derivative formulas by integration of the free densities. (`Breakdown.Periodic.FracR3FreeFormula`)

**Decay of projected heat densities.** Uniformly supported inputs with L³ᐟ² size at most one give fourth-order frequency decay of projected value and gradient densities over the stated bounded position and positive-time ranges. (`Breakdown.Periodic.FracSourceDensityBounds`)

**Source density frequency increments.** On frequency annuli away from zero, the proposition requests uniform Lipschitz bounds for the projected value and gradient densities under the stated support and norm bounds. (`Breakdown.Periodic.FracSourceDensityIncrement`)

**Decay of free heat densities.** For fixed compact test data, the free value and gradient densities have uniform fourth-order frequency decay over the stated bounded position and nonnegative-time ranges. (`Breakdown.Periodic.FracFreeDensityBounds`)

**Frequency increments of free densities.** For fixed compact test data, the proposition requests uniform Lipschitz frequency bounds on annuli for free value and gradient densities. (`Breakdown.Periodic.FracFreeDensityIncrement`)

### Breakdown.Frac.StTorusStep

This file defines the fractional step framework and physical gluing operation, together with the mildness and unboundedness contracts for the glued path.

**Choose the step-kernel constant.** The step constant is chosen from the proved sharp short-time torus kernel bound. (`Breakdown.Periodic.fracStepCK`)

**A chosen bound for the step kernel.** For α greater than one, the chosen step constant is positive and gives the stated kernel norm bound for positive times at most one. (`Breakdown.Periodic.fracStepCK_spec`)

**The fractional torus step framework.** For α greater than one and scale between zero and one, the step framework rescales the torus heat and bilinear operators into a heat-and-bilinear framework. (`Breakdown.Periodic.fracStepFrame`)

**Glue the fractional torus pieces.** The torus glue map selects the appropriate geometric time piece, evaluates it at local time and rescales its amplitude by the inverse dilation weight. (`Breakdown.Periodic.fracGluePieces`)

**Mildness of glued torus pieces.** Matching mild step pieces must glue to a torus mild trajectory, with the stated exact evaluation formula at every local step time. (`Breakdown.Periodic.FracGlueMild`)

**Unbounded norm after gluing.** The unboundedness proposition requires uniformly nonzero base pieces plus geometrically decaying bounded corrections to produce a glued trajectory with unbounded norm before the terminal time. (`Breakdown.Periodic.FracGlueUnbounded`)

### Breakdown.Frac.StTorusStepApprox

This file defines approximate torus pieces and the matching, residual, size, closeness, and transplantation interfaces needed to perturb them into a genuine trajectory.

**One scaled approximate torus piece.** The approximate piece converts the periodized localized velocity to V at the step's physical time and multiplies it by the step dilation weight. (`Breakdown.Periodic.fracApproxPiece`)

**Evaluate and match approximate pieces.** The approximate-links proposition records the pieces' explicit values and their endpoint matching under the geometric dilation weight. (`Breakdown.Periodic.FracApproxLinks`)

**Control weighted approximate residuals.** When the recurrence weight exceeds the stated scale power, the proposition bounds each approximate mild-equation defect by its geometric weight times a positive power of terminal time. (`Breakdown.Periodic.FracApproxResidualSmall`)

**Keep approximate pieces close.** A whole-space approximant close to the profile pieces must remain close to the localized torus pieces, up to any further tolerance at small terminal time. (`Breakdown.Periodic.FracApproxClose`)

**Bound sizes of approximate pieces.** A positive lower bound on the embedded rotating profile gives uniformly bounded approximate pieces with at least half that lower norm at sufficiently small terminal time. (`Breakdown.Periodic.FracApproxSizes`)

**Keep the transplanted datum close.** For supported compact test data, the transplanted initial torus datum differs from the initial approximate piece by at most the original X error plus any chosen small tolerance. (`Breakdown.Periodic.FracDatumClose`)

**Approximate all recurrent profile pieces.** The approximant-existence proposition requests one positive support radius and finite test-field approximant uniformly close to every piece of the recurrent profile. (`Breakdown.Periodic.FracApproximantExists`)

### Breakdown.Frac.StTorusStepCompare

This file defines step entries and declares the chain, frame, finite window, tail, source, and seed comparisons used to transfer the whole space inverse to the torus.

**A whole-space recurrence step.** The whole-space step map propagates an endpoint through the free evolution and divides by the recurrence weight. (`Breakdown.Periodic.fracR3Step`)

**A torus recurrence step.** The torus step map propagates an endpoint using the next geometric scale and the stated amplitude-to-weight factor. (`Breakdown.Periodic.fracTorusStep`)

**A restricted whole-space chain entry.** The whole-space entry restricts to shell data the propagated Lambda response from one sequence position to another. (`Breakdown.Periodic.fracR3Entry`)

**A restricted torus chain entry.** The torus entry restricts the propagated Lambda response using the destination step's similarity scale. (`Breakdown.Periodic.fracTorusEntry`)

**Formula for a whole-space shift chain.** Under the stated concrete framework assumptions, the proposition expresses an iterated recurrence step as weighted dilation and heat evolution of its starting endpoint. (`Breakdown.Periodic.FracR3ChainFormula`)

**Formula for a torus shift chain.** Under the stated geometric-scale assumptions, the proposition expresses an iterated torus recurrence as a weighted heat evolution of its starting endpoint. (`Breakdown.Periodic.FracTorusChainFormula`)

**Shift heat through projected heat.** At nonnegative additional time and positive kernel time, the proposition requires ordinary fractional heat followed by projected heat to add their times. (`Breakdown.Periodic.FracHeatSolenoidalShift`)

**Integral formula for whole-space Lambda.** For an admissible interval, the proposition evaluates the whole-space Lambda map as the finite sum of weighted shell-response integrals. (`Breakdown.Periodic.FracR3LambdaFormula`)

**Integral formula for torus Lambda.** Under the stated scale and support conditions, the proposition evaluates the torus Lambda map as the finite sum of weighted scaled shell-response integrals. (`Breakdown.Periodic.FracTorusLambdaFormula`)

**Formula for whole-space chain entries.** The proposition expresses each restricted whole-space entry as the weighted, dilated projected-heat integral over the initial or complete source interval. (`Breakdown.Periodic.FracR3EntryFormula`)

**Formula for torus chain entries.** Under the stated scale and support conditions, the proposition expresses each torus entry as the matching weighted source-operator integral. (`Breakdown.Periodic.FracTorusEntryFormula`)

**Change the comparison frame.** The frame-change proposition bounds a rescaled torus-versus-space restriction error by the original error at the enlarged radius times the dilation weight. (`Breakdown.Periodic.FracFrameChange`)

**Compare any finite window of entries.** For an admissible recurrence, sufficiently small terminal time makes every entry difference within a chosen finite step window uniformly small relative to the input sequence norm. (`Breakdown.Periodic.FracWindowBound`)

**Geometric bound for distant entries.** For an admissible recurrence, the tail proposition bounds both torus and whole-space entries by a common constant times the geometric shift ratio to the step distance. (`Breakdown.Periodic.FracTailBound`)

**Formula for the whole-space seed inverse.** The proposition evaluates the inverse-shift response to a whole-space seed using the specified heat time, dilation and inverse recurrence weight. (`Breakdown.Periodic.FracR3SeedEntry`)

**Formula for the torus seed inverse.** The proposition evaluates the inverse-shift response to a torus seed using the stated geometric amplitude and physical heat time. (`Breakdown.Periodic.FracTorusSeedEntry`)

**Comparison of the Lambda inverse chains.** Under the stated admissibility conditions, the Lambda-comparison proposition makes the two restricted inverse-chain operators arbitrarily close in norm at sufficiently small terminal time. (`Breakdown.Periodic.FracLambdaComparison`)

**Comparison of finite-dimensional seeds.** For a finite-dimensional supported test lift, the seed-comparison proposition makes the torus and whole-space restricted inverse-seed operators arbitrarily close at small terminal time. (`Breakdown.Periodic.FracSeedComparison`)

### Breakdown.Frac.TorusApproxClose

This file proves that rescaled localized fractional profiles remain close to the original rotating slices, supplying the approximation comparison on the torus route.

**Bound a coordinate difference.** Each coordinate difference between two real vectors is at most their distance in absolute value. (`Breakdown.Periodic.TorusApproxClose.Internal.coord_le`)

**Coordinates of a lattice frequency.** Each lattice frequency coordinate is the corresponding integer coordinate cast to the reals. (`Breakdown.Periodic.TorusApproxClose.Internal.freq_coord`)

**Coordinates of the cell center.** Every coordinate of the chosen cell center is one half. (`Breakdown.Periodic.TorusApproxClose.Internal.center_coord`)

**Wrapping as an integer translation.** The wrapping map equals the original point shifted by the displayed rounded lattice vector. (`Breakdown.Periodic.TorusApproxClose.Internal.wrap_eq`)

**Periodization equals the wrapped value.** For a field vanishing outside the central support region, its lattice periodization equals its value at the wrapped point. (`Breakdown.Periodic.TorusApproxClose.Internal.periodize_wrap`)

**Derivative under two scalar rescalings.** The derivative of an amplitude-scaled and spatially scaled field is the original derivative multiplied by the product of the two scales. (`Breakdown.Periodic.TorusApproxClose.Internal.fderiv_scale_apply`)

**Scaling of gradient energy.** For positive spatial scale, gradient energy scales by amplitude squared divided by spatial scale. (`Breakdown.Periodic.TorusApproxClose.Internal.gradEnergy_scale`)

**Scaling of the L² integral.** For positive spatial scale, the field's square integral scales by amplitude squared divided by spatial scale cubed. (`Breakdown.Periodic.TorusApproxClose.Internal.mass_scale`)

**Square root of the similarity scale.** For positive scale, the square root of the fractional similarity scale is the scale to the reciprocal of twice α. (`Breakdown.Periodic.TorusApproxClose.Internal.sqrt_simScale`)

**Combine fractional amplitude factors.** For positive α and scale, the displayed transplantation and velocity factors multiply to the X-space dilation weight. (`Breakdown.Periodic.TorusApproxClose.Internal.amp_eq`)

**Simplify the mass scaling exponent.** Under the stated positivity assumptions, the compound mass-scaling expression reduces to the displayed power of the product scale. (`Breakdown.Periodic.TorusApproxClose.Internal.mass_exp`)

**Split a dilation difference.** The dilation algebra bounds the difference of two dilated vectors by the scaled input difference plus the scale change on one fixed vector. (`Breakdown.Periodic.TorusApproxClose.Internal.fdil_split`)

**Continuity of the dilated profile piece.** Dilation algebra, dilation continuity and continuity of the embedded profile give continuity of its self-similar piece on every closed interval ending before one. (`Breakdown.Periodic.TorusApproxClose.Internal.fprofileContinuous`)

**Prove closeness of torus approximations.** For 1 < α < 5/4, the transplantation norm and smoothness, approximate field and matching, embedding and dilation, rotating slice continuity, self similar decay, and cutoff closeness hypotheses ensure that any supported approximant within ε of every whole space profile piece is within ε + δ of every torus approximate piece when the positive terminal time is sufficiently small. (`Breakdown.Periodic.fracApproxClose`)

### Breakdown.Frac.TorusApproxCloseAux

This file introduces the rescaled cutoff and its closeness contract, isolating the spatial comparison used by the torus approximate pieces.

**Pull the cutoff field to profile scale.** The pulled-back cutoff field applies fractional amplitude scaling and recenters the localized approximate velocity at the chosen spatial scale. (`Breakdown.Periodic.fracCutAt`)

**Cutoff approximation in energy and mass.** The cutoff-closeness proposition requests vanishing gradient error against the rotating profile and the stated scale-dependent L² bound for the pulled-back cutoff field. (`Breakdown.Periodic.FracCutoffClose`)

### Breakdown.Frac.TorusApproxDatum

This file controls the initial localized and transplanted datum, connecting the finite dimensional perturbation data to the desired smooth periodic initial field.

**Periodization by a wrapped point.** For a field supported within one eighth of the center, lattice periodization equals evaluation at the wrapped point. (`Breakdown.Periodic.TorusApproxDatum.Internal.periodize_wrap`)

**The initial rotating slice is unchanged.** At similarity time zero, the rotating slice equals the original profile. (`Breakdown.Periodic.TorusApproxDatum.Internal.slice_zero`)

**Positive powers under a product bound.** If the product of two positive numbers is at most one, a nonnegative power of the second is bounded by the inverse power of the first. (`Breakdown.Periodic.TorusApproxDatum.Internal.rpow_le_of_mul`)

**Bound inverse powers of products.** The stated lower bound on the product of two positive numbers bounds the negative power of the second by a fixed power of the first. (`Breakdown.Periodic.TorusApproxDatum.Internal.rpow_neg_le_of_mul`)

**Square a real power.** For a positive base, squaring its real power doubles the exponent. (`Breakdown.Periodic.TorusApproxDatum.Internal.sq_rpow`)

**Tail estimate for profile gradients.** Under the stated positive scale and lower product bound, the squared fractional gradient decay is bounded by the displayed integrable tail weight. (`Breakdown.Periodic.TorusApproxDatum.Internal.tail_bound`)

**Inner estimate for profile mass.** For α below five quarters and the stated positive scale product bound, the scaled profile square is bounded by the displayed common decay weight. (`Breakdown.Periodic.TorusApproxDatum.Internal.inner_bound`)

**Shell estimate in a common weight.** For α greater than one and the stated scale product bound, the shell power is bounded by the displayed common decay weight. (`Breakdown.Periodic.TorusApproxDatum.Internal.shell_bound`)

**Rescale a field about the cell center.** The rescaled field multiplies its amplitude and evaluates it at the cell center plus a spatially scaled argument. (`Breakdown.Periodic.TorusApproxDatum.Internal.scaledAt`)

**Derivative of the centered rescaling.** For a differentiable field, the centered rescaling has derivative equal to amplitude times spatial scale times the original derivative. (`Breakdown.Periodic.TorusApproxDatum.Internal.hasFDerivAt_scaledAt`)

**Evaluate the rescaled derivative.** The derivative of the centered rescaling equals the original derivative at the recentered point multiplied by the product of scales. (`Breakdown.Periodic.TorusApproxDatum.Internal.fderiv_scaledAt`)

**Smoothness of the centered rescaling.** Centered spatial rescaling and constant amplitude multiplication preserve smoothness. (`Breakdown.Periodic.TorusApproxDatum.Internal.contDiff_scaledAt`)

**Rescaling preserves zero divergence.** A centered rescaling of a differentiable divergence-free field remains divergence-free. (`Breakdown.Periodic.TorusApproxDatum.Internal.div_scaledAt`)

**Distance after centered scaling.** For nonnegative scale, distance from the rescaled point to the center equals the scale times the original norm. (`Breakdown.Periodic.TorusApproxDatum.Internal.dist_scaled`)

**Support of the pulled-back field.** For positive spatial scale, pulling back a centrally supported field places its support in the stated inverse-scale ball. (`Breakdown.Periodic.TorusApproxDatum.Internal.tsupport_scaledAt`)

**Bound derivatives outside the core.** For the stated profile and exponent range, the decay and approximation interfaces uniformly bound derivatives through order three outside the core region. (`Breakdown.Periodic.TorusApproxDatum.Internal.shell_derivs`)

**Coordinate vectors have unit norm.** Every standard coordinate vector has norm one. (`Breakdown.Periodic.TorusApproxDatum.Internal.unit_norm`)

**Pointwise gradient error of the cutoff.** The stated core agreement, exterior vanishing, shell and profile derivative bounds imply the displayed decaying pointwise bound for the gradient difference. (`Breakdown.Periodic.TorusApproxDatum.Internal.grad_point`)

**Pointwise mass bound for the cutoff.** The stated core agreement, exterior vanishing, shell bound and profile decay imply the displayed weighted pointwise mass estimate. (`Breakdown.Periodic.TorusApproxDatum.Internal.mass_point`)

**Recover the profile in the inner region.** Under the approximation interface and the specified relation between time and spatial scale, the rescaled initial approximate field equals the profile in the inner region. (`Breakdown.Periodic.TorusApproxDatum.Internal.inner_eq`)

**Integrate a common radial majorant.** For α greater than one, a nonnegative function bounded by the displayed integrable radial weight has integral bounded by the same weighted integral. (`Breakdown.Periodic.TorusApproxDatum.Internal.integral_weight_le`)

**A positive scaling power tends to zero.** For positive α, exponent and tolerance, the specified power of the fractional time scale is eventually below that tolerance as time decreases to zero. (`Breakdown.Periodic.TorusApproxDatum.Internal.eventually_small`)

**Prove closeness of initial torus data.** For 1 < α < 5/4, the transplantation norm and smoothness, approximate field and matching, state additivity, and self similar decay hypotheses ensure that a supported test datum's transplanted initial state differs from the first torus approximate piece by at most its whole space distance from the rotating profile plus any prescribed positive δ when the terminal time is small enough. (`Breakdown.Periodic.fracDatumClose`)

### Breakdown.Frac.TorusApproxField

This file supplies the support, smoothness, and inner agreement properties of the localized fractional approximate field.

**Construct the localized field properties.** The self similar solution and homotopy curl hypotheses make every rotating profile's localized approximate velocity and pressure jointly smooth before each positive terminal time, with zero velocity divergence, both fields zero beyond half the central radius, and velocity equal to the similarity field within one quarter of that radius. (`Breakdown.Periodic.fracApproxFieldProperties_of`)

### Breakdown.Frac.TorusApproxForced

This file shows that the periodized fractional approximation satisfies a forced periodic equation with the declared residual.

**Choose a nearby lattice translate.** The nearby lattice index negates the rounded displacement of each coordinate from one half. (`Breakdown.Periodic.ApproxForced.Internal.nearIndex`)

**Lattice frequency coordinates.** Each lattice frequency coordinate is the real cast of its integer coordinate. (`Breakdown.Periodic.ApproxForced.Internal.freq_coord`)

**The center is at one half.** The cell center has one half in each coordinate. (`Breakdown.Periodic.ApproxForced.Internal.center_coord`)

**Coordinate displacement bound.** The absolute difference of any coordinate is bounded by the distance between the two vectors. (`Breakdown.Periodic.ApproxForced.Internal.coord_le`)

**Local formula for periodization.** For a centrally supported field, its periodization near a point equals the field evaluated at one fixed nearby lattice translate. (`Breakdown.Periodic.ApproxForced.Internal.periodize_local`)

**Periodization equals a local translate.** A centrally supported field's periodization agrees on a neighborhood of each point with the selected fixed translate. (`Breakdown.Periodic.ApproxForced.Internal.periodize_eventually`)

**Derivatives of a periodized field.** For the stated central support, every iterated derivative of the periodization equals the derivative of the field at the selected translate. (`Breakdown.Periodic.ApproxForced.Internal.iteratedFDeriv_periodize`)

**First derivative of periodization.** For the stated central support, the derivative of the periodization equals the field derivative at the selected translate. (`Breakdown.Periodic.ApproxForced.Internal.fderiv_periodize`)

**Joint smoothness after periodization.** Uniform central support preserves joint time-space smoothness under lattice periodization. (`Breakdown.Periodic.ApproxForced.Internal.contDiffOn_periodize`)

**Shift a lattice frequency.** Adding a unit integer in one lattice coordinate adds the corresponding standard spatial vector to the frequency. (`Breakdown.Periodic.ApproxForced.Internal.freq_add_single`)

**Periodization is periodic.** Adding a standard unit vector to the input leaves lattice periodization unchanged. (`Breakdown.Periodic.ApproxForced.Internal.periodize_add_unit`)

**Lattice periodization is periodic.** Every lattice-periodized field satisfies the periodicity predicate. (`Breakdown.Periodic.ApproxForced.Internal.isPeriodic_periodize`)

**The derivative is periodic.** The derivative of a periodic field is unchanged by a standard unit translation. (`Breakdown.Periodic.ApproxForced.Internal.fderiv_add_unit`)

**All iterated derivatives are periodic.** Every iterated derivative of a periodic field is unchanged by a standard unit translation. (`Breakdown.Periodic.ApproxForced.Internal.iteratedFDeriv_add_unit`)

**The fractional image is periodic.** The fractional image of a periodic field is unchanged by a standard unit translation. (`Breakdown.Periodic.ApproxForced.Internal.fracPower_add_unit`)

**Smoothness of a slice derivative.** Joint smoothness at a time-space point gives joint smoothness there of the spatial slice derivative. (`Breakdown.Periodic.ApproxForced.Internal.contDiffAt_slice_fderiv`)

**Smoothness of higher slice derivatives.** On an open set, joint smoothness gives joint smoothness of each iterated spatial slice derivative at every point. (`Breakdown.Periodic.ApproxForced.Internal.contDiffAt_slice_iteratedFDeriv`)

**Derivatives vanish outside the core.** Every iterated derivative vanishes strictly outside the specified central support ball. (`Breakdown.Periodic.ApproxForced.Internal.iteratedFDeriv_eq_zero_of_far`)

**Uniform far-remainder estimate.** For increments of norm at least one, uniform field and local derivative bounds give the displayed quadratic bound on the remainder. (`Breakdown.Periodic.ApproxForced.Internal.remainder_far`)

**Read the joint map time derivative.** On an open smoothness region, the time derivative equals the joint derivative applied to the unit time direction. (`Breakdown.Periodic.ApproxForced.Internal.time_deriv_eq`)

**Continuity of higher slice derivatives.** Joint smoothness on an open set makes every iterated spatial slice derivative jointly continuous there. (`Breakdown.Periodic.ApproxForced.Internal.continuousOn_slice_iteratedFDeriv`)

**Continuity of the slice derivative.** Joint smoothness on an open set makes the first spatial slice derivative jointly continuous there. (`Breakdown.Periodic.ApproxForced.Internal.continuousOn_slice_fderiv`)

**Joint continuity of the fractional image.** For the stated exponent range, joint smoothness and uniform spatial derivative bounds imply continuity of the fractional image on the chosen subset. (`Breakdown.Periodic.ApproxForced.Internal.continuousOn_fracPower`)

**Bound periodized derivatives.** A smooth centrally supported field has uniformly bounded periodized spatial derivatives on every closed time interval before the terminal time. (`Breakdown.Periodic.ApproxForced.Internal.periodize_bounds`)

**Continuity of the periodized residual.** Under the stated exponent, smoothness and support conditions, the momentum residual of periodized velocity and pressure is jointly continuous on each earlier closed time slab. (`Breakdown.Periodic.ApproxForced.Internal.residual_continuousOn`)

**Periodic derivative of a periodization.** The derivative of a lattice-periodized field is unchanged by a standard unit translation. (`Breakdown.Periodic.ApproxForced.Internal.fderiv_periodize_add_unit`)

**Periodize the fractional image.** The fractional image of a lattice-periodized field is unchanged by a standard unit translation. (`Breakdown.Periodic.ApproxForced.Internal.fracPower_periodize_add_unit`)

**A forced periodic approximate solution.** For 1 < α < 5/4, the approximate field, covariance, and remainder integrability hypotheses make the periodized approximate velocity and pressure a forced periodic fractional solution with forcing equal to the approximate residual on every nonempty closed interval before its positive terminal time. (`Breakdown.Periodic.fracApproxForcedSolution_of`)

### Breakdown.Frac.TorusApproxLinks

This file verifies the endpoint matching and state evaluations of the approximate pieces, making them compatible with the torus sequence construction.

**Choose the local periodization shift.** The local shift is the lattice vector obtained by negating rounded coordinate displacements from one half. (`Breakdown.Periodic.FracLinks.Internal.nearShift`)

**Coordinates of the integer frequency.** Each frequency coordinate is the real cast of its lattice coordinate. (`Breakdown.Periodic.FracLinks.Internal.freq_coord`)

**Coordinates of the chosen center.** Each coordinate of the chosen center is one half. (`Breakdown.Periodic.FracLinks.Internal.center_coord`)

**Distance controls coordinate differences.** The absolute difference in any coordinate is bounded by the distance between the vectors. (`Breakdown.Periodic.FracLinks.Internal.coord_le`)

**Periodization near a point.** For a centrally supported field, periodization within the stated neighborhood equals evaluation at the selected fixed lattice translate. (`Breakdown.Periodic.FracLinks.Internal.periodize_near`)

**Identify the selected local translate.** The periodization of a centrally supported field agrees near each point with the selected lattice translate. (`Breakdown.Periodic.FracLinks.Internal.periodize_eventually`)

**Lattice coordinate shift formula.** Adding one in a lattice coordinate adds the corresponding standard vector to its frequency. (`Breakdown.Periodic.FracLinks.Internal.freq_add_single`)

**The periodized field is periodic.** Lattice periodization satisfies periodicity for every input field. (`Breakdown.Periodic.FracLinks.Internal.isPeriodic_periodize`)

**Periodization preserves zero divergence.** A centrally supported divergence-free field remains divergence-free after lattice periodization. (`Breakdown.Periodic.FracLinks.Internal.divergence_periodize`)

**Smoothness of the periodized family.** A jointly smooth family with uniform central support remains jointly smooth after periodization. (`Breakdown.Periodic.FracLinks.Internal.contDiffOn_periodize`)

**Support of the approximate velocity.** The approximate-field interface places every nonzero approximate velocity value within one eighth of the cell center. (`Breakdown.Periodic.FracLinks.Internal.field_support`)

**Smoothness after a smooth time change.** The periodized approximate velocity is jointly smooth after any smooth time change staying below the terminal time. (`Breakdown.Periodic.FracLinks.Internal.contDiff_periodized`)

**Continuity of the periodized state.** Under the approximate-field and Fourier-series interfaces, the periodized approximate velocity is continuous in V after the stated smooth time change. (`Breakdown.Periodic.FracLinks.Internal.continuousOn_toV_periodized`)

**Start time of the next step.** The next step starts at the current start plus the current scale times the local interval length. (`Breakdown.Periodic.FracLinks.Internal.stepStart_succ`)

**Continuity of each approximate piece.** The approximation and Fourier-series interfaces make the explicitly scaled periodized field continuous on each local piece interval. (`Breakdown.Periodic.FracLinks.Internal.continuous_piece`)

**Evaluate the approximate piece.** Under the stated profile and approximation assumptions, the approximate piece equals its displayed scaled periodized field at every local time. (`Breakdown.Periodic.FracLinks.Internal.piece_apply`)

**Supply approximate-piece matching.** For α > 1, the approximate field and Fourier series hypotheses identify each approximate piece with the step scale to the dilation exponent times the periodized velocity at the corresponding physical time and prove that successive endpoints match by λ to that exponent, for 0 < T ≤ 1 and 0 < λ < 1. (`Breakdown.Periodic.fracApproxLinks`)

### Breakdown.Frac.TorusApproxResidual

This file converts the physical residual estimate into the small weighted piece defect needed for the torus perturbation argument.

**Bound the forced memory integral.** A short interval, a pointwise force bound and an integrable singular heat estimate give the displayed power bound on the forcing memory integral. (`Breakdown.Periodic.FracApproxResidual.Internal.force_bound`)

**Identify the rescaled step defect.** A rescaled piece of a forced mild solution differs from its unforced step equation by precisely the rescaled forcing integral. (`Breakdown.Periodic.FracApproxResidual.Internal.step_identity`)

**Geometric bound for a scale power.** If the recurrence weight exceeds the corresponding scale power, the n-th step scale to that power is bounded by the weight to n times the initial scale power. (`Breakdown.Periodic.FracApproxResidual.Internal.scale_le`)

**Combine the residual time exponents.** Under the stated positivity and local-time bounds, the compound residual scale expression is bounded by the displayed positive power of the step scale. (`Breakdown.Periodic.FracApproxResidual.Internal.rate_le`)

**Prove smallness of approximate residuals.** For 1 < α < 5/4, the approximate field, residual bound, endpoint matching, forced solution, forced mild representation, and force smoothing hypotheses bound the nth approximate piece's mild equation defect by Kθⁿ times T raised to 1/(4α), for a rotating profile, 0 < λ < 1, θ > λ raised to 1/(4α), and 0 < T ≤ 1. (`Breakdown.Periodic.fracApproxResidualSmall`)

### Breakdown.Frac.TorusApproxSizes

This file proves upper and positive lower size bounds for approximate torus pieces, ensuring the eventual glued trajectory keeps the profile's nontrivial size.

**Select the nearest lattice index.** The selected lattice index negates the rounded displacement of each coordinate from one half. (`Breakdown.Periodic.TorusApproxSizes.Internal.nearIdx`)

**Read a lattice frequency coordinate.** A lattice frequency coordinate equals the real cast of its integer coordinate. (`Breakdown.Periodic.TorusApproxSizes.Internal.freq_coord`)

**The center coordinate is one half.** Each coordinate of the cell center is one half. (`Breakdown.Periodic.TorusApproxSizes.Internal.center_coord`)

**Coordinate error below distance.** The absolute difference of any coordinate is bounded by vector distance. (`Breakdown.Periodic.TorusApproxSizes.Internal.coord_le`)

**Wrapping by the nearest lattice index.** The wrapping map equals the original point plus the selected lattice frequency. (`Breakdown.Periodic.TorusApproxSizes.Internal.wrap_eq`)

**Evaluate periodization at the wrap.** For a field supported in the central one-eighth ball, periodization equals evaluation at the wrapped point. (`Breakdown.Periodic.TorusApproxSizes.Internal.periodize_wrap`)

**Smoothness of the localized velocity.** The approximate-field interface makes every localized velocity slice smooth before the terminal time. (`Breakdown.Periodic.TorusApproxSizes.Internal.field_contDiff`)

**Support of the localized velocity.** The approximate-field interface places every nonzero localized velocity value within one eighth of the center. (`Breakdown.Periodic.TorusApproxSizes.Internal.field_support`)

**Derivative of a centered scaling.** The derivative of the amplitude-scaled and centered spatial rescaling equals the original derivative multiplied by both scales. (`Breakdown.Periodic.TorusApproxSizes.Internal.fderiv_rescale_apply`)

**Scaling preserves zero divergence.** A differentiable divergence-free field remains divergence-free after centered scaling and amplitude multiplication. (`Breakdown.Periodic.TorusApproxSizes.Internal.rescale_div`)

**Square root of the fractional scale.** For positive remaining time, the square root of its reciprocal-α power equals its reciprocal-twice-α power. (`Breakdown.Periodic.TorusApproxSizes.Internal.sqrt_scale`)

**Cancel the normalization factors.** For positive scale and α, the displayed three normalization factors multiply to one. (`Breakdown.Periodic.TorusApproxSizes.Internal.scalar_one`)

**Periodization as transplantation.** Under the stated profile and positivity assumptions, the periodized approximate field equals the transplanted pulled-back cutoff field times the specified amplitude. (`Breakdown.Periodic.TorusApproxSizes.Internal.periodic_eq`)

**Simplify the piece normalization.** For positive scales and α, the displayed normalization ratio equals the ratio of the scales raised to the dilation exponent. (`Breakdown.Periodic.TorusApproxSizes.Internal.coef_eq`)

**Gradient columns below the operator norm.** The sum of the three coordinate derivative norm squares is at most three times the full derivative operator norm square. (`Breakdown.Periodic.TorusApproxSizes.Internal.grad_sum_le`)

**Uniform energy of rotating gradients.** For α greater than one, every rotating slice of the given profile has gradient energy bounded by one common constant. (`Breakdown.Periodic.TorusApproxSizes.Internal.slice_grad_bound`)

**Square a nonnegative real power.** For a nonnegative base, squaring a real power doubles its exponent. (`Breakdown.Periodic.TorusApproxSizes.Internal.sq_pow_rpow`)

**Bound the localized mass uniformly.** For the stated exponent range, the approximation and decay interfaces uniformly bound the localized velocity's L² integral before each admissible terminal time. (`Breakdown.Periodic.TorusApproxSizes.Internal.sq_mass_bound`)

**The mass normalization is contractive.** For α greater than one and scale between zero and one, the displayed mass normalization factor is at most one. (`Breakdown.Periodic.TorusApproxSizes.Internal.scalar_le`)

**Mass of the pulled-back cutoff.** For positive remaining time at most one, the similarity-scale-weighted mass of the pulled-back cutoff is bounded by the original approximate field's mass. (`Breakdown.Periodic.TorusApproxSizes.Internal.cut_mass`)

**The cutoff matches the inner profile.** Under the approximate-field interface, the pulled-back cutoff equals the rotating profile wherever the scaled point lies in the core. (`Breakdown.Periodic.TorusApproxSizes.Internal.core_eq`)

**Gradient convergence of the cutoff.** For α greater than one, the approximation and shell-gradient interfaces make the pulled-back cutoff converge to the rotating slice in gradient energy as remaining time tends to zero. (`Breakdown.Periodic.TorusApproxSizes.Internal.cut_close`)

**Prove upper and lower approximate sizes.** For the stated exponent range, transplantation, field, matching and decay interfaces supply uniform upper and positive lower bounds for approximate pieces. (`Breakdown.Periodic.fracApproxSizes`)

### Breakdown.Frac.TorusApproxSizesAux

This file defines a rescaled cutoff and supplies the auxiliary shell gradient control used in the approximate piece size estimates.

**The approximation in profile coordinates.** The pulled-back cutoff recenters the approximate field and applies the amplitude and spatial scales determined by remaining time. (`Breakdown.Periodic.fracCut`)

**Uniform gradient bound in the shell.** The shell-gradient proposition requests a uniform bound on the approximate velocity's derivative outside the inner core for every admissible time. (`Breakdown.Periodic.FracShellGradientBound`)

**Prove the shell-gradient bound.** For 1 < α < 5/4, the approximate field and self similar decay hypotheses give each rotating profile a uniform bound on the localized approximate field's first derivative outside one quarter of the central radius, for 0 < T ≤ 1 and 0 ≤ t < T. (`Breakdown.Periodic.fracShellGradientBound`)

### Breakdown.Frac.TorusApproximants

This file constructs supported finite approximants for the rotating profile pieces in the periodic inverse comparison route.

**The dilation exponent is positive.** For α greater than one, the X-space dilation exponent is positive. (`Breakdown.Periodic.FracInternal.TorusApproximants.dilExponent_pos`)

**Profile pieces after repeated rotation.** The profile-piece interface makes pieces separated by whole recurrence periods equal to iterates of the rotation applied to the original piece. (`Breakdown.Periodic.FracInternal.TorusApproximants.profile_rot`)

**Build uniformly supported approximants.** For α > 1, the scaled profile piece hypothesis gives every rotating profile that forms a commuting recurrent orbit, every positive subdivision count, and every ε > 0 a supported finite approximant whose whole space pieces are within ε of all orbit pieces uniformly in the step index. (`Breakdown.Periodic.fracApproximantExists`)

### Breakdown.Frac.TorusAssembly

This file combines approximation, inverse, perturbation, and gluing interfaces to construct the fractional torus blowup trajectory.

**Bound the torus seed operator.** Under the sequence-operator specification and the stated scaling conditions, the torus seed operator norm is bounded by the initial-data map norm. (`Breakdown.Periodic.FracTorusAssembly.Internal.norm_fracTorusSeed_le`)

**Read the right inverse coordinatewise.** A right inverse of the torus correction operator satisfies the displayed stepwise recurrence equation, including the initial seed and later endpoint transport. (`Breakdown.Periodic.FracTorusAssembly.Internal.frac_torus_seq_equation`)

**Choose a small enough positive time.** For a positive exponent and threshold, some positive time bound makes the scale power at most that threshold for every smaller nonnegative time. (`Breakdown.Periodic.FracTorusAssembly.Internal.rpow_small`)

**Divergence under constant multiplication.** For a differentiable field, scalar multiplication multiplies its divergence by the same scalar. (`Breakdown.Periodic.FracTorusAssembly.Internal.divergenceAt_const_smul`)

**Positive fractional dilation exponent.** For α greater than one, the dilation exponent is positive. (`Breakdown.Periodic.FracTorusAssembly.Internal.dilExponent_pos`)

**Assemble fractional torus blow-up.** For one less than α less than five quarters, the listed analytic, inverse, approximation, perturbation and gluing interfaces turn rotating-profile existence into an unbounded torus mild trajectory. (`Breakdown.Periodic.fracTorusBlowup_of_parts`)

### Breakdown.Frac.TorusBaseInverse

This file transfers the abstract whole space step inverse to the fractional sequence operator used as the base of the torus perturbation argument.

**Positive exponent for the base inverse.** For α greater than one, the dilation exponent is positive. (`Breakdown.Periodic.FracBaseInverseInternal.exponent_pos`)

**A recurrence gives a right inverse.** If the sequence components satisfy the stated recurrence identities, the assembled chain operator composed with its candidate inverse is the identity. (`Breakdown.Periodic.FracBaseInverseInternal.seqChain_comp_eq_id`)

**Construct the base recurrence inverse.** For α > 1, the scaled step data and sequence operator hypotheses give every commuting recurrent orbit and prescribed dense subspace arbitrarily short steps and a bounded right inverse of the whole space recurrence operator, with a finite dimensional initial correction mapped into that subspace and θ between both specified scale powers and one. (`Breakdown.Periodic.fracBaseInverse`)

### Breakdown.Frac.TorusBlowupExports

This file gathers the analytic providers for the fractional torus approximation and inverse comparison route, culminating in its blowup interface.

**Supply the self-similar solution.** For 1 < α < 5/4, every unit viscosity rotating profile generates jointly smooth similarity velocity and pressure before each positive terminal time, with zero velocity divergence and the fractional momentum equation at every earlier time and spatial point. (`Breakdown.Periodic.TorusBlowupAssembly.Internal.fracSelfSimilarSolves_holds`)

**Supply self-similar decay.** For 1 < α < 5/4, every rotating profile has a constant controlling its similarity velocity derivatives through order three by the smoothed distance to the center raised to −(2α − 1 + j), and its time derivative and pressure gradient by that distance raised to −(4α − 1), uniformly for 0 < T ≤ 1 and 0 ≤ t < T. (`Breakdown.Periodic.TorusBlowupAssembly.Internal.fracSelfSimilarDecay_holds`)

**Supply the localized field properties.** For 1 < α < 5/4, the localized velocity and pressure of every rotating profile are jointly smooth before each positive terminal time, the velocity is divergence free, both fields vanish beyond half the central radius, and the velocity agrees with the similarity field inside one quarter of that radius. (`Breakdown.Periodic.TorusBlowupAssembly.Internal.fracApproxFieldProperties_holds`)

**Supply the approximate-piece links.** For 1 < α < 5/4, every rotating profile's approximate pieces are the stated rescaled periodized velocity slices and their successive endpoints match by λ raised to the dilation exponent whenever 0 < T ≤ 1 and 0 < λ < 1. (`Breakdown.Periodic.TorusBlowupAssembly.Internal.fracApproxLinks_holds`)

**Supply the pointwise fractional bound.** For 1 < α < 5/4, a C³ field with the stated integrable fractional remainder and tail, radius 0 < r ≤ 1, third derivative bound B on the local ball, value and first two derivative bounds A at its center, and tail integral bound L has fractional power norm at most C multiplied by the sum B r^(3 − 2α) + A r^(−2α) + L. (`Breakdown.Periodic.TorusBlowupAssembly.Internal.fracPointwiseBound_holds`)

**Supply third derivative bounds.** For 1 < α < 5/4, each rotating profile's localized approximate field has a uniform third spatial derivative bound outside one quarter of the central radius, over 0 < T ≤ 1 and 0 ≤ t < T. (`Breakdown.Periodic.TorusBlowupAssembly.Internal.fracApproxFieldThirdBound_holds`)

**Supply the space residual bound.** For 1 < α < 5/4, each rotating profile's whole space approximate residual is uniformly bounded in space by K times the remaining time raised to −(2 − 3/(2α)), for 0 < T ≤ 1 and 0 ≤ t < T. (`Breakdown.Periodic.TorusBlowupAssembly.Internal.fracSpaceResidualBound_holds`)

**Supply the periodic residual bound.** For 1 < α < 5/4, each rotating profile's periodized approximate residual is uniformly bounded in space by K times the remaining time raised to −(2 − 3/(2α)), for 0 < T ≤ 1 and 0 ≤ t < T. (`Breakdown.Periodic.TorusBlowupAssembly.Internal.fracApproxResidualBound_holds`)

**Supply the torus forcing laws.** For α greater than one, the torus forcing coefficient, heat-shift and continuity laws hold. (`Breakdown.Periodic.TorusBlowupAssembly.Internal.fracTorusForceAlgebra_holds`)

**Supply the torus kernel laws.** For α greater than one, the torus kernel coefficient, symmetry, continuity and heat-shift laws hold. (`Breakdown.Periodic.TorusBlowupAssembly.Internal.fracTorusKernelAlgebra_holds`)

**Supply the source operator.** For α greater than one, the continuous source-operator realization exists at every scale and time. (`Breakdown.Periodic.TorusBlowupAssembly.Internal.fracSourceOpExists_holds`)

**Supply source-response continuity.** For α > 1, each positive scale μ and fixed real L² source produce a rescaled torus source trajectory continuous at every positive source time. (`Breakdown.Periodic.TorusBlowupAssembly.Internal.fracSourceOpContinuous_holds`)

**Supply the torus shell-response bound.** For α > 1, the torus shell response is bounded by C times τ raised to −3/(4α) times the embedded test field norm times the shell datum norm, whenever 0 < μ ≤ 1, its similarity scale fits the shell, and 0 < μτ ≤ 1. (`Breakdown.Periodic.TorusBlowupAssembly.Internal.fracTorusLambdaBound_holds`)

**Supply the whole-space shell bound.** For α > 1, the whole space shell response at every positive time τ is bounded by C times τ raised to −3/(4α) times the embedded test field norm times the shell datum norm. (`Breakdown.Periodic.TorusBlowupAssembly.Internal.fracR3LambdaBound_holds`)

**Supply fractional forcing smoothing.** For α > 1 and 0 < τ ≤ 1, the torus forcing of a continuous periodic field is bounded by C times τ raised to −1/(2α) times its L² norm over one periodic cell. (`Breakdown.Periodic.TorusBlowupAssembly.Internal.fracForceSmoothing_holds`)

**Supply the forced-to-mild implication.** For one less than α less than five quarters, smooth forced periodic solutions satisfy the forced mild equation. (`Breakdown.Periodic.TorusBlowupAssembly.Internal.fracForcedPeriodicIsMild_holds`)

**Supply small weighted residuals.** For 1 < α < 5/4, a rotating profile, 0 < λ < 1, and θ > λ raised to 1/(4α), the nth approximate piece's defect from its free plus quadratic mild equation is at most Kθⁿ times T raised to 1/(4α), uniformly over 0 < T ≤ 1. (`Breakdown.Periodic.TorusBlowupAssembly.Internal.fracApproxResidualSmall_holds`)

**Supply bounded whole-space restriction.** The whole space shell restriction operators have a single nonnegative operator norm bound uniform in the shell radius. (`Breakdown.Periodic.TorusBlowupAssembly.Internal.restrictR3Bound_holds`)

**Supply chain-component norm bounds.** For α > 1, one constant bounds the whole space and torus source maps by the approximant size and bounds both restriction maps under the stated positive step and shell fitting conditions, while each normalized shift norm is at most its step scale raised to the dilation exponent divided by θ > 0. (`Breakdown.Periodic.TorusBlowupAssembly.Internal.fracOperatorNormBounds_holds`)

**Supply the whole-space chain identity.** For α > 1, a fractional framework with the prescribed bilinear kernel and a step length in (0,1] has its whole space recurrence operator equal exactly to the chain built from its normalized shift, initial seed, shell source response, and shell restriction. (`Breakdown.Periodic.TorusBlowupAssembly.Internal.fracR3ChainEq_holds`)

**Supply the torus chain identity.** For α > 1, 0 < T ≤ 1, 0 < λ < 1, and a positive radius whose initial similarity shell fits inside one eighth, the torus recurrence operator built from transplanted approximant pieces equals the chain of its normalized shift, seed, source response, and restriction. (`Breakdown.Periodic.TorusBlowupAssembly.Internal.fracTorusChainEq_holds`)

**Supply the base right inverse.** For α > 1, every commuting recurrent orbit and prescribed dense subspace admit arbitrarily short positive steps, a weight θ between the stated scale powers and one, and a bounded right inverse of the whole space recurrence operator using a finite dimensional initial correction mapped into that dense subspace. (`Breakdown.Periodic.TorusBlowupAssembly.Internal.fracBaseInverse_holds`)

**Supply the geometric entry-tail bounds.** For α > 1, a matching fractional framework, positive period and subdivision count with step length at most one half, and θ between the dilation weight and one, both whole space and admissibly localized torus entries j steps after their source are bounded by K times (dilation weight divided by θ)ʲ times the shell sequence norm. (`Breakdown.Periodic.TorusBlowupAssembly.Internal.fracTailBound_holds`)

**Supply the whole-space entry formula.** For α > 1 and the stated matching framework, positive period, subdivision count, θ, and radius with step length at most one half, each whole space entry j steps after its source equals θ⁻ʲ times the weighted shell advection integrals after dilation by λʲ and solenoidal heat for time 1 − σ − λʲ(1 − s), integrated to s when j = 0 and to the step endpoint otherwise, where λ = exp(−P/k). (`Breakdown.Periodic.TorusBlowupAssembly.Internal.fracR3EntryFormula_holds`)

**Supply the torus entry formula.** For α > 1, 0 < T ≤ 1, 1/2 ≤ λ < 1, positive θ and radius, and a fitting similarity shell, each torus entry j steps after its source equals θ⁻ʲ times the stated normalized and restricted source integrals at time 1 − σ − λʲ(1 − s), integrated to s when j = 0 and to 1 − λ otherwise. (`Breakdown.Periodic.TorusBlowupAssembly.Internal.fracTorusEntryFormula_holds`)

**Supply the comparison frame change.** For α > 1, 0 < c ≤ 1, and an admissible rescaled shell, the restricted torus versus whole space difference after similarity dilation by c is at most c raised to the dilation exponent times the original difference measured on the correspondingly smaller shell. (`Breakdown.Periodic.TorusBlowupAssembly.Internal.fracFrameChange_holds`)

**Supply projected heat comparison.** For α > 1 and fixed positive source radius, observation radius, time cutoff ε, and tolerance δ, sufficiently small positive scale makes normalized torus forcing and whole space solenoidal heat differ on the observation shell by at most δ times the source L³⁄² norm, uniformly for sources supported in that radius and τ in [ε,ε inverse]. (`Breakdown.Periodic.TorusBlowupAssembly.Internal.fracProjectedHeatComparison_holds`)

**Supply free heat comparison.** For α > 1 and a test field, the restricted normalized torus heat of its transplant converges uniformly to restricted whole space heat as the positive scale tends to zero, over every time interval [0,ε inverse] and fixed positive observation radius. (`Breakdown.Periodic.TorusBlowupAssembly.Internal.fracFreeHeatComparison_holds`)

**Supply embedding-dilation compatibility.** For α greater than one, embedding decay fields commutes with fractional dilation. (`Breakdown.Periodic.TorusBlowupAssembly.Internal.fracEmbedDilate_holds`)

**Supply the whole-space seed formula.** For α > 1, a framework with the fractional heat and dilation, positive period and subdivision count, and θ between the step dilation weight and one, the nth inverse shift seed slot is θ⁻ⁿ times heat for s + λ⁻ⁿ − 1 applied to the seed dilated by λⁿ, where λ = exp(−P/k). (`Breakdown.Periodic.TorusBlowupAssembly.Internal.fracR3SeedEntry_holds`)

**Supply the torus seed formula.** For α > 1, 0 < T ≤ 1, 0 < λ < 1, and θ between λ raised to the dilation exponent and one, the nth torus inverse shift seed slot is the seed heated for T(λⁿs + 1 − λⁿ) and multiplied by (λ raised to the dilation exponent divided by θ)ⁿ. (`Breakdown.Periodic.TorusBlowupAssembly.Internal.fracTorusSeedEntry_holds`)

**Supply the self-similar weak equation.** For 1 < α < 5/4, every unit viscosity rotating profile gives a self similar field satisfying the fractional weak equation on [0,T] for each 0 < T < 1 and every initial similarity phase. (`Breakdown.Periodic.TorusBlowupAssembly.Internal.selfSimilarWeak_holds`)

**Supply finite-window entry comparison.** For α > 1, a matching framework, positive period and subdivision count with step length at most one half, positive radius, and θ between the step dilation weight and one, the torus and whole space entries at any fixed finite range of lags differ by at most η times the shell sequence norm once 0 < T ≤ 1 is sufficiently small. (`Breakdown.Periodic.TorusBlowupAssembly.Internal.fracWindowBound_holds`)

**Supply the seed-operator comparison.** For α > 1, a matching framework and finite dimensional test lift with positive period, subdivision count, and radius, step length at most one half, and θ between the step dilation weight and one, the restricted inverse shift seed maps on the torus and whole space differ in operator norm by at most any prescribed δ > 0 when the positive terminal time is sufficiently small. (`Breakdown.Periodic.TorusBlowupAssembly.Internal.fracSeedComparison_holds`)

**Supply stability under profile changes.** For α > 1, changing all background pieces by at most M changes the whole space or torus recurrence operator by at most eight times its kernel bound times the fourth root of the step length times M, under the respective positive step and scale assumptions. (`Breakdown.Periodic.TorusBlowupAssembly.Internal.fracOpDiffBounds_holds`)

**Supply cutoff closeness.** For 1 < α < 5/4 and every rotating profile, the rescaled cutoff converges to the rotating slice in gradient energy as the remaining time tends to zero, while its squared L² mass is bounded by K times that remaining time raised to −(5 − 4α)/(2α), uniformly for 0 < T ≤ 1 and 0 ≤ t < T. (`Breakdown.Periodic.TorusBlowupAssembly.Internal.fracCutoffClose_holds`)

**Supply torus approximate closeness.** For 1 < α < 5/4, a matching dilation framework, rotating profile, positive period, subdivision count, and support radius, any approximant within ε of every whole space profile piece is within ε + δ of every corresponding torus approximate piece for sufficiently small positive terminal time, for each δ > 0. (`Breakdown.Periodic.TorusBlowupAssembly.Internal.fracApproxClose_holds`)

**Supply approximate upper and lower sizes.** For 1 < α < 5/4, a rotating profile whose embedded slices have a uniform positive norm lower bound c and any 0 < λ < 1 yield approximate torus pieces with a common upper norm bound and pointwise norm at least c/2, uniformly in all pieces when the terminal time is sufficiently small and positive. (`Breakdown.Periodic.TorusBlowupAssembly.Internal.fracApproxSizes_holds`)

**Supply initial-datum closeness.** For 1 < α < 5/4, a rotating profile, 0 < λ < 1, and a test datum supported in a fixed positive radius, the normalized transplant differs from the first approximate piece's initial value by at most the original embedded datum's distance from the profile plus any δ > 0 when the positive terminal time is small enough. (`Breakdown.Periodic.TorusBlowupAssembly.Internal.fracDatumClose_holds`)

**Supply weak-to-mild conversion.** For 1 < α < 5/4 and a < b, embedding each slice of a weak fractional solution gives an X-valued fractional mild trajectory on [a,b]. (`Breakdown.Periodic.TorusBlowupAssembly.Internal.fracMildOfWeak_holds`)

**Supply the complete inverse comparison.** For α > 1, a matching framework, finite dimensional test lift, supported approximant, and the stated positive step parameters with step length at most one half and dilation weight below θ < 1, both restricted inverse shift source maps and seed maps on the torus approach their whole space counterparts in operator norm as the positive terminal time tends to zero. (`Breakdown.Periodic.TorusBlowupAssembly.Internal.fracComparisonSmall_holds`)

**Supply the rotating profile orbit.** For 1 < α < 5/4, the embedded rotating slices of any unit viscosity profile form a recurrent orbit in every framework with the prescribed fractional heat, kernel, and dilation, for any positive period P′ and symmetry given by axial rotation through −aP′. (`Breakdown.Periodic.TorusBlowupAssembly.Internal.fracProfileOrbit_holds`)

**Supply mild gluing on the torus.** For α greater than one, matching scaled torus pieces glue to a mild solution. (`Breakdown.Periodic.TorusBlowupAssembly.Internal.fracGlueMild_holds`)

**A profile gives torus mild blow-up.** For one less than α less than five quarters, a rotating fractional profile yields the stated unbounded torus mild trajectory. (`Breakdown.Periodic.fracTorusBlowup_holds`)

### Breakdown.Frac.TorusChainR3

This file factors the whole space sequence operator through shell responses and shift chains, preparing comparison with the torus operator.

**Extend a piece by clamped evaluation.** For a nonnegative interval length, extending a piece evaluates it at the interval projection of the requested time. (`Breakdown.Periodic.FracChainR3.Internal.extendPiece_eq`)

**Ignore integral endpoint changes.** On a nonnegative interval, functions equal at all interior points have equal interval integrals. (`Breakdown.Periodic.FracChainR3.Internal.integral_congr_Ioo`)

**Compose uniformly bounded sequence maps.** Under the sequence specification and uniform bounds, composition of pointwise sequence operators equals the sequence operator of the pointwise compositions. (`Breakdown.Periodic.FracChainR3.Internal.seqOp_comp`)

**Continuity of an extended piece.** The extension of a continuous piece on a nonnegative interval is continuous. (`Breakdown.Periodic.FracChainR3.Internal.continuous_extendPiece`)

**The extended piece obeys its sup norm.** Every value of an extended piece is bounded in norm by the piece norm. (`Breakdown.Periodic.FracChainR3.Internal.norm_extendPiece_le`)

**Compare the two short-time exponents.** For α greater than one and time between zero and one, the fractional kernel time power is bounded by the ordinary three-quarter singularity. (`Breakdown.Periodic.FracChainR3.Internal.rpow_exponent_le`)

**Bound the shell response operator.** The pointwise shell-response bound implies the displayed operator norm bound with the three-quarter time singularity on short intervals. (`Breakdown.Periodic.FracChainR3.Internal.lambda_bound`)

**Continuity of whole-space shell response.** The projected-heat continuity interface makes every whole-space shell response continuous at positive times. (`Breakdown.Periodic.FracChainR3.Internal.lambda_cont`)

**Factor the whole-space piece operator.** Under the stated factorization, continuity and piece-map interfaces, the weighted shell convolution composed with restriction equals twice the bilinear profile-piece operator. (`Breakdown.Periodic.FracChainR3.Internal.piece_eq`)

**Factor the whole-space sequence operator.** Under the stated interfaces, whole-space Lambda composed with restriction equals the sequence of twice the bilinear profile-piece operators. (`Breakdown.Periodic.FracChainR3.Internal.lambda_restrict`)

**Prove the whole-space chain identity.** For α > 1, the whole space factorization, response bound, sequence, piece composition, piece convolution, piece operator, and solenoidal heat continuity hypotheses identify the recurrence operator with the chain of its shift, seed, shell response, and restriction whenever its framework has the prescribed kernel and its step length lies in (0,1]. (`Breakdown.Periodic.fracR3ChainEq`)

### Breakdown.Frac.TorusChainTorus

This file factors the torus sequence operator through its localized shell responses and shifts, matching the structure of the whole space chain.

**The similarity scale is positive.** Every positive scale has a positive fractional similarity scale. (`Breakdown.Periodic.FracTorusChainTorus.Internal.simScale_pos`)

**Small scales remain at most one.** For α greater than one, a positive scale at most one has similarity scale at most one. (`Breakdown.Periodic.FracTorusChainTorus.Internal.simScale_le_one`)

**Monotonicity of the similarity scale.** For α greater than one, increasing a positive scale increases its similarity scale. (`Breakdown.Periodic.FracTorusChainTorus.Internal.simScale_mono`)

**Every step scale fits the shell.** The stated initial support and scale bounds make every geometric step's similarity scale admissible for the shell restriction. (`Breakdown.Periodic.FracTorusChainTorus.Internal.isShellScale_fracStep`)

**Continuity of torus shell response.** For positive scale, source-operator continuity gives positive-time continuity of the torus shell response. (`Breakdown.Periodic.FracTorusChainTorus.Internal.fracLambdaTorus_continuousOn`)

**Bound the fractional time singularity.** For α greater than one and positive time at most one, the fractional three-over-four-α singularity is bounded by the three-quarter singularity. (`Breakdown.Periodic.FracTorusChainTorus.Internal.rpow_exponent_compare`)

**Torus Lambda factors the piece operator.** Under the stated interfaces and uniform approximant bounds, torus Lambda composed with restriction acts at each step as twice its bilinear profile-piece operator. (`Breakdown.Periodic.FracTorusChainTorus.Internal.fracChain_apply`)

**Prove the torus chain identity.** For α > 1, the torus factorization, response bound, sequence, piece composition, convolution, piece operator, and source continuity hypotheses identify the torus recurrence operator with the chain of its shift, seed, source response, and restriction, for 0 < T ≤ 1, 0 < λ < 1, and a positive shell fitting inside one eighth at the initial scale. (`Breakdown.Periodic.fracTorusChainEq`)

### Breakdown.Frac.TorusCoef

This file proves the periodic fractional Fourier coefficient identity from plane waves and symmetry, which is used to derive the periodic mild equation.

**Complexification keeps the norm.** Complexifying a real spatial vector preserves its norm. (`_private.Breakdown.Frac.TorusCoef.0.Breakdown.Periodic.norm_complexify_eq`)

**Integrable Fourier-coefficient integrand.** A cell-integrable field remains integrable on the cell after complexification and multiplication by a Fourier character. (`_private.Breakdown.Frac.TorusCoef.0.Breakdown.Periodic.integrableOn_coef_of`)

**Read one Fourier coefficient coordinate.** For a cell-integrable field, each coordinate of its Fourier coefficient is the cell integral of the corresponding character-weighted coordinate. (`_private.Breakdown.Frac.TorusCoef.0.Breakdown.Periodic.coef_apply_of`)

**Pair with a coordinate wave.** Pairing a vector with a scalar times a coordinate unit vector gives that scalar times the corresponding coordinate. (`_private.Breakdown.Frac.TorusCoef.0.Breakdown.Periodic.inner_smul_single`)

**Write the character using cosine waves.** The Fourier character is the stated complex combination of a cosine wave and its quarter-period phase shift. (`_private.Breakdown.Frac.TorusCoef.0.Breakdown.Periodic.character_eq`)

**Integrability of a cosine coefficient.** A cosine factor times a coordinate of a cell-integrable field is integrable on the cell. (`_private.Breakdown.Frac.TorusCoef.0.Breakdown.Periodic.integrableOn_cos_mul`)

**Express a Fourier mode by cosine tests.** Each Fourier coefficient coordinate splits into the stated two real cosine integrals. (`_private.Breakdown.Frac.TorusCoef.0.Breakdown.Periodic.coef_split`)

**Smoothness of a cosine vector wave.** A cosine of a linear phase times a constant vector is smooth. (`_private.Breakdown.Frac.TorusCoef.0.Breakdown.Periodic.contDiff_wave`)

**Periodicity of a lattice cosine wave.** A cosine wave with lattice frequency times two pi is periodic. (`_private.Breakdown.Frac.TorusCoef.0.Breakdown.Periodic.isPeriodic_wave`)

**Fractional action in a cosine pairing.** The plane-wave and periodic-symmetry interfaces transfer the fractional multiplier to a cosine test, producing the stated lattice eigenvalue in its integral pairing. (`_private.Breakdown.Frac.TorusCoef.0.Breakdown.Periodic.cos_integral_scale`)

**Prove the periodic coefficient formula.** The plane wave eigenvalue and periodic symmetry hypotheses imply that each Fourier coefficient of the fractional power of a smooth periodic field equals its original coefficient multiplied by (2π times the lattice frequency norm) raised to 2α. (`Breakdown.Periodic.coefFractional_of`)

### Breakdown.Frac.TorusCompareChain

This file computes closed formulas for repeated whole space and torus step operators, enabling direct comparison of individual sequence entries.

**A chain of length zero is the identity.** The shift chain from an index to itself is the identity operator. (`Breakdown.Periodic.FracCompareChain.Internal.shiftChain_self`)

**Append one step to a shift chain.** For an ordered pair of indices, extending the destination by one composes the old shift chain with the next step operator. (`Breakdown.Periodic.FracCompareChain.Internal.shiftChain_succ`)

**Read the endpoint of a piece.** For nonnegative interval length, the endpoint map evaluates the piece at its final time. (`Breakdown.Periodic.FracCompareChain.Internal.pieceEnd_apply`)

**Evaluate a factored shift chain.** When each step factors through the previous endpoint and the stated evolution law, the iterated chain equals the appropriate scalar power times the accumulated evolution of that endpoint. (`Breakdown.Periodic.FracCompareChain.Internal.chain_apply`)

**Read a whole space step.** For a positive step length and the piece operator interface, a whole space step heats the dilated endpoint and multiplies it by the inverse of θ. (`Breakdown.Periodic.FracCompareChain.Internal.r3Step_apply`)

**Expand a whole space step chain.** For positive period and positive step count, the piece operator interface expands a chain of j + 1 whole space steps into one dilation, one heat evolution, and the factor θ to power −(j + 1). (`Breakdown.Periodic.FracCompareChain.Internal.r3Chain`)

**Read a torus step.** For α > 1, positive T and λ at most one, and λ < 1, the piece operator interface expresses a torus step as heat evolution of the endpoint with factor λ raised to the dilation exponent divided by θ. (`Breakdown.Periodic.FracCompareChain.Internal.torusStep_apply`)

**Expand a torus step chain.** For α > 1, positive T at most one, and 0 < λ < 1, the piece operator interface expands a chain of j + 1 torus steps into one heat evolution with the corresponding geometric scalar factor. (`Breakdown.Periodic.FracCompareChain.Internal.torusChain`)

**Supply the whole space chain formula.** For α > 1, the piece operator hypothesis makes j + 1 whole space steps with positive period P and subdivision count k equal θ to power −(j + 1) times dilation by λ^(j + 1) of the endpoint heated for λ^(j + 1)s + λ − λ^(j + 1), where λ = exp(−P/k) and the framework has the specified heat and dilation. (`Breakdown.Periodic.fracR3ChainFormula`)

**Supply the torus chain formula.** For α > 1, the piece operator hypothesis makes j + 1 torus steps starting at index m equal (λ raised to the dilation exponent divided by θ)^(j + 1) times endpoint heat evolution for Tλᵐ(λ^(j + 1)s + λ − λ^(j + 1)), when 0 < T ≤ 1 and 0 < λ < 1. (`Breakdown.Periodic.fracTorusChainFormula`)

### Breakdown.Frac.TorusCompareEntryR3

This file expands whole space source entries as explicit heat and dilation integrals for the finite window comparison.

**Read the whole space source action.** The whole space source operator applies the negative fractional solenoidal heat operator to the shell advection field. (`Breakdown.Periodic.FracCompareEntryR3.Internal.lambda_apply`)

**Compare short time powers.** For α > 1 and 0 < τ ≤ 1, τ raised to −3/(4α) is at most τ raised to −3/4. (`Breakdown.Periodic.FracCompareEntryR3.Internal.rpow_exponent_le`)

**Bound the whole space source operator.** For α > 1, the source bound interface gives a nonnegative constant bounding the operator norm by the test field norm times τ raised to −3/4 for 0 < τ ≤ 1. (`Breakdown.Periodic.FracCompareEntryR3.Internal.lambda_opNorm_le`)

**Continuity of the source action.** The solenoidal heat continuity interface makes each fixed whole space source action continuous at positive times. (`Breakdown.Periodic.FracCompareEntryR3.Internal.lambda_continuousOn`)

**Integrability of the source term.** For α > 1 and 0 ≤ u ≤ 1, the heat continuity and source bound interfaces make the weighted whole space source integrand integrable from zero to u. (`Breakdown.Periodic.FracCompareEntryR3.Internal.integrand_intervalIntegrable`)

**Move a map through source integrals.** For α > 1 and 0 ≤ u ≤ 1, the heat continuity and source bound interfaces allow a continuous linear map into a complete space to pass through the finite sum of weighted source integrals. (`Breakdown.Periodic.FracCompareEntryR3.Internal.map_lambda_sum`)

**Read a nonnegative piece endpoint.** For a nonnegative interval length, the piece endpoint equals evaluation at the right endpoint. (`Breakdown.Periodic.FracCompareEntryR3.Internal.pieceEnd_eq`)

**A chain with no steps is identity.** A shift chain whose start and end indices agree is the identity continuous linear map. (`Breakdown.Periodic.FracCompareEntryR3.Internal.shiftChain_self`)

**Expand a later whole space entry.** Under the chain, heat shift, continuity, and source bound interfaces, positive admissible step parameters turn a prescribed source integral endpoint into the stated dilated heat integral after i + 1 steps. (`Breakdown.Periodic.FracCompareEntryR3.Internal.succ_entry`)

**Supply whole space entry formulas.** For α > 1, the whole space chain and source formulas, heat shift and continuity, and response bound hypotheses express each entry j steps after its source as θ⁻ʲ times the weighted restricted shell advection integral with dilation λʲ and heat time 1 − σ − λʲ(1 − s), with the current time endpoint for j = 0 and the full step endpoint otherwise, under the specified matching framework and positive step restrictions. (`Breakdown.Periodic.fracR3EntryFormula`)

### Breakdown.Frac.TorusCompareEntryTorus

This file expands torus source entries as explicit rescaled forcing integrals for the finite window comparison.

**A chain with no steps is identity.** A shift chain whose start and end indices agree is the identity continuous linear map. (`Breakdown.Periodic.TorusCompareEntryTorus.Internal.shiftChain_self`)

**Read the rescaled torus source.** When the source existence interface holds and μ > 0, the source operator is torus forcing at time μτ applied to the field in the μ similarity coordinates. (`Breakdown.Periodic.TorusCompareEntryTorus.Internal.sourceOp_apply`)

**Heat evolution shifts source time.** Under the torus force algebra and source existence interfaces, positive μ and τ and nonnegative t make heat evolution by μt advance the source time from τ to t + τ. (`Breakdown.Periodic.TorusCompareEntryTorus.Internal.heat_sourceOp`)

**Heat evolution shifts source action.** Under the torus force algebra and source existence interfaces, positive μ and τ and nonnegative t make heat evolution by μt advance a torus source action from τ to t + τ. (`Breakdown.Periodic.TorusCompareEntryTorus.Internal.heat_lambdaTorus`)

**Continuity of a torus source action.** Under the torus force algebra and source existence interfaces and μ > 0, each fixed torus source action is continuous at positive times. (`Breakdown.Periodic.TorusCompareEntryTorus.Internal.lambdaTorus_continuousOn`)

**All step scales fit the shell.** For α > 1, positive T and λ at most one, and positive shell radius b with the initial rescaled radius at most one eighth, every step similarity scale is admissible for the shell. (`Breakdown.Periodic.TorusCompareEntryTorus.Internal.isShellScale_sim`)

**Integrability of torus source terms.** For α > 1, a positive admissible μ at most one, and 0 ≤ u ≤ 1, the force algebra, source existence, and source bounds make each weighted torus source integrand integrable from zero to u. (`Breakdown.Periodic.TorusCompareEntryTorus.Internal.lambda_integrable`)

**Separate geometric scalar factors.** For nonnegative λ, the nth power of λ raised to κ divided by θ equals θ to power −n times λ to power n raised to κ. (`Breakdown.Periodic.TorusCompareEntryTorus.Internal.scalar_split`)

**Rewrite a heated torus source term.** Under force algebra and source existence, positive μ and τ, nonnegative t, and the stated scalar and time identities rewrite a restricted heated torus source action as a rescaled source at time t + τ. (`Breakdown.Periodic.TorusCompareEntryTorus.Internal.entry_pointwise`)

**Read a nonnegative piece endpoint.** For a nonnegative interval length, the piece endpoint equals evaluation at the right endpoint. (`Breakdown.Periodic.TorusCompareEntryTorus.Internal.pieceEnd_eq`)

**Supply torus entry formulas.** For α > 1, the torus chain and source formulas, response bound, force algebra, and source existence hypotheses express each entry j steps after its source as θ⁻ʲ times the weighted normalized source integral at time 1 − σ − λʲ(1 − s), with the current endpoint for j = 0 and full endpoint otherwise, for 0 < T ≤ 1, 1/2 ≤ λ < 1, positive θ and radius, and a fitting shell. (`Breakdown.Periodic.fracTorusEntryFormula`)

### Breakdown.Frac.TorusCompareFinal

This file combines source and seed comparisons into the small operator comparison used to transfer the right inverse to the torus.

**Combine the two comparison bounds.** For α > 1, the source and seed comparison hypotheses imply that both restricted inverse shift maps on the torus approach their whole space counterparts in operator norm as the positive terminal time tends to zero, for a matching framework, finite dimensional test lift, supported approximant, and the stated admissible step and weight parameters. (`Breakdown.Periodic.fracComparisonSmall_of_parts`)

### Breakdown.Frac.TorusCompareFrame

This file tracks gradient and velocity restriction norms under a change of similarity scale, aligning whole space and torus entry comparisons.

**Compute the similarity length.** For c > 0, the square root of its similarity scale is c raised to 1/(2α). (`Breakdown.Periodic.TorusCompareFrame.Internal.sqrtSim`)

**Similarity scales are positive.** A positive scale parameter has a positive similarity scale. (`Breakdown.Periodic.TorusCompareFrame.Internal.simPos`)

**Small scales stay small.** For α > 0 and 0 < c ≤ 1, the similarity scale is at most one. (`Breakdown.Periodic.TorusCompareFrame.Internal.simLeOne`)

**Simplify the gradient weight.** For c > 0, its dilation weight times its similarity scale raised to three quarters equals c. (`Breakdown.Periodic.TorusCompareFrame.Internal.gradWeight`)

**Simplify the gradient norm factor.** For c > 0, c times its similarity scale raised to minus three quarters equals its dilation weight. (`Breakdown.Periodic.TorusCompareFrame.Internal.gradNormFactor`)

**Simplify the velocity weight.** For c > 0, its dilation weight times its similarity scale raised to one quarter equals c raised to 1 − 1/(2α). (`Breakdown.Periodic.TorusCompareFrame.Internal.velWeight`)

**Simplify the velocity norm factor.** For c > 0, c raised to 1 − 1/(2α) times its similarity scale raised to minus one quarter equals its dilation weight. (`Breakdown.Periodic.TorusCompareFrame.Internal.velNormFactor`)

**Rescale the gradient comparison.** For α > 1, 0 < c ≤ 1, and an admissible shell scale, the dilation algebra makes each gradient component of the restricted torus versus whole space difference scale by the dilation weight. (`Breakdown.Periodic.TorusCompareFrame.Internal.gradPart`)

**Rescale the velocity comparison.** For α > 1, 0 < c ≤ 1, and an admissible shell scale, the velocity dilation interface makes the velocity component of the restricted torus versus whole space difference scale by the dilation weight. (`Breakdown.Periodic.TorusCompareFrame.Internal.velocityPart`)

**Supply the change of scale formula.** For α > 1, the velocity dilation and dilation algebra hypotheses bound the restricted torus versus whole space difference after rescaling by c by c raised to the dilation exponent times the difference on the correspondingly rescaled shell, whenever 0 < c ≤ 1 and that shell is admissible. (`Breakdown.Periodic.fracFrameChange`)

### Breakdown.Frac.TorusCompareHeatSolenoidal

This file proves the heat shift law for the whole space solenoidal source operator, which simplifies the source entry formulas.

**Bound the heat multiplier.** For α > 1 and τ > 0, the norm of the scalar heat multiplier times the identity is at most τ raised to −1/(2α). (`Breakdown.Periodic.FracShiftCompare.Internal.phiSmul_norm_le`)

**Measurability of the multiplier.** The scalar heat multiplier times the identity is almost everywhere strongly measurable for every α and τ. (`Breakdown.Periodic.FracShiftCompare.Internal.phiSmul_aesm`)

**Read the multiplier on L² fields.** For α > 1 and τ > 0, the field operator with the scalar heat multiplier agrees almost everywhere with pointwise multiplication of its L² input. (`Breakdown.Periodic.FracShiftCompare.Internal.phiOp_ae`)

**Combine the heat factors.** For nonnegative t, multiplying the source heat factor at τ by the heat factor at t gives the source heat factor at t + τ. (`Breakdown.Periodic.FracShiftCompare.Internal.heat_mul_phi`)

**Heat shifts the L² multiplier.** For α > 1, nonnegative t, and positive τ, applying the source multiplier after L² heat evolution equals the source multiplier at time t + τ. (`Breakdown.Periodic.FracShiftCompare.Internal.phiOp_heat`)

**Heat shifts the state multiplier.** For α > 1, the heat semigroup interface makes the state source multiplier after nonnegative heat evolution equal the multiplier at the sum of the times when its original time is positive. (`Breakdown.Periodic.FracShiftCompare.Internal.phiX_heat`)

**Pair real and complex vectors.** The real inner product of a complexified real vector with a complex vector equals the inner product with that complex vector's real part. (`Breakdown.Periodic.FracShiftCompare.Internal.inner_complexifyVec`)

**Pair real and complex L² fields.** The real inner product of a complexified real L² field with a complex L² field equals the inner product with the latter field's real part. (`Breakdown.Periodic.FracShiftCompare.Internal.inner_complexify`)

**Fourier transform as a real isometry.** This defines the L² Fourier transform as a real linear isometric equivalence by restricting scalars from its complex linear equivalence. (`Breakdown.Periodic.FracShiftCompare.Internal.transformIsometry`)

**Move the Fourier transform in a pair.** The real inner product of a Fourier transformed L² field with another field equals the inner product of the first field with the inverse transform of the second. (`Breakdown.Periodic.FracShiftCompare.Internal.inner_transform`)

**Pair solenoidal heat with a state.** For α > 1 and τ > 0, pairing the solenoidal heat of a real L² field with a state equals pairing that field with the state's source multiplier. (`Breakdown.Periodic.FracShiftCompare.Internal.proj_inner`)

**Supply the solenoidal heat shift.** For α > 1, the heat semigroup hypothesis gives the identity that whole space heat for t ≥ 0 after solenoidal heat for τ > 0 equals solenoidal heat for t + τ on every real L² source. (`Breakdown.Periodic.fracHeatSolenoidalShift`)

### Breakdown.Frac.TorusCompareLambda

This file identifies the whole space and torus source operators with their piecewise integral formulas.

**Evaluate a finite operator sum.** A finite sum of continuous linear maps between piece spaces evaluates pointwise as the corresponding finite sum of their values. (`Breakdown.Periodic.FracCompareLambda.Internal.sum_pieceConv_apply`)

**Compare short time powers.** For α > 1 and 0 < τ ≤ 1, τ raised to −3/(4α) is at most τ raised to −3/4. (`Breakdown.Periodic.FracCompareLambda.Internal.rpow_exponent_le`)

**Similarity scales are positive.** A positive scale parameter has a positive similarity scale. (`Breakdown.Periodic.FracCompareLambda.Internal.simScale_pos`)

**Small similarity scales stay bounded.** For α > 1 and 0 < μ ≤ 1, the similarity scale is at most one. (`Breakdown.Periodic.FracCompareLambda.Internal.simScale_le_one`)

**Similarity scales preserve order.** For α > 1 and 0 < μ ≤ T, the similarity scale of μ is at most the similarity scale of T. (`Breakdown.Periodic.FracCompareLambda.Internal.simScale_mono`)

**All step scales fit the shell.** For α > 1, positive T and λ at most one, and positive b with the initial rescaled radius at most one eighth, every step similarity scale is admissible for the shell. (`Breakdown.Periodic.FracCompareLambda.Internal.isShellScale_step`)

**Continuity of whole space sources.** The solenoidal heat continuity interface makes each fixed whole space source action continuous at positive times. (`Breakdown.Periodic.FracCompareLambda.Internal.lambdaR3_continuousOn`)

**Continuity of torus sources.** For μ > 0, the source continuity interface makes each fixed torus source action continuous at positive times. (`Breakdown.Periodic.FracCompareLambda.Internal.lambdaTorus_continuousOn`)

**Supply whole space source formulas.** For α > 1, the sequence, piece convolution, response bound, and solenoidal heat continuity hypotheses express each whole space source slot as the finite sum of integrals from zero to the slot time of the approximant weights times the shell response of the corresponding shell path, for piece lengths in (0,1]. (`Breakdown.Periodic.fracR3LambdaFormula`)

**Supply torus source formulas.** For α > 1, the sequence, piece convolution, torus response bound, and source continuity hypotheses express each torus source slot as the weighted integral of its shell response at the source step scale, from zero to the slot time, for the stated positive piece length, T and λ at most one, and a fitting positive shell. (`Breakdown.Periodic.fracTorusLambdaFormula`)

### Breakdown.Frac.TorusCompareLambdaAssembly

This file combines the finite window and geometric tail bounds into the source operator comparison for the torus inverse construction.

**Expand the torus inverse source map.** Under the inverse series, sequence, piece composition, and norm interfaces, admissible positive parameters with geometric ratio below one express the restricted torus inverse source map as a finite sum of entries. (`Breakdown.Periodic.FracCompareLambdaAssembly.Internal.torus_apply`)

**Expand the whole space inverse map.** Under the inverse series, sequence, piece composition, and norm interfaces, positive period, step count, and θ with geometric ratio below one express the restricted whole space inverse source map as a finite sum of entries. (`Breakdown.Periodic.FracCompareLambdaAssembly.Internal.r3_apply`)

**A small time gives a small shell.** For α > 0 and positive T and b, the bound T < (1/(64b²)) raised to α makes the similarity length times b at most one eighth. (`Breakdown.Periodic.FracCompareLambdaAssembly.Internal.shell_small`)

**Assemble the source comparison.** For α > 1, the inverse series, sequence, piece composition, operator norm, finite window, and tail hypotheses make the restricted inverse shift source operator on the torus converge in operator norm to its whole space counterpart as positive T tends to zero, for a matching framework and the stated positive parameters with step length at most one half and dilation weight below θ < 1. (`Breakdown.Periodic.fracLambdaComparison`)

### Breakdown.Frac.TorusCompareSeedAssembly

This file combines free heat comparison with geometric tail control to compare the initial seed contributions in the two sequence systems.

**Express the scaled physical field.** For c > 0, the physical field scaling equals dilation at the similarity scale multiplied by c raised to 1 − 1/α. (`Breakdown.Periodic.FracCompareSeedAssembly.Internal.scaleField_eq`)

**Multiply similarity scales.** For nonnegative a and c, the similarity scale of their product is the product of their similarity scales. (`Breakdown.Periodic.FracCompareSeedAssembly.Internal.simScale_mul`)

**Similarity scales are positive.** A positive scale parameter has a positive similarity scale. (`Breakdown.Periodic.FracCompareSeedAssembly.Internal.simScale_pos`)

**Separate the seed scalar factors.** For λ > 0, the nth power of λ raised to the dilation exponent divided by θ equals θ to power −n times λ to power n raised to that exponent. (`Breakdown.Periodic.FracCompareSeedAssembly.Internal.dil_pow_eq`)

**Separate the dilation weight.** For x > 0, its dilation weight is x raised to 1 − 1/α times its similarity scale raised to one quarter. (`Breakdown.Periodic.FracCompareSeedAssembly.Internal.dil_split`)

**Transfer a free heat error bound.** For α > 1 and the stated positive scale and θ restrictions, transplantation and embedding dilation convert the assumed free heat error bound for a dilated test field into an error at most η in the nth seed slot. (`Breakdown.Periodic.FracCompareSeedAssembly.Internal.slot_le_of_freeHeat`)

**Read a torus restriction slot.** Under the sequence and piece composition specifications and a nonnegative piece length, a torus restriction slot applies the spatial restriction at that step's similarity scale. (`Breakdown.Periodic.FracCompareSeedAssembly.Internal.torus_slot`)

**Bound seed errors geometrically.** Under the heat semigroup and dilation algebra interfaces, uniform restriction bounds, a bounded torus seed, 0 < λ < 1, positive θ, and nonnegative time, the seed slot difference is bounded by the stated constant times the nth geometric ratio. (`Breakdown.Periodic.FracCompareSeedAssembly.Internal.slot_le_geometric`)

**Small time gives a small scale.** For α > 1 and positive T and y, T < y raised to α implies that the similarity scale of T is less than y. (`Breakdown.Periodic.FracCompareSeedAssembly.Internal.simScale_small`)

**Small similarity scales stay bounded.** For α > 1 and 0 < T ≤ 1, the similarity scale of T is at most one. (`Breakdown.Periodic.FracCompareSeedAssembly.Internal.simScale_le_one`)

**Make all seed slots close.** For α > 1, the stated transplant, dilation, heat comparison, and restriction interfaces make every seed slot error at most any positive η once T is small enough, provided b > 0 and 0 < λ < 1 with its dilation weight below θ. (`Breakdown.Periodic.FracCompareSeedAssembly.Internal.slot_bound`)

**Assemble the seed comparison.** For α > 1, the seed entry, transplantation, test dilation, free heat comparison, embedding, restriction, sequence, composition, norm, heat semigroup, and dilation hypotheses make the restricted inverse shift seed maps for a finite dimensional test lift on the torus and whole space arbitrarily close in operator norm at sufficiently small positive T under the stated admissible step and weight parameters. (`Breakdown.Periodic.fracSeedComparison`)

### Breakdown.Frac.TorusCompareSeedEntry

This file computes the initial seed entries of the inverse shift operators on the whole space and the torus.

**Rewrite a whole space seed slot.** For heat and dilation operators satisfying the stated semigroup and scaling laws, 0 < μ ≤ λ < 1 and s ≥ 0 turn the dilated heat of an endpoint into the stated heat evolution of the dilated initial state. (`_private.Breakdown.Frac.TorusCompareSeedEntry.0.Breakdown.Periodic.frac_r3_slot`)

**Combine seed heat times.** For positive T, 0 ≤ μ ≤ λ < 1, and s ≥ 0, the two successive torus heat evolutions combine into heat evolution at T times μs + 1 − μ. (`_private.Breakdown.Frac.TorusCompareSeedEntry.0.Breakdown.Periodic.frac_torus_slot`)

**Supply whole space seed entries.** For α > 1, the inverse series, sequence, whole space chain, operator norm, and piece operator hypotheses identify the nth inverse shift seed slot with θ⁻ⁿ times heat for s + λ⁻ⁿ − 1 of the seed dilated by λⁿ, for a matching heat and dilation framework with λ = exp(−P/k), P > 0, k > 0, and λ raised to the dilation exponent below θ < 1. (`Breakdown.Periodic.fracR3SeedEntry`)

**Supply torus seed entries.** For α > 1, the inverse series, sequence, torus chain, operator norm, and piece operator hypotheses identify the nth inverse shift seed slot with (λ raised to the dilation exponent divided by θ)ⁿ times the seed heated for T(λⁿs + 1 − λⁿ), when 0 < T ≤ 1, 0 < λ < 1, and the dilation weight is below θ < 1. (`Breakdown.Periodic.fracTorusSeedEntry`)

### Breakdown.Frac.TorusCompareTail

This file controls the geometric tails of the sequence comparison using shift chain and restriction norm estimates.

**Bound a scaled dilation.** In a scaled mild framework with exponent κ, dilation at μ > 0 has operator norm at most μ raised to κ. (`Breakdown.Periodic.FracTorusCompareTail.Internal.norm_scaledDil_le`)

**Bound one normalized shift step.** In a scaled mild framework and for θ > 0, the normalized endpoint followed by free step operator has norm at most the exponential step scale raised to κ divided by θ. (`Breakdown.Periodic.FracTorusCompareTail.Internal.norm_scaledShift_entry`)

**Supply the tail comparison bound.** For α > 1, the shift chain norm, operator norm, and whole space restriction bound hypotheses give a common geometric bound K times (step dilation weight divided by θ)ʲ times the shell sequence norm for both torus and whole space entries j steps after their source, under the matching framework, half step, positive parameter, and shell fitting conditions. (`Breakdown.Periodic.fracTailBound`)

### Breakdown.Frac.TorusCompareWindow

This file bounds a finite window of sequence entries by splitting the singular time integral and using local solenoidal heat comparison.

**Integrate a mild endpoint singularity.** A function continuous inside a nonnegative interval and bounded there by a constant times the distance to the right endpoint raised to −3/4 is interval integrable. (`Breakdown.Periodic.FracCompareWindow.Internal.intervalIntegrable_of_singular`)

**Continuity of a shifted source term.** Pointwise positive time continuity and a uniform τ to power −3/4 operator bound make the shifted source applied to a continuous path continuous on the stated interval where its source time is positive and at most one. (`Breakdown.Periodic.FracCompareWindow.Internal.continuousOn_apply_shift`)

**Bound a weighted source term.** Given nonnegative bounds for the weight, state, outer map, and source operator, and 0 < v ≤ τ ≤ 1, the weighted composed source norm is bounded by their product times v raised to −3/4. (`Breakdown.Periodic.FracCompareWindow.Internal.norm_term_le`)

**Split a finite window integral.** For continuous weighted source terms satisfying the stated operator and path bounds, a far from zero comparison bound and the split integral interface bound their integral difference by a linear far error plus a constant times ε raised to one quarter. (`Breakdown.Periodic.FracCompareWindow.Internal.window_piece`)

**The dilation exponent is nonnegative.** For α > 1, the dilation exponent is nonnegative. (`Breakdown.Periodic.FracCompareWindow.Internal.exponent_nonneg`)

**Compare short time kernel powers.** For α > 1 and 0 < τ ≤ 1, τ raised to −3/(4α) is at most τ raised to −3/4. (`Breakdown.Periodic.FracCompareWindow.Internal.rpow_kernel_le`)

**Similarity scales are positive.** A positive scale parameter has a positive similarity scale. (`Breakdown.Periodic.FracCompareWindow.Internal.sim_pos`)

**Small similarity scales stay bounded.** For α > 1 and 0 < μ ≤ 1, the similarity scale is at most one. (`Breakdown.Periodic.FracCompareWindow.Internal.sim_le_one`)

**Similarity scales preserve order.** For α > 1 and 0 < μ ≤ T, the similarity scale of μ is at most that of T. (`Breakdown.Periodic.FracCompareWindow.Internal.sim_mono`)

**Multiply similarity scales.** For nonnegative a and c, the similarity scale of their product equals the product of their similarity scales. (`Breakdown.Periodic.FracCompareWindow.Internal.sim_mul`)

**Small time gives a small scale.** For α > 1 and positive T and X, T < X raised to α implies that the similarity scale of T is less than X. (`Breakdown.Periodic.FracCompareWindow.Internal.sim_lt`)

**Bound the torus restriction operator.** A nonnegative uniform bound for the norm of the torus restriction function gives the same bound for the restriction operator norm. (`Breakdown.Periodic.FracCompareWindow.Internal.norm_restrictTorus_le`)

**Small dilations are contractions.** For α > 1 and 0 < c ≤ 1, the dilation algebra interface bounds the fractional dilation operator norm by one. (`Breakdown.Periodic.FracCompareWindow.Internal.norm_dil_le`)

**Bound a weighted identity map.** For α > 1 and 0 < c ≤ 1, the identity on the torus state space multiplied by the dilation weight has operator norm at most one. (`Breakdown.Periodic.FracCompareWindow.Internal.norm_smul_id_le`)

**Bound a fourth root.** For nonnegative r and ε with ε ≤ r to the fourth power, ε raised to one quarter is at most r. (`Breakdown.Periodic.FracCompareWindow.Internal.rpow_quarter_le`)

**A small scale fits the shell.** For positive T and b, T < 1/(64b²) implies that the square root of T times b is at most one eighth. (`Breakdown.Periodic.FracCompareWindow.Internal.sqrt_mul_le_of_lt`)

**Supply source continuity.** For α > 1, the rescaled torus source operator applied to any fixed real L² field is continuous at positive source times for every positive scale. (`Breakdown.Periodic.FracCompareWindow.Internal.source_continuous`)

**Bound one comparison window term.** For α > 1, the stated frame, continuity, dilation, shell, support, and uniform norm hypotheses turn the assumed heat comparison away from zero into the displayed weighted integral error bound with an ε to power one quarter remainder. (`Breakdown.Periodic.FracCompareWindow.Internal.window_term`)

**Close the finite window estimate.** Under the stated positive θ, finite index, nonnegative constant, and parameter choices, the weighted finite sum of comparison errors is at most η times the state norm bound. (`Breakdown.Periodic.FracCompareWindow.Internal.final_arith`)

**Supply the finite window bound.** For α > 1, the entry formulas, frame change, split integral, solenoidal heat comparison, response and restriction bounds, advection, dilation, and continuity hypotheses make torus and whole space entries uniformly close over any fixed finite range of lags as positive T tends to zero, with error at most η times the shell sequence norm under the stated matching framework and admissible step parameters. (`Breakdown.Periodic.fracWindowBound`)

### Breakdown.Frac.TorusCutoffGrad

This file proves that the gradient error of the rescaled cutoff tends to zero near the terminal time, a key part of the torus approximation closeness argument.

**Smoothness of the cutoff field.** For a rotating profile, positive T, and t < T, the approximate field properties interface makes the cutoff field smooth in space. (`Breakdown.Periodic.FracInternal.CutoffGradBound.approx_contDiff`)

**Coordinate vectors have unit norm.** Every standard coordinate vector in the three dimensional space has norm one. (`Breakdown.Periodic.FracInternal.CutoffGradBound.unit_norm`)

**Bound the coordinate derivative sum.** For a continuous linear map on three dimensional space, the sum of the squared norms of its values on coordinate vectors is at most three times its squared operator norm. (`Breakdown.Periodic.FracInternal.CutoffGradBound.sum_sq_le`)

**Bound a dilated spatial derivative.** For a differentiable field, the derivative norm of its translated and rescaled version is at most the product of the absolute amplitude, absolute spatial scale, and derivative norm at the transformed point. (`Breakdown.Periodic.FracInternal.CutoffGradBound.fderiv_dil_norm`)

**Distance after centered dilation.** For r ≥ 0, the distance from the center to the center plus r times y equals r times the norm of y. (`Breakdown.Periodic.FracInternal.CutoffGradBound.dist_dil`)

**The cutoff agrees in the inner region.** Under the approximate field properties interface, a rotating profile with T > 0 and t < T agrees with its rescaled cutoff wherever the physical radius is at most one quarter of the central radius. (`Breakdown.Periodic.FracInternal.CutoffGradBound.core_eq`)

**The cutoff derivative vanishes outside.** Under the approximate field properties interface, a rotating profile with T > 0 and t < T has zero approximate field derivative outside half the central radius. (`Breakdown.Periodic.FracInternal.CutoffGradBound.outer_zero`)

**Split the squared decay bound.** For 0 ≤ R ≤ ρ, the square of B divided by (1 + ρ)² is at most B² times (1 + R) to power −1/2 times (1 + ρ) to power −7/2. (`Breakdown.Periodic.FracInternal.CutoffGradBound.tail_arith`)

**Bound the cutoff gradient error.** For α > 1, a rotating profile and the approximate field interface, the stated profile and outer cutoff derivative bounds give the displayed decaying bound for the summed squared gradient error when the similarity length is at most one sixteenth. (`Breakdown.Periodic.FracInternal.CutoffGradBound.pointwise`)

**Make the cutoff gradient error small.** For 1 < α < 5/4, the approximate field and self similar decay interfaces make the cutoff gradient energy error smaller than any positive tolerance when the remaining time is sufficiently small, uniformly over 0 < T ≤ 1 and 0 ≤ t < T. (`Breakdown.Periodic.fracCutoffGrad`)

### Breakdown.Frac.TorusCutoffMass

This file bounds the L² mass of the rescaled cutoff by its fractional similarity power, supporting the torus approximation size estimates.

**Bound the cutoff velocity field.** For 1 < α < 5/4 and a rotating profile, the self similar decay interface bounds the approximate field by a nonnegative constant times the smoothed inverse radius to power 2α − 1 plus another nonnegative constant. (`Breakdown.Periodic.CutoffMass.Internal.field_bound`)

**Cancel the velocity scaling powers.** For α > 0, μ > 0, and r ≥ 0, the similarity amplitude cancels the scale in the inverse radius power, leaving (1 + r) raised to −(2α − 1). (`Breakdown.Periodic.CutoffMass.Internal.scale_cancel`)

**Cancel opposite scale powers.** For μ > 0, its powers with exponents 1/(2α) and −1/(2α) multiply to one. (`Breakdown.Periodic.CutoffMass.Internal.scale_one`)

**Bound the squared cutoff field.** For α > 1, a rotating profile, T > 0, and t < T, the approximate field interface and the stated nonnegative decay bounds give the displayed compactly supported radial upper bound for the squared rescaled cutoff norm. (`Breakdown.Periodic.CutoffMass.Internal.cut_sq_le`)

**Bound a squared radial decay term.** For r > 0 and p ≥ 0, r² times the square of A times (1 + r) raised to −p is at most A² times r raised to 2 − 2p. (`Breakdown.Periodic.CutoffMass.Internal.sq_rpow_le`)

**Integrate the radial cutoff bound.** For nonnegative radius and constant term and 0 ≤ p < 3/2, the stated radial cutoff majorant is integrable and its integral satisfies the displayed three dimensional power bound. (`Breakdown.Periodic.CutoffMass.Internal.radial_le`)

**Combine amplitude and volume powers.** For α > 0 and μ > 0, the squared similarity amplitude times the cubed inverse similarity length equals μ raised to −(5 − 4α)/(2α). (`Breakdown.Periodic.CutoffMass.Internal.power_identity`)

**Compute the cutoff radius power.** For μ > 0, the stated power of one eighth of the inverse similarity length equals the constant one eighth raised to 5 − 4α times μ raised to −(5 − 4α)/(2α). (`Breakdown.Periodic.CutoffMass.Internal.radius_identity`)

**Bound the cutoff mass.** For 1 < α < 5/4, the approximate field and self similar decay interfaces give every rotating profile a constant bounding its rescaled cutoff squared L² mass by the remaining time raised to −(5 − 4α)/(2α). (`Breakdown.Periodic.fracCutoffMass`)

### Breakdown.Frac.TorusDrift

This file removes the affine spatial pressure increments by a drift transformation while retaining the periodic velocity and original initial datum.

**Translate the second order remainder.** For a smooth field, translating its argument and adding a constant translates its second order remainder without changing its increment. (`Breakdown.Periodic.FracDrift.Internal.remainder_shift`)

**Translate the fractional power.** For a smooth field, translating its argument and adding a constant translates the fractional power without adding any extra term. (`Breakdown.Periodic.FracDrift.Internal.power_shift`)

**Fractional powers preserve periodicity.** For a smooth periodic field, its fractional power is unchanged by a unit translation in any coordinate direction. (`Breakdown.Periodic.FracDrift.Internal.power_periodic`)

**Pressure increments are constant.** For a fractional solution whose velocity is periodic at nonnegative times, the pressure increment under a coordinate unit translation at positive time is independent of the spatial point. (`Breakdown.Periodic.FracDrift.Internal.frac_pressure_shift_pos`)

**Pressure is periodic up to a slope.** For a fractional solution whose velocity is periodic at nonnegative times, pressure at every nonnegative time changes by its corresponding fixed coordinate increment under a unit translation. (`Breakdown.Periodic.FracDrift.Internal.frac_pressure_shift`)

**Rearrange the drift equation.** In an additive commutative group, the stated equation remains valid after adding and cancelling the auxiliary drift terms and adjusting the right side by c. (`Breakdown.Periodic.FracDrift.Internal.frac_combine`)

**Supply periodic pressure by drift.** For every α, the torus drift interface holds, allowing a periodic velocity solution to be adjusted to a solution with periodic pressure while preserving its initial datum. (`Breakdown.Periodic.fracTorusDrift`)

### Breakdown.Frac.TorusExports

This file exports the fractional periodic breakdown statement from the torus blowup interface for exponents between one and five quarters.

**Export fractional torus breakdown.** For 1 < α < 5/4, existence of the specified unbounded torus mild trajectory gives, for every viscosity ν > 0, smooth periodic divergence free initial data admitting no global smooth fractional solution whose velocity remains periodic at all nonnegative times. (`Breakdown.Periodic.fractionalBreakdownOnTorus_of_torusBlowup`)

### Breakdown.Frac.TorusFinal

This file uses mild uniqueness, smooth to mild conversion, drift, and viscosity normalization to turn torus blowup into the final fractional periodic obstruction.

**Normalize the viscosity of a solution.** For ν > 0, rescaling time, velocity, and pressure in a fractional solution of viscosity ν with initial velocity ν times the datum gives a viscosity one solution with the original datum. (`_private.Breakdown.Frac.TorusFinal.0.Breakdown.Periodic.frac_scaled_solution`)

**Derive torus breakdown from blowup.** For the given α, the torus mild uniqueness, smooth to mild, pressure drift, and unbounded mild trajectory hypotheses give every positive viscosity smooth periodic divergence free initial data admitting no global smooth fractional solution with periodic velocity at all nonnegative times. (`Breakdown.Periodic.fractionalBreakdownOnTorus_of_blowup`)

### Breakdown.Frac.TorusForce

This file constructs the fractional torus forcing state from its Fourier coefficients and proves its existence and algebraic properties.

**Nonzero lattice frequencies are large.** Every nonzero lattice index has frequency norm at least one. (`Breakdown.Periodic.FracForce.Internal.one_le_norm_freq`)

**Compare fractional lattice symbols.** For α ≥ 1, the squared ordinary heat frequency is at most the corresponding frequency raised to 2α. (`Breakdown.Periodic.FracForce.Internal.sq_le_rpow`)

**The lattice factor is nonnegative.** The fractional lattice heat factor is nonnegative for every α, time, and lattice index. (`Breakdown.Periodic.FracForce.Internal.factor_nonneg`)

**Compare the two lattice heat factors.** For α ≥ 1, the fractional lattice heat factor is at most the ordinary heat factor at the same time and lattice index. (`Breakdown.Periodic.FracForce.Internal.factor_le_heat`)

**The lattice heat factor decreases.** For s ≤ t, the fractional lattice heat factor at t is at most its value at s. (`Breakdown.Periodic.FracForce.Internal.factor_anti`)

**The lattice factor is even.** The fractional lattice heat factor takes the same value at a lattice index and its negative. (`Breakdown.Periodic.FracForce.Internal.factor_neg`)

**Multiply lattice heat factors.** For nonnegative s and t, the fractional lattice heat factor at s + t is the product of its factors at s and t. (`Breakdown.Periodic.FracForce.Internal.factor_add`)

**Continuity of the lattice factor.** For fixed α and lattice index, the fractional lattice heat factor is continuous in time. (`Breakdown.Periodic.FracForce.Internal.continuous_factor`)

**Define the forced Fourier sequence.** This defines the forced Fourier coefficient sequence by applying the solenoidal projection and the weighted fractional heat factor at positive time, and by zero at nonpositive time. (`Breakdown.Periodic.FracForce.Internal.seq`)

**Bound the forced Fourier sequence.** For α ≥ 1 and 0 < s₁ ≤ s, each forced Fourier coefficient at s is bounded by twice the cell integral of the field norm times the ordinary weighted heat factor at s₁. (`Breakdown.Periodic.FracForce.Internal.norm_seq_le_of_le`)

**Sum the squared heat majorant.** At positive time, the squared weighted ordinary heat majorant is summable over the frequency lattice for any real amplitude. (`Breakdown.Periodic.FracForce.Internal.summable_bound`)

**The forced sequence belongs to ℓ².** For α ≥ 1, the forced Fourier coefficient sequence is square summable for every time and input field. (`Breakdown.Periodic.FracForce.Internal.memℓp_seq`)

**The forced sequence is admissible.** For α ≥ 1, the forced Fourier sequence belongs to the real solenoidal field subspace at every time. (`Breakdown.Periodic.FracForce.Internal.seq_mem`)

**Build the forced torus state.** For α ≥ 1, this packages the square summable forced Fourier sequence and its field subspace membership as a torus state. (`Breakdown.Periodic.FracForce.Internal.vec`)

**Read a forced state coefficient.** For α ≥ 1, each coefficient of the constructed forced torus state is its defining forced Fourier sequence coefficient. (`Breakdown.Periodic.FracForce.Internal.vec_apply`)

**The forced state meets its contract.** For α ≥ 1, the constructed forced torus state satisfies the prescribed Fourier coefficient specification. (`Breakdown.Periodic.FracForce.Internal.vec_spec`)

**Identify the torus force realization.** For α ≥ 1, the chosen torus force equals the explicitly constructed forced Fourier state. (`Breakdown.Periodic.FracForce.Internal.force_eq`)

**Continuity of the forced torus state.** For α ≥ 1 and a fixed input field, the constructed forced torus state is continuous at positive times. (`Breakdown.Periodic.FracForce.Internal.vec_continuousOn`)

**Supply torus force existence.** For α ≥ 1, a torus force realization satisfying its Fourier specification exists. (`Breakdown.Periodic.fracTorusForceExists`)

**Supply the torus force algebra.** For α ≥ 1, the torus heat algebra hypothesis identifies forcing with its prescribed Fourier coefficients, makes forcing at τ ≥ σ > 0 equal heat evolution for τ − σ of forcing at σ, and makes each fixed field's forcing trajectory continuous at positive times. (`Breakdown.Periodic.fracTorusForceAlgebra`)

### Breakdown.Frac.TorusForceSmoothing

This file proves the positive time smoothing bound for periodic forcing from the fractional lattice multiplier estimates.

**Bound a fractional power.** For y ≥ 0 and 0 ≤ p ≤ 1, y raised to p is at most 1 + y. (`Breakdown.Periodic.FracForceSmoothing.Internal.rpow_le_one_add`)

**Bound a power times exponential decay.** For y ≥ 0 and 0 ≤ p ≤ 1, y raised to p times exp(−2y) is at most one. (`Breakdown.Periodic.FracForceSmoothing.Internal.rpow_mul_exp_le`)

**Bound quadratic heat smoothing.** For α > 1, τ > 0, and r ≥ 0, r² times exp(−2r raised to 2α times τ) is at most τ raised to −1/α. (`Breakdown.Periodic.FracForceSmoothing.Internal.sq_mul_exp_le`)

**Bound the weighted lattice factor.** For α > 1 and 0 < τ ≤ 1, the lattice weight times the squared fractional heat factor is at most twice τ raised to −1/α. (`Breakdown.Periodic.FracForceSmoothing.Internal.weight_factor_le`)

**Relate weighted Fourier coefficients.** For a torus state, its lattice weight times the squared norm of its ordinary coefficient equals the squared norm of its state sequence coefficient. (`Breakdown.Periodic.FracForceSmoothing.Internal.weight_mul_sq_coeff`)

**Supply torus force smoothing.** For α > 1, the torus heat and force algebra hypotheses bound forcing at 0 < τ ≤ 1 by C times τ raised to −1/(2α) times the source field's cell L² norm whenever the field is continuous and periodic. (`Breakdown.Periodic.fracForceSmoothing_of`)

### Breakdown.Frac.TorusForced

This file establishes continuity and integrability of periodic nonlinear and source terms, then supplies the forced mild representation.

**Heat evolution respects limits.** The torus heat algebra interface makes simultaneous limits in time and state pass through fractional torus heat evolution. (`Breakdown.Periodic.FracTorusForced.Internal.heat_tendsto`)

**Torus heat is a contraction.** The torus heat algebra interface bounds the norm of a heated state by its original norm at every time. (`Breakdown.Periodic.FracTorusForced.Internal.heat_norm_apply_le`)

**Factor the kernel through heat.** Under the torus kernel algebra interface, the kernel at τ ≥ σ > 0 equals heat evolution for τ − σ of the kernel at σ. (`Breakdown.Periodic.FracTorusForced.Internal.kernel_eq_heat`)

**The kernel respects positive time limits.** Under the heat and kernel algebra interfaces, simultaneous limits of time and both states pass through the kernel when the limiting time is positive. (`Breakdown.Periodic.FracTorusForced.Internal.kernel_tendsto`)

**Kernel norms decrease with time.** Under the heat and kernel algebra interfaces, the kernel operator norm at τ is at most its norm at σ whenever 0 < σ ≤ τ. (`Breakdown.Periodic.FracTorusForced.Internal.kernel_opNorm_anti`)

**Bound the kernel at all positive times.** The heat algebra, kernel algebra, and sharp kernel bound interfaces give a positive constant bounding the kernel by the product of the state norms times Cτ to power −3/(4α) + C for every positive τ. (`Breakdown.Periodic.FracTorusForced.Internal.kernel_norm_le`)

**Integrate the nonlinear kernel term.** For α > 1, the heat algebra, kernel algebra, and sharp bound interfaces make the quadratic kernel term of a continuous path integrable over a nonnegative time interval. (`Breakdown.Periodic.FracTorusForced.Internal.integrable_kernel`)

**Differences preserve periodicity.** The pointwise difference of two periodic vector fields is periodic. (`Breakdown.Periodic.FracTorusForced.Internal.periodic_sub`)

**Forcing preserves subtraction.** Under the torus force algebra interface, forcing the difference of two continuous fields equals the difference of their forced states. (`Breakdown.Periodic.FracTorusForced.Internal.force_sub`)

**Bound forcing by the cell L² norm.** The heat algebra, force algebra, and force smoothing interfaces give a positive constant bounding the forced norm of a continuous periodic field by its cell L² norm times Cτ to power −1/(2α) + C at positive times. (`Breakdown.Periodic.FracTorusForced.Internal.norm_force_le`)

**Cell L² differences tend to zero.** A jointly continuous field on the stated closed time strip has cell L² distance from its value at a fixed time tending to zero within that interval. (`Breakdown.Periodic.FracTorusForced.Internal.tendsto_sqDist`)

**Continuity of time dependent forcing.** Under the heat, force, and smoothing interfaces, a jointly continuous field that is periodic at each time yields a continuous forced term on the stated open interval before its target time. (`Breakdown.Periodic.FracTorusForced.Internal.continuousOn_force`)

**Integrate time dependent forcing.** For α > 1, the heat, force, and smoothing interfaces make the source convolution integrable up to any target time in the closed interval for a jointly continuous periodic forcing field. (`Breakdown.Periodic.FracTorusForced.Internal.integrable_force`)

**Derive a forced mild representation.** For 1 < α < 5/4, the heat algebra, kernel algebra, sharp kernel bound, fractional coefficient, force algebra, and force smoothing interfaces imply that a forced periodic solution has the mild representation. (`Breakdown.Periodic.fracForcedPeriodicIsMild_of`)

### Breakdown.Frac.TorusForcedModes

This file differentiates and integrates individual Fourier modes of a forced periodic fractional solution to obtain its modewise mild identity.

**Differentiate a forced Fourier mode.** Under the fractional coefficient interface, each Fourier mode of a forced periodic solution on a nonempty time interval has the stated fractional damping, projected advection, and projected forcing derivative at interior times. (`Breakdown.Periodic.FracTorusForcedModes.Internal.mode_deriv`)

**Integrate a forced Fourier mode.** Under the kernel, fractional coefficient, and force interfaces, a forced periodic solution with a continuous state path and integrable nonlinear and source terms satisfies the displayed mild identity in each Fourier mode. (`Breakdown.Periodic.FracTorusForcedModes.Internal.mode_identity`)

### Breakdown.Frac.TorusGlue

This file rescales and concatenates matching torus mild pieces into a continuous mild solution before the terminal time.

**State the mild identity at one time.** This proposition requires integrability of the quadratic kernel term and equality of the current state with its heated initial state plus the nonlinear integral. (`Breakdown.Periodic.FracGlue.Internal.FracMildAt`)

**Read the unit scale kernel.** For α > 1, the nonlinear kernel of the unit scale step framework equals the fractional torus kernel. (`Breakdown.Periodic.FracGlue.Internal.unitFrame_K`)

**Read the unit scale heat operator.** For α > 1, the heat operator of the unit scale step framework equals the fractional torus heat operator. (`Breakdown.Periodic.FracGlue.Internal.unitFrame_G`)

**Identify the unit scale mild identity.** For α > 1, the variation of constants identity in the unit scale framework is equivalent to the fractional torus mild identity at the same times. (`Breakdown.Periodic.FracGlue.Internal.unitFrame_mildAt_iff`)

**Transfer a mild identity along equality.** If two paths agree on the closed interval from a to t with a ≤ t, the fractional mild identity for one path on that interval also holds for the other. (`Breakdown.Periodic.FracGlue.Internal.fracMildAt_congr`)

**Read a glued path inside a step.** For T > 0 and 0 < λ < 1, pieces whose endpoints satisfy the dilation matching condition give the stated rescaled piece value at every point of each physical step interval. (`Breakdown.Periodic.FracGlue.Internal.glue_at`)

**Rescale a mild piece to physical time.** For α > 1 and 0 < μ ≤ 1, a path mild in the μ step framework gives a fractional torus mild identity after the stated time and amplitude rescaling on its physical interval. (`Breakdown.Periodic.FracGlue.Internal.piece_mildIdentity`)

**Glue finitely many mild pieces.** For α > 1, 0 < T ≤ 1, and 0 < λ < 1, the concatenation interface makes matching mild pieces into a continuous mild path up to each finite step start. (`Breakdown.Periodic.FracGlue.Internal.glue_upto`)

**Supply mild gluing.** For α > 1, the restriction, concatenation, and time shift hypotheses glue mild pieces with dilation matched endpoints into a torus mild path on [0,T), for 0 < T ≤ 1 and 0 < λ < 1, with its value on every step equal to that piece multiplied by the inverse dilation weight of the step scale. (`Breakdown.Periodic.fracGlueMild_of`)

### Breakdown.Frac.TorusGlueUnbounded

This file uses the positive fractional dilation exponent and the step start values to supply the unboundedness criterion for the glued torus path.

**The dilation exponent is positive.** For α > 1, the dilation exponent is strictly positive. (`Breakdown.Periodic.FracInternal.GlueUnbounded.dilExponent_pos`)

**Read the glued path at a step start.** For T > 0 and 0 < λ < 1, the glued path at the nth step start equals the nth piece's initial value multiplied by the inverse dilation weight of that step scale. (`Breakdown.Periodic.FracInternal.GlueUnbounded.fracGluePieces_stepStart`)

**Supply unboundedness after gluing.** For α > 1, T > 0, and 0 < λ,θ < 1, perturbing pieces with a uniform positive pointwise norm lower bound by θⁿ times uniformly bounded pieces produces a glued torus path whose norm is unbounded on [0,T). (`Breakdown.Periodic.fracGlueUnbounded`)

### Breakdown.Frac.TorusHeat

This file constructs fractional torus heat as a lattice Fourier multiplier and proves its contraction, continuity, and semigroup algebra.

**The lattice heat factor is positive.** The fractional lattice heat factor is strictly positive for every α, time, and lattice index. (`Breakdown.Periodic.FracTorusHeatInternal.factor_pos`)

**The lattice heat factor is at most one.** The fractional lattice heat factor is at most one for every α, time, and lattice index. (`Breakdown.Periodic.FracTorusHeatInternal.factor_le_one`)

**Bound the absolute lattice factor.** The absolute value of the fractional lattice heat factor is at most one for every α, time, and lattice index. (`Breakdown.Periodic.FracTorusHeatInternal.abs_factor_le`)

**Negation reverses lattice frequency.** The frequency of a negated lattice index is the negative of its original frequency. (`Breakdown.Periodic.FracTorusHeatInternal.freq_neg`)

**The lattice heat factor is even.** The fractional lattice heat factor has the same value at a lattice index and its negative. (`Breakdown.Periodic.FracTorusHeatInternal.factor_neg`)

**Multiply nonnegative time heat factors.** For nonnegative times s and t, the fractional lattice heat factor at s + t is the product of its factors at s and t. (`Breakdown.Periodic.FracTorusHeatInternal.factor_add`)

**The zero time heat factor is one.** At time zero, every fractional lattice heat factor equals one. (`Breakdown.Periodic.FracTorusHeatInternal.factor_zero`)

**Negative heat times are clamped.** Replacing time by its maximum with zero leaves the fractional lattice heat factor unchanged. (`Breakdown.Periodic.FracTorusHeatInternal.factor_max`)

**Continuity of the lattice heat factor.** For fixed α and lattice index, the fractional lattice heat factor is continuous in time. (`Breakdown.Periodic.FracTorusHeatInternal.continuous_factor`)

**Scale the divergence pairing.** Multiplying a Fourier coefficient by a real scalar multiplies its divergence pairing by the same scalar viewed as a complex number. (`Breakdown.Periodic.FracTorusHeatInternal.divPairing_real_smul`)

**Heat preserves the field subspace.** Multiplying a torus state sequence by the fractional lattice heat factors preserves membership in the real solenoidal field subspace. (`Breakdown.Periodic.FracTorusHeatInternal.mem`)

**Build the torus heat operator.** This defines a continuous linear torus heat operator by multiplying state sequences by the bounded fractional lattice heat factors and restricting back to the field subspace. (`Breakdown.Periodic.FracTorusHeatInternal.op`)

**Read a torus heat coefficient.** Each sequence coefficient of the constructed heat operator is the original coefficient multiplied by its fractional lattice heat factor. (`Breakdown.Periodic.FracTorusHeatInternal.op_apply`)

**The heat operator meets its contract.** The constructed torus heat operator satisfies its Fourier coefficient specification at every time. (`Breakdown.Periodic.FracTorusHeatInternal.op_spec`)

**Identify the torus heat realization.** The chosen fractional torus heat operator equals the explicitly constructed Fourier multiplier operator. (`Breakdown.Periodic.FracTorusHeatInternal.heat_eq`)

**Continuity of torus heat trajectories.** For every α and torus state, the constructed heat evolution is continuous in time. (`Breakdown.Periodic.FracTorusHeatInternal.op_continuous`)

**Supply torus heat existence.** For every α, a fractional torus heat operator satisfying its Fourier specification exists. (`Breakdown.Periodic.fracTorusHeatExists`)

**Supply the torus heat algebra.** For every α, fractional torus heat multiplies each Fourier coefficient by its lattice heat factor, equals the identity at zero, obeys the semigroup law at nonnegative times, has operator norm at most one, clamps negative times to zero, and gives continuous trajectories for every state. (`Breakdown.Periodic.fracTorusHeatAlgebra`)

### Breakdown.Frac.TorusHeatCompareAssembly

This file turns uniform density estimates and lattice sum approximations into solenoidal and free heat comparisons between the torus and whole space.

**Similarity scales are positive.** A positive scale parameter has a positive similarity scale. (`Breakdown.Periodic.FracHeatCompare.Internal.simScale_pos`)

**Bound the similarity scale.** For α > 0 and positive μ and m, μ < m raised to α implies that the similarity scale of μ is less than m. (`Breakdown.Periodic.FracHeatCompare.Internal.simScale_lt`)

**Read the gradient Fourier density.** The gradient density equals the Fourier phase multiplied by the coordinate derivative factor, fractional heat factor, and solenoidal projection of the transformed source field. (`Breakdown.Periodic.FracHeatCompare.Internal.fracGradDensity_eq`)

**Continuity of the value lattice sum.** For fixed α, lattice scale, time, and source field, the lattice sum of the value density is continuous in the spatial point. (`Breakdown.Periodic.FracHeatCompare.Internal.continuous_value`)

**Continuity of the gradient lattice sum.** For fixed α, lattice scale, time, source field, and coordinate, the lattice sum of the gradient density is continuous in the spatial point. (`Breakdown.Periodic.FracHeatCompare.Internal.continuous_grad`)

**Group value and gradient densities.** This defines a family of Fourier densities indexed by an optional coordinate, using no coordinate for velocity and a chosen coordinate for its gradient. (`Breakdown.Periodic.FracHeatCompare.Internal.familyDensity`)

**Scale the heat comparison difference.** Scaling a source L² field by a real constant scales the difference between its restricted rescaled torus source and its restricted whole space solenoidal heat by the same constant. (`Breakdown.Periodic.FracHeatCompare.Internal.difference_smul`)

**Compare normalized compact sources.** For α > 1, the stated partition, series, inverse formula, density bound, and increment interfaces make torus and whole space source evolutions uniformly δ close at sufficiently small positive scale for compactly supported sources with L³⁄² norm at most one and times in the stated positive window. (`Breakdown.Periodic.FracHeatCompare.Internal.comparison_of_normalized`)

**Supply solenoidal heat comparison.** For α > 1, the partition sum, torus source series, whole space value formula, and source density decay and increment hypotheses imply that normalized torus forcing converges to whole space solenoidal heat on fixed observation shells, uniformly for supported sources of bounded L³⁄² norm and source times in any window [ε,ε inverse] with ε > 0. (`Breakdown.Periodic.fracHeatSolenoidalComparison_of`)

**Supply free heat comparison.** For α > 1, the partition sum, torus free series, whole space free formula, and free density decay and increment hypotheses make the normalized torus heat of a transplanted test field converge to its whole space heat uniformly on a fixed observation shell for times in [0,ε inverse] as the positive scale tends to zero. (`Breakdown.Periodic.fracFreeHeatComparison_of`)

### Breakdown.Frac.TorusHeatCompareDensity

This file proves decay and frequency increment bounds for the Fourier densities used in the torus versus whole space heat comparison.

**The whole space heat factor is positive.** The whole space fractional heat factor is strictly positive for every α, time, and frequency. (`Breakdown.Periodic.FracDensity.Internal.factor_pos`)

**The whole space heat factor is bounded.** The whole space fractional heat factor is at most one for every α, time, and frequency. (`Breakdown.Periodic.FracDensity.Internal.factor_le_one`)

**Compare quadratic and higher powers.** For α ≥ 1 and s ≥ 0, s² − 1 is at most s raised to 2α. (`Breakdown.Periodic.FracDensity.Internal.sq_sub_one_le_rpow`)

**Compare whole space heat factors.** For α ≥ 1 and 0 < ε ≤ τ, the fractional heat factor at τ is at most exp(ε) times the ordinary heat factor at ε. (`Breakdown.Periodic.FracDensity.Internal.factor_le_heat`)

**Bound a polynomially weighted factor.** For α ≥ 1 and 0 < ε ≤ τ, the fractional heat factor times (1 + frequency norm) to the sixth power satisfies the displayed uniform bound depending only on ε. (`Breakdown.Periodic.FracDensity.Internal.factor_decay`)

**Bound an increment of a real power.** For p ≥ 1 and 0 ≤ a ≤ b, the difference between b raised to p and a raised to p is at most p times b raised to p − 1 times b − a. (`Breakdown.Periodic.FracDensity.Internal.rpow_sub_le`)

**Bound differences of real powers.** For p ≥ 1 and a and b between zero and M, the absolute difference of their pth powers is at most p times M raised to p − 1 times their distance. (`Breakdown.Periodic.FracDensity.Internal.abs_rpow_sub_le`)

**Set the heat factor increment bound.** This defines the frequency increment constant as ε inverse times the derivative bound for the radial power on the ball of radius R. (`Breakdown.Periodic.FracDensity.Internal.factorDiffConst`)

**Bound a heat factor increment.** For α ≥ 1, ε > 0, τ ≤ ε inverse, and frequencies of norm at most R, the fractional heat factor difference is bounded by the specified increment constant times the frequency distance. (`Breakdown.Periodic.FracDensity.Internal.factor_diff_le`)

**The increment constant is nonnegative.** For α ≥ 1, ε > 0, and R ≥ 0, the heat factor increment constant is nonnegative. (`Breakdown.Periodic.FracDensity.Internal.factorDiffConst_nonneg`)

**Supply source density decay bounds.** For α > 1, fixed support and observation balls, and ε > 0, both the source value density and each gradient density are bounded by K times (1 + frequency norm) raised to −4, uniformly over supported real L² sources with L³⁄² norm at most one and times in [ε,ε inverse]. (`Breakdown.Periodic.fracSourceDensityBounds`)

**Supply source density increment bounds.** For α > 1, fixed support and observation balls, ε > 0, and a frequency annulus with positive inner radius, the source value and gradient densities have uniform Lipschitz bounds in frequency over supported real L² sources with L³⁄² norm at most one and times in [ε,ε inverse]. (`Breakdown.Periodic.fracSourceDensityIncrement`)

**Bound the free value density.** The free heat value density has norm at most the norm of the source field's Fourier transform at the same frequency. (`Breakdown.Periodic.FracDensity.Internal.norm_free_le`)

**Bound the free gradient density.** The free heat gradient density has norm at most 2π times the frequency norm times the source field's Fourier transform norm. (`Breakdown.Periodic.FracDensity.Internal.norm_freeGrad_le`)

**The heat factor contracts coefficients.** Multiplying a coefficient by the fractional heat factor never increases its norm. (`Breakdown.Periodic.FracDensity.Internal.norm_factor_smul_le`)

**Bound free density increments.** For α ≥ 1 and the stated positive time window and spatial and frequency bounds, a uniformly bounded Lipschitz Fourier transform gives the displayed Lipschitz bound for the free heat density in frequency. (`Breakdown.Periodic.FracDensity.Internal.free_sub`)

**Bound gradient density increments.** The stated bounds on a free value density, its frequency difference, and the second frequency give the displayed difference bound for each free gradient density. (`Breakdown.Periodic.FracDensity.Internal.freeGrad_sub`)

**Supply free density decay bounds.** For α > 1, a test field, a fixed observation ball, and ε > 0, both its free heat value density and gradient densities are bounded by K times (1 + frequency norm) raised to −4 uniformly for times in [0,ε inverse]. (`Breakdown.Periodic.fracFreeDensityBounds`)

**Supply free density increment bounds.** For α > 1, a test field, a fixed observation ball, ε > 0, and a frequency annulus with positive inner radius, its free heat value and gradient densities have uniform Lipschitz bounds in frequency for times in [0,ε inverse]. (`Breakdown.Periodic.fracFreeDensityIncrement`)

### Breakdown.Frac.TorusHeatCompareInverse

This file proves the whole space inverse Fourier formulas for fractional free and solenoidal heat, supplying one side of the localization comparison.

**Bound a square by a higher power.** For α ≥ 1 and t ≥ 0, t² is at most t raised to 2α plus one. (`Breakdown.Periodic.FracHeatCompareInverse.Internal.sq_le_rpow_add_one`)

**The fractional heat factor is positive.** The whole space fractional heat factor is strictly positive for every α, time, and frequency. (`Breakdown.Periodic.FracHeatCompareInverse.Internal.fracHeatFactor_pos`)

**Bound fractional heat by a Gaussian.** For α ≥ 1 and τ ≥ 0, the fractional heat factor is at most exp(τ) times the Gaussian with exponent −4π²τ times the squared frequency norm. (`Breakdown.Periodic.FracHeatCompareInverse.Internal.fracHeatFactor_le_exp_sq`)

**The fractional heat factor is bounded.** The whole space fractional heat factor is at most one for every α, time, and frequency. (`Breakdown.Periodic.FracHeatCompareInverse.Internal.fracHeatFactor_le_one`)

**Continuity in the frequency variable.** For α > 0, the fractional heat factor is continuous as a function of frequency at every fixed time. (`Breakdown.Periodic.FracHeatCompareInverse.Internal.continuous_fracHeatFactor`)

**Bound the projected source density.** For α ≥ 1 and τ ≥ 0, the heated solenoidal Fourier transform of a source field is bounded by the displayed Gaussian times twice exp(τ) times its L¹ integral. (`Breakdown.Periodic.FracHeatCompareInverse.Internal.norm_source_le`)

**Bound the source gradient density.** For α ≥ 1 and τ > 0, each differentiated heated solenoidal source density is bounded by the displayed Gaussian times its L¹ integral and the stated time dependent factor. (`Breakdown.Periodic.FracHeatCompareInverse.Internal.norm_gradSource_le`)

**Realize heat by pointwise multiplication.** For α > 0, the fractional L² heat operator is realized by the identity frequency map and multiplication by its scalar heat factor. (`Breakdown.Periodic.FracHeatCompareInverse.Internal.fracHeat_realized`)

**Read L² heat almost everywhere.** For α > 0, the fractional L² heat operator agrees almost everywhere with multiplication by its scalar heat factor. (`Breakdown.Periodic.FracHeatCompareInverse.Internal.fracHeat_ae`)

**Heated Schwartz fields belong to Lᵖ.** For α > 0, multiplying a Schwartz field by the fractional heat factor gives an Lᵖ field for every exponent p and every time. (`Breakdown.Periodic.FracHeatCompareInverse.Internal.memLp_fracHeat`)

**Write the inverse heat transform.** The inverse Fourier transform of a heat multiplied Schwartz field equals its stated Fourier phase integral at every spatial point. (`Breakdown.Periodic.FracHeatCompareInverse.Internal.inverseTransform_fracHeat`)

**Recover the physical heated field.** For α > 0, an L² field agreeing almost everywhere with a heated Schwartz field has physical realization equal almost everywhere to the real part of the stated inverse Fourier integral. (`Breakdown.Periodic.FracHeatCompareInverse.Internal.toPhys_fracHeat`)

**Supply the whole space value formula.** For α > 1, the solenoidal heat factorization hypothesis identifies the physical velocity and each spatial derivative of the positive time solenoidal heat of a compactly supported real L² source almost everywhere with the real part of the corresponding value or gradient Fourier density integral. (`Breakdown.Periodic.fracR3ValueFormula_of`)

**Supply the whole space free formula.** For α > 1, the heat semigroup hypothesis identifies the velocity and each spatial derivative of the fractional heat of an embedded test field almost everywhere with the real part of its free value or gradient Fourier density integral at every nonnegative time. (`Breakdown.Periodic.fracR3FreeFormula`)

### Breakdown.Frac.TorusHeatCompareProj

This file identifies the solenoidal fractional heat operator with its projected Fourier multiplier, supporting the whole space comparison formulas.

**The whole space heat factor is even.** The fractional heat factor has the same value at a frequency and its negative. (`Breakdown.Periodic.FracSolenoidalProjection.Internal.fracHeat_neg`)

**The source heat factor is even.** The source heat factor has the same value at a frequency and its negative. (`Breakdown.Periodic.FracSolenoidalProjection.Internal.fracPhi_neg`)

**Bound the heat multiplier operator.** The scalar fractional heat factor times the identity has operator norm at most one at every frequency. (`Breakdown.Periodic.FracSolenoidalProjection.Internal.norm_fracHeat_smul_le`)

**Bound a radius by its higher power.** For α > 1 and r ≥ 0, r is at most one plus r raised to 2α. (`Breakdown.Periodic.FracSolenoidalProjection.Internal.base_le`)

**Bound the source multiplier operator.** For α > 1 and τ > 0, the scalar source heat factor times the identity has operator norm at most 1 + 1/τ. (`Breakdown.Periodic.FracSolenoidalProjection.Internal.norm_fracPhi_smul_le`)

**Read a realized heat field operator.** Under the field operator realization interface, the field operator for the fractional heat factor agrees almost everywhere with pointwise multiplication by that factor. (`Breakdown.Periodic.FracSolenoidalProjection.Internal.fracHeat_ae`)

**Read a realized source field operator.** For α > 1 and τ > 0, the field operator realization interface identifies the source multiplier operator almost everywhere with pointwise multiplication by its factor. (`Breakdown.Periodic.FracSolenoidalProjection.Internal.fracPhi_ae`)

**Supply solenoidal heat factorization.** For α > 1 and a compactly supported real L² source, its solenoidal heat at positive time is obtained by multiplying an X state's Fourier representative by 2π times the frequency norm, where that representative is almost everywhere the scalar heat factor times the Leray projection of the source transform. (`Breakdown.Periodic.fracHeatSolenoidalFactor`)

### Breakdown.Frac.TorusHeatCompareTorus

This file rewrites normalized torus heat and source Fourier series as lattice sums of whole space densities at the similarity rescaled frequencies.

**Similarity scales are positive.** A positive scale parameter has a positive similarity scale. (`Breakdown.Periodic.FracTorusShellSeries.Internal.simScale_pos`)

**Recover time from the similarity length.** For α > 0 and μ > 0, the similarity length raised to 2α equals μ. (`Breakdown.Periodic.FracTorusShellSeries.Internal.sqrt_simScale_rpow`)

**Cancel source normalization powers.** For α > 0 and μ > 0, the similarity scale raised to one quarter times μ raised to −1/(4α) equals one. (`Breakdown.Periodic.FracTorusShellSeries.Internal.simScale_quarter`)

**Identify rescaled lattice heat factors.** For α > 0 and μ > 0, the torus lattice heat factor at μt equals the whole space heat factor at t evaluated at the similarity rescaled frequency. (`Breakdown.Periodic.FracTorusShellSeries.Internal.fracFactor_eq`)

**The lattice heat factor is nonnegative.** The fractional lattice heat factor is nonnegative for every α, time, and lattice index. (`Breakdown.Periodic.FracTorusShellSeries.Internal.fracLatticeFactor_nonneg`)

**Nonzero lattice frequencies are large.** Every nonzero lattice index has frequency norm at least one. (`Breakdown.Periodic.FracTorusShellSeries.Internal.one_le_norm_freq`)

**Bound fractional lattice heat.** For α ≥ 1, the fractional lattice heat factor is at most the ordinary lattice heat factor at the same time and frequency. (`Breakdown.Periodic.FracTorusShellSeries.Internal.fracLatticeFactor_le_heat`)

**Read a rescaled source coefficient.** Under the force algebra and source existence interfaces and positive μ and τ, a rescaled source coefficient is its heated solenoidal Fourier coefficient in similarity coordinates. (`Breakdown.Periodic.FracTorusShellSeries.Internal.coeff_fracSourceOp`)

**Express a source term as a density.** For α > 0, positive μ and τ, and a compactly supported source fitting the stated shell, the source coefficient, force, and existence interfaces identify each phase weighted normalized coefficient with the source density at the rescaled lattice frequency times the lattice cell volume. (`Breakdown.Periodic.FracTorusShellSeries.Internal.source_value`)

**Bound normalized source coefficients.** For α ≥ 1 and positive μ and τ, the force algebra and source existence interfaces bound normalized source coefficients by the displayed L¹ cell integral factor times the ordinary heat factor at μτ. (`Breakdown.Periodic.FracTorusShellSeries.Internal.norm_coeff_source_le`)

**Express a free heat term as a density.** For α > 0, a positive admissible similarity scale, and a supported test field, the heat, transplantation coefficient, derivative, and smoothness interfaces identify each normalized free heat Fourier term with its density at the rescaled lattice frequency times the lattice cell volume. (`Breakdown.Periodic.FracTorusShellSeries.Internal.free_value`)

**Supply the torus source series.** For α > 1, the pointwise torus series, source coefficient, force algebra, and source existence hypotheses identify normalized torus source velocity and gradient series almost everywhere on the observation ball with lattice sums of their whole space densities, for positive time and 0 < μ ≤ 1 with the stated observation shell and source support fitting conditions. (`Breakdown.Periodic.fracTorusSourceSeries_of`)

**Supply the torus free heat series.** For α > 1, the pointwise torus series, transplantation coefficient, derivative, transplantation smoothness, step integral, heat algebra, and free density hypotheses identify normalized torus heat velocity and gradient series of a transplanted test field almost everywhere on the observation ball with lattice sums of its free densities, for nonnegative time and a scale 0 < μ ≤ 1 admissible for both support and observation shells. (`Breakdown.Periodic.fracTorusFreeSeries_of`)

### Breakdown.Frac.TorusHeatSolenoidalCont

This file proves positive time continuity of the whole space solenoidal fractional heat operator through its L² multiplier realization.

**Define the L² source multiplier.** This defines the continuous linear L² field operator given by the source heat factor times the identity at each frequency. (`Breakdown.Periodic.FracHeatProjCont.Internal.fracPhiOp`)

**The source heat factor is nonnegative.** The source heat factor is nonnegative for every α, time, and frequency. (`Breakdown.Periodic.FracHeatProjCont.Internal.factor_nonneg`)

**Bound the source heat factor.** For α > 1 and τ > 0, the source heat factor is at most 1 + τ inverse. (`Breakdown.Periodic.FracHeatProjCont.Internal.factor_le`)

**Bound the absolute source heat factor.** For α > 1 and τ > 0, the absolute value of the source heat factor is at most 1 + τ inverse. (`Breakdown.Periodic.FracHeatProjCont.Internal.abs_factor_le`)

**Continuity of the source factor in space.** For α > 1, the source heat factor is continuous in frequency at every fixed time. (`Breakdown.Periodic.FracHeatProjCont.Internal.continuous_factor`)

**Continuity of the source factor in time.** For fixed α and frequency, the source heat factor is continuous in time. (`Breakdown.Periodic.FracHeatProjCont.Internal.continuous_factor_time`)

**Read the L² source multiplier.** For α > 1 and τ > 0, the L² source multiplier agrees almost everywhere with pointwise multiplication by the source heat factor. (`Breakdown.Periodic.FracHeatProjCont.Internal.fracPhiOp_ae`)

**Bound nearby source factor differences.** For α > 1, τ₀ > 0, and τ > τ₀/2, the squared difference of source heat factors at τ and τ₀ is bounded by the square of 2 times (1 + 2/τ₀). (`Breakdown.Periodic.FracHeatProjCont.Internal.sub_sq_factor_le`)

**Continuity of the L² source action.** For α > 1 and a fixed L² field, the source multiplier applied to that field is continuous at positive times. (`Breakdown.Periodic.FracHeatProjCont.Internal.fracPhiOp_continuousOn`)

**Supply solenoidal heat continuity.** For α > 1 and every fixed real L² source, its whole space solenoidal fractional heat state is continuous at positive times. (`Breakdown.Periodic.fracHeatSolenoidalContinuous`)

### Breakdown.Frac.TorusKernel

This file constructs the fractional torus nonlinear kernel by adding a bounded damping multiplier to the ordinary kernel and proves its Fourier algebra.

**Negation reverses lattice frequency.** The frequency of a negated lattice index is the negative of its original frequency. (`_private.Breakdown.Frac.TorusKernel.0.Breakdown.Periodic.FracKernelInternal.freq_neg'`)

**Scale the divergence pairing over ℂ.** Multiplying a coefficient by a complex scalar multiplies its divergence pairing by that scalar. (`_private.Breakdown.Frac.TorusKernel.0.Breakdown.Periodic.FracKernelInternal.divPairing_csmul'`)

**Scale the divergence pairing over ℝ.** Multiplying a coefficient by a real scalar multiplies its divergence pairing by that scalar viewed as a complex number. (`_private.Breakdown.Frac.TorusKernel.0.Breakdown.Periodic.FracKernelInternal.divPairing_smul'`)

**Characterize admissible field sequences.** A sequence belongs to the field subspace exactly when opposite coefficients are complex conjugates and every coefficient has zero divergence pairing. (`_private.Breakdown.Frac.TorusKernel.0.Breakdown.Periodic.FracKernelInternal.mem_fieldSpace'`)

**Nonzero lattice frequencies are large.** Every nonzero lattice index has frequency norm at least one. (`_private.Breakdown.Frac.TorusKernel.0.Breakdown.Periodic.FracKernelInternal.one_le_norm_freq`)

**Compare the lattice dissipation powers.** For α ≥ 1, the ordinary quadratic lattice dissipation symbol is at most the fractional symbol with exponent 2α. (`_private.Breakdown.Frac.TorusKernel.0.Breakdown.Periodic.FracKernelInternal.sq_le_rpow`)

**Define the extra heat damping factor.** This defines the exponential factor for the difference between fractional and ordinary lattice dissipation, using time clamped at zero. (`_private.Breakdown.Frac.TorusKernel.0.Breakdown.Periodic.FracKernelInternal.ratio`)

**Bound the extra heat damping factor.** For α ≥ 1, the absolute value of the extra heat damping factor is at most one at every time and lattice index. (`_private.Breakdown.Frac.TorusKernel.0.Breakdown.Periodic.FracKernelInternal.abs_ratio_le`)

**The extra heat damping factor is even.** The extra heat damping factor has the same value at a lattice index and its negative. (`_private.Breakdown.Frac.TorusKernel.0.Breakdown.Periodic.FracKernelInternal.ratio_neg`)

**Factor fractional lattice heat.** The fractional lattice heat factor is the product of the extra damping factor and the ordinary lattice heat factor. (`_private.Breakdown.Frac.TorusKernel.0.Breakdown.Periodic.FracKernelInternal.factor_eq`)

**Combine nonnegative heat times.** For nonnegative s and τ, the product of fractional lattice heat factors at those times equals the factor at s + τ. (`_private.Breakdown.Frac.TorusKernel.0.Breakdown.Periodic.FracKernelInternal.factor_add`)

**Extra damping preserves field sequences.** For α ≥ 1, multiplying a torus state sequence by the extra heat damping factor preserves membership in the field subspace. (`_private.Breakdown.Frac.TorusKernel.0.Breakdown.Periodic.FracKernelInternal.ratio_mem`)

**Build the extra damping operator.** For α ≥ 1, this defines the continuous linear operator on torus states obtained by multiplying their sequences by the bounded extra heat damping factor. (`_private.Breakdown.Frac.TorusKernel.0.Breakdown.Periodic.FracKernelInternal.mult`)

**Read an extra damping coefficient.** For α ≥ 1, each coefficient after applying the extra damping operator is the original coefficient multiplied by its extra damping factor. (`_private.Breakdown.Frac.TorusKernel.0.Breakdown.Periodic.FracKernelInternal.coeff_mult`)

**The kernel vanishes at nonpositive time.** At nonpositive time, every Fourier coefficient of the ordinary torus kernel applied to two states is zero. (`_private.Breakdown.Frac.TorusKernel.0.Breakdown.Periodic.FracKernelInternal.coeff_kernel_nonpos`)

**Supply fractional torus kernel existence.** For α ≥ 1, a fractional torus kernel satisfying its Fourier coefficient specification exists. (`Breakdown.Periodic.fracTorusKernelExists`)

**Read a fractional kernel coefficient.** For α ≥ 1, every coefficient of the fractional torus kernel equals its defining fractional kernel coefficient. (`_private.Breakdown.Frac.TorusKernel.0.Breakdown.Periodic.FracKernelInternal.coeff_fracKernel`)

**Supply the torus kernel algebra.** For α ≥ 1, the torus heat algebra hypothesis gives the fractional kernel its prescribed Fourier coefficients, symmetry in its two inputs, continuity at positive times, and the identity that heat evolution for s ≥ 0 after kernel time τ > 0 equals the kernel at s + τ. (`Breakdown.Periodic.fracTorusKernelAlgebra`)

### Breakdown.Frac.TorusKernelBound

This file proves the fractional torus kernel bound from weighted Fourier estimates, supplying the short-time estimate used in the periodic mild equation.

**Positive fractional heat factor.** The fractional heat factor is positive at every lattice frequency. (`Breakdown.Periodic.FracInternal.KernelSharp.factor_pos`)

**Heat factor bounded by one.** The fractional heat factor is at most one. (`Breakdown.Periodic.FracInternal.KernelSharp.factor_le_one`)

**A power dominates its argument.** For nonnegative y and exponent at least one, y is at most 1 plus y to that exponent. (`Breakdown.Periodic.FracInternal.KernelSharp.le_one_add_rpow`)

**Scale the quadratic frequency weight.** For α at least one and nonnegative time and frequency, the scaled square is bounded by 1 plus the fractional frequency power times time. (`Breakdown.Periodic.FracInternal.KernelSharp.sq_mul_rpow_le`)

**Heat factor at nonnegative time.** At nonnegative time the fractional heat factor equals the exponential of minus time times the fractional frequency power. (`Breakdown.Periodic.FracInternal.KernelSharp.factor_eq`)

**Fourier energy weight.** The Fourier weight is 1 plus the square of the frequency length multiplied by 2π. (`Breakdown.Periodic.FracInternal.KernelSharp.weight_eq`)

**Scaled weighted heat bound.** For α at least one and time in (0, 1], time to the power 1/α times the weighted heat factor is at most 2. (`Breakdown.Periodic.FracInternal.KernelSharp.scaled_weight_factor_le`)

**Weighted heat bound.** For α at least one and time in (0, 1], the weighted heat factor is at most 2 times time to the power −1/α. (`Breakdown.Periodic.FracInternal.KernelSharp.weight_factor_le`)

**Compare fractional and ordinary heat.** At positive time and α at least one, the fractional heat factor is bounded by e times the ordinary heat factor at time to the power 1/α. (`Breakdown.Periodic.FracInternal.KernelSharp.factor_le_heat`)

**Summable fractional heat factors.** At positive time and α at least one, the fractional heat factors are summable over the lattice. (`Breakdown.Periodic.FracInternal.KernelSharp.summable_factor`)

**Weighted Fourier test.** The Fourier test multiplies each coefficient by minus one half of the weighted fractional heat factor. (`Breakdown.Periodic.FracInternal.KernelSharp.fracTest`)

**Norm of the weighted test.** The test coefficient norm is one half of the weighted heat factor times the original coefficient norm. (`Breakdown.Periodic.FracInternal.KernelSharp.norm_fracTest`)

**Summable weighted test.** A uniform weighted heat bound and finite weighted coefficient energy give a summable sequence of test norms. (`Breakdown.Periodic.FracInternal.KernelSharp.summable_norm_fracTest`)

**Test square from coefficient energy.** A uniform weighted heat bound controls the test norm squared by that bound times the weighted coefficient energy. (`Breakdown.Periodic.FracInternal.KernelSharp.fracTest_sq_le`)

**Weighted square of the test.** A uniform weighted heat bound controls the weighted test norm squared by the square of that bound times the original energy. (`Breakdown.Periodic.FracInternal.KernelSharp.weight_fracTest_sq_le`)

**Combine quarter-power estimates.** The product of the two nonnegative quarter-power energy factors equals A to the power 3/4 times N. (`Breakdown.Periodic.FracInternal.KernelSharp.rpow_combine_gen`)

**Diagonal kernel estimate.** The assumed trilinear Fourier estimate bounds the diagonal fractional torus kernel by the stated short-time constant times the squared input norm. (`Breakdown.Periodic.FracInternal.KernelSharp.norm_kernel_diag_le`)

**Simplify the fractional time power.** For positive α and time, the three-quarter power of the weighted heat constant is at most twice time to the power −3/(4α). (`Breakdown.Periodic.FracInternal.KernelSharp.rpow_constant_le`)

**Sharp fractional torus kernel bound.** For α greater than one, the torus kernel algebra yields the sharp fractional torus kernel bound. (`Breakdown.Periodic.fracTorusKernelSharpBound_of`)

### Breakdown.Frac.TorusMildForm

This file converts smooth periodic fractional solutions into the torus mild equation by solving each Fourier-mode evolution equation.

**Continuity of fractional heat.** The fractional heat algebra gives continuous dependence of the heat evolution on time and initial data. (`Breakdown.Periodic.Internal.FracMild.fracHeat_tendsto`)

**Kernel as later heat evolution.** At positive starting time, the fractional kernel at a later time is the heat evolution of the earlier kernel. (`Breakdown.Periodic.Internal.FracMild.fracKernel_eq_heat`)

**Continuity of the fractional kernel.** The heat and kernel algebra give joint continuity of the fractional kernel at positive times. (`Breakdown.Periodic.Internal.FracMild.fracKernel_tendsto`)

**Kernel norm decreases with time.** The fractional kernel operator norm cannot increase between two positive ordered times. (`Breakdown.Periodic.Internal.FracMild.fracKernel_opNorm_anti`)

**Global fractional kernel bound.** The heat algebra and sharp short-time bound control the kernel by a constant times 1 plus time to the power −3/(4α), times the two input norms. (`Breakdown.Periodic.Internal.FracMild.fracKernel_norm_le`)

**Integrable mild nonlinear term.** For α greater than one, a continuous torus curve has an interval-integrable nonlinear kernel term on every nonnegative compact time interval. (`Breakdown.Periodic.Internal.FracMild.fracIntegrable_kernel`)

**Solenoidal fractional solution.** A fractional solution has zero divergence at every nonnegative time. (`Breakdown.Periodic.Internal.FracMild.fracDivergence_nonneg`)

**Fourier coefficient of a negative.** Negating a field negates each of its Fourier coefficients. (`Breakdown.Periodic.Internal.FracMild.coefField_neg`)

**Continuous time derivative slice.** A jointly smooth field on nonnegative times has a spatially continuous time derivative at each positive time. (`Breakdown.Periodic.Internal.FracMild.continuous_timeDeriv`)

**Fractional Fourier-mode equation.** The coefficient identities turn a smooth periodic fractional solution into the stated dissipative Fourier-mode differential equation. (`Breakdown.Periodic.Internal.FracMild.fracMode_deriv`)

**Integrated Fourier-mode equation.** The coefficient identities and continuity give the Fourier-mode variation-of-constants formula from time zero. (`Breakdown.Periodic.Internal.FracMild.fracMode_identity`)

**Smooth torus solutions are mild.** For 1 < α < 5/4, the heat, kernel and coefficient identities imply that smooth periodic fractional solutions satisfy the torus mild equation. (`Breakdown.Periodic.fracTorusSmoothIsMild_of`)

### Breakdown.Frac.TorusOpDiff

This file supplies the operator-difference estimate needed to compare fractional space and torus evolution steps.

**Fractional operator differences.** For α greater than one, the sequence-operator and piece-operator specifications imply the fractional operator-difference bounds. (`Breakdown.Periodic.fracOpDiffBounds`)

### Breakdown.Frac.TorusOpNorm

This file assembles bounds on the fractional comparison operators from the space and torus shell estimates.

**Compare the short-time exponents.** For α greater than one and time in (0, 1], time to the power −3/(4α) is at most time to the power −3/4. (`Breakdown.Periodic.TorusOpNorm.Internal.rpow_exponent_le`)

**Compare weighted time bounds.** Multiplying the short-time exponent comparison by nonnegative constants preserves the inequality. (`Breakdown.Periodic.TorusOpNorm.Internal.bound_exponent_le`)

**Space shell map preserves sums.** The space shell map sends a finite real linear combination of test fields to the same combination of their images. (`Breakdown.Periodic.TorusOpNorm.Internal.fracLambdaR3_sum`)

**Torus shell map preserves sums.** The torus shell map sends a finite real linear combination of test fields to the same combination of their images. (`Breakdown.Periodic.TorusOpNorm.Internal.fracLambdaTorus_sum`)

**Shell scales along similarity steps.** The initial scale restrictions ensure that every similarity step remains an admissible shell scale. (`Breakdown.Periodic.TorusOpNorm.Internal.isShellScale_simStep`)

**Norm of the scaled dilation.** At positive scale, the scaled mild framework bounds its dilation operator norm by the scale to the framework exponent. (`Breakdown.Periodic.TorusOpNorm.Internal.norm_scaledDil_le`)

**Norm of a shifted space step.** The framework bounds the rescaled free-step and endpoint composition by its exponential scale factor divided by the positive normalization. (`Breakdown.Periodic.TorusOpNorm.Internal.norm_fracR3Shift_entry`)

**Fractional comparison operator bounds.** The shell, restriction, embedding, heat and source bounds combine into the fractional comparison operator norm bounds for α greater than one. (`Breakdown.Periodic.fracOperatorNormBounds`)

### Breakdown.Frac.TorusPeriodizationTail

This file bounds the nonlocal fractional error created by periodizing a field supported near the centre of the unit cell.

**A coordinate is bounded by the norm.** The absolute value of each spatial coordinate is at most the vector norm. (`_private.Breakdown.Frac.TorusPeriodizationTail.0.Breakdown.Periodic.tail_coord_le`)

**Coordinates of the cell centre.** Every coordinate of the cell centre equals one half. (`_private.Breakdown.Frac.TorusPeriodizationTail.0.Breakdown.Periodic.tail_center_apply`)

**Lattice frequency coordinates.** Each coordinate of a lattice frequency is the corresponding integer viewed as a real number. (`_private.Breakdown.Frac.TorusPeriodizationTail.0.Breakdown.Periodic.tail_freq_apply`)

**Zero lattice frequency.** The frequency vector of the zero lattice index is zero. (`_private.Breakdown.Frac.TorusPeriodizationTail.0.Breakdown.Periodic.tail_freq_zero`)

**Lattice points are separated.** Two lattice frequencies less than one unit apart have the same lattice index. (`_private.Breakdown.Frac.TorusPeriodizationTail.0.Breakdown.Periodic.tail_lattice_eq`)

**Central support radius.** The support hypothesis places every nonzero field value within distance 1/8 of the cell centre. (`_private.Breakdown.Frac.TorusPeriodizationTail.0.Breakdown.Periodic.tail_supp`)

**Unique nearby nonzero translate.** Two points less than 3/4 apart can have nonzero supported translates only for the same lattice index. (`_private.Breakdown.Frac.TorusPeriodizationTail.0.Breakdown.Periodic.tail_unique`)

**One translate on a small ball.** On a ball of radius 1/4, at most one lattice translate of the centrally supported field can be nonzero. (`_private.Breakdown.Frac.TorusPeriodizationTail.0.Breakdown.Periodic.tail_local`)

**Smooth periodization.** Periodizing a smooth field supported within the stated central radius preserves smoothness. (`_private.Breakdown.Frac.TorusPeriodizationTail.0.Breakdown.Periodic.tail_contDiff`)

**Describe the periodization tail.** The periodization error is either zero or exactly one nonzero translate with a nonzero lattice index. (`_private.Breakdown.Frac.TorusPeriodizationTail.0.Breakdown.Periodic.tail_cases`)

**Distance across the unit cell.** Every point in the chosen unit cell lies within distance one of its centre. (`_private.Breakdown.Frac.TorusPeriodizationTail.0.Breakdown.Periodic.tail_cell_norm`)

**Distance to a nonzero translate.** A nonzero supported translate from the unit cell forces the displacement to exceed both 3/8 and the stated lattice-dependent radius. (`_private.Breakdown.Frac.TorusPeriodizationTail.0.Breakdown.Periodic.tail_geom`)

**Summable fractional translation tail.** For α greater than one, the translated radial tail with exponent −(3 + 2α) is summable over the lattice. (`_private.Breakdown.Frac.TorusPeriodizationTail.0.Breakdown.Periodic.tail_summable`)

**Fractional periodization tail bound.** For 1 < α < 3/2, additivity, remainder integrability and normalization yield the fractional periodization tail estimate. (`Breakdown.Periodic.fracPeriodizationTail_of`)

### Breakdown.Frac.TorusPlaneWave

This file identifies the fractional operator on a plane wave by computing its derivatives and second-order remainder.

**Derivative of the linear phase.** The derivative of the phase inner product plus a constant is the corresponding inner-product linear map. (`_private.Breakdown.Frac.TorusPlaneWave.0.Breakdown.Periodic.TorusPlaneWave.phaseHasFDerivAt`)

**Derivative of the cosine phase.** The derivative of the cosine phase is minus its sine times the phase derivative. (`_private.Breakdown.Frac.TorusPlaneWave.0.Breakdown.Periodic.TorusPlaneWave.cosHasFDerivAt`)

**Derivative of the sine phase.** The derivative of the sine phase is its cosine times the phase derivative. (`_private.Breakdown.Frac.TorusPlaneWave.0.Breakdown.Periodic.TorusPlaneWave.sinHasFDerivAt`)

**First derivative of a plane wave.** The derivative of a cosine plane wave is minus the sine phase times the frequency-to-amplitude linear map. (`_private.Breakdown.Frac.TorusPlaneWave.0.Breakdown.Periodic.TorusPlaneWave.waveFirst`)

**Plane-wave derivative as a function.** The derivative field of the cosine plane wave has the stated sine-phase formula. (`_private.Breakdown.Frac.TorusPlaneWave.0.Breakdown.Periodic.TorusPlaneWave.waveFderiv`)

**Second derivative of a plane wave.** Differentiating the first derivative gives the stated negative cosine-phase bilinear map. (`_private.Breakdown.Frac.TorusPlaneWave.0.Breakdown.Periodic.TorusPlaneWave.waveSecond`)

**Second directional plane-wave term.** The second derivative in two equal directions is minus the cosine phase times the squared frequency pairing and the amplitude. (`_private.Breakdown.Frac.TorusPlaneWave.0.Breakdown.Periodic.TorusPlaneWave.waveIterated`)

**Plane-wave second-order remainder.** The plane-wave remainder separates into the cosine remainder through quadratic order and the sine remainder through linear order. (`_private.Breakdown.Frac.TorusPlaneWave.0.Breakdown.Periodic.TorusPlaneWave.waveRemainder`)

**Fractional plane-wave eigenvalue.** For 1 < α < 3/2, the scalar symbol and normalization statements establish the plane-wave eigenvalue identity. (`Breakdown.Periodic.planeWaveEigen_of`)

### Breakdown.Frac.TorusPointwiseBound

This file derives a pointwise fractional-operator estimate by splitting the remainder integral into near and far radial regions.

**Three-dimensional radial constant.** The radial integration constant is three times the volume of the unit ball in space. (`_private.Breakdown.Frac.TorusPointwiseBound.0.Breakdown.FracInternal.radialConst`)

**Positive radial integration constant.** The radial integration constant is positive. (`_private.Breakdown.Frac.TorusPointwiseBound.0.Breakdown.FracInternal.radialConst_pos`)

**Radial integration formula.** Integrability of the radius-squared weighted scalar function gives the corresponding spatial integral and radial formula. (`_private.Breakdown.Frac.TorusPointwiseBound.0.Breakdown.FracInternal.radial_aux`)

**Integrate a radial power near zero.** For exponent greater than −3 and positive radius, the radial power is integrable inside the ball with the stated exact integral. (`_private.Breakdown.Frac.TorusPointwiseBound.0.Breakdown.FracInternal.near_radial`)

**Integrate a radial power at infinity.** For exponent less than −3 and positive radius, the radial power is integrable outside the ball with the stated exact integral. (`_private.Breakdown.Frac.TorusPointwiseBound.0.Breakdown.FracInternal.far_radial`)

**Bound the fractional far integral.** For the stated fractional exponent range and radius in (0, 1], the exterior radial integral is bounded by the specified inverse-radius power. (`_private.Breakdown.Frac.TorusPointwiseBound.0.Breakdown.FracInternal.far_le`)

**Bound the distant Taylor remainder.** Bounds on the value and first two derivatives control the second-order remainder by the translated value plus the stated quadratic polynomial in displacement. (`_private.Breakdown.Frac.TorusPointwiseBound.0.Breakdown.FracInternal.remainder_far_le`)

**Pointwise fractional operator bound.** For 1 < α < 3/2, the remainder estimate and normalizer give the pointwise fractional operator bound. (`Breakdown.Periodic.fracPointwiseBound_of`)

### Breakdown.Frac.TorusResidual

This file combines core, shell and outer residual estimates, then transfers the resulting bound to the periodized approximate solution.

**Frequency preserves lattice addition.** The frequency map carries addition of lattice indices to vector addition. (`Breakdown.Periodic.FracResidualCombine.Internal.freq_add'`)

**Coordinates of a lattice frequency.** A lattice frequency has the integer coordinates of its index, viewed in the reals. (`Breakdown.Periodic.FracResidualCombine.Internal.freq_apply'`)

**Cell centre coordinates.** Each coordinate of the centre of the periodic cell equals one half. (`Breakdown.Periodic.FracResidualCombine.Internal.center_apply'`)

**Periodization is periodic.** Translating a periodized field by any lattice frequency leaves its value unchanged. (`Breakdown.Periodic.FracResidualCombine.Internal.latticePeriodize_add`)

**Derivatives preserve a period.** The derivative of a field invariant under a fixed translation has the same translation invariance. (`Breakdown.Periodic.FracResidualCombine.Internal.fderiv_periodic`)

**All derivatives preserve a period.** Every iterated derivative of a periodic field has the same period. (`Breakdown.Periodic.FracResidualCombine.Internal.iteratedFDeriv_periodic`)

**Fractional power preserves a period.** The fractional operator preserves a field's translation period. (`Breakdown.Periodic.FracResidualCombine.Internal.fractionalPowerAt_periodic`)

**Advection preserves a period.** The advection term of a periodic field has the same period. (`Breakdown.Periodic.FracResidualCombine.Internal.advectionAt_periodic`)

**Pressure gradient preserves a period.** The gradient of a periodic scalar field has the same period. (`Breakdown.Periodic.FracResidualCombine.Internal.gradientAt_periodic`)

**Periodic approximate residual.** The fractional approximate residual is invariant under every lattice translation. (`Breakdown.Periodic.FracResidualCombine.Internal.residual_periodic`)

**Represent a point in the unit cell.** Every spatial point is a point of the unit cell plus a lattice frequency. (`Breakdown.Periodic.FracResidualCombine.Internal.cell_decomp`)

**Other translates lie outside the core.** Near a point of the unit cell, every nonzero lattice translate lies beyond the stated central radius. (`Breakdown.Periodic.FracResidualCombine.Internal.far_of_ne`)

**Periodization agrees locally.** A field vanishing outside the central support radius agrees locally with its periodization at each point of the unit cell. (`Breakdown.Periodic.FracResidualCombine.Internal.periodize_local`)

**Pointwise self-similar decay.** The stated profile decay bounds imply the inverse-power velocity bound away from the cell centre for α greater than one. (`Breakdown.Periodic.FracResidualCombine.Internal.self_similar_point`)

**Pointwise homotopy potential bound.** A field with radial decay exponent below two gives the stated one-power-improved homotopy-potential estimate away from the centre. (`Breakdown.Periodic.FracResidualCombine.Internal.potential_point`)

**Pointwise cutoff-field bound.** The field decay and cutoff-gradient bounds control the cutoff field by the field term plus the stated potential term. (`Breakdown.Periodic.FracResidualCombine.Internal.field_point`)

**Uniform approximate-field mass.** For 1 < α < 5/4, the approximate-field and decay hypotheses give a uniform bound on its spatial integral norm before blow-up. (`Breakdown.Periodic.FracResidualCombine.Internal.mass_bound`)

**Join the three residual regions.** Bounds on the core, shell and outer regions combine into a bound for the residual on all of space. (`Breakdown.Periodic.fracSpaceResidualBound_of`)

**Bound the periodized residual.** For 1 < α < 5/4, the space residual and periodization tail estimates give the approximate periodic residual bound. (`Breakdown.Periodic.fracApproxResidualBound_of`)

### Breakdown.Frac.TorusResidualCore

This file controls the fractional residual in the core, where the approximate field agrees with the self-similar field.

**Third derivative outside the core.** This proposition requires a uniform third-derivative bound for the approximate field outside the inner core before blow-up. (`Breakdown.Periodic.FracApproxFieldThirdBound`)

**Finite orders are below infinity.** Every natural derivative order is bounded by the infinite smoothness index. (`Breakdown.Periodic.FracResidualCoreInternal.le_infty`)

**Smooth spatial slices.** A jointly smooth field before the terminal time has a smooth spatial slice at each earlier time. (`Breakdown.Periodic.FracResidualCoreInternal.slice`)

**Derivative of a constant on a ball.** A smooth function constant on a closed ball of positive radius has zero derivative throughout that closed ball. (`Breakdown.Periodic.FracResidualCoreInternal.fderiv_eq_zero_of_const`)

**Derivatives vanish in a zero ball.** Every iterated derivative vanishes at interior points of a closed ball on which the field is zero. (`Breakdown.Periodic.FracResidualCoreInternal.iteratedFDeriv_eq_zero_of_ball`)

**Derivatives vanish on a closed ball.** A smooth field zero on a closed ball of positive radius has all iterated derivatives zero throughout that closed ball. (`Breakdown.Periodic.FracResidualCoreInternal.iteratedFDeriv_eq_zero_closedBall`)

**Uniform decay away from the core.** For α greater than one and derivative order at most three, the stated distance lower bound gives a fixed upper bound on the decay factor. (`Breakdown.Periodic.FracResidualCoreInternal.power_le`)

**Bound the cutoff discrepancy.** Core agreement, exterior vanishing and the derivative-decay assumptions bound both the discrepancy and its third derivative uniformly. (`Breakdown.Periodic.FracResidualCoreInternal.difference_bound`)

**Core residual estimate.** For 1 < α < 5/4, the solution, decay, cutoff, fractional-operator and third-derivative hypotheses establish the core residual bound. (`Breakdown.Periodic.fracResidualCore_of`)

### Breakdown.Frac.TorusResidualOuter

This file controls the residual where the compact approximate field vanishes, leaving the nonlocal fractional contribution.

**Finite orders are below infinity.** Every natural derivative order is below the infinite smoothness index. (`Breakdown.Periodic.FracResidualOuterInternal.nat_le_infty`)

**Integrable exterior radial tail.** A radial power with exponent below −3 is integrable outside the ball of radius 1/64. (`Breakdown.Periodic.FracResidualOuterInternal.tail_integrable`)

**All derivatives vanish outside support.** A smooth field vanishing beyond the central support radius has every iterated derivative zero there, including at the boundary. (`Breakdown.Periodic.FracResidualOuterInternal.iteratedFDeriv_eq_zero_outer`)

**Outer residual estimate.** For 1 < α < 5/4, the decay, approximate-field and fractional remainder estimates give the outer-region residual bound. (`Breakdown.Periodic.fracResidualOuter_of`)

### Breakdown.Frac.TorusResidualOuterBound

This file proves the uniform bounds on the cutoff field and its third derivatives used by the core and exterior residual arguments.

**Finite orders are below infinity.** Every natural derivative order is below the infinite smoothness index. (`Breakdown.Periodic.FracOuterBoundInternal.nat_le_infty`)

**Integrate a power majorant.** An integrand bounded by K times s to an exponent above −1 has integral norm at most K divided by that exponent plus one. (`Breakdown.Periodic.FracOuterBoundInternal.integral_singular_le`)

**Derivative of a parameter integral.** The stated smoothness and integrable power bound control the derivative of the parameter integral by K divided by the exponent plus one. (`Breakdown.Periodic.FracOuterBoundInternal.integral_iter_le`)

**Bound low-order product terms.** For derivative order at most three, the bounded binomial product sum is at most eight times the product of the two bounds. (`Breakdown.Periodic.FracOuterBoundInternal.binom_sum_le3`)

**Derivatives of a translated identity.** Through order three, derivatives of the translated identity are bounded by the maximum of its displacement norm and one. (`Breakdown.Periodic.FracOuterBoundInternal.shift_norm_le`)

**Derivative bound under dilation.** Composing a smooth field with a nonnegative dilation multiplies the order-k derivative bound by the scale to the power k. (`Breakdown.Periodic.FracOuterBoundInternal.dilate_norm_le`)

**Smooth self-similar spatial field.** A smooth profile gives a smooth self-similar spatial field at every fixed pair of times. (`Breakdown.Periodic.FracOuterBoundInternal.selfSimilar_contDiff`)

**Bound derivatives of compact fields.** A smooth compactly supported field has a common nonnegative bound for all derivatives through order three. (`Breakdown.Periodic.FracOuterBoundInternal.bounded_upto3`)

**Compact support of the cutoff gradient.** The gradient of the central cutoff has compact support. (`Breakdown.Periodic.FracOuterBoundInternal.gradient_support`)

**Combine dilation and decay powers.** For positive scale and radius, the product of the dilation and radial powers has the stated simplified exponent. (`Breakdown.Periodic.FracOuterBoundInternal.rpow_combine`)

**Distance lower bound controls decay.** A positive lower bound on distance controls the inverse power of distance plus a nonnegative offset. (`Breakdown.Periodic.FracOuterBoundInternal.far_le`)

**One bound for the permitted powers.** Distances at least 1/16 and exponents between zero and five satisfy the stated fixed inverse-power bound. (`Breakdown.Periodic.FracOuterBoundInternal.const_le`)

**Potential derivatives on the shell.** For 1 < α < 5/4, self-similar decay bounds the first three potential derivatives uniformly on the shell from radius 1/16 to 1/8. (`Breakdown.Periodic.FracOuterBoundInternal.potential_bound`)

**Derivatives vanish in the exterior.** A smooth field zero beyond the central support radius has all iterated derivatives zero in that exterior region. (`Breakdown.Periodic.FracOuterBoundInternal.iteratedFDeriv_eq_zero_outer`)

**Uniform cutoff-field bounds.** For 1 < α < 5/4, the decay and approximate-field hypotheses give the stated velocity growth bound and uniform third-derivative bound outside the inner core. (`Breakdown.Periodic.fracApproxField_bounds`)

### Breakdown.Frac.TorusResidualShell

This file bounds each part of the approximate fractional equation on the transition shell where the cutoff varies.

**Self-similar profile decay bounds.** This proposition records the common decay bound for spatial derivatives through order three, the time derivative and the pressure gradient. (`Breakdown.Periodic.ResidualShell.Internal.ProfileDecay`)

**Finite orders are below infinity.** Every natural derivative order lies below the infinite smoothness index. (`_private.Breakdown.Frac.TorusResidualShell.0.Breakdown.Periodic.ResidualShell.Internal.nat_le_infty`)

**Unit coordinate vectors.** Each standard spatial coordinate vector has norm one. (`_private.Breakdown.Frac.TorusResidualShell.0.Breakdown.Periodic.ResidualShell.Internal.norm_unitVector`)

**Gradient bounded by derivative norm.** The spatial gradient norm is at most three times the derivative operator norm. (`_private.Breakdown.Frac.TorusResidualShell.0.Breakdown.Periodic.ResidualShell.Internal.norm_gradientAt_le`)

**Derivative bounded by gradient norm.** The derivative operator norm of a scalar field is at most its gradient norm. (`_private.Breakdown.Frac.TorusResidualShell.0.Breakdown.Periodic.ResidualShell.Internal.fderiv_norm_le_gradient`)

**Smooth slices before the terminal time.** Joint smoothness before the terminal time gives smoothness of each earlier spatial slice. (`_private.Breakdown.Frac.TorusResidualShell.0.Breakdown.Periodic.ResidualShell.Internal.slice_of_contDiffOn`)

**Bound a compact field derivative.** Each iterated derivative of a smooth compactly supported field has a global nonnegative norm bound. (`_private.Breakdown.Frac.TorusResidualShell.0.Breakdown.Periodic.ResidualShell.Internal.bounded_iteratedFDeriv`)

**Bound finitely many derivatives.** A smooth compactly supported field has a common bound for all derivative orders up to any fixed natural number. (`_private.Breakdown.Frac.TorusResidualShell.0.Breakdown.Periodic.ResidualShell.Internal.bounded_upto`)

**Smooth central cutoff.** The central cutoff is smooth. (`_private.Breakdown.Frac.TorusResidualShell.0.Breakdown.Periodic.ResidualShell.Internal.centralCut_contDiff`)

**Compactly supported central cutoff.** The central cutoff has compact support. (`_private.Breakdown.Frac.TorusResidualShell.0.Breakdown.Periodic.ResidualShell.Internal.centralCut_support`)

**Smooth gradient of a smooth scalar.** The gradient of a smooth scalar field is smooth. (`_private.Breakdown.Frac.TorusResidualShell.0.Breakdown.Periodic.ResidualShell.Internal.gradient_contDiff`)

**Gradient retains compact support.** The gradient of a compactly supported scalar field has compact support. (`_private.Breakdown.Frac.TorusResidualShell.0.Breakdown.Periodic.ResidualShell.Internal.gradient_support`)

**Cutoff norm at most one.** The norm of the central cutoff is at most one at every point. (`_private.Breakdown.Frac.TorusResidualShell.0.Breakdown.Periodic.ResidualShell.Internal.centralCut_norm_le`)

**Cutoff gradient vanishes in the core.** The gradient of the central cutoff is zero strictly inside the inner core. (`_private.Breakdown.Frac.TorusResidualShell.0.Breakdown.Periodic.ResidualShell.Internal.gradient_coreCut_zero`)

**Bound a binomial product sum.** Uniform bounds on the two nonnegative factor sequences bound the order-k product sum by 2 to the power k times their product. (`_private.Breakdown.Frac.TorusResidualShell.0.Breakdown.Periodic.ResidualShell.Internal.binom_sum_le`)

**Derivatives of translation.** Every derivative of the translated identity is bounded by the maximum of its displacement norm and one. (`_private.Breakdown.Frac.TorusResidualShell.0.Breakdown.Periodic.ResidualShell.Internal.shift_norm_le`)

**Dilation scales derivative bounds.** A nonnegative spatial dilation scales the order-k derivative bound by its kth power. (`_private.Breakdown.Frac.TorusResidualShell.0.Breakdown.Periodic.ResidualShell.Internal.dilate_norm_le`)

**Uniform bound for decay powers.** The stated positive distance and exponent bounds give a fixed upper bound on the inverse radial power. (`_private.Breakdown.Frac.TorusResidualShell.0.Breakdown.Periodic.ResidualShell.Internal.decay_le`)

**Choose a nonnegative decay constant.** The self-similar decay hypothesis provides a nonnegative constant satisfying the full profile decay proposition. (`_private.Breakdown.Frac.TorusResidualShell.0.Breakdown.Periodic.ResidualShell.Internal.decay_nonneg`)

**Derivative bounds away from centre.** The profile decay bounds control all derivatives through order three uniformly beyond radius 1/64. (`_private.Breakdown.Frac.TorusResidualShell.0.Breakdown.Periodic.ResidualShell.Internal.field_region_bound`)

**Scaled profile derivative bound.** The profile decay bounds control the dilated derivatives by the stated constant times s to the power 2 − 2α. (`_private.Breakdown.Frac.TorusResidualShell.0.Breakdown.Periodic.ResidualShell.Internal.scaled_bound`)

**Bound derivatives under integration.** An interval-integrable majorant for the kth spatial derivative bounds the kth derivative of the parameter integral. (`_private.Breakdown.Frac.TorusResidualShell.0.Breakdown.Periodic.ResidualShell.Internal.norm_iteratedFDeriv_integral_le`)

**Potential derivative shell estimate.** For 1 < α < 3/2, the solution and decay hypotheses bound potential derivatives through order three by the stated integral majorant on the shell. (`_private.Breakdown.Frac.TorusResidualShell.0.Breakdown.Periodic.ResidualShell.Internal.potential_region_bound`)

**Nonnegative potential majorant.** The potential integral majorant is nonnegative when its decay constant is nonnegative. (`_private.Breakdown.Frac.TorusResidualShell.0.Breakdown.Periodic.ResidualShell.Internal.potential_integral_nonneg`)

**Uniform approximate-field derivatives.** For 1 < α < 3/2, the solution, decay and homotopy-curl hypotheses bound approximate-field derivatives through order three on the stated annulus. (`_private.Breakdown.Frac.TorusResidualShell.0.Breakdown.Periodic.ResidualShell.Internal.approx_region_bound`)

**Differentiate the homotopy potential.** The homotopy potential's time derivative is the integral of the time derivative of the self-similar field in the stated cross product. (`_private.Breakdown.Frac.TorusResidualShell.0.Breakdown.Periodic.ResidualShell.Internal.potential_time_deriv`)

**Integrate the shifted decay power.** For positive shift and radius and exponent above two, the shifted radial integral has the stated explicit bound. (`_private.Breakdown.Frac.TorusResidualShell.0.Breakdown.Periodic.ResidualShell.Internal.rpow_integral_bound`)

**Time derivative of the potential.** The solution and profile decay hypotheses bound the potential's time derivative outside radius 1/16 by the stated blow-up-time power. (`_private.Breakdown.Frac.TorusResidualShell.0.Breakdown.Periodic.ResidualShell.Internal.potential_time_bound`)

**Time derivative of the cutoff field.** The solution and decay hypotheses give a common bound for the cutoff-field time derivative outside radius 1/16 with the stated time exponent. (`_private.Breakdown.Frac.TorusResidualShell.0.Breakdown.Periodic.ResidualShell.Internal.time_term_bound`)

**Segments stay away from the centre.** For the stated endpoint lengths and nonnegative inner product, the joining segment stays at least 1/32 from the centre. (`_private.Breakdown.Frac.TorusResidualShell.0.Breakdown.Periodic.ResidualShell.Internal.segment_far`)

**Pressure difference along a segment.** A derivative bound away from the centre controls the pressure difference along the stated segment by its length times that bound. (`_private.Breakdown.Frac.TorusResidualShell.0.Breakdown.Periodic.ResidualShell.Internal.segment_difference`)

**Pressure relative to its anchor.** The derivative bound controls the pressure difference from the fixed anchor by K on the cutoff shell. (`_private.Breakdown.Frac.TorusResidualShell.0.Breakdown.Periodic.ResidualShell.Internal.pressure_difference`)

**Uniform cutoff-pressure gradient.** The solution and profile decay hypotheses uniformly bound the approximate pressure gradient on the transition shell. (`_private.Breakdown.Frac.TorusResidualShell.0.Breakdown.Periodic.ResidualShell.Internal.pressure_term_bound`)

**Integrable local radial majorant.** A power singularity of exponent less than three, plus a constant, is integrable on the ball of radius 1/8. (`_private.Breakdown.Frac.TorusResidualShell.0.Breakdown.Periodic.ResidualShell.Internal.majorant_integrable`)

**Control a weighted exterior integral.** An integrable majorant for the compactly supported field gives the stated bound for its translated inverse-power tail integral. (`_private.Breakdown.Frac.TorusResidualShell.0.Breakdown.Periodic.ResidualShell.Internal.far_integral`)

**Norm of four summed vectors.** The norm of the sum of four vectors is at most the sum of their norms. (`_private.Breakdown.Frac.TorusResidualShell.0.Breakdown.Periodic.ResidualShell.Internal.norm_four_add_le`)

**Majorant for the approximate field.** The profile, cutoff and decay hypotheses give the stated compactly supported radial majorant for the approximate field away from the centre. (`_private.Breakdown.Frac.TorusResidualShell.0.Breakdown.Periodic.ResidualShell.Internal.approx_majorant`)

**Uniform fractional term on the shell.** For 1 < α < 3/2, the stated solution, cutoff and remainder hypotheses uniformly bound the approximate field's fractional operator on the shell. (`_private.Breakdown.Frac.TorusResidualShell.0.Breakdown.Periodic.ResidualShell.Internal.frac_term_bound`)

**Shell residual estimate.** For 1 < α < 5/4, the solution, decay, cutoff, fractional bound and homotopy-curl hypotheses establish the transition-shell residual estimate. (`Breakdown.Periodic.fracResidualShell_of`)

### Breakdown.Frac.TorusSelfSimilar

This file checks the rotating fractional self-similar change of variables, including spatial operators, time differentiation and smoothness.

**Smooth axial rotation.** The axial rotation specification makes rotation jointly smooth in its angle and vector. (`Breakdown.Periodic.FracSelfSimilar.Internal.rot_contDiff`)

**Differentiate a rotating vector.** The derivative of a rotating vector is the angular-velocity term plus the rotation of its vector derivative. (`Breakdown.Periodic.FracSelfSimilar.Internal.rot_hasDerivAt`)

**Rotation commutes with axial turn.** Axial rotation and the infinitesimal axial turn commute. (`Breakdown.Periodic.FracSelfSimilar.Internal.turn_comm`)

**Derivative of a rescaled field.** The derivative of the translated, rotated and rescaled profile is the stated composition of linear maps. (`Breakdown.Periodic.FracSelfSimilar.Internal.hasFDerivAt_field`)

**Apply the rescaled-field derivative.** Applying that derivative to a vector gives amplitude times scale times the rotated profile derivative. (`Breakdown.Periodic.FracSelfSimilar.Internal.fderiv_field_apply`)

**Trace is invariant under isometries.** Conjugating a spatial linear map by a linear isometry preserves the sum of its coordinate diagonal entries. (`Breakdown.Periodic.FracSelfSimilar.Internal.sum_coord_conj`)

**Divergence under rotation and scale.** The transformed field's divergence is amplitude times spatial scale times the profile divergence at the transformed point. (`Breakdown.Periodic.FracSelfSimilar.Internal.divergence_field`)

**Advection under rotation and scale.** The transformed field's advection is amplitude squared times spatial scale times the rotated profile advection. (`Breakdown.Periodic.FracSelfSimilar.Internal.advection_field`)

**Fractional power under rescaling.** The covariance statement scales the fractional operator by amplitude times the positive spatial scale to the power 2α. (`Breakdown.Periodic.FracSelfSimilar.Internal.power_field`)

**Gradient represents the derivative.** Pairing a scalar field's gradient with a vector equals its derivative applied to that vector. (`Breakdown.Periodic.FracSelfSimilar.Internal.inner_gradient`)

**Gradient of a rescaled pressure.** The rotated and rescaled pressure gradient is pressure amplitude times spatial scale times the rotated original gradient. (`Breakdown.Periodic.FracSelfSimilar.Internal.gradient_field`)

**Differentiate the remaining-time power.** Before time T, the derivative of (T − t) to power p is −p times that power divided by T − t. (`Breakdown.Periodic.FracSelfSimilar.Internal.hasDerivAt_rpow_sub`)

**Differentiate the self-similar field.** Before the positive terminal time, the self-similar field's time derivative is the stated sum of amplitude, rotation and dilation terms. (`Breakdown.Periodic.FracSelfSimilar.Internal.hasDerivAt_selfSimilar`)

**Smooth rotating composition.** Smooth angle and vector functions remain smooth at the point after applying axial rotation. (`Breakdown.Periodic.FracSelfSimilar.Internal.rot_contDiffAt`)

**Smooth spatial composition.** Composing a smooth spatial function with a smooth coordinate map preserves pointwise smoothness. (`Breakdown.Periodic.FracSelfSimilar.Internal.comp_contDiffAt`)

**Smooth remaining-time powers.** Every real power of T minus time is smooth at points with time below T. (`Breakdown.Periodic.FracSelfSimilar.Internal.contDiffAt_pow_sub`)

**Smooth similarity coordinates.** For positive terminal time, the rotating fractional similarity coordinates are smooth before that time. (`Breakdown.Periodic.FracSelfSimilar.Internal.contDiffAt_point`)

**Smooth self-similar velocity.** A smooth profile gives a jointly smooth self-similar velocity before the positive terminal time. (`Breakdown.Periodic.FracSelfSimilar.Internal.contDiffOn_field`)

**Smooth self-similar pressure.** A smooth pressure profile gives a jointly smooth self-similar pressure before the positive terminal time. (`Breakdown.Periodic.FracSelfSimilar.Internal.contDiffOn_pressure`)

**Self-similar fractional solution.** For 1 < α < 5/4, axial rotation and fractional covariance establish the self-similar solution statement. (`Breakdown.Periodic.fracSelfSimilarSolves_of`)

### Breakdown.Frac.TorusSelfSimilarDecay

This file transports the profile decay estimates through the fractional self-similar scaling used by the localization argument.

**Combine self-similar decay factors.** For positive scale and nonnegative radius, the scaled decay expression equals the shifted-radius inverse power. (`Breakdown.Periodic.FracDecay.Internal.scale_identity`)

**Norm of a scaled derivative.** The norm of the jth derivative under scalar dilation is multiplied by the absolute scale to the jth power. (`Breakdown.Periodic.FracDecay.Internal.norm_iteratedFDeriv_scaled`)

**Isometries preserve derivative norms.** Pushing a field forward by a linear isometry preserves each derivative norm at the corresponding inverse image. (`Breakdown.Periodic.FracDecay.Internal.norm_iteratedFDeriv_push`)

**Gradient bound by derivative norm.** The gradient norm is at most three times the derivative norm. (`Breakdown.Periodic.FracDecay.Internal.grad_le`)

**Advection inherits combined decay.** The stated velocity and derivative decay bounds imply advection decay with exponent 4α − 1. (`Breakdown.Periodic.FracDecay.Internal.adv_bound`)

**Spatial decay after self-similar scale.** For positive α and scale, profile derivative decay becomes the stated shifted-radius decay for the rescaled field. (`Breakdown.Periodic.FracDecay.Internal.spatial_core`)

**Rescale the fractional operator.** Fractional covariance gives the stated rotation and scale formula for the operator on a rescaled field. (`Breakdown.Periodic.FracDecay.Internal.frac_core`)

**Fractional decay after scaling.** The profile fractional-operator decay gives the corresponding shifted-radius decay after positive self-similar scaling. (`Breakdown.Periodic.FracDecay.Internal.frac_bound`)

**Pressure-gradient decay after scaling.** The pressure derivative decay gives the stated shifted-radius pressure-gradient bound after positive scaling and rotation. (`Breakdown.Periodic.FracDecay.Internal.pressure_bound`)

**Self-similar decay from the profile.** The solution and covariance hypotheses yield the full fractional self-similar decay statement in the declared exponent range. (`Breakdown.Periodic.fracSelfSimilarDecay_of`)

### Breakdown.Frac.TorusShellLambda

This file proves the fractional torus shell bound by testing weighted Fourier coefficients and interpolating their L2 and L6 estimates.

**Weighted test coefficients.** Each test coefficient is the original coefficient multiplied by its Fourier weight and the scalar multiplier g. (`Breakdown.Periodic.TorusShellLambda.Internal.gCoef`)

**Real field from test coefficients.** The test field is the real part of the Fourier series formed from the weighted coefficients. (`Breakdown.Periodic.TorusShellLambda.Internal.gPhi`)

**Norm of a weighted coefficient.** For nonnegative g, the weighted coefficient norm equals its scalar weight times the original coefficient norm. (`Breakdown.Periodic.TorusShellLambda.Internal.norm_gCoef`)

**Summable weighted test coefficients.** Summability of the weighted square of g makes the test coefficient norms summable. (`Breakdown.Periodic.TorusShellLambda.Internal.summable_norm_gCoef`)

**Square bound for test coefficients.** The stated multiplier bounds control each test coefficient square by B times the original weighted energy. (`Breakdown.Periodic.TorusShellLambda.Internal.sq_norm_gCoef_le`)

**Weighted test-energy bound.** A bound B on the weighted multiplier gives a B-squared bound on each weighted test coefficient square. (`Breakdown.Periodic.TorusShellLambda.Internal.weight_sq_norm_gCoef_le`)

**Bound the real test by its series.** For p at least one, the real test field's Lp size is bounded by the corresponding torus-series norm. (`Breakdown.Periodic.TorusShellLambda.Internal.eLpNorm_gPhi_le`)

**L2 test bound.** The multiplier bounds give a squared L2 series norm at most B times the squared input norm. (`Breakdown.Periodic.TorusShellLambda.Internal.torusSeries_two_gCoef_le`)

**L6 test bound.** The assumed finite-series Sobolev bound gives an L6 test-series norm at most C times B times the input norm. (`Breakdown.Periodic.TorusShellLambda.Internal.torusSeries_six_gCoef_le`)

**L3 test bound by interpolation.** The Sobolev and multiplier bounds put the test field in L3 with the stated cubic-scale norm estimate. (`Breakdown.Periodic.TorusShellLambda.Internal.gPhi_bound`)

**Recover energy by testing.** The specified projected Fourier coefficients identify the squared torus norm with the physical pairing against the real test field. (`Breakdown.Periodic.TorusShellLambda.Internal.norm_sq_eq_pairing`)

**Nonnegative fractional heat factor.** The fractional lattice heat factor is nonnegative. (`Breakdown.Periodic.TorusShellLambda.Internal.fracFactor_nonneg`)

**Fractional heat factor at most one.** The fractional lattice heat factor never exceeds one. (`Breakdown.Periodic.TorusShellLambda.Internal.fracFactor_le_one`)

**Compare quadratic and higher powers.** For nonnegative radius and α at least one, the radius squared is at most its 2α power plus one. (`Breakdown.Periodic.TorusShellLambda.Internal.sq_le_rpow_add_one`)

**Fractional heat against ordinary heat.** At positive time and α at least one, the fractional factor is at most the ordinary heat factor multiplied by the exponential of time. (`Breakdown.Periodic.TorusShellLambda.Internal.fracFactor_le_heat`)

**Summable weighted heat squares.** At positive time and α at least one, the weighted squares of the fractional factors are summable. (`Breakdown.Periodic.TorusShellLambda.Internal.summable_weight_fracFactor`)

**Power times exponential estimate.** For exponent between zero and one, a nonnegative power times the stated exponential is bounded by the reciprocal time power. (`Breakdown.Periodic.TorusShellLambda.Internal.rpow_mul_exp_le`)

**Weighted fractional factor estimate.** For α at least one and time in (0, 1], the weighted factor is at most twice time to the power −1/α. (`Breakdown.Periodic.TorusShellLambda.Internal.weight_fracFactor_le`)

**Source operator as rescaled forcing.** At positive spatial scale, the source operator is the fractional torus force applied to the similarity-rescaled source. (`Breakdown.Periodic.TorusShellLambda.Internal.fracSourceOp_apply`)

**Fourier coefficients of forcing.** At positive time, the fractional torus force coefficient is the heat factor times the solenoidal projection of the source coefficient. (`Breakdown.Periodic.TorusShellLambda.Internal.coeff_fracForce`)

**L3/2 bound for the source operator.** For α greater than one, the forcing and source hypotheses give the stated scale-time bound in terms of a shell-supported source's L3/2 size. (`Breakdown.Periodic.TorusShellLambda.Internal.fracSourceOp_threeHalves`)

**Fractional torus shell bound.** For α greater than one, the forcing algebra and source-operator existence imply the fractional torus shell estimate. (`Breakdown.Periodic.fracTorusLambdaBound`)

### Breakdown.Frac.TorusShellR3

This file supplies the space counterpart of the fractional shell comparison estimate.

**Combine two heat-decay factors.** For the stated nonnegative constants and positive α and time, the square root of the two decay factors has exponent −3/(4α). (`Breakdown.Periodic.Internal.FracShellR3.sqrt_fracPhi_product`)

**Test the space heat-shell term.** The fractional test bounds control the heat-evolved shell advection pairing by the stated product of norms and time power. (`Breakdown.Periodic.Internal.FracShellR3.inner_fracHeatSolenoidal_le`)

**Factor the fractional space shell map.** The fractional bilinear test formula implies the space shell factorization for α greater than one. (`Breakdown.Periodic.fracR3Factor`)

**Fractional space shell bound.** The fractional test-field bounds imply the space shell estimate for α greater than one. (`Breakdown.Periodic.fracR3LambdaBound`)

### Breakdown.Frac.TorusShellTorus

This file factors the torus shell operator through the fractional source operator and its scaling identity.

**Source operator as torus forcing.** At positive scale, the fractional source operator equals the torus force applied to the similarity-rescaled source. (`Breakdown.Periodic.TorusShellTorus.Internal.fracSourceOp_apply`)

**Simplify the shell scaling factor.** For positive α and scale, the shell normalization simplifies to minus the scale to the power −1/(4α). (`Breakdown.Periodic.TorusShellTorus.Internal.scale_identity`)

**Factor the fractional torus shell map.** For α greater than one, the kernel, force and source-operator identities give the fractional torus shell factorization. (`Breakdown.Periodic.fracTorusFactor`)

### Breakdown.Frac.TorusSource

This file constructs the bounded fractional source operator and proves its linearity and continuity.

**Nonzero lattice frequencies have size.** A nonzero lattice frequency has norm at least one. (`Breakdown.Periodic.FracTorusSource.Internal.one_le_norm_freq`)

**Quadratic frequency below its power.** For α at least one, the quadratic lattice frequency weight is at most the fractional frequency power. (`Breakdown.Periodic.FracTorusSource.Internal.sq_le_rpow`)

**Fractional heat is bounded by heat.** For α at least one, the fractional lattice factor is at most the ordinary heat factor. (`Breakdown.Periodic.FracTorusSource.Internal.factor_le_heat`)

**Nonnegative heat multiplier.** The fractional lattice heat factor is nonnegative at every frequency. (`Breakdown.Periodic.FracTorusSource.Internal.factor_nonneg`)

**Sequence coordinates from coefficients.** The stored sequence coordinate is the Fourier coefficient multiplied by the square root of its weight. (`Breakdown.Periodic.FracTorusSource.Internal.seq_eq_smul_coeff`)

**Fractional force norm comparison.** The fractional force algebra bounds the fractional force norm by the ordinary force norm for α at least one. (`Breakdown.Periodic.FracTorusSource.Internal.norm_force_le`)

**Forcing respects coefficient addition.** Adding the source Fourier coefficients adds the corresponding fractional torus forces. (`Breakdown.Periodic.FracTorusSource.Internal.force_add_of_coef`)

**Forcing respects coefficient scaling.** Real scaling of the source Fourier coefficients scales the fractional torus force by the same factor. (`Breakdown.Periodic.FracTorusSource.Internal.force_smul_of_coef`)

**Positive fractional similarity scale.** A positive time scale gives a positive fractional similarity scale. (`Breakdown.Periodic.FracTorusSource.Internal.simScale_pos`)

**Bound the source map.** For α at least one, the fractional forcing algebra gives a uniform operator bound for each fixed source scale and time. (`Breakdown.Periodic.FracTorusSource.Internal.fracSourceFun_bound`)

**Source map preserves addition.** The fractional source map preserves addition of its L2 inputs. (`Breakdown.Periodic.FracTorusSource.Internal.sourceFun_add`)

**Source map preserves real scaling.** The fractional source map preserves multiplication by a real scalar. (`Breakdown.Periodic.FracTorusSource.Internal.sourceFun_smul`)

**Existence of the source operator.** For α greater than one, the fractional force algebra constructs the bounded source operator. (`Breakdown.Periodic.fracSourceOpExists`)

**Continuity of the source operator.** For α greater than one, source-operator existence and forcing algebra give the required source-operator continuity. (`Breakdown.Periodic.fracSourceOpContinuous`)

### Breakdown.Frac.TorusSymmetry

This file proves symmetry of the fractional operator on smooth periodic fields by integration by parts and exchange of the remainder integrals.

**Integer multiples preserve a period.** A periodic field is invariant under any integer multiple of a coordinate period. (`Breakdown.Periodic.TorusSymmetry.Internal.periodic_int_smul`)

**All lattice shifts preserve a period.** A periodic field is invariant under translation by every lattice frequency. (`Breakdown.Periodic.TorusSymmetry.Internal.periodic_freq`)

**Continuous periodic fields are bounded.** A continuous periodic field admits a global norm bound. (`Breakdown.Periodic.TorusSymmetry.Internal.exists_bound_of_periodic`)

**Iterated derivatives stay periodic.** Every iterated derivative of a periodic field is periodic. (`Breakdown.Periodic.TorusSymmetry.Internal.isPeriodic_iteratedFDeriv`)

**The derivative stays periodic.** The derivative of a periodic field is periodic. (`Breakdown.Periodic.TorusSymmetry.Internal.isPeriodic_fderiv`)

**Directional derivatives stay periodic.** Applying a periodic derivative field to a fixed direction gives a periodic field. (`Breakdown.Periodic.TorusSymmetry.Internal.isPeriodic_fderiv_apply`)

**Continuous fields integrate on the cell.** A continuous field is integrable on the periodic cell. (`Breakdown.Periodic.TorusSymmetry.Internal.integrableOn_cell`)

**Expand a vector in coordinate axes.** The sum of the coordinate multiples of the standard unit vectors equals the original vector. (`Breakdown.Periodic.TorusSymmetry.Internal.sum_unitVector`)

**Periodic derivative has zero integral.** A continuously differentiable periodic scalar field has zero cell integral of each fixed directional derivative. (`Breakdown.Periodic.TorusSymmetry.Internal.integral_cell_fderiv_eq_zero`)

**Periodic integration by parts.** For smooth periodic vector fields, moving a directional derivative across the cell inner-product integral changes its sign. (`Breakdown.Periodic.TorusSymmetry.Internal.integral_cell_inner_fderiv`)

**Translate a periodic cell integral.** The cell integral of a smooth periodic scalar field is invariant under any spatial translation. (`Breakdown.Periodic.TorusSymmetry.Internal.integral_cell_add`)

**Second derivative in one direction.** For a smooth field, the repeated derivative in one direction equals the derivative of its directional derivative. (`Breakdown.Periodic.TorusSymmetry.Internal.iteratedFDeriv_two_eq_fderiv_apply`)

**Move the remainder across a pairing.** The periodic cell pairing of one field's second-order remainder equals the pairing with the other field's remainder at the reversed displacement. (`Breakdown.Periodic.TorusSymmetry.Internal.integral_cell_inner_remainder`)

**Bound the remainder for large shifts.** For displacement norm at least one, the remainder is bounded by the translated value and the stated quadratic derivative bound. (`Breakdown.Periodic.TorusSymmetry.Internal.norm_remainder_le_far`)

**Integrability from two radial powers.** An almost-everywhere measurable function dominated by an integrable near-zero power and an integrable far-field power is integrable. (`Breakdown.Periodic.TorusSymmetry.Internal.integrable_of_near_far`)

**Combine real and integer powers.** Under the stated nonvanishing exponent conditions, multiplying a real power by an integer power adds the exponents. (`Breakdown.Periodic.TorusSymmetry.Internal.rpow_mul_pow_eq`)

**Joint continuity of the remainder.** The second-order remainder of a smooth field is jointly continuous in base point and displacement. (`Breakdown.Periodic.TorusSymmetry.Internal.continuous_remainder_pair`)

**Uniform integrable remainder majorant.** For 1 < α < 3/2, the remainder estimate gives a single integrable displacement majorant for a smooth periodic field. (`Breakdown.Periodic.TorusSymmetry.Internal.exists_dominating`)

**Remainder continuous in base point.** For a fixed displacement, the second-order remainder of a smooth field is continuous in the base point. (`Breakdown.Periodic.TorusSymmetry.Internal.continuous_remainder_section`)

**Remainder continuous in displacement.** For a fixed base point, the second-order remainder of a smooth field is continuous in displacement. (`Breakdown.Periodic.TorusSymmetry.Internal.continuous_remainder_increment`)

**Integrable fractional remainder.** For 1 < α < 3/2, a smooth periodic field has an integrable fractional remainder at every base point. (`Breakdown.Periodic.TorusSymmetry.Internal.integrable_remainder_section`)

**Continuous fractional operator.** For 1 < α < 3/2, the remainder bound makes the fractional operator of a smooth periodic field continuous. (`Breakdown.Periodic.TorusSymmetry.Internal.continuous_fractionalPowerAt`)

**Integrable tested remainder.** For 1 < α < 3/2, the tested fractional remainder of two smooth periodic fields is integrable over the cell and all displacements. (`Breakdown.Periodic.TorusSymmetry.Internal.integrable_prod_cell`)

**Symmetry of the periodic operator.** For 1 < α < 3/2, the remainder bound establishes symmetry of the fractional operator on periodic fields. (`Breakdown.Periodic.periodicSymmetry_of`)

### Breakdown.Frac.TorusUnique

This file proves uniqueness of fractional torus mild solutions using a short-interval contraction and continuation across time blocks.

**Difference of diagonal kernel terms.** For a symmetric kernel, the difference of its two diagonal values is its value on the difference and sum of the inputs. (`Breakdown.Periodic.FracTorusUnique.Internal.kernel_sq_sub_sq`)

**Integral of the time singularity.** For γ below one, the interval integral of the terminal-time power equals the stated endpoint power divided by 1 − γ. (`Breakdown.Periodic.FracTorusUnique.Internal.integral_sub_rpow`)

**Integrable time singularity.** For γ below one, the terminal-time power is interval-integrable between any two endpoints. (`Breakdown.Periodic.FracTorusUnique.Internal.intervalIntegrable_sub_rpow`)

**Bound a time-integrated kernel.** The short-time kernel bound and the two uniform input bounds give the stated integral estimate on intervals of length at most one. (`Breakdown.Periodic.FracTorusUnique.Internal.norm_integral_kernel_le`)

**Contraction on a short interval.** The stated time smallness and past vanishing reduce the integral-equation solution's bound from S to S/2 at the endpoint. (`Breakdown.Periodic.FracTorusUnique.Internal.local_contraction`)

**Vanishing from repeated halving.** A continuous curve whose every uniform bound can be halved vanishes throughout the compact interval. (`Breakdown.Periodic.FracTorusUnique.Internal.zero_on_block`)

**Extend vanishing across time blocks.** Initial vanishing and a fixed positive continuation step imply vanishing on the whole stated interval. (`Breakdown.Periodic.FracTorusUnique.Internal.zero_of_blocks`)

**Equation for two mild solutions.** Two mild solutions with the same initial value satisfy the stated integrable difference equation wherever their intervals overlap. (`Breakdown.Periodic.FracTorusUnique.Internal.mild_difference_eq`)

**Fractional torus mild uniqueness.** For 1 < α < 5/4, the kernel algebra and sharp bound yield uniqueness of fractional torus mild solutions. (`Breakdown.Periodic.fracTorusMildUniqueness_of`)
<!-- /passage:front -->

