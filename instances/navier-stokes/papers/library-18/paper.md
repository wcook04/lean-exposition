
<!-- passage:front -->
# Library guide 18: Breakdown/FracCell

**Navier–Stokes pages:** [the paper](../navier-stokes-paper/paper.pdf) · [proof routes](../navier-stokes-routes/paper.md) · [routes in detail](../navier-stokes-route-details/paper.md) · library guide: [1](../navier-stokes-library-01/paper.md) [2](../navier-stokes-library-02/paper.md) [3](../navier-stokes-library-03/paper.md) [4](../navier-stokes-library-04/paper.md) [5](../navier-stokes-library-05/paper.md) [6](../navier-stokes-library-06/paper.md) [7](../navier-stokes-library-07/paper.md) [8](../navier-stokes-library-08/paper.md) [9](../navier-stokes-library-09/paper.md) [10](../navier-stokes-library-10/paper.md) [11](../navier-stokes-library-11/paper.md) [12](../navier-stokes-library-12/paper.md) [13](../navier-stokes-library-13/paper.md) [14](../navier-stokes-library-14/paper.md) [15](../navier-stokes-library-15/paper.md) [16](../navier-stokes-library-16/paper.md) [17](../navier-stokes-library-17/paper.md) **18** [19](../navier-stokes-library-19/paper.md) [20](../navier-stokes-library-20/paper.md) [21](../navier-stokes-library-21/paper.md) [22](../navier-stokes-library-22/paper.md) [23](../navier-stokes-library-23/paper.md) [24](../navier-stokes-library-24/paper.md) [25](../navier-stokes-library-25/paper.md) [26](../navier-stokes-library-26/paper.md) [27](../navier-stokes-library-27/paper.md) [28](../navier-stokes-library-28/paper.md) [29](../navier-stokes-library-29/paper.md) [30](../navier-stokes-library-30/paper.md)

*A plain title and a sentence for each declaration in `Breakdown.FracCell.GivenAuxPin` to `Breakdown.FracCell.GivenProfilePowerFieldJumpsPieces` of Alpöge and Buckmaster's Lean at `ad53419de079eb8f95f60313473374624a348546`, in the authors' file order. Prepared with AI assistance. The authors have not reviewed it.*

Each paragraph names one declaration and says whether it is a definition, a proposition that the library defines (its name usually ends in `Holds` or `Statement`) or a proved result, then what it states. Click a paragraph to open its Lean on the right.

### Breakdown.FracCell.GivenAuxPin

This file converts compact pin-potential regularity into weak second derivatives, negative traces and the smooth-pin identities used in the auxiliary instance. **Reading context:** Appendix B: represented fields and the auxiliary estimates used by the profile, pin and adjoint reductions (B.1 and B.9–B.13).

**Theorem · Scalar weak differentiation of a pin.** A Lipschitz real function with the stated almost-everywhere derivative satisfies directional integration by parts against scalar tests. [`pinWeakScalar`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPin.lean#L15).

**Theorem · Vector weak differentiation of a pin.** A Lipschitz vector field with measurable bounded almost-everywhere derivative satisfies coordinate integration by parts against scalar tests. [`pinWeakSlope`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPin.lean#L32).

**Theorem · Pin differentiation against vector tests.** A Lipschitz vector field with the stated measurable bounded derivative satisfies directional integration by parts against vector test fields. [`pinWeakVec`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPin.lean#L66).

**Theorem · Bounded weak second derivative of a pin.** A globally Lipschitz first derivative has a measurable weak second derivative whose norm is bounded everywhere by the same Lipschitz constant. [`pinSecondBound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPin.lean#L125).

**Theorem · Negative trace of a smooth compact pin.** A compactly supported C¹ field with Lipschitz derivative has weak negative trace equal to minus the sum of its second derivative's diagonal entries. [`pinTrace`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPin.lean#L147).

**Theorem · Regularity of the supplied smooth pin.** Valid auxiliary data give finite energy of the smooth pin and a compactly supported C¹ pin potential with a bounded measurable weak second derivative. [`smoothPin_of_given`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPin.lean#L233).

**Theorem · Pin potential and trace regularity.** Valid auxiliary data give a compactly supported C¹ pin potential with bounded measurable weak second derivative and bounded measurable weak negative trace. [`pinRegular_of_given`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPin.lean#L258).

**Theorem · Auxiliary and profile phases agree.** The auxiliary-instance condition identifies the auxiliary phase with the profile phase at every parameter. [`phase_eq_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPin.lean#L286).

**Theorem · The smooth pin is a scaled derivative.** The auxiliary-instance condition identifies each smooth pin with the derivative of its pin potential divided by the supplied pin scale. [`pinField_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPin.lean#L298).

### Breakdown.FracCell.GivenAuxPinCore

This file converts spline vanishing beyond a finite radial cutoff into compact support and the regularity required of pin potentials. **Reading context:** Appendix B: represented fields and the auxiliary estimates used by the profile, pin and adjoint reductions (B.1 and B.9–B.13).

**Theorem · Lower bound for the selected break.** In a strictly increasing list, a breakpoint at or below the query bounds the last selected breakpoint from below. [`sortedFilterGetD`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinCore.lean#L15).

**Theorem · A cell selected beyond a breakpoint.** On an increasing mesh from zero to one, a query beyond a nonterminal breakpoint selects a cell whose left endpoint is at least that breakpoint. [`cellIndexGe`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinCore.lean#L51).

**Theorem · A spline vanishes beyond its cutoff.** A spline whose pieces vanish from a mesh breakpoint evaluates to zero at and beyond that breakpoint. [`splineZero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinCore.lean#L100).

**Theorem · Zero amplitudes give zero fields.** If the relevant mean or wave amplitudes vanish beyond a radial cutoff, the reduced field vanishes beyond that cutoff. [`reducedZero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinCore.lean#L107).

**Theorem · A compact field vanishes past its cutoff.** A field from compact field data is zero wherever its radial chart lies beyond the cutoff. [`fieldZero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinCore.lean#L150).

**Theorem · Compact field data give compact support.** Valid chart parameters and compact field data give a compactly supported spatial field. [`compactFieldSupport`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinCore.lean#L169).

**Theorem · Regularity of a compact field.** A field from compact field data is C¹, compactly supported, and has a globally Lipschitz derivative. [`compactField_regular`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinCore.lean#L186).

### Breakdown.FracCell.GivenAuxPinSmooth

This file combines local derivative bounds with the compact radial cutoff, including the zero-field case when the cutoff is nonpositive. **Reading context:** Appendix B: represented fields and the auxiliary estimates used by the profile, pin and adjoint reductions (B.1 and B.9–B.13).

**Theorem · The selected break is past the cutoff.** In a strictly increasing list, a cutoff breakpoint below the query bounds the last selected breakpoint from below. [`pinSortedFilterGetD`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmooth.lean#L16).

**Theorem · The cell starts past the cutoff.** Beyond a nonterminal cutoff breakpoint, the selected cell's left endpoint is at least the cutoff. [`pinCellIndexGe`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmooth.lean#L52).

**Theorem · Spline vanishing beyond the cutoff.** A spline vanishing from a mesh breakpoint evaluates to zero at and beyond that breakpoint. [`pinSplineZero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmooth.lean#L101).

**Theorem · Zero amplitudes give zero fields.** Vanishing of the relevant mean or wave amplitudes beyond a cutoff forces the reduced field to vanish there. [`pinReducedZero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmooth.lean#L108).

**Theorem · The field vanishes past its cutoff.** Compact field data make the constructed field vanish wherever the radial chart exceeds the cutoff. [`pinFieldZero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmooth.lean#L151).

**Theorem · Mesh lookup is nonnegative.** Every mesh lookup with default one is nonnegative for a strictly increasing mesh beginning at zero. [`pinGetDNonneg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmooth.lean#L171).

**Theorem · A nonpositive cutoff gives a zero spline.** A valid spline that vanishes from a nonpositive cutoff evaluates to zero everywhere. [`pinSplineAllZero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmooth.lean#L187).

**Theorem · A nonpositive cutoff gives a zero field.** Compact field data with a nonpositive cutoff construct the zero field. [`pinFieldZeroAll`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmooth.lean#L193).

**Theorem · Extending a compactly supported slope.** A field that vanishes outside a ball and is Lipschitz on the displayed larger ball has a global Lipschitz bound. [`pinSlopeGlue`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmooth.lean#L211).

**Theorem · A compact field has a tame derivative.** Valid compact field data give a C¹ spatial field whose derivative is globally Lipschitz. [`compactField_smooth`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmooth.lean#L278).

### Breakdown.FracCell.GivenAuxPinSmoothLocal

This file propagates spline derivative bounds through chart coordinates and phase factors, handles the axis cancellation, and obtains derivative bounds for compact fields on closed balls. **Reading context:** Appendix B: represented fields and the auxiliary estimates used by the profile, pin and adjoint reductions (B.1 and B.9–B.13).

**Predicate · Locally Lipschitz derivative.** Local tameness means that the function has a derivative throughout some ball and that this derivative satisfies one Lipschitz bound there. [`TameAt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocal.lean#L20).

**Theorem · Bounds from a Lipschitz derivative.** A Lipschitz derivative on a ball gives a uniform derivative bound, a Lipschitz bound for the function, and a bound for its values on that ball. [`tame_bounds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocal.lean#L24).

**Theorem · Twice smooth gives local tameness.** Twice continuous differentiability at a point supplies a locally Lipschitz derivative there. [`tame_of_contDiffAt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocal.lean#L53).

**Theorem · A derivative bound gives tameness.** A differentiable function whose derivative is locally Lipschitz is locally tame at every point. [`tame_of_global`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocal.lean#L63).

**Theorem · Local derivative Lipschitz bound.** Local tameness supplies a neighbourhood on which the Fréchet derivative has a finite Lipschitz constant. [`tame_slope`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocal.lean#L71).

**Theorem · Tameness under local equality.** Two functions that agree near the point have the same local tameness property there. [`tame_congr`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocal.lean#L78).

**Theorem · Tameness of a sum.** The sum of two locally tame functions is locally tame at the same point. [`tame_add`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocal.lean#L88).

**Theorem · Tameness under a linear map.** Applying a continuous linear map preserves local tameness. [`tame_clm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocal.lean#L104).

**Theorem · Tameness of a composition.** Composing locally tame functions preserves local tameness at the corresponding points. [`tame_comp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocal.lean#L114).

**Theorem · Tameness of a product.** The product of two locally tame complex functions is locally tame. [`tame_mul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocal.lean#L151).

**Theorem · Tameness under negation.** Negating a locally tame function preserves local tameness. [`tame_neg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocal.lean#L186).

**Theorem · Tameness of a difference.** Subtracting locally tame functions preserves local tameness. [`tame_sub`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocal.lean#L189).

**Theorem · Smooth spatial coordinate.** Each spatial coordinate is smooth to every finite order. [`pin_coord`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocal.lean#L195).

**Theorem · Smooth norm away from the origin.** Spatial norm is smooth to every finite order away from the origin. [`pin_norm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocal.lean#L198).

**Theorem · Smooth normalized coordinate.** Every coordinate divided by spatial norm is smooth away from the origin. [`pin_ratio`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocal.lean#L201).

**Theorem · Smooth radial chart off the origin.** For valid chart parameters, the compactified radial coordinate is smooth away from the origin. [`pin_chartT`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocal.lean#L204).

**Theorem · Smooth height ratio off the origin.** The height-to-radius ratio is smooth away from the origin. [`pin_height`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocal.lean#L210).

**Theorem · Smooth decay factor off the origin.** For valid chart parameters, the decay factor is smooth away from the origin. [`pin_decay`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocal.lean#L213).

**Theorem · Smooth regularized logarithmic phase.** For valid chart parameters, the regularized logarithmic phase is smooth throughout space. [`pin_logPhase`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocal.lean#L225).

**Theorem · Smooth radial frame off the origin.** Every radial frame component is smooth away from the origin. [`pin_radial`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocal.lean#L232).

**Theorem · Smooth polar frame off the origin.** Every polynomial polar frame component is smooth away from the origin. [`pin_polar`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocal.lean#L235).

**Theorem · Smooth azimuthal frame off the origin.** Every polynomial azimuthal frame component is smooth away from the origin. [`pin_azim`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocal.lean#L242).

**Definition · Complex planar coordinate.** The planar coordinate combines the first two spatial coordinates into a complex number. [`pinPlane`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocal.lean#L248).

**Theorem · The planar coordinate is smooth.** The complex planar coordinate is smooth to every finite order. [`pinPlane_contDiff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocal.lean#L250).

**Theorem · Integer phase as a normalized power.** Away from zero, the integer angular phase equals the corresponding integer power of the normalized complex direction. [`pin_exp_arg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocal.lean#L258).

**Theorem · Smooth integer powers away from zero.** An integer power of a twice continuously differentiable complex function remains twice continuously differentiable where its base is nonzero. [`pin_zpow`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocal.lean#L270).

**Theorem · Smooth mode phase away from the axis.** For valid chart parameters, the mode phase is twice continuously differentiable away from the axis. [`pin_phase`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocal.lean#L278).

**Theorem · A coordinate vector as a scaled unit.** A vector with only one nonzero coordinate equals that coordinate times its coordinate unit vector. [`pin_single`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocal.lean#L300).

**Theorem · Assembling locally tame components.** A vector assembled from locally tame real components is locally tame at the same point. [`tame_ofComponents`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocal.lean#L305).

**Theorem · A C² function is locally tame.** A twice continuously differentiable function of two real variables is locally tame at every point. [`pin_tame_all`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocal.lean#L317).

**Theorem · The radial partial derivative is C².** The first-coordinate partial derivative of a C³ function of two real variables is C². [`pin_partial_t`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocal.lean#L320).

**Theorem · The height partial derivative is C².** The second-coordinate partial derivative of a C³ function of two real variables is C². [`pin_partial_x`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocal.lean#L333).

**Theorem · Tame radial derivatives of products.** Multiplying by a C³ factor preserves local tameness of the radial derivative under the stated differentiability and tameness hypotheses. [`pin_tderiv_mul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocal.lean#L346).

**Theorem · Tame height derivatives of products.** Multiplying by a C³ factor preserves local tameness of the height derivative under the stated differentiability and tameness hypotheses. [`pin_xderiv_mul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocal.lean#L362).

**Theorem · The radial core ratio is C².** For valid chart parameters, the regularized radial core ratio is twice continuously differentiable. [`pin_coreRatio`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocal.lean#L378).

**Theorem · The polynomial radial scale is C².** The complex radial factor t times one minus t is twice continuously differentiable. [`pin_scaleA`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocal.lean#L392).

**Theorem · The twisted scale coefficient is C².** For valid chart parameters, the phase-and-decay coefficient in the twisted scale derivative is twice continuously differentiable. [`pin_scaleB`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocal.lean#L395).

**Theorem · The tensor weight is C³.** The product of the polynomial radial weight and a natural power of one minus height squared is three times continuously differentiable. [`pin_weight`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocal.lean#L402).

**Theorem · The angular quadratic is C³.** One minus height squared, included into the complex numbers, is three times continuously differentiable. [`pin_q`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocal.lean#L409).

**Theorem · The radial polynomial weight is C³.** Every radial polynomial weight is three times continuously differentiable. [`pin_p`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocal.lean#L412).

**Theorem · First-order spline evaluation is tame.** A spline with at least first-order matching in both coordinates has locally tame evaluation. [`pin_spline`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocal.lean#L417).

**Theorem · The spline's radial derivative is tame.** A spline with at least second-order radial and first-order height matching has a locally tame radial derivative. [`pin_spline_t`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocal.lean#L422).

**Theorem · The spline's height derivative is tame.** A spline with at least first-order radial and second-order height matching has a locally tame height derivative. [`pin_spline_x`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocal.lean#L427).

**Theorem · Local derivative control for wave modes.** Each component of an included nonzero reduced field mode has a locally Lipschitz derivative. [`reducedField_fderiv_localSlope_wave`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocal.lean#L432).

**Theorem · Local derivative control for the mean.** Each component of the included mean reduced field has a locally Lipschitz derivative. [`reducedField_fderiv_localSlope_mean`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocal.lean#L468).

**Theorem · Tameness of a reconstructed mode.** Differentiable reduced components with locally Lipschitz derivatives and a twice smooth phase give a locally tame reconstructed mode away from the origin. [`pin_field_tame`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocal.lean#L499).

**Definition · Quadratic planar phase.** The planar phase map multiplies the integer angular exponential by squared planar modulus. [`planeMap`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocal.lean#L523).

**Theorem · Differentiability of the planar phase.** For every integer phase index, the quadratic planar phase is differentiable throughout the complex plane. [`planeMap_diff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocal.lean#L526).

**Theorem · Quadratic scaling of the planar phase.** Under positive real scaling, the planar phase map scales by the square of the scale. [`planeMap_scale`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocal.lean#L529).

**Theorem · Linear scaling of the phase derivative.** The derivative of the quadratic planar phase scales linearly under positive real scaling. [`planeMap_fderiv_scale`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocal.lean#L537).

**Theorem · Zero phase derivative at the origin.** The derivative of the quadratic planar phase at the complex origin is zero. [`planeMap_fderiv_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocal.lean#L571).

**Theorem · Angular phase as a unit-direction power.** At a nonzero complex number, the integer angular exponential equals the integer power of its normalized direction. [`plane_exp_arg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocal.lean#L577).

**Theorem · Twice smooth powers off their zero set.** Integer powers preserve twice continuous differentiability at a point where the complex base is nonzero. [`plane_zpow`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocal.lean#L589).

**Theorem · The planar phase is C² away from zero.** The quadratic planar phase is twice continuously differentiable at every nonzero complex point. [`planeMap_smooth`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocal.lean#L597).

**Theorem · The planar phase has a tame derivative.** The derivative of the quadratic integer planar phase is locally Lipschitz everywhere. [`planePhase_fderiv_localSlope`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocal.lean#L613).

**Theorem · Everywhere tame gives a C¹ function.** A function locally tame at every point is C¹ and has a locally Lipschitz derivative. [`tame_contDiff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocal.lean#L691).

**Theorem · Extracting a regular axis factor.** Every included nonzero reduced mode factors by one minus height squared, with a C¹ quotient whose derivative is locally Lipschitz. [`reducedField_wave_axisFactor_slope`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocal.lean#L698).

**Theorem · Angular weight as planar norm squared.** Away from the origin, one minus the squared height ratio equals squared planar norm divided by squared spatial norm. [`pin_one_sub_height`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocal.lean#L806).

**Theorem · Tameness of a wave mode off zero.** Every included nonzero field mode is locally tame away from the spatial origin, including on the axis. [`pin_axis_tame`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocal.lean#L821).

**Theorem · Local slope of the mean derivative.** The derivative of the included mean spatial field is locally Lipschitz throughout space. [`modeFieldOf_fderiv_localSlope_mean`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocal.lean#L879).

**Theorem · Local slope of a wave derivative.** The derivative of each included nonzero spatial field mode is locally Lipschitz throughout space. [`modeFieldOf_fderiv_localSlope_wave`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocal.lean#L895).

**Theorem · Mean derivative bound on a closed ball.** On every closed ball, the included mean field's derivative has a finite Lipschitz constant. [`modeFieldOf_fderiv_slopeOn_mean`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocal.lean#L912).

**Theorem · Wave derivative bound on a closed ball.** On every closed ball, each included nonzero field mode's derivative has a finite Lipschitz constant. [`modeFieldOf_fderiv_slopeOn_wave`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocal.lean#L918).

**Theorem · A finite sum has a common slope bound.** A finite sum of functions each Lipschitz on a set has some common Lipschitz constant on that set. [`slopeOn_finsetSum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocal.lean#L924).

**Theorem · Pin derivative bound on a closed ball.** A compact field with positive cutoff has a derivative Lipschitz bound on every closed ball. [`compactField_fderiv_slopeOn`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocal.lean#L943).

### Breakdown.FracCell.GivenAuxPinSmoothLocalLeaves

This file proves C¹ and Lipschitz gluing for spline pieces, then handles the origin by separating quadratic wave profiles and the mean mode's leading linear map. **Reading context:** Appendix B: represented fields and the auxiliary estimates used by the profile, pin and adjoint reductions (B.1 and B.9–B.13).

**Definition · Counting crossed breakpoints.** The gluing index counts the listed breakpoints at or below the input coordinate. [`glueIdx`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L16).

**Theorem · Recursion for the gluing index.** For an increasing breakpoint list, the gluing index is zero below the first breakpoint and otherwise one plus the index in the remaining list. [`glueIdx_cons`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L18).

**Theorem · The gluing index is bounded.** The number of crossed breakpoints cannot exceed the length of their list. [`glueIdx_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L29).

**Theorem · Gluing two C¹ pieces.** Two differentiable pieces with continuous derivatives glue across a continuous threshold when both values and derivatives agree there. [`glue_two`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L31).

**Theorem · Gluing finitely many C¹ pieces.** Differentiable pieces with continuous derivatives glue across an ordered threshold list when adjacent values and derivatives match at every threshold. [`glue_list`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L65).

**Definition · Polynomials on coordinate pairs.** The evaluator substitutes the two real coordinates as complex polynomial variables. [`evP`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L113).

**Definition · Derivative of polynomial evaluation.** The polynomial derivative map combines its two evaluated partial derivatives with the two coordinate projections. [`dP`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L115).

**Theorem · Evaluating the polynomial derivative.** The polynomial derivative on a direction is the sum of each direction coordinate times its corresponding evaluated partial derivative. [`dP_apply`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L119).

**Theorem · The polynomial derivative formula.** The displayed two-part continuous linear map is the Fréchet derivative of polynomial evaluation. [`evP_hasFDerivAt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L123).

**Theorem · Radial derivatives of equal traces.** Polynomials that agree along a fixed-height line have equal radial partial derivatives along that line. [`evP_line_t`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L153).

**Theorem · Height derivatives of equal traces.** Polynomials that agree along a fixed-radius line have equal height partial derivatives along that line. [`evP_line_x`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L164).

**Theorem · Mixed polynomial partials commute.** The two mixed first polynomial partial derivatives commute. [`pderiv_swap`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L175).

**Theorem · Continuity of the polynomial derivative.** The polynomial evaluation derivative is continuous in its coordinate pair. [`dP_continuous`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L183).

**Predicate · Matching values, derivatives and parity.** The gluing condition requires adjacent radial and height values and normal derivatives to match, together with the appropriate value or derivative vanishing at the parity axis. [`Glued`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L189).

**Theorem · Gluing polynomial rows.** Polynomial pieces with matching radial values and derivatives across ordered breaks have the displayed continuous Fréchet derivative. [`rows_glue`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L199).

**Theorem · Gluing the tensor-product pieces.** The radial and height matching conditions glue the polynomial grid into a differentiable function with continuous derivative. [`half_glue`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L219).

**Definition · Parity extension of polynomial pieces.** The full piecewise polynomial evaluates the selected pieces at absolute height and applies the chosen odd or even sign. [`fullF`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L244).

**Definition · Reflection in the height coordinate.** The reflection map keeps the first coordinate and negates the second. [`reflX`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L247).

**Theorem · Evaluating height reflection.** The height reflection sends a coordinate pair to the pair with negated second coordinate. [`reflX_apply`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L249).

**Definition · Derivative of the parity extension.** The full derivative uses the selected polynomial derivative at nonnegative height and its signed reflected composition at negative height. [`fullD`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L251).

**Theorem · No positive breaks lie below zero.** A list of strictly positive breaks has gluing index zero at the origin. [`glueIdx_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L256).

**Theorem · C¹ gluing across the parity axis.** Ordered positive height breaks and the gluing conditions give the parity-extended function its displayed continuous derivative. [`full_glue`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L262).

**Theorem · Radial derivative preserves parity.** Applying the full derivative in the radial direction gives the parity extension of the radial polynomial derivative with unchanged parity. [`fullD_t`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L317).

**Theorem · Height derivative reverses parity.** Applying the full derivative in the height direction gives the parity extension of the height polynomial derivative with reversed parity. [`fullD_x`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L325).

**Theorem · Evaluation after polynomial substitution.** Evaluating a substituted two-variable polynomial equals evaluating the original polynomial on the evaluated substitutions. [`eval_bind_two`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L333).

**Theorem · Evaluation at a fixed first coordinate.** Substituting a real first coordinate before polynomial evaluation gives evaluation at that fixed coordinate. [`evP_atFirst`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L340).

**Theorem · Evaluation at a fixed second coordinate.** Substituting a real second coordinate before polynomial evaluation gives evaluation at that fixed coordinate. [`evP_atSecond`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L347).

**Theorem · Polynomial equality on a radial join.** Equality after first-coordinate substitution gives equal polynomial values on the corresponding radial join. [`join_t`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L354).

**Theorem · Polynomial equality on a height join.** Equality after second-coordinate substitution gives equal polynomial values on the corresponding height join. [`join_x`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L359).

**Theorem · Parity vanishing after evaluation.** A polynomial whose second-coordinate substitution at zero is zero evaluates to zero on that axis. [`par_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L364).

**Theorem · Interior mesh order and indexing.** A strictly increasing mesh from zero to one has ordered positive interior breaks, the displayed cell count, and the stated interior-index correspondence. [`mesh_facts`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L371).

**Theorem · The spline equals its glued extension.** Parity-extended spline evaluation is exactly the glued piecewise-polynomial construction using the interior mesh breaks. [`spline_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L396).

**Theorem · Spline matching gives gluing data.** At least first-order matching in both coordinates gives the gluing conditions for the original spline pieces. [`glued_base`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L402).

**Theorem · Gluing the radial derivative pieces.** At least second-order radial and first-order height matching gives gluing conditions for the radial polynomial derivatives. [`glued_t`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L424).

**Theorem · Gluing the height derivative pieces.** At least first-order radial and second-order height matching gives gluing conditions for the height derivatives with reversed parity. [`glued_x`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L449).

**Theorem · Gluing two common slope bounds.** Two functions with the same Lipschitz constant on a convex set retain that constant when glued along a linear threshold where they agree. [`slope_glue_two`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L473).

**Theorem · Gluing a finite common slope bound.** A finite ordered gluing of functions with one common Lipschitz constant on a convex set preserves that constant when adjacent values agree. [`slope_glue_list`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L505).

**Theorem · A slope bound for the glued derivative.** Common derivative Lipschitz bounds for polynomial grid pieces give the same bound for the selected derivative on a convex set. [`slope_half`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L536).

**Theorem · Height reflection preserves norm.** Reflecting the second coordinate preserves the norm of a real coordinate pair. [`reflX_norm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L567).

**Theorem · Reflection has operator norm at most one.** The operator norm of height reflection is at most one. [`reflX_opNorm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L571).

**Theorem · A slope bound after parity extension.** Common derivative Lipschitz bounds on a closed ball pass to the derivative of the full parity extension. [`slope_full`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L574).

**Theorem · Polynomial evaluation is C¹.** The polynomial evaluator is continuously differentiable. [`evP_contDiff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L624).

**Theorem · The polynomial derivative is C¹.** The polynomial derivative map is continuously differentiable. [`dP_contDiff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L627).

**Theorem · Polynomial derivative bounds on balls.** Every polynomial derivative has a finite Lipschitz constant on each closed ball. [`dP_slope`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L631).

**Theorem · Local slope of the glued derivative.** The derivative assembled from the matched polynomial pieces is locally Lipschitz. [`fullD_locSlope`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L636).

**Theorem · A tame parity-extended derivative.** The Fréchet derivative of the fully glued parity extension is locally Lipschitz. [`fderiv_fullF`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L655).

**Theorem · Local slope of the spline derivative.** At least first-order matching in both coordinates gives a locally Lipschitz derivative of spline evaluation. [`spline_eval_localSlope`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L663).

**Theorem · Local slope of the radial derivative.** Second-order radial and first-order height matching give a locally Lipschitz derivative of the spline's radial partial derivative. [`spline_tderiv_localSlope`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L670).

**Theorem · Local slope of the height derivative.** First-order radial and second-order height matching give a locally Lipschitz derivative of the spline's height partial derivative. [`spline_xderiv_localSlope`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L691).

**Predicate · Locally Lipschitz derivative.** Local tameness means that the function has a derivative throughout some ball and that this derivative satisfies one Lipschitz bound there. [`TameAt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L718).

**Theorem · Bounds from a Lipschitz derivative.** A Lipschitz derivative on a ball gives a uniform derivative bound, a Lipschitz bound for the function, and a bound for its values on that ball. [`tame_bounds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L722).

**Theorem · Twice smooth gives local tameness.** Twice continuous differentiability at a point supplies a locally Lipschitz derivative there. [`tame_of_contDiffAt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L751).

**Theorem · A derivative bound gives tameness.** A differentiable function whose derivative is locally Lipschitz is locally tame at every point. [`tame_of_global`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L761).

**Theorem · Local derivative Lipschitz bound.** Local tameness supplies a neighbourhood on which the Fréchet derivative has a finite Lipschitz constant. [`tame_slope`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L769).

**Theorem · Tameness under local equality.** Two functions that agree near the point have the same local tameness property there. [`tame_congr`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L776).

**Theorem · Tameness of a sum.** The sum of two locally tame functions is locally tame at the same point. [`tame_add`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L786).

**Theorem · Tameness under a linear map.** Applying a continuous linear map preserves local tameness. [`tame_clm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L802).

**Theorem · Tameness of a composition.** Composing locally tame functions preserves local tameness at the corresponding points. [`tame_comp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L812).

**Theorem · Tameness of a product.** The product of two locally tame complex functions is locally tame. [`tame_mul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L849).

**Theorem · Tameness under negation.** Negating a locally tame function preserves local tameness. [`tame_neg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L884).

**Theorem · Tameness of a difference.** Subtracting locally tame functions preserves local tameness. [`tame_sub`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L887).

**Theorem · Smooth spatial coordinate.** Each spatial coordinate is smooth to every finite order. [`pin_coord`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L893).

**Theorem · Smooth norm away from the origin.** Spatial norm is smooth to every finite order away from the origin. [`pin_norm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L896).

**Theorem · Smooth normalized coordinate.** Every coordinate divided by spatial norm is smooth away from the origin. [`pin_ratio`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L899).

**Theorem · Smooth radial chart off the origin.** For valid chart parameters, the compactified radial coordinate is smooth away from the origin. [`pin_chartT`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L902).

**Theorem · Smooth height ratio off the origin.** The height-to-radius ratio is smooth away from the origin. [`pin_height`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L908).

**Theorem · Smooth decay factor off the origin.** For valid chart parameters, the decay factor is smooth away from the origin. [`pin_decay`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L911).

**Theorem · Smooth regularized logarithmic phase.** For valid chart parameters, the regularized logarithmic phase is smooth throughout space. [`pin_logPhase`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L923).

**Theorem · Smooth radial frame off the origin.** Every radial frame component is smooth away from the origin. [`pin_radial`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L930).

**Theorem · Smooth polar frame off the origin.** Every polynomial polar frame component is smooth away from the origin. [`pin_polar`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L933).

**Theorem · Smooth azimuthal frame off the origin.** Every polynomial azimuthal frame component is smooth away from the origin. [`pin_azim`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L940).

**Definition · Complex planar coordinate.** The planar coordinate combines the first two spatial coordinates into a complex number. [`pinPlane`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L946).

**Theorem · The planar coordinate is smooth.** The complex planar coordinate is smooth to every finite order. [`pinPlane_contDiff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L948).

**Theorem · Integer phase as a normalized power.** Away from zero, the integer angular phase equals the corresponding integer power of the normalized complex direction. [`pin_exp_arg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L956).

**Theorem · Smooth integer powers away from zero.** An integer power of a twice continuously differentiable complex function remains twice continuously differentiable where its base is nonzero. [`pin_zpow`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L968).

**Theorem · Smooth mode phase away from the axis.** For valid chart parameters, the mode phase is twice continuously differentiable away from the axis. [`pin_phase`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L976).

**Theorem · A coordinate vector as a scaled unit.** A vector with only one nonzero coordinate equals that coordinate times its coordinate unit vector. [`pin_single`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L998).

**Theorem · Assembling locally tame components.** A vector assembled from locally tame real components is locally tame at the same point. [`tame_ofComponents`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L1003).

**Theorem · A C² function is locally tame.** A twice continuously differentiable function of two real variables is locally tame at every point. [`pin_tame_all`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L1015).

**Theorem · The radial partial derivative is C².** The first-coordinate partial derivative of a C³ function of two real variables is C². [`pin_partial_t`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L1018).

**Theorem · The height partial derivative is C².** The second-coordinate partial derivative of a C³ function of two real variables is C². [`pin_partial_x`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L1031).

**Theorem · Tame radial derivatives of products.** Multiplying by a C³ factor preserves local tameness of the radial derivative under the stated differentiability and tameness hypotheses. [`pin_tderiv_mul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L1044).

**Theorem · Tame height derivatives of products.** Multiplying by a C³ factor preserves local tameness of the height derivative under the stated differentiability and tameness hypotheses. [`pin_xderiv_mul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L1060).

**Theorem · The radial core ratio is C².** For valid chart parameters, the regularized radial core ratio is twice continuously differentiable. [`pin_coreRatio`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L1076).

**Theorem · The polynomial radial scale is C².** The complex radial factor t times one minus t is twice continuously differentiable. [`pin_scaleA`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L1090).

**Theorem · The twisted scale coefficient is C².** For valid chart parameters, the phase-and-decay coefficient in the twisted scale derivative is twice continuously differentiable. [`pin_scaleB`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L1093).

**Theorem · The tensor weight is C³.** The product of the polynomial radial weight and a natural power of one minus height squared is three times continuously differentiable. [`pin_weight`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L1100).

**Theorem · The angular quadratic is C³.** One minus height squared, included into the complex numbers, is three times continuously differentiable. [`pin_q`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L1107).

**Theorem · The radial polynomial weight is C³.** Every radial polynomial weight is three times continuously differentiable. [`pin_p`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L1110).

**Theorem · First-order spline evaluation is tame.** A spline with at least first-order matching in both coordinates has locally tame evaluation. [`pin_spline`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L1115).

**Theorem · The spline's radial derivative is tame.** A spline with at least second-order radial and first-order height matching has a locally tame radial derivative. [`pin_spline_t`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L1120).

**Theorem · The spline's height derivative is tame.** A spline with at least first-order radial and second-order height matching has a locally tame height derivative. [`pin_spline_x`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L1125).

**Definition · Quadratic planar phase.** The planar phase map multiplies the integer angular exponential by squared planar modulus. [`planeMap`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L1131).

**Theorem · Differentiability of the planar phase.** For every integer phase index, the quadratic planar phase is differentiable throughout the complex plane. [`planeMap_diff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L1134).

**Theorem · Quadratic scaling of the planar phase.** Under positive real scaling, the planar phase map scales by the square of the scale. [`planeMap_scale`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L1137).

**Theorem · Linear scaling of the phase derivative.** The derivative of the quadratic planar phase scales linearly under positive real scaling. [`planeMap_fderiv_scale`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L1145).

**Theorem · Zero phase derivative at the origin.** The derivative of the quadratic planar phase at the complex origin is zero. [`planeMap_fderiv_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L1179).

**Theorem · Angular phase as a unit-direction power.** At a nonzero complex number, the integer angular exponential equals the integer power of its normalized direction. [`plane_exp_arg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L1185).

**Theorem · Twice smooth powers off their zero set.** Integer powers preserve twice continuous differentiability at a point where the complex base is nonzero. [`plane_zpow`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L1197).

**Theorem · The planar phase is C² away from zero.** The quadratic planar phase is twice continuously differentiable at every nonzero complex point. [`planeMap_smooth`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L1205).

**Theorem · Local slope of the planar derivative.** The derivative of the quadratic planar phase map is locally Lipschitz. [`planeSlope`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L1221).

**Theorem · Everywhere tame gives a C¹ function.** A function locally tame at every point is C¹ and has a locally Lipschitz derivative. [`tame_contDiff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L1297).

**Theorem · Recovering an assembled vector component.** An assembled vector evaluated at a coordinate returns the supplied coordinate value. [`orig_ofComponents_apply`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L1306).

**Theorem · Removing two radial powers.** The radial weight with exponent increased by two equals the original weight multiplied by the square of the radial coordinate. [`orig_weightPoly_two`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L1309).

**Theorem · Wave modes have radial and axis factors.** Every included nonzero reduced mode factors by one minus height squared and radial coordinate squared, with a locally tame quotient. [`orig_factor`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L1315).

**Definition · Regular quotient in radial coordinates.** The origin quotient combines the regularized radial decay and phase with the three reduced quotient components in normalized spatial directions. [`orProf`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L1453).

**Theorem · The origin quotient is locally tame.** Locally tame reduced quotients produce a locally tame origin profile at every nonnegative radial coordinate. [`orProf_tame`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L1461).

**Theorem · Angular cancellation as a norm ratio.** Away from the origin, one minus the squared height ratio is squared planar norm divided by squared spatial norm. [`orig_one_sub_height`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L1506).

**Theorem · Separating the quadratic planar phase.** The angular and squared radial factors separate the full mode phase into a quadratic planar phase and a regular radial factor. [`orig_phase_factor`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L1521).

**Theorem · A regularized product for a wave.** After extracting radial and axis factors, each nonzero spatial component equals the real part of the quadratic planar phase times the regular origin quotient. [`orig_key`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L1546).

**Definition · A wave profile with scale separated.** The scaled wave reconstructs its vector components from the quadratic planar phase and the origin quotient at scaled radius and normalized direction. [`scaledWave`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L1568).

**Theorem · Neighbourhood form of local tameness.** Local tameness supplies a neighbourhood of differentiability on which the derivative is Lipschitz. [`tame_region`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L1572).

**Theorem · Norm of the inverse-scale spatial map.** For positive scale, the product map with zero scale coordinate and inverse-scaled spatial coordinate has operator norm at most inverse scale. [`scaleT_norm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L1581).

**Theorem · Differentiating a quadratic rescaling.** A function represented by scale squared times a differentiable profile has the displayed derivative obtained by inverse spatial scaling and the chain rule. [`scaled_hasFDerivAt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L1589).

**Theorem · Quadratic rescaling controls the origin.** A function vanishing at zero with the stated quadratic scaling and uniformly local profile regularity is differentiable near zero and has a Lipschitz derivative there. [`scaled_fderiv_slopeBound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L1607).

**Theorem · Quadratic profile for a nonzero mode.** Each included nonzero mode vanishes at the origin and has a quadratic scaled profile with neighbourhood differentiability and Lipschitz derivative on the fixed annulus. [`modeFieldOf_scaledProfile_wave`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L1716).

**Theorem · Positive lower bound for a finite list.** A finite list of positive reals admits a common strictly positive lower bound. [`divd_pos_list_lower`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L1766).

**Theorem · First substitution in a variable product.** Fixing the first coordinate of a polynomial times a variable substitutes that variable into the product. [`divd_atFirst_mul_X`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L1777).

**Theorem · A radial remainder has a radial factor.** Subtracting evaluation at first coordinate zero leaves a polynomial divisible by the first variable. [`divd_sub_atFirst_dvd`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L1782).

**Theorem · First substitution preserves sums.** Fixing the first coordinate preserves addition of polynomials. [`divd_atFirst_add`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L1803).

**Theorem · Second substitution preserves sums.** Fixing the second coordinate preserves addition of polynomials. [`divd_atSecond_add`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L1807).

**Theorem · Substitution preserves a radial factor.** Fixing the second coordinate commutes with multiplication by the first polynomial variable. [`divd_atSecond_X0_mul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L1811).

**Theorem · The substituted zero polynomial is zero.** Fixing the first coordinate of the zero polynomial gives zero. [`divd_atFirst_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L1815).

**Theorem · Iterated height derivatives are additive.** Every iterated second-coordinate polynomial derivative preserves addition. [`divd_xDeriv_add`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L1818).

**Theorem · Height derivatives keep radial factors.** Iterated second-coordinate differentiation commutes with multiplication by the first polynomial variable. [`divd_xDeriv_X0_mul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L1826).

**Theorem · Partial derivative after substitution.** The second-coordinate partial derivative commutes with fixing the first coordinate. [`divd_pderiv_atFirst`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L1837).

**Theorem · Iterated derivative after substitution.** Every iterated second-coordinate derivative commutes with fixing the first coordinate. [`divd_xDeriv_atFirst`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L1847).

**Theorem · The two coordinate substitutions commute.** Fixing the first and second polynomial coordinates gives the same result in either order. [`divd_atSecond_atFirst`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L1855).

**Theorem · A radial factor after height operations.** After extracting a first-coordinate factor, height differentiation and substitution preserve the corresponding radial-remainder factorization. [`divd_split`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L1862).

**Theorem · Splitting a spline's first radial row.** Near the first radial endpoint, a spline equals its value at zero plus the radial coordinate times a spline quotient with the stated matching orders. [`spline_firstRow_split`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L1875).

**Theorem · Removing one radial factor.** The radial weight with first exponent one equals the radial coordinate times the weight with first exponent zero. [`weightPoly_one_split`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L1921).

**Theorem · The stream amplitude at radial zero.** For an included mean mode, the stream spline at radial zero equals the guard-stream coefficient times height. [`divd_stream_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L1926).

**Theorem · The swirl amplitude at radial zero.** For an included mean mode, the swirl spline at radial zero equals the guard-swirl coefficient. [`divd_swirl_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L1957).

**Definition · Finite geometric endpoint sum.** The endpoint sum adds the first e natural powers of one minus the radial coordinate. [`geomSumOneSub`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L1980).

**Theorem · The radial weight as a linear remainder.** The zero-order radial weight equals one minus the radial coordinate times its finite geometric endpoint sum. [`divd_w_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L1982).

**Definition · Leading reduced mean components.** The leading mean vector records the explicit guard-stream and guard-swirl polynomials in height. [`meanLeading`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L1991).

**Definition · Remainder of the reduced mean mode.** The mean remainder combines the spline quotients, endpoint geometric sum and radial derivative after removing the leading mean term. [`meanRemainder`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L1994).

**Theorem · A linear-plus-quadratic mean expansion.** Near the origin, each reduced mean component is radial coordinate times its leading term plus radial coordinate squared times the displayed remainder. [`divd_reduced_split`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L2003).

**Definition · Linear spatial part of the mean field.** The leading spatial mean part combines planar contraction and rotation with twice the guard-stream expansion in height. [`meanLinearPart`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L2079).

**Definition · The leading mean as a linear map.** The leading mean field is encoded as a real linear map after division by the chart length. [`meanLinearMap`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L2083).

**Definition · The continuous leading mean map.** The finite-dimensional leading mean linear map is packaged as a continuous linear map. [`meanLinearCLM`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L2094).

**Theorem · Evaluating the leading mean map.** Each coordinate of the leading mean map is the corresponding mean linear part divided by the chart length. [`meanLinearCLM_apply`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L2097).

**Theorem · The leading mean coordinates are smooth.** Each coordinate of the mean linear part is smooth to every finite order. [`meanLinearPart_contDiff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L2102).

**Definition · Radial decay divided by shifted radius.** The shifted decay factor multiplies radial decay by the inverse of radius plus the chart length. [`decayOverShift`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L2111).

**Theorem · Shifted decay is analytic at zero.** For valid chart parameters, the shifted decay factor is real analytic at the origin. [`decayOverShift_analytic`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L2113).

**Theorem · The divided decay slope is C².** The divided difference of the shifted decay factor from zero is twice continuously differentiable at every nonnegative radius. [`decaySlope_smooth`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L2129).

**Definition · Scaled quadratic remainder of the mean.** The scaled mean quotient combines the divided radial decay slope with the normalized-frame form of the reduced mean remainder. [`meanScaledQuotient`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L2151).

**Theorem · The mean after removing its linear part.** At sufficiently small chart radius, subtracting the leading linear map from the scaled mean leaves scale squared times the scaled mean quotient. [`divd_identity`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L2161).

**Theorem · The reduced mean remainder is tame.** The stated stream and swirl spline matching makes each component of the reduced mean remainder locally tame. [`divd_H_tame`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L2203).

**Theorem · The scaled mean quotient is tame.** The scaled mean quotient is locally tame at nonnegative scale and nonzero spatial direction under the stated spline and field conditions. [`divd_Fm_tame`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L2240).

**Theorem · Linear and quadratic mean profiles.** The included mean mode vanishes at zero and, after subtracting a continuous linear map, has a quadratic scaled profile with local derivative control on the fixed annulus. [`modeFieldOf_scaledProfile_mean`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L2298).

**Theorem · Wave derivative control near the origin.** The derivative of each included nonzero field mode is Lipschitz on some neighbourhood of the spatial origin. [`modeFieldOf_fderiv_slopeNearOrigin_wave`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L2364).

**Theorem · Mean derivative control near the origin.** The derivative of the included mean field is Lipschitz on some neighbourhood of the spatial origin. [`modeFieldOf_fderiv_slopeNearOrigin_mean`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPinSmoothLocalLeaves.lean#L2371).

### Breakdown.FracCell.GivenAuxPressureOpen

This file derives pressure-term bounds directly from polynomial pieces, including the angular cancellation and shellwise slope estimates needed for weak pressure gradients. **Reading context:** Appendix B: represented fields and the auxiliary estimates used by the profile, pin and adjoint reductions (B.1 and B.9–B.13).

**Definition · A closed radial shell.** The shell consists of spatial points whose norms lie between the given inner and outer radii. [`shellSet`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPressureOpen.lean#L20).

**Theorem · The complementary radial chart.** For valid chart parameters, the complementary radial chart is the chart length divided by radius plus that length. [`chartS_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPressureOpen.lean#L24).

**Theorem · The complementary chart lies in [0,1].** The complementary radial chart lies between zero and one for valid chart parameters. [`chartS_mem`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPressureOpen.lean#L31).

**Theorem · The radial chart is in the unit range.** The compactified radial chart lies between zero and one for valid chart parameters. [`chartT_mem`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPressureOpen.lean#L38).

**Theorem · A radial upper bound for the chart.** Beyond a nonnegative inner radius, the complementary radial chart is bounded by its value at that radius. [`chartS_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPressureOpen.lean#L44).

**Theorem · The decay factor is in the unit range.** The scalar decay factor lies between zero and one for valid chart parameters. [`decay_mem`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPressureOpen.lean#L50).

**Theorem · Quadratic decay of a pressure weight.** A radial pressure weight with outer exponent at least two is bounded outside an inner radius by the square of the complementary chart bound. [`radial_norm_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPressureOpen.lean#L56).

**Theorem · The angular weight is in the unit range.** The angular weight lies between zero and one. [`qOf_mem`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPressureOpen.lean#L71).

**Theorem · The phased angular power is bounded.** The product of a mode phase and any natural angular-weight power has norm at most one. [`angular_norm_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPressureOpen.lean#L85).

**Theorem · A difference bound for two products.** The difference of two complex products is bounded by one factor times the difference of the other, summed in the displayed order. [`mul_sub_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPressureOpen.lean#L96).

**Theorem · Finite sums retain a shell slope bound.** A finite sum of functions with shellwise Lipschitz estimates has a common Lipschitz estimate on the same set. [`sum_shell`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPressureOpen.lean#L102).

**Theorem · Coordinate size is bounded by norm.** The absolute value of a spatial coordinate is at most spatial norm. [`coord_abs_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPressureOpen.lean#L125).

**Theorem · Slope bound for the complementary chart.** Outside a positive inner radius, the complementary chart difference is bounded by distance times the displayed reciprocal-square radial constant. [`chartS_sub`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPressureOpen.lean#L129).

**Theorem · Slope bound for the radial chart.** Outside a positive inner radius, the radial chart has the same displayed distance bound as its complement. [`chartT_sub`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPressureOpen.lean#L147).

**Theorem · Slope bound for the height ratio.** Outside radius a greater than zero, the height ratio has distance bound two divided by a. [`ratio_sub`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPressureOpen.lean#L155).

**Theorem · Exponential is contractive below zero.** For nonpositive real inputs, the difference of their exponentials is at most the difference of the inputs in absolute value. [`exp_sub_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPressureOpen.lean#L177).

**Theorem · Logarithm on a positive lower range.** For inputs bounded below by a positive constant, logarithmic differences are bounded by input differences divided by that constant. [`log_sub_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPressureOpen.lean#L191).

**Theorem · A real-power difference bound.** On a positive interval below one, a nonnegative real power has the displayed difference bound using its exponent and the lower endpoint. [`rpow_sub_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPressureOpen.lean#L204).

**Theorem · A natural-power difference bound.** On the real unit interval in absolute value, the nth power has difference bound n times the input difference. [`pow_sub_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPressureOpen.lean#L215).

**Theorem · Slope of a radial pressure weight.** A radial pressure weight with outer exponent at least two has the displayed shellwise slope bound involving the radius ratio and quadratic chart decay. [`radial_shell`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPressureOpen.lean#L226).

**Theorem · Absolute bound for the height ratio.** The height-to-radius ratio has absolute value at most one. [`height_abs_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPressureOpen.lean#L358).

**Theorem · Complex phase exponentials have norm one.** Every complex exponential of an imaginary real phase has norm one. [`expI_norm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPressureOpen.lean#L365).

**Theorem · Complex phase difference bound.** The distance between two complex unit phase exponentials is bounded by the absolute difference of their real phases. [`expI_sub`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPressureOpen.lean#L368).

**Theorem · The logarithmic phase on a shell.** On a shell with positive inner radius, the logarithmic phase has distance bound outer radius divided by inner radius squared. [`logPhase_sub`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPressureOpen.lean#L377).

**Theorem · Natural powers on the unit circle.** The distance between nth powers of two unit complex numbers is at most n times their original distance. [`unit_pow_sub`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPressureOpen.lean#L409).

**Theorem · Integer powers on the unit circle.** The distance between integer powers of two unit complex numbers is bounded by the absolute exponent times their original distance. [`unit_zpow_sub`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPressureOpen.lean#L420).

**Theorem · Comparing normalized complex directions.** The difference of normalized nonzero complex directions, weighted by the first modulus, is bounded by twice the original complex distance. [`unit_sub_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPressureOpen.lean#L432).

**Theorem · Angular phase as a normalized power.** For nonzero complex input, its integer angular phase equals the corresponding power after division by its modulus. [`expArg_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPressureOpen.lean#L451).

**Theorem · Slope of the quadratic angular phase.** On a planar ball of radius B, the quadratic integer angular phase has the displayed Lipschitz bound proportional to B and the absolute phase index. [`plane_sub`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPressureOpen.lean#L462).

**Theorem · Planar norm is bounded by spatial norm.** The norm of the complex planar coordinate does not exceed the full spatial norm. [`plane_norm_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPressureOpen.lean#L521).

**Theorem · The angular weight as squared norm ratio.** Away from the origin, the angular weight equals squared planar norm divided by squared spatial norm. [`q_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPressureOpen.lean#L530).

**Theorem · Angular cancellation gives a shell slope.** The integer angular phase multiplied by the angular weight has the displayed shellwise distance bound proportional to outer radius over inner radius squared. [`planeField_sub`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPressureOpen.lean#L542).

**Theorem · A shell slope for the angular factor.** A mode phase multiplied by an angular weight power has the displayed shellwise slope bound when every nonzero mode has at least one angular factor. [`angular_shell`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPressureOpen.lean#L606).

**Theorem · Polynomial bound on the unit square.** Every complex polynomial has a common norm bound on the real unit square. [`poly_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPressureOpen.lean#L717).

**Theorem · A cell index is bounded by list length.** The selected cell index is at most the mesh-list length. [`cellIndex_le_len`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPressureOpen.lean#L728).

**Theorem · All spline pieces share a square bound.** All relevant spline pieces have one uniform bound when evaluated on the real unit square. [`pieces_bounded`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPressureOpen.lean#L733).

**Theorem · Counting before and through a breakpoint.** In an increasing list, exactly k entries precede its kth element and exactly k plus one are at or below it. [`count_sorted`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPressureOpen.lean#L749).

**Theorem · Indexing an interior breakpoint.** An interior mesh breakpoint has a positive valid cell index equal to one plus the count of earlier interior breaks, and the mesh lookup at that index recovers it. [`interior_facts`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPressureOpen.lean#L767).

**Theorem · The cell index from the left.** Approaching a point strictly from the left selects the number of interior breaks strictly below it. [`cellIndex_left`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPressureOpen.lean#L786).

**Theorem · The cell index from the right.** Approaching a point from the right eventually preserves its current cell index. [`cellIndex_right'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPressureOpen.lean#L801).

**Theorem · The cell index away from breakpoints.** Away from interior breakpoints, the selected cell is constant on a neighbourhood. [`cellIndex_off`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPressureOpen.lean#L815).

**Theorem · A slope bound across joined intervals.** A piecewise differentiable function with matching join values and a common derivative bound has that same slope bound across the unit interval. [`slope_one`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPressureOpen.lean#L830).

**Definition · Polynomial evaluation at a real pair.** The polynomial evaluator substitutes the two real coordinates into its complex variables. [`evQ`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPressureOpen.lean#L870).

**Theorem · Polynomial evaluation is smooth.** Polynomial evaluation on real coordinate pairs is smooth. [`evQ_contDiff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPressureOpen.lean#L872).

**Theorem · Evaluation after coordinate substitution.** Evaluating a substituted polynomial equals evaluating it on the already evaluated substitutions. [`eval_bind_pair`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPressureOpen.lean#L875).

**Theorem · Fixing the first coordinate.** Substitution of a real first coordinate before evaluation gives evaluation at that fixed first coordinate. [`evQ_atFirst`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPressureOpen.lean#L882).

**Theorem · Fixing the second coordinate.** Substitution of a real second coordinate before evaluation gives evaluation at that fixed second coordinate. [`evQ_atSecond`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPressureOpen.lean#L889).

**Theorem · Equal values on a radial join.** Polynomials equal after fixing the first coordinate have equal evaluations on that radial join. [`join_first`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPressureOpen.lean#L896).

**Theorem · Equal values on a height join.** Polynomials equal after fixing the second coordinate have equal evaluations on that height join. [`join_second`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPressureOpen.lean#L901).

**Theorem · Derivative bound on the unit ball.** The derivative of a polynomial evaluator is uniformly bounded on the closed unit ball. [`dbound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPressureOpen.lean#L906).

**Theorem · A common bound for piece derivatives.** All relevant spline-piece derivatives have one common bound on the closed unit ball. [`dbound_all`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPressureOpen.lean#L912).

**Theorem · The selected cell index is valid.** For a mesh beginning at zero and ending at one, every selected cell index is below its cell count. [`cellIndex_lt_count`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPressureOpen.lean#L920).

**Theorem · A unit-square pair has norm at most one.** A real pair with both coordinates between zero and one has product norm at most one. [`pair_norm_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPressureOpen.lean#L931).

**Theorem · Slope of half-spline evaluation.** A continuous even spline has one Lipschitz bound on the unit square measured by the sum of coordinate differences. [`halfEval_slope`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPressureOpen.lean#L939).

**Theorem · A shell slope for the spline shape.** A continuous even spline composed with the chart coordinates has a shellwise slope bound proportional to inverse inner radius. [`shape_shell`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPressureOpen.lean#L999).

**Theorem · The chart spline shape is bounded.** An even spline evaluated at the radial chart and height ratio has a uniform spatial norm bound. [`shape_bounded`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPressureOpen.lean#L1024).

**Theorem · A shell slope for each pressure term.** A valid pressure term with at least quadratic radial decay and the required angular factor has the displayed shellwise Lipschitz estimate. [`term_shell`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPressureOpen.lean#L1034).

**Theorem · Pressure is Lipschitz on closed annuli.** Pressure constructed from valid pressure data has a finite Lipschitz constant on every annulus with positive inner radius. [`pressure_annulusSlope`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPressureOpen.lean#L1089).

**Theorem · Weighted slopes of pressure terms.** A valid pressure term is differentiable almost everywhere and its derivative is bounded by a constant times the squared complementary chart divided by radius. [`term_slope`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxPressureOpen.lean#L1129).

### Breakdown.FracCell.GivenAuxRingModeWeak

This file builds cylindrical single-mode tests, tracks the frequency shifts under differentiation, and uses Fourier uniqueness to recover pointwise finite-mode representatives of weak derivatives. **Reading context:** Appendix B: represented fields and the auxiliary estimates used by the profile, pin and adjoint reductions (B.1 and B.9–B.13).

**Definition · An integer angular exponential.** The angular wave is the complex exponential with the given integer frequency. [`wave`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L15).

**Theorem · Derivative of an angular wave.** Differentiating an angular wave multiplies it by its integer frequency and the imaginary unit. [`wave_deriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L17).

**Theorem · Angular waves are smooth.** Every integer angular wave is smooth. [`wave_cd`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L25).

**Theorem · Angular waves have period two pi.** Every integer angular wave is periodic with period two pi. [`wave_per`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L29).

**Theorem · Multiplication adds wave frequencies.** The product of angular waves is the wave with the sum of their frequencies. [`wave_mul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L36).

**Theorem · The positive unit-frequency wave.** The frequency-one wave equals cosine plus the imaginary unit times sine. [`wave_one`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L43).

**Theorem · The negative unit-frequency wave.** The frequency-minus-one wave equals cosine minus the imaginary unit times sine. [`wave_neg_one`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L49).

**Definition · A cylindrical test with one angular mode.** The cylindrical lift multiplies a radius-height test profile by a single angular wave. [`cp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L56).

**Predicate · A smooth test supported off the axis.** A good cylindrical profile is smooth, compactly supported, and supported only at strictly positive radius. [`Good`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L58).

**Theorem · Continuous cylindrical coordinates.** The map sending a spatial point to cylindrical radius and height is continuous. [`pair_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L60).

**Theorem · Cylindrical tests vanish near the axis.** A good cylindrical test agrees with zero on a neighbourhood of each point whose cylindrical radius is zero. [`cp_near_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L63).

**Theorem · A lifted cylindrical test is smooth.** The single-mode lift of a good cylindrical profile is smooth throughout space. [`cp_cd`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L70).

**Theorem · Compact support of a lifted test.** The single-mode lift of a good cylindrical profile is compactly supported. [`cp_csupp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L87).

**Theorem · A cylindrical test on a ring.** At positive radius, a lifted cylindrical test equals its radius-height profile times its angular wave. [`cp_cyl`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L105).

**Theorem · Recovering a point from cylindrical data.** A point of positive cylindrical radius is recovered from its radius, planar argument and height. [`cyl_self`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L109).

**Theorem · Cylindrical tests vanish on the axis.** The single-mode lift of a good profile is zero wherever cylindrical radius is not positive. [`cp_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L125).

**Theorem · The test derivative is zero on the axis.** The derivative of a lifted good cylindrical profile is zero wherever cylindrical radius is not positive. [`cp_fderiv_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L128).

**Theorem · Local support and smoothness give a test.** A profile smooth on a good profile's support and locally zero outside it is itself a good cylindrical profile. [`good_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L132).

**Theorem · The complement of support is open.** A point outside a function's topological support has a neighbourhood disjoint from that support. [`near_zero_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L144).

**Definition · Profile for raising the angular mode.** The raising profile is the radial derivative minus frequency times the profile divided by radius. [`plusF`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L148).

**Definition · Profile for lowering the angular mode.** The lowering profile is the radial derivative plus frequency times the profile divided by radius. [`minusF`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L150).

**Definition · Height derivative of the test profile.** The height profile is the derivative of the cylindrical test profile in its height direction. [`heightF`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L152).

**Theorem · Smooth directional profile derivatives.** Every fixed directional derivative of a good cylindrical profile is smooth. [`fd_cd`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L154).

**Theorem · Dividing a profile by positive radius.** A good profile divided by radius is smooth at every point of positive radius. [`quot_cdAt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L157).

**Theorem · Raising preserves good test profiles.** The angular raising profile of a good cylindrical profile is good. [`good_plus`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L161).

**Theorem · Lowering preserves good test profiles.** The angular lowering profile of a good cylindrical profile is good. [`good_minus`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L167).

**Theorem · Height derivatives remain good tests.** The height derivative of a good cylindrical profile is good. [`good_height`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L173).

**Theorem · Good profiles are closed under addition.** The sum of two good cylindrical profiles is good. [`good_add`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L178).

**Theorem · Good profiles are closed under scaling.** Multiplying a good cylindrical profile by a complex constant preserves its goodness. [`good_smul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L184).

**Theorem · A cylindrical point in the radial frame.** A cylindrical point is its radius times the radial unit vector plus its height coordinate vector. [`cyl_radial`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L187).

**Theorem · Changing only the cylindrical height.** Changing the height of a cylindrical point adds that height times the vertical unit vector. [`cyl_height`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L190).

**Theorem · The first Cartesian direction.** The first coordinate unit vector is cosine times the radial direction minus sine times the angular direction. [`e0_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L193).

**Theorem · The second Cartesian direction.** The second coordinate unit vector is sine times the radial direction plus cosine times the angular direction. [`e1_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L196).

**Theorem · Radial derivative of a cylindrical test.** The radial derivative of a lifted test is the radial profile derivative times the unchanged angular wave. [`d_rad`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L199).

**Theorem · Height derivative of a cylindrical test.** The vertical derivative of a lifted test is the height profile derivative times the unchanged angular wave. [`d_height`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L219).

**Theorem · Angular derivative of a cylindrical test.** At positive radius, the angular-direction derivative multiplies the lifted test by frequency times the imaginary unit divided by radius. [`d_ang`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L239).

**Theorem · The planar derivative raises frequency.** The first Cartesian derivative plus the imaginary unit times the second equals the raising profile lifted at the next angular frequency. [`plus_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L253).

**Theorem · Conjugate derivative lowers frequency.** The first Cartesian derivative minus the imaginary unit times the second equals the lowering profile lifted at the preceding angular frequency. [`minus_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L271).

**Theorem · Height derivatives preserve frequency.** The vertical derivative lifts the height profile at the same angular frequency. [`height_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L289).

**Theorem · Lifting preserves addition.** The cylindrical lift of a sum of profiles is the sum of their lifts at the same frequency. [`cp_add`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L302).

**Theorem · Lifting preserves complex scaling.** Multiplying a profile by a complex constant multiplies its cylindrical lift by that constant. [`cp_smul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L305).

**Theorem · First derivative as adjacent modes.** The first Cartesian derivative of a lifted test is half the sum of its raising and lowering lifts. [`d0_cp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L308).

**Theorem · Second derivative as adjacent modes.** The second Cartesian derivative of a lifted test is minus the imaginary unit over two times the difference of its raising and lowering lifts. [`d1_cp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L317).

**Theorem · Derivative of a linear combination.** The derivative of the displayed constant complex linear combination is the same combination of the two derivatives. [`fd_comb`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L327).

**Theorem · The second iterated derivative formula.** For a smooth complex field, its second iterated derivative equals differentiation of its first directional derivative in the displayed order. [`second`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L335).

**Definition · The complex sum of second partials.** The complex Laplacian expression sums the second iterated derivative along the three coordinate directions. [`sumSecondC`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L344).

**Theorem · The Laplacian preserves frequency.** The sum of second partials of a lifted good test is another good cylindrical test at the same frequency. [`sumSecond_cp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L346).

**Theorem · Nonzero waves integrate to zero.** Every nonzero integer wave has zero integral over a full angular period. [`wave_int`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L376).

**Theorem · Angular waves are interval integrable.** Every integer angular wave is integrable on every finite interval. [`wave_ii`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L386).

**Theorem · Projection outside both supports.** Projecting a sum of two finite indexed phase families onto a frequency outside both image sets gives zero. [`two_sum_mode`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L389).

**Theorem · Conjugation reverses frequency.** The complex conjugate of an angular wave is the wave with opposite frequency. [`wave_conj`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L407).

**Theorem · Unsupported real-part modes vanish.** A real part of a finite phase sum has zero angular projection outside the original and reflected frequency sets. [`re_mode`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L413).

**Theorem · Unsupported imaginary-part modes vanish.** An imaginary part of a finite phase sum has zero angular projection outside the original and reflected frequency sets. [`im_mode`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L423).

**Theorem · Linear maps preserve local integrability.** A continuous linear map sends locally integrable fields to locally integrable fields. [`loc_comp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L439).

**Theorem · Local integrability under inclusion.** Including a locally integrable real field into the complex numbers preserves local integrability. [`loc_ofReal`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L444).

**Theorem · Vector components are locally integrable.** Each coordinate of a locally integrable vector field is locally integrable. [`loc_coord`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L448).

**Theorem · Integrability of cylindrical pairings.** A locally integrable complex field has integrable product with every lifted good cylindrical test. [`cpF_int`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L452).

**Theorem · Zero ring projections give zero pairings.** If the relevant angular projection vanishes on every positive-radius ring, its pairing with any matching cylindrical test is zero. [`int_cp_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L457).

**Theorem · Combining two zero cylindrical pairings.** The displayed complex linear combination of two cylindrical test pairings is zero when each pairing is zero. [`int_two_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L469).

**Definition · The angularly weighted scalar field.** The scalar field is included into the complex numbers and multiplied by a fixed angular wave. [`kernW`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L479).

**Theorem · Real tests give good complex profiles.** A smooth compactly supported real test in the positive-radius half-plane gives a good complex cylindrical profile. [`good_real`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L481).

**Theorem · Zero test pairings force zero ring modes.** If all real cylindrical test pairings vanish, the corresponding angular projection vanishes for almost every positive-radius and height pair. [`mode_of_probe`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L486).

**Theorem · Unsupported component modes vanish.** Each real coordinate of a finite vector ring sum has zero projection outside the original and reflected support sets. [`comp_mode`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L541).

**Theorem · Negative phase as the opposite wave.** The complex exponential with negative integer phase is the angular wave of opposite frequency. [`exp_wave`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L552).

**Theorem · Complex integrals from their components.** Integrable complex functions have equal integrals when their real-part and imaginary-part integrals agree. [`cplx`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L555).

**Theorem · Real parts of smooth fields are smooth.** The real part of a smooth complex field is smooth. [`re_cd`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L559).

**Theorem · Smooth imaginary parts.** The imaginary part of a smooth complex field is smooth. [`im_cd`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L562).

**Theorem · Differentiation commutes with real parts.** For a smooth complex field, taking the real part commutes with its directional Fréchet derivative. [`fd_re`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L565).

**Theorem · Derivative of the imaginary part.** For a smooth complex field, taking the imaginary part commutes with its directional Fréchet derivative. [`fd_im`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L571).

**Theorem · Second derivative of the real part.** The second iterated derivative of a smooth complex field commutes with taking its real part. [`it_re`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L577).

**Theorem · Second derivative of the imaginary part.** The second iterated derivative of a smooth complex field commutes with taking its imaginary part. [`it_im`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L584).

**Theorem · A coordinate as an inner product.** Pairing a vector with a coordinate unit vector returns that coordinate. [`inner_unit`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L591).

**Theorem · The Laplacian of a coordinate test field.** The sum of second partials of a scalar test times a coordinate unit vector is the scalar Laplacian times that unit vector. [`sumSecond_smul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L594).

**Theorem · Negative trace against complex tests.** A weak negative trace satisfies the displayed componentwise complex-test integration-by-parts identity when the two integrands are integrable. [`weak_neg_c`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L605).

**Theorem · Weak gradient against complex tests.** A weak scalar gradient satisfies the displayed coordinate integration-by-parts identity against smooth compactly supported complex tests with integrable pairings. [`weak_grad_c`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L632).

**Theorem · Derivative of a coordinate-valued test.** The derivative of a scalar test times a coordinate unit vector is the scalar derivative followed by the coordinate injection. [`fd_smul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L654).

**Theorem · Weak divergence against complex tests.** A weak matrix divergence satisfies componentwise integration by parts against smooth compactly supported complex tests under the displayed integrability assumptions. [`weak_div_c`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L662).

**Theorem · Recognizing a neighbouring frequency.** If a frequency shifted by minus one, zero or one lies in the support, the original frequency lies in the support enlarged by those three shifts. [`shift_mem`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L694).

**Theorem · First derivative as adjacent modes.** Pointwise, the first Cartesian derivative is half the sum of the raised and lowered cylindrical tests. [`d0'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L699).

**Theorem · Second derivative as adjacent modes.** Pointwise, the second Cartesian derivative is minus the imaginary unit over two times the difference of raised and lowered cylindrical tests. [`d1'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L702).

**Theorem · The height derivative keeps its mode.** Pointwise, the vertical derivative is the lifted height profile with unchanged frequency. [`d2'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L705).

**Theorem · Zero modes give zero derivative pairings.** If the target angular projection and both neighbouring projections vanish on every positive-radius ring, all coordinate derivative test pairings vanish. [`d_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L708).

**Theorem · Derivative test pairings are integrable.** A locally integrable field has integrable pairing with every directional derivative of a lifted good cylindrical test. [`dF_int`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L738).

**Theorem · Circle Fourier modes equal angular waves.** The standard Fourier character on the circle of length two pi equals the displayed integer angular wave. [`wave_mode`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L752).

**Theorem · Every angular wave has unit norm.** Every integer angular wave has complex norm one. [`norm_wave`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L760).

**Theorem · Fourier uniqueness almost everywhere.** An integrable function on the open angular period whose pairings with every integer wave vanish is zero almost everywhere. [`circle_unique`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L765).

**Theorem · Shifting a periodic integration interval.** For a two-pi-periodic function, the integral over zero to two pi equals the integral over the open interval from minus pi to pi. [`shift_int`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L823).

**Theorem · Zero integral of nonzero waves.** A nonzero integer wave has zero integral over the open interval from minus pi to pi. [`wave_ioo`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L830).

**Theorem · The zero-frequency wave is one.** The zero-frequency angular wave is constantly one. [`wave_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L833).

**Theorem · Integral of the zero-frequency wave.** The zero-frequency wave integrates to two pi over the open angular period. [`wave_ioo_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L835).

**Theorem · Addition of angles multiplies waves.** The wave at a sum of angles equals the product of the waves at those angles. [`wave_add`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L845).

**Theorem · A wave is integrable on the open period.** Every integer wave is integrable on the open interval from minus pi to pi. [`wave_ion`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L848).

**Theorem · A real part is a reflected phase sum.** The real part of a finite phase sum has a finite phase representation on the union of the original and reflected supports. [`re_rep`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L851).

**Theorem · A wave in cylindrical coordinates.** At positive radius, the angular wave computed from the planar argument of a cylindrical point equals the wave at its supplied angle. [`wave_cyl`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L880).

**Theorem · Periodicity of cylindrical coordinates.** Adding two pi to a cylindrical point's angle leaves the point unchanged. [`cyl_per`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L883).

**Theorem · A finite ring representative.** A locally integrable real field with almost-everywhere vanishing modes outside a finite set has an almost-everywhere equal representative that is a finite phase sum on every ring. [`ringModes_unique`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L894).

**Reader note.** The theorem changes the representative on a null set before asserting a pointwise finite expansion on every ring.

**Theorem · Mode bounds for weak negative traces.** A locally integrable weak negative trace of a finite ring sum has vanishing coordinate modes outside the original and reflected supports for almost every positive-radius ring. [`negTrace_ringModes`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L1029).

**Theorem · Weak gradients add neighbouring modes.** A locally integrable weak gradient of a finite scalar ring sum has vanishing coordinate modes outside the support shifted by minus one, zero and one, almost everywhere in radius and height. [`scalarGradient_ringModes`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L1053).

**Theorem · Weak divergence adds neighbouring modes.** A locally integrable weak matrix divergence has vanishing modes outside the reflected column support enlarged by the three neighbouring shifts, almost everywhere in radius and height. [`matrixDivergence_ringModes`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxRingModeWeak.lean#L1087).

### Breakdown.FracCell.GivenAuxShift

This file supplies the weighted tangent-adjoint product estimates required for the parameter-shift contribution. **Reading context:** Appendix B: represented fields and the auxiliary estimates used by the profile, pin and adjoint reductions (B.1 and B.9–B.13).

**Theorem · Integrable tangent-adjoint products.** Valid profile and auxiliary data give integrability of the squared tangent-adjoint product and of its radius-weighted derivative counterpart. [`shiftWeighted_of_given`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxShift.lean#L18).

### Breakdown.FracCell.GivenAuxShiftParts

This file proves the general decay lemma that makes the parameter-shift products integrable. **Reading context:** Appendix B: represented fields and the auxiliary estimates used by the profile, pin and adjoint reductions (B.1 and B.9–B.13).

**Theorem · Decay controls weighted products.** A C¹ field with inverse-radius decay and inverse-square derivative decay has both displayed squared products integrable against any L² field. [`weighted_pair_integrable`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxShiftParts.lean#L14).

### Breakdown.FracCell.GivenModelCover

This module computes the Fourier modes of piecewise polynomial model fields and rows, proving polynomial representation, class coverage and tail regularity inside cells. **Reading context:** Appendix B: the polynomial cell models and rows used in the local estimates and finite assembly (B.1 and B.4–B.6).

**Theorem · Integral of a circle harmonic.** For positive symmetry order, a circle exponential integrates to 2π at zero mode and to zero otherwise. [`exp_circle`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L21).

**Theorem · Real harmonics split into two modes.** Multiplying a real harmonic of frequency k by the Fourier phase for n splits it into half its amplitude at k−n and half its conjugate amplitude at −k−n. [`term_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L47).

**Theorem · Fourier coefficient of a real sum.** The normalized circle integral of a finite real harmonic sum selects its matching coefficients and conjugates at opposite frequencies. [`mode_re`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L76).

**Theorem · Recover radius and height.** At nonnegative radius and height, cylindrical coordinates recover those inputs and the absolute height equals the height. [`cyl_coords`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L105).

**Theorem · The angle is determined modulo 2π.** At positive radius, the recovered cylindrical angle differs from the input angle by an integer multiple of 2π. [`angle_cyl`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L120).

**Theorem · The frame ignores full angle turns.** At positive radius, the frame built from the recovered angle equals the frame at the input angle. [`frame_angle`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L133).

**Theorem · A harmonic ignores full angle turns.** Integer harmonics evaluated at the recovered cylindrical angle equal those evaluated at the input angle. [`exp_angle`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L138).

**Theorem · The cylindrical frame is orthonormal.** Frame vectors have inner product 1 for equal coordinate indices and 0 otherwise. [`frame_orth`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L150).

**Theorem · Recover vector frame coordinates.** Converting frame coordinates to a Cartesian vector and reading them in the same frame recovers the original coordinates. [`frameVec_cart`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L156).

**Theorem · Recover matrix frame coordinates.** Converting a frame matrix to a Cartesian operator and reading it in the same frame recovers the matrix entries. [`frameMat_cart`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L164).

**Theorem · Cell membership ignores the angle.** Points with equal cylindrical radius and absolute height belong to exactly the same mesh pieces. [`piece_iff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L172).

**Theorem · Region membership ignores the angle.** Points with equal cylindrical radius and absolute height have the same mesh-region membership. [`region_iff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L176).

**Theorem · Cartesian vectors ignore full turns.** At positive radius, Cartesian reconstruction is unchanged when the input angle is replaced by the recovered angle. [`cart_angle`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L181).

**Theorem · Cartesian operators ignore full turns.** At positive radius, operator reconstruction is unchanged when the input angle is replaced by the recovered angle. [`cartOp_angle`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L186).

**Theorem · Reflection signs above the plane.** At nonnegative cylindrical height, both vector and pseudovector reflection signs are 1. [`signs_up`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L191).

**Theorem · A harmonic field on a circle.** At positive radius and nonnegative height, the harmonic field is the real part of its finite exponential sum with doubled nonzero harmonics. [`harm_circle`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L198).

**Theorem · Vector fields in the circle frame.** Above the horizontal plane at positive radius, both vector and pseudovector frame components equal their scalar harmonic components. [`vec_circle`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L207).

**Theorem · Tensor fields in the circle frame.** Above the horizontal plane at positive radius, tensor and pseudotensor frame entries equal their scalar harmonic entries. [`mat_circle`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L215).

**Theorem · A mesh sum along a circle.** At nonnegative radius and height, a piecewise field uses cell membership at angle zero and evaluates its active pieces at the requested angle. [`piecewise_circle`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L224).

**Theorem · A vector component is an inner product.** A cylindrical vector component is its inner product with the corresponding frame vector. [`frameVec_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L234).

**Theorem · Vector components preserve finite sums.** Taking a cylindrical vector component commutes with a finite sum. [`frameVec_sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L237).

**Theorem · Vector components preserve a zero branch.** A cylindrical vector component commutes with choosing a vector or zero. [`frameVec_ite`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L241).

**Theorem · A matrix entry is an inner product.** A cylindrical matrix entry pairs the operator applied to the column frame vector with the row frame vector. [`frameMat_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L245).

**Theorem · Matrix entries preserve finite sums.** Taking a cylindrical matrix entry commutes with a finite sum of operators. [`frameMat_sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L248).

**Theorem · Matrix entries preserve a zero branch.** A cylindrical matrix entry commutes with choosing an operator or zero. [`frameMat_ite`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L252).

**Theorem · Combine cell and harmonic sums.** A finite sum of selected real harmonic sums equals one real harmonic sum indexed by cell and harmonic pairs. [`re_collect`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L256).

**Theorem · Extract a vector harmonic coefficient.** For positive symmetry order, the nth Fourier coefficient of a vector frame component is half the sum of amplitudes at frequency n and conjugate amplitudes at frequency −n. [`vec_mode`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L265).

**Theorem · Extract a matrix harmonic coefficient.** For positive symmetry order, the nth Fourier coefficient of a matrix frame entry is half the sum of amplitudes at frequency n and conjugate amplitudes at frequency −n. [`mat_mode`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L275).

**Definition · Weight of a model harmonic.** The harmonic weight is 1 at the zero harmonic and 2 at every nonzero harmonic. [`wt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L285).

**Definition · A selected cell harmonic coefficient.** The cell coefficient is its weighted polynomial value when the point lies in the selected mesh piece and is zero otherwise. [`cellCoef`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L288).

**Theorem · Modes of piecewise vector fields.** At positive radius and nonnegative height, the vector and pseudovector modes of a mesh field select its cell coefficients at the two frequency signs. [`vec_field_mode`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L292).

**Theorem · Modes of piecewise tensor fields.** At positive radius and nonnegative height, the tensor and pseudotensor modes of a mesh field select its cell coefficients at the two frequency signs. [`mat_field_mode`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L315).

**Theorem · Matrix modes respect circle equality.** Matrix fields that agree on a given circle have equal Fourier modes on that circle. [`modeMat_congr`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L340).

**Theorem · Vector modes respect circle equality.** Vector fields that agree on a given circle have equal Fourier modes on that circle. [`modeVec_congr`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L345).

**Theorem · A cell rectangle lifts to its solid.** Every angular lift of a point in a valid cell rectangle lies in the cell solid. [`cyl_mem_solid`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L350).

**Theorem · Strain inside the mesh region.** Inside the mesh region, the model strain equals the piecewise tensor assembled from its cell polynomials. [`strain_in`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L357).

**Theorem · Curl gradient inside the mesh region.** Inside the mesh region, the model curl gradient equals the piecewise pseudotensor assembled from its cell polynomials. [`curlGrad_in`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L363).

**Theorem · Absent frequencies give a zero sum.** If a mode matches neither sign of any listed harmonic, its selected coefficient sum is zero. [`sum_zero_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L369).

**Theorem · Finite sums preserve degree bounds.** A finite sum of bivariate polynomial functions with the same degree bounds retains those bounds. [`poly_sum'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L376).

**Theorem · Scaling preserves polynomial degree.** Multiplying a bivariate polynomial function by a complex scalar preserves its two degree bounds. [`poly_smul'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L392).

**Theorem · Addition preserves polynomial degrees.** Adding bivariate polynomial functions with the same degree bounds preserves those bounds. [`poly_add'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L402).

**Theorem · Zero has every polynomial degree bound.** The zero function belongs to the bivariate polynomial space for every pair of degree bounds. [`poly_zero'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L407).

**Theorem · Equality preserves polynomial membership.** A function pointwise equal to a bivariate polynomial function has the same polynomial degree bounds. [`poly_congr'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L409).

**Theorem · A constant choice preserves polynomials.** Choosing between a fixed bivariate polynomial function and zero preserves its degree bounds. [`poly_ite'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L414).

**Theorem · A monomial has the stated degrees.** A product of radial and height powers belongs to a bivariate polynomial space when each exponent is within its bound. [`poly_mon'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L420).

**Theorem · Enlarging the polynomial degree bounds.** A polynomial function remains in the polynomial space when both degree bounds are increased. [`poly_mono'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L435).

**Theorem · Product degree bounds add.** Multiplication of bivariate polynomial functions adds their radial and height degree bounds. [`poly_mul'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L445).

**Theorem · Conjugation preserves degree bounds.** Complex conjugation preserves the radial and height degree bounds of a bivariate polynomial function. [`poly_conj'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L464).

**Theorem · Cell polynomial evaluation has bounds.** A cell polynomial of degree d evaluates to a bivariate polynomial function of degree at most d in each coordinate. [`poly_eval'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L472).

**Theorem · Radius is a polynomial function.** The complex-valued radial coordinate has radial degree at most 1 and height degree at most 0. [`poly_fst'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L475).

**Theorem · Constants are polynomial functions.** Every constant complex function belongs to the bivariate polynomial space for every pair of degree bounds. [`poly_const'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L480).

**Theorem · An interior point selects one cell.** An interior point of a valid mesh cell belongs to precisely that cell solid and its selected mesh piece. [`interior_mem`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L486).

**Theorem · Interior cell coefficients simplify.** In a cell interior, the selected coefficient is the weighted polynomial for that cell and zero for every other cell. [`cellCoef_interior`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L519).

**Definition · Polynomial for an interior mode.** The interior mode polynomial selects the cell and combines its matching positive and conjugate negative harmonic coefficients. [`interiorPoly`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L529).

**Theorem · Interior modes have polynomial degrees.** The interior mode polynomial has the same radial and height degree bounds as its cell polynomials. [`interiorPoly_mem`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L536).

**Theorem · Vector modes are interior polynomials.** In a valid cell interior, vector and pseudovector modes equal the corresponding interior mode polynomial. [`vec_interior`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L543).

**Theorem · Tensor modes are interior polynomials.** In a valid cell interior, tensor and pseudotensor modes equal the corresponding interior mode polynomial. [`mat_interior`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L555).

**Definition · Polynomial form of modified radius.** The polynomial modified radius is 1 on an axis cell and the complex radial coordinate on other cells. [`rHatPoly`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L568).

**Theorem · Degree of modified radius.** The polynomial modified radius has radial degree at most 1 and height degree at most 0. [`rHatPoly_mem`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L570).

**Theorem · Modified radius in a cell interior.** Inside a valid radial cell interval, the modified radius equals its polynomial form. [`rHat_interior`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L576).

**Theorem · Subtraction preserves degree bounds.** Subtracting bivariate polynomial functions with the same degree bounds preserves those bounds. [`poly_sub'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L585).

**Theorem · Degree bounds for a cross product.** A cross product of polynomial vector components has degree bounds given by the sums of the input bounds. [`cross_poly`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L591).

**Theorem · Curl adjoint preserves degree bounds.** The algebraic curl-adjoint entries preserve the degree bounds of their polynomial vector components. [`curlAdj_poly`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L598).

**Theorem · Turn adjoint preserves degree bounds.** The inverse turn-adjoint operation preserves the degree bounds of polynomial vector components. [`turn_poly`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L603).

**Theorem · Multiplication by radius adds a degree.** Multiplying a bivariate polynomial function by radius increases its radial degree bound by 1. [`mulFst_poly`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L612).

**Definition · Polynomial for a mixed row mode.** The row mode polynomial combines mixing coefficients with profiles from the selected cell at the matching harmonic and its conjugate. [`rowPoly`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L615).

**Theorem · Mixed row modes have bounded degree.** A row mode polynomial has both degree bounds at most the row-data degree. [`rowPoly_mem`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L623).

**Theorem · Row modes are interior polynomials.** For positive symmetry order, a row field mode in a valid cell interior equals its row mode polynomial. [`row_interior`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L630).

**Theorem · Cylindrical angle is measurable.** The cylindrical angle is measurable. [`angle_meas'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L657).

**Theorem · Cylindrical radius is continuous.** The cylindrical radius is continuous. [`radius_cont'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L661).

**Theorem · Cylindrical height is continuous.** The cylindrical height is continuous. [`height_cont'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L665).

**Theorem · Cell polynomial evaluation is continuous.** A cell polynomial evaluates continuously in its radial and height coordinates. [`evalPoly_cont'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L669).

**Theorem · Harmonic fields are measurable.** Every finite harmonic field assembled from cell polynomials is measurable. [`harm_meas'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L673).

**Theorem · Reflection signs are measurable.** Both vector and pseudovector reflection signs are measurable functions of position. [`sign_meas'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L681).

**Theorem · Coordinate vectors vary continuously.** Placing a real number in one Cartesian coordinate defines a continuous vector-valued map. [`single_cont'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L690).

**Theorem · Frame vectors vary continuously.** Each cylindrical frame vector is continuous in its angle. [`frame_cont'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L698).

**Theorem · Signed harmonic entries are measurable.** The vector and pseudovector sign products times harmonic matrix entries are measurable. [`entry_meas'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L705).

**Theorem · Frame reconstruction is measurable.** A measurable angle and measurable matrix entries reconstruct an almost everywhere strongly measurable Cartesian operator field. [`cartOp_meas'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L711).

**Theorem · Tensor fields are measurable.** Tensor and pseudotensor fields assembled from cell polynomials are almost everywhere strongly measurable for the measure. [`tensor_meas'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L722).

**Theorem · Cell solids are measurable.** The solid associated with a cell box is measurable. [`solid_meas'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L727).

**Theorem · Selected mesh pieces are measurable.** Every selected mesh piece is measurable. [`piece_meas'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L735).

**Theorem · Piecewise assembly is measurable.** A mesh assembly of almost everywhere strongly measurable operator fields retains that measurability. [`piecewise_meas'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L739).

**Theorem · Frame vectors have norm one.** Every cylindrical frame vector has Euclidean norm 1. [`frame_norm'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L745).

**Theorem · An operator bound from its entries.** The norm of an operator reconstructed from a frame matrix is at most the sum of the absolute values of its entries. [`cartOp_norm'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L751).

**Theorem · Harmonic fields are bounded on cells.** A harmonic field is uniformly bounded over all angles above a valid cell rectangle. [`harm_bound'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L759).

**Theorem · Tensor fields are bounded on cells.** Tensor and pseudotensor fields are uniformly bounded over all angles above a valid cell rectangle. [`tensor_bound'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L776).

**Theorem · Bound a piecewise field by its pieces.** The norm of a piecewise operator field is at most the sum of the norms of all its cell fields. [`piecewise_bound'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L797).

**Theorem · Piecewise tensors have cell bounds.** A valid mesh gives uniform bounds for assembled tensor and pseudotensor fields over each cell and all angles. [`model_bound'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L802).

**Theorem · Inactive coefficients give a zero mode.** A selected coefficient sum vanishes if every summand either has unmatched frequency or has zero coefficient. [`sum_zero_or`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L820).

**Theorem · Classes cover active model harmonics.** For a valid cell-model instance with positive symmetry order, covering the active cell harmonics by the classes ensures that every nonzero coupling from a resolved mode to one outside the resolved set and band belongs to a class. [`classCover_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L826).

**Theorem · Auxiliary modes are cell polynomials.** For a valid positive-order model instance, a near-degree bound at least one above the column degree gives polynomial representatives for modified-radius times actuator-gradient and pin-field modes inside each cell. [`actuatorPoly_interior`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L903).

**Theorem · Row couplings are cell polynomials.** For valid positive-order model and row data, a degree bound at least the row degree plus model degree plus two gives cell-interior polynomial representatives for folded and velocity row couplings. [`rowPolynomial_interior`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L923).

**Theorem · The model supplies tail regularity.** A valid model instance with regular centre makes the strain, velocity and band group families tail-regular on each mesh cell. [`tailRegular_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelCover.lean#L1006).

### Breakdown.FracCell.GivenModelDefs

This module records the centre regularity and row signs needed to turn finite model data into analytic cell fields. **Reading context:** Appendix B: the polynomial cell models and rows used in the local estimates and finite assembly (B.1 and B.4–B.6).

**Predicate · Centre regularity conditions.** Centre regularity requires a continuously differentiable centre, an almost everywhere strongly measurable second-derivative field and symmetry of that field in its two directions. [`IsCentreRegular`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelDefs.lean#L32).

**Definition · Sign of a paired row.** The row sign is 1 for a positive row and −1 otherwise. [`pairSign`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelDefs.lean#L48).

**Definition · Signed row harmonic.** The row rotation mode is the harmonic multiplied by the symmetry order and the sign of the row. [`turnMode`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelDefs.lean#L50).

### Breakdown.FracCell.GivenModelMixClauses

This module proves that the row pairing and its inverse square root respect cell, harmonic and partner blocks, giving the orthonormal row mixing identities. **Reading context:** Appendix B: the polynomial cell models and rows used in the local estimates and finite assembly (B.1 and B.4–B.6).

**Theorem · Scaling a cell polynomial.** Multiplying every coefficient of a cell polynomial by a complex scalar multiplies its evaluation by that scalar. [`evalPoly_const_mul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelMixClauses.lean#L19).

**Theorem · Profile of a partner row.** At nonzero harmonic, the partner profile is the original profile multiplied by i or −i according to its sign. [`profile_partner`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelMixClauses.lean#L25).

**Theorem · Pairing vanishes across row blocks.** The test pairing vanishes when the two rows have different cells or different harmonics. [`pairing_eq_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelMixClauses.lean#L40).

**Theorem · Pairing inside a harmonic block.** Rows on the same cell with the same nonzero harmonic have pairing 2π times the radial-weighted integral of the real complex inner product of their polynomial profiles. [`pairing_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelMixClauses.lean#L45).

**Theorem · Pairing preserves each row block.** The test-pairing matrix commutes with the diagonal projection onto each cell and harmonic block. [`commute_proj`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelMixClauses.lean#L54).

**Theorem · Pairing respects partner signs.** For valid row data, moving the partner operation from one pairing argument to the other multiplies by the corresponding row signs, with sign one for zero harmonic. [`pairing_partner`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelMixClauses.lean#L66).

**Theorem · Pairing commutes with pairing of rows.** For valid row data, the test-pairing matrix commutes with the signed partner permutation. [`commute_partner`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelMixClauses.lean#L99).

**Theorem · Mixing is an inverse square root.** For a Hermitian pairing matrix, the mixing matrix is its continuous functional calculus value under x ↦ √(x⁻¹). [`mix_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelMixClauses.lean#L111).

**Theorem · Mixing normalizes the row pairing.** Valid row data give a mixing matrix that normalizes the test pairing to the identity, preserves cell and harmonic blocks and respects partner signs. [`mix_clauses`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelMixClauses.lean#L118).

### Breakdown.FracCell.GivenModelModel

This module assembles the analytic properties of the finite model fields, including symmetry, zero trace, support, integrability and finite harmonic support. **Reading context:** Appendix B: the polynomial cell models and rows used in the local estimates and finite assembly (B.1 and B.4–B.6).

**Theorem · The symmetric-part map is continuous.** Taking the symmetric part is continuous on linear operators. [`symPart_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModel.lean#L12).

**Theorem · Curl-gradient contraction is continuous.** The contraction defining the curl-gradient matrix is continuous in the second-derivative tensor. [`curlGradMatrix_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModel.lean#L17).

**Theorem · The symmetric part is symmetric.** The symmetric part of an operator is self-adjoint for the real inner product. [`symPart_symm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModel.lean#L22).

**Theorem · Cartesian unit vectors are orthonormal.** Two Cartesian unit vectors have inner product 1 when their indices agree and 0 otherwise. [`inner_unit`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModel.lean#L29).

**Theorem · Diagonal curl-gradient entries.** A diagonal curl-gradient entry equals the alternating sum of second-derivative coordinates. [`curlGrad_entry`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModel.lean#L32).

**Theorem · Symmetric second derivatives cancel.** A tensor symmetric in its derivative directions gives a curl-gradient matrix of trace zero. [`curlGrad_trace`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModel.lean#L39).

**Theorem · Trace is additive.** The coordinate trace of a sum of linear operators is the sum of their traces. [`trace_add`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModel.lean#L46).

**Theorem · The zero operator has trace zero.** The sum of the diagonal entries of the zero operator is zero. [`trace_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModel.lean#L50).

**Theorem · Harmonic assembly preserves zero trace.** If each polynomial coefficient matrix has zero trace, its assembled harmonic matrix has zero trace. [`harmonic_trace`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModel.lean#L53).

**Theorem · Vector and pseudovector signs combine.** The product of vector and pseudovector reflection signs equals −1 below the horizontal plane and 1 elsewhere. [`sign_prod`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModel.lean#L70).

**Theorem · Pseudotensor assembly has zero trace.** Polynomial matrices with zero trace produce a pseudotensor field with zero trace at every point. [`pseudoTensor_trace`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModel.lean#L82).

**Theorem · Symmetric coefficients give a tensor.** Symmetric polynomial coefficient matrices produce a pointwise self-adjoint tensor field. [`tensor_symm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModel.lean#L90).

**Theorem · Norm is bounded by radius plus height.** A spatial norm is at most cylindrical radius plus absolute cylindrical height. [`norm_le_parts`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModel.lean#L99).

**Theorem · A cell solid is bounded.** The solid associated with any cell box is bounded. [`solid_bdd`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModel.lean#L115).

**Theorem · The mesh region has finite volume.** A finite cell mesh has a region of finite volume. [`region_fin`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModel.lean#L120).

**Theorem · Bounded finite-support fields are Lᵖ.** An almost everywhere strongly measurable field bounded globally and vanishing off a measurable finite-volume set belongs to every Lᵖ space, including p=∞. [`memLp_of_bd`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModel.lean#L123).

**Theorem · Squared matrix entries vary continuously.** The sum of squared matrix entries is continuous in the operator. [`entrySq_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModel.lean#L135).

**Theorem · Entry energy from an operator bound.** An operator norm bound C gives an entry-square bound of 3C². [`entrySq_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModel.lean#L139).

**Theorem · The zero operator has zero entry energy.** The sum of squared entries of the zero operator is zero. [`entrySq_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModel.lean#L151).

**Theorem · Supported bounded matrix energy.** A strongly measurable, bounded matrix field vanishing outside a mesh region has integrable entry-square energy. [`integrable_entrySq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModel.lean#L153).

**Theorem · The model fields satisfy their clauses.** A valid model instance with regular centre satisfies the measurability, local bounds, exterior values, strain symmetry and zero curl-gradient trace clauses. [`model_clauses`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModel.lean#L171).

**Theorem · Auxiliary model fields are integrable.** A valid model instance supplies the actuator, actuator-gradient, pin-field and pin measurability, energy integrability and support clauses. [`modelAux_clauses`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModel.lean#L265).

**Theorem · The model fields obey reflection laws.** On a contained cell away from the horizontal plane, a model instance has the vector, pseudovector, tensor and auxiliary-field reflection laws. [`modelMirror_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModel.lean#L312).

**Theorem · Auxiliary modes have finite support.** If the selected mode set contains both signs of every model harmonic, all actuator-gradient and pin-field modes outside it vanish at nonzero radius. [`linearModes_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModel.lean#L365).

### Breakdown.FracCell.GivenModelModelFrame

This module builds Cartesian vectors and operators from cylindrical frame coefficients and proves the measurability, bounds and reflection rules needed for model assembly. **Reading context:** Appendix B: the polynomial cell models and rows used in the local estimates and finite assembly (B.1 and B.4–B.6).

**Theorem · The cylindrical frame is orthonormal.** Frame vectors have inner product 1 for equal coordinate indices and 0 otherwise. [`frameUnit_coord`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelFrame.lean#L11).

**Theorem · Frame vectors have norm one.** Every cylindrical frame vector has Euclidean norm 1. [`frameUnit_norm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelFrame.lean#L17).

**Theorem · Coordinate vectors vary continuously.** Placing a real number in one Cartesian coordinate defines a continuous vector-valued map. [`single_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelFrame.lean#L21).

**Theorem · Frame vectors vary continuously.** Each cylindrical frame vector is continuous in its angle. [`frameUnit_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelFrame.lean#L31).

**Theorem · Apply a frame matrix to a vector.** The Cartesian operator sums its frame entries times the input frame components in the output frame directions. [`cartOp_apply`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelFrame.lean#L37).

**Theorem · A symmetric frame matrix is self-adjoint.** A symmetric frame matrix reconstructs a self-adjoint Cartesian operator. [`cartOp_symm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelFrame.lean#L41).

**Theorem · A diagonal entry is an inner product.** A diagonal operator entry is its action on the corresponding Cartesian unit vector paired with that vector. [`entry_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelFrame.lean#L49).

**Theorem · Trace is unchanged by the frame.** The Cartesian trace of a reconstructed operator equals the sum of its frame diagonal entries. [`cartOp_trace`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelFrame.lean#L52).

**Theorem · Operator reconstruction is continuous.** Cartesian operator reconstruction is jointly continuous in its angle and matrix entries. [`cartOp_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelFrame.lean#L62).

**Theorem · Vector reconstruction is continuous.** Cartesian vector reconstruction is jointly continuous in its angle and frame coordinates. [`cart_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelFrame.lean#L67).

**Definition · A real finite harmonic sum.** The cylindrical harmonic value is the real part of a polynomial-coefficient exponential sum with nonzero harmonics doubled. [`harmonicAt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelFrame.lean#L78).

**Theorem · Harmonics use radius and absolute height.** The spatial harmonic field evaluates its cylindrical formula at the radius, absolute height and angle of the point. [`harmonicValue_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelFrame.lean#L82).

**Theorem · Cell polynomial evaluation is continuous.** A cell polynomial evaluates continuously in its radial and height coordinates. [`evalPoly_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelFrame.lean#L85).

**Theorem · A harmonic sum varies continuously.** The finite harmonic sum is continuous jointly in radius, height and angle. [`harmonicAt_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelFrame.lean#L89).

**Theorem · Cartesian coordinates are continuous.** Each Cartesian coordinate is a continuous function of a spatial point. [`cont_coord`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelFrame.lean#L94).

**Theorem · Cylindrical radius is continuous.** The cylindrical radius is continuous. [`cylRadius_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelFrame.lean#L96).

**Theorem · Cylindrical height is continuous.** The cylindrical height is continuous. [`cylHeight_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelFrame.lean#L100).

**Theorem · Cylindrical angle is measurable.** The cylindrical angle is measurable. [`cylAngle_meas`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelFrame.lean#L104).

**Theorem · Harmonic fields are measurable.** Every finite harmonic field assembled from cell polynomials is measurable. [`harmonicValue_meas`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelFrame.lean#L108).

**Theorem · Harmonics are bounded in a cylinder.** A harmonic field is uniformly bounded where its cylindrical radius and absolute height have the upper bounds. [`harmonicValue_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelFrame.lean#L115).

**Theorem · Vector reflection signs are measurable.** Each vector reflection sign is a measurable function of position. [`vectorSign_meas`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelFrame.lean#L124).

**Theorem · Pseudovector signs are measurable.** Each pseudovector reflection sign is a measurable function of position. [`pseudoSign_meas`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelFrame.lean#L129).

**Theorem · Vector reflection signs have size one.** Every vector reflection sign has absolute value 1. [`vectorSign_abs`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelFrame.lean#L134).

**Theorem · Pseudovector signs have size one.** Every pseudovector reflection sign has absolute value 1. [`pseudoSign_abs`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelFrame.lean#L138).

**Theorem · Vector norm from frame components.** The norm of a reconstructed vector is at most the sum of the absolute values of its frame coordinates. [`cart_norm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelFrame.lean#L142).

**Theorem · An operator bound from its entries.** The norm of an operator reconstructed from a frame matrix is at most the sum of the absolute values of its entries. [`cartOp_norm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelFrame.lean#L147).

**Theorem · Measurable vector reconstruction.** Measurable frame components multiplied by measurable signs reconstruct a strongly measurable vector field. [`cart_sm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelFrame.lean#L161).

**Theorem · Measurable operator reconstruction.** A measurable matrix field reconstructs a strongly measurable operator field using the cylindrical angle. [`cartOp_sm0`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelFrame.lean#L168).

**Theorem · Measurable signed operator entries.** Measurable matrix components multiplied by measurable signs reconstruct a strongly measurable operator field. [`cartOp_sm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelFrame.lean#L174).

**Theorem · Bounded vector reconstruction.** Bounded frame components with sign factors of absolute value at most 1 reconstruct a bounded vector field on the set. [`cart_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelFrame.lean#L181).

**Theorem · Bounded operator reconstruction.** Bounded matrix components with sign factors of absolute value at most 1 reconstruct a bounded operator field on the set. [`cartOp_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelFrame.lean#L189).

**Theorem · Harmonics are bounded on a cell solid.** A finite harmonic field is uniformly bounded on any cell solid. [`harmonic_solid`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelFrame.lean#L198).

**Theorem · Vector fields are measurable.** The vector field assembled from cell-polynomial harmonics is strongly measurable. [`vectorOf_sm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelFrame.lean#L203).

**Theorem · Pseudovector fields are measurable.** The pseudovector field assembled from cell-polynomial harmonics is strongly measurable. [`pseudoOf_sm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelFrame.lean#L206).

**Theorem · Tensor fields are measurable.** The tensor field assembled from cell-polynomial harmonics is strongly measurable. [`tensorOf_sm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelFrame.lean#L209).

**Theorem · Pseudotensor fields are measurable.** The pseudotensor field assembled from cell-polynomial harmonics is strongly measurable. [`pseudoTensorOf_sm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelFrame.lean#L214).

**Theorem · Vector fields have cell bounds.** The vector field assembled from cell-polynomial harmonics is uniformly bounded on every cell solid. [`vectorOf_bd`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelFrame.lean#L219).

**Theorem · Pseudovector fields have cell bounds.** The pseudovector field assembled from cell-polynomial harmonics is uniformly bounded on every cell solid. [`pseudoOf_bd`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelFrame.lean#L223).

**Theorem · Tensor fields have cell bounds.** The tensor field assembled from cell-polynomial harmonics is uniformly bounded on every cell solid. [`tensorOf_bd`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelFrame.lean#L227).

**Theorem · Pseudotensor fields have cell bounds.** The pseudotensor field assembled from cell-polynomial harmonics is uniformly bounded on every cell solid. [`pseudoTensorOf_bd`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelFrame.lean#L232).

**Theorem · Cell solids are measurable.** The solid associated with a cell box is measurable. [`solid_meas`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelFrame.lean#L237).

**Theorem · Selected mesh pieces are measurable.** Every selected mesh piece is measurable. [`piece_meas`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelFrame.lean#L243).

**Theorem · The mesh region is measurable.** The union of the mesh cell solids is measurable. [`region_meas`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelFrame.lean#L246).

**Theorem · A selected piece lies in its solid.** Every selected mesh piece is contained in its cell solid. [`piece_sub`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelFrame.lean#L248).

**Theorem · Each solid lies in the mesh region.** Every cell solid is contained in the mesh region. [`solid_sub`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelFrame.lean#L250).

**Theorem · Piecewise fields vanish outside the mesh.** A piecewise mesh field is zero outside the mesh region. [`piecewise_out`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelFrame.lean#L253).

**Theorem · Strong measurability of a mesh field.** A finite mesh assembly of strongly measurable fields is strongly measurable. [`piecewise_sm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelFrame.lean#L258).

**Theorem · Cell bounds give a global mesh bound.** Uniform bounds on each cell solid give a single global bound for the piecewise mesh field. [`piecewise_bd`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelFrame.lean#L263).

**Theorem · Lift additive properties to a mesh.** A property closed under zero and addition holds for a piecewise field when it holds for every active cell value. [`piecewise_induct`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelFrame.lean#L275).

**Theorem · Piece membership uses radius and height.** Equality of radius and absolute height preserves selected mesh-piece membership. [`mem_piece_congr`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelFrame.lean#L286).

**Definition · Sign of a reflected frame coordinate.** The reflection sign is −1 for the vertical coordinate and 1 for the other coordinates. [`zSign`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelFrame.lean#L296).

**Definition · Reflection as a linear map.** Horizontal reflection is packaged as a real linear map on space. [`mirrorLin`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelFrame.lean#L298).

**Theorem · The linear map is reflection.** Applying the reflection linear map gives the spatial mirror operation. [`mirrorLin_apply`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelFrame.lean#L307).

**Theorem · Reflection preserves finite sums.** Reflection of a finite vector sum equals the sum of the reflected vectors. [`mirror_fsum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelFrame.lean#L309).

**Theorem · Reflection fixes zero.** Reflecting the zero vector gives zero. [`mirror_zero'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelFrame.lean#L312).

**Theorem · Reflection preserves radius.** Reflecting a point leaves its cylindrical radius unchanged. [`cylRadius_mirror`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelFrame.lean#L314).

**Theorem · Reflection negates height.** Reflecting a point negates its cylindrical height. [`cylHeight_mirror`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelFrame.lean#L316).

**Theorem · Reflection preserves angle.** Reflecting a point leaves its cylindrical angle unchanged. [`cylAngle_mirror`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelFrame.lean#L318).

**Theorem · Reflection of a frame vector.** A reflected frame vector is the same frame vector multiplied by its vertical-coordinate sign. [`frame_mirror`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelFrame.lean#L320).

**Theorem · Reflection moves across an inner product.** Reflecting the second inner-product argument gives the same value as reflecting the first. [`inner_mirror`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelFrame.lean#L323).

**Theorem · Equal coordinates give equal vectors.** Pointwise equal frame coordinates reconstruct the same Cartesian vector. [`cart_congr`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelFrame.lean#L326).

**Theorem · Equal entries give equal operators.** Pointwise equal frame matrices give the same reconstructed operator value on every vector. [`cartOp_congr`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelFrame.lean#L329).

**Theorem · Reflecting a reconstructed vector.** Reflection of a reconstructed vector multiplies its frame coordinates by their reflection signs. [`cart_mirror`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelFrame.lean#L333).

**Theorem · Scaling a reconstructed vector.** Scaling a reconstructed vector multiplies every frame coordinate by the same real scalar. [`cart_smul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelFrame.lean#L340).

**Theorem · Reflecting a reconstructed operator.** Reflecting the input and output of a reconstructed operator multiplies each matrix entry by its two frame reflection signs. [`cartOp_mirror`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelFrame.lean#L343).

**Theorem · Scaling a reconstructed operator.** Scaling the output of a reconstructed operator multiplies all its matrix entries by the same scalar. [`cartOp_smul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelFrame.lean#L351).

**Theorem · Vector signs under reflection.** Away from height zero, reflection multiplies each vector sign by the corresponding frame reflection sign. [`vectorSign_mirror`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelFrame.lean#L359).

**Theorem · Pseudovector signs under reflection.** Away from height zero, reflection multiplies each pseudovector sign by the negative frame reflection sign. [`pseudoSign_mirror`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelFrame.lean#L370).

**Theorem · Harmonics are reflection invariant.** A scalar harmonic field has equal values at a point and its reflection. [`harmonic_mirror`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelFrame.lean#L381).

**Theorem · Vector fields obey mirror symmetry.** Away from height zero, the assembled vector field at the reflected point is the reflection of its value. [`vectorOf_mirror`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelFrame.lean#L385).

**Theorem · Pseudovectors reverse mirror symmetry.** Away from height zero, the assembled pseudovector field at the reflected point is the negative reflection of its value. [`pseudoOf_mirror`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelFrame.lean#L394).

**Theorem · Tensor fields obey mirror symmetry.** Away from height zero, evaluating a tensor at the reflected point equals reflecting its input and output. [`tensorOf_mirror`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelFrame.lean#L403).

**Theorem · Pseudotensors have odd mirror symmetry.** Away from height zero, evaluating a pseudotensor at the reflected point adds a minus sign to the input-output reflection rule. [`pseudoTensorOf_mirror`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelFrame.lean#L413).

**Theorem · Reflection preserves region membership.** A point belongs to the mesh region exactly when its reflection does. [`mem_region_mirror`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelFrame.lean#L423).

**Theorem · Vector mirror laws pass to the mesh.** A common signed reflection law for the active cell vectors passes to their piecewise mesh field. [`piecewise_mirror_vec`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelFrame.lean#L427).

**Theorem · Operator mirror laws pass to the mesh.** A common signed input-output reflection law for active cell operators passes to their piecewise mesh field. [`piecewise_mirror_op`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelFrame.lean#L438).

### Breakdown.FracCell.GivenModelModelModes

This module proves absence of unlisted Fourier modes by representing the circle functions as finite trigonometric sums with both signs of the target frequency excluded. **Reading context:** Appendix B: the polynomial cell models and rows used in the local estimates and finite assembly (B.1 and B.4–B.6).

**Definition · An integer-frequency circle wave.** The circle wave of integer frequency κ is the complex exponential exp(iκθ). [`wave`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelModes.lean#L11).

**Predicate · A sum avoiding a target frequency.** The frequency-exclusion predicate means that a function has a finite exponential expansion with neither sign of any listed frequency equal to the target. [`TrigFree`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelModes.lean#L13).

**Theorem · Zero avoids every frequency.** The zero function admits a finite harmonic expansion avoiding any chosen target frequency. [`tf_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelModes.lean#L17).

**Theorem · Frequency exclusion survives addition.** The sum of two functions with finite expansions avoiding a target frequency also has such an expansion. [`tf_add`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelModes.lean#L20).

**Theorem · Scaling preserves excluded frequencies.** Multiplication by a constant complex scalar preserves the finite-expansion frequency-exclusion property. [`tf_mul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelModes.lean#L29).

**Theorem · Conjugation reverses frequency.** The conjugate of an integer-frequency wave is the wave at the opposite frequency. [`wave_conj`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelModes.lean#L33).

**Theorem · Conjugation keeps frequency exclusions.** Conjugating a function whose finite expansion excludes both target signs preserves that exclusion. [`tf_conj`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelModes.lean#L41).

**Theorem · Equality preserves frequency exclusion.** A function equal pointwise to one with the frequency-exclusion property inherits that property. [`tf_congr`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelModes.lean#L47).

**Theorem · Real parts preserve frequency exclusion.** Taking the real part of a function with both target signs excluded preserves finite-expansion frequency exclusion. [`tf_re`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelModes.lean#L51).

**Theorem · Finite sums preserve excluded modes.** A finite sum of functions avoiding a target frequency also avoids it in a finite harmonic expansion. [`tf_sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelModes.lean#L57).

**Theorem · A wave avoids other frequencies.** A scalar multiple of a wave avoids a target when neither sign of the wave frequency equals that target. [`tf_wave`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelModes.lean#L62).

**Theorem · A circle wave is continuous.** Every integer-frequency circle wave is continuous in its angle. [`wave_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelModes.lean#L65).

**Theorem · A nonzero wave has zero integral.** A nonzero integer-frequency wave integrates to zero over a full circle. [`integral_wave`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelModes.lean#L69).

**Theorem · An excluded Fourier coefficient is zero.** A function with a finite expansion excluding the target frequency has zero circle integral against the target Fourier phase. [`tf_integral`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelModes.lean#L85).

**Theorem · First cylindrical Cartesian coordinate.** The first Cartesian coordinate of a cylindrical point is r cos θ. [`pt0`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelModes.lean#L109).

**Theorem · Second cylindrical Cartesian coordinate.** The second Cartesian coordinate of a cylindrical point is r sin θ. [`pt1`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelModes.lean#L111).

**Theorem · Height of a cylindrical point.** The height of a cylindrical point is its input height. [`pt_height`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelModes.lean#L113).

**Theorem · Radius is the absolute input radius.** The cylindrical radius of a cylindrical point equals the absolute value of its input radius. [`pt_radius`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelModes.lean#L115).

**Theorem · Phase at a signed radius.** At nonzero input radius, the recovered-angle phase equals the input-angle phase multiplied by the sign of the radius. [`angle_exp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelModes.lean#L122).

**Theorem · Cosine at a signed radius.** At nonzero input radius, the recovered-angle cosine is the input cosine multiplied by the sign of the radius. [`angle_cos`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelModes.lean#L141).

**Theorem · Sine at a signed radius.** At nonzero input radius, the recovered-angle sine is the input sine multiplied by the sign of the radius. [`angle_sin`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelModes.lean#L147).

**Definition · Horizontal frame sign.** The frame scale is 1 in the vertical direction and the supplied sign in the other directions. [`frameScale`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelModes.lean#L153).

**Theorem · Frame vectors at a signed radius.** At nonzero radius, the recovered frame differs from the input frame by the radius sign in horizontal directions. [`frame_angle`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelModes.lean#L155).

**Theorem · Frame vectors are orthonormal.** Frame vectors have inner product 1 at equal indices and 0 at unequal indices. [`frameUnit_inner`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelModes.lean#L162).

**Theorem · Frame entries are inner products.** A frame matrix entry is the inner product of the operator applied to its column frame vector with its row frame vector. [`frameMat_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelModes.lean#L167).

**Theorem · Changing frame signs changes entries.** If frame vectors differ by given scalar factors, reconstructing in one frame and reading in the other multiplies each entry by its two factors. [`frameMat_cartOp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelModes.lean#L171).

**Theorem · Harmonic phases at a signed radius.** At nonzero radius, the recovered-angle harmonic equals its circle wave multiplied by the radius sign raised to the harmonic times symmetry order. [`azimuth_exp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelModes.lean#L178).

**Theorem · Positive order preserves mode exclusion.** Multiplication by a positive symmetry order preserves exclusion of both signs of a harmonic from a target mode. [`freq_ne`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelModes.lean#L202).

**Theorem · Harmonic sums avoid absent modes.** At nonzero radius and positive symmetry order, a harmonic field has a finite circle expansion excluding a mode absent from both signs of its coefficient list. [`harmonic_tf`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelModes.lean#L213).

**Theorem · Tensor entries avoid absent modes.** At nonzero radius and positive symmetry order, frame entries of a tensor field have finite circle expansions excluding unlisted mode signs. [`tensor_tf`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelModes.lean#L225).

**Theorem · Mesh tensor entries avoid absent modes.** Piecewise assembly preserves finite circle expansions excluding a mode absent from both signs of all listed harmonics. [`piecewise_tf`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelModes.lean#L239).

**Theorem · Unlisted tensor modes vanish.** At nonzero radius and positive symmetry order, an assembled tensor Fourier mode is zero if neither sign occurs in its harmonic list. [`modes_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelModelModes.lean#L259).

### Breakdown.FracCell.GivenModelRegion

This module identifies the cell mesh region as a cylinder and supplies the measurable, bounded and symmetry properties used by the exterior construction. **Reading context:** Appendix B: the polynomial cell models and rows used in the local estimates and finite assembly (B.1 and B.4–B.6).

**Theorem · Cylindrical radius is nonnegative.** The cylindrical radius of every spatial point is nonnegative. [`cylRadius_nonneg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRegion.lean#L17).

**Theorem · Square of the cylindrical radius.** The squared cylindrical radius is the sum of the squares of the first two Cartesian coordinates. [`cylRadius_sq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRegion.lean#L19).

**Theorem · Norm in cylindrical coordinates.** The squared spatial norm is the sum of the squared cylindrical radius and squared height. [`norm_sq_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRegion.lean#L22).

**Theorem · Cylindrical radius is continuous.** The cylindrical radius is a continuous function of the spatial point. [`continuous_cylRadius`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRegion.lean#L26).

**Theorem · Cylindrical height is continuous.** The cylindrical height is a continuous function of the spatial point. [`continuous_cylHeight`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRegion.lean#L30).

**Theorem · Recover an inequality from squares.** If b is nonnegative and a² is at most b², then a is at most b. [`le_of_sq_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRegion.lean#L34).

**Theorem · Radius is bounded by the norm.** The cylindrical radius is at most the spatial norm. [`cylRadius_le_norm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRegion.lean#L39).

**Theorem · Height is bounded by the norm.** The absolute cylindrical height is at most the spatial norm. [`abs_cylHeight_le_norm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRegion.lean#L42).

**Theorem · A cell solid is measurable.** The three-dimensional solid associated with a cell box is measurable. [`measurableSet_solid`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRegion.lean#L45).

**Theorem · The mesh region is a cylinder.** A valid mesh fills the closed cylinder whose radius and absolute height are bounded by its outer size. [`region_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRegion.lean#L51).

**Theorem · Rotation preserves radius.** A symmetry rotation leaves the cylindrical radius unchanged. [`cylRadius_turnStep`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRegion.lean#L66).

**Theorem · Rotation preserves height.** A symmetry rotation leaves the cylindrical height unchanged. [`cylHeight_turnStep`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRegion.lean#L73).

**Theorem · Reflection preserves radius.** Reflection across the horizontal plane preserves cylindrical radius. [`cylRadius_mirror`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRegion.lean#L76).

**Theorem · Reflection reverses height.** Reflection across the horizontal plane negates cylindrical height. [`cylHeight_mirror`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRegion.lean#L79).

**Definition · Maximum cylindrical coordinate.** The box size of a point is the larger of its cylindrical radius and absolute height. [`boxMax`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRegion.lean#L82).

**Theorem · Box size is continuous.** The maximum cylindrical coordinate is continuous in the spatial point. [`continuous_boxMax`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRegion.lean#L84).

**Theorem · Box size is nonnegative.** The maximum cylindrical coordinate is nonnegative. [`boxMax_nonneg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRegion.lean#L87).

**Theorem · Box size is bounded by the norm.** The maximum cylindrical coordinate is at most the Euclidean norm. [`boxMax_le_norm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRegion.lean#L89).

**Theorem · Norm is bounded by box size.** The Euclidean norm is at most √2 times the maximum cylindrical coordinate. [`norm_le_boxMax`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRegion.lean#L92).

**Theorem · Lower bound for √2.** The real square root of 2 is at least 1. [`one_le_sqrt_two`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRegion.lean#L102).

**Theorem · Box size scales linearly.** Multiplying a point by a positive real factor multiplies its maximum cylindrical coordinate by the same factor. [`boxMax_smul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRegion.lean#L106).

**Theorem · Radius of the exterior boundary.** The exterior radius equals L at zero box size and otherwise equals L times the norm divided by box size. [`boxRadius_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRegion.lean#L116).

**Theorem · Properties of the cell region.** A valid mesh region is measurable and bounded and is preserved by symmetry rotation and reflection. [`cellRegion_clauses`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRegion.lean#L123).

**Theorem · Properties of the exterior radius.** The mesh boundary radius is measurable, lies between the positive outer size and √2 times that size, is constant along positive rays, and describes the region complement almost everywhere. [`exterior_clauses`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRegion.lean#L147).

**Theorem · The inner ball lies in the mesh.** Every point of norm at most the outer size belongs to a valid mesh region. [`ball_subset_region`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRegion.lean#L210).

### Breakdown.FracCell.GivenModelRegular

This module supplies measurability and boundedness for constant weights and cell matrices and for deviations affine in the modified radial coordinate. **Reading context:** Appendix B: the polynomial cell models and rows used in the local estimates and finite assembly (B.1 and B.4–B.6).

**Theorem · A positive constant weight is regular.** A positive constant weight with matching minimum and maximum satisfies the weight, symmetry and cylindrical sampling clauses. [`weight_clauses`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRegular.lean#L15).

**Theorem · Modified radius is measurable.** The modified radial coordinate of a cell is measurable. [`rHat_measurable`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRegular.lean#L29).

**Theorem · A bound for the modified radius.** On a cell rectangle, the absolute modified radius is bounded by 1 plus the absolute radial endpoints. [`rHat_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRegular.lean#L37).

**Theorem · A bound for an affine cell scalar.** On a cell rectangle, the absolute affine expression a+b r̂ is at most |a|+|b|(1+|r₁|+|r₂|). [`affine_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRegular.lean#L57).

**Theorem · Constant cell scalars are regular.** Spatially constant resolved matrices and constant strain and gradient bounds satisfy the cell-scalar measurability and boundedness conditions. [`scalarsRegular_of_const`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRegular.lean#L66).

**Theorem · Affine class deviations are regular.** Class deviations affine in modified radius are measurable and uniformly bounded on a valid cell rectangle. [`classesRegular_of_affine`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRegular.lean#L95).

**Theorem · A constant matrix equals its sample.** A resolved matrix constant throughout the plane equals its value at the lower-left corner of every cell point. [`localMatrixConst_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRegular.lean#L126).

### Breakdown.FracCell.GivenModelRowTraces

This module computes row Fourier modes on closed cell rectangles and expands their side values and normal traces in the segment polynomial bases. **Reading context:** Appendix B: the polynomial cell models and rows used in the local estimates and finite assembly (B.1 and B.4–B.6).

**Theorem · Mixing preserves cell and harmonic.** For valid row data, a nonzero mixing coefficient connects rows with the same cell and harmonic. [`rt_mix_support`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowTraces.lean#L16).

**Theorem · A vector component is an inner product.** A cylindrical vector component is its inner product with the corresponding frame vector. [`rt_frameVec_apply`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowTraces.lean#L21).

**Theorem · Recover vector frame coordinates.** Converting frame coordinates to a Cartesian vector and reading them in the same frame recovers the original coordinates. [`rt_frameVec_cart`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowTraces.lean#L24).

**Theorem · Frame coordinates of a mixed row.** Taking a frame coordinate of a finite real linear combination gives the same linear combination of frame coordinates. [`rt_frameVec_sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowTraces.lean#L31).

**Theorem · First cylindrical Cartesian coordinate.** The first Cartesian coordinate of a cylindrical point is r cos θ. [`rt_cyl0`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowTraces.lean#L35).

**Theorem · Second cylindrical Cartesian coordinate.** The second Cartesian coordinate of a cylindrical point is r sin θ. [`rt_cyl1`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowTraces.lean#L37).

**Theorem · Height of a cylindrical point.** The height of a cylindrical point is its input height. [`rt_cyl2`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowTraces.lean#L39).

**Theorem · Recover a nonnegative radius.** The cylindrical radius of a point with nonnegative input radius is that radius. [`rt_cyl_radius`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowTraces.lean#L41).

**Theorem · The angle is determined modulo 2π.** At positive radius, the recovered cylindrical angle differs from the input angle by an integer multiple of 2π. [`rt_cyl_angle`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowTraces.lean#L48).

**Theorem · A polynomial with no axis term vanishes.** If the radial-degree-zero coefficients vanish, the cell polynomial evaluates to zero at radius zero. [`rt_eval_axis`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowTraces.lean#L59).

**Theorem · The complex phase has period 2π.** Subtracting any integer number of full turns leaves the complex unit phase unchanged. [`rt_exp_period`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowTraces.lean#L68).

**Theorem · Test-row frame values on a closed cell.** Under the axis compatibility conditions, a test-row frame component on the closed cell rectangle equals its polynomial profile times its harmonic phase, taking the real part. [`rt_term_frame`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowTraces.lean#L73).

**Definition · The mixed row profile.** The mixed row profile sums the polynomial profiles with their mixing coefficients. [`rt_profileSum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowTraces.lean#L118).

**Theorem · Frame formula for a selected row.** For a valid row instance, a selected row's frame component on its cell is the real part of its mixed profile times its harmonic phase. [`rt_row_frame`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowTraces.lean#L121).

**Theorem · Integral of an integer-frequency phase.** An integer-frequency complex phase integrates to 2π at zero frequency and to zero otherwise over a full circle. [`rt_int_exp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowTraces.lean#L144).

**Theorem · Split the row Fourier integrand.** The Fourier integrand of a real row harmonic splits into half its amplitude at the difference frequency and half its conjugate at the negative sum frequency. [`rt_mode_key`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowTraces.lean#L158).

**Theorem · Fourier coefficient including order zero.** The row harmonic integral selects each half-amplitude exactly when its frequency difference or negative frequency sum times the order is zero. [`rt_mode_val`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowTraces.lean#L177).

**Theorem · Exact Fourier formula for a row.** A selected row mode equals the two half-profile terms chosen by the signed frequency-times-order equalities. [`rt_mode_formula`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowTraces.lean#L190).

**Theorem · A cell polynomial at fixed radius.** Fixing radius rewrites the cell polynomial as a height polynomial whose coefficients sum the radial monomials. [`rt_eval_fixR`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowTraces.lean#L204).

**Theorem · A cell polynomial at fixed height.** Fixing height rewrites the cell polynomial as a radial polynomial whose coefficients sum the height monomials. [`rt_eval_fixZ`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowTraces.lean#L211).

**Theorem · Combine conjugate polynomial sums.** A linear combination of a mixed polynomial and its conjugate can be collected coefficient by coefficient at real arguments. [`rt_lin`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowTraces.lean#L219).

**Definition · Extend finite coefficients by zero.** The coefficient extension returns the indexed finite coefficient inside its range and zero outside it. [`rt_ext`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowTraces.lean#L235).

**Theorem · Truncate coefficients that vanish.** If all coefficients from D onward vanish, the finite polynomial sum equals its first D terms with zero-extended coefficients. [`rt_pad`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowTraces.lean#L237).

**Theorem · Segment tests span bounded polynomials.** Nonzero leading coefficients in the segment test family allow every polynomial with D coefficients to be expanded in its first D tests. [`rt_span`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowTraces.lean#L257).

**Theorem · Row side traces have test expansions.** When row degree fits the side degree, every selected row component and mode has a side-trace expansion in the corresponding segment test basis. [`rowTraces_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowTraces.lean#L288).

**Theorem · Normal traces have pressure expansions.** Under the side-degree bound, radial and vertical normal row modes have expansions in the pressure-segment tests of the size. [`rowNormalTraces_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowTraces.lean#L331).

### Breakdown.FracCell.GivenModelRowTurn

This module derives the continuous rotation law for each mixed row, expressing its rotated value through the row and its signed partner. **Reading context:** Appendix B: the polynomial cell models and rows used in the local estimates and finite assembly (B.1 and B.4–B.6).

**Theorem · Coordinates of an arbitrary rotation.** Rotation by φ has the usual two-dimensional sine-cosine formula in the horizontal coordinates and fixes height. [`turn_coords`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowTurn.lean#L17).

**Definition · Arbitrary rotation as a linear map.** Rotation by a fixed angle is packaged as a real linear map on space. [`turnLin`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowTurn.lean#L23).

**Theorem · The linear map is the rotation.** Applying the rotation linear map gives the specified spatial rotation. [`turnLin_apply`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowTurn.lean#L32).

**Theorem · Rotation preserves cylindrical radius.** An arbitrary horizontal rotation leaves the cylindrical radius unchanged. [`radius_turn`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowTurn.lean#L34).

**Theorem · Rotation preserves cylindrical height.** An arbitrary horizontal rotation leaves the cylindrical height unchanged. [`height_turn`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowTurn.lean#L42).

**Theorem · Rotation preserves vector signs.** An arbitrary horizontal rotation preserves the vector reflection signs. [`sign_turn`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowTurn.lean#L45).

**Theorem · Cell solids are rotation invariant.** A point belongs to a cell solid exactly when its rotation by any angle does. [`solid_turn`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowTurn.lean#L49).

**Theorem · Rotation shifts a frame angle.** Adding an angle and any full turns to the frame angle rotates the reconstructed vector by that angle. [`frame_turn`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowTurn.lean#L53).

**Theorem · Recovered angle after rotation.** Away from the axis, rotating by φ adds φ to the cylindrical angle modulo an integer number of full turns. [`angle_turn`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowTurn.lean#L64).

**Theorem · A shifted phase mixes quadratures.** For integer frequency, shifting the angle mixes a real harmonic with its i-multiplied quadrature through the sine and cosine factors. [`mode_shift`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowTurn.lean#L92).

**Theorem · Frame reconstruction is linear.** A real linear combination of reconstructed vectors equals reconstruction of the same combination of frame coordinates. [`cart_lin`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowTurn.lean#L108).

**Theorem · Scale a reconstructed frame vector.** Scaling a reconstructed vector scales every frame coordinate by the same real factor. [`cart_smul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowTurn.lean#L112).

**Definition · Quadrature companion of a test row.** The quadrature field uses the same supported test profile with its complex amplitude multiplied by i. [`quarterField`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowTurn.lean#L116).

**Theorem · Rotation mixes a test row and quadrature.** Away from the axis, a rotated test row is the spatial rotation of its cosine-weighted value plus its sine-weighted quadrature field. [`test_turn`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowTurn.lean#L122).

**Theorem · Evaluate multiplication by i.** Multiplying all cell-polynomial coefficients by i multiplies the evaluated polynomial by i. [`eval_I`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowTurn.lean#L143).

**Theorem · A quadrature field is a signed partner.** For a nonzero harmonic in valid row data, the quadrature field equals the signed test field of the partner row. [`quarter_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowTurn.lean#L152).

**Theorem · Reindex a sum by an involution.** A finite sum with its field indices permuted by an involution equals the sum with that involution applied to its coefficients. [`reindex`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowTurn.lean#L183).

**Theorem · Rotation law for normalized row pairs.** Under harmonic support and partner compatibility of the mixing matrix, a rotated row is the rotated sine-cosine combination of itself and its partner. [`row_turn_core`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowTurn.lean#L188).

**Theorem · Rows satisfy the continuous rotation law.** A valid row instance obeys the signed-harmonic sine-cosine rotation law with its partner at every point off the axis. [`rowTurn_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowTurn.lean#L239).

### Breakdown.FracCell.GivenModelRows

This module combines the normalized test rows into compactly supported orthonormal L² fields and bounds their weighted coefficients by a cell-weighted integral. **Reading context:** Appendix B: the polynomial cell models and rows used in the local estimates and finite assembly (B.1 and B.4–B.6).

**Theorem · Cartesian coordinates are continuous.** Each Cartesian coordinate is a continuous function of a spatial point. [`coord_continuous`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRows.lean#L15).

**Theorem · Cell solids are measurable.** The solid associated with a cell box is measurable. [`solid_measurableSet`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRows.lean#L18).

**Theorem · Selected mesh pieces are measurable.** Every selected mesh piece is measurable. [`piece_measurableSet`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRows.lean#L26).

**Theorem · A selected piece lies in its solid.** Every selected mesh piece is contained in its cell solid. [`piece_subset`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRows.lean#L30).

**Theorem · Distinct selected pieces are disjoint.** A point in one selected mesh piece cannot belong to a different selected piece. [`piece_disjoint`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRows.lean#L33).

**Theorem · Cell weight on a selected piece.** On a selected mesh piece, the cell-weight field equals that cell's assigned weight. [`cellWeightField_apply`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRows.lean#L40).

**Theorem · Cell weight outside all pieces.** The cell-weight field is zero at a point outside every selected piece. [`cellWeightField_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRows.lean#L49).

**Theorem · L² pairings are integrable.** The pointwise inner product of two L² vector fields is integrable. [`inner_integrable`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRows.lean#L54).

**Theorem · Integral pairing equals the L² pairing.** The integral pairing of two L² fields equals the inner product of their L² equivalence classes. [`l2Pair_eq_inner`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRows.lean#L61).

**Theorem · Pairing of finite linear combinations.** The pairing of finite real linear combinations is the double sum of coefficient products times the individual pairings. [`l2Pair_sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRows.lean#L69).

**Definition · Symmetry rotation as a linear map.** The discrete symmetry rotation is packaged as a real linear map on space. [`turnLin`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRows.lean#L93).

**Definition · Reflection as a linear map.** Horizontal reflection is packaged as a real linear map on space. [`mirrorLin`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRows.lean#L102).

**Theorem · Norm bound inside a cell solid.** Inside a cell solid, the spatial norm is at most the sum of its outer radius and upper height. [`solid_norm_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRows.lean#L111).

**Theorem · A row vanishes outside its cell.** If mixing preserves cells and harmonics, a row field vanishes outside its assigned cell solid. [`rowField_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRows.lean#L125).

**Theorem · Normalized rows satisfy their clauses.** A valid positive-order row instance gives orthonormal supported L² class fields, positive row weights bounded by rowMax, and a squared row seminorm bounded by the cell-weighted energy. [`row_clauses`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRows.lean#L134).

### Breakdown.FracCell.GivenModelRowsInBlock

This module rewrites each row using real two-variable polynomials on the upper and lower cell solids so that it satisfies the spectral block-field definition. **Reading context:** Appendix B: the polynomial cell models and rows used in the local estimates and finite assembly (B.1 and B.4–B.6).

**Theorem · Mixing preserves cell and harmonic.** For valid row data, a nonzero mixing coefficient connects rows with the same cell and harmonic. [`rib_mix_support`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowsInBlock.lean#L16).

**Theorem · The horizontal plane has zero volume.** The plane of points with third coordinate zero has volume zero. [`rib_plane_null`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowsInBlock.lean#L21).

**Definition · A polynomial from a coefficient array.** The real coefficient array is assembled as an iterated polynomial in the two cell coordinates. [`ribPoly`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowsInBlock.lean#L33).

**Theorem · Evaluate the coefficient polynomial.** The iterated polynomial evaluates to the double sum of coefficients times radial and height monomials. [`ribPoly_eval`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowsInBlock.lean#L36).

**Theorem · Radial degree of the row polynomial.** The outer polynomial degree of the assembled coefficient array is at most its supplied degree bound. [`ribPoly_natDegree`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowsInBlock.lean#L43).

**Theorem · Coefficients of the row polynomial.** The coefficient of a radial power is the sum of the height monomials whose radial index matches it. [`ribPoly_coeff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowsInBlock.lean#L50).

**Theorem · Height degrees of row coefficients.** Every radial coefficient polynomial has height degree at most the supplied degree bound. [`ribPoly_coeff_natDegree`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowsInBlock.lean#L55).

**Theorem · Zero constant row gives divisibility.** If all radial-degree-zero coefficients vanish, the assembled iterated polynomial is divisible by its outer variable. [`ribPoly_dvd`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowsInBlock.lean#L64).

**Theorem · Real and imaginary coefficient parts.** The real part of a polynomial times a phase expands with cosine times real coefficients and negative sine times imaginary coefficients. [`rib_eval_re`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowsInBlock.lean#L74).

**Theorem · Collect mixed row coefficients.** Under the given signed-height identity, a mixed profile sum separates into cosine and sine polynomials with the real and imaginary coefficients. [`rib_coeff_id`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowsInBlock.lean#L87).

**Definition · Mixed complex row coefficients.** Each mixed row coefficient is the sum of profile coefficients weighted by the real mixing matrix. [`ribQ`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowsInBlock.lean#L106).

**Definition · Real polynomials for both cell halves.** The row polynomials separate real and negative imaginary coefficients and incorporate the lower-half reflection signs and height parity. [`ribA`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowsInBlock.lean#L109).

**Theorem · The two angle conventions agree.** The spectral angle coordinate equals the cylindrical angle used by the cell construction. [`rib_angle`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowsInBlock.lean#L114).

**Theorem · The two cylindrical frames agree.** The spectral frame vector equals the corresponding cylindrical frame vector at the point's angle. [`rib_frameVector`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowsInBlock.lean#L119).

**Theorem · Row values in spectral coordinates.** Under the signed-height identity, the mixed row value equals its spectral frame expansion in cosine and sine polynomials. [`rib_value`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowsInBlock.lean#L122).

**Theorem · Pointwise block representation of a row.** Away from the horizontal plane, a valid row instance equals the sum of its polynomial-trigonometric expressions restricted to the two cell halves. [`rib_point`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowsInBlock.lean#L147).

**Theorem · Almost everywhere block representation.** A valid row instance has bounded-degree real block polynomials, the required axis divisibility and the almost everywhere representation. [`rib_core`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowsInBlock.lean#L206).

**Theorem · Rows belong to their spectral blocks.** A valid row instance gives a spectral block field for every row and its assigned block. [`rowsInBlock_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowsInBlock.lean#L236).

### Breakdown.FracCell.GivenModelRowsParts

This module develops the support, symmetry, circle orthogonality and matrix normalization facts that establish the L² pairing formula for the test rows. **Reading context:** Appendix B: the polynomial cell models and rows used in the local estimates and finite assembly (B.1 and B.4–B.6).

**Theorem · Cartesian coordinates are continuous.** Each Cartesian coordinate is a continuous function of a spatial point. [`coord_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowsParts.lean#L18).

**Theorem · Cylindrical radius is continuous.** The cylindrical radius is continuous. [`cylRadius_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowsParts.lean#L21).

**Theorem · Continuity of absolute height.** The absolute cylindrical height is continuous in position. [`absHeight_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowsParts.lean#L25).

**Theorem · Cell solids are measurable.** The solid associated with a cell box is measurable. [`solid_measurableSet`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowsParts.lean#L28).

**Theorem · Cylindrical angle is measurable.** The cylindrical angle is measurable. [`cylAngle_meas`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowsParts.lean#L34).

**Theorem · Coordinate insertion is scalar scaling.** Inserting a scalar in one Cartesian coordinate equals that scalar times the corresponding unit coordinate vector. [`single_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowsParts.lean#L38).

**Theorem · Coordinate vectors vary continuously.** Placing a real number in one Cartesian coordinate defines a continuous vector-valued map. [`single_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowsParts.lean#L43).

**Theorem · Frame vectors are measurable.** Each cylindrical frame vector is measurable in the angle. [`frameUnit_meas`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowsParts.lean#L49).

**Theorem · Vector reflection signs are measurable.** Each vector reflection sign is a measurable function of position. [`vectorSign_meas`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowsParts.lean#L59).

**Theorem · A uniform bound for frame vectors.** Every cylindrical frame vector has norm at most 2. [`frameUnit_norm_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowsParts.lean#L67).

**Theorem · A coefficient bound for cell polynomials.** On 0≤r≤R and 0≤h≤Z, a cell polynomial norm is bounded by the sum of its coefficient norms multiplied by the corresponding powers of R and Z. [`evalPoly_norm_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowsParts.lean#L83).

**Theorem · Test rows belong to L².** For a valid mesh, every polynomial harmonic test row belongs to L². [`testField_memLp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowsParts.lean#L94).

**Theorem · A squared-coordinate level is null.** The set of real numbers with a fixed square has Lebesgue measure zero. [`level_finite_null`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowsParts.lean#L148).

**Theorem · A fixed-radius cylinder is null.** The spatial set of points with a prescribed cylindrical radius has volume zero. [`radius_level_null`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowsParts.lean#L155).

**Theorem · A fixed absolute height is null.** The spatial set of points with a prescribed absolute cylindrical height has volume zero. [`height_level_null`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowsParts.lean#L175).

**Theorem · Distinct cells overlap on null sets.** In a valid mesh, the intersection of two distinct cell solids has volume zero. [`solid_inter_null`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowsParts.lean#L185).

**Theorem · Coordinates of the symmetry rotation.** The symmetry step rotates the first two coordinates by 2π/m and leaves height fixed. [`turnStep_coords`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowsParts.lean#L195).

**Theorem · Coordinates of horizontal reflection.** Horizontal reflection fixes the first two coordinates and negates the third. [`mirror_coords`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowsParts.lean#L201).

**Theorem · Symmetry rotation preserves radius.** The discrete symmetry rotation leaves cylindrical radius unchanged. [`cylRadius_turn`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowsParts.lean#L204).

**Theorem · Symmetry rotation preserves height.** The discrete symmetry rotation leaves cylindrical height unchanged. [`cylHeight_turn`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowsParts.lean#L212).

**Theorem · Reflection preserves radius.** Reflecting a point leaves its cylindrical radius unchanged. [`cylRadius_mirror`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowsParts.lean#L215).

**Theorem · Reflection preserves absolute height.** Horizontal reflection leaves absolute cylindrical height unchanged. [`absHeight_mirror`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowsParts.lean#L219).

**Theorem · Reflection preserves angle.** Reflecting a point leaves its cylindrical angle unchanged. [`cylAngle_mirror`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowsParts.lean#L223).

**Theorem · Rotation preserves reflection signs.** The discrete symmetry rotation preserves every vector reflection sign. [`vectorSign_turn`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowsParts.lean#L227).

**Theorem · Rotation preserves a cell solid.** A point lies in a cell solid exactly when its symmetry rotation does. [`solid_turn`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowsParts.lean#L231).

**Theorem · Reflection preserves a cell solid.** A point lies in a cell solid exactly when its horizontal reflection does. [`solid_mirror`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowsParts.lean#L235).

**Theorem · Reflecting frame coordinates.** Reflecting a reconstructed vector negates its vertical frame component and fixes the others. [`frame_mirror`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowsParts.lean#L239).

**Theorem · Rotation shifts the frame angle.** Adding the symmetry angle and any full turns to the frame angle rotates the reconstructed vector by the symmetry step. [`frame_turn`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowsParts.lean#L245).

**Theorem · Angle after a symmetry rotation.** Away from the axis, the cylindrical angle after a symmetry step equals its original angle plus 2π/m modulo full turns. [`cylAngle_turn`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowsParts.lean#L256).

**Theorem · Model harmonics obey the symmetry step.** For positive symmetry order, a model harmonic is unchanged by the symmetry angle plus any number of full turns. [`exp_turn`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowsParts.lean#L284).

**Theorem · Test rows have the required symmetry.** For positive order, each test row is a class field with the rotation and reflection symmetry. [`testField_class`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowsParts.lean#L300).

**Theorem · Normalize a positive definite matrix.** Every real positive definite finite matrix admits a congruence transforming it to the identity. [`exists_normalizer`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowsParts.lean#L337).

**Theorem · Normalize while preserving blocks.** A positive definite matrix with zero entries across blocks admits a normalizer with the same block support. [`exists_block_normalizer`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowsParts.lean#L363).

**Theorem · Mixing normalizes and preserves blocks.** Positive definiteness of the test pairing gives identity normalization and mixing supported within cell and harmonic blocks. [`mix_spec`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowsParts.lean#L395).

**Definition · An integer-frequency exponential.** The frequency exponential is the complex phase exp(inθ) for integer n. [`freqExp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowsParts.lean#L452).

**Theorem · Multiplying waves adds frequencies.** The product of two frequency exponentials is the exponential at the sum of their frequencies. [`freqExp_mul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowsParts.lean#L454).

**Theorem · Conjugating a wave negates frequency.** Complex conjugation negates the frequency of a circle exponential. [`freqExp_conj`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowsParts.lean#L461).

**Theorem · Frequency exponentials are continuous.** Each integer-frequency exponential is continuous in its angle. [`freqExp_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowsParts.lean#L469).

**Theorem · A full-circle exponential integral.** The integral over the angle interval from −π to π is 2π for zero frequency and zero otherwise. [`freqExp_integral`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowsParts.lean#L473).

**Theorem · Real parts combine opposite frequencies.** The real part of a complex-amplitude wave is half the sum of the wave and its conjugate at the opposite frequency. [`re_mode`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowsParts.lean#L491).

**Theorem · Orthogonality of nonnegative waves.** Real waves with different nonnegative integer frequencies are orthogonal on a circle, while equal positive frequencies pair to π Re(A conjugate(B)) and frequency zero pairs to 2π Re(A) Re(B). [`mode_angular_int`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowsParts.lean#L495).

**Theorem · Orthogonality of row harmonics.** For positive symmetry order, different row harmonics are orthogonal on a circle, equal positive harmonics pair to π Re(A conjugate(B)), and harmonic zero pairs to 2π Re(A) Re(B). [`mode_angular`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowsParts.lean#L527).

**Theorem · Coordinates of a cylinder point.** A cylindrical point has coordinates r cos θ, r sin θ and z. [`cylPoint_coords`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowsParts.lean#L554).

**Theorem · Recover the principal angle.** At positive radius and angle in (−π, π], the cylindrical angle equals the supplied angle. [`cylAngle_cylPoint`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowsParts.lean#L558).

**Theorem · Recover a nonnegative radius.** The cylindrical radius of a point with nonnegative input radius is that radius. [`cylRadius_cylPoint`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowsParts.lean#L568).

**Theorem · Frame reconstruction preserves pairing.** The inner product of two reconstructed vectors equals the sum of products of their frame coordinates. [`frame_inner`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowsParts.lean#L574).

**Theorem · Test-row pairing in cylindrical form.** For rows in the same cell, their pointwise inner product on a principal-angle circle equals the cell indicator times the profile component pairing. [`testField_inner_cyl`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowsParts.lean#L580).

**Theorem · A vertical coordinate line is null.** A fixed first-coordinate line has planar Lebesgue measure zero. [`line_null_fst`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowsParts.lean#L604).

**Theorem · A horizontal coordinate line is null.** A fixed second-coordinate line has planar Lebesgue measure zero. [`line_null_snd`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowsParts.lean#L608).

**Theorem · Reflecting the cell doubles its integral.** Integrating a continuous cell function with absolute height over the positive-radius plane gives twice its integral over the upper cell rectangle. [`doubling`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowsParts.lean#L612).

**Theorem · L² inner products are integrable.** The pointwise inner product of two L² vector fields is integrable. [`inner_int`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowsParts.lean#L652).

**Theorem · Test pairing for rows in one cell.** For positive order and a valid mesh, the L² pairing of two test rows in the same cell equals their recorded test-pairing entry. [`pairing_same_cell`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowsParts.lean#L659).

**Theorem · The recorded matrix is the L² pairing.** For positive order and a valid mesh, every pair of test rows has L² pairing equal to its test-pairing matrix entry. [`testField_pairing`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowsParts.lean#L735).

### Breakdown.FracCell.GivenModelRowshape

This module proves row support, reflection and Fourier shape, then constructs smooth extensions and polynomial formulas for row derivatives inside cells. **Reading context:** Appendix B: the polynomial cell models and rows used in the local estimates and finite assembly (B.1 and B.4–B.6).

**Theorem · Mixing preserves cell and harmonic.** For valid row data, a nonzero mixing coefficient connects rows with the same cell and harmonic. [`rs_mix_support`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L16).

**Theorem · Reflection multiplies the vertical sign.** Each reflected Cartesian coordinate is the original coordinate multiplied by −1 in the vertical direction and 1 otherwise. [`rs_mirror_coord`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L21).

**Theorem · Reflection preserves finite sums.** Reflection of a finite vector sum equals the sum of the reflected vectors. [`rs_mirror_sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L24).

**Theorem · Reflection commutes with scaling.** Reflecting a real scalar multiple gives the same scalar multiple of the reflected vector. [`rs_mirror_smul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L29).

**Theorem · Reflection fixes zero.** Reflecting the zero vector gives zero. [`rs_mirror_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L33).

**Theorem · Vertical frame sign gives reflection.** Negating the vertical frame coordinate and fixing the others reconstructs the reflected vector. [`rs_cart_sign`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L37).

**Theorem · Reflection preserves radius.** Reflecting a point leaves its cylindrical radius unchanged. [`rs_radius_mirror`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L42).

**Theorem · Reflection negates height.** Reflecting a point negates its cylindrical height. [`rs_height_mirror`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L45).

**Theorem · Reflection preserves angle.** Reflecting a point leaves its cylindrical angle unchanged. [`rs_angle_mirror`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L48).

**Theorem · Test-row reflection below the plane.** Below the horizontal plane, a test row equals the reflection of its value at the mirrored point. [`rs_testField_mirror`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L51).

**Theorem · Selected rows vanish outside their cell.** For a valid row instance, every row selected for a cell vanishes outside that cell's solid. [`rowsInCell_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L67).

**Theorem · A row cell lies in the cell region.** The solid of the row-instance cell is contained in the cell region. [`solidInRegion_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L82).

**Theorem · Selected rows obey the mirror law.** For a valid row instance, each selected row below the horizontal plane is the reflection of its value at the mirrored point. [`rowMirror_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L89).

**Theorem · A vector component is an inner product.** A cylindrical vector component is its inner product with the corresponding frame vector. [`rs_frameVec_apply`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L100).

**Theorem · Recover vector frame coordinates.** Converting frame coordinates to a Cartesian vector and reading them in the same frame recovers the original coordinates. [`rs_frameVec_cart`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L103).

**Theorem · Frame coordinates of a mixed row.** Taking a frame coordinate of a finite real linear combination gives the same linear combination of frame coordinates. [`rs_frameVec_sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L110).

**Theorem · First cylindrical Cartesian coordinate.** The first Cartesian coordinate of a cylindrical point is r cos θ. [`rs_cyl0`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L114).

**Theorem · Second cylindrical Cartesian coordinate.** The second Cartesian coordinate of a cylindrical point is r sin θ. [`rs_cyl1`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L116).

**Theorem · Height of a cylindrical point.** The height of a cylindrical point is its input height. [`rs_cyl2`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L118).

**Theorem · Recover a nonnegative radius.** The cylindrical radius of a point with nonnegative input radius is that radius. [`rs_cyl_radius`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L120).

**Theorem · The angle is determined modulo 2π.** At positive radius, the recovered cylindrical angle differs from the input angle by an integer multiple of 2π. [`rs_cyl_angle`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L127).

**Theorem · A polynomial with no axis term vanishes.** If the radial-degree-zero coefficients vanish, the cell polynomial evaluates to zero at radius zero. [`rs_eval_axis`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L138).

**Theorem · The complex phase has period 2π.** Subtracting any integer number of full turns leaves the complex unit phase unchanged. [`rs_exp_period`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L147).

**Theorem · Test-row frame values on a closed cell.** Under the axis compatibility conditions, a test-row frame component on the closed cell rectangle equals its polynomial profile times its harmonic phase, taking the real part. [`rs_term_frame`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L152).

**Theorem · Frame formula for a selected row.** For a valid row instance, a selected row's frame component on its cell is the real part of its mixed profile times its harmonic phase. [`rs_row_frame`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L197).

**Theorem · Nonzero integer phases integrate to zero.** A complex phase of nonzero integer frequency has zero integral over a full circle. [`rs_int_exp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L221).

**Theorem · Unmatched row harmonics integrate away.** For positive order, a row harmonic paired with a mode matching neither frequency sign has zero Fourier integral. [`rs_mode_term`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L231).

**Theorem · Only the row's two mode signs survive.** For positive order, a selected row has zero modes outside the two signs of its assigned harmonic on the closed cell rectangle. [`rowModeOf_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L265).

**Theorem · Unlisted row modes vanish.** For positive order, every selected row mode outside the row-mode set vanishes on the closed cell rectangle. [`rowModes_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L280).

**Theorem · Cell polynomial evaluation has bounds.** A cell polynomial of degree d evaluates to a bivariate polynomial function of degree at most d in each coordinate. [`rs_poly_eval`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L290).

**Theorem · Conjugated cell polynomials keep degree.** The conjugate of a degree-d cell polynomial evaluates in the bivariate polynomial space with degree bounds d and d. [`rs_poly_conj`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L293).

**Theorem · Zero has every polynomial degree bound.** The zero function belongs to the bivariate polynomial space for every pair of degree bounds. [`rs_poly_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L297).

**Theorem · Addition preserves polynomial degrees.** Adding bivariate polynomial functions with the same degree bounds preserves those bounds. [`rs_poly_add`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L300).

**Theorem · Scaling preserves polynomial degree.** Multiplying a bivariate polynomial function by a complex scalar preserves its two degree bounds. [`rs_poly_smul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L312).

**Theorem · Finite sums preserve degree bounds.** A finite sum of bivariate polynomial functions with the same degree bounds retains those bounds. [`rs_poly_sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L323).

**Theorem · Radius multiplication raises one degree.** Multiplying a polynomial function by radius increases the radial degree bound by 1 and preserves the height bound. [`rs_poly_fst`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L333).

**Theorem · Height multiplication raises one degree.** Multiplying a polynomial function by height increases the height degree bound by 1 and preserves the radial bound. [`rs_poly_snd`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L345).

**Theorem · Enlarging the polynomial degree bounds.** A polynomial function remains in the polynomial space when both degree bounds are increased. [`rs_poly_mono`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L357).

**Theorem · Modified radius has a polynomial product.** Away from zero radius, multiplying a degree-d polynomial by modified radius admits a polynomial representative with both bounds at most d+1. [`rs_rhat_poly`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L376).

**Theorem · Position factors preserve bounded degree.** Multiplying a polynomial by a cylindrical position component increases both available degree bounds by at most 1. [`rs_frameY_poly`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L384).

**Theorem · Rotation factors preserve bounded degree.** Multiplying a polynomial by a rotated-position component increases both available degree bounds by at most 1. [`rs_frameTurnY_poly`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L391).

**Definition · The mixed row profile.** The mixed row profile sums the polynomial profiles with their mixing coefficients. [`rowProfileSum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L398).

**Definition · The two signed row coefficients.** The row-mode value selects half the mixed profile at the positive harmonic and half its conjugate at the negative harmonic. [`rowModeValue`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L401).

**Theorem · Row-mode values are polynomials.** Every algebraic row-mode value has radial and height degree bounds at most the row-data degree. [`rs_value_poly`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L405).

**Theorem · Integral of an integer-frequency phase.** An integer-frequency complex phase integrates to 2π at zero frequency and to zero otherwise over a full circle. [`rs_int_exp'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L435).

**Theorem · Split the row Fourier integrand.** The Fourier integrand of a real row harmonic splits into half its amplitude at the difference frequency and half its conjugate at the negative sum frequency. [`rs_mode_key`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L443).

**Theorem · The two Fourier coefficients of a row.** For positive order, the normalized Fourier integral of a real row harmonic gives half its amplitude at the positive frequency and half its conjugate at the negative frequency. [`rs_mode_val`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L462).

**Theorem · Row modes equal their polynomial values.** For positive order and a valid row instance, each row-mode component on the cell rectangle equals its algebraic row-mode value. [`rs_mode_formula`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L481).

**Theorem · Row polynomial clauses from gradients.** For valid positive-order rows, a high-degree allowance at least two above the row degree and polynomial weighted gradients give the four polynomial clauses for weighted values, position products, rotation products and gradients. [`rowLow_of_gradient`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L494).

**Definition · A smoothed positive radius.** The modified radius uses a smooth transition inside radius δ to remove the singularity of the cylindrical radius at the axis. [`smoothRadius`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L524).

**Theorem · The smoothed radicand is positive.** For positive δ, the expression under the smoothed-radius square root is positive everywhere. [`rs_inner_pos`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L528).

**Theorem · The smoothed radius never vanishes.** For positive δ, the smoothed radius is nonzero at every point. [`rs_rho_ne`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L539).

**Theorem · Smoothed radius agrees away from axis.** At cylindrical radius at least δ>0, the smoothed radius equals the original cylindrical radius. [`rs_rho_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L542).

**Theorem · C² Cartesian coordinates.** Every Cartesian coordinate map is twice continuously differentiable. [`rs_coord_smooth`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L556).

**Theorem · The smoothed radius has two derivatives.** For positive δ, the smoothed radius is twice continuously differentiable on all of space. [`rs_rho_smooth`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L558).

**Definition · Cartesian frame reconstruction formula.** The algebraic frame reconstruction combines horizontal components using two real inputs and retains the vertical component. [`frameCart`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L567).

**Theorem · Algebraic trigonometric reconstruction.** Cylindrical frame reconstruction equals the algebraic formula with inputs cos θ and sin θ. [`rs_cart_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L571).

**Theorem · First algebraic frame coordinate.** The first coordinate of the algebraic frame reconstruction is w₀u−w₁v. [`rs_frameCart0`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L576).

**Theorem · Second algebraic frame coordinate.** The second coordinate of the algebraic frame reconstruction is w₀v+w₁u. [`rs_frameCart1`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L580).

**Theorem · Vertical algebraic frame coordinate.** The vertical coordinate of the algebraic frame reconstruction is w₂. [`rs_frameCart2`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L583).

**Theorem · Smooth inputs give a smooth frame value.** Twice continuously differentiable algebraic frame inputs and component functions produce a twice continuously differentiable vector field. [`rs_frameCart_smooth`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L586).

**Theorem · Angle trigonometry from coordinates.** At positive radius, cosine and sine of the cylindrical angle are the first and second Cartesian coordinates divided by radius. [`rs_angle_trig`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L602).

**Theorem · Integer harmonics are powers of a phase.** The model harmonic exponential equals the basic complex unit phase raised to the harmonic times the symmetry order. [`rs_exp_pow`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L616).

**Definition · A smooth extension of a test row.** The smooth test field replaces radius by the positive smoothed radius and writes its harmonic as a power of normalized horizontal coordinates. [`smoothTestField`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L623).

**Theorem · The extended test row is C².** For positive smoothing scale, the smooth test field is twice continuously differentiable everywhere. [`rs_smoothTest_smooth`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L629).

**Theorem · Extension agrees on the upper cell.** The test field and its smooth extension agree inside its cell at nonnegative height and radius at least the positive smoothing scale. [`rs_smoothTest_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L649).

**Theorem · Rows admit smooth extensions off axis.** Every row of a valid instance admits a global C² extension agreeing on its upper cell portion at radius at least any chosen δ>0. [`rowSmooth_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L662).

**Theorem · A cell solid gives a norm bound.** In a valid cell solid, the spatial norm is at most its outer radius plus upper height. [`rs_norm_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L678).

**Theorem · A C² map is Lipschitz on a closed ball.** A twice continuously differentiable map on a proper normed space has a finite Lipschitz bound on every closed ball. [`rs_slope_of_smooth`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L696).

**Theorem · Cylindrical radius is 1-Lipschitz.** The cylindrical radius has global Lipschitz constant 1. [`rs_radius_slope`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L701).

**Definition · A polynomial with radial powers lowered.** The auxiliary quotient polynomial lowers each radial exponent by 1 using natural-number subtraction. [`divPoly`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L717).

**Theorem · Factor radius from an axis-zero profile.** If all radial-degree-zero coefficients vanish, polynomial evaluation equals radius times the lowered-power polynomial. [`rs_divPoly`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L720).

**Definition · A regular expression for an axis row.** The axis-field formula uses lowered radial powers in horizontal components and the original polynomial in the vertical component. [`axisField`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L735).

**Theorem · The axis expression is C².** The auxiliary axis-field expression is twice continuously differentiable in its scalar radius input and spatial coordinates. [`rs_axisField_smooth`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L739).

**Theorem · Axis rows have a regular expression.** For a zero harmonic with vanishing horizontal axis coefficients, the test row on its upper cell equals the axis-field expression at actual radius. [`rs_axis_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L758).

**Theorem · Rows are Lipschitz on each upper cell.** Every row of a valid instance has a finite Lipschitz bound on the intersection of its solid with nonnegative height. [`rowHalfSlope_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L788).

**Theorem · Smooth row extension from its formula.** The explicit row formula and valid row data give a global C² extension agreeing on the upper cell at radius at least any positive δ. [`rs_smooth_core`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L839).

**Theorem · Recover a vector from frame coordinates.** Reconstructing a vector from its components in the same cylindrical frame returns the vector. [`rs_cart_frameVec`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L854).

**Theorem · A row in cylindrical coordinates.** A selected row on its cell circle equals the frame reconstruction of its mixed profile times its harmonic phase, taking componentwise real parts. [`rs_row_cyl`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L862).

**Theorem · Differentiate rows inside cells.** Every selected row has its Fréchet derivative at every angular lift of an interior point of its valid cell. [`rs_row_hasFDeriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L873).

**Theorem · Radial derivative of a cell polynomial.** Differentiating polynomial evaluation along a radial increment gives the formal radial derivative at increment zero. [`rs_deriv_eval_r`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L909).

**Theorem · Height derivative of a cell polynomial.** Differentiating polynomial evaluation along a height increment gives the formal height derivative at increment zero. [`rs_deriv_eval_z`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L919).

**Theorem · A radial increment is a straight line.** Changing cylindrical radius by s adds s times the radial unit vector to the point. [`rs_curve_r`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L929).

**Theorem · A height increment is a straight line.** Changing cylindrical height by s adds s times the axial unit vector to the point. [`rs_curve_z`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L933).

**Theorem · Derivative of a straight spatial line.** The derivative at zero of y+sv is v. [`rs_line_deriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L937).

**Theorem · Derivative of a shifted cosine.** The derivative at zero of cos(θ+s) is −sin θ. [`rs_cos_deriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L940).

**Theorem · Derivative of a shifted sine.** The derivative at zero of sin(θ+s) is cos θ. [`rs_sin_deriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L945).

**Theorem · Derivative along a circle.** The derivative of the angular coordinate curve at zero is radius times the angular unit vector. [`rs_curve_t`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L950).

**Theorem · Derivative of the cylindrical frame.** Angular differentiation sends the radial frame vector to the angular vector, the angular vector to the negative radial vector and the axial vector to zero. [`rs_frame_deriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L965).

**Definition · Mixed radial profile derivatives.** The mixed radial derivative sums formal radial profile derivatives weighted by the mixing matrix. [`rowDrSum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L997).

**Definition · Mixed height profile derivatives.** The mixed height derivative sums formal height profile derivatives weighted by the mixing matrix. [`rowDzSum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L1000).

**Definition · Rotation of the horizontal row profile.** The frame-rotation term sends the first two mixed profile components to the negative second and the first, with zero vertical component. [`turnPart`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L1003).

**Definition · Cylindrical row-gradient coefficients.** The gradient coefficient uses radial and height derivatives in those directions and the radius-divided harmonic and frame-rotation terms in the angular direction. [`gradCoef`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L1006).

**Theorem · Real parts commute with differentiation.** A real derivative of a complex function gives the derivative of its real part by taking the real part of the derivative. [`rs_re_deriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L1010).

**Theorem · Differentiate in a fixed frame.** Differentiating component functions reconstructed in a fixed frame gives reconstruction of their component derivatives. [`rs_cart_deriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L1014).

**Theorem · Radial derivative of a row.** In a valid cell interior, the radial directional derivative of a selected row is its mixed radial profile derivative reconstructed with the row phase. [`rs_dir_radial`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L1019).

**Theorem · Axial derivative of a row.** In a valid cell interior, the axial directional derivative of a selected row is its mixed height profile derivative reconstructed with the row phase. [`rs_dir_axial`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L1046).

**Theorem · Derivative of a harmonic phase.** The derivative of a shifted phase exp(ik(θ+s)) at zero is the phase multiplied by ik. [`rs_exp_deriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L1072).

**Theorem · Angular derivative of a row.** In a valid cell interior, the angular directional derivative of a selected row uses its angular gradient coefficient and original row phase. [`rs_dir_angular`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L1080).

**Theorem · Frame entries of the row derivative.** In a valid cell interior, a frame entry of the row derivative is the real part of its gradient coefficient times the row phase. [`rs_grad_entry`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L1127).

**Theorem · Bounded monomials are polynomials.** A scalar multiple of a radial-height monomial lies in the degree-d polynomial space when both exponents are at most d. [`rs_poly_monomial`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L1148).

**Theorem · Polynomial radial derivatives.** The formal radial derivative of a degree-d cell polynomial remains within degree bounds d in each coordinate. [`rs_poly_dr`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L1162).

**Theorem · Polynomial height derivatives.** The formal height derivative of a degree-d cell polynomial remains within degree bounds d in each coordinate. [`rs_poly_dz`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L1167).

**Theorem · Lowered-power expression is polynomial.** The lowered-radial-power expression has degree bounds at most d in each coordinate for a degree-d cell polynomial. [`rs_poly_div`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L1178).

**Theorem · Conjugation preserves degree bounds.** Complex conjugation preserves the radial and height degree bounds of a bivariate polynomial function. [`rs_poly_conj_gen`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L1183).

**Theorem · Fourier selection preserves polynomials.** A polynomial representative for modified-radius times a field gives a representative of the same degree for its two signed half-mode selections. [`rs_mode_wrap`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L1188).

**Definition · Mixed lowered-power profiles.** The mixed quotient expression sums the lowered-radial-power profile polynomials with the mixing coefficients. [`rowDivSum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L1220).

**Theorem · Weighted row gradients are polynomials.** For positive order and a degree margin of at least two, modified-radius times every selected row-gradient mode has a polynomial representative inside its cell. [`rowLowGradient_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L1223).

**Theorem · Rows satisfy all low polynomial clauses.** For valid positive-order rows with high-degree allowance at least two above the row degree, weighted row values and their position products, rotation products and interior gradients have polynomial representatives. [`rowLow_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshape.lean#L1332).

### Breakdown.FracCell.GivenModelRowshapeOpen

This module computes the trace of the derivative of a row in cylindrical directions and proves the zero-divergence identity from solenoidal polynomial profiles. **Reading context:** Appendix B: the polynomial cell models and rows used in the local estimates and finite assembly (B.1 and B.4–B.6).

**Theorem · A vector component is an inner product.** A cylindrical vector component is its inner product with the corresponding frame vector. [`sol_frameVec_apply`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshapeOpen.lean#L15).

**Theorem · Recover vector frame coordinates.** Converting frame coordinates to a Cartesian vector and reading them in the same frame recovers the original coordinates. [`sol_frameVec_cart`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshapeOpen.lean#L19).

**Theorem · Recover a vector from frame coordinates.** Reconstructing a vector from its components in the same cylindrical frame returns the vector. [`sol_cart_frameVec`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshapeOpen.lean#L26).

**Theorem · Frame coordinates of a mixed row.** Taking a frame coordinate of a finite real linear combination gives the same linear combination of frame coordinates. [`sol_frameVec_sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshapeOpen.lean#L34).

**Theorem · First cylindrical Cartesian coordinate.** The first Cartesian coordinate of a cylindrical point is r cos θ. [`sol_cyl0`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshapeOpen.lean#L38).

**Theorem · Second cylindrical Cartesian coordinate.** The second Cartesian coordinate of a cylindrical point is r sin θ. [`sol_cyl1`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshapeOpen.lean#L40).

**Theorem · Height of a cylindrical point.** The height of a cylindrical point is its input height. [`sol_cyl2`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshapeOpen.lean#L42).

**Theorem · Recover a nonnegative radius.** The cylindrical radius of a point with nonnegative input radius is that radius. [`sol_cyl_radius`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshapeOpen.lean#L44).

**Theorem · The angle is determined modulo 2π.** At positive radius, the recovered cylindrical angle differs from the input angle by an integer multiple of 2π. [`sol_cyl_angle`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshapeOpen.lean#L51).

**Theorem · A polynomial with no axis term vanishes.** If the radial-degree-zero coefficients vanish, the cell polynomial evaluates to zero at radius zero. [`sol_eval_axis`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshapeOpen.lean#L62).

**Theorem · The complex phase has period 2π.** Subtracting any integer number of full turns leaves the complex unit phase unchanged. [`sol_exp_period`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshapeOpen.lean#L71).

**Theorem · Angle trigonometry from coordinates.** At positive radius, cosine and sine of the cylindrical angle are the first and second Cartesian coordinates divided by radius. [`sol_angle_trig`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshapeOpen.lean#L76).

**Theorem · Test-row formula on both cell halves.** On either cell half, the test-row frame component is its harmonic profile at absolute height with a minus sign for the vertical component below the plane. [`sol_term_frame`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshapeOpen.lean#L90).

**Definition · Mixed profile for the divergence formula.** The mixed profile sums the row polynomial values with their mixing coefficients. [`solA`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshapeOpen.lean#L138).

**Definition · Phase in the divergence formula.** The row phase is the complex exponential at the row harmonic times the symmetry order. [`solE`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshapeOpen.lean#L141).

**Theorem · Row components on both cell halves.** For a valid row instance with block-preserving mixing, frame components equal the mixed profile times the row phase with the lower-half vertical sign. [`sol_row_frame`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshapeOpen.lean#L144).

**Theorem · Trace can be computed in the frame.** The coordinate trace of an operator equals the sum of its diagonal entries in any cylindrical orthonormal frame. [`sol_trace_frame`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshapeOpen.lean#L167).

**Theorem · One-sided agreement fixes the derivative.** Two functions differentiable at zero have equal derivatives if they agree on a nontrivial interval immediately to either side of zero. [`sol_one_sided`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshapeOpen.lean#L181).

**Theorem · Directional chain rule for a component.** Composing a Fréchet-differentiable field with a differentiable curve gives the derivative after pairing with a fixed vector. [`sol_dir`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshapeOpen.lean#L194).

**Theorem · Radial derivative of a cell polynomial.** Differentiating polynomial evaluation along a radial increment gives the formal radial derivative at increment zero. [`sol_deriv_eval_r`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshapeOpen.lean#L205).

**Theorem · Height derivative of a cell polynomial.** Differentiating polynomial evaluation along a height increment gives the formal height derivative at increment zero. [`sol_deriv_eval_z`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshapeOpen.lean#L215).

**Theorem · Derivative under decreasing height.** Differentiating a cell polynomial along height w−s gives the negative formal height derivative at zero. [`sol_deriv_eval_zneg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshapeOpen.lean#L225).

**Theorem · A radial increment is a straight line.** Changing cylindrical radius by s adds s times the radial unit vector to the point. [`sol_curve_r`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshapeOpen.lean#L238).

**Theorem · A height increment is a straight line.** Changing cylindrical height by s adds s times the axial unit vector to the point. [`sol_curve_z`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshapeOpen.lean#L242).

**Theorem · Derivative of a straight spatial line.** The derivative at zero of y+sv is v. [`sol_line_deriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshapeOpen.lean#L246).

**Theorem · Derivative of a shifted cosine.** The derivative at zero of cos(θ+s) is −sin θ. [`sol_cos_deriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshapeOpen.lean#L249).

**Theorem · Derivative of a shifted sine.** The derivative at zero of sin(θ+s) is cos θ. [`sol_sin_deriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshapeOpen.lean#L254).

**Theorem · Derivative along a circle.** The derivative of the angular coordinate curve at zero is radius times the angular unit vector. [`sol_curve_t`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshapeOpen.lean#L259).

**Theorem · Real parts commute with differentiation.** A real derivative of a complex function gives the derivative of its real part by taking the real part of the derivative. [`sol_re_deriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshapeOpen.lean#L274).

**Theorem · Derivative of a harmonic phase.** The derivative of a shifted phase exp(ik(θ+s)) at zero is the phase multiplied by ik. [`sol_exp_deriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshapeOpen.lean#L278).

**Theorem · An angular component in another frame.** The angular component of a vector reconstructed at another angle is the sine-cosine combination of its horizontal coordinates. [`sol_inner_ang`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshapeOpen.lean#L286).

**Theorem · Radial diagonal of a row derivative.** When a row derivative exists at a point of its cell, its radial diagonal entry is the mixed radial derivative of the first profile component times the row phase, taking the real part. [`sol_radial`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshapeOpen.lean#L293).

**Theorem · Axial diagonal entry of a row derivative.** When a row derivative exists at a point of its cell, its axial diagonal entry is the mixed height derivative of the vertical profile component times the row phase, taking the real part. [`sol_axial`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshapeOpen.lean#L322).

**Theorem · Angular diagonal of a row derivative.** When the row derivative exists, radius times its angular diagonal entry is the sum of the radial profile term and angular phase derivative term. [`sol_angular`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshapeOpen.lean#L384).

**Theorem · Solenoidality on the axis.** For a zero-mode solenoidal profile, twice the radial derivative of its first component plus the height derivative of its third component vanishes on the axis. [`sol_axis_identity`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshapeOpen.lean#L424).

**Theorem · Rows have zero derivative trace.** For valid row data and mixing supported in cell and harmonic blocks, the trace of the total Fréchet derivative of each row is zero at every point in its cell solid. [`rowSolenoidal_of_mixSame`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenModelRowshapeOpen.lean#L450).

**Reader note.** Lean defines fderiv as zero where the Fréchet derivative does not exist; this pointwise trace statement uses that totalized derivative.

### Breakdown.FracCell.GivenProfileBounds

This module passes decay and divergence estimates from individual phase-dependent fields to finite parameter-polynomial profiles and their tangent fields. **Reading context:** Appendix B: the represented profile and its regularity, decay and parameter dependence, supplying the data conditions in B.14.

**Theorem · Reconstruct from Cartesian components.** The vector reconstructed from three components is the sum of those components times the Cartesian unit vectors. [`ofComponents_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBounds.lean#L15).

**Theorem · Reduced fields are phase differentiable.** Every component of the reduced field is differentiable with respect to its phase parameter. [`reducedField_diff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBounds.lean#L20).

**Theorem · Physical field is phase differentiable.** At every spatial point, the reconstructed field is differentiable in the phase parameter. [`fieldOf_phase_differentiable`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBounds.lean#L29).

**Theorem · A regular phase derivative exists.** Valid field data with high radial order one give a phase derivative that is C¹, divergence-free and has inverse-distance and inverse-square decay bounds for its value and spatial derivative. [`fieldOf_phaseDeriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBounds.lean#L43).

**Theorem · The phase is bounded on parameter boxes.** The profile phase is uniformly bounded on every finite parameter box. [`phase_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBounds.lean#L52).

**Theorem · Bound parameter monomials on a box.** On a parameter box, the absolute value of a parameter monomial is at most the product of the absolute box radii to its exponents. [`monomial_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBounds.lean#L69).

**Theorem · Use an absolute coefficient in a bound.** For nonnegative weight, an upper bound with coefficient c remains valid when c is replaced by its absolute value. [`le_abs_mul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBounds.lean#L79).

**Theorem · Uniform profile and derivative decay.** Valid profile data give one bound over the parameter box with decay orders 1, 2 and 3 for the profile, its first derivative and its assigned second derivative. [`profile_bounds_everywhere`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBounds.lean#L82).

**Theorem · Divergence preserves finite sums.** At a point where all summands are differentiable, divergence of a finite sum equals the sum of divergences. [`div_sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBounds.lean#L189).

**Theorem · Divergence is linear in smooth fields.** At a common differentiability point, divergence of a real linear combination is the same combination of divergences. [`div_lin`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBounds.lean#L203).

**Theorem · Collect weighted decay coefficients.** Weighted sums sharing a nonnegative decay factor satisfy the bound with absolute coefficient factors. [`sum_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBounds.lean#L212).

**Theorem · Norm of paired finite linear sums.** The norm of a finite sum of paired real multiples is bounded by the sum of their absolute coefficients times vector norms. [`norm_sum_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBounds.lean#L223).

**Theorem · Profile tangents are regular and decay.** Each tangent field of valid profile data is C¹ and divergence-free with value and derivative decay of orders 1 and 2. [`profile_tangent_regular`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBounds.lean#L230).

**Theorem · Parameter shifts are regular and decay.** Each profile tangent used as a parameter shift is C¹ and divergence-free with the value and gradient decay. [`shift_regular_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBounds.lean#L339).

**Theorem · Transfer decay to a certificate profile.** A valid profile instance has uniform value and gradient decay over its parameter box and the second-derivative decay almost everywhere. [`profile_bounds_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBounds.lean#L345).

### Breakdown.FracCell.GivenProfileBoundsField

This module glues near-field and far-field estimates into global field decay and proves regularity of the phase derivative. **Reading context:** Appendix B: the represented profile and its regularity, decay and parameter dependence, supplying the data conditions in B.14.

**Theorem · Convert a near bound to weighted decay.** For 0≤k≤3 and 0≤s≤R, the constant A is at most |A|(1+R)³(1+s)⁻ᵏ. [`weight_near`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsField.lean#L16).

**Theorem · Replace far powers by shifted powers.** For radius at least 1 and exponent between 0 and 3, a power s⁻ᵏ is bounded using 8 times the shifted weight (1+s)⁻ᵏ. [`weight_far`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsField.lean#L34).

**Theorem · Near bound with a combined coefficient.** For 0≤k≤3 and 0≤s≤R, enlarging the near-field coefficient |A|(1+R)³ by 8|D| still bounds A after multiplication by (1+s)⁻ᵏ. [`weight_near_sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsField.lean#L56).

**Theorem · Far bound with a combined coefficient.** The combined near and far coefficient dominates the far power-decay bound when the radius is beyond R≥1. [`weight_far_sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsField.lean#L64).

**Theorem · Extend continuous zero divergence.** A C¹ field whose divergence vanishes almost everywhere has divergence zero at every point. [`divergence_zero_of_ae`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsField.lean#L74).

**Theorem · A reconstructed field is C¹.** Valid chart and field data with high radial order one reconstruct a continuously differentiable field at every phase. [`fieldOf_contDiff_one`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsField.lean#L84).

**Theorem · Uniform local field and gradient bounds.** With phase and position bounded, valid field data with high radial order one give uniform bounds on the field, its derivative and the derivative's Lipschitz constant on unit balls. [`fieldOf_near_bounds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsField.lean#L92).

**Theorem · Global field and derivative decay.** For bounded phase, valid field data with high radial order one give C¹ fields with decay orders 1 and 2 and local derivative Lipschitz constants decaying with order 3. [`fieldOf_decay`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsField.lean#L121).

**Theorem · Reconstructed field is divergence-free.** A field reconstructed from valid chart and field data with high radial order one has zero divergence everywhere. [`fieldOf_divergence`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsField.lean#L145).

**Theorem · Joint C² regularity almost everywhere.** At a fixed phase, the jointly phase-spatial reconstructed field is twice continuously differentiable at almost every spatial point. [`fieldOf_joint_contDiffAt_ae`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsField.lean#L149).

**Theorem · A smooth phase derivative is solenoidal.** With valid chart and field data of high radial order one, at a point of joint C² regularity, the spatial field obtained by phase differentiation has zero divergence. [`phaseDeriv_div_of_smooth`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsField.lean#L175).

**Theorem · Regularity and decay of phase slopes.** For valid field data with high radial order one, phase differentiation gives a C¹ divergence-free field with inverse-distance value decay and inverse-square gradient decay. [`fieldOf_phaseDeriv_regular`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsField.lean#L234).

### Breakdown.FracCell.GivenProfileBoundsFieldParts

This module decomposes phase dependence into four fixed mode fields, then proves joint derivative regularity and quantitative far-field bounds for the field and phase derivative. **Reading context:** Appendix B: the represented profile and its regularity, decay and parameter dependence, supplying the data conditions in B.14.

**Definition · Scale every spline coefficient.** Spline scaling preserves the mesh and multiplies every polynomial piece by a complex constant. [`splineScale`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L16).

**Definition · Scale the four mode amplitudes.** Amplitude scaling multiplies the radial, polar, stream and swirl spline amplitudes by the same complex constant. [`ampScale`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L18).

**Definition · Quarter-turn a pair of modes.** The modified field data multiply mode n by −i and mode −n by i, leaving other amplitudes unchanged. [`quarterTurnData`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L21).

**Theorem · Spline scaling commutes with evaluation.** Evaluating a scaled spline multiplies the original value by the scaling constant. [`splineScale_eval`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L25).

**Theorem · Twisted scaling respects constants.** A constant complex factor can be pulled through the twisted scaling operator. [`twisted_const_mul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L30).

**Theorem · Height derivatives preserve constants.** A constant complex factor can be pulled through the height derivative. [`height_const_mul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L36).

**Theorem · Quarter-turn the reduced mode.** For a nonzero mode n, the quarter-turned field data multiply its reduced field by −i. [`reduced_quarter`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L41).

**Theorem · Reduced fields are affine in phase.** Each reduced field component at phase β is (1−β) times its phase-zero value plus β times its phase-one value. [`reduced_affine`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L84).

**Theorem · Separate a change in phase.** The phase at β factors as the phase at c times the exponential of the phase difference multiplied by mode and logarithmic phase. [`phase_split`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L94).

**Theorem · Real part after a complex rotation.** Multiplication by exp(ia) turns a complex real part into cosine times its real part minus sine times its imaginary part. [`re_rot`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L102).

**Theorem · Separate affine phase contributions.** An affine interpolation of two complex amplitudes with the phase factors splits into the corresponding two weighted real parts. [`combo_re`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L109).

**Theorem · A mode uses four fixed phase fields.** A nonzero mode at arbitrary phase is a sine-cosine combination of its original and quarter-turned fields at phases zero and one. [`mode_phase_identity`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L117).

**Theorem · Local Lipschitzness under bilinear maps.** Applying a continuous bilinear map to two locally Lipschitz functions gives a locally Lipschitz function. [`locSlope_bilin`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L153).

**Theorem · Spatial derivative of a weighted field.** For a C² phase-spatial weight and C¹ field, the spatial derivative is weight times field derivative plus the weight derivative acting on the field value. [`term_fderiv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L208).

**Theorem · Weighted derivative is locally Lipschitz.** The product-rule derivative is jointly locally Lipschitz when its weight is C², its field is C¹ and the field derivative is locally Lipschitz. [`term_locSlope`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L218).

**Theorem · Local Lipschitzness of four terms.** A four-term field with C² scalar weights and C¹ fixed fields with locally Lipschitz derivatives has a jointly locally Lipschitz spatial derivative. [`four_locSlope`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L235).

**Theorem · The logarithmic phase is C².** The logarithmic phase is twice continuously differentiable. [`logPhase_smooth`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L248).

**Definition · Four phase interpolation coefficients.** The four weights combine β and 1−β with sine and cosine of the logarithmic phase differences. [`waveCoef`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L253).

**Definition · Four fixed mode fields.** The four fixed fields are the original and quarter-turned mode fields evaluated at phases zero and one. [`waveParts`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L259).

**Theorem · The four parts reconstruct a mode.** A nonzero mode field equals the sum of the four fixed fields multiplied by their phase-dependent weights. [`mode_eq_parts`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L263).

**Theorem · The interpolation coefficients are C².** Each of the four phase interpolation coefficients is twice continuously differentiable jointly in phase and position. [`waveCoef_smooth`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L271).

**Theorem · Transfer a property to the four parts.** A property holding for original and quarter-turned modes at every phase holds for each of the four selected fields. [`waveParts_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L276).

**Theorem · Joint regularity from the four parts.** C¹ regularity and locally Lipschitz spatial derivatives for the fixed original and quarter-turned modes give joint local Lipschitzness of the mode derivative. [`wave_joint_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L285).

**Theorem · Differentiate the four phase weights.** The phase derivative of a nonzero mode is the sum of its fixed fields times the phase directional derivatives of the four weights. [`mode_phase_hasDerivAt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L298).

**Theorem · Reconstruction commutes with finite sums.** Reconstructing summed Cartesian components equals the finite sum of the reconstructed vectors. [`ofComponents_finsum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L310).

**Theorem · The field is its finite mode sum.** The reconstructed field equals the sum of its listed mode fields. [`fieldOf_eq_modeSum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L315).

**Theorem · The zero mode is phase independent.** The zero-mode field has the same value at every phase as at phase zero. [`mode_zero_indep`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L324).

**Definition · The phase derivative of one mode.** The phase-derivative term is zero for mode zero and otherwise sums the four fixed fields weighted by phase derivatives of their coefficients. [`phaseTerm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L329).

**Theorem · The phase derivative is a mode sum.** The phase derivative of the reconstructed field is the sum of the phase-derivative terms over its listed modes. [`phaseDeriv_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L332).

**Theorem · C¹ phase slopes from smooth modes.** If the original and quarter-turned nonzero mode fields are C¹ at every phase, the field's phase derivative is C¹ in space. [`phaseDeriv_contDiff_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L352).

**Theorem · Scaling commutes with chart derivatives.** Multiplication by a constant polynomial commutes with every order of differentiation in the first chart coordinate. [`tDeriv_C_mul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L373).

**Theorem · Scaling commutes with height derivatives.** Multiplication by a constant polynomial commutes with every order of differentiation in the second chart coordinate. [`xDeriv_C_mul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L380).

**Theorem · Scaling commutes with first substitution.** Substituting the first polynomial coordinate commutes with multiplying by a complex constant. [`atFirst_C_mul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L387).

**Theorem · Scaling respects second substitution.** Substituting the second polynomial coordinate commutes with multiplying by a complex constant. [`atSecond_C_mul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L391).

**Theorem · Scaling preserves the spline class.** Scaling a spline preserves its orders of matching and parity class. [`splineScale_class`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L395).

**Theorem · Conjugation of a scaled spline.** Conjugating a scaled spline conjugates both the scaling constant and the original spline. [`splineScale_conj`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L411).

**Theorem · Conjugation of scaled amplitudes.** Conjugating scaled mode amplitudes conjugates the scalar and the amplitude data. [`ampScale_conj`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L415).

**Theorem · Quarter-turned amplitudes are scaled.** Every amplitude in the quarter-turned data is either unchanged or a complex scalar multiple of its original amplitude. [`quarter_amp_cases`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L419).

**Theorem · Quarter-turning leaves mode zero fixed.** Quarter-turning a nonzero mode leaves the zero-mode amplitude unchanged. [`quarter_amp_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L427).

**Theorem · Conjugating a spline twice restores it.** Applying spline conjugation twice returns the original spline. [`spline_conj_conj`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L433).

**Theorem · Amplitude conjugation is an involution.** Applying amplitude conjugation twice returns the original amplitude data. [`amp_conj_conj`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L437).

**Theorem · Quarter-turning preserves validity.** Quarter-turning a nonzero mode of valid field data with high radial order one preserves the field-data conditions. [`quarterTurnData_isFieldData`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L441).

**Theorem · Reconstructed field is differentiable.** Valid chart and field data with high radial order one give a spatially differentiable reconstructed field at every phase. [`fieldOf_differentiable`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L503).

**Theorem · Almost everywhere zero divergence.** A reconstructed field from valid field data with high radial order one has divergence zero almost everywhere in space. [`fieldOf_div_ae`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L507).

**Theorem · A vector is its coordinate sum.** A vector reconstructed from components is their sum against the Cartesian unit coordinate vectors. [`ofComponents_sum_form`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L512).

**Theorem · Reduced fields are continuous in phase.** At fixed chart coordinates, each reduced field component depends continuously on phase. [`reducedField_phase_continuous`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L517).

**Theorem · Field values are continuous in phase.** At every spatial point, the reconstructed field depends continuously on phase. [`fieldOf_phase_continuous`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L526).

**Theorem · Listed mode fields are C¹.** Every listed mode of valid field data with high radial order one reconstructs a continuously differentiable field. [`mode_contDiff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L534).

**Theorem · Differentiate the finite mode sum.** For valid field data with high radial order one, the spatial derivative of the field is the sum of the spatial derivatives of its listed modes. [`fieldOf_fderiv_modes`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L554).

**Theorem · Local Lipschitzness of wave slopes.** With valid chart and field data of high radial order one, the spatial derivative of each listed nonzero mode is locally Lipschitz jointly in phase and position. [`modeField_fderiv_joint_locallySlope_wave`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L562).

**Theorem · Joint local Lipschitzness of mode slopes.** With valid chart and field data of high radial order one, the spatial derivative of every listed mode is locally Lipschitz jointly in phase and position. [`mode_joint_locallySlope`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L571).

**Theorem · Derivative bounds on joint closed balls.** With valid chart and field data of high radial order one, the spatial derivative of the reconstructed field has a finite Lipschitz bound on every closed ball in phase-position space. [`fieldOf_fderiv_joint_slopeOn`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L586).

**Theorem · Spatial derivative is jointly continuous.** Valid field data with high radial order one give a spatial derivative continuous jointly in phase and position. [`fderiv_joint_continuous_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L618).

**Theorem · The field is jointly continuous.** With valid chart and field data of high radial order one, the reconstructed field is continuous jointly in phase and position. [`fieldOf_joint_continuous`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L626).

**Theorem · Joint continuity of the field derivative.** With valid chart and field data of high radial order one, the spatial derivative of the reconstructed field is continuous jointly in phase and position. [`fieldOf_fderiv_joint_continuous`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L660).

**Theorem · Uniform gradient Lipschitz bounds.** With valid chart and field data of high radial order one, for bounded phase, the spatial field derivatives share one Lipschitz bound on each chosen closed spatial ball. [`fieldOf_fderiv_slope_uniform`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L665).

**Predicate · Far-field bounds on unit balls.** The far-ball condition records differentiability and uniform power bounds for the field, derivative and derivative Lipschitz constant on distant unit balls. [`FarBall`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L686).

**Theorem · Multiply decay powers.** For positive base, multiplying negative real powers adds their decay exponents. [`pw_mul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L691).

**Theorem · Lipschitz bound for a bilinear product.** A norm-controlled bilinear product has Lipschitz constant K₁M₂+M₁K₂ under the input Lipschitz and size bounds. [`slopeOn_bilin`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L696).

**Theorem · Derivative bound gives a Lipschitz bound.** A differentiable function whose derivative is bounded by M on a unit ball is Lipschitz there with nonnegative part of M as constant. [`slopeOn_ball_of_fderiv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L730).

**Theorem · Relax far-ball estimates.** A far-ball estimate remains valid after decreasing decay order, increasing its constant and moving the starting radius outward. [`farBall_weaken`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L737).

**Theorem · Add far-ball estimates.** Two far-ball estimates of the same decay order add with summed constants and the larger starting radius. [`farBall_add`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L748).

**Theorem · Uniform far bounds pass to finite sums.** Uniform far-ball estimates for finitely many parameter-dependent fields give a uniform far-ball estimate for their sum. [`farBall_sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L772).

**Theorem · Evaluate the rank-one operator map.** The continuous bilinear rank-one construction applied to a functional and vector gives their scalar-multiplication operator. [`srl_apply`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L794).

**Theorem · Multiply scalar and vector far estimates.** Multiplying scalar and vector fields with far-ball estimates adds their decay orders, with the factor 4 in the constant. [`farBall_smul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L797).

**Definition · An affine trigonometric expression.** The auxiliary trigonometric function is an affine coefficient times cosine plus another affine coefficient times sine at a common frequency. [`trigLin`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L870).

**Theorem · Differentiate an affine trig sum.** The derivative of the auxiliary trigonometric expression has the same form with the four transformed coefficients. [`trigLin_hasDerivAt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L872).

**Theorem · Bound an affine trigonometric sum.** The auxiliary trigonometric expression is bounded by the sum of absolute coefficients times 1+|u|. [`trigLin_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L885).

**Theorem · Bound the differentiated coefficients.** The sum of absolute differentiated coefficients is at most 1+|k| times the original coefficient sum. [`trigLin_coef`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L898).

**Theorem · Far estimates for a scalar composition.** The logarithmic-coordinate bounds and two derivative bounds for the scalar function imply the specified far-ball estimate for their composition. [`farBall_comp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L905).

**Theorem · Extend pointwise decay to nearby balls.** Pointwise field, derivative and local derivative estimates give a far-ball bound with the enlarged constant and starting radius. [`farBall_of_pointwise`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L972).

**Theorem · Spatial slope of the logarithmic phase.** The logarithmic phase derivative is the inner-product functional at y divided by r_c²+‖y‖². [`logPhase_hasFDerivAt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L1013).

**Theorem · Norm difference on a unit ball.** Points in a unit ball have norms bounded by each other's norm plus 1. [`ball_norms`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L1029).

**Theorem · Far bounds for the logarithmic phase.** Beyond norm 2, the logarithmic phase has the growth, inverse-distance derivative and inverse-square derivative Lipschitz bounds on unit balls. [`logPhase_far`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L1036).

**Theorem · Far bounds for trigonometric phase terms.** Affine sine-cosine expressions of the logarithmic phase satisfy the far-ball bound with growth exponent ε and coefficient-frequency control. [`farBall_trig`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L1179).

**Theorem · Fixed-phase modes have far decay.** Every listed mode at fixed phase has a far-ball decay estimate of order 1+ε. [`mode_farBall`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L1208).

**Theorem · Interpolation weights are trigonometric.** Each interpolation weight is a sine-cosine expression of logarithmic phase with the phase and frequency bounds. [`waveCoef_trig`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L1218).

**Theorem · Uniform far bounds for phase weights.** With phase bounded, each interpolation weight has a uniform far-ball estimate with growth exponent ε. [`waveCoef_farBall`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L1246).

**Theorem · Phase derivatives are trigonometric.** The phase derivative of an interpolation weight is an affine sine-cosine expression of the logarithmic phase. [`waveCoef_dtrig`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L1263).

**Theorem · Fixed mode parts have far decay.** Each of the four fixed fields for a listed nonzero mode has a far-ball decay estimate of order 1+ε. [`waveParts_farBall`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L1296).

**Theorem · Uniform decay of modes in bounded phase.** For bounded phase, each listed mode has a uniform far-ball decay estimate of order 1. [`modeField_farBall_unif`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L1303).

**Theorem · Phase-derivative terms have far decay.** Every listed phase-derivative mode term at a fixed phase has a far-ball decay estimate of order 1. [`phaseTerm_farBall`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L1325).

**Theorem · Uniform far-field and gradient decay.** With valid chart and field data of high radial order one, for bounded phase and sufficiently large norm, the reconstructed field, its derivative and its local derivative Lipschitz constant have decay orders 1, 2 and 3. [`fieldOf_far_bounds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L1361).

**Theorem · The phase derivative is C¹.** For valid field data with high radial order one, the phase derivative at a fixed phase is continuously differentiable in space. [`phaseDeriv_contDiff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L1381).

**Theorem · Far decay of the phase derivative.** With valid chart and field data of high radial order one, at a fixed phase, the phase derivative and its spatial derivative have far-field decay of orders 1 and 2. [`phaseDeriv_far_bounds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileBoundsFieldParts.lean#L1387).

### Breakdown.FracCell.GivenProfileCentre

This module specializes a valid profile to the central parameter and transfers smoothness, weak second derivatives, symmetry and decay to the centre fields. **Reading context:** Appendix B: the represented profile and its regularity, decay and parameter dependence, supplying the data conditions in B.14.

**Definition · Certificate data filled from a profile.** The auxiliary certificate instance replaces order, radii, rates, multiplier, profile, second derivative and fractional-power field with those from the supplied profile data. [`instanceOf`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileCentre.lean#L19).

**Theorem · The constructed profile instance matches.** The certificate record filled from the profile satisfies the profile-instance equalities by construction. [`instanceOf_isInstance`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileCentre.lean#L29).

**Theorem · The centre parameter lies in the box.** For valid profile data, the zero parameter lies in the parameter box of the constructed certificate instance. [`zero_mem_box`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileCentre.lean#L33).

**Theorem · The total second derivative is symmetric.** For a globally differentiable field, its totalized second Fréchet derivative is symmetric in the two direction arguments. [`second_symm_of_differentiable`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileCentre.lean#L37).

**Theorem · The centre field is C¹.** A valid centre instance has a continuously differentiable centre field. [`centre_smooth_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileCentre.lean#L48).

**Theorem · The centre has a weak second derivative.** A valid centre instance supplies an almost everywhere strongly measurable weak second derivative of its gradient. [`centre_second_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileCentre.lean#L53).

**Theorem · The centre is divergence-free.** A valid centre instance has zero divergence everywhere. [`centre_divergence_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileCentre.lean#L64).

**Theorem · The centre has the class symmetries.** A valid centre instance belongs to the field class of its recorded symmetry order. [`centre_class_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileCentre.lean#L69).

**Theorem · The centre and its derivatives decay.** A valid centre instance has one decay bound of orders 1, 2 and 3 for its value, gradient and second derivative. [`centre_bounds_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileCentre.lean#L74).

**Theorem · Centre second derivative is symmetric.** A valid centre instance has a second-derivative field symmetric in its two direction arguments. [`centreSecond_symm_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileCentre.lean#L84).

### Breakdown.FracCell.GivenProfileCentreTrace

This module derives the centre curl-gradient trace identity from symmetry of the centre second derivative. **Reading context:** Appendix B: the represented profile and its regularity, decay and parameter dependence, supplying the data conditions in B.14.

**Theorem · Diagonal curl-gradient entries.** A diagonal curl-gradient entry equals the alternating sum of second-derivative coordinates. [`diag_entry`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileCentreTrace.lean#L16).

**Theorem · Symmetric second derivatives cancel.** A tensor symmetric in its derivative directions gives a curl-gradient matrix of trace zero. [`trace_zero_of_symm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileCentreTrace.lean#L25).

**Theorem · The centre curl gradient has trace zero.** A valid centre instance has zero coordinate trace for its curl-gradient field at every point. [`centreTraceFree_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileCentreTrace.lean#L37).

### Breakdown.FracCell.GivenProfileDefs

This module defines the tangent fields of the finite-parameter profile by differentiating at the central parameter. **Reading context:** Appendix B: the represented profile and its regularity, decay and parameter dependence, supplying the data conditions in B.14.

**Definition · Tangent to a profile parameter.** The ith tangent field is the derivative of the profile with respect to the ith parameter direction at parameter zero. [`tangentField`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDefs.lean#L22).

### Breakdown.FracCell.GivenProfileDrift

This module uses drift linearity and decay to place profile drifts in L² and establish continuity of profile gradients in their squared-entry integral. **Reading context:** Appendix B: the represented profile and its regularity, decay and parameter dependence, supplying the data conditions in B.14.

**Theorem · Axial turning is additive.** The infinitesimal axial-turn map preserves vector addition. [`turn_add`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDrift.lean#L17).

**Theorem · Axial turning commutes with scaling.** The infinitesimal axial-turn map preserves real scalar multiplication. [`turn_smul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDrift.lean#L20).

**Theorem · Axial turning sends zero to zero.** The infinitesimal axial-turn map sends the zero vector to zero. [`turn_zero'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDrift.lean#L23).

**Theorem · Axial turning is continuous.** The infinitesimal axial-turn map is continuous. [`continuous_axialTurn'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDrift.lean#L26).

**Theorem · Drift is additive in field and gradient.** Adding two fields and their assigned gradients adds their drift expressions at fixed exponent and rotation rate. [`drift_add`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDrift.lean#L30).

**Theorem · Drift commutes with real scaling.** Scaling a field and its assigned gradient by the same real constant scales the drift by that constant. [`drift_smul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDrift.lean#L36).

**Theorem · Zero field and gradient give zero drift.** The drift of the zero field with zero assigned gradient is zero. [`drift_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDrift.lean#L41).

**Theorem · Drift respects finite linear sums.** The drift of a finite real linear combination of fields and gradients is the same combination of their drift expressions. [`drift_sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDrift.lean#L45).

**Theorem · Derivative of the profile's finite sum.** The profile derivative is the sum of the component field derivatives weighted by the parameter monomials. [`profile_hasFDerivAt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDrift.lean#L61).

**Theorem · The parameter box is compact.** Every finite-dimensional parameter box is compact. [`box_compact`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDrift.lean#L73).

**Theorem · Profile coefficient bounds on the box.** All listed parameter monomials and the phase share one uniform bound on the profile parameter box. [`box_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDrift.lean#L79).

**Theorem · Entry energy is bounded by operator norm.** The sum of squared operator entries is at most three times the squared operator norm. [`entrySq_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDrift.lean#L96).

**Theorem · Entry energy varies continuously.** The sum of squared operator entries is continuous in the operator. [`entrySq_continuous`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDrift.lean#L108).

**Theorem · Inverse-square decay gives L² membership.** An almost everywhere strongly measurable spatial vector field with the inverse-square decay belongs to L². [`memLp_two_of_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDrift.lean#L112).

**Theorem · The drift expression is measurable.** The drift formed from a continuous field and its total derivative is measurable. [`drift_measurable`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDrift.lean#L130).

**Theorem · The reconstructed drift belongs to L².** At the matching exponent and phase, the drift of a field reconstructed from valid data with high radial order one belongs to L². [`fieldOf_drift`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDrift.lean#L153).

**Theorem · Every certificate profile has L² drift.** For a valid profile instance at its assigned exponent, the profile drift belongs to L² at every parameter in the box. [`profile_drift_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDrift.lean#L165).

**Theorem · Energy continuity of profile gradients.** For a valid profile instance, nearby parameters in the box have arbitrarily small integrated squared-entry difference between their profile gradients. [`profile_continuous_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDrift.lean#L197).

### Breakdown.FracCell.GivenProfileDriftLocal

This module differentiates the combined dilation and rotation flow, exposes the cancellation in the drift formula and proves quadratic vanishing of its reduced far-field terms. **Reading context:** Appendix B: the represented profile and its regularity, decay and parameter dependence, supplying the data conditions in B.14.

**Definition · Rotation in the horizontal plane.** The plane-turn map rotates the first two coordinates by θ and fixes the third. [`planeTurn`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDriftLocal.lean#L20).

**Theorem · Coordinates of the plane rotation.** The plane-turn map has the sine-cosine horizontal coordinates and unchanged height. [`planeTurn_coords`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDriftLocal.lean#L24).

**Theorem · Plane rotation preserves norm.** The plane-turn map preserves the Euclidean norm. [`norm_planeTurn`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDriftLocal.lean#L29).

**Theorem · Norm under positive exponential scaling.** Scaling a vector by exp τ multiplies its norm by exp τ. [`norm_scale`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDriftLocal.lean#L37).

**Theorem · Rotation does not change the flow radius.** The norm after exponential dilation and rotation equals the norm after dilation alone. [`flowPoint_norm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDriftLocal.lean#L40).

**Theorem · The flow preserves height ratio.** Exponential dilation combined with horizontal rotation preserves the normalized height coordinate. [`flowPoint_height`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDriftLocal.lean#L44).

**Theorem · Rotation factors out of a mode phase.** When the first coordinate is nonzero, the mode phase under dilation and rotation is the dilated phase multiplied by the integer-mode rotation exponential. [`flowPoint_modePhase`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDriftLocal.lean#L53).

**Theorem · Frames under dilation and rotation.** At a nonzero point, the reduced radial, polar and azimuthal frames under dilation and rotation have the rotated horizontal components and unchanged vertical components. [`flowPoint_frames`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDriftLocal.lean#L99).

**Theorem · Undo a rotation in the first component.** Under c²+s²=1, the linear combination of real harmonic frame sums recovers their original first horizontal component. [`re_turn_combo`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDriftLocal.lean#L137).

**Theorem · Undo a rotation in the second component.** Under c²+s²=1, the linear combination of real harmonic frame sums recovers their original second horizontal component. [`re_turn_combo'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDriftLocal.lean#L152).

**Theorem · The rotated-back field along the flow.** When the first coordinate is nonzero, rotating back a dilated and rotated field leaves fixed frame vectors and inserts the mode rotation phases in its reduced expansion. [`flow_identity`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDriftLocal.lean#L167).

**Definition · The reduced dilation-rotation drift term.** The reduced flow term combines the weighted field, its chart derivative and the rotational correction weighted by one minus the core ratio. [`flowTerm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDriftLocal.lean#L229).

**Theorem · Split the plane rotation into directions.** Plane rotation decomposes into cosine times the horizontal projection, sine times axial turning and the unchanged vertical projection. [`planeTurn_split`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDriftLocal.lean#L236).

**Theorem · Recover a point from planar parts.** Adding the horizontal coordinate projection and the vertical coordinate projection returns the original point. [`split_base`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDriftLocal.lean#L242).

**Theorem · Velocity of the dilation-rotation flow.** The derivative at zero of the exponential dilation and angular-speed flow is y plus its angular speed times axial turning of y. [`curve_hasDerivAt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDriftLocal.lean#L247).

**Theorem · Zero-angle rotation is the identity.** Plane rotation by zero leaves every vector unchanged. [`planeTurn_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDriftLocal.lean#L268).

**Theorem · The flow starts at the original point.** The exponential dilation and rotation flow at parameter zero equals its starting point. [`curve_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDriftLocal.lean#L273).

**Theorem · The chart radius under dilation.** The compactified radius under exponential dilation is the dilated norm divided by that norm plus L₀. [`scaled_chartT`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDriftLocal.lean#L278).

**Theorem · Dilation derivative of the chart radius.** The chart-radius derivative along exponential dilation at zero is t(1−t). [`chartT_hasDerivAt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDriftLocal.lean#L283).

**Theorem · Dilation derivative of the decay factor.** Along exponential dilation, the decay factor has derivative −2εt times its original value at zero. [`decay_hasDerivAt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDriftLocal.lean#L298).

**Theorem · Positive dilation preserves the angle.** Exponential dilation leaves the angular coordinate unchanged. [`angleOf_scale`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDriftLocal.lean#L315).

**Theorem · Dilation derivative of logarithmic phase.** Along exponential dilation, the derivative of logarithmic phase at zero equals the core ratio at the compactified radius. [`logPhase_hasDerivAt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDriftLocal.lean#L322).

**Theorem · Differentiate the combined mode phase.** The dilation-rotation phase derivative is its original phase multiplied by i times the sum of the rotation frequency and logarithmic-phase contribution. [`phase_hasDerivAt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDriftLocal.lean#L354).

**Theorem · Differentiate a generic reduced field.** Away from height zero and spline breaks, the reduced field along dilation has derivative t(1−t) times its chart derivative. [`reduced_hasDerivAt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDriftLocal.lean#L388).

**Theorem · Differentiate the reduced flow expansion.** At a generic chart point, the real mode expansion along the dilation-rotation flow differentiates by the decay, phase and chart product-rule terms. [`rhs_hasDerivAt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDriftLocal.lean#L406).

**Theorem · Drift cancels first-order terms.** At the matching exponent, phase and rotation speed, the algebraic drift combination equals the expansion in reduced flow terms. [`flow_combo`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDriftLocal.lean#L460).

**Theorem · Drift equals the reduced flow expansion.** Away from coordinate planes and spline breaks, twice the exponent times the physical drift equals the reduced flow-term reconstruction. [`drift_flow_formula_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDriftLocal.lean#L497).

**Theorem · Export the generic drift formula.** At generic points and matching exponent, the physical drift is given by the reduced flow-term formula with the factor 2α. [`drift_flow_formula`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDriftLocal.lean#L610).

**Theorem · Smooth partial derivatives remain smooth.** An infinitely differentiable three-variable function has a smooth first chart partial derivative and the one-variable derivative at each slice. [`partial_t`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDriftLocal.lean#L624).

**Theorem · Vanishing at the endpoint gives decay.** A smooth function vanishing at t=1 has a linear (1−t) bound and its cancellation with (1−t) times its derivative has a quadratic bound on the compact ranges. [`weight_of_vanish`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDriftLocal.lean#L643).

**Definition · Reduced field from four amplitudes.** The generalized reduced field builds the zero-mode stream-swirl formula or the nonzero-mode radial-polar formula from four supplied amplitudes. [`genField`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDriftLocal.lean#L694).

**Theorem · Spline amplitudes give the reduced field.** Substituting the four parity-adjusted spline amplitudes into the generalized field gives the original reduced field. [`reduced_eq_gen`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDriftLocal.lean#L709).

**Theorem · The generalized field vanishes at t=1.** With high-order weight 1, every component of the generalized reduced field vanishes at compactified radius 1. [`gen_vanish`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDriftLocal.lean#L718).

**Theorem · Local equality restricts to chart slices.** Functions equal near a chart point remain equal near its first-coordinate slice through that point. [`slice_t`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDriftLocal.lean#L725).

**Theorem · Restrict local equality to height slices.** Functions equal near a chart point remain equal near its second-coordinate slice through that point. [`slice_x`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDriftLocal.lean#L733).

**Theorem · Multiplication preserves local equality.** Multiplying two locally equal functions by the same chart function preserves their local equality. [`germ_mul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDriftLocal.lean#L741).

**Theorem · Multiply and restrict a height slice.** A common multiplier and restriction to the second-coordinate slice preserve local equality at a chart point. [`slice_x_mul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDriftLocal.lean#L747).

**Theorem · Multiply and restrict a chart slice.** A common multiplier and restriction to the first-coordinate slice preserve local equality at a chart point. [`slice_t_mul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDriftLocal.lean#L752).

**Theorem · Amplitudes determine the local field.** Replacing each amplitude by a locally equal function leaves the generalized reduced field value unchanged at the point. [`gen_eq_of_germ`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDriftLocal.lean#L757).

**Theorem · Local amplitudes determine local fields.** If all four amplitude functions agree locally with replacements, their generalized reduced fields agree locally as well. [`gen_germ`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDriftLocal.lean#L782).

**Theorem · Smooth fields from local amplitudes.** Four amplitudes smooth near a chart point give an infinitely differentiable generalized reduced field jointly in phase and chart coordinates there. [`gen_contDiffAt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDriftLocal.lean#L794).

**Definition · A signed reflected polynomial amplitude.** The polynomial amplitude substitutes the chosen height sign and applies the parity sign for an odd reflected amplitude. [`polyAmp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDriftLocal.lean#L840).

**Theorem · Polynomial amplitudes are smooth.** Every signed reflected polynomial amplitude is infinitely differentiable in its chart coordinates. [`polyAmp_contDiff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDriftLocal.lean#L843).

**Theorem · Polynomial reduced fields are smooth.** Generalized reduced fields built from four signed polynomial amplitudes are infinitely differentiable jointly in phase and chart coordinates. [`gen_poly_contDiff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDriftLocal.lean#L847).

**Theorem · A spline equals one polynomial locally.** Away from mesh breaks and height zero, spline evaluation agrees locally with the appropriately reflected selected polynomial piece. [`spline_germ`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDriftLocal.lean#L855).

**Theorem · Cell indices stay within the mesh range.** The index selected by a list of breaks is at most the number of breaks. [`cellIndex_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDriftLocal.lean#L878).

**Theorem · Weighted bounds from endpoint zeros.** With valid chart and field data of high radial order one, on the generic chart domain and bounded phase range, reduced fields have linear endpoint decay and the derivative-corrected combination has quadratic endpoint decay. [`reduced_weight_bounds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDriftLocal.lean#L884).

**Theorem · The core-ratio gap vanishes at infinity.** For valid chart parameters and 0≤t<1, one minus the core ratio lies between zero and max(2,4r_c²/L₀²)(1−t). [`core_gap_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDriftLocal.lean#L971).

**Theorem · Reduced drift terms vanish quadratically.** With valid chart and field data of high radial order one, on the generic chart domain with phase and rotation speed bounded, every listed reduced flow term is bounded by a constant times (1−t)². [`flowTerm_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDriftLocal.lean#L1013).

### Breakdown.FracCell.GivenProfileDriftSt

This module extends generic-point drift estimates to all of space and exports the phase continuity and gradient bounds needed by the profile drift argument. **Reading context:** Appendix B: the represented profile and its regularity, decay and parameter dependence, supplying the data conditions in B.14.

**Theorem · Almost everywhere phase continuity.** At almost every spatial point, the field's spatial derivative depends continuously on phase. [`grad_continuous_main`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDriftSt.lean#L23).

**Theorem · Extend continuous inequalities.** An almost everywhere inequality between continuous real spatial functions holds at every point. [`le_of_ae_le_continuous`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDriftSt.lean#L48).

**Theorem · The drift of a C¹ field is continuous.** The drift expression formed from a C¹ field and its derivative is continuous in space. [`drift_continuous`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDriftSt.lean#L59).

**Theorem · A vector norm bound by its components.** The norm of a vector reconstructed from components is bounded by the sum of their absolute values. [`norm_ofComponents_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDriftSt.lean#L72).

**Theorem · Normalized coordinates are bounded.** The absolute value of any Cartesian coordinate divided by the vector norm is at most 1. [`coord_div_norm_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDriftSt.lean#L77).

**Theorem · Reduced frame coordinates are bounded.** Every component of the radial, polar and azimuthal reduced frame vectors has absolute value at most 1. [`frame_bounds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDriftSt.lean#L84).

**Theorem · Drift decays at generic points.** With valid chart and field data of high radial order one, for the matching fractional exponent and phase, the drift has inverse-square decay away from coordinate planes and all spline breaks. [`fieldOf_drift_generic`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDriftSt.lean#L118).

**Theorem · Drift decays everywhere.** With valid chart and field data of high radial order one, for the matching fractional exponent and phase, the reconstructed field's drift has an inverse-square decay bound at every spatial point. [`drift_bound_main`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDriftSt.lean#L221).

**Theorem · Valid fields are differentiable.** Valid chart and field data with high radial order one give a differentiable spatial field at every phase. [`fieldOf_differentiable`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDriftSt.lean#L247).

**Theorem · Uniform gradient decay in bounded phase.** With valid chart and field data of high radial order one, for bounded phase, the reconstructed field gradients have a common inverse-square decay bound. [`fieldOf_grad_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDriftSt.lean#L252).

**Theorem · Almost everywhere gradient continuity.** For valid field data with high radial order one, the spatial gradient depends continuously on phase at almost every spatial point. [`fieldOf_grad_continuous`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDriftSt.lean#L259).

**Theorem · Export the global drift decay bound.** With valid chart and field data of high radial order one, at the phase tied to rotation rate and exponent, the drift has a global inverse-square decay bound. [`fieldOf_drift_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileDriftSt.lean#L264).

### Breakdown.FracCell.GivenProfileFarModeBounds

This module turns a radial-angular decomposition into quantitative decay of a mode field, its derivative and its derivative Lipschitz constant on distant unit balls. **Reading context:** Appendix B: the represented profile and its regularity, decay and parameter dependence, supplying the data conditions in B.14.

**Predicate · A slope bound on a set.** The slope-bound predicate bounds every output difference by K times the corresponding input difference on the set. [`SlopeBoundOn`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeBounds.lean#L15).

**Predicate · Field and derivative bounds on a ball.** The ball-data predicate records differentiability, value and derivative bounds and a derivative slope bound on a unit ball. [`BallData`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeBounds.lean#L18).

**Theorem · Derivative bounds give ballwise slopes.** Differentiability and a uniform derivative bound on an open ball give the same bound for all secant slopes there. [`slopeBoundOn_of_fderiv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeBounds.lean#L22).

**Theorem · Slope bounds depend only on set values.** A field equal on the set to one satisfying a slope bound inherits that slope bound. [`slopeBoundOn_congr`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeBounds.lean#L27).

**Theorem · Increase a slope-bound constant.** A valid slope bound remains valid after its constant is increased. [`slopeBoundOn_mono`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeBounds.lean#L31).

**Theorem · Slope constants add under addition.** Adding two fields with slope bounds gives a slope bound equal to the sum of the constants. [`slopeBoundOn_add`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeBounds.lean#L34).

**Theorem · A slope bound for a scalar product.** The product of a scalar field and a vector field has slope constant k₁v₂+v₁k₂ under the slope and size bounds. [`slopeBoundOn_smul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeBounds.lean#L42).

**Theorem · A slope bound for rank-one operators.** A rank-one operator field built from a functional and vector has slope constant k₁v₂+v₁k₂ under their slope and size bounds. [`slopeBoundOn_smulRight`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeBounds.lean#L58).

**Theorem · Relax ball-data bounds.** Increasing the value, derivative and derivative-slope bounds preserves the ball-data predicate. [`ballData_mono`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeBounds.lean#L79).

**Theorem · Add the three ball-data bounds.** Adding two fields adds their value, derivative and derivative-slope bounds on a common unit ball. [`ballData_add`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeBounds.lean#L83).

**Theorem · Zero has zero ball-data bounds.** The zero field satisfies all three ball-data bounds with constant zero. [`ballData_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeBounds.lean#L93).

**Theorem · Ball-data bounds pass to finite sums.** A finite sum of fields has ball-data bounds given by the sums of the corresponding individual bounds. [`ballData_sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeBounds.lean#L96).

**Theorem · Product estimates on a unit ball.** Scalar multiplication combines ball-data bounds through the product-rule formulas for value, derivative and derivative slope. [`ballData_smul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeBounds.lean#L106).

**Theorem · Derivative of a degree-zero field scales.** For a field invariant under positive dilation, its derivative at z is the inverse scale times the derivative at the rescaled point, under differentiability there. [`hom_fderiv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeBounds.lean#L128).

**Theorem · Scale-dependent angular field bounds.** A degree-zero field differentiable off zero with locally Lipschitz derivative has bounded values, inverse-distance derivative bounds and inverse-square derivative slope bounds on distant unit balls. [`hom_ball`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeBounds.lean#L140).

**Theorem · Derivative of the Euclidean norm.** At a nonzero point, the norm derivative is the inner-product functional with the normalized point. [`norm_hasFDerivAt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeBounds.lean#L198).

**Theorem · The norm derivative has norm one.** At a nonzero point, the continuous linear functional defining the norm derivative has operator norm 1. [`normMap_norm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeBounds.lean#L214).

**Theorem · Control a change of direction.** For nonzero z and w, their normalized-direction difference is at most 2‖z−w‖/‖z‖. [`unit_sub_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeBounds.lean#L217).

**Theorem · An inverse factor raises decay order.** For a positive base, multiplying a negative real power by its inverse raises the decay exponent by 1. [`rpow_step`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeBounds.lean#L238).

**Theorem · Compare decay at comparable radii.** For nonnegative decay exponent, radius at least half the reference radius gives the factor 2ᵇ in the inverse-power comparison. [`rpow_half`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeBounds.lean#L242).

**Theorem · Radial derivative bounds lift to space.** A radial function with C² regularity and three power-decay bounds gives corresponding spatial ball-data bounds beyond a sufficiently large radius. [`radial_ball`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeBounds.lean#L250).

**Theorem · Radial-angular sums give far decay.** A finite sum of decaying radial weights times regular degree-zero angular fields has the far bounds for its value, derivative and local derivative slope. [`far_of_split`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeBounds.lean#L340).

**Theorem · Decay at the assigned field order.** A valid mode of order e has value decay e+ε, derivative decay e+ε+1 and local derivative Lipschitz decay e+ε+2. [`modeFieldOf_far_bounds_order`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeBounds.lean#L410).

**Theorem · Weaken an inverse-power decay estimate.** At radius at least 1, reducing a decay exponent preserves the upper bound after taking the absolute coefficient. [`rpow_weaken`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeBounds.lean#L423).

**Theorem · Cubic-order modes have three far bounds.** A valid mode of order 3 has far decay bounds of orders 3, 4 and 5 for value, derivative and local derivative Lipschitz constant. [`modeFieldOf_far_bounds_three`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeBounds.lean#L427).

**Theorem · First-order modes have fractional decay.** A valid mode of order 1 has far decay bounds of orders 1+ε, 2+ε and 3+ε for value, derivative and local derivative Lipschitz constant. [`modeFieldOf_far_bounds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeBounds.lean#L443).

### Breakdown.FracCell.GivenProfileFarModeSplit

This module extracts a finite radial-angular expansion beyond the final spline break using polynomial interpolation, then estimates each radial weight and regular angular factor. **Reading context:** Appendix B: the represented profile and its regularity, decay and parameter dependence, supplying the data conditions in B.14.

**Definition · The positive chart denominator.** The chart denominator is L₀²t²+r_c²(1−t)². [`chartQ`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L14).

**Definition · Logarithmic phase as a radius function.** The radial logarithmic phase is one half of log(1+r²/r_c²). [`phaseR`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L16).

**Definition · Complex mode value at a chosen radius.** The complex auxiliary mode formula uses a supplied radial value and the point's angular coordinates and reduced frame vectors. [`innerAt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L18).

**Definition · Rotate the horizontal vector coordinates.** The auxiliary rotation map applies the sine-cosine rotation to the first two coordinates and retains height. [`turnVec`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L25).

**Definition · A radial interpolation weight.** The complex radial weight combines the decay factor, endpoint power, chart-denominator quotient, interpolation polynomial and logarithmic phase. [`radialWeight`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L28).

**Theorem · A mode is the real complex formula.** A mode field is reconstructed from the real parts of its complex auxiliary values at the point's actual norm. [`modeFieldOf_eq_innerAt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L32).

**Theorem · The chart denominator is positive.** Valid chart parameters make the quadratic chart denominator positive for every real t. [`chartQ_pos`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L35).

**Predicate · Polynomial dependence near infinity.** The local-polynomial predicate gives a polynomial of degree at most N in t on (t_L,1) for each fixed height coordinate. [`LocPoly`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L47).

**Theorem · Restrict a tail and enlarge its degree.** Local polynomial dependence survives raising the lower endpoint and enlarging the degree bound. [`LocPoly.mono`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L50).

**Theorem · Add local polynomial degree bounds.** Adding locally polynomial functions gives a degree bound equal to the maximum of their two bounds. [`LocPoly.add`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L56).

**Theorem · Multiply local polynomial degree bounds.** Multiplying locally polynomial functions gives a degree bound equal to the sum of their two bounds. [`LocPoly.mul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L65).

**Theorem · Height-only functions have degree zero.** A function independent of t has local polynomial degree at most zero in t. [`LocPoly.const`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L74).

**Theorem · A fixed polynomial is locally polynomial.** A function given by evaluation of a fixed polynomial satisfies the local-polynomial predicate with its natural degree. [`LocPoly.ofPoly`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L78).

**Theorem · A tail polynomial is valid locally.** At an interior point of the tail interval, a locally polynomial function agrees in a neighborhood with a polynomial of its degree. [`LocPoly.eventually`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L83).

**Theorem · Tail polynomials are differentiable.** A locally polynomial function has its ordinary t-derivative at every interior point of its tail interval. [`LocPoly.hasDerivAt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L90).

**Theorem · Chart derivative keeps the degree bound.** Differentiating a locally polynomial function in t preserves its available local polynomial degree bound. [`LocPoly.tderiv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L98).

**Theorem · Height derivative keeps the degree bound.** When height derivatives exist throughout a nonempty tail interval, height differentiation preserves the local t-polynomial degree bound. [`LocPoly.xderiv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L109).

**Predicate · Polynomial dependence on a tail.** The weaker local-polynomial predicate records existence of a finite t-degree bound on the tail interval. [`LP`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L166).

**Theorem · Add functions polynomial on the tail.** The sum of two functions polynomial in t on a common tail interval is polynomial there with some finite degree bound. [`LP.add`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L168).

**Theorem · Multiply tail-polynomial functions.** The product of two functions polynomial in t on a common tail interval is polynomial there with some finite degree bound. [`LP.mul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L174).

**Theorem · Height functions are tail polynomials.** A function independent of t has some finite polynomial degree bound on every tail interval. [`LP.const`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L180).

**Theorem · Constants are tail polynomials.** A constant complex function is polynomial in the tail coordinate. [`LP.cst`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L182).

**Theorem · Negation preserves tail polynomial form.** Negating a function polynomial on the tail preserves that property. [`LP.neg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L184).

**Theorem · Subtract tail-polynomial functions.** Subtracting two functions polynomial on a common tail interval preserves the property. [`LP.sub`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L188).

**Theorem · The tail coordinate is polynomial.** The complex-valued coordinate t is polynomial on the tail interval. [`LP.tvar`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L193).

**Theorem · Tail-coordinate powers are polynomial.** Every natural-number power of the complex tail coordinate is polynomial there. [`LP.tpow`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L196).

**Theorem · Chart derivatives preserve tail form.** Differentiating in t preserves the existence of a finite local polynomial degree bound. [`LP.tderiv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L199).

**Theorem · Height derivatives preserve tail form.** Under the height differentiability and nonempty interval assumptions, height differentiation preserves polynomial dependence on t in the tail. [`LP.xderiv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L204).

**Theorem · Chart denominator is a tail polynomial.** The quadratic chart denominator is polynomial in the tail coordinate. [`LP.quadQ`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L210).

**Theorem · All interior breaks lie before one point.** For any finite list of breaks, a point t_L in [0,1) bounds every listed break smaller than 1 from above. [`tail_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L215).

**Theorem · The selected cell is fixed in the tail.** If all breaks below 1 lie at or below t_L, all points in (t_L,1) select the same cell index. [`cellIndex_tail`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L232).

**Theorem · The selected index fits the break list.** The selected cell index is at most the number of listed breaks. [`cellIndex_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L244).

**Definition · Freeze height in a bivariate polynomial.** The auxiliary univariate polynomial fixes the second complex coordinate and retains the first-coordinate powers. [`tPoly`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L250).

**Theorem · Evaluation after freezing a coordinate.** Evaluating the auxiliary univariate polynomial equals evaluating the original bivariate polynomial with its second coordinate fixed. [`tPoly_eval`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L253).

**Theorem · Degree after freezing a coordinate.** The degree of the frozen-height polynomial is at most the largest first-coordinate exponent in the original support. [`tPoly_natDegree`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L261).

**Theorem · Splines are polynomial past their breaks.** Every parity-adjusted spline is polynomial in t on some interval (t_L,1), with one finite degree bound across heights. [`spline_locPoly`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L266).

**Theorem · Height derivatives of regular splines.** With both spline regularity orders at least 1, every height slice is differentiable. [`spline_diffX`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L283).

**Theorem · Derivative of an endpoint power.** The derivative of (1−t)ᵉ is −e(1−t)ᵉ⁻¹, including the natural-number zero-exponent case. [`pow_deriv_one`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L289).

**Theorem · Factor endpoint powers through twisting.** For a tail-polynomial amplitude, multiplying its twisted derivative by the chart denominator exposes the common endpoint power. [`twisted_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L298).

**Definition · Weighted nonzero-mode amplitude.** The auxiliary wave amplitude multiplies its spline by the prescribed low-order t power and axis weight. [`waveV`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L325).

**Definition · A wave amplitude with an axis factor.** The second auxiliary wave amplitude adds a factor 1−x² to the weighted wave amplitude. [`waveW`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L328).

**Definition · A mean amplitude with a radial factor.** The auxiliary mean amplitude multiplies its spline by the chart coordinate t. [`meanV`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L331).

**Definition · A mean stream amplitude with axis weight.** The auxiliary mean stream amplitude multiplies the odd spline by 1−x². [`meanW`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L333).

**Theorem · The axis weight is differentiable.** The complex-valued function 1−x² is differentiable at every real x. [`sq_diff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L335).

**Theorem · Nonzero modes have a polynomial tail.** For a nonzero mode with the polar-spline class, the denominator times each reduced component factors into its high-order endpoint weight and a tail-polynomial function. [`far_wave`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L338).

**Theorem · The zero mode has a polynomial tail.** With the stream-spline class, the denominator times each zero-mode reduced component factors into its high-order endpoint weight and a tail-polynomial function. [`far_mean`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L427).

**Theorem · Real parts of complex tail polynomials.** A locally polynomial complex function at a fixed height is the sum of a real polynomial and i times another of the degree bounds. [`split_parts`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L497).

**Theorem · Real polynomial tails of reduced fields.** Valid field data give a common tail interval and finite degree bound for the real and imaginary polynomial factors of every reduced component. [`reducedField_far_poly`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L519).

**Theorem · Lagrange reconstruction of a polynomial.** A real polynomial of degree less than K is its Lagrange interpolation sum on K distinct sample points. [`interp_real`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L542).

**Theorem · Interpolate the reduced field's tail.** Every listed reduced mode can be reconstructed beyond the final break from finitely many sampled radii with the polynomial radial weights. [`reducedField_far_interp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L549).

**Theorem · Norm under positive scalar dilation.** A positive dilation multiplies the vector norm by the same factor. [`norm_smul_pos`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L605).

**Theorem · Height ratio is dilation invariant.** Positive dilation leaves the normalized height coordinate unchanged. [`height_smul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L608).

**Theorem · The radial frame is dilation invariant.** Positive dilation leaves every reduced radial-frame component unchanged. [`radial_smul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L616).

**Theorem · The polar frame is dilation invariant.** Positive dilation leaves every reduced polar-frame component unchanged. [`polar_smul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L624).

**Theorem · Azimuthal frame is dilation invariant.** Positive dilation leaves every reduced azimuthal-frame component unchanged. [`azim_smul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L632).

**Theorem · Positive dilation preserves angle.** Positive scalar dilation leaves the angular coordinate unchanged. [`angle_smul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L640).

**Theorem · Fixed-radius mode values ignore dilation.** At a fixed supplied radius, the auxiliary complex mode value is unchanged by positive dilation of its directional input. [`innerAt_smul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L646).

**Theorem · Normalization cancels positive dilation.** Normalizing a positively dilated point to radius R gives the same vector as normalizing the original point. [`scale_dir`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L651).

**Theorem · Normalization gives the chosen radius.** For R>0 and a nonzero point, scaling its direction to radius R gives a vector of norm R. [`norm_dir`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L659).

**Theorem · An exponential splits over a phase sum.** The complex exponential of i times a sum of real phases is the product of their separate phase exponentials. [`exp_split`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L663).

**Theorem · Valid mode fields are differentiable.** Each listed mode of valid field data is differentiable at every spatial point. [`modeField_diff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L671).

**Theorem · Mode derivatives are locally Lipschitz.** The spatial derivative of each listed valid mode field is locally Lipschitz. [`modeField_slope`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L691).

**Theorem · Reconstruct paired coefficient sums.** Componentwise sums of paired real multiples reconstruct as the corresponding sums of scalar multiples of vectors. [`ofComponents_pair`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L699).

**Theorem · Coordinates of the auxiliary rotation.** The auxiliary rotation has the usual sine-cosine horizontal coordinates and unchanged height. [`turn_apply`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L705).

**Theorem · The auxiliary rotation preserves norm.** The auxiliary horizontal rotation preserves spatial norm. [`turn_norm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L710).

**Theorem · Rotation preserves normalized height.** The auxiliary rotation leaves the normalized height coordinate unchanged. [`height_turn`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L718).

**Theorem · Reduced frames rotate with the point.** Rotating a point rotates the horizontal components of all three reduced frames and preserves their vertical components. [`frame_turn`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L722).

**Theorem · Integer argument phases are unit powers.** For nonzero complex w, the exponential of i times an integer multiple of its argument equals the corresponding integer power of w/‖w‖. [`exp_arg_pow`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L738).

**Theorem · Factor angular phases under rotation.** Off the axis, an integer angular phase after rotation is the product of the rotation phase and the original angular phase. [`angle_turn`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L750).

**Theorem · Rotation of a single mode field.** For a valid listed mode at a nonzero point, rotating its input multiplies the internal complex mode by the mode rotation phase and rotates the reconstructed output. [`turn_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L774).

**Theorem · Opposite rotations cancel.** Applying a rotation and then its negative-angle rotation returns the original vector. [`turn_turn`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L820).

**Definition · Rotation as a real linear map.** The auxiliary horizontal rotation is packaged as a real linear map. [`turnLin`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L826).

**Definition · Rotation as a continuous linear map.** The auxiliary rotation linear map is packaged as a continuous linear map. [`turnCLM`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L835).

**Theorem · Evaluate the continuous rotation map.** The continuous linear rotation map acts by the auxiliary spatial rotation. [`turnCLM_apply`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L837).

**Theorem · Compose locally Lipschitz operators.** Locally Lipschitz operator fields near a point have a locally Lipschitz pointwise composition near that point. [`slopeAt_comp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L839).

**Theorem · Constant fields are locally Lipschitz.** A constant operator field has a Lipschitz bound on a neighborhood of every point. [`slopeAt_const`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L883).

**Theorem · Direction normalization is smooth.** Scaling a point to a fixed radius along its direction is infinitely differentiable at every nonzero point. [`dir_smooth`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L887).

**Theorem · Restrict angular derivatives.** A differentiable field with locally Lipschitz derivative, composed with direction normalization and fixed linear maps, is differentiable off zero with locally Lipschitz derivative there. [`angular_regular`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L890).

**Theorem · Real part of an amplitude and phase.** The real part of a complex amplitude times a real factor and phase equals the factor times its cosine-sine real-imaginary combination. [`re_form`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L926).

**Theorem · Multiply two absolute-value bounds.** Two absolute-value bounds multiply to an absolute-value bound for the product. [`abs_mul2_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L933).

**Theorem · Multiply three absolute-value bounds.** Three absolute-value bounds multiply to an absolute-value bound for the triple product. [`abs_mul3_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L937).

**Theorem · Endpoint powers give radial decay.** For L>0, r>1, γ≤β, β≥0 and j≥0, a positive s≤L/r satisfies s^(β+j)≤L^(β+j)r^(−γ−j). [`pow_to_r`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L941).

**Theorem · Compactified distance versus 1/r.** For L>0 and r>1, the complementary compactified radius is L/(r+L), lies strictly between zero and one, and is comparable to 1/r with explicit constants depending on L. [`sigma_facts`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L950).

**Theorem · Derivative of compactified distance.** For positive L and r, the derivative of 1−r/(r+L) is minus its square divided by L. [`sigma_deriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L961).

**Theorem · Second slope of compactified distance.** The derivative of the first compactified-distance derivative is twice its cube divided by L². [`sigma1_deriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L971).

**Theorem · First radial slope of logarithmic phase.** For valid chart parameters, the radial logarithmic phase has derivative r/(r_c²+r²). [`phase_deriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L979).

**Theorem · Second radial slope of log phase.** The derivative of r/(r_c²+r²) is (r_c²−r²)/(r_c²+r²)². [`phase1_deriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L990).

**Definition · Divide by the chart quadratic.** The auxiliary quotient evaluates the polynomial at 1−s and divides by the chart denominator at 1−s. [`quotQ`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L1002).

**Theorem · The chart quotient is smooth.** For valid chart parameters, the polynomial divided by the positive chart denominator is infinitely differentiable. [`quotQ_smooth`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L1004).

**Definition · Distance from the compactified endpoint.** The endpoint distance is 1−r/(r+L₀). [`sg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L1013).

**Definition · The nonoscillatory radial factor.** The nonoscillatory factor is s to the power 2ε+e times the polynomial chart quotient. [`gF`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L1015).

**Definition · First derivative of the radial factor.** The first radial-factor derivative formula combines the differentiated power and the derivative of the chart quotient. [`gF1`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L1018).

**Definition · Second derivative of the radial factor.** The second radial-factor derivative formula expands the power, cross and quotient-second-derivative terms. [`gF2`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L1021).

**Theorem · The chart quotient has two derivatives.** The smooth chart quotient and its first derivative have their ordinary derivatives everywhere. [`quotQ_hasDeriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L1027).

**Theorem · Radial-factor derivative formulas.** At positive s, the nonoscillatory radial factor and its first derivative have the two explicitly defined derivative formulas. [`gF_hasDeriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L1034).

**Definition · The real oscillatory radial factor.** The real oscillatory factor is the real part of a complex amplitude multiplied by the logarithmic radial phase. [`hF`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L1042).

**Definition · First slope of the oscillatory factor.** The first oscillatory-factor derivative combines the sine-cosine derivative with κ times the radial phase derivative. [`hF1`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L1045).

**Definition · Second slope of the oscillatory factor.** The second oscillatory-factor derivative contains the squared phase-derivative term and the phase-second-derivative term. [`hF2`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L1048).

**Theorem · Oscillatory derivative formulas.** The oscillatory radial factor and its first derivative have the two explicitly defined derivative formulas. [`hF_hasDeriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L1053).

**Theorem · Oscillatory factor and derivative bounds.** At positive radius, the oscillatory factor is bounded and its first two derivatives have the inverse-radius and inverse-square bounds. [`hF_bounds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L1075).

**Theorem · Bounds on the nonoscillatory derivatives.** On 0< s≤1, the nonoscillatory factor and its first two derivatives have the common power bound with zero, one and two divisions by s. [`gF_bounds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L1127).

**Theorem · Combine a coefficient and a decay bound.** The nonnegative-factor inequalities combine to give the final bound |v|≤Cρ. [`fin_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L1206).

**Theorem · Multiply absolute-value inequalities.** The product of two quantities is bounded in absolute value by the product of their supplied bounds. [`abs_mul_le_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L1213).

**Theorem · Decay of radial interpolation weights.** Each real radial interpolation weight is C² beyond radius 1 and has decay orders e+ε, e+ε+1 and e+ε+2 through two derivatives. [`radialWeight_bounds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L1215).

**Theorem · Separate radial and angular factors.** Every listed valid mode has a finite far-field expansion into decaying C² radial factors and dilation-invariant angular fields differentiable off zero with locally Lipschitz derivatives. [`modeFieldOf_radial_split`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileFarModeSplit.lean#L1384).

### Breakdown.FracCell.GivenProfilePower

This module uses linearity and field-level existence to identify the supplied fractional-power field for every profile parameter. **Reading context:** Appendix B: the represented profile and its regularity, decay and parameter dependence, supplying the data conditions in B.14.

**Theorem · Zero has zero weak fractional power.** The zero field is a weak fractional power of the zero field for every real exponent. [`power_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePower.lean#L19).

**Theorem · Weak fractional powers add.** For 1<α<3/2, weak fractional powers of two L⁶ fields add to a weak fractional power of their sum. [`power_add`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePower.lean#L22).

**Theorem · Finite linear sums have weak powers.** For 1<α<3/2, a finite real linear combination of L⁶ fields with weak fractional powers remains in L⁶ and has a weak fractional power. [`power_sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePower.lean#L30).

**Theorem · A reconstructed field has a weak power.** Valid chart and field data with high radial order one give a weak fractional power of the reconstructed field at exponent 1+ε. [`fieldOf_power_exists`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePower.lean#L46).

**Theorem · The assigned profile power is valid.** For a valid profile instance and the matching exponent, every profile in the parameter box has its assigned field as a weak fractional power. [`profile_power_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePower.lean#L63).

### Breakdown.FracCell.GivenProfilePowerField

This module establishes L⁶ integrability of reconstructed fields and converts weighted second-derivative translation control into an L² translation modulus. **Reading context:** Appendix B: the represented profile and its regularity, decay and parameter dependence, supplying the data conditions in B.14.

**Theorem · A radial decay criterion for Lᵖ.** For finite nonzero q, the weight (1+‖y‖)⁻ᵃ belongs to Lᑫ when aq>3. [`memLp_decay`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerField.lean#L16).

**Theorem · Inverse-distance decay gives L⁶.** A continuous field with inverse-distance decay belongs to L⁶ in three-dimensional space. [`memLp_six_of_decay`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerField.lean#L27).

**Theorem · Cubic weights under a small shift.** A shift of norm at most 1 increases the cubic decay weight by at most a factor of 8. [`weight_shift_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerField.lean#L34).

**Theorem · Weighted control gives an L² modulus.** A measurable second-derivative field with cubic decay and weighted linear translation control belongs to L² and has squared L² translation difference bounded by a constant times shift length. [`secondModulus_of_parts`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerField.lean#L49).

**Theorem · A coordinate is bounded by the norm.** The absolute value of each Cartesian coordinate is at most the spatial norm. [`coord_abs_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerField.lean#L98).

**Theorem · Normalized coordinates are bounded.** Each Cartesian coordinate divided by the norm has absolute value at most 1. [`div_norm_abs_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerField.lean#L101).

**Theorem · Normalized height lies between −1 and 1.** The absolute normalized height coordinate is at most 1. [`heightRatio_abs_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerField.lean#L105).

**Theorem · Polar-frame components are bounded.** Every reduced polar-frame component has absolute value at most 1. [`polarVecQ_abs_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerField.lean#L107).

**Theorem · Azimuthal-frame components are bounded.** Every reduced azimuthal-frame component has absolute value at most 1. [`azimVecQ_abs_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerField.lean#L124).

**Theorem · Bound a vector by absolute components.** The norm of a reconstructed vector is at most the sum of its three absolute components. [`ofComponents_norm_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerField.lean#L136).

**Theorem · Bound a three-component mode term.** A unit complex phase times three bounded components with frame factors of size at most 1 has norm at most three times the common component bound. [`modeTerm_norm_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerField.lean#L141).

**Theorem · The chart radius is nonnegative.** For valid chart parameters, the compactified radius is nonnegative everywhere. [`chartT_nonneg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerField.lean#L153).

**Theorem · The chart radius is below one.** For valid chart parameters, the compactified radius is strictly less than 1 everywhere. [`chartT_lt_one`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerField.lean#L156).

**Theorem · Endpoint distance gives physical decay.** One minus the chart radius is bounded by (L₀+1)/(1+‖y‖). [`one_sub_chartT_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerField.lean#L159).

**Theorem · Reduced endpoint decay gives field decay.** A common linear endpoint bound for all reduced components gives inverse-distance decay of the reconstructed spatial field. [`fieldOf_norm_le_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerField.lean#L170).

**Theorem · Cell selection stays in the mesh range.** The selected cell index is at most the number of mesh breaks. [`cellIndex_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerField.lean#L212).

**Theorem · Polynomial bounds on the unit square.** A complex bivariate polynomial has a finite uniform bound on the real unit square. [`polyEval_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerField.lean#L218).

**Theorem · The parity sign has norm at most one.** The complex sign used by odd spline reflection has norm at most 1. [`sign_norm_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerField.lean#L226).

**Theorem · Splines are bounded on the chart box.** A spline is uniformly bounded for 0≤t≤1 and |x|≤1. [`spline_eval_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerField.lean#L229).

**Theorem · Polynomial evaluation preserves C¹.** Substituting two C¹ real functions into a complex bivariate polynomial gives a C¹ function. [`polyEval_contDiff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerField.lean#L251).

**Theorem · Directional derivative bounds on a box.** The derivative of a C¹ function in a fixed direction has a finite bound on every closed coordinate rectangle. [`partial_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerField.lean#L264).

**Theorem · Derivative along the first coordinate.** A C¹ planar function restricted to its first coordinate has derivative given by the Fréchet derivative on (1,0). [`deriv_first_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerField.lean#L271).

**Theorem · Bound weighted radial derivatives.** A C¹ scalar weight times a polynomial has a uniformly bounded first-coordinate derivative on the unit square. [`tweight_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerField.lean#L277).

**Theorem · Lower breaks are fixed to the right.** For a finite break list, points sufficiently close to the right of u have the same breaks at or below them as u. [`filter_le_eventually`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerField.lean#L288).

**Theorem · Cell index is locally fixed on the right.** For a finite break list, the selected index is constant on some right neighborhood including the current point. [`cellIndex_eventually`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerField.lean#L304).

**Theorem · Right-side formula bounds the derivative.** If a function agrees just to the right with a differentiable formula, its total derivative norm at the endpoint is bounded by the formula's derivative norm. [`norm_deriv_le_of_eqOn_Ici`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerField.lean#L309).

**Theorem · Bound weighted radial spline slopes.** Multiplying a spline by a C¹ chart-coordinate weight gives a uniformly bounded total chart derivative on the closed chart box. [`spline_tderiv_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerField.lean#L321).

**Theorem · Left-side formula bounds the derivative.** If a function agrees just to the left with a differentiable formula, its total derivative norm at the endpoint is bounded by the formula's derivative norm. [`norm_deriv_le_of_eqOn_Iic`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerField.lean#L351).

**Theorem · Derivative along the second coordinate.** A C¹ planar function restricted to its second coordinate has derivative given by the Fréchet derivative on (0,1). [`deriv_second_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerField.lean#L363).

**Theorem · Bound weighted height derivatives.** A C¹ height weight multiplied by a polynomial with scaled height argument is height-differentiable with uniformly bounded derivative on 0≤t≤1 and |x|≤1. [`xweight_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerField.lean#L369).

**Theorem · Bound weighted height spline slopes.** Multiplying a spline by a C¹ height weight gives a uniformly bounded total height derivative on the closed chart box. [`spline_xderiv_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerField.lean#L383).

**Theorem · Bound polynomial weights by powers.** For nonzero high order and 0≤t≤1, the polynomial weight has norm at most 1−t. [`weightPoly_norm_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerField.lean#L444).

**Theorem · The core ratio has size at most one.** The chart core ratio has absolute value at most 1. [`coreRatioT_abs_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerField.lean#L453).

**Theorem · Axis powers have norm at most one.** When |x|≤1, every natural power of the axis factor 1−x² has norm at most 1. [`axisFactor_norm_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerField.lean#L460).

**Theorem · Bound the twisted derivative.** For valid chart parameters and 0≤t<1, a radial slice derivative bound B gives the twisted-derivative bound (1−t)B+(|n||β|+1)‖f(t,x)‖. [`twistedScale_norm_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerField.lean#L465).

**Theorem · Bound a sum with one subtraction.** The norm of a+b−c is at most the sum of the three norms. [`norm_add_sub_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerField.lean#L492).

**Theorem · Linear vanishing of a reduced mode.** With nonzero high order, each reduced mode component has a bound proportional to 1−t throughout the chart box. [`reducedField_mode_norm_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerField.lean#L497).

**Theorem · A common endpoint bound for all modes.** With nonzero high order, the finitely many listed modes share one linear endpoint bound on the chart box. [`reducedField_norm_le_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerField.lean#L639).

**Theorem · The reconstructed field is C¹.** Valid chart and field data with high radial order one give a continuously differentiable reconstructed field. [`fieldOf_contDiff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerField.lean#L648).

**Theorem · The reconstructed field belongs to L⁶.** A field reconstructed from valid data with high radial order one belongs to L⁶. [`fieldOf_memLp_six`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerField.lean#L652).

**Theorem · L² Hessian with translation control.** A field reconstructed from valid data with high radial order one has an L² weak second derivative whose squared L² translation difference is bounded by a constant times the shift length for shifts of norm at most 1. [`fieldOf_second_modulus`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerField.lean#L658).

### Breakdown.FracCell.GivenProfilePowerFieldJumps

This module combines boundedness with a small exceptional-set cover to control translation differences of the second derivative in a cubic weighted integral. **Reading context:** Appendix B: the represented profile and its regularity, decay and parameter dependence, supplying the data conditions in B.14.

**Theorem · A negative cubic power is reciprocal.** For a positive real number, its real power −3 equals the inverse of its ordinary cube. [`rpow_neg_three_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumps.lean#L19).

**Theorem · The cubic decay weight is nonnegative.** The weight (1+‖y‖)⁻³ is nonnegative everywhere. [`weight_nonneg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumps.lean#L22).

**Theorem · The cubic decay weight is at most one.** The weight (1+‖y‖)⁻³ is at most 1 everywhere. [`weight_le_one`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumps.lean#L25).

**Theorem · Total second derivative decays cubically.** Valid field data with high radial order one give a global cubic decay bound for the total second Fréchet derivative of the reconstructed field. [`second_decay`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumps.lean#L29).

**Theorem · Jump covers control translations.** A bounded field with the small weighted exceptional sets and integrable difference bounds has a weighted translation modulus linear in shift length. [`modulus_of_cover`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumps.lean#L77).

**Theorem · Weighted translation bounds for Hessians.** For valid field data with high radial order one, the total second derivative has a cubic-weighted translation difference bounded by a constant times the shift length for shifts of norm at most 1. [`fieldOf_second_weighted_modulus`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumps.lean#L117).

### Breakdown.FracCell.GivenProfilePowerFieldJumpsCover

This module bounds weighted neighborhoods of spherical and conical spline interfaces, separating translations crossing them from segments controlled by third derivatives. **Reading context:** Appendix B: the represented profile and its regularity, decay and parameter dependence, supplying the data conditions in B.14.

**Theorem · The spatial dimension is three.** The real dimension of the spatial vector space is 3. [`dim_space`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsCover.lean#L17).

**Theorem · Integrability of the cubic radial weight.** The product of the cubic decay weight and inverse radius is integrable over space. [`weight_inv_norm_integrable`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsCover.lean#L19).

**Theorem · Absorb a quadratic factor in the weight.** For a nonnegative real y, y²(1+y)⁻³ is at most 1. [`sq_mul_weight_le_one`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsCover.lean#L46).

**Theorem · Shell weight controlled by thickness.** The cubic weight is integrable on every closed shell with nonnegative ordered radii, and its integral is bounded by a constant times the shell thickness. [`weight_shell`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsCover.lean#L52).

**Definition · Insert a height into planar coordinates.** The plane lift inserts a real height as the third Cartesian coordinate of a planar point. [`planeLift`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsCover.lean#L126).

**Theorem · Height of a lifted planar point.** The third coordinate of a plane lift is its supplied height. [`planeLift_two`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsCover.lean#L129).

**Theorem · Other coordinates of a plane lift.** The two remaining coordinates of a plane lift equal the supplied planar coordinates. [`planeLift_succAbove`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsCover.lean#L133).

**Theorem · Lifting bounds the planar norm below.** The planar point's norm is at most the norm of its lift at any height. [`norm_le_lift`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsCover.lean#L138).

**Theorem · Lift-height changes are vertical.** Two lifts of the same planar point differ by the vertical coordinate vector of their height difference. [`planeLift_sub`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsCover.lean#L143).

**Theorem · Lift norms vary at most with height.** The difference between the norms of two lifts is bounded by the absolute difference of their heights. [`planeLift_norm_slope`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsCover.lean#L153).

**Theorem · Conical band has controlled slice width.** For |c|<1, two heights in the same conical band of thickness δ differ by at most 2δ/(1−|c|). [`band_slice`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsCover.lean#L157).

**Theorem · Conical weight scales with thickness.** For |c|<1, the cubic weight on the band |y₂−c‖y‖|≤δ is integrable and its integral is bounded by a constant times δ. [`weight_band`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsCover.lean#L179).

**Theorem · Third derivatives control a safe segment.** A segment avoiding the listed spherical and conical interfaces and staying at radius at least half its starting norm has second-derivative difference bounded by 2K‖h‖/‖y‖. [`second_segment_of_third`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsCover.lean#L264).

**Theorem · The cubic spatial weight is nonnegative.** The cubic decay weight is nonnegative at every spatial point. [`weight_nonneg'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsCover.lean#L312).

**Theorem · Weighted bounds add over a union.** For two measurable sets with integrable cubic weight, their union has integrable weight and its integral is at most the sum of the two integrals. [`union_two`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsCover.lean#L315).

**Theorem · Weighted bounds add over finite unions.** A finite union of measurable sets with integrable cubic weight is measurable and has weight integral at most the sum of the individual integrals. [`union_finset`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsCover.lean#L329).

**Theorem · A small cover isolates derivative jumps.** With valid chart and field data of high radial order one, every small shift of a valid field admits a measurable exceptional set of weighted size O(‖h‖) and an integrable control function bounding second-derivative differences off that set. [`fieldOf_second_jump_cover`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsCover.lean#L348).

### Breakdown.FracCell.GivenProfilePowerFieldJumpsPieces

This module describes the finite spherical and conical interfaces where spline formulas can change, freezes the polynomial pieces away from them, and bounds third derivatives by a constant divided by distance to the origin. Weighted derivative estimates treat the mean mode and the nonzero modes separately. **Reading context:** Appendix B: the represented profile and its regularity, decay and parameter dependence, supplying the data conditions in B.14.

**Definition · Contribution of one physical mode.** A mode contribution is the real vector obtained by multiplying its reduced radial, polar and azimuthal components by the frame, mode phase and decay factor. [`modeTerm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L16).

**Theorem · Cell selection is locally constant.** If a coordinate avoids the interior entries of a break list, its selected cell index is constant in a neighborhood. [`cellIndex_eventuallyEq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L22).

**Theorem · Freeze a half-spline polynomial.** When both coordinates avoid the interior breaks, half-spline evaluation agrees locally with its selected polynomial piece. [`evalHalf_eventuallyEq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L39).

**Theorem · Avoid a compactified-radius break.** For valid parameters and a nonzero point, avoiding the radius L₀b/(1−b) ensures that the compactified radius differs from b. [`chartT_ne_of_radius`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L50).

**Theorem · Interior breaks lie between zero and one.** For a strictly increasing break list with endpoints zero and one, every interior break lies strictly between those endpoints. [`interior_bounds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L64).

**Theorem · Freeze a parity-reflected spline.** Away from height zero and the interior radial and absolute-height breaks, spline evaluation locally equals the selected polynomial with the appropriate reflection and parity sign. [`eval_eventuallyEq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L86).

**Theorem · Avoid an absolute-height break.** At a nonzero point, avoiding the two cones y₂=±b‖y‖ ensures that the absolute normalized height differs from b. [`heightRatio_abs_ne`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L111).

**Theorem · Avoid a normalized-height break.** At a nonzero point, avoiding the cone y₂=c‖y‖ ensures that the normalized height differs from c. [`heightRatio_ne_of_cone`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L120).

**Theorem · The mean mode has unit phase.** The phase factor for mode zero is identically one. [`modePhase_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L127).

**Theorem · Phase through a normalized complex pair.** Away from the horizontal axis, the mode phase is the integer power of the normalized horizontal complex coordinate multiplied by the logarithmic radial phase. [`modePhase_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L130).

**Definition · The four splines belonging to a mode.** The spline list for a mode contains its radial, polar, stream and swirl splines. [`splinesOf`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L147).

**Definition · Spherical spline interfaces.** The break radii collect the compactified-radius break values from all mode splines after applying b↦L₀b/(1−b). [`breakRadii`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L150).

**Definition · Conical spline interfaces.** The break-cone slopes consist of zero and both signs of every height break whose absolute value is less than one. [`breakCones`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L154).

**Theorem · All interface cones are nondegenerate.** Every slope in the finite break-cone set has absolute value less than one. [`breakCones_abs_lt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L159).

**Theorem · Interface avoidance fixes chart cells.** For valid chart parameters, a nonzero point avoiding all break spheres and cones avoids the interior radial breaks and height zero for every listed spline, and on tensor meshes also avoids the interior absolute-height breaks. [`good_point`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L168).

**Predicate · Weighted derivatives through order three.** The weighted derivative predicate requires three continuous derivatives on the domain and bounds the jth derivative by a common constant times the radial weight divided by ‖y‖ʲ for j≤3. [`SymbolW`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L192).

**Theorem · Multiply weighted derivative bounds.** On an open domain, the product of two functions with weighted derivative bounds has the product weight when both original weights are nonnegative. [`SymbolW.mul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L196).

**Theorem · A quadratic weight gives a third bound.** A weighted derivative estimate with weight at most c r² yields a bound K/r for the third derivative at every nonzero point of the domain. [`SymbolW.third_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L239).

**Definition · Insert a complex real part in one slot.** The component map sends a complex number to its real part times one Cartesian basis vector. [`compMap`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L250).

**Lemma · Component insertion has norm at most one.** The operator norm of each map that inserts a complex real part into a Cartesian coordinate is at most one. [`compMap_norm_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L253).

**Lemma · Reconstruction is a sum of linear maps.** Reconstructing a real vector from complex component real parts equals the sum of the three component insertion maps. [`ofComponents_re_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L259).

**Theorem · Combine component derivative bounds.** If all three complex components are C³ at a point and their third derivatives have norm at most K, the reconstructed real vector is C³ there and its third derivative has norm at most 3K. [`components_third`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L266).

**Lemma · Scale derivatives of degree-zero maps.** For a function invariant under positive dilation, the jth Fréchet derivative at y equals cʲ times the derivative at cy for c>0. [`iteratedFDeriv_scale_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L289).

**Theorem · Derivative bounds from degree zero.** A degree-zero homogeneous function that is C³ away from the origin has derivatives of orders zero through three bounded by C/‖y‖ʲ. [`homogeneous_zero_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L310).

**Theorem · Restrict a weighted derivative estimate.** A weighted derivative estimate remains valid after restricting its domain. [`SymbolW.mono`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L349).

**Theorem · Add functions with one derivative weight.** On an open domain, adding two functions with the same weighted derivative bound preserves that weight. [`SymbolW.add`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L354).

**Theorem · Enlarge the permitted radial weight.** A weighted derivative estimate remains valid with a new weight whenever the old weight is bounded by a nonnegative constant times the new one on the domain. [`SymbolW.weight_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L370).

**Theorem · Constants have unit derivative weight.** Every constant complex function satisfies the weighted derivative estimate with constant radial weight one. [`SymbolW.const`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L380).

**Theorem · Degree zero gives unit weight.** A C³ degree-zero homogeneous function satisfies the unit-weight derivative estimate on any domain avoiding the origin. [`SymbolW.of_homogeneous`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L388).

**Lemma · Differentiate composition with dilation.** For c>0, the jth derivative of u↦F(cu) is cʲ times the jth derivative of F at cu. [`scale_comp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L396).

**Lemma · Bound norm derivatives on the sphere.** There is a constant B≥1 bounding the first three derivatives of the norm on the unit sphere by Bʲ. [`norm_derivs_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L417).

**Theorem · Lift radial derivative estimates.** A radial function whose first three derivatives obey weighted inverse-power bounds on positive radii gives a spatial function h(‖y‖) with the corresponding weighted derivative estimate away from the origin. [`SymbolW.of_radial`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L445).

**Theorem · Real degree zero gives complex bounds.** Complexifying a real C³ degree-zero homogeneous function gives the unit-weight derivative estimate away from the origin. [`SymbolW.of_homogeneous_real`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L506).

**Lemma · Normalized coordinates are C³ off zero.** Each coordinate divided by the spatial norm is C³ away from the origin. [`coord_div_norm_contDiffOn`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L512).

**Lemma · Normalized coordinates ignore dilation.** A positive dilation leaves each coordinate divided by the spatial norm unchanged. [`coord_div_norm_smul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L520).

**Theorem · Normalized height is C³ off zero.** The normalized height is C³ away from the origin. [`heightRatio_contDiffOn`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L525).

**Theorem · Normalized height ignores dilation.** A positive dilation leaves the normalized height unchanged. [`heightRatio_smul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L528).

**Theorem · Radial frame components are C³.** Each component of the radial frame is C³ away from the origin. [`radialVec_contDiffOn`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L531).

**Theorem · The radial frame ignores dilation.** A positive dilation leaves the radial frame unchanged. [`radialVec_smul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L534).

**Theorem · Regularized azimuthal frame is C³.** Each component of the regularized azimuthal frame is C³ away from the origin. [`azimVecQ_contDiffOn`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L538).

**Theorem · Azimuthal frame ignores dilation.** A positive dilation leaves the regularized azimuthal frame unchanged. [`azimVecQ_smul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L544).

**Theorem · Regularized polar frame is C³.** Each component of the regularized polar frame is C³ away from the origin. [`polarVecQ_contDiffOn`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L553).

**Theorem · The polar frame ignores dilation.** A positive dilation leaves the regularized polar frame unchanged. [`polarVecQ_smul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L561).

**Theorem · Compose through a compact range.** On an open domain, a C³ map with inverse-power derivative bounds and image in a compact set gives a unit-weight derivative estimate after composition with a globally C³ function. [`SymbolW.comp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L571).

**Lemma · Complexification controls derivatives.** At a point where a real scalar function is Cⁱ, the norm of the ith Fréchet derivative of its complexification is at most the absolute value of its ith scalar derivative. [`ofReal_iteratedFDeriv_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L616).

**Theorem · The complementary radius has unit weight.** For valid parameters, the complexified complementary compactified radius satisfies the unit-weight derivative estimate away from the origin. [`chartS_symbol`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L624).

**Theorem · The spatial norm has linear weight.** The complexified spatial norm satisfies the weighted derivative estimate with weight |r| away from the origin. [`norm_symbol`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L671).

**Theorem · Compactified radius has linear weight.** For valid parameters, the complexified compactified radius satisfies the weighted derivative estimate with weight |r| away from the origin. [`chartT_symbol`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L687).

**Theorem · Polynomial substitution preserves C³.** Evaluating a complex bivariate polynomial at two C³ complex functions gives a C³ function. [`mvpoly_contDiff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L706).

**Lemma · Recover real derivative bounds.** A unit-weight estimate for the complexification of a real function yields bounds C/‖y‖ⁱ for its real derivatives through order three on an open domain. [`real_deriv_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L717).

**Theorem · Complementary radius is C³ off zero.** For valid parameters, the complementary compactified radius is C³ away from the origin. [`chartS_contDiffOn`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L732).

**Theorem · A chart polynomial has unit weight.** For valid parameters, every complex bivariate polynomial evaluated at compactified radius and a constant multiple of normalized height has the unit-weight derivative estimate away from the origin. [`piece_symbol`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L740).

**Lemma · Positive-degree maps vanish at zero.** A function positively homogeneous of natural degree at least one takes value zero at the origin. [`hom_zero_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L799).

**Lemma · Homogeneity gives a global power bound.** In a finite-dimensional domain, a degree-d positively homogeneous function with d≥1 that is continuous away from zero satisfies a global bound C‖x‖ᵈ. [`hom_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L809).

**Theorem · High degree supplies smoothness at zero.** In a finite-dimensional domain, a degree-d positively homogeneous function that is Cᵐ away from zero is Cᵐ at zero whenever m< d. [`hom_contDiffAt_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L833).

**Definition · Fourth-power angular core.** The angular core multiplies the fourth power of a complex radius by the integer angular phase exp(ik arg w). [`axisCore`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L902).

**Lemma · The angular core has degree four.** Positive dilation multiplies the angular core by the fourth power of the dilation factor. [`axisCore_hom`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L905).

**Lemma · Integer phase as a normalized power.** For a nonzero complex number and integer k, its k-fold angular exponential equals the kth integer power of its normalization to unit modulus. [`exp_arg_zpow`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L912).

**Lemma · Normalized integer powers are C³.** Every integer power of a normalized complex coordinate is C³ at nonzero points. [`unit_zpow_contDiffAt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L923).

**Lemma · The angular core is C³ off zero.** The fourth-power angular core is C³ away from the complex origin. [`axisCore_contDiffOn`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L936).

**Lemma · The angular core is C³ at every point.** The fourth radial power makes the angular core C³ at every complex point, including the origin. [`axisCore_contDiffAt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L949).

**Definition · Horizontal complex projection.** The plane map is the continuous real-linear projection y↦y₀+iy₁. [`planeMap`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L956).

**Lemma · Evaluate the horizontal projection.** Applying the plane map gives the complex number with real part y₀ and imaginary part y₁. [`planeMap_apply`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L960).

**Lemma · Spatial norm squared by coordinates.** The square of the spatial norm is the sum of the three squared Cartesian coordinates. [`norm_sq_space`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L963).

**Theorem · The angular factor has unit weight.** For every integer angular frequency, q(y)² exp(ik angle(y)) has the unit-weight derivative estimate away from the spatial origin, including points on the axis. [`axis_symbol`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L967).

**Lemma · Bound three exponential derivatives.** For any real frequency, all derivatives through order three of the pure complex exponential are uniformly bounded on the real line. [`phase_deriv_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L1011).

**Lemma · First logarithmic radial derivative.** For positive core radius, the derivative of half the logarithm of 1+r²/r_c² is r/(r²+r_c²). [`logRad_deriv1`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L1049).

**Lemma · Second logarithmic radial derivative.** For positive core radius, the derivative of r/(r²+r_c²) is (r_c²−r²)/(r²+r_c²)². [`logRad_deriv2`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L1061).

**Lemma · Third logarithmic radial derivative.** For positive core radius, the next derivative is (2r³−6r_c²r)/(r²+r_c²)³. [`logRad_deriv3`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L1073).

**Lemma · Inverse-power logarithmic bounds.** For positive core radius and radius s, the first three derivatives of the logarithmic radial phase have absolute value at most 8/sⁱ. [`logRad_iter`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L1091).

**Theorem · Logarithmic phase has unit weight.** For valid parameters and any real phase frequency, the logarithmic radial exponential has the unit-weight derivative estimate away from the origin. [`logPhase_symbol`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L1135).

**Lemma · Derivatives of a shifted real power.** For real L, b and s, the ith total derivative of Lᵇ(r+L)⁻ᵇ at s is Lᵇ times the descending Pochhammer factor at −b times (s+L)⁻ᵇ⁻ⁱ. [`shiftedPow_iteratedDeriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L1177).

**Reader note.** This identity uses Lean’s total real-power and derivative functions, so the statement does not require positive L or s.

**Lemma · Bound the first three power factors.** For 0≤b≤2 and derivative order at most three, the absolute value of the descending Pochhammer factor at −b is at most 24. [`fallingProduct_small`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L1184).

**Lemma · A shifted power loses its decay factor.** For positive L and s and nonnegative b, Lᵇ(s+L)⁻ᵇ⁻ⁱ is at most (s+L)⁻ⁱ. [`shiftedPow_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L1208).

**Lemma · Complementary radius as a quotient.** For valid parameters, the complementary compactified radius is L₀/(‖y‖+L₀). [`chartS_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L1219).

**Lemma · Real powers of complementary radius.** For valid parameters, the bth real power of the complementary compactified radius is L₀ᵇ(‖y‖+L₀)⁻ᵇ. [`chartS_rpow`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L1227).

**Lemma · Shifted powers are C³ at positive radii.** For positive L and radius s, the shifted real-power function Lᵇ(r+L)⁻ᵇ is C³ at s. [`shiftedPow_contDiffAt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L1233).

**Theorem · The decay factor has unit weight.** For valid parameters, the complexified decay factor satisfies the unit-weight derivative estimate away from the origin. [`decay_symbol`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L1238).

**Theorem · The core ratio has unit weight.** For valid parameters, the complexified core ratio evaluated at compactified radius satisfies the unit-weight derivative estimate away from the origin. [`coreRatio_symbol`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L1278).

**Definition · Choose a frame component.** The frame selector returns a component of the radial, regularized polar or regularized azimuthal frame according to its first index. [`vecOf`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L1321).

**Theorem · Unit weight for frame components.** Each complexified selected frame component satisfies the unit-weight derivative estimate away from the origin. [`vecOf_symbol`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L1324).

**Definition · Frozen polynomial model of a wave mode.** The frozen wave model combines decay, the regularized angular phase, logarithmic phase, a quadratic compactified-radius factor, two chart polynomials and one frame component. [`waveModel`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L1337).

**Theorem · A frozen wave has quadratic weight.** For valid parameters, the frozen wave model satisfies a weighted derivative estimate whose radial weight is r². [`waveModel_symbol`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L1348).

**Theorem · Third derivatives of a frozen wave.** For valid parameters, every frozen wave model is C³ away from the origin and has third derivative bounded by K/‖y‖ for some K≥0. [`waveModel_third`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L1369).

**Theorem · Separate angular and radial phase.** The mode phase factors into its integer angular exponential and its logarithmic radial exponential. [`modePhase_split`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L1380).

**Theorem · Differentiate a polynomial radially.** The derivative in the first coordinate of a bivariate polynomial evaluation is the evaluation of its first formal partial derivative. [`mvpoly_hasDerivAt_fst`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L1389).

**Theorem · Differentiate a polynomial in height.** The derivative in the second coordinate of a bivariate polynomial evaluation is the evaluation of its second formal partial derivative. [`mvpoly_hasDerivAt_snd`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L1433).

**Theorem · Local equality preserves radial slopes.** Functions that agree near a coordinate pair have first-coordinate slice derivatives that also agree locally. [`slice_deriv_fst`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L1476).

**Theorem · Local equality preserves height slopes.** Functions that agree near a coordinate pair have second-coordinate slice derivatives that also agree locally. [`slice_deriv_snd`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L1486).

**Definition · Reflect the polynomial height variable.** Polynomial reflection leaves the first indeterminate unchanged and multiplies the second by the prescribed sign. [`flipPoly`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L1496).

**Lemma · Evaluate a reflected polynomial.** Evaluating the reflected polynomial at (t,x) equals evaluating the original polynomial at (t,σx). [`eval_flipPoly`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L1499).

**Definition · The locally selected parity polynomial.** The local polynomial selects a spline piece and applies the height reflection and parity sign appropriate to the base point. [`locPoly`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L1509).

**Lemma · The selected index has a coarse bound.** For any break list, the selected cell index is less than the list length plus one. [`cellIndex_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L1512).

**Lemma · A spline equals its local polynomial.** Away from height zero and the interior radial and absolute-height breaks, a spline agrees locally with evaluation of its selected parity polynomial. [`spline_local`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L1518).

**Definition · Weighted radial wave component.** The radial wave component multiplies the even radial spline by t^(L+2)(1−t) and (1−x²)^(a+2). [`radPart`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L1528).

**Definition · Weighted polar wave component.** The polar wave component multiplies the odd polar spline by t^(L+2)(1−t) and (1−x²)^(a+2). [`polPart`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L1531).

**Lemma · Reduced components of a nonzero mode.** For nonzero mode and orders L+2, a+2 and one, the reduced vector consists of the weighted radial and polar components and an azimuthal component determined by their twisted radial and height derivatives. [`reduced_wave_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L1534).

**Lemma · Differentiate the wave radial weight.** The derivative of t^(L+2)(1−t) is (L+2)t^(L+1)(1−t)−t^(L+2). [`weight_hasDerivAt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L1542).

**Lemma · Differentiate angular vanishing.** The derivative of the complexified angular factor 1−x² is −2x. [`axis_hasDerivAt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L1552).

**Definition · Polynomial wave terms without core ratio.** The first wave polynomial family collects the radial, polar and azimuthal terms remaining after factoring out t²(1−x²)² and separating the core-ratio correction. [`waveQ1`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L1559).

**Definition · Polynomial core-ratio correction.** The second wave polynomial family is zero in the radial and polar slots and records the logarithmic-phase core-ratio correction in the azimuthal slot. [`waveQ2`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L1576).

**Lemma · Factor a local nonzero mode.** With local radial and polar polynomial formulas and the mode orders, each reduced component locally factors as t²(1−x²)² times a polynomial plus the core ratio times a second polynomial. [`wave_local`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L1581).

**Lemma · The chart pair is continuous off zero.** For valid parameters, the pair of compactified radius and normalized height tends to its value at every nonzero point. [`pair_tendsto`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L1655).

**Lemma · Selected index names an existing cell.** For a break list with endpoints zero and one, the selected index is less than the cell count. [`cellIndex_lt_count`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L1666).

**Lemma · Split off the first-variable boundary.** Every bivariate polynomial is its restriction at first coordinate zero plus the first indeterminate times another polynomial. [`first_split`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L1677).

**Lemma · Differentiate the mean radial weight.** The derivative of t(1−t) is 1−2t. [`weight_one_hasDerivAt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L1702).

**Lemma · Reduced components of the mean mode.** When the high order is one, the mean-mode reduced components are the explicit stream, twisted radial and swirl expressions with radial weight t(1−t). [`reduced_mean_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L1711).

**Definition · Polynomial formula for the mean mode.** The mean-mode polynomial family combines the local stream and swirl polynomials, their required derivatives and the radial factor t(1−t) into three reduced components. [`meanQ`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L1720).

**Lemma · Freeze the mean-mode polynomial.** Local polynomial formulas for the stream and swirl splines give local polynomial formulas for all three reduced mean-mode components. [`mean_local`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L1729).

**Lemma · Later cell has an earlier interior break.** If the selected cell index is nonzero, some interior break is at most the selected coordinate. [`exists_break_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L1780).

**Lemma · Reflect an odd boundary decomposition.** If a spline piece is gX₁+X₀R, its odd local parity polynomial retains the boundary term gX₁ and transforms only the remainder by reflection and sign. [`locPoly_odd_split`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L1787).

**Lemma · Reflect an even boundary decomposition.** If a spline piece is g+X₀R, its even local parity polynomial retains g and reflects only the remainder. [`locPoly_even_split`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L1795).

**Definition · Mean guard in chart coordinates.** The chart mean guard has components −g(1−3x²), −3gx and w. [`meanGuardX`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L1802).

**Definition · Residual mean polynomial after the guard.** The residual mean-polynomial family collects the terms left after extracting the prescribed first-order stream and swirl guard from the mean mode. [`meanQA`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L1805).

**Lemma · Split mean guard and quadratic remainder.** If the stream and swirl polynomials have the prescribed boundary decompositions, each mean polynomial equals t times its guard component plus t² times the residual polynomial. [`meanQ_split`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L1818).

**Theorem · Finite local formulas for wave modes.** For a listed nonzero mode of valid data with high radial order one, a finite polynomial family supplies local formulas of the form t²q²(Q₁+coreRatio·Q₂) for every reduced component away from the break interfaces and the origin. [`wave_freeze`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L1829).

**Theorem · Third-derivative bound for a wave mode.** For a listed nonzero mode of valid data with high radial order one, finitely many spheres and cones exclude every formula change, and elsewhere the physical mode is C³ with third derivative at most K/‖y‖. [`waveTerm_third_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L1871).

**Definition · Linear spatial mean guard.** The linear mean guard has components −gy₀−wy₁, wy₀−gy₁ and 2gy₂, using the prescribed stream and swirl guard constants. [`meanLin`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L1938).

**Definition · Mean guard at normalized height.** The mean guard evaluates the chart guard at normalized spatial height using the prescribed stream and swirl constants. [`meanGuard`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L1943).

**Theorem · Mean guard reconstructs a linear field.** At a nonzero point, compactified radius times the frame reconstruction of the mean guard equals the linear spatial guard divided by ‖y‖+L₀. [`meanGuard_sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L1946).

**Theorem · The corrected decay has linear weight.** For valid parameters, decay times complementary compactified radius minus one satisfies the weighted derivative estimate with radial weight |r|. [`decayS_symbol`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L1958).

**Theorem · Linear weight for guard components.** Every constant multiple of a complexified linear mean-guard component satisfies the weighted derivative estimate with radial weight |r| away from the origin. [`meanLin_symbol`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L2059).

**Theorem · Third derivatives of linear functions.** The third Fréchet derivative of any constant multiple of a complexified real linear functional is zero everywhere. [`linear_third_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L2090).

**Theorem · Two local models for the mean mode.** For valid field data with high radial order one containing mode zero, a finite polynomial family and positive threshold give either a local guard-plus-quadratic formula or a local polynomial formula with compactified radius above that threshold away from interfaces. [`mean_freeze`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L2104).

**Definition · Quadratic remainder near the origin.** The near mean model multiplies decay, compactified radius squared, one chart polynomial and one frame component. [`meanNear`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L2186).

**Definition · Polynomial mean model at larger radii.** The far mean model multiplies decay, one chart polynomial and one frame component. [`meanFar`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L2190).

**Definition · Correction to the linear mean guard.** The mean correction is the linear spatial guard divided by L₀, multiplied by decay times complementary compactified radius minus one. [`meanRest`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L2194).

**Theorem · Bound the near mean third derivative.** For valid parameters, each near mean model is C³ away from the origin and has third derivative bounded by K/‖y‖. [`meanNear_third`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L2197).

**Theorem · Bound the mean correction derivative.** For valid parameters, each linear-guard correction is C³ away from the origin and has third derivative bounded by K/‖y‖. [`meanRest_third`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L2214).

**Theorem · Bound the far mean third derivative.** For valid parameters, each far mean model is C³ away from the origin and has third derivative bounded by K/‖y‖³. [`meanFar_third`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L2226).

**Theorem · Bound the mean mode away from interfaces.** For valid field data with high radial order one containing mode zero, finitely many spheres and cones exclude every formula change, and elsewhere the physical mean mode is C³ with third derivative at most K/‖y‖. [`meanTerm_third_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L2240).

**Lemma · Read one reconstructed component.** The jth coordinate of a vector reconstructed from three components is the jth supplied component. [`ofComponents_apply`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L2386).

**Lemma · The field is the sum of its modes.** The reconstructed physical field equals the finite sum of its listed physical mode contributions. [`fieldOf_eq_sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L2389).

**Lemma · C³ differentiates the Hessian.** If a function is C³ at a point, its second total Fréchet derivative is differentiable there and the norm of its derivative equals the norm of the third iterated Fréchet derivative. [`third_of_contDiffAt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L2397).

**Theorem · Third-derivative bounds between breaks.** For valid field data with high radial order one, a finite set of spheres and cones contains all interface exceptions, and at every other nonzero point the second derivative of the physical field is differentiable with derivative norm at most K/‖y‖. [`fieldOf_third_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldJumpsPieces.lean#L2406).
<!-- /passage:front -->

