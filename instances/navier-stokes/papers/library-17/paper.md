
<!-- passage:front -->
# Library guide 17: Breakdown/FracCell

**Navier–Stokes pages:** [the paper](../navier-stokes-paper/paper.pdf) · [proof routes](../navier-stokes-routes/paper.md) · [routes in detail](../navier-stokes-route-details/paper.md) · library guide: [1](../navier-stokes-library-01/paper.md) [2](../navier-stokes-library-02/paper.md) [3](../navier-stokes-library-03/paper.md) [4](../navier-stokes-library-04/paper.md) [5](../navier-stokes-library-05/paper.md) [6](../navier-stokes-library-06/paper.md) [7](../navier-stokes-library-07/paper.md) [8](../navier-stokes-library-08/paper.md) [9](../navier-stokes-library-09/paper.md) [10](../navier-stokes-library-10/paper.md) [11](../navier-stokes-library-11/paper.md) [12](../navier-stokes-library-12/paper.md) [13](../navier-stokes-library-13/paper.md) [14](../navier-stokes-library-14/paper.md) [15](../navier-stokes-library-15/paper.md) [16](../navier-stokes-library-16/paper.md) **17** [18](../navier-stokes-library-18/paper.md) [19](../navier-stokes-library-19/paper.md) [20](../navier-stokes-library-20/paper.md) [21](../navier-stokes-library-21/paper.md) [22](../navier-stokes-library-22/paper.md) [23](../navier-stokes-library-23/paper.md) [24](../navier-stokes-library-24/paper.md) [25](../navier-stokes-library-25/paper.md) [26](../navier-stokes-library-26/paper.md) [27](../navier-stokes-library-27/paper.md) [28](../navier-stokes-library-28/paper.md) [29](../navier-stokes-library-29/paper.md) [30](../navier-stokes-library-30/paper.md)

*A plain title and a sentence for each declaration in `Breakdown.FracCell.EnergyRadialParts` to `Breakdown.FracCell.GivenAuxInverseSquareRing` of Alpöge and Buckmaster's Lean at `ad53419de079eb8f95f60313473374624a348546`, in the authors' file order. Prepared with AI assistance. The authors have not reviewed it.*

Each paragraph names one declaration and says whether it is a definition, a proposition that the library defines (its name usually ends in `Holds` or `Statement`) or a proved result, then what it states. Click a paragraph to open its Lean on the right.

### Breakdown.FracCell.EnergyRadialParts

This file converts the radial trace law into the interior, projected and outer test forms whose sum is the radial cell energy.

**The radial trace interface.** The interface requires mode integrability and radial integration by parts with face moments, allowing a cell on the axis when the radial test vanishes there. (`Breakdown.CellCert.CellEnergy.RadialTraceStatement`)

Proved by `Breakdown.CellCert.CellEnergy.radialTrace`.

**Radial integration by parts.** For a second-order field on a valid cell away from the axis, the radial-trace interface gives integration by parts for component combinations and endpoint-vanishing radial tests. (`Breakdown.CellCert.CellEnergy.RadialInner.field_parts`)

**An unweighted low-row pairing.** Under the radial trace and energy-setting assumptions away from the axis, a low pairing row equals the strain-field integral against a polynomial test. (`Breakdown.CellCert.CellEnergy.RadialInner.low_pair`)

**Construct the interior radial test.** Within the stated degree bounds, the weighted interior monomial has a C1 radial factor vanishing at both endpoints whose derivative stays in the required polynomial space. (`Breakdown.CellCert.CellEnergy.RadialInner.inner_test`)

**The reference-radius endpoint factor.** One minus the squared reference radius equals four times the product of the endpoint distances divided by the squared radial width. (`Breakdown.CellCert.CellEnergy.RadialInner.one_sub_refR_sq`)

**The interior radial weight is continuous.** The interior radial weight is continuous. (`Breakdown.CellCert.CellEnergy.RadialInner.weight_cont`)

**Nonnegative interior radial weight.** On a valid cell rectangle, the interior radial weight is nonnegative. (`Breakdown.CellCert.CellEnergy.RadialInner.weight_nonneg`)

**The interior radial weight is positive.** On the interior of a valid cell, the interior radial weight is positive. (`Breakdown.CellCert.CellEnergy.RadialInner.weight_pos`)

**Cancel a squared real weight.** A squared real weight times a complex quotient can be rearranged into a product with one copy of the weight, including the zero-weight convention. (`Breakdown.CellCert.CellEnergy.RadialOuter.ptw`)

**The outer radial test supremum.** For positive degree cutoff and identified integrable moments, the outer radial test supremum equals its inverse-Gram row form. (`Breakdown.CellCert.CellEnergy.RadialOuter.outer_sup`)

**Add outer row evaluations.** Evaluation of a sum of outer-row functions equals the sum of their evaluations. (`Breakdown.CellCert.CellEnergy.RadialOuter.rowApply_add`)

**Sum outer row evaluations.** Evaluation commutes with finite sums of outer-row functions. (`Breakdown.CellCert.CellEnergy.RadialOuter.rowApply_sum`)

**Scale outer row evaluations.** A complex scalar multiplying an outer-row function factors out of its evaluation. (`Breakdown.CellCert.CellEnergy.RadialOuter.rowApply_mul`)

**Expand radial face moments.** Under the radial trace and energy-setting assumptions, height moments convert represented radial face rows into component-weighted monomial face moments. (`Breakdown.CellCert.CellEnergy.RadialOuter.face_expand`)

**The weighted low-row pairing.** Under the radial trace and energy-setting assumptions, the weighted low pairing row equals the strain-field integral against the line-weighted polynomial test. (`Breakdown.CellCert.CellEnergy.RadialOuter.low_pair_weighted`)

**The negative product test is polynomial.** The negative product of a bounded-degree radial polynomial and a bounded-degree height power lies in the required polynomial space. (`Breakdown.CellCert.CellEnergy.RadialOuter.poly_mem`)

**Construct the outer radial test.** The outer radial test admits a C1 radial factor with the prescribed endpoint values and a polynomial weighted derivative within the selected cutoff. (`Breakdown.CellCert.CellEnergy.RadialOuter.outer_test`)

**The outer radial row value.** Under the radial trace and energy-setting assumptions, the outer radial row is the radial-field moment weighted by radius, reference radius and the outer test. (`Breakdown.CellCert.CellEnergy.RadialOuter.outer_row`)

**The radial projection form value.** Under the radial trace and energy-setting assumptions, the radial projection form equals the weighted radial-derivative energy of the projected strain field. (`Breakdown.CellCert.CellEnergy.RadialPieces.proj_piece`)

**The interior radial form value.** For a cell away from the axis, the radial trace and energy setting identify the interior radial form with its weighted polynomial test supremum. (`Breakdown.CellCert.CellEnergy.RadialPieces.inner_piece`)

**The outer radial form value.** The radial trace and energy setting identify the outer radial form with the radius-weighted test supremum of the reference-radius radial field. (`Breakdown.CellCert.CellEnergy.RadialPieces.outer_piece`)

### Breakdown.FracCell.EnergyRadialProj

This file differentiates the finite polynomial projection in radius and identifies the represented low rows with strain coefficients.

**Continuity of the radial line weight.** The cell line weight is continuous as a function of radius. (`Breakdown.CellCert.CellEnergy.RadialProjInternal.lineWeight_cont`)

**Continuity of the reference radius.** The cell reference-radius coordinate is continuous. (`Breakdown.CellCert.CellEnergy.RadialProjInternal.refR_cont`)

**Radial basis polynomials are C1.** Every radial basis polynomial is continuously differentiable. (`Breakdown.CellCert.CellEnergy.RadialProjInternal.radialPoly_diff`)

**Continuity of the height basis.** Every height basis polynomial is continuous. (`Breakdown.CellCert.CellEnergy.RadialProjInternal.heightPoly_cont`)

**Radial slope of a product basis.** The radial slope of a tensor-product basis function is the derivative of its radial factor times its height factor. (`Breakdown.CellCert.CellEnergy.RadialProjInternal.slope_eq`)

**Continuity of a radial basis slope.** Every tensor-product basis function has a continuous radial slope. (`Breakdown.CellCert.CellEnergy.RadialProjInternal.slope_cont`)

**Differentiate the radial basis expansion.** The radial derivative of a finite complex basis expansion is the same coefficient sum of the radial basis slopes. (`Breakdown.CellCert.CellEnergy.RadialProjInternal.deriv_basis_sum`)

**Represented low rows give coefficients.** A representation of the field and mode integrability identify each low strain-combination row with its basis coefficient. (`Breakdown.CellCert.CellEnergy.RadialProjInternal.row_value`)

### Breakdown.FracCell.EnergyTop

This file turns differences of polynomial projection energies into the explicit top-degree coefficient form used in the cell energy allowance.

**The top-form rectangle is compact.** The cell rectangle used by the top-form calculation is compact. (`Breakdown.CellCert.CellEnergy.TopFormInternal.rect_compact`)

**The complex line weight is continuous.** The line weight embedded in the complex numbers is continuous on the radial-height plane. (`Breakdown.CellCert.CellEnergy.TopFormInternal.lw_cont`)

**Weighted integrals of continuous fields.** A continuous complex field is integrable on the rectangle after multiplication by the line weight. (`Breakdown.CellCert.CellEnergy.TopFormInternal.good_of_cont`)

**Multiply by a continuous test.** A line-weighted integrable field remains integrable after multiplication by a conjugated continuous test on the cell rectangle. (`Breakdown.CellCert.CellEnergy.TopFormInternal.int_mul`)

**Expand the weighted pairing definition.** The cell pairing with line weight is the rectangle integral of the weighted field times the conjugate test. (`Breakdown.CellCert.CellEnergy.TopFormInternal.pair_def`)

**Subtract in the first pairing argument.** For line-weighted integrable fields and a continuous test, subtracting the first arguments subtracts their pairings. (`Breakdown.CellCert.CellEnergy.TopFormInternal.pair_sub_left`)

**Sum the second pairing argument.** For a line-weighted integrable field and finitely many continuous tests, pairing with their sum equals the sum of the pairings. (`Breakdown.CellCert.CellEnergy.TopFormInternal.pair_sum_right`)

**Scale the second pairing argument.** A scalar multiplying the second weighted-pairing argument comes out conjugated. (`Breakdown.CellCert.CellEnergy.TopFormInternal.pair_smul_right`)

**Sum the first pairing argument.** For continuous fields and test, a finite sum in the first weighted-pairing argument becomes a sum of pairings. (`Breakdown.CellCert.CellEnergy.TopFormInternal.pair_sum_left`)

**Scale the first pairing argument.** A scalar multiplying the first weighted-pairing argument comes out unchanged. (`Breakdown.CellCert.CellEnergy.TopFormInternal.pair_smul_left`)

**Conjugating a weighted pairing swaps it.** Conjugating the real-weighted cell pairing exchanges its two arguments. (`Breakdown.CellCert.CellEnergy.TopFormInternal.pair_conj`)

**A square norm is a self-pairing.** The weighted square norm is the real part of the field's weighted self-pairing. (`Breakdown.CellCert.CellEnergy.TopFormInternal.normSq_eq`)

**The complex product basis.** The complex product basis is the real cell basis embedded in the complex numbers. (`Breakdown.CellCert.CellEnergy.TopFormInternal.basisC`)

**Continuity of the complex product basis.** Every complex product basis function is continuous. (`Breakdown.CellCert.CellEnergy.TopFormInternal.basisC_cont`)

**The basis pairing matrix is identity.** A valid cell basis has weighted pairings equal to one for matching two-dimensional indices and zero otherwise. (`Breakdown.CellCert.CellEnergy.TopFormInternal.pairingMat`)

**Expand a first-slot basis combination.** Pairing a finite basis combination with a continuous test gives the same coefficient sum of basis pairings. (`Breakdown.CellCert.CellEnergy.TopFormInternal.pair_comb_left`)

**Expand a second-slot basis combination.** Pairing an integrable field with a finite basis combination gives the sum of basis pairings with conjugated coefficients. (`Breakdown.CellCert.CellEnergy.TopFormInternal.pair_comb_right`)

**Expand powers in a triangular family.** Positive leading coefficients give a finite triangular-polynomial expansion of every real power within the degree cutoff. (`Breakdown.CellCert.CellEnergy.TopFormInternal.pow_span`)

**Expand monomials in the product basis.** A valid cell basis gives a finite complex product-basis expansion of each monomial within the two degree cutoffs. (`Breakdown.CellCert.CellEnergy.TopFormInternal.mono_expand`)

**Finite sums preserve polynomial degrees.** A finite sum of functions in the same bounded-degree polynomial space stays in that space. (`Breakdown.CellCert.CellEnergy.TopFormInternal.poly_sum`)

**Scaling preserves polynomial degrees.** Complex scalar multiplication preserves the indicated polynomial degree limits. (`Breakdown.CellCert.CellEnergy.TopFormInternal.poly_smul`)

**Monomials satisfy the degree limits.** A monomial belongs to the polynomial space whenever each exponent satisfies its corresponding cutoff. (`Breakdown.CellCert.CellEnergy.TopFormInternal.poly_mono`)

**Basis functions have the required degree.** A complex cell basis function belongs to the polynomial space determined by cutoffs above its indices. (`Breakdown.CellCert.CellEnergy.TopFormInternal.poly_basis`)

**Polynomial functions are continuous.** Every function in the indicated finite polynomial space is continuous. (`Breakdown.CellCert.CellEnergy.TopFormInternal.poly_cont`)

**A basis pairing gives the coefficient.** The line-weighted pairing with a real basis function embedded in the complex numbers equals the corresponding cell coefficient. (`Breakdown.CellCert.CellEnergy.TopFormInternal.coef_eq`)

**Projection norm from coefficient squares.** For a valid cell basis and line-weighted integrable field, the projected square norm is the finite sum of squared coefficient norms. (`Breakdown.CellCert.CellEnergy.TopFormInternal.normSq_proj`)

**Quadratic evaluation adds matrices.** Quadratic evaluation of a matrix sum equals the sum of its two evaluations. (`Breakdown.CellCert.CellEnergy.TopFormInternal.qfv_add`)

**Quadratic evaluation sums matrices.** Quadratic evaluation commutes with a finite sum of matrices. (`Breakdown.CellCert.CellEnergy.TopFormInternal.qfv_sum`)

**Evaluate a diagonal selected-slot form.** A diagonal form pulled back through coordinate-selection rows equals the weighted sum of squared selected coordinates. (`Breakdown.CellCert.CellEnergy.TopFormInternal.quad_diag`)

**Unit low rows select strain slots.** A low row formed from a unit component array is exactly the coordinate-selection row for that strain slot. (`Breakdown.CellCert.CellEnergy.TopFormInternal.rows_eq`)

**Replace product indices by nested sums.** Summing over a product of finite index types equals the corresponding two nested range sums. (`Breakdown.CellCert.CellEnergy.TopFormInternal.prod_to_range`)

**Select the upper tail of a finite sum.** An indicator selecting indices above the lower cutoff gives the full finite sum minus its lower prefix. (`Breakdown.CellCert.CellEnergy.TopFormInternal.ind_sum`)

**Select the lower part of a finite sum.** An indicator selecting indices below a cutoff gives the sum over that shorter range. (`Breakdown.CellCert.CellEnergy.TopFormInternal.low_sum`)

**Separate the top-degree bands.** For cutoff at least two, the two selected upper index bands equal the displayed differences of rectangular coefficient sums. (`Breakdown.CellCert.CellEnergy.TopFormInternal.top_arith`)

**The top-degree energy form.** The mode-integrability statement identifies each retained mode’s top matrix form with the sum over components of the top-degree radial and height gradient energies in every valid energy setting. (`Breakdown.CellCert.CellEnergy.topForm_holds`)

### Breakdown.FracCell.ExteriorDefs

This file records the geometric and coefficient bounds used to control the quadratic form outside the finite cell region.

**The exterior geometric and analytic data.** The proposition structure requires a positive bounded homogeneous exterior radius, its almost-everywhere region identity, strain and curl-gradient bounds, and the final coefficient inequality. (`Breakdown.CellCert.Exterior.IsExteriorData`)

### Breakdown.FracCell.ExteriorNonneg

This file combines pointwise coefficient bounds with the weak radial estimate to prove nonnegativity outside the cell region.

**Entry square is nonnegative.** The sum of squared matrix entries is nonnegative. (`_private.Breakdown.FracCell.ExteriorNonneg.0.Breakdown.CellCert.Exterior.entrySq_nonneg'`)

**Absorb the exterior cross term.** Under the stated sign and coefficient bounds, the exterior lower estimate is bounded below by the adjusted gradient energy minus the inverse-square velocity cost. (`_private.Breakdown.FracCell.ExteriorNonneg.0.Breakdown.CellCert.Exterior.pointwise_real`)

**Exterior energy is nonnegative.** The weak-ray and exterior-pointwise interfaces imply exterior nonnegativity. (`Breakdown.CellCert.Exterior.exteriorNonneg_of`)

### Breakdown.FracCell.ExteriorPart

This file carries the exterior nonnegativity estimate into the exterior part of the full cell-form decomposition.

**The exterior form contribution.** The exterior-nonnegativity interface implies nonnegativity of the exterior part of the cell form. (`Breakdown.CellCert.Exterior.exteriorPartNonneg_of`)

### Breakdown.FracCell.ExteriorPointwise

This file supplies the pointwise exterior inequality that precedes radial integration.

**The pointwise exterior estimate.** For 1 < α < 5/4, valid form and exterior data and an admissible input bound the local density outside the cell region below by the gradient-energy coefficient minus the stated wave and mean curl-gradient velocity costs. (`Breakdown.CellCert.Exterior.exteriorPointwise`)

### Breakdown.FracCell.FarSupportZeroExtension

This file extends a far-field kernel by zero when its supporting set of retained coordinates is enlarged, preserving its form and dominance bound.

**Extend a far kernel by zero.** The extended kernel agrees with the original when both indices lie in the selected low support or auxiliary coordinates and is zero otherwise. (`Breakdown.CellCert.CellSystem.zeroExtKernel`)

**The extension agrees on its support.** For two indices in the retained support, the zero-extended kernel equals the original kernel. (`Breakdown.CellCert.CellSystem.zeroExtKernel_of_mem`)

**Zero outside the first support.** If the first index lies outside the retained support, the extended kernel is zero. (`Breakdown.CellCert.CellSystem.zeroExtKernel_of_not_mem_left`)

**Zero outside the second support.** If the second index lies outside the retained support, the extended kernel is zero. (`Breakdown.CellCert.CellSystem.zeroExtKernel_of_not_mem_right`)

**Enlarging support preserves the sum.** Summing a zero-extended kernel over a larger support gives the original quadratic sum over the smaller support. (`Breakdown.CellCert.CellSystem.kernelSum_zeroExt`)

**Preserve far-field kernel dominance.** A kernel dominating the far majorant on a smaller support still dominates it after zero extension to the full low support. (`Breakdown.CellCert.CellSystem.farKernelDominates_of_system`)

**The zero extension preserves the matrix.** Replacing an extended far kernel and larger support by its original kernel and smaller support leaves the assembled far matrix unchanged. (`Breakdown.CellCert.CellSystem.farMatrix_zeroExt`)

### Breakdown.FracCell.FieldJointSmooth

This file proves joint smoothness of the parameter-dependent spline field away from chart seams and excluded coordinate sets.

**Smoothness in a neighbourhood.** The predicate says that the two-variable complex function is smooth on some open neighbourhood of the selected point. (`Breakdown.FracInternal.FieldJoint.SmoothNear`)

**Local smooth functions add.** Adding two functions smooth near the same point preserves local smoothness. (`Breakdown.FracInternal.FieldJoint.smoothNear_add`)

**Local smooth functions multiply.** Multiplying two functions smooth near the same point preserves local smoothness. (`Breakdown.FracInternal.FieldJoint.smoothNear_mul`)

**Global smoothness gives local smoothness.** A globally smooth two-variable function is smooth near every point. (`Breakdown.FracInternal.FieldJoint.smoothNear_smooth`)

**Differentiate the first local variable.** The first partial derivative of a locally smooth function remains locally smooth. (`Breakdown.FracInternal.FieldJoint.smoothNear_derivT`)

**Differentiate the second local variable.** The partial derivative in the second coordinate of a locally smooth function remains locally smooth. (`Breakdown.FracInternal.FieldJoint.smoothNear_derivX`)

**Spline smoothness away from breaks.** A reflected spline evaluation is smooth near points away from its radial breaks, polar breaks and zero polar coordinate. (`Breakdown.FracInternal.FieldJoint.smoothNear_spline`)

**Add an unused smooth parameter.** A function smooth near a two-variable point remains smooth at that point after adjoining an unused parameter. (`Breakdown.FracInternal.FieldJoint.smoothNear_contDiffAt`)

**Embed a smooth real function in complex.** Embedding a real smooth function into the complex numbers preserves smoothness at the selected point. (`Breakdown.FracInternal.FieldJoint.ofReal_contDiffAt`)

**Smoothness of the core ratio.** For valid chart parameters, the core-ratio factor is smooth as a function of the parameter and chart coordinates. (`Breakdown.FracInternal.FieldJoint.coreRatio_contDiffAt`)

**Joint smoothness of twisted scaling.** For valid chart parameters and a locally smooth amplitude, the twisted scale is jointly smooth in the phase parameter and chart coordinates. (`Breakdown.FracInternal.FieldJoint.twisted_contDiffAt`)

**A smooth amplitude is locally smooth.** A globally smooth real amplitude, embedded in the complex numbers, satisfies the local smoothness predicate. (`Breakdown.FracInternal.FieldJoint.smoothNear_real`)

**Powers preserve local smoothness.** Every natural power of a locally smooth complex amplitude remains locally smooth. (`Breakdown.FracInternal.FieldJoint.smoothNear_pow`)

**Joint smoothness of reduced components.** For valid chart parameters and away from all amplitude spline breaks and zero polar coordinate, each reduced field component is jointly smooth in the phase parameter and chart variables. (`Breakdown.FracInternal.FieldJoint.reduced_contDiffAt`)

**Joint smoothness of the spatial field.** Away from the stated origin, angular, polar and spline-break exclusions, the field is jointly smooth in the phase parameter and spatial point. (`Breakdown.FracInternal.FieldJoint.joint_fieldOf`)

### Breakdown.FracCell.FieldModeSquare

This file proves weighted square integrability of velocity and gradient modes on valid cells, supplying the regularity needed for coefficient pairings and energy sums.

**Weighted squares of field modes.** For a valid cell and a second-order field, every gradient-mode entry and velocity-mode component is weighted square integrable on the cell rectangle. (`Breakdown.CellCert.CellAnalysis.fieldModeSquare_holds`)

### Breakdown.FracCell.FieldWitness

This file constructs the smoothing witnesses used by spectral cell bounds, combining interval certificates with the on-axis and off-axis constructions.

**One cutoff for the permitted polynomials.** An axis gradient bound and smoothing parameter at least twenty-four give a single Lipschitz cutoff satisfying the axis estimate for every polynomial within the degree cutoff and index zero or one, with zero constant term required at index one. (`Breakdown.CellCert.Spectral.Internal.FieldWitness.axisClosed_uniform`)

**The certificate minimum is attained.** The certificate minimum is either one or a value from a certificate pair whose parameter is within the selected threshold. (`Breakdown.CellCert.Spectral.Internal.FieldWitness.certMin_mem`)

**The trivial interval bound.** At positive smoothing parameter, the smoothed polynomial pairing is at most the polynomial's interval square integral. (`Breakdown.CellCert.Spectral.Internal.FieldWitness.interval_trivial`)

**The trivial axis certificate.** For positive parameter, bound one with the zero cutoff is an axis certificate. (`Breakdown.CellCert.Spectral.Internal.FieldWitness.axis_trivial`)

**The interval upper bound is certified.** Valid spectral data, the closed-interval interface and a positive smoothing parameter give an interval certificate at the stored upper bound. (`Breakdown.CellCert.Spectral.Internal.FieldWitness.intervalUpper_cert`)

**The axis upper bound has a certificate.** For valid spectral data on an axis block and positive parameter, some no-larger parameter and cutoff realize an axis certificate at the stored upper bound. (`Breakdown.CellCert.Spectral.Internal.FieldWitness.axisUpper_cert`)

**Pair two interval resolvents.** The interval-identity interface expresses the resolvent-polynomial pairing as the resolvent pairing plus inverse-parameter derivative pairing. (`Breakdown.CellCert.Spectral.Internal.FieldWitness.resolvent_pair`)

**Scale the interval smoothing estimate.** An interval certificate at the rescaled positive parameter bounds the physical-interval approximation and derivative energies for every polynomial within the degree cutoff. (`Breakdown.CellCert.Spectral.Internal.FieldWitness.interval_scaled`)

**Pad the even-derivative series.** The finite even-derivative polynomial series can be extended to any range longer than the polynomial degree with zero additional derivatives. (`Breakdown.CellCert.Spectral.Internal.FieldWitness.evenSeries_eq_range`)

**The even-derivative series is linear.** The even-derivative series respects real linear combinations of polynomials. (`Breakdown.CellCert.Spectral.Internal.FieldWitness.evenSeries_linear`)

**The interval resolvent is linear.** The interval resolvent respects real linear combinations of polynomials. (`Breakdown.CellCert.Spectral.Internal.FieldWitness.resolvent_linear`)

**The smoothed polynomial pairing identity.** The interval-identity interface expresses the smoothed pairing as the approximation-error pairing plus inverse-parameter derivative pairing. (`Breakdown.CellCert.Spectral.Internal.FieldWitness.smoothed_pair`)

**Construct the field smoothing witness.** The closed-interval, off-axis-core and on-axis-core statements give every square integrable block field an approximation with a square integrable weak gradient and prescribed block modes whose squared error plus inverse-parameter gradient energy satisfies the stored spectral bound for every positive smoothing parameter and valid spectral data. (`Breakdown.CellCert.Spectral.fieldWitness_of_cores`)

### Breakdown.FracCell.FieldWitnessRect

This file states the rectangle smoothing estimates that supply the off-axis and on-axis field witnesses.

**The off-axis rectangle witness.** Positive smoothing parameter, ordered rectangle endpoints and two interval certificates give a C1 boundary-vanishing approximation with the stated error, gradient and mass bound. (`Breakdown.CellCert.Spectral.RectOffStatement`)

Proved by `Breakdown.CellCert.Spectral.rectOff_holds`.

**The axis rectangle witness.** Compatible axis and interval certificates give a finite radial expansion with endpoint-vanishing C1 height coefficients and the stated radially weighted error and gradient bound. (`Breakdown.CellCert.Spectral.RectAxisStatement`)

Proved by `Breakdown.CellCert.Spectral.rectAxis_holds`.

### Breakdown.FracCell.FieldWitnessSt

This file states the mode-compatible smoothing predicate and the separate block constructions for cells touching or avoiding the axis.

**A mode-compatible smoothing witness.** The predicate requires an L2 approximant with a square-integrable weak gradient, the prescribed block modes and the stated approximation-plus-gradient energy bound. (`Breakdown.CellCert.Spectral.BlockSmoothing`)

**The off-axis block construction.** For a valid positive-inner-radius block, compatible interval certificates give a smoothing witness with the radius-ratio and angular-frequency allowance. (`Breakdown.CellCert.Spectral.OffAxisCoreStatement`)

Proved from further statements by `Breakdown.CellCert.Spectral.offAxisCore_of_rect`, `Breakdown.CellCert.Spectral.offAxisCore_of_grad`, `Breakdown.CellCert.Spectral.offAxisCore_of_weak`, `Breakdown.CellCert.Spectral.offAxisCore_of_parts`.

**The on-axis block construction.** For an axis block of zero mode, compatible axis and height certificates give a smoothing witness bounded by the sum of their two constants. (`Breakdown.CellCert.Spectral.OnAxisCoreStatement`)

Proved from further statements by `Breakdown.CellCert.Spectral.onAxisCore_of_parts`, `Breakdown.CellCert.Spectral.onAxisCore_of_rect`.

### Breakdown.FracCell.FinalChain

This file assembles the analytic interfaces, cell geometry, polynomial rows, tree decomposition and spectral estimates into the conditional fractional breakdown chain at exponent 501/500. Its providers establish analytic implications; the cell-system condition remains a hypothesis requiring suitable concrete data.

**The chosen exponent is in range.** The exponent 501/500 lies strictly between one and five quarters. (`Breakdown.CellCert.FinalChain.order_bounds`)

**A cell certificate implies breakdown.** A fractional cell-certificate hypothesis at exponent 501/500 implies the stated fractional breakdown assertions on both Euclidean space and the torus. (`Breakdown.CellCert.FinalChain.breakdown_of_cellHypothesis`)

**The remaining cell assumptions.** The proposition packages the base, geometric, row, centre, model and approximation assumptions that remain before form nonnegativity and the two spectral estimates are supplied. (`Breakdown.CellCert.FinalChain.IsCellRest`)

**The remaining split assumptions.** The proposition requires measurable cells whose union equals the cell region, negligible overlaps, supported rows, linear admissible moments, compatible injective actuator slots and vanishing delay forms. (`Breakdown.CellCert.FinalChain.IsCellSplitRest`)

**The data attached to one cell.** The structure stores a box, scalar bounds, polynomial bases, mode classes, rows and coordinates for one entry of the cell decomposition. (`Breakdown.CellCert.FinalChain.CellEntry`)

**The facts attached to one cell.** The proposition requires valid cell and coordinate data, agreement of the split cell with the solid box almost everywhere, and agreement of row assignment with cell membership. (`Breakdown.CellCert.FinalChain.IsCellFacts`)

**Recover the form assumptions.** The remaining cell assumptions imply the form-data conditions at the same exponent. (`Breakdown.CellCert.FinalChain.isFormData_of_rest`)

**Complete the cell certificate.** The remaining cell assumptions, form nonnegativity, the spectral smoothing estimate and the spectral tail estimate together imply the full fractional cell condition. (`Breakdown.CellCert.FinalChain.isFracCell_of_rest`)

**Assemble the analytic layers.** For exponent between one and five quarters, compatible cell, split, tree, matrix and spectral data with the stated tail bound imply the full fractional cell condition. (`Breakdown.CellCert.FinalChain.isFracCell_of_layers`)

**Complete the cell split.** In the permitted exponent range, form data, the remaining split assumptions, exterior data and the facts for every cell imply the complete cell-split condition. (`Breakdown.CellCert.FinalChain.isCellSplit_of_cells`)

**The layers imply fractional breakdown.** At exponent 501/500, the compatible cell, split, tree, matrix and spectral layers with the required tail bound imply breakdown on space and on the torus. (`Breakdown.CellCert.FinalChain.breakdown_of_layers`)

**Assemble the box scalar bounds.** Valid box and weight tests, the stated degree gaps, unresolved-mode vanishing, nonnegative mean and wave bounds, and the strain estimate imply the cell-scalar conditions at exponent 501/500. (`Breakdown.CellCert.FinalCellSystem.CellDataBoxInternal.scalars_of`)

**Valid cell boxes, scalars and bases.** The cell-system condition gives every split cell a valid box, valid scalars at exponent 501/500 and valid polynomial bases. (`Breakdown.CellCert.FinalCellSystem.cellDataBox_holds`)

**Reflect the model fields.** For a valid model instance inside the cell region and away from zero height, the model velocity, curl, strain, curl gradient, actuator gradient and pin fields obey their specified reflection identities. (`_private.Breakdown.FracCell.FinalChain.0.Breakdown.CellCert.FinalCellSystem.model_mirror_of_instance`)

**Model conditions from centre data.** The centre smoothness, weak second derivative and symmetry interfaces, together with the model and auxiliary clauses, imply the cell model-data interface. (`Breakdown.CellCert.FinalCellSystem.cellDataModel_of`)

**Supported rows with prescribed modes.** The cell-system condition gives each split cell rows supported there, vanishing outside their prescribed modes and assigned opposite-mode pair, with positive row weights. (`Breakdown.CellCert.FinalCellSystem.cellDataRows_holds`)

**An escaping subset has zero volume.** A subset of a convex set has zero volume if every point admits a direction that leaves the convex set immediately for every positive displacement. (`_private.Breakdown.FracCell.FinalChain.0.Breakdown.CellCert.FinalCellSystem.null_of_escape`)

**A coordinate plane has zero volume.** The set on which one spatial coordinate equals a fixed real number has zero volume. (`_private.Breakdown.FracCell.FinalChain.0.Breakdown.CellCert.FinalCellSystem.coord_null`)

**A radial level has zero volume.** A fixed cylindrical-radius level set has zero volume. (`_private.Breakdown.FracCell.FinalChain.0.Breakdown.CellCert.FinalCellSystem.radius_null`)

**A height level has zero volume.** A fixed level set of the absolute cylindrical height has zero volume. (`_private.Breakdown.FracCell.FinalChain.0.Breakdown.CellCert.FinalCellSystem.height_null`)

**Separated cell solids barely overlap.** When the radial or height intervals are separated by the stated weak endpoint inequalities, the intersection of the two cell solids has zero volume. (`Breakdown.CellCert.FinalCellSystem.solid_inter_null`)

**Distinct cells have null overlap.** The cell-system condition makes the intersection of any two distinct split cells have zero volume. (`Breakdown.CellCert.FinalCellSystem.cellsApart_holds`)

**Rows vanish outside their cells.** For valid mesh and row instances, each row vanishes outside the solid box of its assigned cell, as required by the row support interface. (`Breakdown.CellCert.FinalCellSystem.rowsInCellOf_holds`)

**Assemble the given-data components.** The listed profile, centre, actuator, adjoint, region, model, row, weight and exterior interfaces turn a cell-system condition into the base, cell, exterior and extra given-data conditions together with row orthonormality. (`Breakdown.CellCert.FinalCellSystem.givenParts_of_system`)

**Recover the remaining cell assumptions.** The kernel, row-mode, adjoint, row-turn, sum-weight and centre-splitting interfaces turn the cell-system and given-data conditions into the remaining cell assumptions at exponent 501/500. (`Breakdown.CellCert.FinalCellSystem.cellRest_of_system`)

**Recover the exterior data.** The ball-containment interface, cell-system condition and exterior given-data condition imply valid exterior data at exponent 501/500. (`Breakdown.CellCert.FinalCellSystem.exterior_of_system`)

**Recover the remaining split assumptions.** The mesh-moment and split-geometry interfaces, together with the cell-system and form-data conditions, imply the remaining assumptions for the system's cell split. (`Breakdown.CellCert.FinalCellSystem.splitRest_of_mesh`)

**Assemble each cell's local data.** The row-polynomial, row-trace, normal-trace, cell-data, coordinate-data and row-membership statements give every cell of a valid system valid cell data and coordinates at exponent 501/500, with row assignment equivalent to membership in its row set. (`Breakdown.CellCert.FinalCellSystem.cellOfSystem_of_rest`)

**Assemble the cell-data groups.** The box, model, row and far-field cell-data statements combine the geometric and scalar validity, model regularity and symmetries, row support and mode restrictions, class coverage and matrix bounds for every cell of a valid system at exponent 501/500. (`Breakdown.CellCert.FinalCellSystem.cellDataRest_of_groups`)

**Row assignment equals cell membership.** Under the cell-system condition, assignment of a row to a split cell is equivalent to membership in that cell’s row set. (`Breakdown.CellCert.FinalCellSystem.rowsHere_holds`)

**A cell solid is measurable.** The solid associated with a cell box is a measurable subset of space. (`Breakdown.CellCert.FinalCellSystem.solid_measurable`)

**Assemble the split geometry.** The row-support and cell-separation statements give a valid cell system measurable cells with pairwise null overlaps whose union equals the cell region, and make every row vanish outside its assigned cell. (`Breakdown.CellCert.FinalCellSystem.splitGeometry_of`)

**Assemble the cell row facts.** The row-support, allowed-mode, assigned-mode and row-clause statements give every cell of a valid system supported rows with positive weights whose modes vanish outside the prescribed set and the assigned opposite-mode pair. (`Breakdown.CellCert.FinalCellSystem.cellDataRows_of`)

**Recover the spectral data.** The row-block interface, cell-system condition and row orthonormality imply the system's spectral-data condition. (`Breakdown.CellCert.FinalCellSystem.spectral_of_system`)

**Convert a system cell into an entry.** The definition packages one system cell's box, bounds, bases, classes, rows and mesh coordinates as an entry for the final chain. (`Breakdown.CellCert.FinalCellSystem.chainEntry`)

**Recover the cell-entry facts.** The cell-of-system statement and the cell-system condition give each converted entry valid cell data and coordinates at exponent 501/500, almost-everywhere agreement between its solid and split cell, and equivalence of row assignment with row-set membership. (`Breakdown.CellCert.FinalCellSystem.cellFacts_of_system`)

**Enclose the auxiliary support.** For valid chart and auxiliary data, a region containing the prescribed ball also contains every point below the auxiliary support threshold. (`Breakdown.CellCert.FinalCellSystem.supportRegionOf_holds`)

**The centre curl gradient has zero trace.** For valid profile data and a centre instance, the trace of the centre curl gradient vanishes at every point. (`Breakdown.CellCert.FinalCellSystem.centreTraceFreeOf_holds`)

**Angular row weights obey the bound.** For valid row-turn data and a second-order field, the weighted angular row coefficients are bounded by the row-turn constant squared times the gradient energy. (`Breakdown.CellCert.FinalCellSystem.rowModeGradient_holds`)

**Polynomial row traces.** For compatible mesh, row and pressure-layout data with the required degree bound, each row-mode component on a side is represented by the prescribed finite polynomial basis. (`Breakdown.CellCert.FinalCellSystem.rowTracesOf_holds`)

**Polynomial normal row traces.** For valid mesh and row data, a matching cell-row instance and a pressure layout of sufficient side degree, the radial and vertical normal row-mode traces have the prescribed lower-degree polynomial expansions. (`Breakdown.CellCert.FinalCellSystem.rowNormalTracesOf_holds`)

**Each row belongs to its block.** For valid mesh, row data and a row instance, every row is a field of its assigned spectral block. (`Breakdown.CellCert.FinalCellSystem.rowsInBlockOf_holds`)

**The rotation rate is continuous.** For valid profile data and a profile instance, the rotation rate is continuous on the parameter box. (`Breakdown.CellCert.FinalCellSystem.rotationRateContinuousOf_holds`)

**The multiplier is continuous.** For valid profile data and a profile instance, the multiplier is continuous on the parameter box. (`Breakdown.CellCert.FinalCellSystem.multiplierContinuousOf_holds`)

**Continuously differentiable profiles.** For valid profile data and a profile instance, every profile in the parameter box is continuously differentiable. (`Breakdown.CellCert.FinalCellSystem.profileSmoothOf_holds`)

**The profile second derivative is valid.** For valid profile data and a profile instance, the supplied profile second derivative is a weak second derivative and is strongly measurable almost everywhere. (`Breakdown.CellCert.FinalCellSystem.profileSecondOf_holds`)

**The profiles have zero divergence.** For valid profile data and a profile instance, every profile in the parameter box has zero divergence at every point. (`Breakdown.CellCert.FinalCellSystem.profileDivergenceOf_holds`)

**The profiles have the required symmetry.** For valid profile data and a profile instance, each profile in the parameter box belongs to the specified symmetry class. (`Breakdown.CellCert.FinalCellSystem.profileClassOf_holds`)

**Continuously differentiable centre.** For valid profile data and a centre instance, the centre field is continuously differentiable. (`Breakdown.CellCert.FinalCellSystem.centreSmoothOf_holds`)

**The centre second derivative is valid.** For valid profile data and a centre instance, the stored second derivative is a weak second derivative of the centre gradient and is strongly measurable almost everywhere. (`Breakdown.CellCert.FinalCellSystem.centreSecondOf_holds`)

**The centre has zero divergence.** For valid profile data and a centre instance, the centre field has zero divergence everywhere. (`Breakdown.CellCert.FinalCellSystem.centreDivergenceOf_holds`)

**The centre has the required symmetry.** For valid profile data and a centre instance, the centre field belongs to the required symmetry class. (`Breakdown.CellCert.FinalCellSystem.centreClassOf_holds`)

**The centre has a symmetric Hessian.** For valid profile data and a centre instance, the centre second derivative is symmetric in its two directional arguments. (`Breakdown.CellCert.FinalCellSystem.centreSecondSymmOf_holds`)

**The actuator fields have the right class.** For valid chart and auxiliary data identified with the certificate actuators and order, every actuator is square integrable and belongs to the required symmetry class. (`Breakdown.CellCert.FinalCellSystem.actuatorOfGiven_holds`)

**The actuator gradients are valid.** For valid chart and auxiliary data, every actuator's classical derivative is its weak gradient, is strongly measurable almost everywhere and has integrable squared matrix norm. (`Breakdown.CellCert.FinalCellSystem.actuatorGradientOfGiven_holds`)

**The actuator fields have bounded support.** For valid chart and auxiliary data, each actuator vanishes outside any region containing the points below the auxiliary support threshold. (`Breakdown.CellCert.FinalCellSystem.actuatorSupportOfGiven_holds`)

**The smooth pin data satisfy the bounds.** For valid chart and auxiliary data, each smooth pin is square integrable and its potential is C1 with compact support and a measurable, almost-everywhere bounded weak second derivative. (`Breakdown.CellCert.FinalCellSystem.smoothPinOfGiven_holds`)

**The adjoint fields have the right class.** For valid chart and auxiliary data identified with the certificate fields, the active adjoints are solenoidal L2 fields in the required symmetry class, and their sharp fields are square integrable. (`Breakdown.CellCert.FinalCellSystem.adjointSolenoidalOfGiven_holds`)

**Regularity of the adjoint fields.** For valid chart and auxiliary data, each adjoint and its first two classical derivatives satisfy the adjoint-regularity predicate. (`Breakdown.CellCert.FinalCellSystem.adjointRegularOfGiven_holds`)

**The cell region satisfies its clauses.** A cell region equal to that of a valid mesh is measurable, bounded and closed under the required rotation step and reflection. (`Breakdown.CellCert.FinalCellSystem.cellRegionClauses_holds`)

**The model fields satisfy their clauses.** Valid mesh, model and centre data give the model fields their measurability, bounds, exterior values, strain symmetry and zero curl-gradient trace. (`Breakdown.CellCert.FinalCellSystem.modelClauses_holds`)

**The auxiliary models satisfy the clauses.** Valid mesh and model instances give the model actuators, actuator gradients, model pin fields and pins their square-integrability and exterior-vanishing properties. (`Breakdown.CellCert.FinalCellSystem.modelAuxClauses_holds`)

**The rows satisfy their clauses.** For valid mesh and row instances of positive symmetry order, the rows satisfy square integrability, orthonormality, compact-support bounds, symmetry, positive bounded weights and the weighted projection estimate. (`Breakdown.CellCert.FinalCellSystem.rowClauses_holds`)

**A positive constant weight is valid.** A positive constant weight with matching lower and upper bounds satisfies the weight measurability, bounds, symmetry and cylindrical-sampling clauses. (`Breakdown.CellCert.FinalCellSystem.weightClauses_holds`)

**The exterior radius is valid.** For a valid mesh and the prescribed box radius and radius bounds, the exterior radius is measurable, positive and homogeneous, and describes the cell-region complement almost everywhere. (`Breakdown.CellCert.FinalCellSystem.exteriorClauses_holds`)

**The outer ball lies in the mesh region.** The region of a valid mesh contains the closed ball whose radius is the mesh's outer size. (`Breakdown.CellCert.FinalCellSystem.ballSubsetRegion_holds`)

**Cell sums imply a kernel bound.** Valid cell-sum data whose individual box bounds are all at most a common constant imply the corresponding kernel bound. (`Breakdown.CellCert.FinalCellSystem.kernelBoundOfCellSums_holds`)

**The row-turn data are valid.** Valid given data and row-turn numbers produce valid row-turn data at the selected rate. (`Breakdown.CellCert.FinalCellSystem.rowTurnDataOf_holds`)

**The adjoint kernel bound holds.** A cell-system condition implies the required kernel bound for each active adjoint weight throughout the parameter box. (`Breakdown.CellCert.FinalCellSystem.adjointKernelOf_holds`)

**The canonical mesh moments are linear.** For 1 < α < 5/4, valid form and mesh data make the canonical moment map preserve zero, addition and real scaling on admissible fields, and recover the actuator coefficients in their designated slots. (`Breakdown.CellCert.FinalCellSystem.meshMomentLinear_holds`)

**The dual data imply the local bound.** In the permitted exponent range, the stated weight, profile, inverse-square and adjoint-dual hypotheses imply the local adjoint estimate for second-order fields with the required fractional power and square-integrable drift. (`Breakdown.CellCert.FinalCellSystem.adjointLocalOfDual_holds`)

**The system supplies valid form data.** The proposition asks every cell-system condition to imply valid form data at exponent 501/500. (`Breakdown.CellCert.FinalCellSystem.FormDataOfSystemStatement`)

No theorem in the library states this proposition as its result.

**Each system cell has valid scalars.** A cell-system condition implies the cell-scalar conditions at exponent 501/500 for each cell of its split. (`Breakdown.CellCert.FinalCellSystem.CellDataFarInternal.scalars_of_system`)

**Each system cell has valid bases.** A cell-system condition implies valid polynomial bases for every cell of its split. (`Breakdown.CellCert.FinalCellSystem.CellDataFarInternal.bases_of_system`)

**Each system cell lies in the region.** A cell-system condition places the solid box of every split cell inside the cell region. (`Breakdown.CellCert.FinalCellSystem.CellDataFarInternal.solid_of_system`)

**Build the far-field cell data.** The form-data and centre smoothness, second-derivative and symmetry statements give every cell of a valid system harmonic-class coverage of nonzero resolved-to-unresolved interactions, the finite far-form bound and the multiplier-matrix bound at exponent 501/500. (`Breakdown.CellCert.FinalCellSystem.cellDataFar_of_form`)

**The low row gradients are polynomial.** The proposition requires each rescaled row-mode gradient to agree inside its cell with a polynomial in the high-degree space, assuming valid row instances, positive symmetry order and the stated degree gap. (`Breakdown.CellCert.FinalCellSystem.RowLowGradientOfStatement`)

Proved by `Breakdown.CellCert.FinalCellSystem.rowLowGradientOf_holds`.

**The rows are locally solenoidal.** The proposition requires every row of a valid mesh and row instance to have zero derivative trace on the solid box of its assigned cell. (`Breakdown.CellCert.FinalCellSystem.RowSolenoidalOfStatement`)

Proved by `Breakdown.CellCert.FinalCellSystem.rowSolenoidalOf_holds`.

**Recover the row-shape conditions.** The low row-gradient and row-solenoidality interfaces, together with a cell-system condition, imply the row-shape condition for each split cell. (`_private.Breakdown.FracCell.FinalChain.0.Breakdown.CellCert.FinalCellSystem.cellRowShape`)

**Build the remaining coordinate data.** The skeleton-slot, form-data, low row-gradient and row-solenoidality statements give every cell of a valid system positive viscosity, valid row shape and gauge data, linear shifts with correct jumps and zero roots, and the skeleton coordinate identity. (`Breakdown.CellCert.FinalCellSystem.cellCoordsRest_of`)

**Skeleton coordinates match moments.** For 1 < α < 5/4 and valid form and mesh data, applying each cell’s skeleton coordinate matrix to the canonical moments of an admissible input gives its local coordinate values. (`Breakdown.CellCert.FinalCellSystem.meshSkeletonSlot_holds`)

**Polynomial rescaled row gradients.** The theorem proves the polynomial representation of rescaled row-mode gradients under the interface's mesh, row, positive-order and degree-gap assumptions. (`Breakdown.CellCert.FinalCellSystem.rowLowGradientOf_holds`)

**Zero divergence inside row cells.** The theorem proves that valid row instances have zero derivative trace on the solid box of each row's assigned cell. (`Breakdown.CellCert.FinalCellSystem.rowSolenoidalOf_holds`)

**The system rows are polynomial.** A cell-system condition implies the required polynomial-row condition, with the stored degree bound, on every split cell. (`Breakdown.CellCert.FinalCellSystem.rowPolynomialOfSystem_holds`)

**The profiles have uniform decay bounds.** For valid profile data and a profile instance, a common constant bounds the profile and its first two derivatives by inverse first, second and third powers of one plus distance, with the second-derivative bound almost everywhere. (`Breakdown.CellCert.FinalCellSystem.profileBoundsOf_holds`)

**The profile drift is square integrable.** For valid profile data and a profile instance with matching exponent, the drift of every profile in the parameter box is square integrable. (`Breakdown.CellCert.FinalCellSystem.profileDriftOf_holds`)

**The profile fractional power is valid.** For valid profile data and a profile instance with matching exponent, the stored profile power is its weak fractional power throughout the parameter box. (`Breakdown.CellCert.FinalCellSystem.profilePowerOf_holds`)

**The profile gradients vary continuously.** For valid profile data and a profile instance, profile gradients vary continuously over the parameter box in their integrated squared difference. (`Breakdown.CellCert.FinalCellSystem.profileContinuousOf_holds`)

**The centre has uniform decay bounds.** For valid profile data and a centre instance, a common constant bounds the centre and its first two derivatives by inverse first, second and third powers of one plus distance. (`Breakdown.CellCert.FinalCellSystem.centreBoundsOf_holds`)

**The required sums have valid weights.** Under the given-data, positive-weight and amplitude-index assumptions, the specified curl errors, amplitude and higher-profile gradient squares, phase-curvature gradient squares and active adjoint coefficient-field squares divided by the weight satisfy the sum-weight conditions. (`Breakdown.CellCert.FinalCellSystem.sumWeightsOf_holds`)

**The centre difference has a kernel bound.** A cell-system condition bounds the squared difference between each profile gradient and the centre gradient by the stored centre kernel constant squared in the kernel-bound sense. (`Breakdown.CellCert.FinalCellSystem.centreKernelSplitOf_holds`)

**The adjoint dual core is valid.** For valid chart and auxiliary data, the adjoint and sharp fields have the stated weak gradients, measurability and square-integrability properties, and their viscous combination has the required weighted weak negative trace. (`Breakdown.CellCert.FinalCellSystem.adjointDualCoreOfGiven_holds`)

**The adjoint dual structure is valid.** Given valid data at exponent 501/500 and the required amplitude indices, the constructed adjoint dual satisfies the structural conditions for every adjoint index and parameter. (`Breakdown.CellCert.FinalCellSystem.adjointDualStructureOf_holds`)

### Breakdown.FracCell.FiniteDefs

This file states the finite-dimensional quadratic bound used to compare a state and its auxiliary coordinates with an energy.

**A quadratic bound for an extended state.** The predicate requires the block quadratic form at the shifted state and every auxiliary vector to be bounded above by the state's given energy. (`Breakdown.CellCert.Finite.IsStateBound`)

### Breakdown.FracCell.FormNonneg

This file converts a valid tree certificate into nonnegativity of the analytic quadratic form, using the cell split and linearity of admissible fields and their moments.

**The space of admissible fields.** Given the admissible-linearity interface, the definition makes the admissible field tuples into a real submodule. (`Breakdown.CellCert.Assembly.FormNonnegInternal.admissibleSpace`)

**The linear moment map.** A valid cell split makes its moment map a real linear map from the admissible submodule to the finite coordinate space. (`Breakdown.CellCert.Assembly.FormNonnegInternal.momentMap`)

**A zero coordinate vector is zero.** A Euclidean coordinate vector with zero entry is the zero vector. (`Breakdown.CellCert.Assembly.FormNonnegInternal.single_zero'`)

**The model field vanishes at zero.** Putting zero into every field, derivative and coefficient argument makes the model field, with zero added forcing, identically zero. (`Breakdown.CellCert.Assembly.FormNonnegInternal.modelField_zero`)

**The zero-field quadratic form bound.** The quadratic form evaluated on zero fields and zero coefficients is at most zero. (`Breakdown.CellCert.Assembly.FormNonnegInternal.quadForm_zero`)

**A tree certificate gives nonnegativity.** In the permitted exponent range, the splitting and admissible-linearity interfaces and a compatible tree certificate imply nonnegativity of the quadratic form for second-order fields and symmetry-compatible gradient forcing. (`Breakdown.CellCert.Assembly.formNonneg_of_tree_of`)

### Breakdown.FracCell.FormulaDataDefs

This file defines the face data and gauge-shift conditions used to encode an admissible field as finite cell coordinates. It states the interfaces that identify coefficients, impose relations and remove redundant pressure data.

**The moment on a radial face.** The definition chooses the radial strip moment on the inner or outer radial face, with the opposite radial endpoint as its reference. (`Breakdown.CellCert.CellFormula.radialFaceMoment`)

**The moment on a horizontal face.** The definition chooses the height strip moment on the lower or upper face, using radial weight equal to the radius. (`Breakdown.CellCert.CellFormula.heightFaceMoment`)

**Low entries recover the coefficients.** The proposition requires every designated low entry of a valid cell layout to equal the corresponding low coefficient of an admissible field. (`Breakdown.CellCert.CellFormula.LowEntryStatement`)

Proved by `Breakdown.CellCert.CellFormula.lowEntry_holds`.

**Gradient fields have potentials.** The proposition asks each gradient field to admit a potential satisfying the supplied potential predicate. (`Breakdown.CellCert.CellFormula.AdmissiblePotentialStatement`)

No theorem in the library states this proposition as its result.

**Face data ignore the opposite endpoint.** The proposition requires velocity, normal-derivative and pressure moments to agree for valid segments with identical face geometry and test coefficients, under the stated non-axis and radial nonnegativity assumptions. (`Breakdown.CellCert.CellFormula.SegmentIndependenceStatement`)

Proved by `Breakdown.CellCert.CellFormula.segmentIndependence_holds`.

**Corner data ignore the opposite edges.** The proposition requires an admissible field's corner moment away from the axis to be independent of the opposite radial and height endpoints, subject to nondegeneracy and radial nonnegativity. (`Breakdown.CellCert.CellFormula.CornerIndependenceStatement`)

Proved by `Breakdown.CellCert.CellFormula.cornerIndependence_holds`.

**The true data satisfy the relations.** The proposition requires every relation row of a valid cell layout to have zero pairing with the true data of an admissible field. (`Breakdown.CellCert.CellFormula.RelationsHoldStatement`)

Proved from further statements by `Breakdown.CellCert.CellFormula.relationsHold_of_leaves`, `Breakdown.CellCert.CellFormula.relationsHold_of_modes`, `Breakdown.CellCert.CellFormula.relationsHold_of_core`, `Breakdown.CellCert.CellFormula.relationsHold_of`.

**Parametrization fixes the true data.** The proposition requires a valid cell parametrization to reproduce the true data of every admissible field. (`Breakdown.CellCert.CellFormula.TrueParamStatement`)

Proved from further statements by `Breakdown.CellCert.CellFormula.trueParam_of`.

**The strain value on a face.** The definition takes the appropriate radial or height face moment of a gradient-mode component using the matching second derivative and one-dimensional basis polynomial. (`Breakdown.CellCert.CellFormula.CellLayout.strainFaceValue`)

**The strain face rows represent values.** The proposition requires the strain face value to equal its finite row applied to true data, under the layout, degree and non-axis conditions. (`Breakdown.CellCert.CellFormula.StrainFaceStatement`)

Proved by `Breakdown.CellCert.CellFormula.strainFace_holds`. Also proved from further statements by `Breakdown.CellCert.CellFormula.strainFace_of_leaves`, `Breakdown.CellCert.CellFormula.strainFace_of_core`, `Breakdown.CellCert.CellFormula.strainFace_of_remaining`, `Breakdown.CellCert.CellFormula.strainFace_of_trace`, `Breakdown.CellCert.CellFormula.strainFace_of`, `Breakdown.CellCert.CellFormula.strainFace_of_traces`, `_private.Breakdown.FracCell.StrainFaceGuarded.0.Breakdown.CellCert.CellFormula.strainFace_guarded`, `Breakdown.CellCert.CellFormula.strainFace_of_axis`.

**Conjugate data have conjugate values.** The proposition requires a valid pressure layout's conjugate datum to evaluate to the complex conjugate of the original true datum. (`Breakdown.CellCert.CellFormula.ConjugateDataStatement`)

Proved by `Breakdown.CellCert.CellFormula.conjugateData_holds`.

**The deleted plane data vanish.** The proposition requires every plane-deleted datum of an admissible field in a valid pressure layout to vanish. (`Breakdown.CellCert.CellFormula.PlaneDeletedStatement`)

Proved from further statements by `Breakdown.CellCert.CellFormula.Internal.PlaneDeleted.planeDeleted_of_mirror`, `Breakdown.CellCert.CellFormula.planeDeleted_of`.

**A valid pressure gauge shift.** The proposition requires the endpoint and pointwise shifts to be real linear on admissible fields and to agree at the specified radial endpoints, with the inner endpoint condition excluded on the axis. (`Breakdown.CellCert.CellFormula.IsGaugeShift`)

**Shift a pressure root datum.** The definition adds the left and right gauge contributions to a pressure datum using its two stored shift coefficients. (`Breakdown.CellCert.CellFormula.CellLayout.rootShifted`)

**Construct a valid gauge shift.** The proposition asks linear endpoint shifts satisfying the gauge jump and root equations to produce a valid gauge shift whose gauge-deleted data vanish on admissible fields. (`Breakdown.CellCert.CellFormula.GaugeShiftOfStatement`)

Proved by `Breakdown.CellCert.CellFormula.gaugeShiftOf_holds`. Also proved from further statements by `Breakdown.CellCert.CellFormula.gaugeShiftOf_of`.

**Reduce the shifted data to real entries.** The proposition requires the expansion map to recover the real part of valid shifted data once the gauge-deleted entries vanish. (`Breakdown.CellCert.CellFormula.ShiftedRealReductionStatement`)

Proved from further statements by `Breakdown.CellCert.CellFormula.shiftedRealReduction_of_plane`, `Breakdown.CellCert.CellFormula.shiftedRealReduction_of_leaves`, `Breakdown.CellCert.CellFormula.shiftedRealReduction_of`.

**Parametrization fixes shifted data.** The proposition requires a valid cell parametrization to preserve the shifted data of every admissible field for every gauge-shift datum. (`Breakdown.CellCert.CellFormula.ShiftedParamStatement`)

Proved from further statements by `Breakdown.CellCert.CellFormula.shiftedParam_of`, `Breakdown.CellCert.CellFormula.shiftedParam_of_relations`, `Breakdown.CellCert.CellFormula.shiftedParam_of_modes`, `Breakdown.CellCert.CellFormula.shiftedParam_of_core`, `Breakdown.CellCert.CellFormula.shiftedParam_of_recover`.

### Breakdown.FracCell.FormulaDefs

This file specifies how analytic cell quantities are represented by finite matrices and row vectors. It packages the regularity, polynomial, trace and gauge conditions needed for canonical formula inputs.

**The augmented coefficient vector.** The definition combines low field coefficients with the real coefficient and pin vectors, embedding the latter two into complex coordinates. (`Breakdown.CellCert.CellFormula.augVector`)

**The near term has a matrix formula.** The proposition requires the near weighted cell term to equal the near matrix evaluated on the augmented coefficients, for valid form and cell data in the permitted exponent range. (`Breakdown.CellCert.CellFormula.NearIdentityStatement`)

Proved from further statements by `Breakdown.CellCert.CellFormula.nearIdentity_of`.

**The row pairing has a vector formula.** The proposition requires each selected row's pairing with the auxiliary field to equal the real part of its finite row vector applied to augmented coefficients, under the form and cell hypotheses. (`Breakdown.CellCert.CellFormula.RowYIdentityStatement`)

Proved from further statements by `Breakdown.CellCert.CellFormula.rowYIdentity_of`.

**The far term has a matrix formula.** The proposition requires the far form to equal the far matrix on augmented coefficients whenever the far support lies within the low support. (`Breakdown.CellCert.CellFormula.FarIdentityStatement`)

Proved by `Breakdown.CellCert.CellFormula.farIdentity`.

**Evaluate a row from the layout data.** The definition adds the real part of the complex layout-row pairing to the real coefficient-vector contribution. (`Breakdown.CellCert.CellFormula.layoutRowValue`)

**The row-shape assumptions.** The proposition packages row regularity away from the axis, reflection, zero divergence, symmetry and the polynomial representations of rescaled velocity, position, turning and gradient modes. (`Breakdown.CellCert.CellFormula.IsRowShape`)

**The layout computes the low row value.** The proposition requires the low row value to equal its layout-data expression under the form, cell, row-shape, pressure-layout and polynomial trace assumptions. (`Breakdown.CellCert.CellFormula.LayoutRowValueStatement`)

Proved by `Breakdown.CellCert.CellFormula.layoutRowValue_holds`. Also proved from further statements by `Breakdown.CellCert.CellFormula.layoutRowValue_of_strainFace`.

**Gauge shifts preserve row values.** The proposition requires valid pressure gauge shifts to preserve every selected layout row value under the form, cell, row-shape and normal-trace assumptions. (`Breakdown.CellCert.CellFormula.GaugeInvarianceStatement`)

Proved by `Breakdown.CellCert.CellFormula.gaugeInvariance_holds`.

**Coordinates for the formula matrix.** The definition combines skeleton and interior coordinates with the coefficient and pin vectors divided by the supplied viscosity. (`Breakdown.CellCert.CellFormula.CellFormulaInputs.coordsOf`)

**The formula inputs are valid.** The proposition requires linear data reconstruction, agreement with true data and low coefficients, correct row values and a local matrix form bounded by the analytic local cell form. (`Breakdown.CellCert.CellFormula.IsFormulaInputs`)

**The canonical formula inputs are valid.** The proposition requires canonical inputs to satisfy the formula-input conditions under the form, cell, row-shape, pressure-layout, parametrization, gauge and polynomial trace hypotheses. (`Breakdown.CellCert.CellFormula.CanonicalInputsValidStatement`)

Proved from further statements by `Breakdown.CellCert.CellFormula.canonicalInputsValid_of`, `Breakdown.CellCert.CellFormula.canonicalInputsValid_of_open`.

### Breakdown.FracCell.FormulaFar

This file proves the far-form matrix identity by embedding its finite support into the augmented coefficient space.

**Entries of the far matrix.** A far-matrix entry equals the far kernel at the embedded indices when both lie in the selected support, and equals zero otherwise. (`Breakdown.CellCert.CellFormula.FormulaFarInternal.farMatrix_eq`)

**Sum over the embedded far support.** When the far support lies in the low support, summing supported values over augmented indices equals summing directly over the far support and the two coefficient blocks. (`Breakdown.CellCert.CellFormula.FormulaFarInternal.sum_aug`)

**The far matrix represents the far form.** The theorem proves the far-form matrix identity under the interface's support-containment assumption. (`Breakdown.CellCert.CellFormula.farIdentity`)

### Breakdown.FracCell.FormulaModeRestriction

This file removes unused angular modes from the near matrix and transfers matrix inequalities between equivalent row descriptions. It verifies the required vanishing from finite-mode piecewise models.

**The zero vector has zero rank-one matrix.** The rank-one matrix built from the zero vector is zero. (`Breakdown.CellCert.CellSystem.rankOne_zero_vec`)

**Remove vanishing modes from the matrix.** Restricting the auxiliary modes preserves the near matrix when the retained set contains the resolved and band modes and both relevant coefficient vectors vanish on discarded modes. (`Breakdown.CellCert.CellSystem.nearMatrix_yModes`)

**Equivalent rows give the same formula.** Changing the auxiliary modes and far support or kernel preserves the exact formula when it preserves both the near and far matrices. (`Breakdown.CellCert.CellSystem.exactFormula_systemRows`)

**Transfer the reduced formula bound.** A bound by the exact formula for modified row data transfers to the original row data when the near and far matrices agree. (`Breakdown.CellCert.CellSystem.givenLeExact_of_systemRows`)

**The turning inverse preserves zero.** The adjoint turning inverse sends the zero vector to zero. (`Breakdown.CellCert.CellSystem.turnAdjInv_zero_vec`)

**The folded field vanishes off the band.** Outside the resolved and band modes, the folded field vanishes when all model actuator-gradient and pin modes at that point vanish. (`Breakdown.CellCert.CellSystem.yFoldedOf_eq_zero_of_off_band`)

**Axis support gives zero coefficients.** A function that vanishes whenever its radial coordinate is nonzero has every cell polynomial coefficient equal to zero. (`Breakdown.CellCert.CellSystem.coef_eq_zero_off_axis`)

**The off-band coefficient vectors vanish.** Outside the resolved and band modes, vanishing model actuator-gradient and pin modes away from the axis imply zero symmetric and antisymmetric coefficient vectors. (`Breakdown.CellCert.CellSystem.symVec_antiVec_eq_zero_of_off_band`)

**Piecewise models have finite modes.** For positive symmetry order, piecewise polynomial tensor models have zero modes at frequencies outside both signs of their finite angular index set, away from the axis. (`Breakdown.CellCert.CellSystem.modelModes_zero_of_piecewise`)

**Model vanishing permits mode restriction.** Restricting auxiliary modes preserves the near matrix when the retained set contains resolved and band modes and the model actuator-gradient and pin modes vanish off the axis for every discarded mode. (`Breakdown.CellCert.CellSystem.nearMatrix_yModes_of_model`)

### Breakdown.FracCell.FormulaNear

This file proves the near-form matrix identity by substituting finite synthesis formulas and distributing quadratic evaluation over the matrix construction.

**Substitute the low strain data.** Replacing the resolved low strain and velocity by equal supplied functions, and the real parameters by equal complex embeddings, preserves the auxiliary strain expression. (`Breakdown.CellCert.CellFormula.FormulaNear.Internal.yStrain_eq_of`)

**Substitute the low velocity data.** Replacing the resolved low strain and velocity by equal supplied functions preserves the auxiliary velocity expression. (`Breakdown.CellCert.CellFormula.FormulaNear.Internal.yVelocity_eq_of`)

**Substitute the folded field data.** Replacing the resolved low strain, velocity and embedded real parameters by equal supplied data preserves the folded auxiliary field. (`Breakdown.CellCert.CellFormula.FormulaNear.Internal.yFolded_eq_of`)

**Equal functions have equal coefficients.** Functions that agree on the cell rectangle have equal cell polynomial coefficients. (`Breakdown.CellCert.CellFormula.FormulaNear.Internal.coef_congr`)

**Quadratic evaluation is additive.** For a fixed complex vector, the definition makes real quadratic evaluation an additive map from complex matrices to the reals. (`Breakdown.CellCert.CellFormula.FormulaNear.Internal.quadHom`)

**Evaluate a sum of two matrices.** Quadratic evaluation of a sum of two matrices equals the sum of their quadratic evaluations. (`Breakdown.CellCert.CellFormula.FormulaNear.Internal.quad_add`)

**Evaluate a finite sum of matrices.** Quadratic evaluation commutes with finite sums of matrices. (`Breakdown.CellCert.CellFormula.FormulaNear.Internal.quad_sum`)

**Evaluate a conditional matrix.** Quadratic evaluation of a matrix selected conditionally against zero equals the correspondingly selected scalar value. (`Breakdown.CellCert.CellFormula.FormulaNear.Internal.quad_ite`)

**Scale a matrix by a real number.** Multiplying a complex matrix by a real scalar multiplies its real quadratic value by that scalar. (`Breakdown.CellCert.CellFormula.FormulaNear.Internal.quad_smul`)

**Evaluate a rank-one matrix.** The quadratic value of a rank-one matrix equals the squared norm of its defining finite linear pairing. (`Breakdown.CellCert.CellFormula.FormulaNear.Internal.quad_rankOne`)

**The near matrix identity follows.** The synthesis and coefficient-linearity interfaces imply the near weighted term's matrix representation. (`Breakdown.CellCert.CellFormula.nearIdentity_of`)

### Breakdown.FracCell.FormulaPolar

This file proves that polarization recovers the symmetric matrix representation of a real quadratic function.

**Transpose preserves a quadratic value.** A real matrix and its transpose have equal quadratic values on every vector. (`Breakdown.CellCert.CellFormula.FormulaPolar.quad_transpose`)

**Polarization symmetrizes the matrix.** If a function is represented by a real matrix, its polarized matrix is one half of the sum of that matrix and its transpose. (`Breakdown.CellCert.CellFormula.FormulaPolar.polarized_eq`)

**Polarization recovers a quadratic form.** The theorem proves that evaluating the polarized matrix of a real quadratic function recovers the function. (`Breakdown.CellCert.CellFormula.polarization`)

### Breakdown.FracCell.FormulaQuadratic

This file proves that the assembled cell formula is a real quadratic function of its finite coordinates, using linear data reconstruction and elementary closure properties.

**Adding quadratic functions.** The sum of two real quadratic functions is real quadratic. (`Breakdown.CellCert.CellFormula.FormulaQuadraticInternal.quad_add`)

**Scaling preserves quadratic functions.** Multiplication by any real scalar preserves the real-quadratic property. (`Breakdown.CellCert.CellFormula.FormulaQuadraticInternal.quad_mul`)

**A difference of quadratics is quadratic.** The difference of two real quadratic functions is real quadratic. (`Breakdown.CellCert.CellFormula.FormulaQuadraticInternal.quad_sub`)

**Division preserves quadratic functions.** Dividing a real quadratic function by any real scalar preserves the real-quadratic property under Lean's total division convention. (`Breakdown.CellCert.CellFormula.FormulaQuadraticInternal.quad_div`)

**Finite sums of quadratics are quadratic.** A finite sum of real quadratic functions is real quadratic. (`Breakdown.CellCert.CellFormula.FormulaQuadraticInternal.quad_sum`)

**A bilinear diagonal is quadratic.** A function equal to a bilinear form evaluated twice on the same vector is real quadratic. (`Breakdown.CellCert.CellFormula.FormulaQuadraticInternal.quad_of_bilin`)

**A squared linear functional is quadratic.** The square of a real linear functional is a real quadratic function. (`Breakdown.CellCert.CellFormula.FormulaQuadraticInternal.quad_sq`)

**Linear substitution preserves the form.** Composing real quadratic evaluation of a complex matrix with a real linear coordinate map gives a real quadratic function. (`Breakdown.CellCert.CellFormula.FormulaQuadraticInternal.quad_form`)

**The real part of a complex pairing.** The definition packages the real part of a fixed finite complex pairing as a real linear functional. (`Breakdown.CellCert.CellFormula.FormulaQuadraticInternal.reLin`)

**A real finite pairing as a linear map.** The definition packages a fixed finite real pairing as a real linear functional. (`Breakdown.CellCert.CellFormula.FormulaQuadraticInternal.dotLin`)

**The linear reconstruction of data.** Given linearity of coordinate reconstruction, the definition extracts the skeleton and interior coordinates and reconstructs the complex data as a real linear map. (`Breakdown.CellCert.CellFormula.FormulaQuadraticInternal.dataMap`)

**Scale selected coordinates by viscosity.** The definition selects the designated coordinates and multiplies them by the split viscosity as a real linear map. (`Breakdown.CellCert.CellFormula.FormulaQuadraticInternal.scaledMap`)

**Combine data and two coefficient vectors.** The definition combines three real linear maps into the complex data vector with its two embedded real coefficient blocks. (`Breakdown.CellCert.CellFormula.FormulaQuadraticInternal.dataVecMap`)

**Build the augmented vector linearly.** The definition turns linear data and coefficient maps into the augmented low-coefficient vector as a real linear map. (`Breakdown.CellCert.CellFormula.FormulaQuadraticInternal.augMap`)

**The row residual is a linear map.** The definition subtracts the auxiliary row pairing from the data-row and coefficient contributions to form a real linear residual map. (`Breakdown.CellCert.CellFormula.FormulaQuadraticInternal.residualMap`)

**Evaluate the linear residual map.** The constructed linear residual map evaluates to the stated formula residual on the same data and coefficient vectors. (`Breakdown.CellCert.CellFormula.FormulaQuadraticInternal.residualMap_apply`)

**The finite formula is quadratic.** The theorem proves that the formula value is real quadratic whenever its coordinate-to-data reconstruction is real linear. (`Breakdown.CellCert.CellFormula.formulaQuadratic`)

### Breakdown.FracCell.FormulaRepresents

This file combines the near, row, far and polarization identities to compare the exact finite matrix with the analytic cell form.

**The exact matrix bounds the cell form.** In the permitted exponent range, the five named formula interfaces, valid form, cell and formula inputs, far-support containment and positive split viscosity imply that the exact matrix value on reconstructed coordinates is at most the cell form divided by that viscosity. (`Breakdown.CellCert.CellFormula.exactFormula_represents_of`)

### Breakdown.FracCell.FormulaRowY

This file proves the row pairing formula by synthesizing low modes and rearranging the finite coefficient sums.

**Synthesize the auxiliary strain.** When synthesis reproduces the resolved low strain and velocity, the auxiliary strain equals its expression in synthesized fields and the augmented coefficient vector. (`Breakdown.CellCert.CellFormula.FormulaRowY.yStrain_eq`)

**Synthesize the auxiliary velocity.** When synthesis reproduces the resolved low strain and velocity, the auxiliary velocity equals its expression in the synthesized fields. (`Breakdown.CellCert.CellFormula.FormulaRowY.yVelocity_eq`)

**Synthesize the folded auxiliary field.** When synthesis reproduces the resolved low strain and velocity, the folded auxiliary field equals its expression in synthesized fields and augmented coefficients. (`Breakdown.CellCert.CellFormula.FormulaRowY.yFolded_eq`)

**The cell rectangle is measurable.** The cell rectangle is a measurable subset of the radial-height plane. (`Breakdown.CellCert.CellFormula.FormulaRowY.rect_measurable`)

**Recover the folded field coefficients.** When synthesis agrees with the low fields on the rectangle, each folded-field coefficient equals the coefficient calculated from the augmented vector. (`Breakdown.CellCert.CellFormula.FormulaRowY.coef_yFolded`)

**Recover the velocity coefficients.** When synthesis agrees with the low fields on the rectangle, each auxiliary velocity coefficient equals its finite formula on the augmented vector. (`Breakdown.CellCert.CellFormula.FormulaRowY.coef_yVelocity`)

**Distribute the two row pairings.** The weighted symmetric and antisymmetric combinations of two finite pairings can be collected into one pairing with the shared input vector. (`Breakdown.CellCert.CellFormula.FormulaRowY.pair_term`)

**Exchange coordinate and component sums.** A finite coordinate pairing with a double component sum equals the component sums of the coordinate pairings. (`Breakdown.CellCert.CellFormula.FormulaRowY.swap_inner`)

**Exchange coordinate and mode sums.** A finite coordinate pairing with mode and polynomial sums equals the mode and polynomial sums of the coordinate pairings. (`Breakdown.CellCert.CellFormula.FormulaRowY.swap_outer`)

**Move a condition outside a pairing.** A finite pairing with a conditionally zero coefficient vector equals the conditionally zero pairing. (`Breakdown.CellCert.CellFormula.FormulaRowY.ite_sum`)

**The row pairing identity follows.** The synthesis and coefficient-linearity interfaces imply the auxiliary row pairing's finite vector formula. (`Breakdown.CellCert.CellFormula.rowYIdentity_of`)

### Breakdown.FracCell.FormulaSymm

This file records the symmetry of the exact real matrix produced by polarization.

**The exact formula matrix is symmetric.** The exact formula matrix is symmetric for every supplied set of cell formula inputs and row data. (`Breakdown.CellCert.CellFormula.exactFormula_symm`)

### Breakdown.FracCell.FormulaSynthesis

This file reconstructs low polynomial fields from their orthogonal coefficients and proves the synthesis interface used by the near and row matrix identities.

**A triangular family spans monomials.** Polynomials with nonzero leading coefficients span every monomial up to the selected degree through a finite real linear combination. (`Breakdown.CellCert.CellFormula.FormulaSynthesis.Internal.mono_span`)

**The radial basis is continuous.** Every stored radial basis polynomial is continuous. (`Breakdown.CellCert.CellFormula.FormulaSynthesis.Internal.radialPoly_continuous`)

**The height basis is continuous.** Every stored height basis polynomial is continuous. (`Breakdown.CellCert.CellFormula.FormulaSynthesis.Internal.heightPoly_continuous`)

**The radial line weight is continuous.** The radial line-weight function of a cell box is continuous. (`Breakdown.CellCert.CellFormula.FormulaSynthesis.Internal.lineWeight_continuous`)

**The product basis is continuous.** Each product of a radial and height basis polynomial is continuous on the radial-height plane. (`Breakdown.CellCert.CellFormula.FormulaSynthesis.Internal.basisVal_continuous`)

**The cell rectangle is compact.** The rectangle associated with a cell box is compact. (`Breakdown.CellCert.CellFormula.FormulaSynthesis.Internal.rect_compact`)

**The product basis is orthonormal.** For valid cell bases, the weighted rectangle integral of two product-basis functions is one for matching indices and zero otherwise. (`Breakdown.CellCert.CellFormula.FormulaSynthesis.Internal.basis_orth`)

**Exchange two pairs of finite sums.** Four nested finite sums can be reordered by exchanging the first pair of indices with the second pair. (`Breakdown.CellCert.CellFormula.FormulaSynthesis.Internal.sum_swap4`)

**Expand a polynomial in the cell basis.** For valid cell bases, every polynomial with both degrees bounded by the selected cutoff admits a finite expansion in the product basis up to that cutoff. (`Breakdown.CellCert.CellFormula.FormulaSynthesis.Internal.poly_expand`)

**Extract a finite expansion coefficient.** For valid cell bases, taking an in-range coefficient of a finite product-basis expansion recovers the corresponding expansion coefficient. (`Breakdown.CellCert.CellFormula.FormulaSynthesis.Internal.coef_comb`)

**Reconstruct a polynomial from its data.** For valid cell bases, a polynomial within the degree cutoff equals the product-basis expansion using its own coefficients. (`Breakdown.CellCert.CellFormula.FormulaSynthesis.Internal.expand`)

**Projection lies in the polynomial space.** The chosen cell projection belongs to the specified polynomial space for every input function. (`Breakdown.CellCert.CellFormula.FormulaSynthesis.Internal.proj_mem`)

**Collapse the strain synthesis sum.** At a resolved mode, the low-support sum of unit strain terms reduces to the double polynomial-basis sum for the selected strain component. (`Breakdown.CellCert.CellFormula.FormulaSynthesis.Internal.collapse_strain`)

**Collapse the velocity synthesis sum.** At a resolved mode, the low-support sum of unit velocity terms reduces to the double polynomial-basis sum for the selected velocity component. (`Breakdown.CellCert.CellFormula.FormulaSynthesis.Internal.collapse_velocity`)

**The low fields are synthesized exactly.** The theorem proves that valid form and cell bases reconstruct the low strain and velocity of an admissible field from its augmented coefficients throughout the cell rectangle. (`Breakdown.CellCert.CellFormula.synthesis`)

### Breakdown.FracCell.FormulaYLinear

This file proves that the cell output coefficients depend linearly on the augmented input, using bounded Fourier modes and integrability in cylindrical coordinates; it is reusable cell analysis for the Appendix B route and the fractional extension.

**Add two essentially bounded functions.** The sum of two essentially bounded complex functions is essentially bounded for the same measure. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.bd_add`)

**Subtract bounded functions.** The difference of two essentially bounded complex functions is essentially bounded for the same measure. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.bd_sub`)

**Negate an essentially bounded function.** Negating an essentially bounded complex function preserves essential boundedness. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.bd_neg`)

**Multiply bounded functions.** The product of two essentially bounded complex functions is essentially bounded for the same measure. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.bd_mul`)

**Constant functions are bounded.** Every constant complex function is essentially bounded for the given measure. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.bd_const`)

**Finite sums preserve boundedness.** A finite sum of essentially bounded complex functions is essentially bounded. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.bd_sum`)

**Conjugation preserves boundedness.** Complex conjugation preserves essential boundedness. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.bd_conj`)

**A conditional choice stays bounded.** Choosing between two essentially bounded functions by a fixed proposition preserves essential boundedness. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.bd_ite`)

**Bound components of a three-vector.** Each component of a three-vector assembled from essentially bounded scalar functions is essentially bounded. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.bd_vec3`)

**Bound the strain-velocity vector.** Componentwise essential bounds for the strain matrix and velocity imply essential bounds for their packed twelve-component vector. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.bd_pairVec`)

**Bound the strain wave action.** Componentwise essential bounds for the background matrices, strain and velocity imply essential bounds for the strain wave action. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.bd_wave`)

**Bound the velocity wave action.** Componentwise essential bounds for the curl-gradient matrix and strain imply essential bounds for the velocity wave action. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.bd_waveVel`)

**Bound the local matrix action.** Componentwise essential bounds for the local matrix, strain and velocity imply essential bounds for the local matrix action. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.bd_local`)

**Compact cell rectangle.** The cell rectangle is compact. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.rect_compact`)

**Measurable cell rectangle.** The cell rectangle is measurable. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.rect_meas`)

**Finite measure of the cell rectangle.** Volume restricted to the cell rectangle is a finite measure. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.rect_finite`)

**Bound continuous functions on cells.** Every continuous complex function is essentially bounded on the cell rectangle. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.bd_cont`)

**Bound the product polynomial basis.** Each product of a radial and a height basis polynomial is essentially bounded on the cell rectangle. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.bd_poly`)

**Bound the radial coordinate.** The radial coordinate is essentially bounded on the cell rectangle. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.bd_fst`)

**Bound the line weight.** The cell line weight is essentially bounded on the cell rectangle. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.bd_lw`)

**Bound the adjusted radius.** The adjusted radial factor is essentially bounded on the cell rectangle. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.bd_rHat`)

**Cancel the line weight.** Multiplying the line weight by the adjusted radial factor recovers the radial coordinate. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.lw_rHat`)

**Bound synthesized strain modes.** Every component of a strain mode synthesized from augmented coefficients is essentially bounded on the cell rectangle. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.bd_synthStrain`)

**Bound synthesized velocity modes.** Every component of a velocity mode synthesized from augmented coefficients is essentially bounded on the cell rectangle. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.bd_synthVelocity`)

**Bound the cell velocity output.** Essential bounds on the curl-gradient modes, input modes and relevant local matrix imply essential bounds on each cell velocity output component. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.bd_yVel`)

**Bound the unforced strain output.** Essential bounds on the strain and curl-gradient modes, input modes and relevant local matrix imply essential bounds on the strain output with zero actuator and pin coefficients. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.bd_yStrain0`)

**Separate actuator and pin strain terms.** The strain output splits into its zero-actuator, zero-pin part and the displayed adjusted-radius-weighted sum of actuator-gradient and pin modes. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.yStrain_split`)

**Separate actuator and pin folded terms.** The folded output splits into its zero-actuator, zero-pin part and the displayed adjusted-radius-weighted sum of actuator-gradient and pin modes. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.yFold_split`)

**Bound the unforced folded output.** The stated mode and local-matrix bounds make each folded output component with zero actuator and pin coefficients essentially bounded. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.bd_yFold0`)

**Integrate the weighted folded output.** The stated mode bounds, radial actuator and pin integrability, and bounded multiplier imply integrability of the line-weighted folded output times that multiplier. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.int_yFold`)

**Integrate the weighted velocity output.** The stated mode and local-matrix bounds and a bounded multiplier imply integrability of the line-weighted velocity output times that multiplier. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.int_yVel`)

**Packing preserves addition.** Packing the sum of two strain-velocity pairs equals the sum of their packed vectors. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.pairVec_add`)

**Packing preserves scalar multiplication.** Packing a scalar multiple of a strain-velocity pair equals that scalar times its packed vector. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.pairVec_smul`)

**Strain wave action preserves addition.** With fixed background matrices, the strain wave action preserves addition of strain-velocity inputs. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.wave_add`)

**Scale the strain wave input.** Scaling both strain and velocity scales the strain wave action by the same complex scalar. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.wave_smul`)

**Velocity wave action preserves addition.** With fixed curl-gradient matrix, the velocity wave action preserves addition of strains. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.waveVel_add`)

**Scale the velocity wave input.** Scaling the strain scales the velocity wave action by the same complex scalar. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.waveVel_smul`)

**Matrix action preserves addition.** Applying a fixed matrix to a vector sum equals the sum of its two actions. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.matAct_add`)

**Matrix action preserves scaling.** A fixed matrix action commutes with complex scalar multiplication. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.matAct_smul`)

**Extract strain from a sum.** Extracting strain from a sum of packed vectors equals the sum of their extracted strains. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.splitStrain_add`)

**Extract strain from a scalar multiple.** Extracting strain commutes with complex scalar multiplication. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.splitStrain_smul`)

**Extract velocity from a sum.** Extracting velocity from a sum of packed vectors equals the sum of their extracted velocities. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.splitVelocity_add`)

**Extract velocity from a scalar multiple.** Extracting velocity commutes with complex scalar multiplication. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.splitVelocity_smul`)

**Turn correction preserves addition.** The inverse adjoint-turn map preserves addition of vectors. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.turnAdjInv_add`)

**Turn correction preserves scaling.** The inverse adjoint-turn map commutes with complex scalar multiplication. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.turnAdjInv_smul`)

**Unforced strain output is additive.** With zero actuator and pin coefficients, the cell strain output preserves addition of strain-velocity inputs. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.yStrainOf_add`)

**Unforced strain output respects scaling.** With zero actuator and pin coefficients, scaling the strain-velocity input scales each strain output component by the same scalar. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.yStrainOf_smul`)

**Cell velocity output is additive.** The cell velocity output preserves addition of strain-velocity inputs. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.yVelocityOf_add`)

**Cell velocity output respects scaling.** Scaling the strain-velocity input scales the cell velocity output by the same scalar. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.yVelocityOf_smul`)

**Unforced folded output is additive.** With zero actuator and pin coefficients, the folded output preserves addition of strain-velocity inputs. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.yFold0_add`)

**Unforced folded output respects scaling.** With zero actuator and pin coefficients, scaling the strain-velocity input scales each folded output component by the same scalar. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.yFold0_smul`)

**Strain synthesis preserves addition.** Synthesizing strain from a sum of augmented coefficient vectors gives the sum of their synthesized strains. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.synthStrain_add`)

**Strain synthesis respects scaling.** Strain synthesis commutes with complex scalar multiplication of augmented coefficients. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.synthStrain_smul`)

**Velocity synthesis preserves addition.** Synthesizing velocity from a sum of augmented coefficient vectors gives the sum of their synthesized velocities. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.synthVelocity_add`)

**Velocity synthesis respects scaling.** Velocity synthesis commutes with complex scalar multiplication of augmented coefficients. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.synthVelocity_smul`)

**Coordinate sum for a linear functional.** An additive, complex-homogeneous functional on a finite coordinate space equals the sum of each coordinate times its value on the corresponding unit vector. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.lin_repr`)

**Expand folded output in coordinates.** The folded output synthesized from augmented coefficients equals the sum of those coefficients times the outputs for individual coordinate unit vectors. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.fold_linear`)

**Expand velocity output in coordinates.** The velocity output synthesized from augmented coefficients equals the sum of those coefficients times the outputs for individual coordinate unit vectors. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.vel_linear`)

**Regularity required of cell modes.** Mode regularity requires bounded strain and curl-gradient components and integrable radius-weighted actuator-gradient and pin components on the cell rectangle. (`Breakdown.CellCert.CellFormula.ModeRegularity`)

**Mode regularity from cell data.** For 1 < α < 5/4, admissible form data and cell data are required to imply the mode-regularity conditions. (`Breakdown.CellCert.CellFormula.ModeRegularityStatement`)

Proved by `Breakdown.CellCert.CellFormula.FormulaYLinearInternal.modeRegularity`.

**Linear coefficients from regular modes.** The mode-regularity statement expresses every matrix and velocity output coefficient as a fixed coefficient vector paired linearly with the augmented input coordinates when 1 < α < 5/4 and the form and cell data are valid. (`Breakdown.CellCert.CellFormula.yCoefLinear_of_modes`)

**Identify three real coordinates.** This measurable equivalence identifies a planar pair and a height with the three-dimensional Euclidean space. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.toSp`)

**Coordinate map preserves volume.** The measurable identification of three real coordinates with space preserves volume. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.toSp_mp`)

**Cylindrical point through identification.** Applying the coordinate identification to ((r cos θ, r sin θ), z) gives the cylindrical point at (r,θ,z). (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.toSp_apply`)

**Cylindrical coordinate chart.** The cylindrical chart is the product of the planar polar-coordinate partial homeomorphism and the identity on height. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.cylM`)

**Derivative of the inverse chart.** The candidate inverse cylindrical-chart derivative is the product of the inverse polar derivative and the identity on height. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.cylD`)

**Differentiate the inverse chart.** The inverse cylindrical chart has the stated product derivative at every point. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.cylD_has`)

**Cylindrical Jacobian determinant.** The determinant of the inverse cylindrical-chart derivative is the radial coordinate. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.cylD_det`)

**Inverse chart covers almost all space.** The image of the cylindrical chart target under its inverse agrees with the full coordinate space almost everywhere. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.cylM_image_ae`)

**Integrability after cylindrical change.** An integrable function remains integrable on the chart target after inverse cylindrical substitution and multiplication by the radial Jacobian. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.cyl_change`)

**Exchange height and angle coordinates.** This measurable equivalence swaps the second and third entries of the nested coordinate product. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.swapE`)

**Coordinate exchange preserves volume.** Exchanging height and angle coordinates preserves volume. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.swapE_mp`)

**Evaluate the coordinate exchange.** The coordinate exchange sends ((r,z),θ) to ((r,θ),z). (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.swapE_apply`)

**Domain after coordinate exchange.** Pulling the cylindrical chart target back through the coordinate exchange gives positive radius, arbitrary height and angle in (−π,π). (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.swapE_preimage`)

**Integrate over angular fibers.** For an integrable spatial function, its angular integral multiplied by radius is integrable over positive radius and arbitrary height. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.fiber_int`)

**Recover the planar angle.** The angle function is the complex argument of the first two spatial coordinates. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.angOf`)

**Lift a matrix mode to space.** The lifted matrix component multiplies its cylindrical-frame entry by the negative angular Fourier phase evaluated at the spatial angle. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.liftMat`)

**First coordinate of a cylindrical point.** The first coordinate of a cylindrical point is r cos θ. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.cyl0`)

**Second coordinate of a cylindrical point.** The second coordinate of a cylindrical point is r sin θ. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.cyl1`)

**Height of a cylindrical point.** The third coordinate of a cylindrical point is its height z. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.cyl2`)

**Recover angle inside the chart.** At positive radius and angle in (−π,π), the spatial angle of a cylindrical point equals the original angle. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.angOf_cyl`)

**Bound cylindrical frame vectors.** Every cylindrical frame vector has norm at most one. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.frame_norm`)

**Bound a cylindrical matrix entry.** The absolute value of a cylindrical-frame matrix entry is at most the operator norm of the matrix. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.frame_le`)

**Unit norm of an imaginary phase.** The complex exponential of minus a real number times the imaginary unit has norm one. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.exp_norm`)

**Bound a lifted matrix component.** The norm of a lifted Fourier matrix component is at most the pointwise operator norm of the original matrix field. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.liftMat_norm`)

**Continuous single-coordinate embedding.** Placing a real scalar in one fixed Euclidean coordinate is continuous. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.single_cont`)

**Continuous cylindrical frame.** Every cylindrical frame vector depends continuously on angle. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.frame_cont`)

**Continuous cylindrical matrix entry.** Each cylindrical-frame matrix entry depends continuously on the angle and the underlying linear operator. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.frameMat_cont`)

**Continuous spatial coordinate.** Each spatial coordinate projection is continuous. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.coord_cont`)

**Measurable spatial angle.** The planar angle of a spatial point is measurable. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.angOf_meas`)

**Continuous angular phase.** For a fixed frequency, the negative complex angular Fourier phase is continuous in angle and the accompanying matrix variable. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.phase_cont`)

**Continuous phased frame entry.** The product of the angular Fourier phase and a cylindrical-frame matrix entry is continuous in angle and matrix. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.liftFun_cont`)

**Measurable angle-field pair.** Pairing the spatial angle with an almost-everywhere strongly measurable matrix field preserves almost-everywhere strong measurability. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.pair_meas`)

**Measurable lifted matrix mode.** The lifted matrix mode of an almost-everywhere strongly measurable matrix field is almost-everywhere strongly measurable. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.liftMat_meas`)

**Periodic angular matrix integrand.** The matrix-mode angular integrand is periodic with period 2π. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.mode_periodic`)

**Matrix mode on a symmetric angular arc.** A matrix mode equals its angular Fourier integral over [−π,π], multiplied by 1/(2π). (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.modeMat_sym`)

**Express a mode through the spatial lift.** At positive radius, a matrix mode equals the angular integral of its lifted spatial component over [−π,π], multiplied by 1/(2π). (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.mode_fiber`)

**Discard the zero-radius part of a cell.** If the cell's lower radial endpoint is nonnegative, intersecting its rectangle with positive radius changes it only on a null set. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.rect_ae`)

**Integrable radius-weighted matrix mode.** An integrable spatial function agreeing with the lifted mode on the positive-radius cell implies integrability of the corresponding radius-weighted matrix mode. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.mode_int`)

**Control an operator by squared columns.** A three-dimensional operator norm is at most three plus the sum of the squared norms of its columns. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.norm_le_sq`)

**Integrable lifted actuator component.** A measurable matrix field supported in a bounded set with integrable squared column norms has integrable lifted Fourier components. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.act_int`)

**Points above the cell rectangle.** For a valid cell box, every angle over a point of its rectangle gives a point of its solid cell. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.cyl_solid`)

**Measurable solid cell.** The solid region determined by a cell box is measurable. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.solid_meas`)

**Bound modes of a bounded matrix field.** A measurable matrix field bounded on a finite-volume valid cell solid has essentially bounded matrix modes on the cell rectangle. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.bdd_mode`)

**Bounded and integrable cell modes.** For 1 < α < 5/4, valid form and cell data give essentially bounded strain and curl-gradient modes and integrable radius-weighted actuator-gradient and pin modes on the cell rectangle. (`Breakdown.CellCert.CellFormula.FormulaYLinearInternal.modeRegularity`)

**Linear formulas for cell coefficients.** For 1 < α < 5/4, valid form and cell data express every matrix and velocity output coefficient as its fixed coefficient vector paired linearly with the augmented input coordinates. (`Breakdown.CellCert.CellFormula.yCoefLinear`)

### Breakdown.FracCell.GaugeFluxParts

This file proves zero-mode cylindrical calculus and pressure-side flux cancellation used by the gauge-invariance step in the cell certificate analysis.

**First Cartesian unit vector.** This abbreviation selects the first Cartesian unit vector. (`Breakdown.CellCert.CellFormula.Internal.GaugeFluxParts.e₀`)

**Second Cartesian unit vector.** This abbreviation selects the second Cartesian unit vector. (`Breakdown.CellCert.CellFormula.Internal.GaugeFluxParts.e₁`)

**Third Cartesian unit vector.** This abbreviation selects the third Cartesian unit vector. (`Breakdown.CellCert.CellFormula.Internal.GaugeFluxParts.e₂`)

**Scale a Cartesian unit vector.** A vector with one coordinate a equals a times the corresponding unit vector. (`Breakdown.CellCert.CellFormula.Internal.GaugeFluxParts.single_eq'`)

**Cylindrical point in Cartesian basis.** A cylindrical point equals r cos θ times the first unit vector plus r sin θ times the second plus z times the third. (`Breakdown.CellCert.CellFormula.Internal.GaugeFluxParts.cyl_eq`)

**Radial direction in Cartesian basis.** The radial unit vector equals cos θ times the first Cartesian unit vector plus sin θ times the second. (`Breakdown.CellCert.CellFormula.Internal.GaugeFluxParts.rad_eq`)

**Angular direction in Cartesian basis.** The angular unit vector equals minus sin θ times the first Cartesian unit vector plus cos θ times the second. (`Breakdown.CellCert.CellFormula.Internal.GaugeFluxParts.ang_eq`)

**Continuous cylindrical point map.** At fixed height, the cylindrical point depends continuously on radius and angle. (`Breakdown.CellCert.CellFormula.Internal.GaugeFluxParts.cyl_cont`)

**Continuous cylindrical basis vectors.** Each cylindrical frame vector depends continuously on angle. (`Breakdown.CellCert.CellFormula.Internal.GaugeFluxParts.frame_cont`)

**Differentiate cylindrical radius.** The derivative of a cylindrical point with respect to radius is the radial unit vector. (`Breakdown.CellCert.CellFormula.Internal.GaugeFluxParts.cyl_dr`)

**Differentiate cylindrical height.** The derivative of a cylindrical point with respect to height is the axial unit vector. (`Breakdown.CellCert.CellFormula.Internal.GaugeFluxParts.cyl_dz`)

**Differentiate cylindrical angle.** The derivative of a cylindrical point with respect to angle is radius times the angular unit vector. (`Breakdown.CellCert.CellFormula.Internal.GaugeFluxParts.cyl_dt`)

**Differentiate the angular unit vector.** The angular derivative of the angular unit vector is minus the radial unit vector. (`Breakdown.CellCert.CellFormula.Internal.GaugeFluxParts.ang_dt`)

**Full turn preserves a cylindrical point.** Adding 2π to the angle leaves a cylindrical point unchanged. (`Breakdown.CellCert.CellFormula.Internal.GaugeFluxParts.cyl_per`)

**Full turn preserves angular direction.** Adding 2π to the angle leaves the angular unit vector unchanged. (`Breakdown.CellCert.CellFormula.Internal.GaugeFluxParts.ang_per`)

**Continuous cylindrical radius.** Cylindrical radius is a continuous function on space. (`Breakdown.CellCert.CellFormula.Internal.GaugeFluxParts.radius_cont`)

**Continuous height coordinate.** The height coordinate is continuous on space. (`Breakdown.CellCert.CellFormula.Internal.GaugeFluxParts.height_cont`)

**Recover a nonnegative radius.** At nonnegative radius, the cylindrical radius of the corresponding cylindrical point is the original radius. (`Breakdown.CellCert.CellFormula.Internal.GaugeFluxParts.cyl_radius`)

**Recover the height coordinate.** The height of a cylindrical point is its original height parameter. (`Breakdown.CellCert.CellFormula.Internal.GaugeFluxParts.cyl_height`)

**Differentiate a parameter integral.** Joint continuity of an integrand and its parameter derivative permits differentiation under a fixed interval integral. (`Breakdown.CellCert.CellFormula.Internal.GaugeFluxParts.param_deriv`)

**Zero vector mode is an angular mean.** The zero vector mode is the real angular mean of the cylindrical-frame component, viewed as a complex number. (`Breakdown.CellCert.CellFormula.Internal.GaugeFluxParts.modeVec_zero`)

**Zero matrix mode is an angular mean.** The zero matrix mode is the real angular mean of the cylindrical-frame matrix entry, viewed as a complex number. (`Breakdown.CellCert.CellFormula.Internal.GaugeFluxParts.modeMat_zero`)

**Trace is unchanged by cylindrical frame.** The sum of the diagonal cylindrical-frame entries equals the Cartesian trace of the linear operator. (`Breakdown.CellCert.CellFormula.Internal.GaugeFluxParts.frame_trace`)

**Differentiate a circular pairing.** For a twice continuously differentiable field and the stated continuous differentiable parametrization, differentiating its circular pairing gives the integral of the field derivative applied to the parameter velocity. (`Breakdown.CellCert.CellFormula.Internal.GaugeFluxParts.circ_deriv`)

**Continuous matrix entry along a curve.** A continuous operator-valued curve has continuous cylindrical-frame matrix entries. (`Breakdown.CellCert.CellFormula.Internal.GaugeFluxParts.fm_cont`)

**Zero-mode divergence identities.** Admissible cell data, the row-shape condition and an active row give radial and axial derivative identities, the angular diagonal relation and zero trace inside the cell. (`Breakdown.CellCert.CellFormula.Internal.GaugeFluxParts.zero_calc`)

**Polynomial function of a real variable.** This predicate says that a complex-valued function on the reals is evaluation of a complex polynomial. (`Breakdown.CellCert.CellFormula.Internal.GaugeFluxParts.IsP`)

**Constant functions are polynomial.** A constant complex-valued function is polynomial in the real variable. (`Breakdown.CellCert.CellFormula.Internal.GaugeFluxParts.isP_const`)

**Add polynomial functions.** The sum of two polynomial functions is polynomial. (`Breakdown.CellCert.CellFormula.Internal.GaugeFluxParts.isP_add`)

**Subtract polynomial functions.** The difference of two polynomial functions is polynomial. (`Breakdown.CellCert.CellFormula.Internal.GaugeFluxParts.isP_sub`)

**Sum a finite polynomial family.** A finite sum of functions polynomial on the selected indices is polynomial. (`Breakdown.CellCert.CellFormula.Internal.GaugeFluxParts.isP_sum`)

**Polynomial primitives stay polynomial.** The integral from zero to a variable endpoint of a polynomial function is polynomial. (`Breakdown.CellCert.CellFormula.Internal.GaugeFluxParts.isP_prim`)

**Integrate a weighted polynomial slice.** Integrating a bivariate polynomial over a fixed height interval after multiplying by a natural radial power gives a polynomial in radius. (`Breakdown.CellCert.CellFormula.Internal.GaugeFluxParts.isP_slice`)

**Zero derivative forces global constancy.** A polynomial function whose derivative vanishes on a nonempty open interval equals its value at zero everywhere. (`Breakdown.CellCert.CellFormula.Internal.GaugeFluxParts.isP_const_of_deriv`)

**Conjugate an interval integral.** Complex conjugation commutes with an interval integral. (`Breakdown.CellCert.CellFormula.Internal.GaugeFluxParts.ii_conj`)

**Polynomial functions are continuous.** Every complex polynomial function of a real variable is continuous. (`Breakdown.CellCert.CellFormula.Internal.GaugeFluxParts.isP_cont`)

**Radial weight preserves test polynomials.** Multiplying a finite face-test polynomial expansion by radius gives a polynomial function. (`Breakdown.CellCert.CellFormula.Internal.GaugeFluxParts.isP_test`)

**Differentiate a smooth slice integral.** A continuously differentiable bivariate function has the stated radial derivatives both before and after integration over a fixed interval. (`Breakdown.CellCert.CellFormula.Internal.GaugeFluxParts.param_deriv_cd`)

**Recover a value from radial weighting.** If r is nonzero, ρr^e = r and ρu = P, then u = Pr^e/r. (`Breakdown.CellCert.CellFormula.Internal.GaugeFluxParts.solve_rhat`)

**Cancel the total zero-mode flux.** For admissible cell data and row shape, the stated zero-mode calculus and polynomial top and bottom traces make the radius-weighted lateral flux plus the upper radial primitive minus the lower primitive vanish. (`Breakdown.CellCert.CellFormula.Internal.GaugeFluxParts.flux_main`)

**Zero-mode calculus for valid form data.** Valid form and cell data with the row-shape condition give the displayed zero-mode derivative, angular-diagonal and divergence identities for active rows inside the cell. (`Breakdown.CellCert.CellFormula.rowMode_zero_calc`)

**Cancel conjugated pressure-side flux.** For admissible cell data, row shape and pressure layout, the stated zero-mode calculus and polynomial boundary traces imply the conjugated pressure-side flux identity. (`Breakdown.CellCert.CellFormula.presSide_flux_of_calc`)

### Breakdown.FracCell.GaugeInvariance

This file proves that compatible pressure gauge shifts leave the cell row constraints unchanged, using polynomial trace recovery and cancellation of boundary fluxes.

**Pressure change on a face moment.** The pressure-shift value uses the chosen left or right gauge on radial faces and the difference of point-gauge-weighted radial primitives on height faces. (`_private.Breakdown.FracCell.GaugeInvariance.0.Breakdown.CellCert.CellFormula.presShiftValue`)

**Continuous face test polynomial.** Every face-segment test polynomial is continuous. (`_private.Breakdown.FracCell.GaugeInvariance.0.Breakdown.CellCert.CellFormula.test_continuous`)

**Recover coefficients by orthogonality.** Integrating a finite test-basis expansion against one basis element recovers its coefficient when the tests are orthonormal on the segment. (`_private.Breakdown.FracCell.GaugeInvariance.0.Breakdown.CellCert.CellFormula.coef_of_orth`)

**Conjugate a test polynomial expansion.** Conjugating a complex expansion in real test polynomials conjugates its coefficients. (`_private.Breakdown.FracCell.GaugeInvariance.0.Breakdown.CellCert.CellFormula.conj_poly`)

**Integrate a test polynomial expansion.** The interval integral of a finite test-polynomial expansion is the sum of each coefficient times the corresponding test integral. (`_private.Breakdown.FracCell.GaugeInvariance.0.Breakdown.CellCert.CellFormula.interval_poly`)

**Integrate a radius-weighted expansion.** The integral from zero to v of radius times a test-polynomial expansion is the sum of its coefficients times the radial test primitives. (`_private.Breakdown.FracCell.GaugeInvariance.0.Breakdown.CellCert.CellFormula.weighted_poly`)

**Telescope matching functions on tiles.** On a nondegenerate interval tiled by disjoint-interior subintervals, endpoint differences of functions agreeing with one common function sum to that function's total endpoint difference. (`_private.Breakdown.FracCell.GaugeInvariance.0.Breakdown.CellCert.CellFormula.tele_family`)

**Combine radial pressure segments.** For a valid pressure layout, continuous trace functions on radial segments covering the height interval have conjugate integrals summing to the whole radial-face flux. (`_private.Breakdown.FracCell.GaugeInvariance.0.Breakdown.CellCert.CellFormula.radial_side`)

**Combine height pressure segments.** For a valid pressure layout, matching primitive functions on height segments covering the radial interval have endpoint differences summing to the total radial endpoint difference. (`_private.Breakdown.FracCell.GaugeInvariance.0.Breakdown.CellCert.CellFormula.height_side`)

**Evaluate one pressure-shift segment.** For 1 < α < 5/4 and the stated valid form, cell, row and pressure data, a polynomial face trace converts the pressure-row pairing with a gauge shift into the displayed oriented boundary flux. (`_private.Breakdown.FracCell.GaugeInvariance.0.Breakdown.CellCert.CellFormula.segment_value`)

**Pressure shifts cancel across all faces.** For 1 < α < 5/4, the stated admissible cell and form data, row shape, pressure layout, polynomial traces and compatible gauge shift make the total zero-mode pressure-row shift pairing vanish. (`_private.Breakdown.FracCell.GaugeInvariance.0.Breakdown.CellCert.CellFormula.pres_total`)

**Corner values ignore pressure slots.** A corner-value row evaluates to zero on every pressure datum slot. (`_private.Breakdown.FracCell.GaugeInvariance.0.Breakdown.CellCert.CellFormula.cornerAt_presSlot`)

**Side velocity ignores pressure slots.** A side-velocity row evaluates to zero on every pressure datum slot. (`_private.Breakdown.FracCell.GaugeInvariance.0.Breakdown.CellCert.CellFormula.sideVelocityRow_presSlot`)

**Side gradient ignores pressure slots.** A side-gradient row evaluates to zero on every pressure datum slot. (`_private.Breakdown.FracCell.GaugeInvariance.0.Breakdown.CellCert.CellFormula.sideGradientRow_presSlot`)

**Turn rows ignore pressure slots.** A turn-side row evaluates to zero on every pressure datum slot. (`_private.Breakdown.FracCell.GaugeInvariance.0.Breakdown.CellCert.CellFormula.turnSideRow_presSlot`)

**Base face rows ignore pressure slots.** A base-face row evaluates to zero on every pressure datum slot. (`_private.Breakdown.FracCell.GaugeInvariance.0.Breakdown.CellCert.CellFormula.faceBaseRow_presSlot`)

**Strain face rows ignore pressure slots.** A strain-face row evaluates to zero on every pressure datum slot. (`_private.Breakdown.FracCell.GaugeInvariance.0.Breakdown.CellCert.CellFormula.strainFaceRow_presSlot`)

**Normal-face rows ignore pressure shifts.** Pairing a normal-face data row with any pressure shift gives zero. (`_private.Breakdown.FracCell.GaugeInvariance.0.Breakdown.CellCert.CellFormula.normalFace_pressureShift`)

**Pressure shifts preserve row values.** For 1 < α < 5/4, valid form and cell data, row shape, a pressure layout and the stated polynomial normal traces ensure that a valid gauge shift of admissible pressure data leaves every selected layout row value unchanged. (`Breakdown.CellCert.CellFormula.gaugeInvariance_holds`)

### Breakdown.FracCell.GaugeInvarianceParts

This file supplies trace formulas, zero-mode flux cancellation and finite tiling identities needed to prove pressure gauge invariance in the cell layer.

**Vertical lines have zero area.** A vertical line in the radius-height plane has zero volume. (`_private.Breakdown.FracCell.GaugeInvarianceParts.0.Breakdown.CellCert.CellFormula.null_vert`)

**Horizontal lines have zero area.** A horizontal line in the radius-height plane has zero volume. (`_private.Breakdown.FracCell.GaugeInvarianceParts.0.Breakdown.CellCert.CellFormula.null_horiz`)

**Recover an endpoint by weighted calculus.** For distinct endpoints and a function with the stated continuous derivative, the oriented integral of the displayed affine-weighted derivative expression equals the value at the chosen endpoint. (`_private.Breakdown.FracCell.GaugeInvarianceParts.0.Breakdown.CellCert.CellFormula.ftc_line`)

**Radial strip moment equals a face trace.** A continuous radial representative and derivative agreeing almost everywhere with the strip data identify the radial strip moment with its weighted endpoint trace integral. (`_private.Breakdown.FracCell.GaugeInvarianceParts.0.Breakdown.CellCert.CellFormula.radial_strip`)

**Height strip moment equals a face trace.** A continuous height representative and derivative agreeing almost everywhere with the strip data identify the height strip moment with its weighted endpoint trace integral. (`_private.Breakdown.FracCell.GaugeInvarianceParts.0.Breakdown.CellCert.CellFormula.height_strip`)

**Bivariate polynomials are differentiable.** Every function in the stated bivariate polynomial space is continuously differentiable. (`_private.Breakdown.FracCell.GaugeInvarianceParts.0.Breakdown.CellCert.CellFormula.poly_contDiff`)

**Smooth representative of a weighted mode.** On a valid cell box, a mode whose adjusted-radius multiple is polynomial away from radius zero admits a continuously differentiable representative on an open neighborhood of the rectangle. (`_private.Breakdown.FracCell.GaugeInvarianceParts.0.Breakdown.CellCert.CellFormula.low_fn`)

**Radial derivative of a smooth function.** A continuously differentiable function on an open set has radial slice derivative equal to its Fréchet derivative applied to (1,0). (`_private.Breakdown.FracCell.GaugeInvarianceParts.0.Breakdown.CellCert.CellFormula.line_r`)

**Height derivative of a smooth function.** A continuously differentiable function on an open set has height slice derivative equal to its Fréchet derivative applied to (0,1). (`_private.Breakdown.FracCell.GaugeInvarianceParts.0.Breakdown.CellCert.CellFormula.line_z`)

**Continuous directional derivative.** On an open set where a function is continuously differentiable, its Fréchet derivative in any fixed direction is continuous. (`_private.Breakdown.FracCell.GaugeInvarianceParts.0.Breakdown.CellCert.CellFormula.fderiv_cont`)

**Pressure trace from the boundary value.** For 1 < α < 5/4 and the stated valid cell, form, row and pressure-layout data, a boundary representative turns the pressure-segment trace into its test-weighted boundary integral. (`Breakdown.CellCert.CellFormula.presSide_trace`)

**Conjugated pressure flux vanishes.** For 1 < α < 5/4 and the stated valid cell, form, row and pressure data, polynomial top and bottom traces satisfy the displayed conjugated zero-mode flux cancellation. (`Breakdown.CellCert.CellFormula.presSide_flux`)

**Telescope a finite interval partition.** Positive-length subintervals with disjoint interiors that cover a nondegenerate interval have endpoint differences summing to the total endpoint difference. (`_private.Breakdown.FracCell.GaugeInvarianceParts.0.Breakdown.CellCert.CellFormula.tile_aux`)

**Telescope over a finite tiling.** For a finite disjoint-interior tiling of a nondegenerate interval, the sum of endpoint differences of any function equals its total endpoint difference. (`Breakdown.CellCert.CellFormula.tiling_telescope`)

### Breakdown.FracCell.GaugeShiftOf

This file constructs the pressure gauge-shift interface from conjugate symmetry of true cell data, treating the zero Fourier mode as real.

**Negation fixes the zero mode.** Negating a layout mode whose integer value is zero returns the same mode. (`Breakdown.CellCert.CellFormula.GaugeShiftOf.Internal.negMode_zero`)

**Zero-mode shift from endpoint gauges.** At the zero mode, the constructed pressure shift equals the left shift coefficient times the left gauge plus the right shift coefficient times the right gauge. (`Breakdown.CellCert.CellFormula.GaugeShiftOf.Internal.shift_eq`)

**Pressure datum is a zero-mode real part.** When the layout contains the zero mode, its pressure datum value is the real part of the corresponding true pressure datum. (`Breakdown.CellCert.CellFormula.GaugeShiftOf.Internal.pdv_eq`)

**Zero-mode pressure data are real.** Under the conjugate-data interface, a valid pressure layout and admissible field tuple make each zero-mode pressure datum equal to its real part embedded in the complex numbers. (`Breakdown.CellCert.CellFormula.GaugeShiftOf.Internal.true_real`)

**Construct gauge shifts from conjugacy.** The conjugate-data statement makes shifts that are linear on admissible fields and satisfy the prescribed jumps and zero roots into a valid pressure gauge shift with every deleted coordinate zero, assuming a valid pressure layout and gauge specification. (`Breakdown.CellCert.CellFormula.gaugeShiftOf_of`)

### Breakdown.FracCell.GivenAuxActuator

This file turns the supplied spline actuator data into compactly supported symmetry-class fields with square-integrable weak gradients, discharging analytic actuator requirements in the cell certificate construction.

**Bound a list lookup with a default.** If every list entry and the default value one are at least tb, every lookup with that default is at least tb. (`_private.Breakdown.FracCell.GivenAuxActuator.0.Breakdown.CellCert.GivenFields.getD_ge_of_all`)

**Cell selection respects a mesh break.** In a strictly increasing mesh from zero to one, selecting the cell of u ≥ tb returns a lower endpoint at least tb when tb is an interior mesh break. (`_private.Breakdown.FracCell.GivenAuxActuator.0.Breakdown.CellCert.GivenFields.break_le_cell`)

**A vanishing spline evaluates to zero.** A spline on a tensor mesh that vanishes from a positive interior mesh break evaluates to zero at and beyond that break for either parity choice. (`_private.Breakdown.FracCell.GivenAuxActuator.0.Breakdown.CellCert.GivenFields.eval_vanish`)

**Derivative on a vanishing half-line.** A function vanishing from tb onward has Lean derivative zero at every t ≥ tb. (`_private.Breakdown.FracCell.GivenAuxActuator.0.Breakdown.CellCert.GivenFields.deriv_vanish`)

**Twisted scaling preserves vanishing.** If a two-variable function vanishes at every height from tb onward, its twisted scaling also vanishes there. (`_private.Breakdown.FracCell.GivenAuxActuator.0.Breakdown.CellCert.GivenFields.twisted_vanish`)

**Height differentiation preserves zero.** If a two-variable function vanishes at every height from tb onward, its height derivative also vanishes there. (`_private.Breakdown.FracCell.GivenAuxActuator.0.Breakdown.CellCert.GivenFields.height_vanish`)

**Vanishing zero-mode amplitudes.** If the mean stream and swirl spline amplitudes vanish from tb onward, every reduced zero-mode field component vanishes there. (`_private.Breakdown.FracCell.GivenAuxActuator.0.Breakdown.CellCert.GivenFields.reducedField_vanish_zero`)

**Vanishing nonzero-mode amplitudes.** If the radial and polar spline amplitudes of a nonzero mode vanish from tb onward, every reduced component of that mode vanishes there. (`_private.Breakdown.FracCell.GivenAuxActuator.0.Breakdown.CellCert.GivenFields.reducedField_vanish_ne`)

**Vanishing modes give a zero field.** If every retained reduced mode vanishes at a point's chart coordinates, the reconstructed field vanishes at that point. (`_private.Breakdown.FracCell.GivenAuxActuator.0.Breakdown.CellCert.GivenFields.fieldOf_vanish`)

**Compact data vanish past their cutoff.** Compact field data with positive support break give a zero reconstructed field wherever the chart radius is at least that break. (`Breakdown.CellCert.GivenFields.fieldOf_eq_zero_of_compact`)

**Place actuator support in a region.** Valid chart and auxiliary data make each actuator vanish outside any region containing every point below the support break in chart radius. (`Breakdown.CellCert.GivenFields.actuatorSupport_of_given`)

**Convert chart radius to a norm bound.** For valid chart parameters and tb < 1, chart radius below tb implies ‖y‖ ≤ L₀tb/(1 − tb). (`_private.Breakdown.FracCell.GivenAuxActuator.0.Breakdown.CellCert.GivenFields.norm_le_of_chart_lt`)

**A ball encloses the support region.** A region containing a ball of radius at least L₀ times the support break divided by one minus that break contains all points below the chart support cutoff. (`Breakdown.CellCert.GivenFields.supportRegion_of`)

**Compact data give compact support.** For valid chart parameters and positive support break, compact field data reconstruct a compactly supported field. (`Breakdown.CellCert.GivenFields.fieldOf_hasCompactSupport_of_compact`)

**Classical derivative is a weak gradient.** A continuously differentiable field has its Fréchet derivative as a weak gradient. (`_private.Breakdown.FracCell.GivenAuxActuator.0.Breakdown.CellCert.GivenFields.weakGradient_of_contDiff_one`)

**Actuators satisfy the field class.** Valid chart and auxiliary data, matching symmetry order and the stated actuator identification make all certificate actuators square integrable and members of the required symmetry class. (`Breakdown.CellCert.GivenFields.actuator_of_given`)

**Actuators have integrable weak gradients.** Valid chart and auxiliary data give each actuator its Fréchet derivative as weak gradient, with almost-everywhere strong measurability and integrable squared matrix entries. (`Breakdown.CellCert.GivenFields.actuatorGradient_of_given`)

### Breakdown.FracCell.GivenAuxActuatorClass

This file proves rotation and reflection symmetries of fields reconstructed from the supplied modal spline data, establishing the class condition needed for actuator certificates.

**First coordinate after a rotation step.** A rotation step sends the first coordinate to cos(2π/m)y₀ − sin(2π/m)y₁. (`_private.Breakdown.FracCell.GivenAuxActuatorClass.0.Breakdown.CellCert.GivenFields.turn_zero`)

**Second coordinate after a rotation step.** A rotation step sends the second coordinate to sin(2π/m)y₀ + cos(2π/m)y₁. (`_private.Breakdown.FracCell.GivenAuxActuatorClass.0.Breakdown.CellCert.GivenFields.turn_one`)

**Rotation preserves the height coordinate.** A rotation step leaves the third coordinate unchanged. (`_private.Breakdown.FracCell.GivenAuxActuatorClass.0.Breakdown.CellCert.GivenFields.turn_two`)

**Rotation preserves spatial norm.** A rotation step preserves the Euclidean norm. (`_private.Breakdown.FracCell.GivenAuxActuatorClass.0.Breakdown.CellCert.GivenFields.turn_norm`)

**Angle after a discrete rotation.** A rotation step changes the planar angle by 2π/m modulo a full turn, or leaves it unchanged. (`_private.Breakdown.FracCell.GivenAuxActuatorClass.0.Breakdown.CellCert.GivenFields.turn_angle`)

**Mode phase respects the rotation step.** For valid chart parameters, each mode phase is invariant under the prescribed discrete rotation. (`_private.Breakdown.FracCell.GivenAuxActuatorClass.0.Breakdown.CellCert.GivenFields.turn_phase`)

**Assemble complex frame coefficients.** Each frame coefficient is the decay factor times the sum of phase-weighted reduced modal coefficients in that frame component. (`_private.Breakdown.FracCell.GivenAuxActuatorClass.0.Breakdown.CellCert.GivenFields.frameCoef`)

**Reconstruct from frame coefficients.** The reconstructed field is the Cartesian vector obtained by combining the real parts of its three frame coefficients with the radial, polar and azimuthal frame vectors. (`_private.Breakdown.FracCell.GivenAuxActuatorClass.0.Breakdown.CellCert.GivenFields.fieldOf_frame`)

**Reconstructed fields respect rotation.** For valid chart parameters, evaluating the reconstructed field at a rotation step equals rotating its value. (`_private.Breakdown.FracCell.GivenAuxActuatorClass.0.Breakdown.CellCert.GivenFields.turn_fieldOf`)

**Reflect an even spline evaluation.** Evaluating the even spline extension at −x gives its value at x. (`_private.Breakdown.FracCell.GivenAuxActuatorClass.0.Breakdown.CellCert.GivenFields.eval_even_neg`)

**Odd spline evaluation is reflection odd.** Away from x = 0, evaluating the odd spline extension at −x gives minus its value at x. (`_private.Breakdown.FracCell.GivenAuxActuatorClass.0.Breakdown.CellCert.GivenFields.eval_odd_neg`)

**Twisted scaling preserves even parity.** Equality of a function at x and −x for every first-coordinate value implies the same equality for its twisted scaling. (`_private.Breakdown.FracCell.GivenAuxActuatorClass.0.Breakdown.CellCert.GivenFields.twisted_even`)

**Twisted scaling preserves odd parity.** Opposite values of a function at x and −x for every first-coordinate value imply opposite values for its twisted scaling. (`_private.Breakdown.FracCell.GivenAuxActuatorClass.0.Breakdown.CellCert.GivenFields.twisted_odd`)

**Derivative of an odd height function.** Away from zero, the height derivative of a function odd away from zero is even. (`_private.Breakdown.FracCell.GivenAuxActuatorClass.0.Breakdown.CellCert.GivenFields.height_even_of_odd`)

**Reflection signs of reduced components.** Reflecting a nonzero height ratio preserves the first and third reduced field components and negates the second. (`_private.Breakdown.FracCell.GivenAuxActuatorClass.0.Breakdown.CellCert.GivenFields.reducedField_mirror`)

**First coordinate under reflection.** The mirror map preserves the first Cartesian coordinate. (`_private.Breakdown.FracCell.GivenAuxActuatorClass.0.Breakdown.CellCert.GivenFields.mirror_zero`)

**Second coordinate under reflection.** The mirror map preserves the second Cartesian coordinate. (`_private.Breakdown.FracCell.GivenAuxActuatorClass.0.Breakdown.CellCert.GivenFields.mirror_one`)

**Reflection reverses height.** The mirror map negates the third Cartesian coordinate. (`_private.Breakdown.FracCell.GivenAuxActuatorClass.0.Breakdown.CellCert.GivenFields.mirror_two`)

**Reflection preserves spatial norm.** The mirror map preserves the Euclidean norm. (`_private.Breakdown.FracCell.GivenAuxActuatorClass.0.Breakdown.CellCert.GivenFields.mirror_norm`)

**Reconstructed fields respect reflection.** Away from the zero-height plane, evaluating the reconstructed field at the mirrored point equals mirroring its value. (`_private.Breakdown.FracCell.GivenAuxActuatorClass.0.Breakdown.CellCert.GivenFields.mirror_fieldOf`)

**Almost every point has nonzero height.** The third Cartesian coordinate is nonzero almost everywhere for volume. (`_private.Breakdown.FracCell.GivenAuxActuatorClass.0.Breakdown.CellCert.GivenFields.ae_height_ne`)

**Symmetry class of reconstructed fields.** For valid chart parameters, every reconstructed field belongs to the symmetry class of the chart order. (`Breakdown.CellCert.GivenFields.fieldOf_class`)

### Breakdown.FracCell.GivenAuxActuatorOpen

This file proves continuous differentiability of reconstructed actuator modes, gluing spline pieces and removing apparent angular and origin singularities; these regularity facts feed the compact-support and weak-gradient actuator checks.

**Reconstruct one modal field.** A single modal field is the real Cartesian reconstruction of the phase-weighted reduced mode and its three frame directions, multiplied by the decay factor. (`Breakdown.CellCert.GivenFields.modeFieldOf`)

**Count passed mesh breaks.** The gluing index counts the list entries at or below the chosen coordinate. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.glueIdx`)

**Gluing index at the first break.** In a strictly increasing list, the gluing index is one plus the tail index when the first break has been reached and is zero otherwise. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.glueIdx_cons`)

**Gluing index is bounded by list length.** The number of passed mesh breaks is at most the number of list entries. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.glueIdx_le`)

**Join two differentiable pieces.** Two differentiable pieces with continuous derivatives and matching values and derivatives on a continuous-coordinate interface glue to a differentiable function with continuous derivative. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.glue_two`)

**Join a finite sequence of pieces.** Along strictly ordered coordinate breaks, differentiable pieces with continuous derivatives and matching adjacent values and derivatives glue to a differentiable function with continuous derivative. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.glue_list`)

**Evaluate a two-variable polynomial.** Polynomial evaluation substitutes the two real coordinates, viewed as complex numbers, into a two-variable complex polynomial. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.evP`)

**Build the polynomial derivative.** The candidate polynomial derivative combines the two evaluated formal partial derivatives with the corresponding coordinate projections. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.dP`)

**Apply the polynomial derivative.** Applying the polynomial derivative to a direction gives the sum of its two coordinates times the corresponding evaluated partial derivatives. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.dP_apply`)

**Differentiate polynomial evaluation.** A two-variable polynomial evaluation has the stated linear derivative at every real coordinate pair. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.evP_hasFDerivAt`)

**Derivatives of matching slices.** Polynomials agreeing along a line with fixed second coordinate have equal first partial derivatives along that line. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.evP_line_t`)

**Match derivatives on a vertical slice.** Polynomials agreeing along a line with fixed first coordinate have equal second partial derivatives along that line. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.evP_line_x`)

**Formal mixed partials commute.** The two formal partial derivatives of a two-variable polynomial commute. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.pderiv_swap`)

**Continuous polynomial derivative.** The candidate derivative of a polynomial evaluation is continuous. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.dP_continuous`)

**Conditions for gluing spline pieces.** The gluing predicate requires adjacent polynomial values and normal partials to match at both kinds of mesh break, together with the stated odd or even condition at the reflection axis. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.Glued`)

**Glue along first-coordinate breaks.** Strictly ordered first-coordinate breaks with matching polynomial values and first partials produce a differentiable piecewise function with continuous derivative. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.rows_glue`)

**Glue across both coordinate meshes.** Strictly ordered meshes and the gluing conditions produce a differentiable piecewise polynomial function with continuous derivative across both coordinates. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.half_glue`)

**Extend pieces by reflection parity.** The full piecewise function evaluates the selected polynomial at the absolute second coordinate and applies the chosen odd sign on the negative side. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.fullF`)

**Reflect the second coordinate linearly.** This continuous linear map preserves the first coordinate and negates the second. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.reflX`)

**Evaluate the coordinate reflection.** The coordinate reflection sends (t,x) to (t,−x). (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.reflX_apply`)

**Derivative for the reflected extension.** The full derivative uses the local polynomial derivative on the nonnegative side and the parity-signed derivative composed with reflection on the negative side. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.fullD`)

**Zero lies before all positive breaks.** If every second-coordinate mesh break is positive, the gluing index at zero is zero. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.glueIdx_zero`)

**Glue the reflected spline globally.** Strictly ordered meshes, positive second-coordinate breaks and the gluing conditions make the parity extension differentiable everywhere with continuous derivative. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.full_glue`)

**First partial keeps reflection parity.** The full derivative in the first coordinate equals the parity extension of the first formal partials with the original parity. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.fullD_t`)

**Second partial reverses parity.** The full derivative in the second coordinate equals the parity extension of the second formal partials with the opposite parity. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.fullD_x`)

**Evaluate after polynomial substitution.** Evaluating a polynomial after substituting polynomials for its variables equals evaluating it at the substituted polynomial values. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.eval_bind_two`)

**Evaluate a fixed first coordinate.** Substituting a constant for the first polynomial variable evaluates the original polynomial at that first coordinate. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.evP_atFirst`)

**Evaluate a fixed second coordinate.** Substituting a constant for the second polynomial variable evaluates the original polynomial at that second coordinate. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.evP_atSecond`)

**First-coordinate join gives equal values.** Equal polynomial restrictions at a fixed first coordinate give equal evaluated values along that line. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.join_t`)

**Equal values at a second-coordinate join.** Equal polynomial restrictions at a fixed second coordinate give equal evaluated values along that line. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.join_x`)

**A zero restriction vanishes on the axis.** If a polynomial restricts to zero at second coordinate zero, every evaluated value on that axis is zero. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.par_zero`)

**Interior mesh breaks and cell count.** A strictly increasing mesh from zero to one has positive ordered interior breaks, one fewer interior break than cells, and the displayed index correspondence with the full mesh. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.mesh_facts`)

**Spline evaluation as reflected pieces.** Evaluating a spline equals the parity extension of its polynomial pieces across the interior mesh breaks. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.spline_eq`)

**Spline matching supplies gluing data.** A spline of class at least one in both coordinates satisfies the gluing conditions for its original parity. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.glued_base`)

**First partials inherit gluing data.** A spline of first-coordinate class at least two and second-coordinate class at least one gives gluing data for its first formal partials with unchanged parity. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.glued_t`)

**Second partials inherit reversed parity.** A spline of first-coordinate class at least one and second-coordinate class at least two gives gluing data for its second formal partials with reversed parity. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.glued_x`)

**Spline evaluation is differentiable.** A spline of class at least one in each coordinate has a continuously differentiable evaluation function. (`Breakdown.CellCert.GivenFields.spline_eval_contDiff`)

**Regularity of the first spline partial.** With class at least two in the first coordinate and at least one in the second, the first-coordinate spline derivative is continuously differentiable jointly. (`Breakdown.CellCert.GivenFields.spline_tderiv_contDiff`)

**Regularity of the second spline partial.** With class at least one in the first coordinate and at least two in the second, the second-coordinate spline derivative is continuously differentiable jointly. (`Breakdown.CellCert.GivenFields.spline_xderiv_contDiff`)

**Regularity of a first partial derivative.** The first partial derivative of a twice continuously differentiable bivariate function is continuously differentiable jointly. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.partial_t_contDiff`)

**Regularity of a second partial.** The second partial derivative of a twice continuously differentiable bivariate function is continuously differentiable jointly. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.partial_x_contDiff`)

**Regularity of a product's first partial.** The first partial of a product is continuously differentiable when one factor is twice continuously differentiable and the other factor and its first partial are continuously differentiable. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.tderiv_mul_contDiff`)

**Regularity of a product's second partial.** The second partial of a product is continuously differentiable when one factor is twice continuously differentiable and the other factor and its second partial are continuously differentiable. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.xderiv_mul_contDiff`)

**Transfer regularity across equality.** A function pointwise equal to a continuously differentiable function is continuously differentiable. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.contDiff_of_eq`)

**Smooth compactified core ratio.** For valid chart parameters, the compactified core-ratio function is smooth. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.coreRatioT_contDiff`)

**Smooth radial and height weight.** The product of the radial weight polynomial and any natural power of one minus the squared height ratio is smooth. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.smooth_weight`)

**Smooth weight with an extra axis factor.** Multiplying the radial and height weight by one additional factor of one minus the squared height ratio remains smooth. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.smooth_weight'`)

**Regularity of reduced nonzero modes.** Valid chart and field data make every component of a retained nonzero reduced mode continuously differentiable in its two chart coordinates. (`Breakdown.CellCert.GivenFields.reducedField_wave_contDiff`)

**Smooth radial weight polynomial.** The radial weight polynomial, viewed as a function of the two chart coordinates, is smooth. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.smooth_p`)

**Smooth quadratic height factor.** One minus the squared second chart coordinate is a smooth complex-valued function. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.smooth_q`)

**Regularity of the reduced mean mode.** Valid chart and field data containing the zero mode make every reduced mean-mode component continuously differentiable in its chart coordinates. (`Breakdown.CellCert.GivenFields.reducedField_mean_contDiff`)

**Read a reconstructed component.** The selected coordinate of a vector reconstructed from real components equals that component. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.ofComponents_apply'`)

**Smooth Cartesian coordinate projection.** Every Cartesian coordinate projection is smooth. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.coord_contDiff`)

**Smooth norm away from the origin.** The Euclidean norm is smooth at every nonzero point. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.norm_contDiffAt`)

**Nonzero points have nonzero norm.** A nonzero spatial point has nonzero norm. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.norm_ne`)

**Smooth chart radius off the origin.** For valid chart parameters, the compactified radius is smooth at every nonzero point. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.chartT_contDiffAt`)

**Smooth height ratio off the origin.** The height ratio is smooth at every nonzero point. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.heightRatio_contDiffAt`)

**Smooth decay factor off the origin.** For valid chart parameters, the decay factor is smooth at every nonzero point. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.decayFactor_contDiffAt`)

**Smooth logarithmic phase.** For valid chart parameters, the logarithmic phase function is smooth. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.logPhase_contDiff`)

**Smooth radial frame off the origin.** Every radial frame component is smooth at a nonzero point. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.radialVec_contDiffAt`)

**Smooth polar frame off the origin.** Every scaled polar-frame component is smooth at a nonzero point. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.polarVecQ_contDiffAt`)

**Smooth azimuthal frame off the origin.** Every scaled azimuthal-frame component is smooth at a nonzero point. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.azimVecQ_contDiffAt`)

**Complex embedding preserves regularity.** Viewing a real-valued function as complex-valued preserves its stated differentiability order at a point. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.ofReal_contDiffAt`)

**Encode the horizontal plane as complex.** The planar coordinate map forms a complex number from the first two Cartesian coordinates. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.planeOf`)

**Expand the planar complex coordinate.** The planar coordinate equals the first Cartesian coordinate plus the second times the imaginary unit. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.planeOf_eq`)

**Smooth planar coordinate map.** The planar complex coordinate map is smooth. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.planeOf_contDiff`)

**Integer angular phase as a power.** For a nonzero complex number, the exponential of an integer multiple of its argument equals the corresponding integer power of the number divided by its norm. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.exp_arg_int`)

**Regularity from reduced modes and phase.** At a nonzero point, continuously differentiable reduced components and phase give a continuously differentiable reconstructed field for valid chart parameters. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.field_contDiffAt_gen`)

**Regularity of one mode away from zero.** For valid chart parameters, a mode with continuously differentiable reduced components and phase is continuously differentiable at any nonzero point. (`Breakdown.CellCert.GivenFields.modeFieldOf_contDiffAt_of`)

**Extract the nonzero-mode axis factor.** Valid chart and field data let every retained nonzero reduced mode be factored as one minus squared height ratio times a continuously differentiable coefficient family. (`Breakdown.CellCert.GivenFields.reducedField_wave_axisFactor`)

**Raise radial weight order by two.** Increasing the radial weight's first index by two multiplies it by the square of the chart radius. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.weightPoly_two`)

**Extract axis and origin factors.** Valid chart and field data let every retained nonzero reduced mode be factored as one minus squared height ratio times squared chart radius times a continuously differentiable family. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.reducedField_wave_originFactor`)

**Squared radius regularizes angular phase.** For every integer angular frequency, squared complex norm times its angular phase is continuously differentiable on the whole complex plane. (`Breakdown.CellCert.GivenFields.planePhase_contDiff`)

**Regularity from phased coefficients.** At a nonzero point, continuously differentiable phase-times-reduced components give a continuously differentiable reconstructed field for valid chart parameters. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.field_contDiffAt_gen'`)

**Express the transverse radius ratio.** At a nonzero point, one minus squared height ratio equals squared planar norm divided by squared spatial norm. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.one_sub_heightRatio_sq`)

**Nonzero modes are regular on the axis.** Valid chart and field data make every retained nonzero modal field continuously differentiable at each nonzero spatial point, including points on the axis. (`Breakdown.CellCert.GivenFields.modeFieldOf_contDiffAt_axis_of`)

**Zero derivative from quadratic vanishing.** A complex-valued function bounded by C‖y‖² near zero, with C ≥ 0, has zero Fréchet derivative at zero. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.quad_hasFDerivAt`)

**Extend differentiability to the origin.** Continuous differentiability off the origin, quadratic vanishing and a derivative bound tending continuously to zero imply continuous differentiability at the origin. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.origin_crit`)

**Bound the derivative of a product.** The stated bounds on two differentiable complex functions and their derivatives bound the product derivative by ad + cb. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.prod_fderiv_bound`)

**Control changes of radius and direction.** Around a fixed nonzero y, the change in the radius-direction pair is at most (1 + 2/‖y‖) times the spatial displacement. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.dir_slope`)

**Bound the radius-direction derivative.** At nonzero y, the derivative of the radius-direction map has norm at most 1 + 2/‖y‖. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.dir_fderiv_bound`)

**Smooth radius-direction map.** The radius-direction map is smooth at every nonzero spatial point. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.dir_contDiffAt`)

**Uniform bounds for directional profiles.** A profile continuously differentiable on the compact radius-unit-sphere set has a uniformly bounded radius-direction composition whose derivative is bounded by B(1 + 2/‖y‖) away from zero. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.comp_dir_bounds`)

**Planar norm bounded by spatial norm.** The squared planar norm is at most the squared spatial norm. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.planeOf_sq_le`)

**Origin profile for a nonzero mode.** The origin profile combines the reduced coefficient family, directional frame factors, logarithmic phase and decay divided by (r + L₀)². (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.originProfile`)

**Regularity of the origin profile.** For valid chart parameters and continuously differentiable coefficient components, the origin profile is continuously differentiable at every nonnegative radius. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.originProfile_contDiffAt`)

**Factor the phase near the origin.** Away from zero, the mode phase times the axis and squared-chart-radius factors equals the displayed product of squared planar norm, integer angular phase, inverse radial denominator and logarithmic phase. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.phase_origin_factor`)

**Nonzero modes are regular at the origin.** Valid chart and field data make each retained nonzero modal field continuously differentiable at the origin. (`Breakdown.CellCert.GivenFields.modeFieldOf_contDiffAt_origin_wave`)

**Origin regularity from small derivatives.** Continuous differentiability off zero, quadratic vanishing and derivatives uniformly tending to zero imply continuous differentiability at the origin. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.origin_crit_eps`)

**Zero slice has no tangential derivative.** A differentiable function vanishing on the entire zero-radius slice has zero derivative in every direction tangent to that slice. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.slice_deriv_zero`)

**Control a slice by its derivative.** A function differentiable along a nonnegative radius interval with derivative norm at most B changes by at most B times the interval length. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.slice_bound`)

**Origin regularity of a weighted profile.** A profile continuously differentiable at nonnegative radii and vanishing on the zero-radius slice gives a continuously differentiable radius-weighted directional function at the origin. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.norm_mul_slice_contDiffAt`)

**Reduced core of the mean mode.** The mean core collects the weighted stream-derivative, compactified radial stream and swirl expressions after extracting one chart-radius factor from the reduced mean mode. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.meanCore`)

**Extract one radial weight factor.** The radial weight of first index one equals chart radius times the weight of first index zero. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.weightPoly_one`)

**Factor chart radius from the mean mode.** Every reduced mean-mode component equals chart radius times its mean-core component. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.meanCore_factor`)

**Regularity of the mean core.** Valid field data containing the zero mode make every mean-core component continuously differentiable in the chart coordinates. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.meanCore_contDiff`)

**Stream guard value at chart origin.** Valid field data containing the zero mode make the stream amplitude at chart radius zero equal the stream guard times the height ratio. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.meanStream_at_zero`)

**Swirl guard value at chart origin.** Valid field data containing the zero mode make the swirl amplitude at chart radius zero equal the constant swirl guard. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.meanSwirl_at_zero`)

**Evaluate the mean core at zero radius.** Valid field data containing the zero mode give mean-core values −g(1 − 3x²), −3gx and h at chart radius zero, where g and h are the stream and swirl guards. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.meanCore_zero`)

**Profile for the mean-mode origin proof.** The mean profile combines the mean core with directional frame coefficients and the decay factor divided by (r + L₀). (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.meanProfile`)

**Regularity of the mean profile.** Valid chart and field data containing the zero mode make the mean profile continuously differentiable at every nonnegative radius. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.meanProfile_contDiffAt`)

**Linear mean field from guard values.** The linear mean component is L₀⁻¹ times the displayed Cartesian combination of stream strain and swirl rotation determined by the two guard values. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.meanLinear`)

**Regularity of the linear mean field.** Each component of the linear mean field is continuously differentiable. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.meanLinear_contDiff`)

**Origin profile recovers the linear mean.** For valid chart and field data containing the zero mode, radius times the mean profile at zero radius and the normalized direction equals the linear mean field. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.meanProfile_origin`)

**Mean mode through its radial profile.** For valid chart parameters, each mean-mode field component is the real part of radius times the mean profile at the point's radius and normalized direction. (`_private.Breakdown.FracCell.GivenAuxActuatorOpen.0.Breakdown.CellCert.GivenFields.modeField_mean_eq`)

**Mean mode is regular at the origin.** Valid chart and field data containing the zero mode make the mean-mode field continuously differentiable at the origin. (`Breakdown.CellCert.GivenFields.modeFieldOf_contDiffAt_origin_mean`)

**Global regularity of nonzero modes.** Valid chart parameters and compact field data with positive support break make every retained nonzero modal field continuously differentiable everywhere. (`Breakdown.CellCert.GivenFields.modeFieldOf_contDiff_wave`)

**Global regularity of the mean mode.** Valid chart parameters and compact field data with positive support break containing the zero mode make the mean-mode field continuously differentiable everywhere. (`Breakdown.CellCert.GivenFields.modeFieldOf_contDiff_mean`)

### Breakdown.FracCell.GivenAuxActuatorSmooth

In the supplied auxiliary field branch of the cell certificate route, this file combines the mode fields and proves first derivative continuity for compact actuator data.

**Assemble a sum from its components.** Assembling a vector from finite sums of coordinates equals the finite sum of the vectors assembled from each coordinate function. (`_private.Breakdown.FracCell.GivenAuxActuatorSmooth.0.Breakdown.CellCert.GivenFields.ofComponents_sum`)

**Express the field as a sum of modes.** The constructed field is the finite sum of its mode fields over the stored mode set. (`Breakdown.CellCert.GivenFields.fieldOf_eq_sum_modes`)

**Smoothness of a compact field.** For valid chart parameters and compact field data with positive support break, the constructed field is continuously differentiable for every phase parameter. (`Breakdown.CellCert.GivenFields.fieldOf_contDiff_of_compact`)

### Breakdown.FracCell.GivenAuxAdjoint

This file packages decay, symmetry, weak derivative, and integrability facts for supplied adjoint fields and pressures, discharging analytic hypotheses of the certificate reduction.

**A discrete turn fixes zero.** Every discrete turn maps the zero vector to zero. (`Breakdown.CellCert.GivenFields.AdjointInternal.turn_zero`)

**Reflection fixes zero.** The mirror reflection maps the zero vector to zero. (`Breakdown.CellCert.GivenFields.AdjointInternal.mirror_zero'`)

**A discrete turn preserves addition.** A discrete turn of a vector sum is the sum of the turned vectors. (`Breakdown.CellCert.GivenFields.AdjointInternal.turn_add`)

**Reflection preserves addition.** The mirror reflection of a vector sum is the sum of the reflected vectors. (`Breakdown.CellCert.GivenFields.AdjointInternal.mirror_add'`)

**A discrete turn preserves scaling.** A discrete turn commutes with multiplication by any real scalar. (`Breakdown.CellCert.GivenFields.AdjointInternal.turn_smul`)

**Reflection preserves scaling.** The mirror reflection commutes with multiplication by any real scalar. (`Breakdown.CellCert.GivenFields.AdjointInternal.mirror_smul'`)

**L² fields are locally integrable.** Every L² field on three dimensional space is locally integrable. (`Breakdown.CellCert.GivenFields.AdjointInternal.loc_two`)

**A test derivative is continuous.** Every coordinate directional derivative of a scalar test function is continuous. (`Breakdown.CellCert.GivenFields.AdjointInternal.test_deriv_cont`)

**A test derivative has compact support.** Every coordinate directional derivative of a scalar test function has compact support. (`Breakdown.CellCert.GivenFields.AdjointInternal.test_deriv_supp`)

**A test gradient is continuous.** The gradient of a scalar test function is continuous. (`Breakdown.CellCert.GivenFields.AdjointInternal.grad_cont`)

**A test gradient has compact support.** The gradient of a scalar test function has compact support. (`Breakdown.CellCert.GivenFields.AdjointInternal.grad_supp`)

**Integrate an L² field against a gradient.** The inner product of an L² vector field with the gradient of a scalar test function is integrable. (`Breakdown.CellCert.GivenFields.AdjointInternal.inner_integrable`)

**The classical derivative is weak.** For a continuously differentiable vector field, its classical derivative is also its weak gradient. (`Breakdown.CellCert.GivenFields.AdjointInternal.weak_of_C1`)

**Zero divergence gives weak solenoidality.** A continuously differentiable field with zero pointwise divergence has zero integral pairing with every scalar test gradient. (`Breakdown.CellCert.GivenFields.AdjointInternal.sol_of_div`)

**Integrate a Lipschitz field by parts.** For a Lipschitz vector field and a scalar test function, the integral of the test directional derivative times the field equals minus the integral of the test function times the field's directional derivative. (`Breakdown.CellCert.GivenFields.AdjointInternal.weak_of_slope`)

**A Lipschitz gradient has a weak Hessian.** The derivative of a Lipschitz continuous linear map valued field is its weak second derivative in the stated sense. (`Breakdown.CellCert.GivenFields.AdjointInternal.weakSecond_of_slope`)

**Polynomial decay gives Lᵖ membership.** An almost everywhere strongly measurable field bounded almost everywhere by C times (1 + radius) raised to −a belongs to finite nonzero Lᵖ whenever a times p exceeds three. (`Breakdown.CellCert.GivenFields.AdjointInternal.memLp_of_decay`)

**Absorb a polynomial radial weight.** Multiplying (1 + radius) raised to −a by radius to a natural power k is bounded by (1 + radius) raised to −(a − k). (`Breakdown.CellCert.GivenFields.AdjointInternal.weight_le`)

**Coordinate vectors have unit norm.** Every coordinate unit vector in three dimensional space has norm one. (`Breakdown.CellCert.GivenFields.AdjointInternal.unit_norm`)

**State the adjoint field properties.** This proposition packages first derivative continuity, almost everywhere second differentiability, weighted L² and L³ bounds, a weak second derivative, weak solenoidality, and the discrete turn and mirror symmetries of an adjoint field. (`Breakdown.CellCert.GivenFields.AdjointInternal.GoodField`)

**The zero field has adjoint properties.** The zero vector field satisfies the packaged adjoint field properties for every symmetry order. (`Breakdown.CellCert.GivenFields.AdjointInternal.good_zero`)

**Add fields with adjoint properties.** The sum of two fields satisfying the packaged adjoint properties satisfies the same properties. (`Breakdown.CellCert.GivenFields.AdjointInternal.good_add`)

**Scale a field with adjoint properties.** Every real scalar multiple of a field satisfying the packaged adjoint properties satisfies the same properties. (`Breakdown.CellCert.GivenFields.AdjointInternal.good_smul`)

**Construct a valid adjoint field.** For valid chart parameters and valid field data with high order parameter three, the constructed field satisfies the packaged adjoint properties for the chart's symmetry order. (`Breakdown.CellCert.GivenFields.AdjointInternal.good_field`)

**An admissible atom belongs to L².** For valid chart parameters and atom data, the constructed atom belongs to L² for every phase parameter. (`Breakdown.CellCert.GivenFields.AdjointInternal.atom_two`)

**An adjoint family has the properties.** For valid chart parameters and auxiliary data, each evaluated adjoint family field satisfies the packaged adjoint properties. (`Breakdown.CellCert.GivenFields.AdjointInternal.good_adjoint`)

**Extract adjoint regularity.** The packaged adjoint field properties imply the reduction's adjoint regularity condition for the field and its first two classical derivatives. (`Breakdown.CellCert.GivenFields.AdjointInternal.regular_of_good`)

**State the pressure regularity properties.** This proposition packages L² membership, almost everywhere differentiability, a locally integrable weak gradient, a radial weighted L² gradient, and a gradient bound by the minimum of inverse radius and inverse radius cubed. (`Breakdown.CellCert.GivenFields.AdjointInternal.GoodScalar`)

**The pressure decay weight is nonnegative.** The minimum of inverse radius and inverse radius cubed is nonnegative at every point. (`Breakdown.CellCert.GivenFields.AdjointInternal.min_nonneg'`)

**Gradients preserve sums.** At a point where two scalar functions are differentiable, the gradient of their sum equals the sum of their gradients. (`Breakdown.CellCert.GivenFields.AdjointInternal.gradientAt_add`)

**Gradients preserve real scaling.** At a point where a scalar function is differentiable, scaling the function by a real constant scales its gradient by the same constant. (`Breakdown.CellCert.GivenFields.AdjointInternal.gradientAt_smul`)

**Zero pressure has the properties.** The zero scalar field satisfies the packaged pressure regularity properties. (`Breakdown.CellCert.GivenFields.AdjointInternal.scalar_zero`)

**Add pressures with the properties.** The sum of two scalar fields satisfying the packaged pressure regularity properties satisfies the same properties. (`Breakdown.CellCert.GivenFields.AdjointInternal.scalar_add`)

**Scale pressure with the properties.** Every real scalar multiple of a scalar field satisfying the packaged pressure regularity properties satisfies the same properties. (`Breakdown.CellCert.GivenFields.AdjointInternal.scalar_smul`)

**Bound the weighted pressure decay.** Radius times the minimum of inverse radius and inverse radius cubed is at most four times (1 + radius) raised to −2. (`Breakdown.CellCert.GivenFields.AdjointInternal.weight_min`)

**Construct a regular pressure field.** For valid chart parameters and pressure data, the constructed pressure satisfies the packaged scalar regularity properties. (`Breakdown.CellCert.GivenFields.AdjointInternal.good_pressureOf`)

**An adjoint pressure has the properties.** For valid chart parameters and auxiliary data, every evaluated adjoint pressure satisfies the packaged scalar regularity properties. (`Breakdown.CellCert.GivenFields.AdjointInternal.good_pressure`)

**Supply adjoint solenoidality and size.** For valid chart and auxiliary data realizing a certificate's adjoint and sharp fields with matching symmetry order, every active adjoint in the parameter box is an L² solenoidal symmetry class field and its sharp field belongs to L². (`Breakdown.CellCert.GivenFields.adjointSolenoidal_of_given`)

**Supply adjoint derivative regularity.** For valid chart parameters and auxiliary data, each evaluated adjoint field and its first two classical derivatives satisfy the reduction's adjoint regularity condition. (`Breakdown.CellCert.GivenFields.adjointRegular_of_given`)

**Supply adjoint pressure regularity.** For valid chart parameters and auxiliary data, each adjoint pressure has the stated L², weak gradient, radial weighted L² gradient, and almost everywhere inverse radius decay bounds. (`Breakdown.CellCert.GivenFields.adjointPressure_of_given`)

### Breakdown.FracCell.GivenAuxAdjointCore

This file proves the modewise smoothness, solenoidality, symmetry, far decay, and pressure estimates that support the supplied adjoint field contracts in the cell certificate route.

**Assemble a sum from its components.** Assembling a vector from finite sums of coordinates equals the finite sum of the vectors assembled from each coordinate function. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.ofComponents_sum`)

**Express a field as a sum of modes.** The constructed field equals the finite sum of its mode fields, each multiplied by the scalar one. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.field_modes`)

**Smoothness of an admissible mode.** For valid chart parameters and valid field data with high order parameter three, every included mode field is continuously differentiable. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.mode_contDiff`)

**Smoothness of the complete field.** For valid chart parameters and valid field data with high order parameter three, the complete constructed field is continuously differentiable. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.field_contDiff`)

**Nonzero modes have zero divergence.** When the chart symmetry order and the mode index are nonzero, the reduced divergence of that wave mode is zero for all chart coordinates and phase parameters. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.wave_div_zero`)

**The constructed field is divergence free.** For valid chart parameters and valid field data with high order parameter three, the constructed field has zero divergence everywhere. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.field_divergence`)

**Complexification preserves far decay.** Viewing a real field as a complex field preserves its specified far decay property. (`_private.Breakdown.FracCell.GivenAuxAdjointCore.0.Breakdown.CellCert.GivenFields.AdjointCoreInternal.far_ofReal`)

**Taking real parts preserves far decay.** Taking the real part of a complex field preserves its specified far decay property. (`_private.Breakdown.FracCell.GivenAuxAdjointCore.0.Breakdown.CellCert.GivenFields.AdjointCoreInternal.far_re`)

**Read a coordinate insertion map.** The stated continuous linear map from scalars to vectors inserts its input into the chosen coordinate and sets the others to zero. (`_private.Breakdown.FracCell.GivenAuxAdjointCore.0.Breakdown.CellCert.GivenFields.AdjointCoreInternal.single_clm`)

**An admissible mode has cubic decay.** For valid chart parameters and valid field data with high order parameter three, every included mode field satisfies the far decay property with exponent three. (`_private.Breakdown.FracCell.GivenAuxAdjointCore.0.Breakdown.CellCert.GivenFields.AdjointCoreInternal.mode_farDecay`)

**Bound a mode and its far derivatives.** For valid chart parameters and field data with high order three, every included mode has far field bounds of orders radius to −3 for its value, radius to −4 for its derivative, and radius to −5 for the derivative's local Lipschitz constant. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.mode_far`)

**Add local Lipschitz bounds.** A finite sum of functions that are Lipschitz on the same set is Lipschitz there with constant equal to the sum of their constants. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.slopeOn_sum_le`)

**Bound a sum by weighted constants.** If each term has norm at most its constant times a nonnegative common weight, the sum has norm at most the sum of the absolute constants times that weight. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.norm_sum_le_weight`)

**Bound the field and its far derivatives.** For valid chart parameters and field data with high order three, the full field has the stated inverse cubic value, inverse quartic derivative, and inverse fifth local derivative Lipschitz bounds outside a radius at least one. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.field_far`)

**Replace radius by one plus radius.** For a ≥ 0 and r ≥ 1, r raised to −a is at most 2 raised to a times (1 + r) raised to −a. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.far_weight`)

**Introduce a bounded region weight.** For a ≥ 0 and 0 ≤ r ≤ R, the product of (1 + R) raised to a and (1 + r) raised to −a is at least one. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.near_weight`)

**Join near and far decay bounds.** For a nonnegative exponent and radius at least one, a uniform inner bound and an inverse power outer bound combine into a global bound by a constant times (1 + radius) raised to the negative exponent. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.weight_glue`)

**Bound a continuous function on a ball.** A continuous real function on three dimensional space has a uniform upper bound on every closed ball centered at zero. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.ball_bound`)

**Global cubic decay of the field.** For valid chart parameters and valid field data with high order three, the field is globally bounded by a constant times (1 + radius) raised to −3. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.field_decay`)

**Global quartic decay of the derivative.** For valid chart parameters and valid field data with high order three, the field derivative is globally bounded by a constant times (1 + radius) raised to −4. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.field_gradDecay`)

**The derivative is Lipschitz on each ball.** For valid chart parameters and field data with high order three, the field derivative has a Lipschitz bound on each closed ball centered at zero. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.field_ballSlope`)

**Join local Lipschitz bounds globally.** A function that is Lipschitz on the stated central ball, uniformly bounded everywhere, and uniformly Lipschitz on unit balls centered outside that ball is globally Lipschitz. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.slope_glue`)

**Bound a scaled real constant.** For a weight between zero and one, a real constant times that weight is at most the absolute value of the constant. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.le_abs_of_weight`)

**The field derivative is Lipschitz.** For valid chart parameters and valid field data with high order three, the field derivative is globally Lipschitz with some nonnegative constant. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.field_gradSlope`)

**Fifth order second derivative decay.** For valid chart parameters and valid field data with high order three, the second derivative is bounded almost everywhere by a constant times (1 + radius) raised to −5. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.field_secondDecay`)

**Read the first coordinate of a turn.** The first coordinate after a discrete turn is cos(2π/m) times the first coordinate minus sin(2π/m) times the second. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.turn0`)

**Read the second coordinate of a turn.** The second coordinate after a discrete turn is sin(2π/m) times the first coordinate plus cos(2π/m) times the second. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.turn1`)

**A discrete turn preserves height.** A discrete turn leaves the third coordinate unchanged. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.turn2`)

**A discrete turn preserves norm.** A discrete turn leaves the Euclidean norm unchanged. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.norm_turn`)

**Track the angle of a discrete turn.** For positive symmetry order m, multiplying the angle after a turn by the integer nm changes its original value only by an integer multiple of 2π. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.angle_turn`)

**The mode phase respects discrete turns.** For a positive chart symmetry order, the complex mode phase is unchanged by one discrete turn. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.phase_turn`)

**Read an assembled vector coordinate.** Each coordinate of a vector assembled from a coordinate function equals that function's value at the coordinate. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.ofComponents_apply`)

**Separate the real mode coefficients.** Taking the real part of the stated complex weighted sum commutes with forming the three real scalar coordinate contributions. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.re_lin`)

**Define a moving frame coefficient.** This defines each real field coefficient by summing the phase weighted reduced mode coefficient, multiplying by the decay factor, and taking its real part. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.coefOf`)

**Express the field in its moving frame.** Each coordinate of the constructed field is the sum of its three real coefficients times the corresponding radial, polar, and azimuthal frame coordinates. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.field_comp`)

**Frame coefficients respect turns.** For a positive chart symmetry order, each real moving frame coefficient is unchanged by one discrete turn. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.coef_turn`)

**The field respects discrete turns.** For a positive chart symmetry order, evaluating the constructed field at a turned point equals turning its value at the original point. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.field_turn`)

**The selected cell index is in range.** For a breakpoint list beginning at zero and ending at one, the selected cell index is less than the number of cells for every input. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.cellIndex_lt`)

**The cell index at zero is zero.** For a strictly increasing breakpoint list beginning at zero, the selected cell index at zero equals zero. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.cellIndex_zero`)

**An odd spline vanishes on the equator.** A spline in the stated odd class has zero half domain evaluation at height zero for every radial chart coordinate. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.evalHalf_zero`)

**Odd spline evaluation changes sign.** If a spline's half domain evaluation vanishes at height zero, its odd extension changes sign when height is negated. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.evalOdd_neg`)

**Even spline evaluation keeps its sign.** The even extension of a spline is unchanged when height is negated. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.evalEven_neg`)

**An odd function has an even derivative.** The height derivative of a function odd in height is even in height. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.hd_odd`)

**An even function has an odd derivative.** The height derivative of a function even in height is odd in height. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.hd_even`)

**Twisted scaling preserves oddness.** The twisted scaling operator preserves oddness in the height coordinate. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.ts_odd`)

**Twisted scaling preserves evenness.** The twisted scaling operator preserves evenness in the height coordinate. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.ts_even`)

**Track reduced field parity.** For valid field data with high order three and an included mode, negating height preserves the radial and azimuthal reduced coefficients and negates the polar coefficient. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.reduced_neg`)

**Reflection fixes the first coordinate.** The mirror reflection leaves the first coordinate unchanged. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.mir0`)

**Reflection fixes the second coordinate.** The mirror reflection leaves the second coordinate unchanged. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.mir1`)

**Reflection reverses height.** The mirror reflection negates the third coordinate. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.mir2`)

**Reflection preserves norm.** The mirror reflection preserves the Euclidean norm. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.norm_mirror`)

**Track reflected frame coefficients.** For valid field data with high order three, reflection preserves the radial and azimuthal real coefficients and negates the polar coefficient. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.coef_mirror`)

**The field respects reflection.** For valid field data with high order three, evaluating the field at a reflected point equals reflecting its value at the original point. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.field_mirror'`)

**Supply the field reflection symmetry.** For valid chart parameters and field data with high order three, the constructed field commutes with reflection at every point. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.field_mirror`)

**Supply both field symmetries.** For valid chart parameters and field data with high order three, the constructed field commutes with both the chart's discrete turn and mirror reflection. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.field_class`)

**Bound an atom term near infinity.** For valid chart parameters and an admissible atom spline, the norm of its atom term is bounded everywhere by a constant times the squared complementary radial chart coordinate. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.atomTerm_tail`)

**Sum fields with a common decay weight.** A finite sum of complex fields each bounded by some constant times the same weight admits a bound of the same form. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.sum_tail`)

**Bound the decay factor by zero and one.** For valid chart parameters, the decay factor is nonnegative and at most one everywhere. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.decay_le_one`)

**Bound the complementary chart weight.** For valid chart parameters, the squared complementary radial chart coordinate is at most the square of the maximum of the chart length and one times (1 + radius) raised to −2. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.sq_weight`)

**Bound a vector by its coordinates.** The norm of a vector with three real coordinates is at most the sum of their absolute values. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.norm_ofComponents_le`)

**Measurability from three coordinates.** A vector field assembled from three measurable real coordinate functions is measurable. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.measurable_ofComponents3`)

**An atom has inverse square decay.** For valid chart parameters and atom data, the constructed atom is almost everywhere strongly measurable and bounded everywhere by a constant times (1 + radius) raised to −2. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.atom_bound`)

**Bound a cell index by the list length.** The selected cell index is at most the breakpoint list length for every input. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.cellIndex_le_length`)

**Bound spline values on the chart square.** Every stored spline evaluation, with either parity choice, is uniformly bounded when both chart coordinates have absolute value at most one. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.spline_bound`)

**Every mode phase has norm one.** The complex mode phase has norm one at every point for all parameters. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.norm_modePhase`)

**The mode phase is measurable.** For every chart, mode index, and phase parameter, the mode phase is measurable in space. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.modePhase_measurable`)

**Measurability of chart spline values.** Evaluating a spline at the radial and height chart coordinates gives a measurable spatial function for either parity choice. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.evalChart_measurable`)

**Pressure shapes are measurable.** Every pressure shape built from the stated chart parameters, natural orders, and spline is measurable. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.shape_measurable`)

**Bound a pressure shape near infinity.** For valid chart parameters and high order at least two, a pressure shape is bounded by a constant times the squared complementary radial chart coordinate. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.shape_bound`)

**Chart coordinates are smooth off zero.** For valid chart parameters, the radial and height chart coordinate maps are continuously differentiable at every nonzero point. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.chartMap_contDiffAt`)

**The phase is smooth away from its cut.** At a point whose second coordinate is nonzero, the mode phase is continuously differentiable. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.phase_contDiffAt`)

**Differentiate a spline inside its cells.** For valid chart parameters, nonzero third coordinate, and radial and absolute height coordinates avoiding all spline breakpoints, the even spline evaluated in chart coordinates is differentiable at that point. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.evalChart_differentiableAt`)

**Almost everywhere pressure derivatives.** For valid chart parameters, every constructed pressure field is differentiable almost everywhere. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.pressure_diff`)

**Bound the pressure derivative.** For valid chart parameters and pressure data, the derivative norm is bounded almost everywhere by a constant times the squared complementary chart coordinate divided by radius. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.pressure_slope`)

**The constructed pressure is measurable.** Every constructed pressure field is measurable for all chart parameters, pressure data, and phase parameters. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.pressure_measurable`)

**The constructed pressure is bounded.** For valid chart parameters and pressure data, the absolute pressure is uniformly bounded throughout space. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.pressure_bounded`)

**The pressure gradient is a weak gradient.** For valid chart parameters and pressure data, the classical pressure gradient satisfies the reduction's weak scalar gradient identity. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.pressure_weak`)

**Turn chart slope bounds into decay.** For r > 0, 0 ≤ s ≤ 1, c ≥ 1, and s ≤ c/(1 + r), s²/r is at most c² times the minimum of inverse radius and inverse radius cubed. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.slope_weight`)

**Bound the gradient by the derivative.** At every point, the gradient norm of a scalar function is at most three times its Fréchet derivative norm. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.norm_gradientAt_le`)

**Bound pressure gradients near and far.** For valid chart parameters and pressure data, the gradient norm is bounded almost everywhere by a constant times the minimum of inverse radius and inverse radius cubed. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.pressure_gradBound`)

**Collect the pressure analytic properties.** For valid chart parameters and pressure data, the pressure is almost everywhere strongly measurable, has inverse square decay, is differentiable almost everywhere, and has the stated weak gradient and near and far gradient bounds. (`Breakdown.CellCert.GivenFields.AdjointCoreInternal.pressure_core`)

### Breakdown.FracCell.GivenAuxAtomAxis

This file factors the endpoint vanishing spline pieces to remove the apparent angular singularity and prove first derivative continuity of admissible atom terms on the nonzero vertical axis.

**Factor the boundary value difference.** A polynomial minus its value with the second variable set to one is divisible by that variable minus one. (`Breakdown.CellCert.GivenFields.AtomAxisInternal.dvd_sub_atSecond`)

**Factor an axis vanishing polynomial.** A polynomial whose second variable specialization at one vanishes has a factor of one minus that variable. (`Breakdown.CellCert.GivenFields.AtomAxisInternal.factor_of_atSecond`)

**Differentiate past a constant factor.** If a polynomial factor has zero derivative in the first variable, every iterated first variable derivative of its product equals that factor times the corresponding derivative of the other polynomial. (`Breakdown.CellCert.GivenFields.AtomAxisInternal.tDeriv_mul_left`)

**The axis factor has zero radial partial.** The first variable partial derivative of one minus the second variable is zero. (`Breakdown.CellCert.GivenFields.AtomAxisInternal.pderiv_one_sub`)

**The second variable ignores the first.** The first variable partial derivative of the second variable is zero. (`Breakdown.CellCert.GivenFields.AtomAxisInternal.pderiv_X_one`)

**Specialization preserves products.** Setting the first variable to a complex constant commutes with multiplying polynomials. (`Breakdown.CellCert.GivenFields.AtomAxisInternal.atFirst_mul`)

**Specialization keeps the axis factor.** Setting the first variable to any constant leaves one minus the second variable unchanged. (`Breakdown.CellCert.GivenFields.AtomAxisInternal.atFirst_one_sub`)

**Specialization keeps the second variable.** Setting the first variable to any constant leaves the second variable unchanged. (`Breakdown.CellCert.GivenFields.AtomAxisInternal.atFirst_X_one`)

**The axis factor is a nonzero polynomial.** The polynomial one minus the second variable is nonzero. (`Breakdown.CellCert.GivenFields.AtomAxisInternal.one_sub_ne`)

**Choose the polynomial axis quotient.** This chooses a quotient of the last height cell polynomial by one minus the second variable when such a quotient exists, and returns zero otherwise. (`Breakdown.CellCert.GivenFields.AtomAxisInternal.quotPiece`)

**Read the chosen axis quotient.** When the last height cell polynomial has a factor of one minus the second variable, multiplying that factor by the chosen quotient recovers the polynomial. (`Breakdown.CellCert.GivenFields.AtomAxisInternal.quotPiece_spec`)

**Build the axis quotient spline.** This defines a spline with the original radial breakpoints and height breakpoints zero and one, whose pieces are the second variable times the chosen axis quotient polynomials. (`Breakdown.CellCert.GivenFields.AtomAxisInternal.quotSpline`)

**Two distinct endpoints need two entries.** A list beginning at zero and ending at one has at least two entries. (`Breakdown.CellCert.GivenFields.AtomAxisInternal.length_two`)

**Interior breakpoints are below one.** In a strictly increasing list ending at one, every breakpoint remaining after deleting both endpoints is less than one. (`Breakdown.CellCert.GivenFields.AtomAxisInternal.interior_lt_one`)

**Select the final cell above all breaks.** If an input is at least every interior breakpoint, its selected cell index is the number of cells minus one. (`Breakdown.CellCert.GivenFields.AtomAxisInternal.cellIndex_top`)

**The cell index stays within range.** For a breakpoint list with at least two entries, every selected cell index is less than the number of cells. (`Breakdown.CellCert.GivenFields.AtomAxisInternal.cellIndex_lt`)

**Factor every nonzero harmonic axis cell.** For an admissible atom spline with nonzero harmonic index, every valid radial row of its final height cell factors as one minus the height variable times its chosen quotient. (`Breakdown.CellCert.GivenFields.AtomAxisInternal.piece_factor`)

**The quotient spline has the stated class.** For an admissible atom spline with nonzero harmonic index, the quotient construction belongs to the stated odd spline class with one derivative in each coordinate. (`Breakdown.CellCert.GivenFields.AtomAxisInternal.quotSpline_class`)

**Factor spline values near the axis.** For an admissible atom spline with nonzero harmonic index and positive height above every interior height breakpoint, height times the original half domain value equals one minus height times the odd quotient spline value. (`Breakdown.CellCert.GivenFields.AtomAxisInternal.evalHalf_factor`)

**Encode the horizontal plane as ℂ.** This defines the complex horizontal coordinate whose real and imaginary parts are the first two spatial coordinates. (`Breakdown.CellCert.GivenFields.AtomAxisInternal.planeW`)

**The horizontal coordinate is smooth.** The map from three dimensional space to its complex horizontal coordinate is smooth of every finite order. (`Breakdown.CellCert.GivenFields.AtomAxisInternal.planeW_contDiff`)

**Split the squared spatial norm.** The squared spatial norm equals the squared norm of the complex horizontal coordinate plus the squared height coordinate. (`Breakdown.CellCert.GivenFields.AtomAxisInternal.norm_sq_split`)

**Complexification preserves smoothness.** Viewing a real function as complex valued preserves continuous differentiability at a point. (`Breakdown.CellCert.GivenFields.AtomAxisInternal.ofReal_cd`)

**The norm is smooth away from zero.** The spatial norm is continuously differentiable at every nonzero point. (`Breakdown.CellCert.GivenFields.AtomAxisInternal.norm_cd`)

**Coordinate functions are smooth.** Every spatial coordinate function is continuously differentiable at every point. (`Breakdown.CellCert.GivenFields.AtomAxisInternal.coord_cd`)

**The height ratio is smooth off zero.** The height ratio is continuously differentiable at every nonzero point. (`Breakdown.CellCert.GivenFields.AtomAxisInternal.heightRatio_cd`)

**The radial chart is smooth off zero.** For valid chart parameters, the radial chart coordinate is continuously differentiable at every nonzero point. (`Breakdown.CellCert.GivenFields.AtomAxisInternal.chartT_cd`)

**The decay factor is smooth off zero.** For valid chart parameters, the decay factor is continuously differentiable at every nonzero point. (`Breakdown.CellCert.GivenFields.AtomAxisInternal.decay_cd`)

**The logarithmic phase is smooth.** For valid chart parameters, the logarithmic phase is continuously differentiable at every point. (`Breakdown.CellCert.GivenFields.AtomAxisInternal.logPhase_cd`)

**Define the expression near the axis.** This defines an alternative atom expression using the decay and logarithmic phase factors, planar powers and angular phase, the stated radial normalizations and sign, and the odd quotient spline. (`Breakdown.CellCert.GivenFields.AtomAxisInternal.axisForm`)

**Identify the atom near either axis.** For a nonzero admissible harmonic, sign ±1, and a nonzero point in the stated final height cell with positive denominators, the decayed atom term equals its quotient based axis expression. (`Breakdown.CellCert.GivenFields.AtomAxisInternal.point_identity`)

**Smoothness on the nonzero axis.** For valid chart parameters and an admissible nonzero harmonic atom spline, the decayed atom term is continuously differentiable at every nonzero point on the vertical axis. (`Breakdown.CellCert.GivenFields.AtomAxisInternal.axis_main`)

**Supply atom smoothness on the axis.** For valid chart parameters, a ≤ 1, an admissible atom spline, and the stated zero harmonic compatibility, every nonzero harmonic decayed atom term is continuously differentiable on the vertical axis away from zero. (`Breakdown.CellCert.GivenFields.atomScalar_contDiffAt_axis`)

### Breakdown.FracCell.GivenAuxAtomGrad

This file extends derivative bounds from points off the vertical axis to the axis and supplies a global decay bound for admissible atom gradients.

**Compare nearby inverse square weights.** If the distance from z to y is at most half of 1 + the norm of y, the inverse square weight at z is at most four times that weight at y. (`Breakdown.CellCert.GivenFields.AtomGradInternal.weight_shift`)

**Bound a step leaving the axis.** For a function continuous at a point on the vertical axis and differentiable off it with the stated inverse square derivative bound, a sufficiently short positive step in a nonvertical direction satisfies the displayed increment bound. (`Breakdown.CellCert.GivenFields.AtomGradInternal.ray_step`)

**Extend a derivative bound onto the axis.** If a function has the stated nonnegative inverse square derivative bound off the vertical axis and is differentiable at an axis point, its derivative there satisfies the same weight bound with four times the constant. (`Breakdown.CellCert.GivenFields.AtomGradInternal.axis_bound`)

**Supply a global atom gradient bound.** For valid chart parameters, a ≤ 1, an admissible atom spline, and zero harmonic compatibility, the derivative norm of the decayed atom term is everywhere bounded by a constant times (1 + radius) raised to −2. (`Breakdown.CellCert.GivenFields.atomScalar_gradBound`)

### Breakdown.FracCell.GivenAuxAtomGradOff

This file combines spline endpoint vanishing with chart and phase derivative estimates to bound admissible atom gradients away from the vertical axis, supporting the auxiliary field regularity contracts.

**Evaluate after first specialization.** Evaluating a polynomial after setting its first variable to c equals evaluating the original polynomial with first coordinate c and the original second coordinate. (`Breakdown.CellCert.GivenFields.AtomGradOffInternal.eval_atFirst'`)

**Evaluate after second specialization.** Evaluating a polynomial after setting its second variable to c equals evaluating the original polynomial with its original first coordinate and second coordinate c. (`Breakdown.CellCert.GivenFields.AtomGradOffInternal.eval_atSecond'`)

**Bound the cell index by the final index.** Every selected cell index is at most the breakpoint list length minus two, with subtraction taken in natural numbers. (`Breakdown.CellCert.GivenFields.AtomGradOffInternal.cellIndex_le'`)

**Two distinct endpoints need two entries.** A list beginning at zero and ending at one has at least two entries. (`Breakdown.CellCert.GivenFields.AtomGradOffInternal.two_le_length'`)

**Interior breakpoints are below one.** In a strictly increasing list ending at one, every breakpoint remaining after deleting both endpoints is less than one. (`Breakdown.CellCert.GivenFields.AtomGradOffInternal.interior_lt_one'`)

**Interior breakpoints are positive.** In a strictly increasing list beginning at zero, every breakpoint remaining after deleting both endpoints is positive. (`Breakdown.CellCert.GivenFields.AtomGradOffInternal.interior_pos'`)

**The cell index at zero is zero.** For a strictly increasing breakpoint list beginning at zero, the selected cell index at zero equals zero. (`Breakdown.CellCert.GivenFields.AtomGradOffInternal.cellIndex_zero'`)

**The cell index at one is the last.** For a strictly increasing breakpoint list ending at one, the selected cell index at one equals the list length minus two in natural number arithmetic. (`Breakdown.CellCert.GivenFields.AtomGradOffInternal.cellIndex_one'`)

**The cell index lies within range.** For a breakpoint list beginning at zero and ending at one, every selected cell index is less than the number of cells. (`Breakdown.CellCert.GivenFields.AtomGradOffInternal.cell_lt`)

**The atom spline vanishes at the origin.** An admissible atom spline evaluates to zero at radial chart coordinate zero for every height. (`Breakdown.CellCert.GivenFields.AtomGradOffInternal.spline_t0`)

**An atom spline vanishes at the far end.** An admissible atom spline evaluates to zero at radial chart coordinate one for every height. (`Breakdown.CellCert.GivenFields.AtomGradOffInternal.spline_t1`)

**Nonzero harmonics vanish on the axis.** An admissible atom spline with nonzero harmonic index has zero half domain value at height coordinate one for every radial coordinate. (`Breakdown.CellCert.GivenFields.AtomGradOffInternal.spline_x1`)

**Bound atom spline values and derivatives.** An admissible atom spline has a nonnegative uniform constant giving the stated endpoint vanishing value bound, the additional axis factor for nonzero scalar harmonics, a derivative norm bound, and a height derivative bound on the chart rectangle. (`Breakdown.CellCert.GivenFields.AtomGradOffInternal.spline_bounds`)

**Write the angular weight in coordinates.** At every nonzero point, the angular weight equals the squared horizontal norm divided by the squared spatial norm and also equals one minus the squared height ratio. (`Breakdown.CellCert.GivenFields.AtomGradOffInternal.q_eq`)

**The horizontal norm is at most the norm.** The norm of the complex horizontal coordinate is at most the full spatial norm. (`Breakdown.CellCert.GivenFields.AtomGradOffInternal.plane_le`)

**The absolute height ratio is at most one.** The absolute value of the height ratio is at most one at every point. (`Breakdown.CellCert.GivenFields.AtomGradOffInternal.height_abs_le`)

**Differentiate and bound the spatial norm.** At every nonzero point, the spatial norm has its classical Fréchet derivative and that derivative has operator norm at most one. (`Breakdown.CellCert.GivenFields.AtomGradOffInternal.normD`)

**Subtract horizontal coordinates.** The difference of two complex horizontal coordinates equals the complex horizontal coordinate of the spatial difference. (`Breakdown.CellCert.GivenFields.AtomGradOffInternal.plane_sub`)

**Horizontal coordinates are Lipschitz.** The map to the complex horizontal coordinate is Lipschitz with constant one. (`Breakdown.CellCert.GivenFields.AtomGradOffInternal.plane_slope`)

**Differentiate horizontal coordinates.** The map to the complex horizontal coordinate is differentiable over the reals everywhere. (`Breakdown.CellCert.GivenFields.AtomGradOffInternal.plane_diff`)

**Bound the horizontal derivative.** The complex horizontal coordinate has its classical Fréchet derivative at every point, with operator norm at most one. (`Breakdown.CellCert.GivenFields.AtomGradOffInternal.planeD`)

**Bound the horizontal norm derivative.** Where the horizontal coordinate is nonzero, its norm has its classical Fréchet derivative with operator norm at most one. (`Breakdown.CellCert.GivenFields.AtomGradOffInternal.planeNormD`)

**Differentiate a reciprocal.** At a point where a differentiable real function is nonzero, its reciprocal has derivative equal to the original derivative multiplied by minus the inverse square of its value. (`Breakdown.CellCert.GivenFields.AtomGradOffInternal.invD`)

**Compute the reciprocal derivative norm.** Multiplying a real continuous linear map by minus the inverse square of b multiplies its norm by the inverse square of b. (`Breakdown.CellCert.GivenFields.AtomGradOffInternal.invD_norm`)

**Bound the chart coordinate derivatives.** For valid chart parameters and a nonzero point, radial and height chart derivatives exist with norms bounded respectively by the chart length divided by (radius + chart length)² and by 2/radius. (`Breakdown.CellCert.GivenFields.AtomGradOffInternal.chart_derivs`)

**Differentiate the angular square root.** Away from the vertical axis, the square root of the angular weight equals horizontal norm divided by spatial norm, and its complex valued derivative has norm at most 2/radius. (`Breakdown.CellCert.GivenFields.AtomGradOffInternal.sqrt_factor`)

**Express an integer angular phase.** For a nonzero complex number and integer k, exp(i times k times its argument) equals the kth integer power of the number divided by its norm. (`Breakdown.CellCert.GivenFields.AtomGradOffInternal.exp_arg_zpow'`)

**Bound the angular phase derivative.** Away from the vertical axis, the integer angular phase has a derivative with norm at most twice the absolute mode index divided by the horizontal norm. (`Breakdown.CellCert.GivenFields.AtomGradOffInternal.angle_factor`)

**Bound the radial phase derivative.** For valid chart parameters, the decay factor times the logarithmic complex phase has norm at most one and, away from zero, has a derivative bounded by a nonnegative constant divided by radius plus chart length. (`Breakdown.CellCert.GivenFields.AtomGradOffInternal.amp_factor`)

**Supply an atom bound away from the axis.** For valid chart parameters, a ≤ 1, an admissible atom spline, and zero harmonic compatibility, the decayed atom term is differentiable off the vertical axis and its derivative obeys a nonnegative inverse square decay bound. (`Breakdown.CellCert.GivenFields.atomScalar_offAxisGrad`)

### Breakdown.FracCell.GivenAuxAtomSlope

This file joins the near-origin, intermediate-annulus and far-field estimates into the weighted derivative bound for each scalar atom. **Reading context:** Appendix B: represented fields and the auxiliary estimates used by the profile, pin and adjoint reductions (B.1 and B.9–B.13).

**Theorem · Reciprocal form of the slope weight.** For positive radius, the slope weight is the reciprocal of the radius times the cube of one plus the radius. [`slope_w_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlope.lean#L17).

**Theorem · Radii in a half-radius ball.** A point in the ball of radius half the centre's norm has norm between one half and three halves of that norm. [`slope_ball_norm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlope.lean#L21).

**Theorem · Closed annuli are compact.** The set of spatial points whose norms lie between two fixed bounds is compact. [`slope_annulus_compact`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlope.lean#L29).

**Theorem · Distance bound gives Lipschitz control.** A common distance bound on a set gives a Lipschitz constant after converting the bound to a nonnegative real. [`slope_bound_of_slope`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlope.lean#L36).

**Theorem · Norm under inverse scaling.** Scaling by the inverse of a positive radius divides the norm by that radius. [`slope_scaled_norm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlope.lean#L41).

**Theorem · Distance under inverse scaling.** Scaling both points by the inverse of a positive radius multiplies their distance by the same inverse. [`slope_scaled_dist`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlope.lean#L44).

**Theorem · Distance with a fixed first coordinate.** Pairs with equal first coordinate have the same distance as their spatial coordinates. [`slope_prod_dist`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlope.lean#L48).

**Theorem · Scaling into a fixed annulus.** A point with norm between half and three halves of a positive radius rescales into the closed annulus with radii one half and three halves. [`slope_in_annulus`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlope.lean#L51).

**Theorem · Gluing near and far slope bounds.** Compatible near-origin and far-field rescalings with locally Lipschitz derivatives give a ballwise bound weighted by the inverse radius and the inverse cube of one plus the radius. [`slope_glue`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlope.lean#L59).

**Theorem · Weighted slope bound for an atom.** An admissible scalar atom with exponent at most one has a derivative Lipschitz bound on each half-radius ball, weighted by the inverse radius and the inverse cube of one plus the radius. [`atomScalar_slopeBound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlope.lean#L177).

### Breakdown.FracCell.GivenAuxAtomSlopeFar

This file factors the double zero at the outer spline endpoint and uses it to build the far-field rescaling of the atom derivative. **Reading context:** Appendix B: represented fields and the auxiliary estimates used by the profile, pin and adjoint reductions (B.1 and B.9–B.13).

**Theorem · Factoring a first-coordinate remainder.** Subtracting evaluation at first coordinate one leaves a polynomial divisible by the first coordinate minus one. [`dvd_sub_atFirst`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeFar.lean#L22).

**Theorem · One zero gives a linear factor.** A polynomial vanishing at first coordinate one has a factor one minus that coordinate. [`factor_one`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeFar.lean#L45).

**Theorem · The endpoint factor vanishes.** Evaluating one minus the first polynomial variable at first coordinate one gives zero. [`atFirst_one_sub_X0`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeFar.lean#L51).

**Theorem · A double zero gives a square factor.** Vanishing of a polynomial and its first-coordinate derivative at one gives a squared endpoint factor. [`factor_two`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeFar.lean#L54).

**Definition · Quotient by the squared endpoint factor.** The quotient selects a polynomial after removing the squared endpoint factor when such a factorization exists, and returns zero otherwise. [`quot2`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeFar.lean#L69).

**Reader note.** The definition uses choice for an existing quotient and a zero fallback; later hypotheses establish the factorization before it is used.

**Theorem · The chosen quotient factors the input.** When the polynomial and its first-coordinate derivative vanish at one, the chosen quotient gives the required squared-factor identity. [`quot2_spec`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeFar.lean#L72).

**Theorem · The squared endpoint factor is nonzero.** The square of one minus the first polynomial variable is a nonzero polynomial. [`sq_ne`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeFar.lean#L79).

**Theorem · Height derivatives preserve a factor.** A factor independent of the second polynomial variable can be pulled through every iterated second-coordinate derivative. [`xDeriv_mul_left`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeFar.lean#L84).

**Theorem · The endpoint factor has no height change.** The squared first-coordinate endpoint factor has zero derivative in the second coordinate. [`pderiv_sq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeFar.lean#L93).

**Theorem · Height substitution preserves a factor.** Substituting a second coordinate preserves the squared first-coordinate endpoint factor. [`atSecond_sq_mul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeFar.lean#L96).

**Definition · Spline after removing far-end zeros.** The last-row spline replaces the radial mesh by the interval from zero to one and divides the last radial pieces by the squared endpoint factor. [`lastRow`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeFar.lean#L100).

**Predicate · Double vanishing at the far endpoint.** The far-end condition requires every last-row piece and its first radial derivative to vanish at radial coordinate one. [`AtInfinity`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeFar.lean#L103).

**Theorem · The quotient keeps the spline class.** A spline with the far-end double-zero condition retains its first-order spline class after the last-row quotient construction. [`lastRow_class`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeFar.lean#L107).

**Theorem · A two-point mesh has one cell.** The cell index of the mesh consisting of zero and one is zero for every input. [`lastRow_cell`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeFar.lean#L131).

**Theorem · Far-row factorization of the spline.** Beyond all interior radial breaks, the original spline equals the last-row quotient multiplied by the square of one minus the radial coordinate. [`lastRow_eval`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeFar.lean#L134).

**Predicate · Locally Lipschitz derivative.** Local tameness means that the function has a derivative throughout some ball and that this derivative satisfies one Lipschitz bound there. [`TameAt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeFar.lean#L158).

**Theorem · Bounds from a Lipschitz derivative.** A Lipschitz derivative on a ball gives a uniform derivative bound, a Lipschitz bound for the function, and a bound for its values on that ball. [`tame_bounds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeFar.lean#L162).

**Theorem · Twice smooth gives local tameness.** Twice continuous differentiability at a point supplies a locally Lipschitz derivative there. [`tame_of_contDiffAt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeFar.lean#L190).

**Theorem · Smooth derivative gives tameness.** A continuously differentiable function with locally Lipschitz derivative is locally tame everywhere. [`tame_global`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeFar.lean#L200).

**Theorem · Tameness under local equality.** Two functions that agree near the point have the same local tameness property there. [`tame_congr`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeFar.lean#L209).

**Theorem · Tameness of a composition.** Composing locally tame functions preserves local tameness at the corresponding points. [`tame_comp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeFar.lean#L219).

**Theorem · Tameness of a product.** The product of two locally tame complex functions is locally tame. [`tame_mul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeFar.lean#L256).

**Theorem · A tame neighbourhood and its derivative.** Local tameness gives a neighbourhood on which the function is differentiable and its derivative is Lipschitz. [`tame_region`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeFar.lean#L291).

**Definition · Quadratic angular phase.** The planar phase map multiplies the integer angular exponential by the squared modulus. [`pmap`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeFar.lean#L301).

**Theorem · Quadratic phase has a tame derivative.** Every integer quadratic angular phase has a locally Lipschitz derivative, including at the planar origin. [`pmap_tame`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeFar.lean#L303).

**Theorem · First-order splines are locally tame.** A spline in the first-order class has a locally Lipschitz derivative at every pair of real coordinates. [`spline_tame`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeFar.lean#L306).

**Theorem · Atoms vanish twice at infinity.** The atom-spline conditions imply the far-end double-zero condition. [`atInf_of_atom`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeFar.lean#L310).

**Theorem · The axis quotient keeps far-end zeros.** For a nonzero harmonic, the atom's axis quotient still vanishes twice at the far endpoint. [`atInf_quot`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeFar.lean#L313).

**Theorem · Axis factorization on the last row.** Beyond the angular breaks, the last-row spline and its axis quotient satisfy the identity obtained by multiplying by the angular coordinate and one minus that coordinate. [`axis_half`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeFar.lean#L332).

**Theorem · Angular square root as a norm ratio.** Away from the spatial origin, the angular square root equals planar norm divided by full spatial norm. [`sqrt_q`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeFar.lean#L371).

**Definition · Angular part of the far profile.** The far angular profile combines the integer phase, the prescribed angular power, and the last-row spline. [`Yf`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeFar.lean#L380).

**Theorem · Smooth spatial norm off the origin.** The spatial norm is twice continuously differentiable in the product variables away from the origin. [`cd_norm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeFar.lean#L384).

**Theorem · Smooth spatial coordinate.** Each spatial coordinate is twice continuously differentiable in the product variables. [`cd_coord`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeFar.lean#L387).

**Theorem · Smooth height ratio off the origin.** The height divided by radius is twice continuously differentiable away from the spatial origin. [`cd_height`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeFar.lean#L390).

**Theorem · Smooth planar coordinate.** The complex planar coordinate is twice continuously differentiable in the product variables. [`cd_plane`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeFar.lean#L393).

**Theorem · Smoothness under complex inclusion.** Including a real twice differentiable function into the complex numbers preserves that smoothness. [`cd_ofReal`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeFar.lean#L396).

**Theorem · A spline in smooth coordinates is tame.** Composing a first-order spline with two twice continuously differentiable coordinates gives a locally tame function. [`tame_spline_comp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeFar.lean#L400).

**Theorem · A nonzero planar part excludes zero.** A spatial point with nonzero complex planar coordinate is nonzero. [`ne_of_plane`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeFar.lean#L406).

**Theorem · Far angular profile off the axis.** Off the axis, the far angular profile factors through the quadratic planar phase and explicit norm ratios. [`Y_off`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeFar.lean#L411).

**Theorem · Far angular tameness off the axis.** A valid last-row spline gives a locally tame far angular profile away from the axis. [`Y_tame_off`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeFar.lean#L424).

**Theorem · Positive unit phase as a coordinate.** For angular power and phase both one, the far angular profile uses the complex planar coordinate divided by spatial norm. [`Y_plus`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeFar.lean#L442).

**Theorem · Negative unit phase as a conjugate.** For angular power one and phase minus one, the far angular profile uses the conjugate planar coordinate divided by spatial norm. [`Y_minus`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeFar.lean#L455).

**Definition · Axis factor in the far profile.** The axis factor combines inverse radial powers, the signed height ratio, and the denominator given by radius plus signed height. [`Kf`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeFar.lean#L472).

**Theorem · Far angular factorization at the axis.** For a nonzero harmonic in the last angular cell, the far profile factors through a quadratic phase and the axis quotient spline. [`Y_axis`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeFar.lean#L475).

**Theorem · Far angular tameness on the axis.** The axis cancellation in a nonzero-harmonic atom gives local tameness at every nonzero point of the axis. [`Y_tame_axis`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeFar.lean#L536).

**Theorem · Tameness of the far angular profile.** Admissible atom data with angular power at most one give a locally tame far angular profile away from the spatial origin. [`Y_tame`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeFar.lean#L587).

**Definition · Radial chart at inverse scale.** The far radial coordinate is spatial norm divided by spatial norm plus scale times the chart length. [`tauF`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeFar.lean#L624).

**Definition · Decay and phase at inverse scale.** The far scalar factor combines the rescaled decay power with the logarithmic radial phase. [`Ef`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeFar.lean#L626).

**Definition · Rescaled far atom.** The far profile multiplies its decay-and-phase factor by the angular quotient evaluated at the far radial coordinate. [`Ff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeFar.lean#L630).

**Theorem · The far rescaled atom is locally tame.** For admissible atom data, the far profile is locally tame at nonnegative scale and nonzero spatial position. [`F_tame`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeFar.lean#L633).

**Theorem · Atom factorization at inverse scale.** In the last radial cell, evaluating the atom at inverse scale separates an explicit complex scale factor from the far profile. [`far_identity`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeFar.lean#L660).

**Theorem · Far rescaling of the atom derivative.** The derivative of an admissible scalar atom at inverse scale is a locally Lipschitz profile multiplied by a scalar whose norm is bounded by the cube of the scale. [`atomScalar_fderiv_farScaled`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeFar.lean#L732).

### Breakdown.FracCell.GivenAuxAtomSlopeLocal

This file proves local regularity of the scalar atom derivative, treating points off the axis, the zero harmonic, and axis cancellation separately. **Reading context:** Appendix B: represented fields and the auxiliary estimates used by the profile, pin and adjoint reductions (B.1 and B.9–B.13).

**Predicate · Locally Lipschitz derivative.** Local tameness means that the function has a derivative throughout some ball and that this derivative satisfies one Lipschitz bound there. [`TameAt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeLocal.lean#L25).

**Theorem · Bounds from a Lipschitz derivative.** A Lipschitz derivative on a ball gives a uniform derivative bound, a Lipschitz bound for the function, and a bound for its values on that ball. [`tame_bounds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeLocal.lean#L29).

**Theorem · Twice smooth gives local tameness.** Twice continuous differentiability at a point supplies a locally Lipschitz derivative there. [`tame_of_contDiffAt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeLocal.lean#L57).

**Theorem · A derivative bound gives tameness.** A differentiable function whose derivative is locally Lipschitz is locally tame at every point. [`tame_of_global`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeLocal.lean#L67).

**Theorem · Local derivative Lipschitz bound.** Local tameness supplies a neighbourhood on which the Fréchet derivative has a finite Lipschitz constant. [`tame_slope`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeLocal.lean#L75).

**Theorem · Tameness under local equality.** Two functions that agree near the point have the same local tameness property there. [`tame_congr`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeLocal.lean#L82).

**Theorem · Tameness of a composition.** Composing locally tame functions preserves local tameness at the corresponding points. [`tame_comp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeLocal.lean#L92).

**Theorem · Tameness of a product.** The product of two locally tame complex functions is locally tame. [`tame_mul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeLocal.lean#L129).

**Theorem · Twice smooth norm off the origin.** The spatial norm is twice continuously differentiable at every nonzero point. [`norm2`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeLocal.lean#L166).

**Theorem · Twice smooth coordinate functions.** Each spatial coordinate is twice continuously differentiable everywhere. [`coord2`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeLocal.lean#L169).

**Theorem · Twice smooth height ratio.** The height-to-radius ratio is twice continuously differentiable away from the origin. [`height2`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeLocal.lean#L172).

**Theorem · Twice smooth radial chart.** For valid chart parameters, the compactified radial coordinate is twice continuously differentiable away from the origin. [`chartT2`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeLocal.lean#L175).

**Theorem · Twice smooth decay factor.** For valid chart parameters, the decay factor is twice continuously differentiable away from the origin. [`decay2`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeLocal.lean#L180).

**Theorem · Twice smooth logarithmic phase.** The regularized logarithmic phase is twice continuously differentiable for valid chart parameters. [`logPhase2`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeLocal.lean#L193).

**Theorem · Twice smooth complex inclusion.** Complex inclusion preserves twice continuous differentiability of a real-valued function. [`ofReal2`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeLocal.lean#L200).

**Theorem · Twice smooth planar coordinate.** Combining the first two spatial coordinates into a complex number gives a twice continuously differentiable function. [`plane2`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeLocal.lean#L204).

**Theorem · Smooth integer powers away from zero.** An integer power of a twice continuously differentiable complex function remains twice continuously differentiable where that function is nonzero. [`zpow2`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeLocal.lean#L207).

**Theorem · Integer phase as a unit complex power.** For a nonzero complex number, its integer angular phase equals the corresponding power of its normalized complex direction. [`exp_arg_zpow`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeLocal.lean#L214).

**Theorem · Local tameness of spline evaluation.** Evaluation of a first-order spline has a locally Lipschitz derivative at every pair of coordinates. [`tame_spline`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeLocal.lean#L226).

**Theorem · Local tameness in chart coordinates.** A first-order spline remains locally tame after substitution of the radial chart and a fixed multiple of the height ratio, away from the origin. [`tame_chartSpline`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeLocal.lean#L231).

**Theorem · Local tameness in the standard chart.** A first-order spline composed with the radial chart and height ratio is locally tame away from the origin. [`tame_chartSpline_one`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeLocal.lean#L237).

**Theorem · Scalar atom tameness off the axis.** An admissible scalar atom has a locally Lipschitz derivative wherever its planar coordinate is nonzero. [`tame_offAxis`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeLocal.lean#L242).

**Theorem · Square root of the angular weight.** Away from the origin, the angular square root is the planar norm divided by spatial norm. [`sqrt_q_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeLocal.lean#L290).

**Theorem · Unit phase recovers the planar value.** Multiplying the positive unit angular phase by the planar modulus recovers the complex planar value. [`phase_plus`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeLocal.lean#L305).

**Theorem · Negative phase recovers the conjugate.** Multiplying the negative unit angular phase by the planar modulus recovers the complex conjugate. [`phase_minus`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeLocal.lean#L313).

**Theorem · Tameness of the zero harmonic.** The zero-harmonic atom is locally tame away from the origin when its angular exponent is at most one and equals the absolute phase index. [`tame_harmonicZero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeLocal.lean#L322).

**Theorem · Scalar atom tameness on the axis.** A nonzero-harmonic atom has a locally Lipschitz derivative at every nonzero point of the axis. [`tame_axis`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeLocal.lean#L373).

**Theorem · Atom derivative is locally Lipschitz.** Admissible scalar atoms with angular exponent at most one have locally Lipschitz derivatives on punctured space. [`atomScalar_fderiv_locallySlopeBound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeLocal.lean#L444).

### Breakdown.FracCell.GivenAuxAtomSlopeNear

This file extracts the atom spline's zero at the origin and builds a small-scale derivative profile that stays regular at scale zero. **Reading context:** Appendix B: represented fields and the auxiliary estimates used by the profile, pin and adjoint reductions (B.1 and B.9–B.13).

**Predicate · Locally Lipschitz derivative.** Local tameness means that the function has a derivative throughout some ball and that this derivative satisfies one Lipschitz bound there. [`TameAt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeNear.lean#L23).

**Theorem · Bounds from a Lipschitz derivative.** A Lipschitz derivative on a ball gives a uniform derivative bound, a Lipschitz bound for the function, and a bound for its values on that ball. [`tame_bounds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeNear.lean#L27).

**Theorem · Twice smooth gives local tameness.** Twice continuous differentiability at a point supplies a locally Lipschitz derivative there. [`tame_of_contDiffAt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeNear.lean#L56).

**Theorem · A derivative bound gives tameness.** A differentiable function whose derivative is locally Lipschitz is locally tame at every point. [`tame_of_global`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeNear.lean#L66).

**Theorem · Local derivative Lipschitz bound.** Local tameness supplies a neighbourhood on which the Fréchet derivative has a finite Lipschitz constant. [`tame_slope`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeNear.lean#L74).

**Theorem · Tameness under local equality.** Two functions that agree near the point have the same local tameness property there. [`tame_congr`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeNear.lean#L81).

**Theorem · Tameness of a sum.** The sum of two locally tame functions is locally tame at the same point. [`tame_add`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeNear.lean#L91).

**Theorem · Tameness under a linear map.** Applying a continuous linear map preserves local tameness. [`tame_clm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeNear.lean#L107).

**Theorem · Tameness of a composition.** Composing locally tame functions preserves local tameness at the corresponding points. [`tame_comp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeNear.lean#L117).

**Theorem · Tameness of a product.** The product of two locally tame complex functions is locally tame. [`tame_mul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeNear.lean#L154).

**Theorem · Tameness under negation.** Negating a locally tame function preserves local tameness. [`tame_neg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeNear.lean#L189).

**Theorem · Tameness of a difference.** Subtracting locally tame functions preserves local tameness. [`tame_sub`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeNear.lean#L192).

**Theorem · Local data give tameness.** Differentiability on a neighbourhood and a Lipschitz derivative on that neighbourhood supply local tameness. [`tame_of_local`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeNear.lean#L202).

**Theorem · Neighbourhood form of tameness.** Local tameness supplies neighbourhood differentiability together with a Lipschitz bound for the derivative. [`tame_out`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeNear.lean#L211).

**Definition · Polynomials in real coordinates.** The near-field polynomial evaluator substitutes the two real coordinates as complex polynomial variables. [`nearEv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeNear.lean#L221).

**Theorem · Evaluation after polynomial substitution.** Evaluating a substituted polynomial agrees with first evaluating the substituted variables and then evaluating the original polynomial. [`near_eval_bind`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeNear.lean#L223).

**Theorem · Evaluation at a fixed first coordinate.** Polynomial evaluation after fixing the first coordinate agrees with evaluating the original polynomial at that fixed coordinate. [`nearEv_atFirst`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeNear.lean#L230).

**Theorem · Positive interior radial breaks.** A strictly increasing radial mesh from zero to one has positive interior breaks and one more cell than interior breaks. [`near_mesh`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeNear.lean#L237).

**Theorem · A positive lower bound for a finite list.** A finite list of positive real numbers has a common positive lower bound. [`near_pos_lower`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeNear.lean#L255).

**Theorem · Substitution in a variable product.** Fixing the first coordinate of a polynomial times a coordinate variable substitutes that variable accordingly. [`near_atFirst_mul_X`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeNear.lean#L266).

**Theorem · Removing the value at zero.** Subtracting a polynomial's value at first coordinate zero leaves a factor of the first coordinate. [`near_sub_atFirst_dvd`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeNear.lean#L271).

**Theorem · Height substitution preserves radius.** Substitution in the second coordinate commutes with multiplication by the first polynomial variable. [`near_atSecond_X0_mul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeNear.lean#L292).

**Theorem · Height differentiation preserves radius.** Every iterated second-coordinate derivative commutes with multiplication by the first polynomial variable. [`near_xDeriv_X0_mul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeNear.lean#L296).

**Theorem · Extracting the atom's radial zero.** Near radial coordinate zero, an atom spline factors as the radial coordinate times a first-order spline on a single radial cell. [`near_origin_split`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeNear.lean#L307).

**Definition · Angular profile of the near atom.** The near angular profile combines the integer angular phase, its angular power, and spline evaluation in the height ratio. [`atomAngularProfile`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeNear.lean#L368).

**Theorem · Spatial coordinates are smooth.** Each spatial coordinate is smooth to every finite order. [`ang_coord`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeNear.lean#L372).

**Definition · The complex planar coordinate.** The planar coordinate combines the first and second spatial coordinates as a complex number. [`angPlane`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeNear.lean#L375).

**Theorem · The planar coordinate is smooth.** The complex planar coordinate is smooth to every finite order. [`angPlane_contDiff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeNear.lean#L377).

**Theorem · Angular exponential as an integer power.** Away from zero, the integer angular exponential is the integer power of the normalized planar complex number. [`ang_exp_arg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeNear.lean#L385).

**Theorem · Twice smooth integer powers.** Integer powers preserve twice continuous differentiability where the complex base is nonzero. [`ang_zpow`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeNear.lean#L397).

**Theorem · Spatial squared norm by coordinates.** The squared spatial norm is the sum of the squares of its three coordinates. [`ang_normsq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeNear.lean#L405).

**Theorem · Planar squared norm by coordinates.** The squared planar norm is the sum of the squares of the first two spatial coordinates. [`ang_plane_normsq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeNear.lean#L409).

**Theorem · Angular square root as a radius ratio.** Away from the origin, the square root of the angular weight is planar norm divided by spatial norm. [`ang_sqrt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeNear.lean#L414).

**Theorem · Smooth height ratio in product space.** The height ratio is twice continuously differentiable in the product variables when the spatial point is nonzero. [`ang_height`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeNear.lean#L423).

**Theorem · Angular spline in smooth coordinates.** A first-order angular spline composed with scale and height ratio is locally tame away from the origin. [`ang_spline_tame`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeNear.lean#L429).

**Theorem · Near angular tameness off the axis.** The near angular profile is locally tame wherever the planar coordinate is nonzero. [`ang_offAxis`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeNear.lean#L440).

**Theorem · Negative phase gives conjugation.** The negative unit angular phase times the planar modulus equals the complex conjugate. [`ang_conj_identity`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeNear.lean#L468).

**Theorem · Positive phase gives the identity.** The positive unit angular phase times the planar modulus equals the original complex number. [`ang_id_identity`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeNear.lean#L480).

**Theorem · Low angular powers are locally tame.** When the angular exponent is at most one and matches the absolute phase index, the near angular profile is locally tame away from the origin. [`ang_harmonic`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeNear.lean#L489).

**Theorem · Extracting an angular endpoint zero.** Subtracting evaluation at second coordinate one leaves a factor of the second coordinate minus one. [`near_sub_atSecond_dvd`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeNear.lean#L530).

**Theorem · Polynomial evaluation is smooth.** A complex polynomial evaluated at real coordinate pairs is smooth to every finite order. [`nearEv_contDiff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeNear.lean#L561).

**Theorem · Interior breaks stay below one.** The interior points of a finite increasing mesh ending at one have a common upper bound strictly below one. [`near_upper_gap`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeNear.lean#L580).

**Definition · Quadratic planar phase map.** The near-field planar map multiplies the angular exponential by the squared planar modulus. [`planeMapN`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeNear.lean#L607).

**Theorem · Quadratic planar phase is locally tame.** The quadratic planar phase has a locally Lipschitz derivative for every integer phase index. [`planeMapN_tame`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeNear.lean#L610).

**Theorem · Axis cancellation gives tameness.** A vanishing angular endpoint and a tame planar phase factor give local tameness of the angular profile on the nonzero axis. [`axis_core`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeNear.lean#L613).

**Theorem · Tameness on the nonzero axis.** For angular power at most one, an endpoint-vanishing single-row spline gives a locally tame angular profile on the nonzero axis. [`ang_axis`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeNear.lean#L730).

**Theorem · Tameness of the near angular profile.** Either angular endpoint cancellation or a matching low harmonic gives local tameness of the near angular profile away from the origin. [`ang_tame`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeNear.lean#L755).

**Definition · Radial chart at small scale.** The near radial coordinate is scale times radius divided by scale times radius plus the chart length. [`nearT`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeNear.lean#L766).

**Definition · Atom profile after removing scale.** The near profile removes the leading radial scale from the atom and keeps its decay, phase, radial quotient and angular factors. [`nearProfile`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeNear.lean#L768).

**Theorem · Splitting an additive phase.** The complex exponential of an imaginary sum is the product of the two corresponding phase exponentials. [`near_exp_add`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeNear.lean#L773).

**Theorem · Atom factorization near the origin.** Where the spline factors by the radial coordinate, the atom at positive scale equals that scale times the near profile. [`near_identity`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeNear.lean#L778).

**Theorem · The near profile is locally tame.** The near profile has a locally Lipschitz derivative where the spatial point and radial denominator are nonzero, under the stated spline and angular conditions. [`near_tame`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeNear.lean#L807).

**Theorem · Restriction does not increase norm.** Restricting a continuous linear map on scale and space to its spatial input does not increase its operator norm. [`nearGlue_comp_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeNear.lean#L845).

**Theorem · Rescaling the near derivative.** A scale-linear representation with locally Lipschitz derivative produces a locally Lipschitz spatial derivative profile for the original function. [`nearGlue`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeNear.lean#L851).

**Theorem · A regular scaled atom profile.** Every admissible scalar atom has a positive-scale representation by a near profile with neighbourhood differentiability and locally Lipschitz derivative on the fixed annulus. [`atomScalar_nearProfile`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeNear.lean#L897).

**Theorem · Near rescaling of the atom derivative.** The derivative of an admissible scalar atom at small positive scale is represented by a locally Lipschitz profile on the fixed annulus. [`atomScalar_fderiv_nearScaled`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxAtomSlopeNear.lean#L928).

### Breakdown.FracCell.GivenAuxDual

This file assembles scalar-atom, field-mode and flux estimates into the weak-derivative regularity required of the constructed dual auxiliary fields. **Reading context:** Appendix B: represented fields and the auxiliary estimates used by the profile, pin and adjoint reductions (B.1 and B.9–B.13).

**Theorem · Pairing an L² field with a test field.** An L² vector field has integrable inner product with every continuous compactly supported vector field. [`int_inner_two`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDual.lean#L12).

**Theorem · Multiplying an L² field by a test.** A continuous compactly supported scalar times an L² vector field is integrable. [`int_smul_two`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDual.lean#L22).

**Theorem · Local integrability gives test pairings.** A locally integrable vector field has integrable inner product with every continuous compactly supported vector field. [`int_inner_loc`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDual.lean#L30).

**Theorem · Scalar test derivatives stay supported.** Each coordinate derivative of a scalar test function is continuous and compactly supported. [`test_deriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDual.lean#L41).

**Theorem · Vector test derivatives stay supported.** Each coordinate derivative of a vector test function is continuous and compactly supported. [`test_vec_deriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDual.lean#L46).

**Theorem · The test Laplacian stays supported.** The negative sum of second partial derivatives of a vector test function is continuous and compactly supported. [`test_sumSecond`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDual.lean#L51).

**Theorem · Trace regularity of the zero field.** The zero vector field satisfies trace regularity. [`tr_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDual.lean#L65).

**Theorem · Trace regularity of a sum.** The sum of trace-regular vector fields is trace regular. [`tr_add`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDual.lean#L77).

**Theorem · Scaling a trace-regular field.** Multiplication by a real scalar preserves trace regularity. [`tr_smul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDual.lean#L122).

**Theorem · Trace regularity of finite sums.** A finite sum of trace-regular fields is trace regular. [`tr_sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDual.lean#L155).

**Theorem · Integrability of gradient pairings.** An operator field with L² columns has integrable entrywise pairing with the derivative of a test vector field. [`int_entry`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDual.lean#L164).

**Theorem · Entrywise pairing distributes over sums.** The entrywise inner product is additive in its second operator argument. [`entry_add`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDual.lean#L171).

**Theorem · Scaling an entrywise pairing.** A real scalar in the second operator argument factors out of the entrywise inner product. [`entry_smul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDual.lean#L175).

**Theorem · Radial flux regularity of zero.** The zero operator field satisfies radial flux regularity. [`fr_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDual.lean#L179).

**Theorem · Radial flux regularity of a sum.** The sum of radial-flux-regular operator fields is radial-flux regular. [`fr_add`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDual.lean#L187).

**Theorem · Scaling a regular radial flux.** Multiplication by a real scalar preserves radial flux regularity. [`fr_smul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDual.lean#L208).

**Theorem · Regularity of finite radial flux sums.** A finite sum of regular radial fluxes is a regular radial flux. [`fr_sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDual.lean#L221).

**Theorem · A coordinate vector as a scaled unit.** A vector with one nonzero coordinate is that coordinate times the corresponding unit vector. [`single_smul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDual.lean#L230).

**Theorem · Real planar atom as harmonic sums.** The real planar atom is the sum of the real positive-branch harmonics and the nonzero negative-branch harmonics. [`plane_re`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDual.lean#L237).

**Theorem · Imaginary planar atom as harmonic sums.** The imaginary planar atom is written as real parts of positive and negative harmonic branches with their respective imaginary factors. [`plane_im`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDual.lean#L248).

**Theorem · Real height atom as a harmonic sum.** The real height atom sums its harmonics with coefficient one for the zero harmonic and two for every other harmonic. [`height_re`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDual.lean#L261).

**Theorem · Vector atom as coordinate harmonics.** The atom vector is the sum of its real planar and height harmonic contributions along the three coordinate unit vectors. [`atom_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDual.lean#L271).

**Theorem · Trace regularity of an atom.** Valid chart parameters and atom data give a trace-regular atom field at every phase. [`atom_reg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDual.lean#L290).

**Theorem · Rank-one maps preserve vector sums.** The rank-one map formed from a fixed scalar functional distributes over addition of its output vector. [`sr_add`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDual.lean#L317).

**Theorem · Rank-one maps preserve finite sums.** The rank-one map formed from a fixed scalar functional distributes over finite sums of output vectors. [`sr_sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDual.lean#L321).

**Theorem · Regularity of the constructed flux.** Valid chart and flux data produce a radial-flux-regular operator field. [`flux_reg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDual.lean#L331).

**Theorem · Field as a sum of real modes.** The constructed vector field is its finite sum of decayed phase modes in the radial, polar and azimuthal frame. [`field_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDual.lean#L355).

**Theorem · Trace regularity of the field.** Field data of high order three produce a trace-regular vector field. [`field_reg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDual.lean#L364).

**Theorem · Measurability of the field derivative.** The Fréchet derivative of a spatial vector field is almost everywhere strongly measurable. [`fderiv_meas`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDual.lean#L383).

**Theorem · L² columns give finite matrix energy.** An operator field whose coordinate columns are L² has integrable squared entry norm. [`entry_int_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDual.lean#L386).

**Theorem · Trace regularity of the adjoint field.** Valid auxiliary data give trace regularity of each adjoint field at every parameter. [`adjoint_reg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDual.lean#L392).

**Theorem · Trace regularity of an atom family.** A finite family of valid atom fields remains trace regular after evaluation at its parameter and phase. [`atoms_reg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDual.lean#L398).

**Theorem · Trace regularity of the sharp field.** Valid auxiliary data give a trace-regular sharp field for every viscosity and parameter. [`sharp_reg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDual.lean#L405).

**Theorem · Regularity needed by the adjoint dual.** Valid auxiliary data supply the adjoint and sharp weak gradients, their measurability and energy bounds, and a radially weighted L² negative trace for the required combination. [`adjointDualCore_of_given`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDual.lean#L419).

**Theorem · Regularity of dual auxiliary fields.** Valid auxiliary data supply weak gradients and weighted negative traces for the dual and potential fields, together with a weak divergence and weighted L² bound for the flux. [`dualFields_of_given`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDual.lean#L437).

### Breakdown.FracCell.GivenAuxDualParts

This file states trace and radial-flux regularity, proves their assembly lemmas, and supplies the spline bounds and scalar inputs used by the dual-field construction. **Reading context:** Appendix B: represented fields and the auxiliary estimates used by the profile, pin and adjoint reductions (B.1 and B.9–B.13).

**Predicate · Trace regularity requirements.** Trace regularity requires an L² field, almost-everywhere differentiability, its weak gradient with L² columns, and a locally integrable negative trace whose radial weighting is L². [`IsTraceRegular`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualParts.lean#L17).

**Predicate · Radial flux regularity requirements.** Radial flux regularity requires a measurable operator field with L² columns and a locally integrable weak matrix divergence whose radial weighting is L². [`IsRadialFluxRegular`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualParts.lean#L25).

**Theorem · Differentiating a vector component.** For a smooth vector field, differentiating a coordinate agrees with taking that coordinate of the vector derivative. [`comp_fderiv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualParts.lean#L33).

**Theorem · Components of a vector test field.** Every coordinate of a vector test field is a scalar test function. [`comp_test`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualParts.lean#L40).

**Theorem · Weak gradients against vector tests.** A weak vector gradient satisfies coordinate integration by parts against vector test fields when the relevant fields are locally integrable. [`vec_weak`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualParts.lean#L45).

**Theorem · Pairing a locally integrable field.** A locally integrable field has integrable inner product with every continuous compactly supported test field. [`int_loc`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualParts.lean#L76).

**Theorem · Directional derivatives of test fields.** A coordinate directional derivative of a vector test field is again a vector test field. [`dir_test`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualParts.lean#L86).

**Theorem · Second partials as derivative columns.** For a smooth vector field, the sum of second partials is the sum of derivatives of its coordinate derivative columns. [`ssp_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualParts.lean#L91).

**Theorem · Negative trace from weak Hessian columns.** Weak gradients of the derivative columns supply the negative trace as the negative sum of their diagonal evaluations. [`trace_of_cols`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualParts.lean#L101).

**Theorem · A Lipschitz field has its weak gradient.** The Fréchet derivative of a globally Lipschitz vector field is a weak gradient of that field. [`weak_of_boundedSlope`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualParts.lean#L127).

**Theorem · Assembling trace regularity.** A Lipschitz L² field with L² derivative columns and the stated weak second-derivative bounds satisfies trace regularity. [`traceRegular_of_parts`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualParts.lean#L182).

**Theorem · Reading a constructed vector component.** Evaluating a vector assembled from its components returns the selected component. [`ofComponents_apply`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualParts.lean#L201).

**Theorem · Radial functional on a unit vector.** The radial scalar functional evaluated on a coordinate unit vector has norm at most one. [`radial_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualParts.lean#L204).

**Theorem · Radial direction as normalized position.** The radial frame vector is spatial position divided by its norm. [`radial_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualParts.lean#L214).

**Theorem · Assembling radial flux regularity.** An L² radial output field and a locally integrable weak matrix divergence with radial L² control give radial flux regularity. [`fluxRegular_of_parts`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualParts.lean#L218).

**Theorem · Polynomial bound on the unit square.** A complex polynomial has a common norm bound on pairs of real coordinates of absolute value at most one. [`poly_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualParts.lean#L238).

**Theorem · Quadratic endpoint remainder.** On the unit rectangle, the remainder after subtracting a polynomial's value and first radial term at one is bounded by a constant times the squared distance to that endpoint. [`poly_endRemainder`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualParts.lean#L258).

**Theorem · Evaluating a substituted first variable.** Evaluating a polynomial after fixing its first variable agrees with evaluation at the resulting pair of coordinates. [`eval_atFirst`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualParts.lean#L321).

**Theorem · Interior mesh points are below one.** Every interior point of a strictly increasing mesh ending at one is less than one. [`interior_lt_one`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualParts.lean#L331).

**Theorem · A mesh from zero to one has two points.** A list beginning at zero and ending at one has at least two entries. [`two_le_length`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualParts.lean#L340).

**Theorem · Double endpoint zeros give tail decay.** A tensor spline whose last radial pieces vanish to first order at one is bounded by a constant times the squared distance to one. [`tail_bound_split`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualParts.lean#L349).

**Theorem · The selected cell is measurable.** The cell-index function of any finite real mesh is measurable. [`cellIndex_measurable`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualParts.lean#L437).

**Theorem · Continuity of the coordinate pair.** The map from a real pair to its two complex coordinates is continuous. [`vec_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualParts.lean#L451).

**Theorem · Half-spline evaluation is measurable.** Uncurried evaluation of a spline on the half-domain is measurable. [`evalHalf_measurable`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualParts.lean#L457).

**Theorem · Parity-extended spline is measurable.** Uncurried spline evaluation with either parity is measurable. [`eval_measurable`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualParts.lean#L471).

**Theorem · Ranges and decay of chart coordinates.** Valid chart parameters place the radial coordinate between zero and one, bound the height ratio by one, and bound the positive complementary radial coordinate by inverse spatial decay. [`chart_facts`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualParts.lean#L489).

**Theorem · A scalar atom is measurable.** The scalar atom term is measurable for all displayed chart, harmonic, phase and spline data. [`atom_measurable`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualParts.lean#L509).

**Theorem · Double endpoint zeros give L² atoms.** A tensor spline with the far-end double-zero condition yields an L² real coordinate atom after applying decay and any fixed complex coefficient. [`atomTerm_memLpTwo_of_tail`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualParts.lean#L530).

**Theorem · Trace regularity of a scalar atom.** An admissible atom with angular exponent at most one gives a trace-regular real coordinate field. [`atomTerm_traceRegular`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualParts.lean#L615).

**Theorem · Trace regularity of a field mode.** Each included mode of valid high-order-three field data is trace regular. [`fieldMode_traceRegular`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualParts.lean#L622).

**Theorem · Regularity of a scalar radial flux.** A valid flux spline gives radial flux regularity for the associated real coordinate atom and radial functional. [`fluxTerm_radialRegular`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualParts.lean#L632).

### Breakdown.FracCell.GivenAuxDualPartsRest

This file turns decay and Lipschitz estimates into weak first and second derivatives, then transports the scalar estimates to coordinate atoms and field modes. **Reading context:** Appendix B: represented fields and the auxiliary estimates used by the profile, pin and adjoint reductions (B.1 and B.9–B.13).

**Theorem · A Lipschitz field has a weak gradient.** The Fréchet derivative of a globally Lipschitz vector field is its weak gradient. [`weak_of_slopeBound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRest.lean#L19).

**Theorem · Coordinate unit vectors have norm one.** Each coordinate unit vector has norm one. [`unit_norm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRest.lean#L75).

**Theorem · Inverse-square decay gives L².** An almost-everywhere strongly measurable field bounded by inverse-square spatial decay belongs to L². [`memLp_of_decay`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRest.lean#L78).

**Theorem · The inverse-square weight is at most one.** The inverse square of one plus spatial norm is bounded above by one. [`decay_le_one`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRest.lean#L97).

**Theorem · Derivative decay gives a global slope.** A continuously differentiable vector field with inverse-square derivative decay is globally Lipschitz. [`slopeBound_of_decay`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRest.lean#L100).

**Theorem · Derivative decay gives L² columns.** Inverse-square decay of the derivative makes every coordinate derivative column L². [`gradMemLp_of_decay`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRest.lean#L110).

**Theorem · Weak Hessian from derivative bounds.** A globally Lipschitz first derivative with almost-everywhere inverse-cube second-derivative decay gives weak Hessian columns and a radially weighted L² trace. [`second_of_slope`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRest.lean#L119).

**Definition · Real coordinate map from a scalar.** The scalar-to-vector map multiplies by a fixed complex coefficient, takes the real part, and places it along a coordinate unit vector. [`lin`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRest.lean#L179).

**Theorem · Evaluating the real coordinate map.** The scalar-to-vector map returns the real part of the coefficient times the input along the chosen unit vector. [`lin_apply`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRest.lean#L182).

**Theorem · Coordinate atom as a linear image.** A real coordinate atom is the fixed scalar-to-vector linear image of its complex scalar atom. [`atom_fun`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRest.lean#L185).

**Theorem · Linear maps preserve local integrability.** A continuous linear map sends a locally integrable complex field to a locally integrable vector field. [`li_comp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRest.lean#L191).

**Theorem · Derivative through a linear map.** For a Lipschitz scalar field, composition with a continuous linear map commutes with the Fréchet derivative almost everywhere. [`tr_fderiv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRest.lean#L196).

**Theorem · Transporting derivative energy.** A Lipschitz scalar field with inverse-square derivative decay has L² coordinate derivatives after a continuous linear map. [`tr_grad`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRest.lean#L201).

**Theorem · Transporting weak second derivatives.** A continuous linear map transports the scalar weak Hessian identity, local integrability and weighted trace estimate to a vector field. [`tr_second`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRest.lean#L214).

**Theorem · Derivative of a smooth component.** For a smooth vector field, the derivative of a component is that component of the vector derivative. [`comp_fderiv'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRest.lean#L259).

**Theorem · A vector test has scalar components.** Every coordinate of a vector test field is a scalar test function. [`comp_test'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRest.lean#L266).

**Theorem · The normalized spatial direction.** The radial frame vector equals the inverse spatial norm times position. [`radial_eq'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRest.lean#L271).

**Theorem · Pairing with a coordinate unit vector.** The inner product with a coordinate unit vector extracts that coordinate. [`inner_unit`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRest.lean#L277).

**Theorem · Pairing with a rank-one radial map.** The entrywise pairing with a rank-one operator equals the inner product of the first operator applied to its input direction with its output vector. [`entry_radial`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRest.lean#L280).

**Theorem · A coordinate atom is globally Lipschitz.** Each admissible real coordinate atom with angular exponent at most one has a finite global Lipschitz constant. [`atomTerm_boundedSlope`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRest.lean#L297).

**Theorem · L² derivatives of a coordinate atom.** Every coordinate derivative of an admissible real coordinate atom belongs to L². [`atomTerm_gradMemLpTwo`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRest.lean#L304).

**Theorem · Weak second derivatives of an atom.** An admissible real coordinate atom has weak Hessian columns with locally integrable diagonal entries and radially weighted L² trace. [`atomTerm_second`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRest.lean#L312).

**Theorem · A field mode is globally Lipschitz.** Every included mode of valid high-order-three field data has a finite global Lipschitz constant. [`fieldMode_boundedSlope`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRest.lean#L323).

**Theorem · A field mode belongs to L².** Every included mode of valid high-order-three field data belongs to L². [`fieldMode_memLpTwo`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRest.lean#L332).

**Theorem · L² derivatives of a field mode.** Every coordinate derivative of an included high-order-three field mode belongs to L². [`fieldMode_gradMemLpTwo`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRest.lean#L341).

**Theorem · Weak second derivatives of a field mode.** An included high-order-three field mode has weak Hessian columns with local integrability and radially weighted L² trace. [`fieldMode_second`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRest.lean#L350).

**Theorem · Weak divergence of a radial atom flux.** A valid scalar flux atom has a weak matrix divergence that is locally integrable and becomes L² after multiplication by radius. [`fluxTerm_radialDiv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRest.lean#L363).

### Breakdown.FracCell.GivenAuxDualPartsRestOpen

This file provides concrete polynomial, spline and radial-decay estimates before deriving the global regularity and weak derivatives used by the dual-field assembly. **Reading context:** Appendix B: represented fields and the auxiliary estimates used by the profile, pin and adjoint reductions (B.1 and B.9–B.13).

**Definition · Polynomial evaluation on a real pair.** The polynomial evaluator substitutes the two real coordinates as complex variables. [`pk`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpen.lean#L22).

**Theorem · Polynomial evaluation is C¹.** Evaluation of the complex polynomial on real coordinate pairs is continuously differentiable. [`pk_contDiff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpen.lean#L24).

**Definition · First-coordinate polynomial derivative.** The first partial derivative is the Fréchet derivative of polynomial evaluation along the first coordinate direction. [`pkt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpen.lean#L43).

**Definition · Second-coordinate polynomial derivative.** The second partial derivative is the Fréchet derivative of polynomial evaluation along the second coordinate direction. [`pkx`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpen.lean#L45).

**Theorem · Derivative in the first coordinate.** The first-coordinate slice of polynomial evaluation has derivative equal to its first partial derivative. [`pk_hasDerivAt_t`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpen.lean#L47).

**Theorem · Derivative in the second coordinate.** The second-coordinate slice of polynomial evaluation has derivative equal to its second partial derivative. [`pk_hasDerivAt_x`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpen.lean#L53).

**Theorem · Polynomial and partials on the square.** A polynomial and both first partial derivatives have a common bound on the unit square. [`pk_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpen.lean#L59).

**Theorem · Cell index bounded by mesh length.** A cell index never exceeds the length of its mesh list. [`cellIndex_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpen.lean#L79).

**Theorem · A uniform bound for all spline pieces.** All relevant polynomial pieces and their first partial derivatives have one common bound on the unit square. [`pieces_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpen.lean#L84).

**Theorem · The cell index is locally fixed on right.** Approaching a point from the right eventually leaves its cell index unchanged. [`cellIndex_right`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpen.lean#L95).

**Theorem · Reflection fixes the left cell index.** Approaching a point from the left eventually leaves the cell index of its negative unchanged. [`cellIndex_left_neg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpen.lean#L109).

**Theorem · Derivative bound from one-sided equality.** A function agreeing locally on a uniquely differentiable set with a differentiable comparison has derivative norm bounded by the comparison derivative. [`deriv_norm_le_of_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpen.lean#L125).

**Theorem · Parity signs have norm at most one.** Either complex parity sign has norm at most one. [`sign_norm_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpen.lean#L134).

**Theorem · Radial derivative bound for a spline.** A scalar radial weight times a spline has derivative bounded by the weight and its derivative times one fixed spline constant on the unit rectangle. [`shape_tderiv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpen.lean#L137).

**Theorem · Height derivative bound for a spline.** An angular weight times a spline has derivative bounded by the weight and its derivative times one fixed spline constant on the unit rectangle. [`shape_xderiv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpen.lean#L164).

**Theorem · A spline is bounded on the rectangle.** Spline evaluation is uniformly bounded on radial coordinates from zero to one and height coordinates of absolute value at most one. [`shape_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpen.lean#L213).

**Theorem · Cubic radial weight has quadratic decay.** On the unit interval, the high-order-three radial weight is bounded by the square of one minus the radial coordinate. [`w_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpen.lean#L224).

**Theorem · Derivative of the cubic radial weight.** The high-order-three radial weight has a derivative bounded by its degree factor times quadratic endpoint decay. [`w_deriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpen.lean#L231).

**Theorem · Derivative of an angular power.** On the unit height interval, a power of one minus height squared is bounded by one and has derivative norm bounded by twice its exponent. [`v_deriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpen.lean#L248).

**Theorem · The regularized core ratio is bounded.** The absolute value of the radial core ratio is at most one. [`core_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpen.lean#L265).

**Theorem · Bound for the twisted radial derivative.** The twisted derivative is bounded by the ordinary radial derivative plus the displayed phase and decay coefficients times the function bound. [`twist_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpen.lean#L269).

**Theorem · Quadratic decay of the reduced field.** Each component of a high-order-three reduced field is bounded by a constant times the squared distance to the outer radial endpoint. [`reduced_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpen.lean#L295).

**Theorem · A coordinate is bounded by the norm.** The absolute value of each spatial coordinate is bounded by spatial norm. [`coord_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpen.lean#L429).

**Theorem · Normalized coordinates are bounded.** Every spatial coordinate divided by spatial norm has absolute value at most one. [`ratio_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpen.lean#L433).

**Theorem · The height ratio is bounded.** The height-to-radius ratio has absolute value at most one. [`height_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpen.lean#L437).

**Theorem · Radial frame components are bounded.** Every component of the radial frame vector has absolute value at most one. [`radial_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpen.lean#L439).

**Theorem · Polar frame components are bounded.** Every component of the polynomial polar frame vector has absolute value at most one. [`polar_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpen.lean#L441).

**Theorem · Azimuthal frame components are bounded.** Every component of the polynomial azimuthal frame vector has absolute value at most one. [`azim_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpen.lean#L455).

**Theorem · The radial chart lies in the unit range.** For valid chart parameters, the compactified radial coordinate lies between zero and one. [`chartT_mem`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpen.lean#L463).

**Theorem · The decay factor is bounded by one.** For valid chart parameters, the complex inclusion of the decay factor has norm at most one. [`decay_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpen.lean#L468).

**Theorem · The mode phase has unit norm.** The complex mode phase has norm one at every spatial point. [`phase_norm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpen.lean#L475).

**Theorem · Chart decay implies spatial decay.** The square of one minus the radial chart coordinate is bounded by the displayed chart constant times inverse-square spatial decay. [`weight_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpen.lean#L478).

**Theorem · A real component bound by amplitudes.** With scalar and frame factors bounded by one, the real component of a mode is bounded by the sum of its three complex amplitudes. [`comp_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpen.lean#L494).

**Theorem · Vector norm bounded by component sums.** The norm of a vector assembled from components is bounded by the sum of their absolute values. [`ofComponents_norm_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpen.lean#L508).

**Theorem · Inverse-square decay of each mode.** A high-order-three field mode has a global inverse-square spatial decay bound. [`mode_decay`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpen.lean#L513).

**Theorem · Negative real powers as reciprocals.** The negative integer real power of one plus spatial norm is its corresponding reciprocal natural power. [`inv_weight`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpen.lean#L548).

**Theorem · Comparing far-field decay weights.** Outside the unit ball, a sufficiently high inverse power of radius is bounded by the stated inverse power of one plus radius times a power of two. [`far_weight`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpen.lean#L551).

**Theorem · Compensating a decay weight on a ball.** On a ball of radius R, multiplying inverse decay by the corresponding power of one plus R gives a bound of at least one. [`near_weight`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpen.lean#L563).

**Theorem · Extending a far derivative bound.** A C¹ field with inverse-fourth derivative decay outside a ball has a global inverse-square derivative bound. [`grad_of_far`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpen.lean#L568).

**Theorem · Second derivative from far slope decay.** A globally Lipschitz operator field with inverse-fifth local slope decay has a global inverse-cube derivative bound. [`second_of_far`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpen.lean#L593).

**Theorem · Far slope control gives a global bound.** A bounded locally Lipschitz operator field with the stated decaying far-field local slopes is globally Lipschitz. [`slope_of_far`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpen.lean#L621).

**Theorem · Slope bound along a punctured segment.** A derivative bound on punctured space bounds increments along every segment avoiding the origin. [`seg_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpen.lean#L671).

**Theorem · Extending the slope estimate to zero.** Continuity at the origin extends a uniform punctured derivative bound to increments from the origin. [`to_origin_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpen.lean#L678).

**Theorem · A punctured derivative bound is global.** A continuous function with uniformly bounded derivative away from the origin is globally Lipschitz with that bound. [`slopeBound_of_punctured_open`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpen.lean#L712).

**Theorem · Continuity of the radial decay weight.** Every real inverse power of one plus spatial norm is continuous. [`wt_continuous`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpen.lean#L731).

**Theorem · When radial decay is square integrable.** The radial decay weight belongs to L² when its exponent is greater than three halves. [`wt_memLp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpen.lean#L734).

**Theorem · Dominated radial decay gives L².** An almost-everywhere measurable field dominated by radial decay of exponent greater than three halves belongs to L². [`memLp_of_wt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpen.lean#L748).

**Theorem · Inverse radius is locally integrable.** The inverse spatial norm is integrable on every ball centred at zero. [`invNorm_intOn`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpen.lean#L755).

**Theorem · Inverse-radius local integrability.** An almost-everywhere measurable field bounded by a constant times inverse radius is locally integrable. [`locInt_of_inv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpen.lean#L764).

**Theorem · Extra decay reduces inverse radius.** Adding a nonnegative radial decay exponent to inverse radius does not increase the weight. [`inv_wt_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpen.lean#L772).

**Theorem · Radius times inverse radius is bounded.** Spatial norm multiplied by its inverse is at most one, including at the origin. [`norm_inv_mul_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpen.lean#L776).

**Theorem · Weighted inverse-radius integrability.** An almost-everywhere measurable field bounded by inverse radius times a nonnegative decay weight is locally integrable. [`locInt_of_wt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpen.lean#L781).

**Theorem · Radial weighting removes the singularity.** An inverse-radius bound with decay exponent greater than three halves makes the radius-weighted field L². [`memLp_of_invWt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpen.lean#L790).

**Theorem · A scalar atom is globally Lipschitz.** An admissible scalar atom with angular exponent at most one has a finite global Lipschitz constant. [`atomScalar_slope`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpen.lean#L808).

**Theorem · Inverse-square derivative decay of atoms.** The derivative of an admissible scalar atom has an almost-everywhere inverse-square spatial decay bound. [`atomScalar_gradDecay`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpen.lean#L821).

**Theorem · Weak second derivatives of scalar atoms.** An admissible scalar atom has weak derivative columns with locally integrable entries and radially weighted L² trace. [`atomScalar_second`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpen.lean#L829).

**Theorem · A field mode is C¹.** Each included mode of valid high-order-three field data is continuously differentiable throughout space. [`fieldMode_contDiffOne`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpen.lean#L862).

**Theorem · A field mode has a Lipschitz derivative.** The derivative of each included high-order-three field mode has a finite global Lipschitz constant. [`fieldMode_fderivSlope`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpen.lean#L886).

**Theorem · Global decay of a field mode.** Each included high-order-three field mode has a global inverse-square decay bound. [`fieldMode_decay`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpen.lean#L909).

**Theorem · Global decay of a mode derivative.** The derivative of each included high-order-three field mode has a global inverse-square decay bound. [`fieldMode_gradDecay`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpen.lean#L917).

**Theorem · Decay of a mode's second derivative.** The second derivative of each included high-order-three field mode has an almost-everywhere inverse-cube decay bound. [`fieldMode_secondDecay`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpen.lean#L928).

**Theorem · Weak radial divergence of a scalar flux.** A valid flux spline supplies a scalar radial-divergence identity with locally integrable divergence and radially weighted L² control. [`fluxScalar_radialDiv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpen.lean#L941).

### Breakdown.FracCell.GivenAuxDualPartsRestOpenLeaves

This file proves the radial flux integration identity, removes the origin in weak derivative identities, and supplies the polynomial endpoint and far-field estimates needed by the dual fields. **Reading context:** Appendix B: represented fields and the auxiliary estimates used by the profile, pin and adjoint reductions (B.1 and B.9–B.13).

**Definition · Polynomial evaluated on a real pair.** The polynomial evaluator substitutes the real coordinate pair as two complex variables. [`pk`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L24).

**Theorem · Continuous complex coordinate pairs.** The map from a real pair to its two complex coordinates is continuous. [`vec_continuous`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L26).

**Theorem · Polynomial evaluation is continuous.** Polynomial evaluation on real coordinate pairs is continuous. [`pk_continuous`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L32).

**Theorem · Polynomial bounds on the unit square.** A complex polynomial is uniformly bounded on the real unit square. [`pk_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L35).

**Theorem · Evaluation with a fixed first coordinate.** Evaluation after fixing the first polynomial variable agrees with evaluating at the resulting pair. [`eval_atFirst`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L45).

**Theorem · Endpoint vanishing after evaluation.** A polynomial vanishing at first coordinate one evaluates to zero there for every second coordinate. [`pk_one_eq_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L55).

**Theorem · Derivative of polynomial evaluation.** Differentiating evaluation in the first real coordinate gives evaluation of the first polynomial partial derivative. [`pk_hasDerivAt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L60).

**Theorem · Bounds from a double endpoint zero.** A bounded second radial derivative and a double zero at one give quadratic decay of the polynomial and linear decay of its first derivative. [`tail_poly`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L90).

**Theorem · Cell index stays within the mesh.** The selected cell index is bounded by the mesh length minus two, using natural-number subtraction. [`cellIndex_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L115).

**Theorem · Interior mesh points lie below one.** Every interior break of a strictly increasing mesh ending at one lies strictly below one. [`interior_lt_one`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L120).

**Theorem · Distinct endpoints need two entries.** A mesh list beginning at zero and ending at one contains at least two entries. [`two_le_length`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L129).

**Theorem · Decay bounds for a flux spline piece.** The far-end double-zero condition gives quadratic decay of every selected spline piece and linear decay of its radial derivative. [`flux_tail`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L138).

**Theorem · Norm under positive radial scaling.** Multiplication by a positive scalar multiplies spatial norm by that scalar. [`norm_smul_pos`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L222).

**Theorem · Height ratio is unchanged by scaling.** Positive radial scaling preserves the height-to-radius ratio. [`height_smul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L225).

**Theorem · Angular weight is unchanged by scaling.** Positive radial scaling preserves the angular weight. [`q_smul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L231).

**Theorem · Angle is unchanged by radial scaling.** Positive radial scaling preserves the planar angle. [`angle_smul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L234).

**Definition · Scalar atom on a fixed ray.** The ray profile expresses the scalar atom in terms of a radial variable with its spatial angle and height ratio fixed. [`prof`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L240).

**Theorem · The atom equals its radial profile.** At a positive multiple of a spatial point, the scalar atom equals its ray profile evaluated at the scaled norm. [`ray`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L246).

**Theorem · Bound for the radial product derivative.** The stated factor and derivative bounds control the derivative combination for radius squared times a flux profile by the displayed quadratic tail constant. [`combo_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L251).

**Theorem · Derivative estimate within a radial cell.** Polynomial endpoint bounds give a derivative at scale one for the radius-squared flux expression, with the displayed phase-dependent quadratic decay bound. [`local_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L302).

**Theorem · The cell remains fixed from the right.** The cell index is eventually unchanged when its coordinate approaches from the right. [`cellIndex_right`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L381).

**Theorem · Derivative control from a local model.** Local equality on a uniquely differentiable set bounds the derivative norm by the derivative of the smooth comparison. [`deriv_norm_le_of_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L395).

**Theorem · Bounded height ratio.** The height-to-radius ratio has absolute value at most one. [`height_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L404).

**Theorem · Angular powers have norm at most one.** Every natural power of the angular square root has complex norm at most one. [`sqrt_q_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L411).

**Theorem · A parity sign is bounded.** The norm of either complex parity sign is at most one. [`sign_norm_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L417).

**Theorem · A bound for radial flux differentiation.** For a valid flux spline, differentiating scale squared times the scalar atom at scale one gives a uniform quadratic chart-decay bound away from the origin. [`flux_deriv_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L420).

**Theorem · The cell is fixed away from breaks.** Away from every interior mesh break, the cell index is constant on a neighbourhood. [`cellIndex_nhds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L468).

**Theorem · Radial flux is differentiable off breaks.** The scale-squared flux profile is differentiable at scale one when the spatial point is nonzero and its radial chart avoids spline breaks. [`flux_differentiable`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L483).

**Theorem · Measurable half-spline evaluation.** Uncurried half-spline evaluation is measurable. [`evalHalf_measurable`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L519).

**Theorem · Measurable parity-extended evaluation.** Spline evaluation with either parity is measurable as a function of both coordinates. [`eval_measurable`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L547).

**Theorem · Measurability of the decayed atom.** The scalar atom including its decay factor is measurable. [`atom_measurable`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L566).

**Theorem · Almost all radii avoid finite breaks.** Almost every spatial point is nonzero and has radial chart coordinate outside any specified finite list. [`good_ae`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L589).

**Theorem · A weighted bound for flux divergence.** The radial divergence expression is almost everywhere measurable and bounded by inverse radius times inverse-square spatial decay. [`flux_divBound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L611).

**Theorem · Integrability of inverse radius on balls.** Inverse spatial norm is integrable on every ball centred at zero. [`invNorm_intOn`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L658).

**Theorem · A scalar flux atom is bounded.** A valid flux spline gives a uniform bound for the scalar atom including its decay factor. [`u_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L667).

**Theorem · Measurable radial flux derivative.** The derivative at scale one of the scale-squared scalar flux profile is almost everywhere strongly measurable. [`deriv_aesm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L702).

**Theorem · Uniform test-function and support bounds.** A scalar test function and its derivative admit global bounds and vanish outside a common positive-radius ball. [`test_bounds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L725).

**Theorem · Integrability of a truncated singularity.** A constant times inverse radius, restricted to a ball centred at zero, is integrable. [`ind_integrable`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L742).

**Theorem · Derivative of a rescaled test integral.** For a bounded measurable field, differentiating the inverse-radius pairing with a rescaled test at scale one gives the negative radial-derivative pairing. [`j2_deriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L747).

**Theorem · Weak radial divergence from ray control.** A uniform ray Lipschitz bound gives the integration-by-parts identity for the radial divergence expression of a scalar flux atom. [`flux_weak`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L814).

**Theorem · Continuous pieces across ordered breaks.** Continuous pieces indexed by ordered threshold crossings glue to a continuous function when adjacent pieces agree at each threshold. [`glue_continuous`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L934).

**Theorem · Indexing an interior mesh break.** The kth interior break is the original mesh entry at index k plus one. [`interior_get`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L963).

**Theorem · Radial continuity of the extended spline.** A radially continuous spline remains continuous in its radial coordinate after parity extension. [`t_continuous`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L971).

**Theorem · Right derivatives along positive rays.** The scale-squared flux profile has a right derivative at every positive scale, bounded by that scale times one common constant. [`ray_right_deriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L1000).

**Theorem · Continuity along positive rays.** The scale-squared scalar flux profile is continuous at all positive scales. [`ray_continuousOn`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L1064).

**Theorem · Uniform local slope along rays.** The scale-squared scalar flux profile has one Lipschitz bound on the scale ball of radius one half about one, uniformly over nonzero spatial points. [`ray_slope`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L1094).

**Theorem · Far decay survives complex inclusion.** Including a real field into the complex numbers preserves its far-decay exponent. [`far_ofReal`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L1130).

**Theorem · Far decay survives taking real parts.** Taking real parts preserves the far-decay exponent of a complex field. [`far_re`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L1137).

**Theorem · Coordinate injection as a linear map.** The scalar coordinate injection sends a real number to the vector with that number in the chosen coordinate. [`single_clm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L1144).

**Theorem · Cubic far decay of a field mode.** Every included mode of valid high-order-three field data satisfies the far-decay condition with exponent three. [`mode_farDecay`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L1150).

**Theorem · Slope after vector evaluation.** Evaluating a Lipschitz operator field on a vector of norm at most one preserves the Lipschitz constant. [`slope_apply`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L1207).

**Theorem · A contractive scalar map preserves slope.** Composing a complex Lipschitz function with the stated contractive real linear map preserves its Lipschitz constant. [`slope_part`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L1216).

**Theorem · Derivative bound from a local slope.** A weighted Lipschitz bound on the half-radius ball bounds the derivative at its centre with the nonnegative part of the coefficient. [`fderiv_le_of_ball`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L1222).

**Theorem · The weighted singularity is bounded.** Inverse radius times inverse-cube spatial decay is bounded by inverse radius. [`weight_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L1231).

**Theorem · The spatial origin has measure zero.** Almost every spatial point is nonzero. [`ae_ne_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L1235).

**Theorem · Norm of a coordinate unit vector.** Each coordinate unit vector has norm one. [`unit_norm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L1240).

**Theorem · Scalar integration by parts off zero.** The stated boundedness, annular Lipschitz and weighted slope conditions give integration by parts for a real component of a complex field. [`part_identity`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L1242).

**Theorem · A weak Hessian identity from slopes.** An inverse-square derivative bound and the weighted local Lipschitz bound for the derivative imply the weak second-derivative identity. [`weak_second`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L1270).

**Theorem · Polynomial vanishing at the origin edge.** A polynomial vanishing at first coordinate zero evaluates to zero there for every second coordinate. [`pk_zero_eq_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L1391).

**Theorem · Linear growth from an endpoint zero.** A bounded radial derivative and a zero at the origin bound the polynomial by the derivative constant times the radial coordinate. [`origin_poly`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L1396).

**Theorem · Interior mesh breaks are positive.** Every interior break of a strictly increasing mesh beginning at zero is positive. [`interior_pos`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L1408).

**Theorem · A spline's linear bound at the origin.** Vanishing of the first radial pieces at zero gives a common linear-in-radius bound for the selected spline piece on the unit rectangle. [`origin_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L1418).

**Theorem · Continuity of a scalar atom at zero.** An admissible scalar atom including its decay factor is continuous at the spatial origin. [`origin_continuousAt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L1478).

**Theorem · Coordinate functions are C¹.** Each spatial coordinate is continuously differentiable. [`coord_smooth`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L1528).

**Theorem · The planar coordinate in real components.** The complex planar coordinate equals the first coordinate plus the second coordinate times the imaginary unit. [`plane_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L1531).

**Theorem · The planar coordinate is C¹.** The complex planar coordinate is continuously differentiable. [`plane_contDiff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L1534).

**Theorem · Angular phase as a normalized power.** At a nonzero complex number, the integer angular exponential is the integer power of its unit direction. [`exp_arg_zpow`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L1541).

**Theorem · C¹ integer powers away from zero.** Integer powers preserve continuous differentiability at points where the complex base is nonzero. [`zpow_contDiffAt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L1553).

**Theorem · Scalar atoms are C¹ off the axis.** An admissible scalar atom is continuously differentiable at every point with nonzero planar coordinate. [`offAxis_contDiffAt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L1560).

**Theorem · Angular square root as a norm ratio.** Away from the origin, the angular square root equals the planar norm divided by spatial norm. [`sqrt_q_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L1630).

**Theorem · Positive unit phase gives the coordinate.** The positive unit angular phase times the planar modulus equals the original complex number. [`phase_plus`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L1645).

**Theorem · Negative unit phase gives the conjugate.** The negative unit angular phase times the planar modulus equals the complex conjugate. [`phase_minus`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L1653).

**Theorem · C¹ regularity of the zero harmonic.** A zero-harmonic atom with matching angular exponent at most one is continuously differentiable away from the origin. [`harmonicZero_contDiffAt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L1661).

**Theorem · The mode derivative is locally Lipschitz.** The derivative of each included high-order-three field mode is locally Lipschitz everywhere. [`fieldMode_fderiv_localSlope`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L1738).

**Theorem · Far bounds for the mode derivative.** Outside some ball, the mode derivative has inverse-fourth decay and its unit-ball Lipschitz constant has inverse-fifth decay. [`fieldMode_farBounds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L1745).

**Theorem · Continuity and punctured atom bounds.** An admissible scalar atom is continuous everywhere, differentiable off the origin, and has inverse-square derivative decay there. [`atomScalar_punctured`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L1759).

**Theorem · Weak second derivatives of an atom.** Each coordinate derivative of an admissible scalar atom satisfies the weak derivative integration-by-parts identity. [`atomScalar_weakSecond`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L1783).

**Theorem · Weighted second-derivative bound.** Almost everywhere, every derivative column of an admissible scalar atom has derivative norm bounded by inverse radius times inverse-cube spatial decay. [`atomScalar_secondBound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L1793).

**Theorem · The scalar flux integration identity.** A valid scalar flux atom satisfies radial integration by parts with the divergence given by its scale-squared ray derivative divided by radius. [`fluxScalar_weak`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L1803).

**Theorem · Decay of the scalar flux divergence.** The scalar flux divergence is almost everywhere strongly measurable and bounded by inverse radius times inverse-square spatial decay. [`fluxScalar_divBound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxDualPartsRestOpenLeaves.lean#L1811).

### Breakdown.FracCell.GivenAuxFarDecay

This file defines a far-decay condition that tracks the function, its derivative and the derivative's slope, then proves rules for combining those estimates. **Reading context:** Appendix B: represented fields and the auxiliary estimates used by the profile, pin and adjoint reductions (B.1 and B.9–B.13).

**Predicate · Far-field decay with derivative control.** The far-decay predicate requires local differentiability, a decay bound for the field, one extra inverse power for its derivative, and two extra inverse powers for the derivative's local Lipschitz bound. [`FarDecay`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxFarDecay.lean#L13).

**Theorem · Multiplying inverse powers.** For a positive base, inverse powers multiply by adding their exponents. [`rpow_pair`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxFarDecay.lean#L20).

**Theorem · Monotonicity of inverse powers.** For a base at least one, increasing a decay exponent decreases its inverse power. [`rpow_anti`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxFarDecay.lean#L25).

**Theorem · Weakening a far-decay exponent.** A far-decay estimate also holds for any smaller decay exponent. [`FarDecay.mono`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxFarDecay.lean#L28).

**Theorem · Far decay of a sum.** The sum of two fields with the same far-decay exponent has that exponent. [`FarDecay.add`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxFarDecay.lean#L38).

**Theorem · Far decay under a linear map.** A continuous linear map preserves a field's far-decay exponent. [`FarDecay.clm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxFarDecay.lean#L63).

**Theorem · Decay exponents add under products.** The product of complex fields with far-decay exponents a and b has exponent a plus b. [`FarDecay.mul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxFarDecay.lean#L83).

**Theorem · Field and slope bounds from far decay.** The far-decay predicate supplies pointwise field and derivative bounds together with a weighted Lipschitz bound for the derivative on distant unit balls. [`FarDecay.bounds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxFarDecay.lean#L155).

**Theorem · Complex inclusion preserves decay.** Including a real field into the complex numbers preserves its far-decay exponent. [`FarDecay.ofReal`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxFarDecay.lean#L167).

**Theorem · Real parts preserve far decay.** Taking a complex field's real part preserves its far-decay exponent. [`FarDecay.re`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxFarDecay.lean#L173).

**Theorem · Real products add decay exponents.** The product of real fields with far-decay exponents a and b has exponent a plus b. [`FarDecay.rmul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxFarDecay.lean#L179).

**Theorem · Negation preserves far decay.** Negating a field preserves its far-decay exponent. [`FarDecay.neg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxFarDecay.lean#L186).

**Theorem · Constant fields have exponent zero.** A constant field satisfies the far-decay condition with exponent zero. [`FarDecay.const`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxFarDecay.lean#L192).

**Theorem · Upper norm bound in a unit ball.** A point in the unit ball about y has norm at most the norm of y plus one. [`ball_norm_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxFarDecay.lean#L200).

**Theorem · Lower norm bound in a unit ball.** A point in the unit ball about y has norm at least the norm of y minus one. [`ball_norm_ge`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxFarDecay.lean#L204).

**Theorem · Position has decay exponent minus one.** The identity spatial map satisfies the far-decay condition with exponent minus one, expressing its linear growth. [`FarDecay.ident`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxFarDecay.lean#L210).

**Theorem · Power bounds for comparable radii.** If a positive quantity lies between two constant multiples of a radius, every real power is bounded by the stated sum of the two comparison powers. [`pow_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxFarDecay.lean#L220).

**Theorem · Taking a power of a decay weight.** For positive radius, a real power of an inverse-power weight multiplies the two exponents. [`rpow_weight`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxFarDecay.lean#L236).

**Theorem · Powers of comparable decaying fields.** A real field with matching positive lower and upper far-field bounds retains the far-decay condition under real powers, with the exponent multiplied accordingly. [`FarDecay.rpow`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxFarDecay.lean#L241).

**Theorem · Far decay for paired coordinates.** Pairing two real fields with the same far-decay exponent preserves that exponent. [`FarDecay.prodMk`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxFarDecay.lean#L330).

**Theorem · Composition through a compact range.** An exponent-zero map with compact far-field range retains exponent-zero control after a differentiable map whose derivative is locally Lipschitz. [`FarDecay.comp_compact`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxFarDecay.lean#L355).

**Theorem · Slope decay under bounded composition.** A bounded differentiable outer function with bounded Lipschitz derivative converts the stated inner derivative decay into exponent-zero far decay. [`FarDecay.comp_slope`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxFarDecay.lean#L420).

**Theorem · Derivative decay of a logarithm.** A decaying positive function with a matching far-field lower bound has logarithmic derivative of inverse-radius size and derivative slope of inverse-square size. [`FarDecay.log_slope`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxFarDecay.lean#L479).

### Breakdown.FracCell.GivenAuxFarDecayLeaves

This file applies the far-decay calculus to chart coordinates, frame vectors, phases and reduced modes, exposing the cubic outer-endpoint factor responsible for field-mode decay. **Reading context:** Appendix B: represented fields and the auxiliary estimates used by the profile, pin and adjoint reductions (B.1 and B.9–B.13).

**Theorem · Coordinates have linear far-field growth.** Each spatial coordinate satisfies the far-decay condition with exponent minus one. [`coord_far`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxFarDecayLeaves.lean#L12).

**Theorem · Squared norm has quadratic growth.** The squared spatial norm satisfies the far-decay condition with exponent minus two. [`normSq_far`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxFarDecayLeaves.lean#L18).

**Theorem · A lower bound for distant squared norms.** On unit balls whose centres have norm at least two, squared norm is at least one quarter of the centre's squared norm. [`normSq_low`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxFarDecayLeaves.lean#L29).

**Theorem · Powers of the squared norm.** A real power of squared spatial norm equals the spatial norm raised to twice that power. [`sq_rpow`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxFarDecayLeaves.lean#L35).

**Theorem · The norm has linear far-field growth.** Spatial norm satisfies the far-decay condition with exponent minus one. [`norm_far`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxFarDecayLeaves.lean#L39).

**Theorem · Inverse norm has exponent-one decay.** Inverse spatial norm satisfies the far-decay condition with exponent one. [`invNorm_far`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxFarDecayLeaves.lean#L48).

**Theorem · Normalized coordinates: exponent zero.** A coordinate divided by spatial norm satisfies the far-decay condition with exponent zero. [`ratio_far`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxFarDecayLeaves.lean#L57).

**Theorem · The radial frame has exponent zero.** Each radial frame component satisfies exponent-zero far decay. [`radial_far`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxFarDecayLeaves.lean#L63).

**Theorem · The polar frame has exponent zero.** Each polynomial polar frame component satisfies exponent-zero far decay. [`polar_far`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxFarDecayLeaves.lean#L65).

**Theorem · The azimuthal frame has exponent zero.** Each polynomial azimuthal frame component satisfies exponent-zero far decay. [`azim_far`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxFarDecayLeaves.lean#L93).

**Theorem · The complementary radial chart formula.** For valid chart parameters, the complementary radial chart is the chart length divided by radius plus that length. [`chartS_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxFarDecayLeaves.lean#L105).

**Theorem · The complementary chart decays once.** For valid chart parameters, the complementary radial chart has far-decay exponent one. [`chartS_far`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxFarDecayLeaves.lean#L114).

**Theorem · The decay factor has exponent zero.** The scalar decay factor satisfies exponent-zero far decay for valid chart parameters. [`decay_far`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxFarDecayLeaves.lean#L125).

**Theorem · The radial chart has exponent zero.** The compactified radial coordinate satisfies exponent-zero far decay for valid chart parameters. [`chartT_far`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxFarDecayLeaves.lean#L145).

**Theorem · The coordinate chart has exponent zero.** The pair consisting of radial chart and height ratio satisfies exponent-zero far decay. [`chart_far`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxFarDecayLeaves.lean#L154).

**Theorem · The chart lies in a fixed rectangle.** For valid chart parameters and radius at least one, the chart lies in the product of the unit radial interval and the height interval from minus one to one. [`chart_mem`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxFarDecayLeaves.lean#L158).

**Theorem · Local Lipschitz bounds survive addition.** The sum of locally Lipschitz maps is locally Lipschitz. [`locSlope_add`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxFarDecayLeaves.lean#L175).

**Theorem · Local Lipschitz scalar multiplication.** Multiplying a locally Lipschitz vector-valued map by a locally Lipschitz complex scalar preserves local Lipschitz regularity. [`locSlope_smul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxFarDecayLeaves.lean#L183).

**Theorem · Products with Lipschitz derivatives.** Two C¹ complex functions with locally Lipschitz derivatives have a differentiable product with locally Lipschitz derivative. [`tame_mul2`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxFarDecayLeaves.lean#L226).

**Theorem · Sums have locally Lipschitz derivatives.** Two differentiable complex functions with locally Lipschitz derivatives have a sum with the same properties. [`tame_add2`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxFarDecayLeaves.lean#L237).

**Theorem · Cubic endpoint factor of the mean mode.** The polar component of the included mean mode factors by the cube of one minus the radial coordinate, with a differentiable quotient whose derivative is locally Lipschitz. [`mean_factor_one`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxFarDecayLeaves.lean#L246).

**Theorem · Cubic factor of each mean component.** Every component of the included mean mode has a cubic outer-endpoint factor and a differentiable quotient with locally Lipschitz derivative. [`mean_factor`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxFarDecayLeaves.lean#L288).

**Theorem · Imaginary exponentials have norm one.** The exponential of any purely imaginary real phase has complex norm one. [`exp_unit`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxFarDecayLeaves.lean#L309).

**Theorem · Logarithmic phases have exponent zero.** Every fixed multiple of the regularized logarithmic phase gives a complex exponential with exponent-zero far decay. [`logPhase_exp_far`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxFarDecayLeaves.lean#L313).

**Theorem · Changing the origin preserves far decay.** Functions agreeing away from the spatial origin have the same supplied far-decay estimate. [`FarDecay.congr_far`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxFarDecayLeaves.lean#L384).

**Theorem · Angular phases have exponent zero.** Each included nonzero reduced field mode, multiplied by its angular phase, has exponent-zero far decay. [`angle_order0`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxFarDecayLeaves.lean#L407).

**Theorem · Fully phased modes have exponent zero.** Each included nonzero reduced field mode, with its full mode phase, has exponent-zero far decay. [`phased_order0`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxFarDecayLeaves.lean#L458).

**Theorem · Cubic factors in two wave components.** The radial and polar components of a nonzero high-order-three mode equal their order-zero versions multiplied by the cubic outer-endpoint factor. [`wave_factor01`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxFarDecayLeaves.lean#L475).

**Theorem · The azimuthal wave's cubic factor.** The azimuthal component factors by the cubic outer-endpoint weight with an explicit radial-component correction to its order-zero expression. [`wave_factor2`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxFarDecayLeaves.lean#L488).

**Theorem · Cubic far decay of nonzero modes.** Every included nonzero high-order-three reduced mode with its phase satisfies far decay of exponent three. [`phased_far_wave`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxFarDecayLeaves.lean#L537).

**Theorem · Cubic far decay of all included modes.** Every included high-order-three reduced mode with its phase, including the mean, satisfies far decay of exponent three. [`phased_far`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxFarDecayLeaves.lean#L585).

### Breakdown.FracCell.GivenAuxInverseSquare

This file combines radial L² estimates and finite angular representations to produce the inverse-square remainder required by the adjoint reduction. **Reading context:** Appendix B: represented fields and the auxiliary estimates used by the profile, pin and adjoint reductions (B.1 and B.9–B.13).

**Theorem · An integrable square bound gives L².** An almost-everywhere measurable vector field whose squared norm is dominated by an integrable function belongs to L². [`memLp_sq_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquare.lean#L25).

**Theorem · Pointwise equality preserves L².** A field pointwise equal to an L² field also belongs to L². [`memLp_of_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquare.lean#L33).

**Theorem · Axial rotation is continuous.** The axial-turn linear map is continuous. [`turn_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquare.lean#L37).

**Theorem · The radius is measurable.** Spatial norm is almost everywhere strongly measurable. [`aesm_norm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquare.lean#L50).

**Theorem · Measurability of operator evaluation.** Evaluating an almost-everywhere measurable operator field on an almost-everywhere measurable vector field preserves that measurability. [`aesm_apply`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquare.lean#L53).

**Theorem · Weighted L² of a derivative evaluation.** A radius-fourth weighted matrix-energy bound makes radius times the derivative applied to any radius-bounded vector field belong to L². [`apply_weighted`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquare.lean#L59).

**Theorem · Weighted L² of the adjoint drift.** The adjoint drift has radially weighted L² control when its field has radial L² control and its derivative has the stated radius-fourth matrix-energy bound. [`drift_weighted`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquare.lean#L75).

**Theorem · Weighted L² of adjoint convection.** The adjoint convection field has radial L² control under the stated profile bounds, radial adjoint bound and derivative-energy bound. [`conv_weighted`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquare.lean#L92).

**Theorem · Removing radial decay factors.** Inverse-radius decay of a nonnegative amplitude and inverse-square decay of a derivative give uniform bounds after the displayed radial weighting. [`decay_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquare.lean#L135).

**Theorem · Weighted L² survives addition.** Adding two fields with radially weighted L² control preserves that control. [`w_add`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquare.lean#L155).

**Theorem · Weighted L² survives subtraction.** Subtracting two fields with radially weighted L² control preserves that control. [`w_sub`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquare.lean#L159).

**Theorem · Scaling preserves weighted L².** Multiplying a field by a real scalar preserves its radially weighted L² control. [`w_smul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquare.lean#L163).

**Theorem · Weighted L² survives finite sums.** A finite sum of fields with radially weighted L² control retains that control. [`w_sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquare.lean#L167).

**Theorem · Measurability after removing radius.** Measurability of the radius-weighted field implies almost-everywhere measurability of the field itself. [`aesm_of_weighted`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquare.lean#L172).

**Theorem · The constructed profile is continuous.** A valid profile instance is continuous at every parameter. [`profile_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquare.lean#L184).

**Theorem · Weighted L² of a compact pin trace.** A bounded almost-everywhere measurable weak negative trace of a compactly supported field has radially weighted L² control. [`pinTrace_weighted_of_support`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquare.lean#L193).

**Theorem · Regularity of an amplitude direction.** An included single-coordinate amplitude direction is C¹, divergence-free, and has inverse-radius field decay with inverse-square derivative decay. [`amplitude_regular_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquare.lean#L240).

**Theorem · Finite modes of amplitude convection.** Convection of an included amplitude direction with the adjoint field has an almost-everywhere finite ring representation. [`ringRep_convAmp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquare.lean#L254).

**Theorem · Finite modes of the remainder.** The stated profile, auxiliary identifications and weak-derivative hypotheses give a finite ring representation for the inverse-square remainder. [`inverseSquare_ring`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquare.lean#L265).

**Theorem · Weighted L² of the remainder.** The stated profile and auxiliary weighted estimates make the inverse-square remainder belong to L² after multiplication by radius. [`inverseSquare_weighted`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquare.lean#L335).

**Theorem · A finite-mode weighted remainder.** The supplied profile and auxiliary hypotheses produce an almost-everywhere equal measurable inverse-square remainder with radial L² control and only finitely many angular modes. [`inverseSquare_of_given`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquare.lean#L395).

**Reader note.** The conclusion chooses a representative equal almost everywhere to the displayed remainder; its mode-vanishing assertion holds pointwise on every ring for that representative.

### Breakdown.FracCell.GivenAuxInverseSquareModes

This file proves finite angular support of the constructed fields and of their derivative and convection terms, then transfers that support to weak derivatives through almost-everywhere representatives. **Reading context:** Appendix B: represented fields and the auxiliary estimates used by the profile, pin and adjoint reductions (B.1 and B.9–B.13).

**Predicate · Scalar trigonometric sums on rings.** A scalar ring sum represents the real scalar field on every ring by one fixed finite set of integer complex phases. [`IsRingScalarTrigSum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L23).

**Predicate · Finite angular sums away from the axis.** The off-axis polynomial condition represents a complex field on every ring of nonzero radius by finitely many integer phases. [`IsPolyOff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L31).

**Predicate · Independence of the angular coordinate.** Angular invariance means that the field takes the same value at every angle on each fixed ring. [`IsInv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L35).

**Theorem · The height coordinate of a ring.** The third coordinate of a ring point is its height parameter. [`ring_two`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L37).

**Theorem · The first coordinate of a ring.** The first coordinate of a ring point is radius times cosine of its angle. [`ring_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L40).

**Theorem · The second coordinate of a ring.** The second coordinate of a ring point is radius times sine of its angle. [`ring_one`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L43).

**Theorem · The norm of a ring point.** The norm of a ring point is the square root of radius squared plus height squared. [`ring_norm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L46).

**Theorem · Zero-radius rings ignore angle.** At zero ring radius, changing the angle leaves the spatial point unchanged. [`ring_axis`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L53).

**Theorem · Enlarging off-axis angular support.** An off-axis finite angular expansion remains valid when the frequency set is enlarged. [`IsPolyOff.mono`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L56).

**Theorem · Support of a sum of angular expansions.** Adding off-axis angular expansions uses the union of their finite frequency sets. [`IsPolyOff.add`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L64).

**Theorem · Support of angular products.** Multiplying off-axis angular expansions uses pairwise sums of their frequencies. [`IsPolyOff.mul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L72).

**Theorem · Conjugation reverses angular frequencies.** Complex conjugation of an off-axis angular expansion negates its frequency set. [`IsPolyOff.conj`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L92).

**Theorem · Scaling a finite angular expansion.** Multiplication by a complex constant preserves the frequency set of an off-axis angular expansion. [`IsPolyOff.const_mul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L105).

**Theorem · Zero has empty off-axis support.** The zero complex field has an off-axis angular expansion with empty support. [`IsPolyOff.zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L114).

**Theorem · Finite sums have finite angular support.** A finite sum of fields with finite off-axis angular expansions has a finite off-axis expansion. [`IsPolyOff.sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L116).

**Theorem · Angular invariance gives the zero mode.** An angularly invariant complex field has off-axis support contained in the zero mode. [`IsPolyOff.of_inv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L126).

**Theorem · Real parts add reflected frequencies.** The real part of an off-axis angular expansion uses its original frequencies together with their negatives. [`IsPolyOff.ofReal_re`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L131).

**Theorem · Imaginary parts reflect frequencies.** The imaginary part of an off-axis angular expansion uses its original frequencies together with their negatives. [`IsPolyOff.ofReal_im`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L141).

**Theorem · The planar coordinate has frequency one.** The complex planar coordinate has a single off-axis angular frequency, equal to one. [`IsPolyOff.plane`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L151).

**Theorem · An integer phase has one frequency.** The integer angular exponential has off-axis support consisting of its phase index alone. [`IsPolyOff.angle`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L159).

**Theorem · Extending angular sums onto the axis.** Finite off-axis expansions of both vector components give a ring trigonometric sum after adding the zero frequency. [`trig_of_polyOff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L193).

**Theorem · Existence of support for an angular sum.** The sum of two complex fields with finite off-axis angular support also has finite support. [`ex_add`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L207).

**Theorem · Finite support of angular products.** The product of two complex fields with finite off-axis angular support also has finite support. [`ex_mul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L213).

**Theorem · Conjugates have finite angular support.** Conjugating a complex field preserves existence of finite off-axis angular support. [`ex_conj`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L219).

**Theorem · Real parts have finite angular support.** Taking a real part preserves existence of finite off-axis angular support. [`ex_re`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L223).

**Theorem · Invariant fields have finite support.** Every angularly invariant complex field has finite off-axis angular support. [`ex_inv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L227).

**Theorem · Pure phases have finite angular support.** Every integer angular phase has finite off-axis angular support. [`ex_angle`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L229).

**Theorem · Finite sums preserve finite support.** A finite sum of complex fields with finite off-axis angular support retains finite support. [`ex_sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L232).

**Theorem · Constants have finite angular support.** Every constant complex field has finite off-axis angular support. [`ex_const`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L235).

**Theorem · Coordinates have finite angular support.** Every spatial coordinate, included into the complex numbers, has finite off-axis angular support. [`ex_coord`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L237).

**Theorem · Finite support from radius and height.** Any complex function of spatial norm and height has finite off-axis angular support. [`ex_normInv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L255).

**Theorem · A scalar atom has finite angular support.** Every scalar atom term has finite off-axis angular support. [`ex_atomTerm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L258).

**Theorem · A component of an assembled vector.** Evaluating an assembled vector at a coordinate returns its supplied component. [`ofc`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L274).

**Theorem · The decay factor has finite support.** The decay factor, included into the complex numbers, has finite off-axis angular support. [`ex_decay`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L277).

**Theorem · Horizontal atom has finite support.** The horizontal component of an atom has finite off-axis angular support. [`ex_hor_atom`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L280).

**Theorem · Vertical atom has finite support.** The vertical component of an atom has finite off-axis angular support. [`ex_vert_atom`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L292).

**Theorem · The mode phase has finite support.** Every full mode phase has finite off-axis angular support. [`ex_modePhase`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L301).

**Theorem · Radial frame has finite angular support.** Each radial frame component has finite off-axis angular support. [`ex_radial`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L311).

**Theorem · Polar frame has finite angular support.** Each polynomial polar frame component has finite off-axis angular support. [`ex_polar`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L318).

**Theorem · Azimuthal frame has finite support.** Each polynomial azimuthal frame component has finite off-axis angular support. [`ex_azim`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L341).

**Theorem · Finite support of field components.** Each component of the complex decayed mode sum has finite off-axis angular support. [`ex_fieldComp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L364).

**Theorem · Extending a scalar sum onto the axis.** A scalar field with finite off-axis support becomes a scalar ring sum after adding the zero frequency. [`scalar_of_polyOff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L374).

**Theorem · Cell index bounded by mesh length.** The selected cell index never exceeds the length of the mesh list. [`cellIndex_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L385).

**Theorem · Bounded spline evaluation on the square.** Spline evaluation with either parity is bounded on the real unit square. [`spline_bd`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L391).

**Predicate · Uniform boundedness of a complex field.** Uniform boundedness means that one real constant bounds the norm of the complex field everywhere. [`IsBdd`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L406).

**Theorem · Bounded fields have bounded products.** The product of two uniformly bounded complex fields is uniformly bounded. [`IsBdd.mul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L408).

**Theorem · Bounded fields have bounded sums.** The sum of two uniformly bounded complex fields is uniformly bounded. [`IsBdd.add`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L415).

**Theorem · Conjugation preserves boundedness.** The conjugate of a uniformly bounded complex field is uniformly bounded. [`IsBdd.conj`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L420).

**Theorem · A constant field is bounded.** Every constant complex field is uniformly bounded. [`IsBdd.const`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L424).

**Theorem · Finite sums preserve boundedness.** A finite sum of uniformly bounded complex fields is uniformly bounded. [`IsBdd.sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L426).

**Theorem · Absolute bound for the radial chart.** Valid chart parameters give absolute radial chart coordinate at most one. [`chartT_abs`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L435).

**Theorem · Absolute bound for the height ratio.** The height-to-radius ratio has absolute value at most one. [`height_abs`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L445).

**Theorem · The angular weight is between 0 and 1.** The angular weight is between zero and one. [`q_bounds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L453).

**Theorem · Scalar atom terms are bounded.** For valid chart parameters, every displayed scalar atom term is uniformly bounded. [`bdd_atomTerm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L461).

**Theorem · The decay factor is bounded.** For valid chart parameters, the complex decay factor is uniformly bounded. [`bdd_decay`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L478).

**Theorem · Real parts of bounded fields are bounded.** A uniform complex norm bound gives a uniform absolute bound for the real part. [`bdd_re`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L487).

**Theorem · Bounded imaginary parts.** A uniform complex norm bound gives a uniform absolute bound for the imaginary part. [`bdd_im`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L491).

**Theorem · Norm bound by component absolute values.** The norm of an assembled vector is at most the sum of the absolute values of its three components. [`ofComponents_norm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L495).

**Theorem · Measurability of an assembled vector.** Three measurable real component functions give a measurable assembled vector field. [`ofComponents_meas`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L500).

**Theorem · Atoms are measurable and bounded.** For valid chart parameters, the constructed atom vector is measurable and uniformly bounded. [`atomOf_meas_bdd`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L510).

**Theorem · Atoms are locally integrable.** For valid chart parameters, every constructed atom field is locally integrable. [`atomOf_locInt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L538).

**Theorem · The radial frame is measurable.** The vector assembled from radial frame components is measurable. [`radial_meas`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L543).

**Theorem · A norm bound for the radial frame.** The norm of the radial frame vector is bounded by three. [`radial_bdd`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L554).

**Theorem · Local integrability of fluxes.** For valid chart parameters, the constructed flux operator field is locally integrable. [`fluxOf_locInt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L565).

**Theorem · The angular coordinate is measurable.** The planar angular coordinate is measurable. [`angle_meas`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L582).

**Theorem · Mode phases are measurable.** Every full mode phase is measurable. [`modePhase_meas`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L591).

**Theorem · Mode phases are bounded.** Every full mode phase is uniformly bounded. [`bdd_modePhase`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L596).

**Theorem · Absolute decay factor at most one.** For valid chart parameters, the absolute value of the scalar decay factor is at most one. [`decay_abs`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L599).

**Theorem · Pressure shapes are measurable.** Every displayed pressure shape is measurable as a function of space. [`shape_meas`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L608).

**Theorem · Pressure shapes are bounded.** For valid chart parameters, every displayed pressure shape is uniformly bounded. [`bdd_shape`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L629).

**Theorem · Local integrability of pressure.** For valid chart parameters, the pressure assembled from its finite data is locally integrable. [`pressureOf_locInt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L647).

**Theorem · Coordinate vectors are scaled units.** A single-coordinate vector is the corresponding unit vector multiplied by that coordinate. [`single_smul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L671).

**Theorem · Differentiating a circular ring.** The derivative of a ring point with respect to angle is its axial-turn vector. [`ring_hasDerivAt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L676).

**Definition · Horizontal projection as a linear map.** The horizontal projection combines the first two vector coordinates into a complex number. [`horCLM`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L692).

**Definition · Vertical projection as a linear map.** The vertical projection includes the third vector coordinate into the complex numbers. [`vertCLM`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L696).

**Theorem · Evaluating horizontal projection.** The horizontal linear map returns the first coordinate plus the imaginary unit times the second. [`horCLM_apply`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L698).

**Theorem · Evaluating vertical projection.** The vertical linear map returns the third coordinate as a complex number. [`vertCLM_apply`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L701).

**Theorem · Differentiating a finite phase sum.** The derivative of a finite angular phase sum multiplies each coefficient by its integer frequency times the imaginary unit. [`trigSeries_hasDerivAt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L704).

**Theorem · Angular derivatives preserve support.** The derivative of a differentiable ring sum along axial turn has the same finite angular support. [`trig_turnDeriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L716).

**Theorem · Weighted finite sums have finite support.** A finite real linear combination of ring trigonometric fields has finite angular support. [`trig_fsum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L750).

**Theorem · Radial derivatives stay in a finite span.** A pointwise derivative in an auxiliary parameter of finite phase sums with a common support still lies in that same phase span. [`span_limit`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L763).

**Theorem · Scaling a ring scales radius and height.** Scaling a ring's radius and height by the same real number scales the spatial ring point by that number. [`ring_smul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L797).

**Theorem · Radial derivatives preserve support.** The derivative of a differentiable ring sum applied to position itself has the same finite angular support. [`trig_selfDeriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L801).

**Theorem · Off-axis equality preserves support.** Fields that agree on all rings of nonzero radius have the same supplied off-axis frequency support. [`polyOff_congr`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L844).

**Theorem · Horizontal support of a ring sum.** The horizontal component of a ring trigonometric field has the same off-axis support. [`polyOff_hor`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L850).

**Theorem · Vertical support of a ring sum.** The vertical component of a ring trigonometric field has the same off-axis support. [`polyOff_vert`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L856).

**Predicate · A real component with finite support.** A real component has the finite-polynomial property when its complex inclusion has some finite off-axis angular support. [`IsCompPoly`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L862).

**Theorem · Adding real finite-mode components.** The sum of real components with finite off-axis angular support retains finite support. [`IsCompPoly.add`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L864).

**Theorem · Multiplying real finite-mode components.** The product of real components with finite off-axis angular support retains finite support. [`IsCompPoly.mul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L869).

**Theorem · Finite support of real constants.** A constant real function has finite off-axis angular support. [`IsCompPoly.const`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L874).

**Theorem · Subtracting real finite-mode components.** The difference of real components with finite off-axis angular support retains finite support. [`IsCompPoly.sub`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L876).

**Theorem · Finite sums of real mode components.** A finite sum of real finite-mode components has finite off-axis angular support. [`IsCompPoly.sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L881).

**Theorem · Finite support of vector coordinates.** Every real coordinate of a vector ring sum has finite off-axis angular support. [`ex_comp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L887).

**Theorem · Height derivatives preserve support.** The derivative of a differentiable ring sum in the vertical coordinate direction has the same finite angular support. [`trig_heightDeriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L900).

**Theorem · Planar squared norm from spatial norm.** Spatial norm squared minus height squared equals the sum of squares of the planar coordinates. [`nsq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L947).

**Theorem · First coordinate derivative formula.** Away from the axis, the first coordinate evaluation of a linear map is recovered from its position, angular-turn and height evaluations using the displayed planar-radius formula. [`grad_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L952).

**Theorem · Second coordinate derivative formula.** Away from the axis, the second coordinate evaluation of a linear map is recovered from its position, angular-turn and height evaluations using the displayed planar-radius formula. [`grad_one`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L962).

**Theorem · Nonzero ring radius excludes the axis.** A ring of nonzero radius has nonzero sum of squared planar coordinates. [`ring_q`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L972).

**Theorem · Finite support of partial derivatives.** Every coordinate derivative of a differentiable finite ring sum has finite off-axis angular support. [`ex_grad`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L979).

**Theorem · Curl in coordinate entries.** Each curl component is the double sum of derivative entries weighted by the three-index permutation sign. [`curl_apply`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L1000).

**Theorem · Adjoint action in coordinates.** Each coordinate of an operator's adjoint applied to a vector is the displayed sum of the vector coordinates times matrix entries. [`adjoint_apply`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L1004).

**Theorem · Cross products preserve finite support.** The cross product of vector fields with finite-mode components has finite-mode components. [`compPoly_cross`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L1012).

**Theorem · Finite support of convection.** The adjoint convection of differentiable fields with finite ring support has finite ring support. [`trig_convection`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L1028).

**Theorem · Support of an indexed finite sum.** Summing an indexed family of off-axis expansions uses the finite union of the displayed support sets. [`polyOff_biUnion`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L1062).

**Theorem · Radius-height functions: zero mode.** A complex function depending only on spatial norm and height has off-axis support contained in the zero frequency. [`of_normInv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L1075).

**Theorem · Angular support of a mode phase.** The full mode phase has off-axis support in the singleton containing the mode index times the chart's angular period index. [`modePhase_poly`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L1078).

**Theorem · Component support independent of phase.** Each complex field component has a finite angular support that works for every phase parameter. [`fieldComp_unif`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L1089).

**Theorem · Field support independent of phase.** The assembled field has one finite ring-frequency set that works for every phase parameter. [`ringTrig_fieldOf_unif`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L1103).

**Theorem · Common support under finite sums.** A finite real linear combination of ring sums with one common support retains that support. [`trig_fsum_unif`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L1117).

**Theorem · Uniform support of the profile family.** The whole profile family has one finite ring-frequency set valid for every parameter. [`profile_unif`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L1126).

**Theorem · The reduced field is affine in phase.** Each reduced field component at phase beta equals its phase-zero value plus beta times the difference between its phase-one and phase-zero values. [`red_affine`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L1131).

**Theorem · Phase differentiability of components.** Every reduced field component is differentiable in its phase parameter. [`red_diff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L1138).

**Theorem · Mode phases are differentiable in phase.** The mode-phase expression is differentiable in its phase parameter. [`modePhase_diff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L1146).

**Theorem · Differentiability in phase.** At every spatial point, the constructed field is differentiable with respect to phase. [`fieldOf_diffBeta`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L1154).

**Theorem · The profile varies differentiably.** At every spatial point, the profile is differentiable with respect to its finite-dimensional parameter. [`profile_diffq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L1168).

**Theorem · Finite support of tangent fields.** Every tangent field of the profile has a finite ring-frequency representation. [`tangent_ringTrig`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L1175).

**Theorem · Components preserve local integrability.** Each coordinate of a locally integrable vector field is locally integrable. [`comp_locInt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L1215).

**Theorem · Assembling a finite ring representative.** Almost-everywhere finite ring representatives for all real coordinates combine into a finite ring representative of the vector field. [`rep_of_components`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L1223).

**Theorem · Weak negative traces keep finite support.** A locally integrable weak negative trace of a locally integrable finite ring sum has a finite ring representation. [`ringRep_of_weakNegTrace`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L1246).

**Theorem · Finite support of weak gradients.** A locally integrable weak gradient of a locally integrable finite scalar ring sum has a finite ring representation. [`ringRep_of_weakScalarGradient`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L1251).

**Theorem · Weak divergence keeps finite support.** A locally integrable weak matrix divergence has a finite ring representation when the locally integrable operator field's columns share finite ring support. [`ringRep_of_weakMatrixDivergence`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L1256).

**Theorem · The constructed field has finite support.** The field assembled from its finite data is a finite ring trigonometric sum. [`ringTrig_fieldOf`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L1262).

**Theorem · The constructed atom has finite support.** The atom assembled from its finite harmonic data is a finite ring trigonometric sum. [`ringTrig_atomOf`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L1275).

**Theorem · Finite support of adjoint pressure.** Every auxiliary adjoint pressure is a finite scalar ring trigonometric sum. [`ringTrig_adjointPressureField`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L1280).

**Theorem · Common finite support of flux columns.** All coordinate columns of an auxiliary flux field share one finite ring-frequency set. [`ringTrig_fluxFieldOf_columns`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L1301).

**Theorem · The adjoint field is differentiable.** Valid auxiliary data give a differentiable adjoint field. [`differentiable_adjointField`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L1329).

**Theorem · The adjoint field has finite support.** Every constructed adjoint field is a finite ring trigonometric sum. [`ringTrig_adjointField`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L1336).

**Theorem · The adjoint field is locally integrable.** Valid auxiliary data give a locally integrable adjoint field. [`locInt_adjointField`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L1341).

**Theorem · Atom families are locally integrable.** For valid chart parameters, an evaluated finite atom family is locally integrable. [`locInt_atomFamily`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L1345).

**Theorem · Adjoint pressure is locally integrable.** For valid chart parameters, every auxiliary adjoint pressure is locally integrable. [`locInt_adjointPressureField`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L1352).

**Theorem · Pin potentials are locally integrable.** Valid auxiliary data give locally integrable pin-potential fields. [`locInt_pinPotentialField`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L1360).

**Theorem · Auxiliary flux is locally integrable.** For valid chart parameters, each auxiliary flux field is locally integrable. [`locInt_fluxFieldOf`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L1365).

**Theorem · Finite modes of the radial derivative.** The derivative of the adjoint field applied to position has a finite ring representation. [`ringRep_fderiv_self`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L1372).

**Theorem · Finite modes of the angular derivative.** The derivative of the adjoint field applied to axial turn has a finite ring representation. [`ringRep_fderiv_turn`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L1379).

**Theorem · Adjoint convection has finite support.** Adjoint convection with the profile or a tangent field has a finite ring representation under the stated regularity hypotheses. [`ringRep_convectionField`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareModes.lean#L1386).

### Breakdown.FracCell.GivenAuxInverseSquareOpen

This file applies the finite-mode calculus to the drift, convection and weak derivative terms appearing in the inverse-square remainder. **Reading context:** Appendix B: represented fields and the auxiliary estimates used by the profile, pin and adjoint reductions (B.1 and B.9–B.13).

**Theorem · Subtracting ring trigonometric sums.** The difference of ring trigonometric sums supported on the same finite frequency set has the same support. [`trig_sub`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareOpen.lean#L18).

**Theorem · Finite angular support of an atom family.** Each evaluated finite atom family is a ring trigonometric sum with finite frequency support. [`trig_atomFamily`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareOpen.lean#L24).

**Theorem · Axial turn preserves angular support.** Applying the axial-turn map preserves the frequency support of a ring trigonometric sum. [`trig_turn`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareOpen.lean#L29).

**Theorem · A ring sum supplies a representative.** A pointwise ring trigonometric sum supplies an almost-everywhere finite ring representation. [`ringRep_of_trig`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareOpen.lean#L47).

**Theorem · Weighted L² implies measurability.** Radially weighted L² control implies almost-everywhere strong measurability of the unweighted field. [`aesm_of_weighted`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareOpen.lean#L50).

**Theorem · Weighted L² gives local integrability.** Radially weighted L² control implies local integrability of the unweighted field. [`locInt_of_weighted`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareOpen.lean#L61).

**Theorem · Finite ring representation of drift.** The adjoint drift built from valid auxiliary data has a finite ring representation. [`ringRep_drift`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareOpen.lean#L65).

**Theorem · Finite ring representation of convection.** Adjoint convection with the profile or one of its tangent fields has a finite ring representation. [`ringRep_convection`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareOpen.lean#L75).

**Theorem · Finite modes of the sharp trace.** The weak negative trace of the viscosity-adjoint plus sharp field has a finite ring representation under radial L² control. [`ringRep_sharpTrace`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareOpen.lean#L82).

**Theorem · Finite angular support of the pin trace.** A bounded measurable weak negative trace of a pin potential has a finite ring representation. [`ringRep_pinTrace`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareOpen.lean#L98).

**Theorem · Finite modes of the pressure gradient.** A radially weighted L² weak gradient of the auxiliary adjoint pressure has a finite ring representation. [`ringRep_pressureGrad`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareOpen.lean#L106).

**Theorem · Finite angular support of the dual trace.** A weak negative trace of the dual field with radial L² control has a finite ring representation. [`ringRep_dualTrace`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareOpen.lean#L113).

**Theorem · Finite support of the potential trace.** A weak negative trace of the auxiliary potential with radial L² control has a finite ring representation. [`ringRep_potentialTrace`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareOpen.lean#L120).

**Theorem · Finite modes of the flux divergence.** A weak matrix divergence of the auxiliary flux with radial L² control has a finite ring representation. [`ringRep_fluxDiv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareOpen.lean#L128).

### Breakdown.FracCell.GivenAuxInverseSquareRing

This file distinguishes pointwise finite trigonometric support from an almost-everywhere representative, and uses weak-derivative uniqueness to move between representatives. **Reading context:** Appendix B: represented fields and the auxiliary estimates used by the profile, pin and adjoint reductions (B.1 and B.9–B.13).

**Predicate · Finite trigonometric sums on rings.** A ring trigonometric sum represents both horizontal and vertical field components on each ring using one fixed finite set of integer frequencies. [`IsRingTrigSum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareRing.lean#L16).

**Predicate · An almost-everywhere finite ring model.** A finite ring representation means that the field agrees almost everywhere with a field having finite trigonometric support on every ring. [`HasRingRep`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareRing.lean#L23).

**Theorem · Nonzero integer phases integrate to zero.** A nonzero integer complex phase has zero integral over the interval from minus pi to pi. [`integral_exp_int`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareRing.lean#L26).

**Theorem · Modes outside a finite ring sum vanish.** An angular mode outside the support of a ring trigonometric sum is zero. [`angularMode_eq_zero_of_trig`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareRing.lean#L43).

**Theorem · Enlarging the finite angular support.** A ring trigonometric sum remains valid when its finite frequency set is enlarged. [`IsRingTrigSum.mono`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareRing.lean#L65).

**Theorem · Adding ring sums with common support.** The sum of two ring trigonometric fields with the same support retains that support. [`IsRingTrigSum.add`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareRing.lean#L76).

**Theorem · Scaling a ring trigonometric sum.** Multiplying a ring trigonometric field by a real scalar preserves its frequency support. [`IsRingTrigSum.smul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareRing.lean#L92).

**Theorem · The zero field has empty angular support.** The zero vector field is a ring trigonometric sum supported on the empty frequency set. [`IsRingTrigSum.zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareRing.lean#L113).

**Theorem · Adding finite ring representatives.** The sum of fields with almost-everywhere finite ring representations has such a representation. [`HasRingRep.add`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareRing.lean#L118).

**Theorem · Scaling a finite ring representative.** Multiplication by a real scalar preserves existence of a finite ring representation. [`HasRingRep.smul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareRing.lean#L127).

**Theorem · Subtracting finite ring representatives.** The difference of fields with finite ring representations has a finite ring representation. [`HasRingRep.sub`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareRing.lean#L133).

**Theorem · Finite sums of ring representatives.** A finite sum of fields with finite ring representations again has a finite ring representation. [`HasRingRep.sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareRing.lean#L139).

**Theorem · A representative with finite modes.** A finite ring representation supplies an almost-everywhere equal representative whose horizontal and vertical modes vanish outside one finite set on every ring. [`HasRingRep.modes`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareRing.lean#L151).

**Theorem · Ring models respect a.e. equality.** Almost-everywhere equal fields share the existence of a finite ring representation. [`HasRingRep.of_ae`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareRing.lean#L162).

**Theorem · Test pairings determine a field a.e..** Locally integrable vector fields with equal pairings against all vector tests agree almost everywhere. [`ae_eq_of_test_pairing`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareRing.lean#L169).

**Theorem · Uniqueness of a weak negative trace.** Two locally integrable weak negative traces of the same field agree almost everywhere. [`weakNegTrace_ae_unique`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareRing.lean#L197).

**Theorem · Uniqueness of weak matrix divergence.** Two locally integrable weak matrix divergences of the same operator field agree almost everywhere. [`weakMatrixDivergence_ae_unique`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareRing.lean#L202).

**Theorem · Uniqueness of a weak scalar gradient.** Two locally integrable weak gradients of the same scalar field agree almost everywhere. [`weakScalarGradient_ae_unique`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareRing.lean#L208).

**Theorem · Local integrability from weighted L².** A measurable field with radially weighted L² control is locally integrable. [`weighted_locallyIntegrable`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenAuxInverseSquareRing.lean#L232).
<!-- /passage:front -->

