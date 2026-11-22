
<!-- passage:front -->
# Library guide 16: Breakdown/FracCell

**Navier–Stokes pages:** [the paper](../navier-stokes-paper/paper.pdf) · [proof routes](../navier-stokes-routes/paper.md) · [routes in detail](../navier-stokes-route-details/paper.md) · library guide: [1](../navier-stokes-library-01/paper.md) [2](../navier-stokes-library-02/paper.md) [3](../navier-stokes-library-03/paper.md) [4](../navier-stokes-library-04/paper.md) [5](../navier-stokes-library-05/paper.md) [6](../navier-stokes-library-06/paper.md) [7](../navier-stokes-library-07/paper.md) [8](../navier-stokes-library-08/paper.md) [9](../navier-stokes-library-09/paper.md) [10](../navier-stokes-library-10/paper.md) [11](../navier-stokes-library-11/paper.md) [12](../navier-stokes-library-12/paper.md) [13](../navier-stokes-library-13/paper.md) [14](../navier-stokes-library-14/paper.md) [15](../navier-stokes-library-15/paper.md) **16** [17](../navier-stokes-library-17/paper.md) [18](../navier-stokes-library-18/paper.md) [19](../navier-stokes-library-19/paper.md) [20](../navier-stokes-library-20/paper.md) [21](../navier-stokes-library-21/paper.md) [22](../navier-stokes-library-22/paper.md) [23](../navier-stokes-library-23/paper.md) [24](../navier-stokes-library-24/paper.md) [25](../navier-stokes-library-25/paper.md) [26](../navier-stokes-library-26/paper.md) [27](../navier-stokes-library-27/paper.md) [28](../navier-stokes-library-28/paper.md) [29](../navier-stokes-library-29/paper.md) [30](../navier-stokes-library-30/paper.md)

*A plain title and a sentence for each declaration in `Breakdown.FracCell.AdjointConvectionPairing` to `Breakdown.FracCell.EnergyRadialPairing` of Alpöge and Buckmaster's Lean at `ad53419de079eb8f95f60313473374624a348546`, in the authors' file order. Prepared with AI assistance. The authors have not reviewed it.*

Each paragraph names one declaration and says whether it is a definition, a proposition that the library defines (its name usually ends in `Holds` or `Statement`) or a proved result, then what it states. Click a paragraph to open its Lean on the right.

### Breakdown.FracCell.AdjointConvectionPairing

This file identifies the weak convection pairing with its adjoint expression, using L2 integration by parts for the cell certificate fields.

**Integrable L2 inner product.** The pointwise inner product of two L2 fields is integrable. (`Breakdown.FracInternal.ConvectionPairing.inner_int`)

**Matrix columns belong to L2.** An almost-everywhere measurable matrix field with integrable entry-square sum has each column in L2. (`Breakdown.FracInternal.ConvectionPairing.col_memLp`)

**L2 membership from a majorant.** An almost-everywhere measurable field dominated almost everywhere by an L2 scalar function belongs to L2. (`Breakdown.FracInternal.ConvectionPairing.memLp_of_bound`)

**Coordinate bounded by vector norm.** Every coordinate's absolute value is at most the spatial vector norm. (`Breakdown.FracInternal.ConvectionPairing.coord_le`)

**Coordinate unit-vector norm.** Every standard spatial unit vector has norm one. (`Breakdown.FracInternal.ConvectionPairing.unit_norm`)

**Matrix entry bounded by operator norm.** The absolute value of a matrix entry is at most its operator norm. (`Breakdown.FracInternal.ConvectionPairing.apply_coord_le`)

**Differentiate a vector coordinate.** For a differentiable vector field, differentiating one coordinate gives that coordinate of the field derivative. (`Breakdown.FracInternal.ConvectionPairing.coord_fderiv`)

**Coordinate expansion of a vector.** A spatial vector is the sum of its coordinate multiples of the unit vectors. (`Breakdown.FracInternal.ConvectionPairing.sum_unit`)

**Pairing with a coordinate vector.** The inner product with a coordinate unit vector extracts the corresponding coordinate. (`Breakdown.FracInternal.ConvectionPairing.inner_unit`)

**Weak product rule with a scalar.** A weakly differentiable field multiplied by a C1 scalar satisfies the stated tested product rule. (`Breakdown.FracInternal.ConvectionPairing.weak_smul_left`)

**Take a coordinate through an integral.** For an integrable vector field, taking a coordinate commutes with integration. (`Breakdown.FracInternal.ConvectionPairing.integral_coord`)

**Locally integrable coordinates.** Each coordinate of a locally integrable vector field is locally integrable. (`Breakdown.FracInternal.ConvectionPairing.loc_coord`)

**Weak product rule with a vector.** A weakly differentiable scalar coordinate times a C1 vector field satisfies the stated tested product rule. (`Breakdown.FracInternal.ConvectionPairing.weak_smul_right`)

**Expand the curl cross pairing.** The curl cross-product pairing equals the stated sum of antisymmetrized matrix-column pairings. (`Breakdown.FracInternal.ConvectionPairing.cross_alg`)

**Adjoint convection pairing identity.** For the stated adjoint, solenoidal decaying background and second-order field assumptions, the convection-adjoint pairing is integrable and equals the two displayed convection terms. (`Breakdown.CellCert.Reduction.convectionPairing_eq`)

### Breakdown.FracCell.AdjointConvectionPairingParts

This file extends weak derivative identities to complex tests and Fourier distributions, then obtains the integration-by-parts identity used in the adjoint convection calculation.

**Complexify a weak derivative test.** The real weak derivative identity extends to smooth compactly supported complex tests after complexifying the fields. (`Breakdown.FracInternal.ConvectionPairing.test_complex`)

**Extend weak testing to rapid decay.** For L2 fields, the weak derivative identity holds against every complex Schwartz test. (`Breakdown.FracInternal.ConvectionPairing.dir_rapid`)

**Weak derivative as a distribution.** The L2 weak derivative identity becomes the corresponding directional derivative identity for tempered distributions. (`Breakdown.FracInternal.ConvectionPairing.lineDeriv_dir`)

**Fourier transform of a weak derivative.** A distributional derivative relation between L2 fields becomes multiplication by 2πi times the frequency coordinate almost everywhere. (`Breakdown.FracInternal.ConvectionPairing.freq_dir`)

**Real pairing through Fourier transform.** The real L2 pairing equals the real part of the complex Fourier-space pairing. (`Breakdown.FracInternal.ConvectionPairing.real_pair_eq`)

**Weak L2 integration by parts.** Two L2 fields with the stated L2 weak derivatives satisfy the antisymmetric derivative-pairing identity. (`Breakdown.FracInternal.ConvectionPairing.pair_of_dir`)

**C1 compact tests for weak gradients.** A locally integrable weak gradient can be tested against C1 compactly supported scalar functions. (`Breakdown.FracInternal.ConvectionPairing.weak_of_C1`)

### Breakdown.FracCell.AdmissibleLinear

This file establishes the linear closure properties of the symmetry and regularity conditions imposed on admissible cell fields.

**Axial step fixes zero.** The discrete axial rotation step sends zero to zero. (`Breakdown.CellCert.Assembly.AdmissibleLinearInternal.turnStep_zero`)

**Reflection fixes zero.** The reflection sends zero to zero. (`Breakdown.CellCert.Assembly.AdmissibleLinearInternal.mirror_zero`)

**Axial step preserves addition.** The discrete axial rotation step preserves vector addition. (`Breakdown.CellCert.Assembly.AdmissibleLinearInternal.turnStep_add`)

**Reflection preserves addition.** The reflection preserves vector addition. (`Breakdown.CellCert.Assembly.AdmissibleLinearInternal.mirror_add`)

**Axial step preserves real scaling.** The discrete axial rotation step commutes with real scalar multiplication. (`Breakdown.CellCert.Assembly.AdmissibleLinearInternal.turnStep_smul`)

**Reflection preserves real scaling.** The reflection commutes with real scalar multiplication. (`Breakdown.CellCert.Assembly.AdmissibleLinearInternal.mirror_smul`)

**Zero field has every class symmetry.** The zero vector field satisfies the class-field condition at every order. (`Breakdown.CellCert.Assembly.AdmissibleLinearInternal.class_zero`)

**Class symmetry is closed under sums.** The sum of two fields in the same symmetry class remains in that class. (`Breakdown.CellCert.Assembly.AdmissibleLinearInternal.class_add`)

**Class symmetry is closed under scaling.** A real multiple of a class field remains in the same class. (`Breakdown.CellCert.Assembly.AdmissibleLinearInternal.class_smul`)

**Zero is a gradient field.** The zero vector field satisfies the gradient-field condition. (`Breakdown.CellCert.Assembly.AdmissibleLinearInternal.gradient_zero`)

**Real multiples of gradient fields.** A real multiple of a gradient field is again a gradient field. (`Breakdown.CellCert.Assembly.AdmissibleLinearInternal.gradient_smul`)

**Zero is a second-order field.** The zero velocity, gradient and second derivative satisfy the second-order field conditions at every order. (`Breakdown.CellCert.Assembly.AdmissibleLinearInternal.second_zero`)

**Admissible fields form a linear class.** The zero field tuple is admissible, and sums and real scalar multiples of admissible field tuples remain admissible. (`Breakdown.CellCert.Assembly.admissibleLinear`)

### Breakdown.FracCell.AdmissiblePotential

This file obtains a measurable locally square-integrable scalar potential from the weak gradient-field condition.

**Vanishing forced by a bad test.** Under the stated weak identity, a test whose potential term is not almost-everywhere measurable forces every tested gradient pairing to vanish. (`Breakdown.CellCert.CellFormula.AdmissiblePotentialInternal.right_zero_of_bad`)

**Integrable tested gradient component.** A measurable gradient field with the stated local square-integrability has integrable compactly supported tested components. (`Breakdown.CellCert.CellFormula.AdmissiblePotentialInternal.test_mul_integrable`)

**Detect a nonmeasurable potential.** If the proposed scalar potential is not almost-everywhere measurable, some smooth compact test has a nonmeasurable derivative-weighted potential term. (`Breakdown.CellCert.CellFormula.AdmissiblePotentialInternal.bad_exists`)

**Choose a regular weak potential.** Every gradient field has an almost-everywhere measurable, locally square-integrable scalar potential satisfying the coordinate weak derivative identities. (`Breakdown.CellCert.CellFormula.admissiblePotential_holds`)

### Breakdown.FracCell.AngularFrame

This file converts weak angular differentiation in Cartesian coordinates into the cylindrical-frame matrix-mode identity.

**Expand a vector in its coordinates.** Every spatial vector equals the sum of its coordinate multiples of the standard unit vectors. (`Breakdown.CellCert.CellEnergy.Internal.AngularFrame.vec_expand`)

**Expand a matrix pairing.** A linear-map pairing is the double sum of its coordinate matrix entries weighted by the two input coordinates. (`Breakdown.CellCert.CellEnergy.Internal.AngularFrame.inner_expand`)

**Gradient of one matrix entry.** The auxiliary vector collects the first index of a second-derivative tensor for a fixed matrix entry. (`Breakdown.CellCert.CellEnergy.Internal.AngularFrame.gv`)

**Pair the auxiliary gradient vector.** Pairing the auxiliary vector with a direction recovers the corresponding second-derivative tensor entry in that direction. (`Breakdown.CellCert.CellEnergy.Internal.AngularFrame.gv_inner`)

**Expand the angular third-order entry.** The angular frame component of the second derivative expands into the stated Cartesian component pairings. (`Breakdown.CellCert.CellEnergy.Internal.AngularFrame.third_expand`)

**Expand a cylindrical matrix entry.** A matrix entry in the cylindrical frame is the corresponding double coordinate expansion. (`Breakdown.CellCert.CellEnergy.Internal.AngularFrame.mat_expand`)

**Differentiate a frame coordinate.** The derivative of a cylindrical-frame coordinate is the stated frame-turn combination. (`Breakdown.CellCert.CellEnergy.Internal.AngularFrame.frame_comp_deriv`)

**Smooth frame coordinates.** Every cylindrical-frame coordinate is a smooth function of angle. (`Breakdown.CellCert.CellEnergy.Internal.AngularFrame.frame_comp_smooth`)

**Periodic frame coordinates.** Every cylindrical-frame coordinate has period 2π. (`Breakdown.CellCert.CellEnergy.Internal.AngularFrame.frame_comp_periodic`)

**Angular matrix test weight.** The angular test weight is the negative-frequency exponential times two cylindrical-frame coordinates. (`Breakdown.CellCert.CellEnergy.Internal.AngularFrame.wgt`)

**Derivative of the angular weight.** The angular weight derivative combines the frequency factor with the derivatives of its two frame coordinates. (`Breakdown.CellCert.CellEnergy.Internal.AngularFrame.wgt_hasDeriv`)

**Smooth angular matrix weight.** The angular matrix test weight is smooth. (`Breakdown.CellCert.CellEnergy.Internal.AngularFrame.wgt_smooth`)

**Periodic integer-frequency weight.** At integer frequency, the angular matrix test weight has period 2π. (`Breakdown.CellCert.CellEnergy.Internal.AngularFrame.wgt_periodic`)

**Matrix angular-combination identity.** The angular matrix combination equals the stated negative derivative-weight expansion. (`Breakdown.CellCert.CellEnergy.Internal.AngularFrame.comb_algebra`)

**Integrable continuous complex weight.** A continuous complex weight times an interval-integrable real function is integrable over one full circle. (`Breakdown.CellCert.CellEnergy.Internal.AngularFrame.ii_cmul`)

**Integrable double coordinate sum.** A finite double sum of circle-integrable functions is circle-integrable. (`Breakdown.CellCert.CellEnergy.Internal.AngularFrame.ii_sum2`)

**Integrate a double coordinate sum.** A circle integral commutes with a finite double sum of integrable coordinate terms. (`Breakdown.CellCert.CellEnergy.Internal.AngularFrame.int_sum2`)

**Angular gradient-mode formula.** The component integrability and tested angular identities give the stated frame-combination formula for the angular gradient mode. (`Breakdown.CellCert.CellEnergy.Internal.AngularFrame.point`)

**Local integrability from a square bound.** An almost-everywhere measurable scalar whose square has an integrable majorant is locally integrable. (`Breakdown.CellCert.CellEnergy.Internal.AngularFrame.locInt_sq`)

**Vector local integrability from energy.** An almost-everywhere measurable vector field whose squared norm has an integrable majorant is locally integrable. (`Breakdown.CellCert.CellEnergy.Internal.AngularFrame.locInt_vec`)

**Norm of a coordinate unit vector.** Every standard coordinate unit vector has norm one. (`Breakdown.CellCert.CellEnergy.Internal.AngularFrame.unit_norm`)

**Bound a coordinate pairing square.** The square of a vector's pairing with a coordinate unit vector is at most its norm squared. (`Breakdown.CellCert.CellEnergy.Internal.AngularFrame.inner_sq_le`)

**Measurable matrix columns.** Evaluating an almost-everywhere measurable matrix field at a fixed unit vector preserves almost-everywhere measurability. (`Breakdown.CellCert.CellEnergy.Internal.AngularFrame.meas_G`)

**Measurable second-derivative columns.** Evaluating an almost-everywhere measurable second-derivative field at two unit vectors preserves almost-everywhere measurability. (`Breakdown.CellCert.CellEnergy.Internal.AngularFrame.meas_H`)

**Column energy below matrix energy.** The squared norm of one matrix column is at most the sum of the squared matrix entries. (`Breakdown.CellCert.CellEnergy.Internal.AngularFrame.G_sq_le`)

**Tensor entry below total energy.** The squared norm of a tensor entry is at most the sum over all coordinate pairs. (`Breakdown.CellCert.CellEnergy.Internal.AngularFrame.H_sq_le`)

**Angular frame identity from weak tests.** The weak circle statement expresses each angular gradient mode as the prescribed frequency and frame combination of gradient modes almost everywhere under the energy-setting hypotheses. (`Breakdown.CellCert.CellEnergy.angularFrame_of_circle`)

### Breakdown.FracCell.AngularHeightMode

This file combines the weak circle identity with symmetry of second derivatives to identify angular and height mode entries.

**Angular second-derivative mode.** For a second-order field, the weak circle identity gives the frame-combination formula almost everywhere at positive radius. (`Breakdown.CellCert.CellFormula.Internal.AngularHeightMode.turn_second`)

**Expand a bilinear map.** A bilinear map applied to two vectors is the double sum of its coordinate evaluations. (`Breakdown.CellCert.CellFormula.Internal.AngularHeightMode.bil_expand`)

**Coordinate symmetry implies symmetry.** Symmetry of a bilinear map on every coordinate pair implies symmetry on all input vectors. (`Breakdown.CellCert.CellFormula.Internal.AngularHeightMode.bilin_symm`)

**Swap the last two frame indices.** Coordinate symmetry of the second derivative permits swapping the final two indices of its cylindrical-frame tensor. (`Breakdown.CellCert.CellFormula.Internal.AngularHeightMode.third_swap`)

**Swap the final mode indices.** For a second-order field, the final two third-order mode indices can be swapped almost everywhere at positive radius. (`Breakdown.CellCert.CellFormula.Internal.AngularHeightMode.mode_swap`)

**Angular-height mode identity.** The weak circle statement expresses radius times each angular-height second-derivative mode as its frequency multiple of the height-gradient mode plus the corresponding frame correction, almost everywhere at positive radius for second-order fields. (`Breakdown.CellCert.CellFormula.angularHeightMode_of_circle`)

### Breakdown.FracCell.AngularMode

This file derives the cylindrical Fourier-mode identities for angular derivatives, including the frame-rotation correction terms.

**Angular derivative of the frame.** The frame-turn vector consists of the angular unit vector, minus the radial unit vector and zero. (`Breakdown.CellCert.CellFormula.Internal.AngularMode.turnUnit`)

**Cartesian field component.** The scalar component pairs the vector field with a chosen coordinate unit vector. (`Breakdown.CellCert.CellFormula.Internal.AngularMode.fc`)

**Gradient of a field component.** The component-gradient vector collects the corresponding row of the matrix field in Cartesian coordinates. (`Breakdown.CellCert.CellFormula.Internal.AngularMode.gc`)

**Angular vector test weight.** The test weight is a negative-frequency exponential multiplied by one cylindrical-frame coordinate. (`Breakdown.CellCert.CellFormula.Internal.AngularMode.wt`)

**Coordinate expansion of a vector.** Every vector is the sum of its coordinate multiples of the standard unit vectors. (`Breakdown.CellCert.CellFormula.Internal.AngularMode.vec_expand`)

**Coordinate extracted by inner product.** Pairing a coordinate unit vector with a vector extracts that coordinate. (`Breakdown.CellCert.CellFormula.Internal.AngularMode.unit_inner`)

**Expand a vector inner product.** The vector inner product is the sum of coordinate-weighted component pairings. (`Breakdown.CellCert.CellFormula.Internal.AngularMode.inner_comp`)

**Pair a component gradient.** Pairing the component-gradient vector with a direction expands into the corresponding coordinate sum. (`Breakdown.CellCert.CellFormula.Internal.AngularMode.gc_inner`)

**Expand a matrix pairing by rows.** The matrix pairing is the stated sum of component-gradient pairings weighted by the output vector coordinates. (`Breakdown.CellCert.CellFormula.Internal.AngularMode.mat_inner`)

**Derivative of a frame coordinate.** The angular derivative of a frame coordinate is the matching frame-turn coordinate. (`Breakdown.CellCert.CellFormula.Internal.AngularMode.unit_hasDeriv`)

**Smooth cylindrical frame coordinate.** Each cylindrical-frame coordinate depends smoothly on angle. (`Breakdown.CellCert.CellFormula.Internal.AngularMode.unit_smooth`)

**Periodic cylindrical frame coordinate.** Each cylindrical-frame coordinate has period 2π. (`Breakdown.CellCert.CellFormula.Internal.AngularMode.unit_periodic`)

**Differentiate the Fourier phase.** The derivative of the negative-frequency exponential is the same exponential multiplied by minus the frequency times i. (`Breakdown.CellCert.CellFormula.Internal.AngularMode.exp_hasDeriv`)

**Differentiate the vector test weight.** The test-weight derivative is the frequency term plus the frame-turn correction. (`Breakdown.CellCert.CellFormula.Internal.AngularMode.wt_hasDeriv`)

**Formula for the test-weight derivative.** The ordinary derivative of the test weight equals its explicit frequency-and-frame formula. (`Breakdown.CellCert.CellFormula.Internal.AngularMode.wt_deriv`)

**Smooth vector test weight.** The angular vector test weight is smooth. (`Breakdown.CellCert.CellFormula.Internal.AngularMode.wt_smooth`)

**Periodic integer-mode test weight.** The test weight at integer frequency is 2π-periodic. (`Breakdown.CellCert.CellFormula.Internal.AngularMode.wt_periodic`)

**Integrable weighted circle component.** A continuous complex multiplier times an integrable real circle component is integrable. (`Breakdown.CellCert.CellFormula.Internal.AngularMode.ii_cmul`)

**Integrable finite circle sum.** A finite sum of circle-integrable coordinate functions is integrable. (`Breakdown.CellCert.CellFormula.Internal.AngularMode.ii_sum`)

**Integrate a finite circle sum.** The circle integral commutes with the finite sum of integrable coordinate terms. (`Breakdown.CellCert.CellFormula.Internal.AngularMode.int_sum`)

**Frame vector in Cartesian coordinates.** A cylindrical-frame vector component expands as the stated sum of Cartesian component pairings. (`Breakdown.CellCert.CellFormula.Internal.AngularMode.frameVec_eq`)

**Angular matrix column expansion.** The radius-weighted angular matrix column expands through the component gradients and angular unit vector. (`Breakdown.CellCert.CellFormula.Internal.AngularMode.frameMat_eq`)

**Velocity mode from Cartesian tests.** The velocity mode is the normalized circle integral of the weighted Cartesian field components. (`Breakdown.CellCert.CellFormula.Internal.AngularMode.mode_eq`)

**Gradient mode by integration by parts.** The stated weak angular identities express the radius-weighted gradient mode using derivatives of the angular test weights. (`Breakdown.CellCert.CellFormula.Internal.AngularMode.grad_eq`)

**Average a linear combination.** The normalized circle integral preserves the stated linear combination of two integrable functions. (`Breakdown.CellCert.CellFormula.Internal.AngularMode.comb`)

**Three angular mode identities.** The weak component identities yield the three radius-weighted angular gradient formulas, with the radial and angular frame corrections. (`Breakdown.CellCert.CellFormula.Internal.AngularMode.point`)

**Locally integrable gradient columns.** A measurable matrix field with integrable entry energy has locally integrable columns. (`Breakdown.CellCert.CellFormula.Internal.AngularMode.loc_col`)

**Locally integrable scalar pairings.** Pairing a locally integrable vector field with a fixed vector is locally integrable. (`Breakdown.CellCert.CellFormula.Internal.AngularMode.loc_inner`)

**Angular modes from weak circle tests.** The weak circle statement expresses radius times each angular gradient mode as its frequency multiple of the velocity mode plus the corresponding frame correction, almost everywhere at positive radius for second-order fields. (`Breakdown.CellCert.CellFormula.angularMode`)

### Breakdown.FracCell.AssemblyDefs

This file defines the field admissibility, local density and cell splitting conditions used to assemble the fractional cell certificate.

**Admissible cell field tuple.** A field tuple is admissible when its first three components form a second-order field and its final field is both a gradient and a class field. (`Breakdown.CellCert.Assembly.IsAdmissible`)

**Local fractional quadratic density.** The local density combines weighted second derivatives, curl and gradient energy, model stretching and actuator-gradient terms. (`Breakdown.CellCert.Assembly.CellSplit.localDensity`)

**Assembled state with free coordinates.** The state combines the moment vector shifted by the free-coordinate matrix with the free coordinates themselves. (`Breakdown.CellCert.Assembly.CellSplit.stateOf`)

**One cell's quadratic contribution.** A cell contribution combines its local density integral, assigned row squares and pin-field pairings. (`Breakdown.CellCert.Assembly.CellSplit.cellPart`)

**Quadratic contribution outside cells.** The exterior contribution is the local density integral outside the union of all cells. (`Breakdown.CellCert.Assembly.CellSplit.exteriorPart`)

**Conditions for a cell decomposition.** The cell-split proposition requires measurable disjoint cells, compatible linear moments, cell bounds, a nonnegative exterior and vanishing delay forms. (`Breakdown.CellCert.Assembly.CellSplit.IsCellSplit`)

**Analytic conditions for the cell form.** The form-data proposition records the certificate base, bounded cell region, centre decay and the model measurability, boundedness and support conditions. (`Breakdown.CellCert.Assembly.IsFormData`)

### Breakdown.FracCell.AxisClosed

This file proves the closed-axis polynomial estimates used to control finite radial cell expansions.

**Endpoint-vanishing polynomial.** The bump polynomial is X to power m times (1 − X) to power m. (`Breakdown.FracInternal.AxisClosedParts.bumpPoly`)

**Real shifted Legendre polynomial.** The orthogonal polynomial is the shifted Legendre polynomial with integer coefficients mapped to the reals. (`Breakdown.FracInternal.AxisClosedParts.orthPoly`)

**Rodrigues formula for the polynomial.** The mth derivative of the bump polynomial is m factorial times the chosen shifted Legendre polynomial. (`Breakdown.FracInternal.AxisClosedParts.factorial_mul_orthPoly`)

**Endpoint factors after differentiation.** Up to order m, the differentiated bump polynomial retains the stated power of X times 1 − X as a factor. (`Breakdown.FracInternal.AxisClosedParts.iter_factor`)

**Lower derivatives vanish at endpoints.** Every derivative of the bump polynomial below order m vanishes at both zero and one. (`Breakdown.FracInternal.AxisClosedParts.iter_eval_zero`)

**Polynomial integration by parts.** The polynomial derivative integral equals its endpoint terms minus the integral with the derivative moved to the other factor. (`Breakdown.FracInternal.AxisClosedParts.parts_gen`)

**Integration by parts without boundary.** When the differentiated polynomial vanishes at both endpoints, integration by parts has no boundary term. (`Breakdown.FracInternal.AxisClosedParts.parts_zero`)

**Repeated polynomial integration by parts.** Up to order m, moving derivatives off the bump polynomial contributes the sign (−1) to that order. (`Breakdown.FracInternal.AxisClosedParts.iter_parts`)

**Orthogonal to lower-degree polynomials.** The order-m shifted Legendre polynomial has zero integral pairing with every polynomial of degree below m. (`Breakdown.FracInternal.AxisClosedParts.orth`)

**Reflection of the shifted polynomial.** Reflecting the polynomial through X ↦ 1 − X multiplies it by the parity sign (−1) to power m. (`Breakdown.FracInternal.AxisClosedParts.comp_symm`)

**Value at the left endpoint.** The shifted Legendre polynomial equals one at zero. (`Breakdown.FracInternal.AxisClosedParts.l_zero`)

**Derivative at the left endpoint.** Its derivative at zero equals minus m times m + 1. (`Breakdown.FracInternal.AxisClosedParts.dl_zero`)

**Value at the right endpoint.** The shifted Legendre polynomial equals (−1) to power m at one. (`Breakdown.FracInternal.AxisClosedParts.l_one`)

**Derivative at the right endpoint.** Its derivative at one equals (−1) to power m times m times m + 1. (`Breakdown.FracInternal.AxisClosedParts.dl_one`)

**Reproduce a polynomial endpoint.** For degree at most q, pairing against the derivative of the next shifted polynomial with radial weight reproduces the stated endpoint value. (`Breakdown.FracInternal.AxisClosedParts.reproduce`)

**Weighted polynomial Cauchy-Schwarz.** The radial-weighted polynomial pairing squared is at most the product of the two weighted square integrals. (`Breakdown.FracInternal.AxisClosedParts.pair_le`)

**Polynomial endpoint energy bound.** A polynomial of degree at most q has its squared value at one bounded by (q + 1)(q + 2) times its radial energy. (`Breakdown.FracInternal.AxisClosedParts.endpoint`)

**Polynomial bound on the outer half.** On radii from 1/2 to one, the weighted polynomial square is bounded by 4(q + 1) squared times its radial energy. (`Breakdown.FracInternal.AxisClosedParts.sup_bound`)

**Continuous radial polynomial energy.** For angular index at most one and the stated divisibility condition, the radial derivative-and-angular energy density is continuous. (`Breakdown.FracInternal.AxisClosedParts.grad_cont`)

**Pointwise cutoff-energy bound.** The stated sign and cutoff assumptions give the displayed upper bound for the cutoff-modified radial energy. (`Breakdown.FracInternal.AxisClosedParts.pt_upper`)

**Closed-axis estimate.** An axis gradient bound and μ at least 24 give each polynomial of degree at most q a Lipschitz cutoff vanishing at one with the stated axis-functional bound, for index zero or one and divisibility by the radial variable when the index is one. (`Breakdown.CellCert.Spectral.axisClosed_holds`)

### Breakdown.FracCell.AxisFlux

This file recovers the axis-cell boundary flux identity from radial weak derivatives and angular-mode relations.

**The zero-radius line has measure zero.** The first coordinate is nonzero almost everywhere in the radius-height plane. (`Breakdown.CellCert.CellFormula.AxisFluxInternal.ae_fst_ne_zero`)

**Axis boundary moment identity.** The integrability, radius relation and zero-boundary weak identity give the stated radial boundary-moment formula. (`Breakdown.CellCert.CellFormula.AxisFluxInternal.hbase`)

**Axis flux from mode identities.** Axis-mode integrability, radial integration by parts and angular-mode identities give the stated boundary flux formula for the zero velocity mode of a second-order field, with positive outer radius, ordered heights and a continuous height test. (`Breakdown.CellCert.CellFormula.axisFlux_of`)

### Breakdown.FracCell.AxisGradModeIntegrable

This file supplies the integrability statement for gradient modes on cells touching the axis.

**Integrable gradient modes at the axis.** Every gradient-mode entry of a second-order field is integrable on the rectangle of a valid cell whose inner radius is zero. (`Breakdown.CellCert.CellFormula.axisGradModeIntegrable_holds`)

### Breakdown.FracCell.AxisLift

This file closes the construction of admissible zero-mode lifts on cells touching the symmetry axis.

**Axis-cell lift estimate.** On a zero-mode axis block with positive outer radius and ordered nonnegative heights, a Lipschitz cutoff vanishing at one and continuously differentiable height coefficients vanishing at the endpoints and in the constant transverse terms give the explicit lift a finite-energy modal weak gradient and the stated radial-height approximation bound. (`Breakdown.CellCert.Spectral.axisLift`)

### Breakdown.FracCell.AxisLiftDeriv

This file identifies the derivative of the explicit axis lift away from cell seams and the axis, sufficient for the weak-gradient construction.

**Cylindrical seams have measure zero.** Almost every spatial point avoids any prescribed finite sets of radii and heights. (`Breakdown.CellCert.Spectral.Internal.AxisLiftDeriv.null_cyl`)

**Expand in the cylindrical frame.** Every vector is the sum of its cylindrical-frame components times the frame vectors. (`Breakdown.CellCert.Spectral.Internal.AxisLiftDeriv.decomp`)

**Linear maps agree on a frame.** Two linear maps agreeing on every vector of a cylindrical frame are equal. (`Breakdown.CellCert.Spectral.Internal.AxisLiftDeriv.clm_eq`)

**Apply a frame matrix to a basis vector.** The frame-matrix construction sends a frame basis vector to the corresponding column combination. (`Breakdown.CellCert.Spectral.Internal.AxisLiftDeriv.form_apply`)

**Extract a frame coefficient.** Pairing a frame expansion with one frame vector extracts its coefficient. (`Breakdown.CellCert.Spectral.Internal.AxisLiftDeriv.frame_coef`)

**Cosine of cylindrical angle.** At positive radius, the cosine of the recovered cylindrical angle equals the original angle's cosine. (`Breakdown.CellCert.Spectral.Internal.AxisLiftDeriv.cos_angle`)

**Sine of cylindrical angle.** At positive radius, the sine of the recovered cylindrical angle equals the original angle's sine. (`Breakdown.CellCert.Spectral.Internal.AxisLiftDeriv.sin_angle`)

**Frame at a cylindrical point.** At positive radius, the spatial frame vector at a cylindrical point equals the angle-defined frame vector. (`Breakdown.CellCert.Spectral.Internal.AxisLiftDeriv.frame_any`)

**Recover a point from its coordinates.** Converting a point to cylindrical coordinates and back recovers the point. (`Breakdown.CellCert.Spectral.Internal.AxisLiftDeriv.cyl_self`)

**Lift evaluated in cylindrical form.** At positive radius, the indicated axis lift equals its frame expansion with cell indicators and radial lift values. (`Breakdown.CellCert.Spectral.Internal.AxisLiftDeriv.psi_cyl`)

**Cylindrical point in coordinate axes.** A cylindrical point expands into cosine and sine radial components and its height component. (`Breakdown.CellCert.Spectral.Internal.AxisLiftDeriv.cyl_lin`)

**Axis cell solid is closed.** A cell solid with inner radius zero is a closed set. (`Breakdown.CellCert.Spectral.Internal.AxisLiftDeriv.solid_closed`)

**Select the active height half.** Strictly inside one height half of an axis cell, the sum of the two indicators selects that half's value. (`Breakdown.CellCert.Spectral.Internal.AxisLiftDeriv.sel`)

**Height derivative in the moving frame.** The local cylindrical representation and height derivatives determine the field derivative in the height direction. (`Breakdown.CellCert.Spectral.Internal.AxisLiftDeriv.dir_z`)

**Radial derivative of a component.** Inside the radial and height intervals, a cylindrical coefficient's radial derivative is the corresponding frame component of the field derivative. (`Breakdown.CellCert.Spectral.Internal.AxisLiftDeriv.dir_r`)

**Angular derivative of an axis lift.** The zero-mode cylindrical representation determines the angular derivative from the radial and angular components divided by radius. (`Breakdown.CellCert.Spectral.Internal.AxisLiftDeriv.dir_t`)

**Differentiate the height coefficients.** Differentiating a finite radial polynomial with C1 height coefficients gives the stated sum of their height derivatives. (`Breakdown.CellCert.Spectral.Internal.AxisLiftDeriv.hz_aux`)

**Pointwise derivative of the axis lift.** Away from the axis and cell seams, a differentiable zero-mode axis lift has derivative equal to the explicit lift-gradient formula. (`Breakdown.CellCert.Spectral.point_deriv`)

**Axis-lift derivative identity.** Under the zero-mode axis-block geometry, Lipschitz cutoff and endpoint and transverse coefficient conditions, the classical derivative of the explicit lift equals its prescribed gradient almost everywhere wherever the lift is differentiable. (`Breakdown.CellCert.Spectral.liftDeriv_holds`)

### Breakdown.FracCell.AxisLiftEnergy

This file writes the axis lift's error and gradient energy as scalar radial-height integrals and assembles the lift estimate.

**Frame matrix energy is sum of squares.** The matrix entry energy of a cylindrical-frame matrix is the sum of the squares of its frame coefficients. (`Breakdown.CellCert.Spectral.Internal.AxisLift.entry_frame`)

**Sine lift coefficient vanishes.** The lift coefficient in the second trigonometric channel is zero. (`Breakdown.CellCert.Spectral.Internal.AxisLift.coef_one`)

**Lift gradient in cylindrical coordinates.** For zero angular mode and positive radius, the lift gradient has the stated cylindrical-frame matrix expansion. (`Breakdown.CellCert.Spectral.Internal.AxisLift.grad_cyl`)

**Square a disjoint indicator sum.** Away from the midplane, the squared sum over the two axis-cell indicators equals the sum of their indicated squares. (`Breakdown.CellCert.Spectral.Internal.AxisLift.sq_ind`)

**Scalar lift-energy density.** The scalar integrand combines squared lifting error with inverse-λ weighted radial, height and angular derivative energy, multiplied by radius. (`Breakdown.CellCert.Spectral.Internal.AxisLift.integrand`)

**Expand the lift-gradient energy.** The sum of the lift-gradient coefficient squares is the stated sum of radial, height and angular energy terms. (`Breakdown.CellCert.Spectral.Internal.AxisLift.coef_sq`)

**Split the lift energy by height half.** At positive radius away from the midplane, the full indicated error and gradient energy split into the scalar integrands for the two height halves. (`Breakdown.CellCert.Spectral.Internal.AxisLift.point`)

**Integrable cylindrical average.** A spatially integrable scalar field has an integrable radius-weighted angular average on the positive radial half-plane. (`Breakdown.CellCert.Spectral.Internal.AxisLift.cyl_int`)

**Axis-cell indicator as a rectangle.** On positive radii, the axis-cell indicator equals the indicator of the corresponding radial-height rectangle. (`Breakdown.CellCert.Spectral.Internal.AxisLift.box_eq`)

**Integrate one axis-cell half.** The integrable indicated cell expression equals its iterated radial and height interval integral. (`Breakdown.CellCert.Spectral.Internal.AxisLift.gpiece`)

**Measurable lift-energy density.** Continuous cutoff and field data with C1 height coefficients make the scalar lift-energy density measurable. (`Breakdown.CellCert.Spectral.Internal.AxisLift.integrand_meas`)

**Nonnegative lift-energy density.** For positive λ and nonnegative radius, the scalar lift-energy density is nonnegative. (`Breakdown.CellCert.Spectral.Internal.AxisLift.integrand_nonneg`)

**Nonnegative cell indicator.** Every axis-cell indicator is nonnegative. (`Breakdown.CellCert.Spectral.Internal.AxisLift.ind_nonneg`)

**Axis lift from its weak gradient.** The finite-energy weak-gradient statement gives the explicit axis lift its modal gradient and radial-height approximation estimate under the stated block geometry, cutoff and coefficient conditions. (`Breakdown.CellCert.Spectral.axisLift_of_grad`)

**Axis lift from slope and derivative.** The lift slope and derivative statements give the explicit axis lift a finite-energy modal weak gradient and the radial-height approximation estimate under the stated block geometry, cutoff and coefficient conditions. (`Breakdown.CellCert.Spectral.axisLift_of_parts`)

### Breakdown.FracCell.AxisLiftParts

This file defines the radial, height and frame coefficients of the axis lift and states its L2 weak-gradient requirements.

**Radial polynomial lift value.** The lift value is the radial cutoff times the finite radial polynomial with height-dependent coefficients. (`Breakdown.CellCert.Spectral.liftVal`)

**Radial derivative of the lift.** The radial lift term is the derivative of the cutoff-weighted radial polynomial. (`Breakdown.CellCert.Spectral.liftRad`)

**Height derivative of the lift.** The height lift term replaces each height coefficient by its derivative, retaining the radial cutoff and powers. (`Breakdown.CellCert.Spectral.liftHgt`)

**Frame coefficients of the lift gradient.** The lift-gradient coefficients select radial, height or angular frame terms in the cosine channel and zero in the sine channel. (`Breakdown.CellCert.Spectral.liftCoef`)

**Explicit axis-lift gradient.** The lift gradient sums the indicated cell frame matrices formed from the trigonometric lift coefficients. (`Breakdown.CellCert.Spectral.liftGrad`)

**Weak-gradient conditions for the lift.** This proposition requires the stated axis lift to be L2 with a measurable square-integrable explicit weak gradient under the cutoff and boundary conditions. (`Breakdown.CellCert.Spectral.LiftGradStatement`)

Proved from further statements by `Breakdown.CellCert.Spectral.liftGrad_of_parts`.

**Continuous lift value.** A continuous cutoff and continuous height coefficients give a continuous scalar lift value. (`Breakdown.CellCert.Spectral.Internal.AxisLiftParts.val_cont`)

**Measurable radial lift derivative.** A continuous cutoff and continuous height coefficients give a measurable radial derivative of the lift. (`Breakdown.CellCert.Spectral.Internal.AxisLiftParts.rad_meas`)

**Continuous height lift derivative.** A continuous cutoff and C1 height coefficients give a continuous height derivative of the lift. (`Breakdown.CellCert.Spectral.Internal.AxisLiftParts.hgt_cont`)

**Measurable lift-gradient coefficients.** Under the stated cutoff and height regularity, each frame coefficient of the lift gradient is measurable. (`Breakdown.CellCert.Spectral.Internal.AxisLiftParts.coef_meas`)

**Lift gradient has the required mode.** The explicit lift-gradient field satisfies the mode-gradient condition under the stated regularity assumptions. (`Breakdown.CellCert.Spectral.liftGrad_mode`)

### Breakdown.FracCell.AxisLiftSlope

This file shows the explicit axis lift is Lipschitz and compactly supported, including its behaviour at zero radius.

**Lipschitz scalar-vector product.** A bounded Lipschitz scalar times a Lipschitz vector function bounded on its nonzero set is Lipschitz. (`Breakdown.CellCert.Spectral.Internal.AxisLiftSlope.slope_smul`)

**Bounded Lipschitz product.** The product of two bounded Lipschitz scalar functions remains bounded and Lipschitz. (`Breakdown.CellCert.Spectral.Internal.AxisLiftSlope.bl_mul`)

**Finite sums of Lipschitz fields.** A finite sum of Lipschitz fields is Lipschitz. (`Breakdown.CellCert.Spectral.Internal.AxisLiftSlope.slope_sum`)

**Radius below the spatial norm.** The cylindrical radius is at most the spatial norm. (`Breakdown.CellCert.Spectral.Internal.AxisLiftSlope.rad_le`)

**Radius as a complex norm.** The cylindrical radius is the complex norm of the first two coordinates. (`Breakdown.CellCert.Spectral.Internal.AxisLiftSlope.rad_cx`)

**Radius is one-Lipschitz.** The cylindrical radius has Lipschitz constant one. (`Breakdown.CellCert.Spectral.Internal.AxisLiftSlope.rad_slope`)

**Coordinates are one-Lipschitz.** Every spatial coordinate has Lipschitz constant one. (`Breakdown.CellCert.Spectral.Internal.AxisLiftSlope.coord_slope`)

**Planar coordinate below radius.** Each of the first two coordinate absolute values is at most the cylindrical radius. (`Breakdown.CellCert.Spectral.Internal.AxisLiftSlope.coord_le`)

**Powers preserve bounded Lipschitz data.** Every natural power of a bounded Lipschitz scalar function is bounded and Lipschitz. (`Breakdown.CellCert.Spectral.Internal.AxisLiftSlope.pow_bl`)

**Clamp a C1 scalar to an interval.** Clamping the argument of a C1 scalar function to a closed ordered interval produces a bounded Lipschitz function. (`Breakdown.CellCert.Spectral.Internal.AxisLiftSlope.clamp_slope`)

**Unnormalized cylindrical frame vectors.** The auxiliary vectors are the planar radial vector, its quarter-turn and the fixed height unit vector. (`Breakdown.CellCert.Spectral.Internal.AxisLiftSlope.wvec`)

**Lipschitz unnormalized frame vectors.** Each auxiliary frame vector is Lipschitz as a function of position. (`Breakdown.CellCert.Spectral.Internal.AxisLiftSlope.wvec_slope`)

**First coordinate below radius.** The first coordinate's absolute value is at most the cylindrical radius. (`Breakdown.CellCert.Spectral.Internal.AxisLiftSlope.c0_le`)

**Second coordinate below radius.** The second coordinate's absolute value is at most the cylindrical radius. (`Breakdown.CellCert.Spectral.Internal.AxisLiftSlope.c1_le`)

**Norm of a coordinate unit vector.** Every standard spatial unit vector has norm one. (`Breakdown.CellCert.Spectral.Internal.AxisLiftSlope.unit_norm`)

**Growth of the unnormalized frame.** Each auxiliary frame vector has norm at most twice the cylindrical radius plus one. (`Breakdown.CellCert.Spectral.Internal.AxisLiftSlope.wvec_bd`)

**Remove the frame's radial denominator.** For radial or angular components, radius times the unit frame vector equals the auxiliary unnormalized vector. (`Breakdown.CellCert.Spectral.Internal.AxisLiftSlope.frame_w`)

**Membership in an axis cell.** For inner radius zero, membership in a cell solid is exactly the outer-radius and height-interval condition. (`Breakdown.CellCert.Spectral.Internal.AxisLiftSlope.mem_iff`)

**Lipschitz and compact axis lift.** Under the zero-mode axis-block geometry, a Lipschitz cutoff vanishing at one and continuously differentiable coefficients with the stated endpoint and transverse zeros make the explicit lift Lipschitz and compactly supported. (`Breakdown.CellCert.Spectral.liftSlope_holds`)

### Breakdown.FracCell.AxisLiftWeak

This file turns the Lipschitz axis lift and its almost-everywhere derivative formula into the required square-integrable weak gradient.

**Matrix energy from operator norm.** The sum of squared matrix entries is at most three times the operator norm squared. (`Breakdown.CellCert.Spectral.Internal.AxisLiftWeak.entry_le`)

**Continuous matrix entry energy.** The matrix entry-square sum is a continuous function of the linear map. (`Breakdown.CellCert.Spectral.Internal.AxisLiftWeak.entry_cont`)

**Directional derivative of a coordinate.** At a differentiability point, the directional derivative of a field coordinate equals that coordinate of the field derivative. (`Breakdown.CellCert.Spectral.Internal.AxisLiftWeak.comp_line`)

**Weak gradient of a Lipschitz lift.** A compactly supported Lipschitz field with the stated almost-everywhere derivative identification has the indicated L2 weak gradient and finite matrix energy. (`Breakdown.CellCert.Spectral.weak_of_slopeBound`)

**Lipschitz axis-lift requirement.** This proposition requires the explicit axis lift to be Lipschitz and compactly supported under the stated cutoff, coefficient and boundary conditions. (`Breakdown.CellCert.Spectral.LiftSlopeStatement`)

Proved by `Breakdown.CellCert.Spectral.liftSlope_holds`.

**Axis-lift derivative requirement.** This proposition requires the explicit lift-gradient formula to agree almost everywhere with the derivative wherever that derivative exists. (`Breakdown.CellCert.Spectral.LiftDerivStatement`)

Proved by `Breakdown.CellCert.Spectral.liftDeriv_holds`.

**Combine the lift regularity statements.** The lift slope and derivative statements make the explicit axis lift square integrable with the prescribed measurable finite-energy weak gradient under the stated block geometry, cutoff and coefficient conditions. (`Breakdown.CellCert.Spectral.liftGrad_of_parts`)

### Breakdown.FracCell.AxisModeIntegrable

This file closes axis-mode integrability, with height-translation identities for cylindrical gradient modes.

**Translate a cylindrical point in height.** Adding a height coordinate vector translates the height of a cylindrical point by the same amount. (`_private.Breakdown.FracCell.AxisModeIntegrable.0.Breakdown.CellCert.CellFormula.AxisModeIntegrableInternal.cylPoint_shift`)

**Height translation of a gradient mode.** Translating the matrix field in height translates its cylindrical gradient-mode height argument. (`_private.Breakdown.FracCell.AxisModeIntegrable.0.Breakdown.CellCert.CellFormula.AxisModeIntegrableInternal.gradMode_shift`)

**Integrable modes at the axis.** For every second-order field, each gradient-mode entry multiplied by radius is integrable on every closed radial-height rectangle extending from radius zero. (`Breakdown.CellCert.CellFormula.axisModeIntegrable`)

### Breakdown.FracCell.AxisWeak

This file derives weak radial and height identities using smooth compact tests supported away from the axis.

**Weak testing by linear-map fields.** The coordinate weak derivative identity extends to smooth compactly supported complex linear-map-valued tests. (`_private.Breakdown.FracCell.AxisWeak.0.Breakdown.CellCert.CellFormula.weakCLM`)

**Smooth spatial coordinates.** Each spatial coordinate function is smooth. (`_private.Breakdown.FracCell.AxisWeak.0.Breakdown.CellCert.CellFormula.coord_smooth`)

**Continuous cylindrical radius.** The cylindrical radius is continuous. (`_private.Breakdown.FracCell.AxisWeak.0.Breakdown.CellCert.CellFormula.rad_cont`)

**Smooth radius away from the axis.** The cylindrical radius is smooth at every point of positive radius. (`_private.Breakdown.FracCell.AxisWeak.0.Breakdown.CellCert.CellFormula.rad_smoothAt`)

**Planar coordinates bounded by radius.** Each planar coordinate's absolute value is bounded by the cylindrical radius. (`_private.Breakdown.FracCell.AxisWeak.0.Breakdown.CellCert.CellFormula.abs_coord_le`)

**Norm bounded by coordinate magnitudes.** The spatial norm is at most the sum of the three coordinate absolute values. (`_private.Breakdown.FracCell.AxisWeak.0.Breakdown.CellCert.CellFormula.norm_le_coords`)

**Glue smoothness across a zero region.** A field smooth beyond the stated radius and zero below it is globally smooth. (`_private.Breakdown.FracCell.AxisWeak.0.Breakdown.CellCert.CellFormula.smooth_of`)

**Local vanishing below the cutoff radius.** At a point below the stated radius, a field vanishing throughout that region is locally equal to zero. (`_private.Breakdown.FracCell.AxisWeak.0.Breakdown.CellCert.CellFormula.zero_near`)

**Compact support stays off the axis.** A compact support contained in positive radii has a positive radius lower bound and a finite norm bound. (`_private.Breakdown.FracCell.AxisWeak.0.Breakdown.CellCert.CellFormula.supp_bounds`)

**Bounds on the lifted support.** The stated radial-height support bounds imply a positive radial lower bound and a spatial norm bound for every nonzero lifted value. (`_private.Breakdown.FracCell.AxisWeak.0.Breakdown.CellCert.CellFormula.off_supp`)

**Integrable compact linear-map test.** A continuous compactly supported linear-map field applied to a locally integrable field is integrable. (`_private.Breakdown.FracCell.AxisWeak.0.Breakdown.CellCert.CellFormula.integrable_apply`)

**Normalized planar direction.** The normalized planar direction is the first two coordinates divided by cylindrical radius. (`_private.Breakdown.FracCell.AxisWeak.0.Breakdown.CellCert.CellFormula.uvec`)

**Smooth normalized direction off axis.** The normalized planar direction is smooth at positive radius. (`_private.Breakdown.FracCell.AxisWeak.0.Breakdown.CellCert.CellFormula.uvec_smoothAt`)

**Lift a radial-height test.** The lifted test evaluates the angular linear-map weight at the normalized direction and multiplies it by the radial-height amplitude divided by a radius power. (`_private.Breakdown.FracCell.AxisWeak.0.Breakdown.CellCert.CellFormula.fieldOf`)

**Smooth radial-height coordinates.** The radius-height coordinate map is smooth away from the axis. (`_private.Breakdown.FracCell.AxisWeak.0.Breakdown.CellCert.CellFormula.pair_smoothAt`)

**Smooth compact lifted test.** The support and smoothness hypotheses make the lifted test smooth, compactly supported and zero below the positive support radius. (`_private.Breakdown.FracCell.AxisWeak.0.Breakdown.CellCert.CellFormula.fieldOf_smooth`)

**Coordinate of a translated line.** Each coordinate of a translated and scaled vector is the corresponding affine scalar expression. (`_private.Breakdown.FracCell.AxisWeak.0.Breakdown.CellCert.CellFormula.coord_add_smul`)

**Height derivative of a lifted test.** Differentiating the lifted test in height differentiates its radial-height amplitude in the height direction. (`_private.Breakdown.FracCell.AxisWeak.0.Breakdown.CellCert.CellFormula.deriv_z`)

**Evaluate the lifted linear map.** Applying the lifted test equals its scalar amplitude divided by radius power times the angular linear map's value. (`_private.Breakdown.FracCell.AxisWeak.0.Breakdown.CellCert.CellFormula.fieldOf_apply`)

**Coordinate-weighted product rule.** Differentiating a coordinate times a differentiable linear-map field gives the stated product rule. (`_private.Breakdown.FracCell.AxisWeak.0.Breakdown.CellCert.CellFormula.prod_deriv`)

**Radial derivative from two coordinates.** The sum of the two planar coordinate derivatives of the weighted lifted tests equals the lifted radial derivative. (`_private.Breakdown.FracCell.AxisWeak.0.Breakdown.CellCert.CellFormula.deriv_r`)

**Single-coordinate vector formula.** A vector supported in one coordinate equals that coordinate's unit vector multiplied by its value. (`_private.Breakdown.FracCell.AxisWeak.0.Breakdown.CellCert.CellFormula.single_eq`)

**Combine the planar weak-gradient terms.** The two coordinate-weighted test pairings combine into the normalized radial-direction pairing with the stated radius factor. (`_private.Breakdown.FracCell.AxisWeak.0.Breakdown.CellCert.CellFormula.key3_of`)

**Regularity of coordinate-weighted tests.** The coordinate-weighted lifted tests remain smooth and compactly supported under the stated support assumptions. (`_private.Breakdown.FracCell.AxisWeak.0.Breakdown.CellCert.CellFormula.prod_facts`)

**Regularity of test derivatives.** A fixed directional derivative of a smooth compactly supported test is continuous and compactly supported. (`_private.Breakdown.FracCell.AxisWeak.0.Breakdown.CellCert.CellFormula.deriv_facts`)

**Weak radial and height identities.** A locally integrable finite-dimensional field and its locally integrable weak gradient satisfy the stated radial and height integration-by-parts identities for smooth angular weights and smooth compactly supported radial-height tests supported away from the axis. (`Breakdown.CellCert.CellFormula.axisWeak`)

### Breakdown.FracCell.BasisEnergySum

This file realizes the cell polynomial bases as a complete orthonormal family in the weighted L2 space, giving the basis energy sum.

**Measurable cell rectangle.** The cell rectangle is measurable. (`Breakdown.CellCert.CellAnalysis.BasisSeriesInternal.rect_meas`)

**Compact cell rectangle.** The cell rectangle, viewed as a subtype, is a compact space. (`Breakdown.CellCert.CellAnalysis.BasisSeriesInternal.rect_compactSpace`)

**Continuous radial line weight.** The cell's radial line weight is continuous. (`Breakdown.CellCert.CellAnalysis.BasisSeriesInternal.lw_cont`)

**Nonnegative radial line weight.** The line weight is nonnegative on the cell rectangle. (`Breakdown.CellCert.CellAnalysis.BasisSeriesInternal.lw_nonneg`)

**Bounded radial line weight.** On the cell rectangle, the line weight is at most the maximum of the outer radius and one. (`Breakdown.CellCert.CellAnalysis.BasisSeriesInternal.lw_le`)

**Area measure on the cell subtype.** The cell subtype measure is the pullback of planar volume under inclusion. (`Breakdown.CellCert.CellAnalysis.BasisSeriesInternal.rho`)

**Nonnegative cell weight.** The subtype weight is the nonnegative-real version of the radial line weight. (`Breakdown.CellCert.CellAnalysis.BasisSeriesInternal.wt`)

**Weighted measure on the cell.** The weighted cell measure is the subtype area measure multiplied by the nonnegative radial density. (`Breakdown.CellCert.CellAnalysis.BasisSeriesInternal.nu`)

**Cell inclusion is measurably embedded.** Including the cell subtype in the radius-height plane is a measurable embedding. (`Breakdown.CellCert.CellAnalysis.BasisSeriesInternal.emb`)

**Push cell measure to the rectangle.** Pushing the subtype measure forward gives planar volume restricted to the cell rectangle. (`Breakdown.CellCert.CellAnalysis.BasisSeriesInternal.map_rho`)

**Measurable cell weight.** The nonnegative subtype weight is measurable. (`Breakdown.CellCert.CellAnalysis.BasisSeriesInternal.wt_meas`)

**Recover the real line weight.** Converting the subtype weight back to the reals recovers the cell line weight. (`Breakdown.CellCert.CellAnalysis.BasisSeriesInternal.wt_coe`)

**Finite area of the cell subtype.** The area measure on the cell subtype is finite. (`Breakdown.CellCert.CellAnalysis.BasisSeriesInternal.rho_finite`)

**Finite weighted cell measure.** The weighted cell measure is finite. (`Breakdown.CellCert.CellAnalysis.BasisSeriesInternal.nu_finite`)

**Convert a weighted cell integral.** Integration against the weighted subtype measure equals the rectangle integral with the radial line weight. (`Breakdown.CellCert.CellAnalysis.BasisSeriesInternal.integral_nu`)

**Weighted integrability equivalence.** Subtype integrability under the weighted measure is equivalent to integrability of the line-weighted function on the rectangle. (`Breakdown.CellCert.CellAnalysis.BasisSeriesInternal.integrable_nu_iff`)

**Weighted-square data define an L2 field.** The cell weighted-square condition places the restricted field in L2 for the weighted cell measure. (`Breakdown.CellCert.CellAnalysis.BasisSeriesInternal.memLp_of`)

**Complex scalar inner product.** The complex inner product is conjugation of the first input multiplied by the second. (`Breakdown.CellCert.CellAnalysis.BasisSeriesInternal.inner_C`)

**L2 inner product through representatives.** Almost-everywhere representatives identify the L2 inner product with the integral of their conjugate product. (`Breakdown.CellCert.CellAnalysis.BasisSeriesInternal.inner_ae`)

**Tensor-product basis function.** The scalar basis function is the complex embedding of the radial basis polynomial times the height basis polynomial. (`Breakdown.CellCert.CellAnalysis.BasisSeriesInternal.bv`)

**Continuous radial basis polynomial.** Every radial basis polynomial is continuous. (`Breakdown.CellCert.CellAnalysis.BasisSeriesInternal.radial_cont`)

**Continuous height basis polynomial.** Every height basis polynomial is continuous. (`Breakdown.CellCert.CellAnalysis.BasisSeriesInternal.height_cont`)

**Basis function as a continuous map.** The tensor-product basis function is bundled as a continuous complex function on the cell rectangle. (`Breakdown.CellCert.CellAnalysis.BasisSeriesInternal.eC`)

**Basis function as an L2 vector.** The continuous basis function is placed in L2 for the weighted cell measure. (`Breakdown.CellCert.CellAnalysis.BasisSeriesInternal.eL`)

**Pointwise representative of the basis.** The L2 basis vector agrees almost everywhere with its polynomial formula. (`Breakdown.CellCert.CellAnalysis.BasisSeriesInternal.eL_ae`)

**Weighted basis orthogonality.** The cell-basis conditions make the weighted integral of two basis functions equal to one for equal indices and zero otherwise. (`Breakdown.CellCert.CellAnalysis.BasisSeriesInternal.orth`)

**Orthonormal L2 basis family.** The cell-basis conditions make the L2 polynomial family orthonormal. (`Breakdown.CellCert.CellAnalysis.BasisSeriesInternal.orth_eL`)

**Cell monomial as a continuous map.** The cell monomial is the product of the radial and height coordinate powers, bundled as a continuous complex map. (`Breakdown.CellCert.CellAnalysis.BasisSeriesInternal.mono`)

**Span of the cell monomials.** The monomial space is the complex linear span of all cell monomials. (`Breakdown.CellCert.CellAnalysis.BasisSeriesInternal.M`)

**Multiply cell monomials.** Multiplication of two cell monomials adds their radial and height exponents. (`Breakdown.CellCert.CellAnalysis.BasisSeriesInternal.mono_mul`)

**Monomial span closed under products.** The product of two functions in the monomial span remains in that span. (`Breakdown.CellCert.CellAnalysis.BasisSeriesInternal.mul_mem_M`)

**Constant one in the monomial span.** The constant function one belongs to the monomial span. (`Breakdown.CellCert.CellAnalysis.BasisSeriesInternal.one_mem_M`)

**Real monomials are self-conjugate.** Complex conjugation leaves every cell monomial unchanged. (`Breakdown.CellCert.CellAnalysis.BasisSeriesInternal.star_mono`)

**Monomial span closed under conjugation.** The monomial span is closed under complex conjugation. (`Breakdown.CellCert.CellAnalysis.BasisSeriesInternal.star_mem_M`)

**Cell polynomial star algebra.** The monomial span is bundled as a complex star subalgebra of the continuous cell functions. (`Breakdown.CellCert.CellAnalysis.BasisSeriesInternal.A`)

**Cell polynomials separate points.** The cell polynomial algebra separates points of the rectangle. (`Breakdown.CellCert.CellAnalysis.BasisSeriesInternal.A_sep`)

**Powers lie in the triangular span.** Polynomials with positive leading coefficients span every scalar monomial. (`Breakdown.CellCert.CellAnalysis.BasisSeriesInternal.pow_mem_span`)

**Finite expansion of a scalar power.** Every scalar power has a finite linear expansion in the stated triangular polynomial family. (`Breakdown.CellCert.CellAnalysis.BasisSeriesInternal.pow_expand`)

**Expand monomials in the cell basis.** The cell-basis conditions put every cell monomial in the span of the continuous tensor-product basis functions. (`Breakdown.CellCert.CellAnalysis.BasisSeriesInternal.mono_mem_V`)

**Monomial span lies in the basis span.** The entire cell monomial space is contained in the tensor-product basis span. (`Breakdown.CellCert.CellAnalysis.BasisSeriesInternal.M_le_V`)

**Dense polynomial basis span.** The tensor-product L2 basis has dense linear span in the weighted cell L2 space. (`Breakdown.CellCert.CellAnalysis.BasisSeriesInternal.span_dense`)

**Coefficient as a basis inner product.** The inner product of a basis vector with an L2 field is its cell-basis coefficient. (`Breakdown.CellCert.CellAnalysis.BasisSeriesInternal.inner_e_F`)

**Reversed coefficient pairing.** The reversed L2 pairing with a basis vector is the complex conjugate of the cell coefficient. (`Breakdown.CellCert.CellAnalysis.BasisSeriesInternal.inner_W_e`)

**Cell basis energy identity.** For a valid cell and bases, the sum of coefficient pairings of finite families of weighted square-integrable functions equals their weighted integral pairing on the cell rectangle. (`Breakdown.CellCert.CellAnalysis.basisEnergySum_holds`)

### Breakdown.FracCell.BlockLocal

This file reduces local cell-block bounds to the field-witness construction and cylindrical integral estimates.

**Orthonormal cylindrical frame.** The inner product of two frame vectors is one for equal indices and zero otherwise. (`Breakdown.CellCert.Spectral.Internal.BlockLocal.frame_inner`)

**Subtract two shaped fields.** The difference of two shaped fields is the shaped field formed by subtracting their coefficient functions. (`Breakdown.CellCert.Spectral.Internal.BlockLocal.shape_sub`)

**Mode fields have block shape.** Every mode field satisfies the block-shape condition. (`Breakdown.CellCert.Spectral.Internal.BlockLocal.mode_shaped`)

**Mode-gradient columns have block shape.** Applying a mode-gradient field to a frame vector gives a block-shaped field. (`Breakdown.CellCert.Spectral.Internal.BlockLocal.gradient_shaped`)

**Identify the block inner coefficient.** The block inner coefficient equals its explicit block-inner value. (`Breakdown.CellCert.Spectral.Internal.BlockLocal.inner_eq`)

**Local block statement from a witness.** The field-witness statement gives a block-shaped square integrable approximation with a finite-energy weak gradient and the stated relative error bound when the spectral data are valid, λ is positive, the block is assigned to a row and its inner value is below one. (`Breakdown.CellCert.Spectral.blockLocal_of_field`)

**Block bound from interval and cell data.** The interval estimates, closed-axis estimate, field witness and cylindrical formula combine into the block bound. (`Breakdown.CellCert.Spectral.blockBound_of_field_cyl`)

### Breakdown.FracCell.CanonicalInputs

This file verifies that canonical cell coordinates and gauge-shifted field data supply the inputs required by the local energy estimates.

**Lower moments of an orthogonal basis.** The orthogonality and nonzero leading coefficients force all lower monomial moments of a basis polynomial to vanish. (`Breakdown.CellCert.CellFormula.CanonicalInputs.Internal.moment_zero`)

**Continuous cell line weight.** The cell's radial line weight is continuous. (`Breakdown.CellCert.CellFormula.CanonicalInputs.Internal.lineWeight_continuous`)

**Continuous radial basis.** Every radial cell-basis polynomial is continuous. (`Breakdown.CellCert.CellFormula.CanonicalInputs.Internal.radialPoly_continuous`)

**Continuous height basis.** Every height cell-basis polynomial is continuous. (`Breakdown.CellCert.CellFormula.CanonicalInputs.Internal.heightPoly_continuous`)

**High coefficients of a polynomial vanish.** A polynomial of degree at most d in each variable has zero basis coefficient whenever either index exceeds d. (`Breakdown.CellCert.CellFormula.CanonicalInputs.Internal.coef_poly_zero`)

**Projection has the prescribed degrees.** The cell polynomial projection belongs to the stated radial-height polynomial space. (`Breakdown.CellCert.CellFormula.CanonicalInputs.Internal.proj_mem`)

**Pressure shift vanishes on low entries.** The pressure gauge shift is zero at every datum selected by a low-mode entry. (`Breakdown.CellCert.CellFormula.CanonicalInputs.Internal.pressureShift_low`)

**Low entries recover true coefficients.** The low-entry statement identifies selected shifted data with the corresponding low coefficients of an admissible field. (`Breakdown.CellCert.CellFormula.CanonicalInputs.Internal.lowEntry_agree_of`)

**Parameters depend on free entries.** Two data vectors agreeing outside the solved set have the same parameterized vector. (`Breakdown.CellCert.CellFormula.CanonicalInputs.Internal.param_congr`)

**Free coordinates preserve addition.** Taking the free part of the data preserves addition. (`Breakdown.CellCert.CellFormula.CanonicalInputs.Internal.freePart_add`)

**Free coordinates preserve real scaling.** Taking the free part of the data preserves real scalar multiplication. (`Breakdown.CellCert.CellFormula.CanonicalInputs.Internal.freePart_smul`)

**Parameterization preserves addition.** The parameterization map preserves addition. (`Breakdown.CellCert.CellFormula.CanonicalInputs.Internal.param_add`)

**Parameterization preserves real scaling.** The parameterization map preserves real scalar multiplication. (`Breakdown.CellCert.CellFormula.CanonicalInputs.Internal.param_smul`)

**Complex coordinates preserve addition.** The layout's real-to-complex coordinate map preserves addition. (`Breakdown.CellCert.CellFormula.CanonicalInputs.Internal.realCoord_add`)

**Complex coordinates preserve scaling.** The layout's real-to-complex coordinate map preserves real scalar multiplication. (`Breakdown.CellCert.CellFormula.CanonicalInputs.Internal.realCoord_smul`)

**Coordinate embedding preserves sums.** Embedding skeleton and interior coordinates preserves addition. (`Breakdown.CellCert.CellFormula.CanonicalInputs.Internal.embed_add`)

**Coordinate embedding preserves scaling.** Embedding skeleton and interior coordinates preserves real scalar multiplication. (`Breakdown.CellCert.CellFormula.CanonicalInputs.Internal.embed_smul`)

**Linear canonical coordinate map.** Embedding coordinates, forming complex data and parameterizing them gives a real linear map. (`Breakdown.CellCert.CellFormula.CanonicalInputs.Internal.coord_linear_of`)

**Reconstruct parameterized data.** Data fixed by the parameterization are recovered from their selected real skeleton and interior coordinates. (`Breakdown.CellCert.CellFormula.CanonicalInputs.Internal.data_represents_of`)

**Corner rows ignore pressure data.** The corner row evaluates to zero on every pressure datum. (`Breakdown.CellCert.CellFormula.CanonicalInputs.Internal.cornerAt_pres`)

**Velocity side rows ignore pressure.** The side-velocity row evaluates to zero on every pressure datum. (`Breakdown.CellCert.CellFormula.CanonicalInputs.Internal.sideVelocityRow_pres`)

**Gradient side rows ignore pressure.** The side-gradient row evaluates to zero on every pressure datum. (`Breakdown.CellCert.CellFormula.CanonicalInputs.Internal.sideGradientRow_pres`)

**Turned side rows ignore pressure.** The turned side row evaluates to zero on every pressure datum. (`Breakdown.CellCert.CellFormula.CanonicalInputs.Internal.turnSideRow_pres`)

**Base face rows ignore pressure.** The base face row evaluates to zero on every pressure datum. (`Breakdown.CellCert.CellFormula.CanonicalInputs.Internal.faceBaseRow_pres`)

**Strain face rows ignore pressure.** The strain face row evaluates to zero on every pressure datum. (`Breakdown.CellCert.CellFormula.CanonicalInputs.Internal.strainFaceRow_pres`)

**Gauge shifts preserve pressure-free rows.** A row that vanishes on pressure data has the same value on shifted and true field data. (`Breakdown.CellCert.CellFormula.CanonicalInputs.Internal.rowApply_shifted`)

**Recover the radial side index.** Encoding a radial side in the four-side index recovers its original radial-side index. (`Breakdown.CellCert.CellFormula.CanonicalInputs.Internal.sideRadialIndex_eq`)

**Recover the height side index.** Encoding a height side in the four-side index recovers its original height-side index. (`Breakdown.CellCert.CellFormula.CanonicalInputs.Internal.sideHeightIndex_eq`)

**Shifted data represent the field.** The strain-face statement and layout assumptions show that gauge-shifted data represent the admissible field for the cell energy calculation. (`Breakdown.CellCert.CellFormula.CanonicalInputs.Internal.represents_of`)

**Canonical cell inputs are valid.** The row, gauge, local-form, low-entry, parameter and strain-face statements establish validity of the canonical cell inputs. (`Breakdown.CellCert.CellFormula.canonicalInputsValid_of`)

### Breakdown.FracCell.CellAnalysisAssembly

This file assembles the analytic cell inequalities in successive stages, ending with the cell-matrix bound after the named analytic interfaces have been discharged; its closed theorem still assumes valid numerical and geometric cell data.

**Cell matrix below cell contribution.** For 1 < α < 5/4 and the stated form, cell, coordinate and moment conditions, the cell matrix on every admissible assembled state is bounded by its physical cell contribution, using the lower bound for the cell contribution by the cell form. (`Breakdown.CellCert.CellAnalysis.cellBound_of_cellData_of`)

**Velocity tail from gradient energy.** The bound of the velocity tail by top-degree and gradient-tail energy follows from the weak radial-mode identity, square integrability of gradient modes, square integrability of velocity modes, height-mode integration-by-parts identity and radial polynomial-projection bound. (`Breakdown.CellCert.CellAnalysis.velocityTail_of_open`)

**Cell density after tail charges.** The cell density lower bound after explicit tail charges follows from the weighted coefficient-tail estimate and sharp modal quadratic estimate. (`Breakdown.CellCert.CellAnalysis.cellSharpBound_of_leaves`)

**Cell density after tail charges.** The cell density lower bound after explicit tail charges follows from the square integrability of the cylindrical modes, radial-mode integration-by-parts relation, height-mode integration-by-parts relation, weak radial-mode identity, height-mode integration-by-parts identity, sharp row-pairing identity, bound for unresolved rows using harmonic classes and bound on the high-mode Y charges. (`Breakdown.CellCert.CellAnalysis.cellSharpBound_of_open`)

**Finite form below local energy.** The lower bound for the local analytic form by its finite quadratic form follows from the radial component energy estimate, height component energy estimate, angular component energy estimate, finite form for the top-degree energy, finite form for the harmonic-class losses, finite form for the resolved-mode pairings and finite form for the cross terms. (`Breakdown.CellCert.CellEnergy.localFormBound_of_leaves`)

**Finite local form below cell energy.** Under the stated cell, basis, scalar, regularity and representation conditions, the finite local quadratic form is at most the analytic local cell form. (`Breakdown.CellCert.CellEnergy.localForm_le_of`)

**Finite form below local energy.** The lower bound for the local analytic form by its finite quadratic form follows from the radial component energy estimate, height component energy estimate, angular component energy estimate, finite form for the top-degree energy, finite form for the harmonic-class losses, integrability of the resolved-mode pairings, polynomial expansion of the low gradient modes, polynomial expansion of the low velocity modes and finite form for the cross terms. (`Breakdown.CellCert.CellEnergy.localFormBound_of_parts`)

**Finite form below local energy.** The lower bound for the local analytic form by its finite quadratic form follows from the radial component energy estimate, height component energy estimate, angular component energy estimate, finite form for the top-degree energy, finite form for the harmonic-class losses, integrability of the resolved-mode pairings and finite form for the cross terms. (`Breakdown.CellCert.CellEnergy.localFormBound_of_open`)

**Exact formula below scaled cell form.** For 1 < α < 5/4 and the stated valid cell and formula inputs with positive split viscosity, the exact finite quadratic formula is at most the cell form divided by that viscosity, using the quadratic representation of the cell formula, identity for the near quadratic form, identity for the row and Y coefficient pairing and identity for the far quadratic form. (`Breakdown.CellCert.CellFormula.exactFormula_represents_of_quadratic`)

**Bound the exact cell formula.** The bound for the exact finite cell formula follows from the quadratic representation of the cell formula, identity for the near quadratic form, synthesis of the finite cell formula and linearity of the Y coefficients. (`Breakdown.CellCert.CellFormula.exactFormulaBound_of_leaves`)

**Real coordinates for shifted data.** The real-coordinate reduction of gauge-shifted data follows from the removal of redundant plane coordinates. (`Breakdown.CellCert.CellFormula.shiftedRealReduction_of_plane`)

**Real coordinates for shifted data.** The real-coordinate reduction of gauge-shifted data follows from the independence of segment data and independence of corner data. (`Breakdown.CellCert.CellFormula.shiftedRealReduction_of_leaves`)

**Valid cell coefficient relations.** The validity of the cell coefficient relations follows from the radial coefficient relations, height coefficient relations, angular coefficient relations, weak radial-mode identity, height side relations, integrability of radius-weighted modes at the axis, axis boundary-flux identity, stream-function relations and side-splitting relations. (`Breakdown.CellCert.CellFormula.relationsHold_of_leaves`)

**Parameterize shifted cell data.** The parameterization of gauge-shifted data follows from the parameterization of the true field data. (`Breakdown.CellCert.CellFormula.shiftedParam_of`)

**Parameterize shifted cell data.** The parameterization of gauge-shifted data follows from the validity of the cell coefficient relations. (`Breakdown.CellCert.CellFormula.shiftedParam_of_relations`)

**Identify the face strain rows.** The identification of the face strain rows follows from the evaluation of velocity side data, evaluation of gradient side data, tangential derivative relation on radial faces, angular derivative relation on radial faces, normal derivative relation on height faces, angular derivative relation on height faces and trace-free face relation. (`Breakdown.CellCert.CellFormula.strainFace_of_leaves`)

**Exact formula below scaled cell form.** For 1 < α < 5/4 and the stated valid cell and formula inputs with positive split viscosity, the exact finite quadratic formula is at most the cell form divided by that viscosity, using the identity for the near quadratic form, identity for the row and Y coefficient pairing and identity for the far quadratic form. (`Breakdown.CellCert.CellFormula.exactFormula_represents`)

**Bound the exact cell formula.** The bound for the exact finite cell formula follows from the linearity of the Y coefficients. (`Breakdown.CellCert.CellFormula.exactFormulaBound_of_coefLinear`)

**Bound the exact cell formula.** For 1 < α < 5/4, valid form, cell and formula data with positive split viscosity and far support contained in the retained low support bound the exact matrix on reconstructed admissible coordinates by the analytic cell form divided by the split viscosity. (`Breakdown.CellCert.CellFormula.exactFormulaBound_holds`)

**Construct the prescribed gauge shift.** For a valid pressure layout and gauge specification, left and right shifts that are linear on admissible fields and satisfy the prescribed jump and root conditions define a valid gauge shift whose deleted data coordinates vanish. (`Breakdown.CellCert.CellFormula.gaugeShiftOf_holds`)

**Cell matrix below scaled cell form.** For 1 < α < 5/4 and the stated form, coordinate, moment and free-slot conditions, the cell matrix on the assembled state is bounded by 4π times the cell form, using the bound for the exact finite cell formula, validity of the canonical cell inputs, removal of redundant plane coordinates and construction of the prescribed gauge shift. (`Breakdown.CellCert.CellCoordinates.cellMatrix_le_cellForm_of_coords_of`)

**Cell matrix below cell contribution.** For 1 < α < 5/4 and the stated form, cell, coordinate and moment conditions, the cell matrix on every admissible assembled state is bounded by its physical cell contribution, using the lower bound for the cell contribution by the cell form, bound for the exact finite cell formula, validity of the canonical cell inputs, removal of redundant plane coordinates and construction of the prescribed gauge shift. (`Breakdown.CellCert.CellCoordinates.cellBound_of_coords`)

**Cell matrix below scaled cell form.** For 1 < α < 5/4 and the stated form, coordinate, moment and free-slot conditions, the cell matrix on the assembled state is bounded by 4π times the cell form, using the validity of the canonical cell inputs, independence of segment data and independence of corner data. (`Breakdown.CellCert.CellCoordinates.cellMatrix_le_cellForm_of_open`)

**Cell matrix below cell contribution.** For 1 < α < 5/4 and the stated form, cell, coordinate and moment conditions, the cell matrix on every admissible assembled state is bounded by its physical cell contribution, using the lower bound for the cell contribution by the cell form, validity of the canonical cell inputs, independence of segment data and independence of corner data. (`Breakdown.CellCert.CellCoordinates.cellBound_of_open`)

**Majorize far coefficients.** The majorant for the far-coefficient sum follows from the far-coefficient representation and comparison of cylindrical integral expressions. (`Breakdown.CellCert.CellAnalysis.farMajorant_of_open`)

**Finite far row contribution.** For a valid cell and bases with polynomial row data of degree E, the far row square equals its finite sum through the prescribed degree E. (`Breakdown.CellCert.CellAnalysis.rowFarFinite_closed`)

**Stream-function boundary flux.** The stream-function boundary-flux relation follows from the cylindrical boundary-flux identity, radial flux relation across the axis, independence of stream data and height boundary-flux relation. (`Breakdown.CellCert.CellCoordinates.fluxStream_of_open`)

**Compatible mesh coordinates.** The compatibility of the assembled mesh coordinates follows from the identification of the mesh skeleton slots, linearity of the mesh gauge data and affine dependence of the cell data. (`Breakdown.CellCert.CellCoordinates.meshCompatibility_of_slot`)

**Integrable cylindrical modes.** Every velocity-mode component and gradient-mode entry of a second-order field becomes integrable on a valid cell rectangle after multiplication by the radial line weight. (`Breakdown.CellCert.CellFormula.modeIntegrable_holds`)

**Finite form below local energy.** The lower bound for the local analytic form by its finite quadratic form follows from the radial trace identity, weak height-mode identity, weak circle integration-by-parts identity, integrability of the resolved-mode pairings and finite form for the cross terms. (`Breakdown.CellCert.CellEnergy.localFormBound_of_modes`)

**Valid cell coefficient relations.** The validity of the cell coefficient relations follows from the radial-mode integration-by-parts relation, height-mode integration-by-parts identity, angular derivative-mode identities, weak radial-mode identity, integrability of radius-weighted modes at the axis, axis boundary-flux identity, integrability of modes on strips, cylindrical boundary-flux identity and integrability of modes on cell rectangles. (`Breakdown.CellCert.CellFormula.relationsHold_of_modes`)

**Parameterize shifted cell data.** The parameterization of gauge-shifted data follows from the radial-mode integration-by-parts relation, height-mode integration-by-parts identity, angular derivative-mode identities, weak radial-mode identity, integrability of radius-weighted modes at the axis, axis boundary-flux identity, integrability of modes on strips, cylindrical boundary-flux identity and integrability of modes on cell rectangles. (`Breakdown.CellCert.CellFormula.shiftedParam_of_modes`)

**Valid canonical cell inputs.** The validity of the canonical cell inputs follows from the identification of the cell layout rows with field values, invariance of the cell data under gauge changes, lower bound for the local analytic form by its finite quadratic form, parameterization of gauge-shifted data, independence of segment data, independence of corner data and identification of the face strain rows. (`Breakdown.CellCert.CellFormula.canonicalInputsValid_of_open`)

**Cell matrix below cell contribution.** For 1 < α < 5/4 and the stated form, cell, coordinate and moment conditions, the cell matrix on every admissible assembled state is bounded by its physical cell contribution, using the lower bound for the cell contribution by the cell form, identification of the cell layout rows with field values, invariance of the cell data under gauge changes, lower bound for the local analytic form by its finite quadratic form, parameterization of gauge-shifted data, identification of the face strain rows, independence of segment data and independence of corner data. (`Breakdown.CellCert.CellCoordinates.cellBound_of_parts`)

**Velocity tail from gradient energy.** The bound of the velocity tail by top-degree and gradient-tail energy follows from the weak radial-mode identity and height-mode integration-by-parts identity. (`Breakdown.CellCert.CellAnalysis.velocityTail_of_weak`)

**Valid cell coefficient relations.** The validity of the cell coefficient relations follows from the radial-mode integration-by-parts relation, height-mode integration-by-parts identity, weak circle integration-by-parts identity, weak radial-mode identity and cylindrical boundary-flux identity. (`Breakdown.CellCert.CellFormula.relationsHold_of_core`)

**Parameterize shifted cell data.** The parameterization of gauge-shifted data follows from the radial-mode integration-by-parts relation, height-mode integration-by-parts identity, weak circle integration-by-parts identity, weak radial-mode identity and cylindrical boundary-flux identity. (`Breakdown.CellCert.CellFormula.shiftedParam_of_core`)

**Identify the face strain rows.** The identification of the face strain rows follows from the integrability of side-strip data, tangential derivative relation on radial faces, angular derivative relation on radial faces, normal derivative relation on height faces, weak circle integration-by-parts identity and trace-free face relation. (`Breakdown.CellCert.CellFormula.strainFace_of_core`)

**Cell density after tail charges.** The cell density lower bound after explicit tail charges follows from the radial-mode integration-by-parts relation, height-mode integration-by-parts relation, weak radial-mode identity, height-mode integration-by-parts identity, sharp row-pairing identity, bound for unresolved rows using harmonic classes and bound on the high-mode Y charges. (`Breakdown.CellCert.CellAnalysis.cellSharpBound_of_modes`)

**Cell form below its contribution.** The lower bound for the cell contribution by the cell form follows from the expression of the cell density by its cylindrical modes, radial-mode integration-by-parts relation, height-mode integration-by-parts relation, weak radial-mode identity, height-mode integration-by-parts identity, sharp row-pairing identity, bound for unresolved rows using harmonic classes and bound on the high-mode Y charges. (`Breakdown.CellCert.CellAnalysis.cellFormBound_of_open`)

**Cell matrix below cell contribution.** For 1 < α < 5/4 and the stated form, cell, coordinate and moment conditions, the cell matrix on every admissible assembled state is bounded by its physical cell contribution, using the expression of the cell density by its cylindrical modes, radial-mode integration-by-parts relation, height-mode integration-by-parts relation, weak radial-mode identity, height-mode integration-by-parts identity, sharp row-pairing identity, bound for unresolved rows using harmonic classes, bound on the high-mode Y charges, identification of the cell layout rows with field values, invariance of the cell data under gauge changes, radial trace identity, weak height-mode identity, weak circle integration-by-parts identity, integrability of the resolved-mode pairings, finite form for the cross terms, radial-mode integration-by-parts relation, cylindrical boundary-flux identity, integrability of side-strip data, tangential derivative relation on radial faces, angular derivative relation on radial faces, normal derivative relation on height faces, trace-free face relation, independence of segment data and independence of corner data. (`Breakdown.CellCert.CellCoordinates.cellBound_of_leaves`)

**Velocity tail from gradient energy.** For a valid cell, degree cutoff at least five and a second-order field, any nonnegative multiple of the velocity-tail sum is bounded by the same multiple of the top-degree gradient contribution plus the full gradient-tail sum. (`Breakdown.CellCert.CellAnalysis.velocityTail_holds`)

**Majorize far coefficients.** The majorant for the far-coefficient sum follows from the far-coefficient representation. (`Breakdown.CellCert.CellAnalysis.farMajorant_of_coef`)

**Cell density after tail charges.** The cell density lower bound after explicit tail charges follows from the sharp row-pairing identity, bound for unresolved rows using harmonic classes and bound on the high-mode Y charges. (`Breakdown.CellCert.CellAnalysis.cellSharpBound_of_remaining`)

**Cylindrical boundary flux.** The cylindrical boundary-flux identity follows from the strip trace identity. (`Breakdown.CellCert.CellFormula.cylinderFlux_of_trace`)

**Identify the face strain rows.** The identification of the face strain rows follows from the weak mixed radial derivative relation and trace-free face relation. (`Breakdown.CellCert.CellFormula.strainFace_of_remaining`)

**Stream-function boundary flux.** The stream-function boundary-flux relation follows from the strip trace identity, independence of stream data and height boundary-flux relation. (`Breakdown.CellCert.CellCoordinates.fluxStream_of_stream`)

**Cell matrix below cell contribution.** For 1 < α < 5/4 and the stated form, cell, coordinate and moment conditions, the cell matrix on every admissible assembled state is bounded by its physical cell contribution, using the density identity on cylindrical slices, sharp row-pairing identity, bound for unresolved rows using harmonic classes, bound on the high-mode Y charges, identification of the cell layout rows with field values, invariance of the cell data under gauge changes, integrability of the resolved-mode pairings, finite form for the cross terms, strip trace identity, weak mixed radial derivative relation, trace-free face relation, independence of segment data and independence of corner data. (`Breakdown.CellCert.CellCoordinates.cellBound_of_remaining`)

**Majorize far coefficients.** For 1 < α < 5/4, valid form, box, scalar and basis data with the stated cell inclusion, mode containment and far-majorant condition bound the weighted far-coefficient sum of every admissible input by the finite far form. (`Breakdown.CellCert.CellAnalysis.farMajorant_holds`)

**Sharp identity for the row pairing.** The sharp row-pairing identity follows from the expanded Fourier-mode identity for the row pairing. (`Breakdown.CellCert.CellAnalysis.sharpRowIdentity_of_unfolded`)

**Cylindrical boundary flux.** For a second-order field, positive outer radius, a distinct nonnegative comparison radius and ordered heights, the zero-mode radial side flux plus the upper and lower height fluxes sums to zero. (`Breakdown.CellCert.CellFormula.cylinderFlux_holds`)

**Identify the face strain rows.** The identification of the face strain rows follows from the trace-free face relation. (`Breakdown.CellCert.CellFormula.strainFace_of_trace`)

**Stream-function boundary flux.** The stream-function boundary-flux relation follows from the independence of stream data and height boundary-flux relation. (`Breakdown.CellCert.CellCoordinates.fluxStream_of_segment`)

**Cell matrix below cell contribution.** For 1 < α < 5/4 and the stated form, cell, coordinate and moment conditions, the cell matrix on every admissible assembled state is bounded by its physical cell contribution, using the density identity on cylindrical slices, expanded Fourier-mode identity for the row pairing, bound for unresolved rows using harmonic classes, bound on the high-mode Y charges, identification of the cell layout rows with field values, invariance of the cell data under gauge changes, integrability of the resolved-mode pairings, finite form for the cross terms, trace-free face relation and independence of segment data. (`Breakdown.CellCert.CellCoordinates.cellBound_of_final`)

**Sharp modal energy-tail bound.** The sharp modal energy-tail estimate follows from the modal energy-sum identity, gradient-mode energy identity, vorticity-mode energy identity, velocity coefficient identity and regularity of the modal energy tails. (`Breakdown.CellCert.CellAnalysis.sharpEnergyTail_of_open`)

**Modal stretching supremum bound.** The supremum bound for modal stretching follows from the circle estimate for the model strain, mean-mode circle estimate, circle estimate for the oscillatory model gradient and bound on the oscillatory mode sum. (`Breakdown.CellCert.CellAnalysis.sharpSupremum_of_open`)

**Bound the high-mode Y charges.** The bound on the high-mode Y charges follows from the regularity of the mode expansions, Fourier-series representation of the modes, circle estimate for the model strain, mean-mode circle estimate, circle estimate for the oscillatory model gradient, bound on the oscillatory mode sum, sharp cross-term identity, harmonic-class cross-term bound, modal energy-sum identity, gradient-mode energy identity, vorticity-mode energy identity, velocity coefficient identity and regularity of the modal energy tails. (`Breakdown.CellCert.CellAnalysis.sharpYCharge_of_open`)

**Density on cylindrical slices.** For 1 < α < 5/4, valid form data and a valid cell with axisymmetric weight, model reflection symmetry and cell-region inclusion express the full-turn density and pin integrals almost everywhere as 2π times their stated modal sums and pairings. (`Breakdown.CellCert.CellAnalysis.densitySlice_holds`)

**Unresolved row class bound.** For 1 < α < 5/4, valid form and cell data with an axisymmetric weight bound minus twice the unresolved row pairing for admissible inputs and row-supported multipliers by the class-weighted multiplier squares plus the unresolved row charge. (`Breakdown.CellCert.CellAnalysis.unresolvedRowClass_holds`)

**Sharp modal energy-tail bound.** The sharp modal energy-tail estimate follows from the gradient-mode energy identity, vorticity-mode energy identity and velocity coefficient identity. (`Breakdown.CellCert.CellAnalysis.sharpEnergyTail_of_rest`)

**Modal stretching supremum bound.** The supremum bound for modal stretching follows from the circle estimate for the model strain, circle estimate for the oscillatory model gradient and bound on the oscillatory mode sum. (`Breakdown.CellCert.CellAnalysis.sharpSupremum_of_rest`)

**Symmetric sharp cross-term identity.** The symmetric form of the sharp cross-term identity follows from the regularity of the oscillatory cross terms. (`Breakdown.CellCert.CellAnalysis.sharpCrossSymm_of_rest`)

**Bound the high-mode Y charges.** The bound on the high-mode Y charges follows from the regularity of the mode expansions, circle estimate for the model strain, circle estimate for the oscillatory model gradient, bound on the oscillatory mode sum, sharp cross-term identity, harmonic-class cross-term bound, gradient-mode energy identity, vorticity-mode energy identity and velocity coefficient identity. (`Breakdown.CellCert.CellAnalysis.sharpYCharge_of_rest`)

**Compatible mesh coordinates.** The compatibility of the assembled mesh coordinates follows from the identification of the mesh skeleton slots. (`Breakdown.CellCert.CellCoordinates.meshCompatibility_of_rest`)

**Cell matrix below cell contribution.** For 1 < α < 5/4 and the stated form, cell, coordinate and moment conditions, the cell matrix on every admissible assembled state is bounded by its physical cell contribution, using the expanded Fourier-mode identity for the row pairing, bound on the high-mode Y charges, identification of the cell layout rows with field values, trace-free face relation and independence of segment data. (`Breakdown.CellCert.CellCoordinates.cellBound_of_rest`)

**Regular oscillatory cross terms.** The regularity of the oscillatory cross terms follows from the regularity of the mode expansions. (`Breakdown.CellCert.CellAnalysis.waveCrossRegular_of_expansion`)

**Symmetric sharp cross-term identity.** The symmetric form of the sharp cross-term identity follows from the regularity of the mode expansions. (`Breakdown.CellCert.CellAnalysis.sharpCrossSymm_of_expansion`)

**Harmonic-class cross-term bound.** The harmonic-class cross-term bound follows from the decomposition of products across harmonic classes and regularity of the harmonic-class cross terms. (`Breakdown.CellCert.CellAnalysis.classCross_of_rest`)

**Bound the high-mode Y charges.** The bound on the high-mode Y charges follows from the regularity of the mode expansions, circle estimate for the model strain, circle estimate for the oscillatory model gradient, bound on the oscillatory mode sum, sharp cross-term identity, decomposition of products across harmonic classes, regularity of the harmonic-class cross terms, gradient-mode energy identity, vorticity-mode energy identity and velocity coefficient identity. (`Breakdown.CellCert.CellAnalysis.sharpYCharge_of_leafset`)

**Cell matrix below cell contribution.** For 1 < α < 5/4 and the stated form, cell, coordinate and moment conditions, the cell matrix on every admissible assembled state is bounded by its physical cell contribution, using the expanded Fourier-mode identity for the row pairing, regularity of the mode expansions, circle estimate for the model strain, circle estimate for the oscillatory model gradient, bound on the oscillatory mode sum, sharp cross-term identity, decomposition of products across harmonic classes, regularity of the harmonic-class cross terms, gradient-mode energy identity, vorticity-mode energy identity, velocity coefficient identity, identification of the cell layout rows with field values, trace-free face relation and independence of segment data. (`Breakdown.CellCert.CellCoordinates.cellBound_of_leafset`)

**Sharp modal energy-tail bound.** For 1 < α < 5/4, valid form and cell data with an axisymmetric weight bound the base energy, sharp weighted term and absorption sum by the total modal energy for every admissible input. (`Breakdown.CellCert.CellAnalysis.sharpEnergyTail_holds`)

**Modal stretching supremum bound.** For 1 < α < 5/4, valid form and cell data with an axisymmetric weight make the negative modal supremum sum at most the sharp stretching quantity for every admissible input. (`Breakdown.CellCert.CellAnalysis.sharpSupremum_holds`)

**Harmonic-class cross-term bound.** The harmonic-class cross-term bound follows from the decomposition of products across harmonic classes. (`Breakdown.CellCert.CellAnalysis.classCross_of_productSplit`)

**Bound the high-mode Y charges.** The bound on the high-mode Y charges follows from the regularity of the mode expansions, sharp cross-term identity and decomposition of products across harmonic classes. (`Breakdown.CellCert.CellAnalysis.sharpYCharge_of_final`)

**Stream-function boundary flux.** For an admissible field, a layout with matching symmetry order and a valid face segment, the stated constant or linear test representation identifies zero-mode side fluxes with endpoint differences of the stream value under the radius and endpoint conditions, and the stream value at zero height vanishes. (`Breakdown.CellCert.CellCoordinates.fluxStream_holds`)

**Compatible mesh coordinates.** For 1 < α < 5/4, valid form and mesh data give canonical moments matching every local coordinate map, valid gauge roots and jumps, linear canonical shifts and moments on admissible fields, and recovery of the designated actuator coefficients. (`Breakdown.CellCert.CellCoordinates.meshCompatibility_holds`)

**Cell matrix below cell contribution.** For 1 < α < 5/4 and the stated form, cell, coordinate and moment conditions, the cell matrix on every admissible assembled state is bounded by its physical cell contribution, using the expanded Fourier-mode identity for the row pairing, regularity of the mode expansions, sharp cross-term identity, decomposition of products across harmonic classes, identification of the cell layout rows with field values and trace-free face relation. (`Breakdown.CellCert.CellCoordinates.cellBound_of_core`)

**Regular mode expansions.** The regularity of the mode expansions follows from the second-derivative tensor Fourier-series identity, gradient Fourier-series identity and regularity of the oscillatory mode terms. (`Breakdown.CellCert.CellAnalysis.modeExpansionRegular_of_series`)

**Symmetric sharp cross-term identity.** The symmetric form of the sharp cross-term identity follows from the second-derivative tensor Fourier-series identity, gradient Fourier-series identity and regularity of the oscillatory mode terms. (`Breakdown.CellCert.CellAnalysis.sharpCrossSymm_of_series`)

**Cell matrix below cell contribution.** For 1 < α < 5/4 and the stated form, cell, coordinate and moment conditions, the cell matrix on every admissible assembled state is bounded by its physical cell contribution, using the expanded Fourier-mode identity for the row pairing, second-derivative tensor Fourier-series identity, gradient Fourier-series identity, regularity of the oscillatory mode terms, sharp cross-term identity, decomposition of products across harmonic classes, identification of the cell layout rows with field values and trace-free face relation. (`Breakdown.CellCert.CellCoordinates.cellBound_of_tail`)

**Sharp cross-term identity.** The sharp cross-term identity follows from the symmetric form of the sharp cross-term identity. (`Breakdown.CellCert.CellAnalysis.sharpCross_of_symm`)

**Sharp cross-term identity.** The sharp cross-term identity follows from the second-derivative tensor Fourier-series identity, gradient Fourier-series identity and regularity of the oscillatory mode terms. (`Breakdown.CellCert.CellAnalysis.sharpCross_of_series`)

**Bound the high-mode Y charges.** The bound on the high-mode Y charges follows from the second-derivative tensor Fourier-series identity, gradient Fourier-series identity, regularity of the oscillatory mode terms and decomposition of products across harmonic classes. (`Breakdown.CellCert.CellAnalysis.sharpYCharge_of_series`)

**Cell matrix below cell contribution.** For 1 < α < 5/4 and the stated form, cell, coordinate and moment conditions, the cell matrix on every admissible assembled state is bounded by its physical cell contribution, using the expanded Fourier-mode identity for the row pairing, second-derivative tensor Fourier-series identity, gradient Fourier-series identity, regularity of the oscillatory mode terms, decomposition of products across harmonic classes, identification of the cell layout rows with field values and trace-free face relation. (`Breakdown.CellCert.CellCoordinates.cellBound_of_last`)

**Bound the high-mode Y charges.** The bound on the high-mode Y charges follows from the second-derivative tensor Fourier-series identity, gradient Fourier-series identity, regularity of the oscillatory mode terms and harmonic-class cross-term bound. (`Breakdown.CellCert.CellAnalysis.sharpYCharge_of_cross`)

**Cell matrix below cell contribution.** For 1 < α < 5/4 and the stated form, cell, coordinate and moment conditions, the cell matrix on every admissible assembled state is bounded by its physical cell contribution, using the expanded Fourier-mode identity for the row pairing, second-derivative tensor Fourier-series identity, gradient Fourier-series identity, regularity of the oscillatory mode terms, harmonic-class cross-term bound, identification of the cell layout rows with field values and trace-free face relation. (`Breakdown.CellCert.CellCoordinates.cellBound_of_cross`)

**Expanded row-mode identity.** For 1 < α < 5/4, valid form and cell data with an axisymmetric weight express each selected row pairing of the high coupling field as 4π times the sum of its resolved-and-band unfolded pairings and unresolved mode series for every admissible input. (`Breakdown.CellCert.CellAnalysis.rowModeUnfolded_holds`)

**Bound the high-mode Y charges.** The bound on the high-mode Y charges follows from the regularity of the oscillatory mode terms and harmonic-class cross-term bound. (`Breakdown.CellCert.CellAnalysis.sharpYCharge_of_wave`)

**Identify the face strain rows.** For a valid cell layout and an admissible input, every selected strain-face moment within the side degree bound equals its row evaluated on the true field data, with nonzero inner radius required on the inner radial face. (`Breakdown.CellCert.CellFormula.strainFace_holds`)

**Cell matrix below cell contribution.** For 1 < α < 5/4 and the stated form, cell, coordinate and moment conditions, the cell matrix on every admissible assembled state is bounded by its physical cell contribution, using the regularity of the oscillatory mode terms, harmonic-class cross-term bound and identification of the cell layout rows with field values. (`Breakdown.CellCert.CellCoordinates.cellBound_of_wave`)

**Cell matrix below cell contribution.** For 1 < α < 5/4 and the stated form, cell, coordinate and moment conditions, the cell matrix on every admissible assembled state is bounded by its physical cell contribution, using the regularity of the oscillatory mode terms and identification of the cell layout rows with field values. (`Breakdown.CellCert.CellCoordinates.cellBound_of_waveRegular`)

**Cell matrix below cell contribution.** For 1 < α < 5/4 and the stated form, cell, coordinate and moment conditions, the cell matrix on every admissible assembled state is bounded by its physical cell contribution, using the identification of the cell layout rows with field values. (`Breakdown.CellCert.CellCoordinates.cellBound_of_layoutRow`)

**Cell matrix below cell contribution.** For 1 < α < 5/4 and the stated form, cell, coordinate and moment conditions, the cell matrix on every admissible assembled state is bounded by its physical cell contribution. (`Breakdown.CellCert.CellCoordinates.cellBound_closed`)

### Breakdown.FracCell.CellCoordsDefs

This file states how the finite cell coordinates, gauge data and matrix embeddings correspond to the analytic field data.

**Valid cell coordinates and embedding.** The coordinate-validity proposition requires a valid conjugation-compatible layout, gauge and trace data, correct moment slots, and the stated bounds connecting the given matrix to the exact formula. (`Breakdown.CellCert.CellCoordinates.IsCellCoords`)

### Breakdown.FracCell.CellDataDefs

This file defines the weighted cell energies, resolved and unresolved mode charges, and the conditions that make a cell certificate represent the analytic quadratic form.

**Radially weighted rectangle measure.** The cell measure is planar volume restricted to the rectangle with density given by the radial line weight. (`Breakdown.CellCert.CellAnalysis.CellBox.measure`)

**Scaled polynomial function space.** The scaled polynomial space consists of the prescribed scalar multiplier times polynomials of the stated two degrees. (`Breakdown.CellCert.CellAnalysis.scaledPolyFn`)

**Supremum over polynomial tests.** The test supremum takes the supremum of squared weighted pairings divided by strictly positive test norms. (`Breakdown.CellCert.CellAnalysis.CellBox.testSupremum`)

**Radial projected energy.** The radial energy combines the projected derivative energy with the stated polynomial-test suprema, using a separate axis case. (`Breakdown.CellCert.CellAnalysis.CellBox.radialEnergy`)

**Height projected energy.** The height energy combines the projected height derivative energy with the stated polynomial-test suprema and axis case. (`Breakdown.CellCert.CellAnalysis.CellBox.heightEnergy`)

**Angular projected energy.** The angular energy uses a radius-scaled test space on the axis and the stated projected norm plus remainder test away from the axis. (`Breakdown.CellCert.CellAnalysis.CellBox.angularEnergy`)

**Radial derivative mode.** The radial gradient mode selects the radial final index of the second-derivative tensor mode. (`Breakdown.CellCert.CellAnalysis.radialGradMode`)

**Height derivative mode.** The height gradient mode selects the height final index of the second-derivative tensor mode. (`Breakdown.CellCert.CellAnalysis.heightGradMode`)

**Radius-weighted angular gradient mode.** The angular gradient mode is radius times the angular final-index second-derivative mode. (`Breakdown.CellCert.CellAnalysis.angularGradMode`)

**Second-derivative mode energy.** The second-derivative mode energy sums the squared norms of every tensor-mode entry. (`Breakdown.CellCert.CellAnalysis.secondModeSq`)

**Curl-gradient mode energy.** The curl-gradient mode energy sums the squared curl-component norms of the second-derivative mode slices. (`Breakdown.CellCert.CellAnalysis.curlGradModeSq`)

**Resolved gradient energy.** The gradient energy sums the radial, height and angular energies over every matrix component. (`Breakdown.CellCert.CellAnalysis.CellBox.strainEnergy`)

**Resolved vorticity energy.** The vorticity energy sums the radial, height and angular energies of the curl components. (`Breakdown.CellCert.CellAnalysis.CellBox.vorticityEnergy`)

**Gradient energy beyond projection.** The gradient-tail weight measures the radial and height derivatives left after subtracting the polynomial projection. (`Breakdown.CellCert.CellAnalysis.CellBox.tailGradWeight`)

**Full weighted gradient energy.** The full gradient weight is the inner-radius multiple of the stated radial and height weighted derivative norms. (`Breakdown.CellCert.CellAnalysis.CellBox.fullGradWeight`)

**Radial orthogonal projection.** The radial projection chooses polynomial coefficients satisfying the weighted moment equations, and returns zero when no such coefficients exist. (`Breakdown.CellCert.CellAnalysis.CellBox.projR`)

**Top-degree derivative energy.** The top part is the difference between the stated successive radial and height projection energies. (`Breakdown.CellCert.CellAnalysis.CellBox.topPart`)

**Velocity derivative tail.** The velocity tail measures radial error beyond the radial projection and height error between that projection and the full polynomial projection. (`Breakdown.CellCert.CellAnalysis.CellBox.velocityTail`)

**Resolved modal energy requirement.** This proposition bounds resolved gradient and vorticity energies, including their tails, by the corresponding full second-derivative mode integrals under the stated degree and axis conditions. (`Breakdown.CellCert.CellAnalysis.ResolvedEnergyStatement`)

Proved from further statements by `Breakdown.CellCert.CellAnalysis.resolvedEnergy_of`, `Breakdown.CellCert.CellAnalysis.resolvedEnergy_of_modes`, `Breakdown.CellCert.CellAnalysis.resolvedEnergy_of_modeFacts`.

**Unresolved modal energy requirement.** This proposition bounds the full weighted radial, height and angular gradient-mode energy by the second-derivative mode integral. (`Breakdown.CellCert.CellAnalysis.UnresolvedEnergyStatement`)

Proved by `Breakdown.CellCert.CellAnalysis.unresolvedEnergy`.

**Velocity-tail energy requirement.** For degree at least five, this proposition bounds a nonnegatively weighted velocity tail by the corresponding top-degree and gradient-tail energies. (`Breakdown.CellCert.CellAnalysis.VelocityTailStatement`)

Proved by `Breakdown.CellCert.CellAnalysis.velocityTail_holds`. Also proved from further statements by `Breakdown.CellCert.CellAnalysis.velocityTail_of_open`, `Breakdown.CellCert.CellAnalysis.velocityTail_of_weak`, `Breakdown.CellCert.CellAnalysis.velocityTail_of`, `Breakdown.CellCert.CellAnalysis.velocityTail_of_parts`, `Breakdown.CellCert.CellAnalysis.velocityTail_of_leaves`.

**Trace-free complex matrix.** A complex matrix is trace-free when the sum of its diagonal entries is zero. (`Breakdown.CellCert.CellAnalysis.IsTraceFree`)

**Squared symmetric matrix part.** The symmetric square is the sum of squared norms of the symmetrized matrix entries. (`Breakdown.CellCert.CellAnalysis.symSq`)

**Squared antisymmetric matrix part.** The antisymmetric square is the sum of squared norms of the antisymmetrized matrix entries. (`Breakdown.CellCert.CellAnalysis.antiSq`)

**Angular action on a velocity mode.** The angular action multiplies by the frequency times i and adds the radial-angular frame corrections. (`Breakdown.CellCert.CellAnalysis.turnVec`)

**Local curl-gradient density.** The density form combines the curl square and full matrix square with the stated fractional coercivity coefficients. (`Breakdown.CellCert.CellAnalysis.CellScalars.densityForm`)

**Resolved pair loss.** The pair loss is the local matrix form minus the model stretching supremum loss. (`Breakdown.CellCert.CellAnalysis.CellScalars.pairLoss`)

**Unresolved-mode penalty.** The penalty is the chosen linear combination of strain, curl and velocity squares. (`Breakdown.CellCert.CellAnalysis.CellScalars.penalty`)

**Valid scalar cell estimates.** The scalar-data proposition imposes mode symmetries, coefficient bounds, pointwise absorption inequalities, positive tail weights and the required polynomial degree separation. (`Breakdown.CellCert.CellAnalysis.IsCellScalars`)

**Harmonic-class stretching loss.** A harmonic-class loss combines its strain deviation times curl energy with the stated gradient-deviation charge for strain and velocity. (`Breakdown.CellCert.CellAnalysis.CellClasses.classLoss`)

**Low polynomial gradient mode.** The low gradient mode is the two-variable polynomial projection through the stated degree. (`Breakdown.CellCert.CellAnalysis.CellBox.lowStrain`)

**Low polynomial velocity mode.** The low velocity mode is the polynomial projection through one less than the stated degree in each variable. (`Breakdown.CellCert.CellAnalysis.CellBox.lowVelocity`)

**Low gradient matrix at a point.** The low-gradient matrix collects all projected gradient-mode entries at one radial-height point. (`Breakdown.CellCert.CellAnalysis.CellBox.lowStrainAt`)

**Low velocity vector at a point.** The low-velocity vector collects all projected velocity-mode components at one radial-height point. (`Breakdown.CellCert.CellAnalysis.CellBox.lowVelocityAt`)

**Pairing of two resolved modes.** The resolved pair integrand combines their wave coupling and, on the diagonal, the local matrix form. (`Breakdown.CellCert.CellAnalysis.CellScalars.pairIntegrand`)

**Integrated resolved-mode pair form.** The local pair form is the real part of the weighted double sum of resolved-mode pairing integrals. (`Breakdown.CellCert.CellAnalysis.CellScalars.localPairForm`)

**Integrated harmonic-class losses.** The class term sums the assigned class losses of resolved low modes with their class share weights. (`Breakdown.CellCert.CellAnalysis.CellScalars.classTerm`)

**Resolved energy with top allowance.** The energy term combines gradient and vorticity energies and subtracts the allocated top-degree contribution. (`Breakdown.CellCert.CellAnalysis.CellScalars.energyTerm`)

**Actuator and pin linear terms.** The linear term pairs low gradient modes with the actuator and pin modes using their stated coefficients. (`Breakdown.CellCert.CellAnalysis.CellScalars.linearTerm`)

**Local cell quadratic form.** The local cell form is energy minus class losses plus resolved pair and linear terms. (`Breakdown.CellCert.CellAnalysis.CellScalars.localCellForm`)

**High-mode strain charge.** The strain Y term combines wave action, local matrix action and actuator-pin contributions with the radial conversion factor. (`Breakdown.CellCert.CellAnalysis.CellScalars.yStrain`)

**High-mode velocity charge.** The velocity Y term combines wave and local matrix actions with the radial conversion factor. (`Breakdown.CellCert.CellAnalysis.CellScalars.yVelocity`)

**Fold velocity into unresolved strain.** The folded Y term retains strain on resolved modes and folds the velocity charge into strain on unresolved modes. (`Breakdown.CellCert.CellAnalysis.CellScalars.yFolded`)

**Symmetric coefficient square.** The symmetric coefficient square is the squared norm sum of the symmetric matrix part. (`Breakdown.CellCert.CellAnalysis.CellScalars.symCoefSq`)

**Selected weighted coefficient charges.** The selected coefficient sum divides the symmetric, antisymmetric and velocity coefficient squares by their respective tail weights on the stated index ranges. (`Breakdown.CellCert.CellAnalysis.CellScalars.weightedCoefSum`)

**Finite near-coefficient charge.** The near charge applies the selected weighted coefficient sum to every finite near index. (`Breakdown.CellCert.CellAnalysis.CellScalars.nearWeighted`)

**Infinite far-coefficient charge.** The far charge sums the weighted coefficient squares over indices beyond the near degree. (`Breakdown.CellCert.CellAnalysis.CellScalars.farWeighted`)

**Reflection sign of a frame component.** Reflection changes the sign of the height component below the midplane and leaves all other components unchanged. (`Breakdown.CellCert.CellAnalysis.CellScalars.mirrorSign`)

**Reconstruct the low velocity field.** The low velocity field reconstructs the resolved polynomial modes in the Cartesian frame with the prescribed reflection sign. (`Breakdown.CellCert.CellAnalysis.CellScalars.lowVelocityField`)

**Reconstruct the low gradient field.** The low gradient field reconstructs the resolved polynomial matrix modes with one reflection sign for each frame index. (`Breakdown.CellCert.CellAnalysis.CellScalars.lowGradField`)

**Coupling of the high remainders.** The high coupling field combines the curl of the gradient remainder with model velocity and model curl with the velocity remainder. (`Breakdown.CellCert.CellAnalysis.CellScalars.highCouplingField`)

**Complex vector pairing.** The vector pairing sums each first-vector component times the conjugate of the second-vector component. (`Breakdown.CellCert.CellAnalysis.CellScalars.vecPair`)

**Row pairing with Y coefficients.** The row-Y pairing is the real part of the stated weighted near-coefficient matrix and velocity pairings. (`Breakdown.CellCert.CellAnalysis.CellScalars.rowYPair`)

**Far square of a row combination.** The far row square sums the weighted squares of a row combination's coefficients beyond the near degree. (`Breakdown.CellCert.CellAnalysis.CellScalars.rowSquareFar`)

**Low part of the row value.** The low row value subtracts the high-coupling pairing from the full row pairing and divides by 4π. (`Breakdown.CellCert.CellAnalysis.CellScalars.lowRowValue`)

**Select a low field coefficient.** The low-coefficient selector chooses a projected gradient entry for the first three column tags and a projected velocity component for the fourth. (`Breakdown.CellCert.CellAnalysis.CellScalars.lowCoef`)

**Vector for the far quadratic form.** The far vector combines low field coefficients with the actuator and free pin coefficients. (`Breakdown.CellCert.CellAnalysis.CellScalars.farVector`)

**Evaluate the far kernel form.** The far form is the real part of the finite sesquilinear form of the far kernel on its selected support. (`Breakdown.CellCert.CellAnalysis.CellScalars.farFormValue`)

**Residual row coefficient.** The row residual is the low row value minus its row-Y pairing. (`Breakdown.CellCert.CellAnalysis.CellScalars.rowResidual`)

**Full cell certificate form.** The cell form subtracts the near and allocated far charges from the local form and adds squares of the reduced row residuals. (`Breakdown.CellCert.CellAnalysis.CellScalars.cellForm`)

**Valid analytic and finite cell data.** The cell-data proposition combines geometry, scalar and basis validity with model symmetries, row and class conditions, multiplier bounds and the far-form and reducer estimates. (`Breakdown.CellCert.CellAnalysis.IsCellData`)

### Breakdown.FracCell.CellDensityModes

This file closes the passage from the physical cell density to its cylindrical mode formula.

**Cell density from its slice identity.** The cylindrical slice identity expresses the density and pin integrals as 4π times their radius-weighted modal integrals for 1 < α < 5/4, valid form data, admissible inputs and valid cells with the stated weight, mirror and inclusion conditions. (`Breakdown.CellCert.CellAnalysis.cellDensityModes_of`)

### Breakdown.FracCell.CellDensityModesBound

This file supplies the elementary energy and integrability bounds needed before integrating the cell density.

**Curl energy below matrix energy.** The curl norm squared is at most twice the matrix entry-square sum. (`Breakdown.FracInternal.CellDensityModesBound.curl_le`)

**Coordinate curl-square bound.** The coordinate curl expression squared and summed is at most twice the sum of squared matrix entries. (`Breakdown.FracInternal.CellDensityModesBound.curl_real`)

**Curl-gradient below full second energy.** The curl-gradient square is at most twice the full second-derivative square. (`Breakdown.FracInternal.CellDensityModesBound.curlGrad_le`)

**Bound a matrix pairing.** The absolute matrix-entry pairing is at most the sum of the two matrix entry-square sums. (`Breakdown.FracInternal.CellDensityModesBound.entryInner_le`)

**Continuous curl energy.** The squared curl norm is continuous in the matrix. (`Breakdown.FracInternal.CellDensityModesBound.cont_curl`)

**Continuous curl-gradient energy.** The curl-gradient square is continuous in the second-derivative tensor. (`Breakdown.FracInternal.CellDensityModesBound.cont_curlGrad`)

**Continuous matrix energy.** The matrix entry-square sum is continuous. (`Breakdown.FracInternal.CellDensityModesBound.cont_entrySq`)

**Nonnegative curl-gradient energy.** The curl-gradient square is nonnegative. (`Breakdown.FracInternal.CellDensityModesBound.nonneg_curlGrad`)

**Nonnegative matrix entry energy.** The matrix entry-square sum is nonnegative. (`Breakdown.FracInternal.CellDensityModesBound.nonneg_entrySq`)

**Integrable matrix pairing.** Two measurable matrix fields with integrable entry-square sums have an integrable entry pairing. (`Breakdown.FracInternal.CellDensityModesBound.pair_integrable`)

**Integrability of model stretching.** This proposition requires the model stretching form to be integrable on each valid cell for admissible fields and 1 < α < 5/4. (`Breakdown.CellCert.CellAnalysis.JFormIntegrableStatement`)

Proved by `Breakdown.CellCert.CellAnalysis.jFormIntegrable`.

**Density integrability from stretching.** Integrability of the model stretching form implies integrability of the full density and pin pairings. (`Breakdown.CellCert.CellAnalysis.densityIntegrable_of`)

### Breakdown.FracCell.CellDensityModesCoupling

This file expands the model stretching coupling in Cartesian entries and proves it is integrable on a cell.

**Expand the model stretching form.** The model stretching form equals the stated coordinate sums involving strain, curl gradient, velocity and gradient entries. (`Breakdown.FracInternal.CellDensityModesCoupling.jForm_eq`)

**Bound a matrix entry.** Every matrix entry's absolute value is at most the operator norm. (`Breakdown.FracInternal.CellDensityModesCoupling.entry_le`)

**Bound the symmetric operator part.** The norm of the symmetric part of a linear map is at most the original operator norm. (`Breakdown.FracInternal.CellDensityModesCoupling.symPart_le`)

**Bound a curl-gradient entry.** Each curl-gradient matrix entry has absolute value at most nine times the second-derivative operator norm. (`Breakdown.FracInternal.CellDensityModesCoupling.entry_curlGradMatrix`)

**Uniform model coefficient bounds.** Valid form data give a uniform bound on all model strain and curl-gradient entries. (`Breakdown.FracInternal.CellDensityModesCoupling.model_bounds`)

**Spatial norm from radius and height.** The spatial norm is at most cylindrical radius plus absolute height. (`Breakdown.FracInternal.CellDensityModesCoupling.norm_le_cyl`)

**Finite volume of a cell solid.** Every cell solid has finite volume. (`Breakdown.FracInternal.CellDensityModesCoupling.solid_finite`)

**Permutation signs have size at most one.** Every permutation sign has absolute value at most one. (`Breakdown.FracInternal.CellDensityModesCoupling.perm_le`)

**Bound a signed coefficient.** Multiplying a coefficient bounded by C by a factor of absolute value at most one keeps its norm at most C. (`Breakdown.FracInternal.CellDensityModesCoupling.coef_le`)

**Integrable model stretching form.** For 1 < α < 5/4, valid form data and a valid cell make the model strain-curl form of every admissible input integrable on the solid cell. (`Breakdown.CellCert.CellAnalysis.jFormIntegrable`)

### Breakdown.FracCell.CellDensityModesMirror

This file checks reflection invariance of the quadratic density terms and states the required weak-gradient reflection law.

**Coordinate signs under reflection.** The reflection sign vector is one on the two planar coordinates and minus one on height. (`Breakdown.FracInternal.CellDensityModesMirror.sgn`)

**Reflect a vector coordinate.** Reflection multiplies each vector coordinate by its corresponding sign. (`Breakdown.FracInternal.CellDensityModesMirror.mirror_apply`)

**Reflection is an involution.** Reflecting a vector twice returns the original vector. (`Breakdown.FracInternal.CellDensityModesMirror.mirror_mirror`)

**Reflection signs square to one.** Every reflection sign multiplied by itself equals one. (`Breakdown.FracInternal.CellDensityModesMirror.sgn_sq`)

**Reflect a coordinate unit vector.** Reflection multiplies a coordinate unit vector by its coordinate sign. (`Breakdown.FracInternal.CellDensityModesMirror.mirror_unit`)

**Apply a matrix by coordinates.** Each coordinate of a matrix applied to a vector is the corresponding matrix-entry sum. (`Breakdown.FracInternal.CellDensityModesMirror.apply_sum`)

**Entries of a reflected matrix.** Conjugating a matrix by reflection multiplies each entry by its row and column signs. (`Breakdown.FracInternal.CellDensityModesMirror.entry_conj`)

**Entries of a negated reflection.** Negated reflection conjugation multiplies a matrix entry by minus its row and column signs. (`Breakdown.FracInternal.CellDensityModesMirror.entry_conj_neg`)

**Vector norm squared by coordinates.** The spatial norm squared is the sum of coordinate squares. (`Breakdown.FracInternal.CellDensityModesMirror.vec_sq`)

**Matrix energy by entries.** The matrix entry energy is the double sum of the squared entries. (`Breakdown.FracInternal.CellDensityModesMirror.entrySq_eq`)

**Inner product by coordinates.** The spatial inner product is the sum of coordinate products. (`Breakdown.FracInternal.CellDensityModesMirror.inner_eq`)

**Curl by permutation signs.** Each curl component is the stated permutation-sign sum of matrix entries. (`Breakdown.FracInternal.CellDensityModesMirror.curl_apply`)

**Reflect a second-derivative tensor.** Reflection conjugation multiplies each tensor coordinate by the three corresponding signs. (`Breakdown.FracInternal.CellDensityModesMirror.second_conj`)

**Reflection preserves matrix energy.** Conjugation by reflection preserves the matrix entry-square sum. (`Breakdown.FracInternal.CellDensityModesMirror.entrySq_mirror`)

**Reflection preserves curl energy.** Conjugation by reflection preserves the squared curl norm. (`Breakdown.FracInternal.CellDensityModesMirror.curl_mirror`)

**Reflection preserves second energy.** The stated tensor reflection preserves the full second-derivative energy. (`Breakdown.FracInternal.CellDensityModesMirror.fullSecond_mirror`)

**Reflected curl-gradient energy.** The stated tensor reflection preserves curl-gradient energy. (`Breakdown.FracInternal.CellDensityModesMirror.curlGrad_mirror`)

**Reflection preserves matrix pairings.** Reflecting both matrices by conjugation preserves their entry pairing. (`Breakdown.FracInternal.CellDensityModesMirror.entryInner_mirror`)

**Reflection preserves model stretching.** The stated reflection laws for strain, curl gradient, gradient and velocity preserve the model stretching form. (`Breakdown.FracInternal.CellDensityModesMirror.jForm_mirror`)

**Zero-height coordinate plane.** The height plane is the linear subspace of vectors whose height coordinate is zero. (`Breakdown.FracInternal.CellDensityModesMirror.heightPlane`)

**Membership in the height plane.** A vector belongs to the height plane exactly when its height coordinate is zero. (`Breakdown.FracInternal.CellDensityModesMirror.mem_heightPlane`)

**The midplane has measure zero.** Almost every spatial point has nonzero cylindrical height. (`Breakdown.FracInternal.CellDensityModesMirror.ae_height_ne`)

**Weak-gradient reflection requirement.** This proposition requires the gradient and second derivative of every second-order field to obey their reflection laws almost everywhere. (`Breakdown.CellCert.CellAnalysis.GradientMirrorStatement`)

Proved by `Breakdown.CellCert.CellAnalysis.gradientMirror`.

**Density reflection from its gradients.** The weak-gradient reflection statement implies reflection invariance of the density and pin pairings. (`Breakdown.CellCert.CellAnalysis.densityMirror_of`)

### Breakdown.FracCell.CellDensityModesParts

This file separates the density-mode conversion into integrability, reflection and circle-slice obligations.

**Integrable density and pin pairings.** For valid form and symmetric cell data with 1 < α < 5/4, this proposition requires integrability of the local density and every pin pairing. (`Breakdown.CellCert.CellAnalysis.DensityIntegrableStatement`)

Proved from further statements by `Breakdown.CellCert.CellAnalysis.densityIntegrable_of`.

**Reflection-invariant cell density.** Under the stated admissibility and cell assumptions, this proposition requires the density and pin pairings to be reflection-invariant almost everywhere. (`Breakdown.CellCert.CellAnalysis.DensityMirrorStatement`)

Proved from further statements by `Breakdown.CellCert.CellAnalysis.densityMirror_of`.

**Circle-slice density formula.** Under the stated cell assumptions, this proposition identifies each angular density integral and pin pairing with 2π times its mode expression almost everywhere. (`Breakdown.CellCert.CellAnalysis.DensitySliceStatement`)

Proved by `Breakdown.CellCert.CellAnalysis.densitySlice_holds`. Also proved from further statements by `Breakdown.CellCert.CellAnalysis.densitySlice_of`.

**Assemble the cell density formula.** Density integrability, reflection invariance and the slice formula express the density and pin integrals as 4π times their radius-weighted modal integrals under the stated exponent, form, cell, symmetry and admissibility conditions. (`Breakdown.CellCert.CellAnalysis.cellDensityModes_of_parts`)

### Breakdown.FracCell.CellDensityModesSolid

This file reduces integrals over a reflected cylindrical cell solid to twice the weighted radial-height integral on its upper half.

**Radius of a cylindrical point.** At nonnegative radius, the cylindrical point has that same radius. (`Breakdown.FracInternal.CellDensityModesSolid.cyl_radius`)

**Height of a cylindrical point.** The height of a cylindrical point is its supplied height coordinate. (`Breakdown.FracInternal.CellDensityModesSolid.cyl_height`)

**Cylindrical evaluation is periodic.** Evaluating any scalar field on a fixed-radius fixed-height circle is 2π-periodic in angle. (`Breakdown.FracInternal.CellDensityModesSolid.cyl_periodic`)

**Zero volume of the midplane.** The plane with zero height coordinate has spatial volume zero. (`Breakdown.FracInternal.CellDensityModesSolid.plane_null`)

**Measurable cell solid.** Every cell solid is measurable. (`Breakdown.FracInternal.CellDensityModesSolid.solid_closed`)

**Reflection reverses height.** Reflection negates the height coordinate. (`Breakdown.FracInternal.CellDensityModesSolid.mirror_two`)

**Reflection preserves radius.** Reflection leaves cylindrical radius unchanged. (`Breakdown.FracInternal.CellDensityModesSolid.mirror_radius`)

**Reflection preserves absolute height.** Reflection leaves absolute cylindrical height unchanged. (`Breakdown.FracInternal.CellDensityModesSolid.mirror_height`)

**Reflect the upper half of the cell.** The inverse image of the positive-height half under reflection is the negative-height part of the cell. (`Breakdown.FracInternal.CellDensityModesSolid.mirror_pre`)

**Adding the midplane changes no measure.** The positive-height and nonnegative-height cell halves agree almost everywhere. (`Breakdown.FracInternal.CellDensityModesSolid.pos_ae`)

**Double a reflection-invariant integral.** An integrable reflection-invariant function on a cell has integral twice its integral over the nonnegative-height half. (`Breakdown.FracInternal.CellDensityModesSolid.half_split`)

**Upper solid membership by coordinates.** At positive radius in a valid cell, membership in the upper solid is equivalent to membership of radius and height in the cell rectangle. (`Breakdown.FracInternal.CellDensityModesSolid.cyl_mem`)

**Measurable radial-height rectangle.** The cell rectangle is measurable. (`Breakdown.FracInternal.CellDensityModesSolid.rect_meas`)

**Shift the angular integration interval.** The angular integral over −π to π equals the integral over zero to 2π. (`Breakdown.FracInternal.CellDensityModesSolid.period_shift`)

**Remove the zero-radius boundary.** Restricting a valid cell rectangle to positive radius changes it only on a null set. (`Breakdown.FracInternal.CellDensityModesSolid.rect_ae`)

**Upper cell integral in cylindrical form.** The integral over the upper cell equals the rectangle integral of radius times the full angular integral. (`Breakdown.FracInternal.CellDensityModesSolid.upper_cyl`)

**Full reflected cell integral.** For an integrable reflection-invariant field, the full cell integral is twice its radius-weighted rectangle and angular integral. (`Breakdown.FracInternal.CellDensityModesSolid.solid_formula`)

### Breakdown.FracCell.CellDensityModesTurn

This file transfers axial rotation symmetry from a weak second-order field to its gradient and second derivative.

**Weak derivative in any direction.** Coordinate weak derivative identities combine into the identity for every fixed spatial direction. (`Breakdown.FracInternal.CellDensityModesTurn.weak_dir`)

**Tests under an inverse isometry.** Composing a scalar test with an inverse linear isometry preserves the test-field conditions. (`Breakdown.FracInternal.CellDensityModesTurn.test_equiv`)

**Derivative of an isometric test.** Differentiating an inverse-isometry test in a transformed direction gives the original directional derivative at the inverse image. (`Breakdown.FracInternal.CellDensityModesTurn.deriv_equiv`)

**Transport weak derivatives by symmetry.** The stated L2 derivative and field-symmetry assumptions transport coordinate weak derivatives through a linear isometry almost everywhere. (`Breakdown.FracInternal.CellDensityModesTurn.weak_equiv`)

**Linear map from coordinate columns.** The coordinate-weighted sum of a linear map's columns equals its value on the vector. (`Breakdown.FracInternal.CellDensityModesTurn.sum_units`)

**Gradient inherits field symmetry.** For a second-order field equivariant under an isometry, its weak gradient obeys the corresponding transformation almost everywhere. (`Breakdown.FracInternal.CellDensityModesTurn.first_turn`)

**Bilinear map from coordinate columns.** A coordinate expansion in the first input of a bilinear map recovers its value on that input. (`Breakdown.FracInternal.CellDensityModesTurn.sum_units2`)

**L2 directional matrix evaluation.** A measurable matrix field with integrable entry energy belongs to L2 after evaluation on any fixed direction. (`Breakdown.FracInternal.CellDensityModesTurn.memLp_dir`)

**L2 second-derivative evaluation.** The measurable tensor-energy hypothesis puts the stated coordinate-direction evaluation in L2. (`Breakdown.FracInternal.CellDensityModesTurn.memLp_dir2`)

**Weak derivative of a fixed column.** For a second-order field, the derivative of a fixed gradient-column combination is the corresponding second-derivative combination in the weak sense. (`Breakdown.FracInternal.CellDensityModesTurn.weak_comb`)

**Second derivative inherits symmetry.** For a second-order equivariant field, its second derivative obeys the corresponding two-input isometry law almost everywhere. (`Breakdown.FracInternal.CellDensityModesTurn.second_turn`)

**Axial-gradient symmetry requirement.** This proposition requires weak gradients and second derivatives to transform under the class rotation step almost everywhere. (`Breakdown.CellCert.CellAnalysis.GradientTurnStatement`)

Proved by `Breakdown.CellCert.CellAnalysis.gradientTurn`.

**Axial symmetry of weak derivatives.** The weak gradient and second derivative of a second-order field transform equivariantly under the discrete turn almost everywhere. (`Breakdown.CellCert.CellAnalysis.gradientTurn`)

### Breakdown.FracCell.CellDensityModesWeak

This file derives the weak-gradient reflection law from field symmetry and uniqueness of weak derivatives.

**Reflection as an isometry equivalence.** The reflection is the function underlying the specified linear isometry equivalence. (`Breakdown.FracInternal.CellDensityModesWeak.mirror_coe`)

**Reflection as a linear isometry.** The reflection is also the function underlying that equivalence's linear isometry. (`Breakdown.FracInternal.CellDensityModesWeak.mirror_coe'`)

**Reflection preserves negation.** Reflecting a negated vector gives the negative of its reflection. (`Breakdown.FracInternal.CellDensityModesWeak.mirror_neg`)

**Reflection is measurably embedded.** Reflection is a measurable embedding of space. (`Breakdown.FracInternal.CellDensityModesWeak.mirror_emb`)

**Reflect a scalar test.** Composing a scalar test with reflection preserves the test-field conditions. (`Breakdown.FracInternal.CellDensityModesWeak.test_comp`)

**Derivative of a reflected test.** Reflecting a test multiplies its coordinate derivative by the corresponding reflection sign. (`Breakdown.FracInternal.CellDensityModesWeak.deriv_comp`)

**Reflect a weak coordinate derivative.** The weak derivative of a field with the stated reflection parity inherits that parity times the coordinate reflection sign almost everywhere. (`Breakdown.FracInternal.CellDensityModesWeak.weak_mirror`)

**Vector coordinate expansion.** Every vector is the sum of its coordinate multiples of standard unit vectors. (`Breakdown.FracInternal.CellDensityModesWeak.vec_expand`)

**Extend matrix reflection from axes.** The reflection law on every coordinate column implies the full conjugation law for the linear map. (`Breakdown.FracInternal.CellDensityModesWeak.lin_from_units`)

**Extend tensor reflection from axes.** The reflection law on coordinate pairs implies the full two-input tensor reflection law. (`Breakdown.FracInternal.CellDensityModesWeak.bilin_from_units`)

**Square-integrable gradient columns.** A measurable matrix field with integrable entry energy has L2 coordinate columns. (`Breakdown.FracInternal.CellDensityModesWeak.memLp_col`)

**Square-integrable tensor columns.** A measurable second-derivative field with finite coordinate energy has L2 coordinate-pair evaluations. (`Breakdown.FracInternal.CellDensityModesWeak.memLp_col2`)

**Reflection law for weak derivatives.** The weak gradient and second derivative of a second-order field transform by reflecting both their input directions and output vector almost everywhere. (`Breakdown.CellCert.CellAnalysis.gradientMirror`)

### Breakdown.FracCell.CellFormBound

This file combines the modal density inequality with a scalar completion of squares to obtain the physical cell-form bound.

**Complete the scalar row square.** For positive row weight and the stated low-row normalization, the displayed linear and penalty terms are bounded by the weighted full row square. (`_private.Breakdown.FracCell.CellFormBound.0.Breakdown.CellCert.CellAnalysis.row_square_step`)

**Cell bound from density and modes.** The density-mode identity and modal bound show that 4π times the cell form is at most its physical split-cell contribution under the stated exponent, form, cell, weight, row-assignment and admissibility conditions. (`Breakdown.CellCert.CellAnalysis.cellFormBound_of_modes`)

**Cell bound with energy interfaces.** The density and modal bounds give the same 4π-scaled cell-form inequality under the stated validity and matching conditions, with the resolved, unresolved and velocity-tail energy interfaces also accepted as hypotheses. (`Breakdown.CellCert.CellAnalysis.cellFormBound_of`)

### Breakdown.FracCell.CellFormBoundSharp

This file completes the symmetric, antisymmetric and velocity squares, splitting near and far charges to pass from the sharp modal estimate to the cell-form bound.

**Complete a complex square.** For positive h, the weighted complex square plus twice the real pairing is bounded below by minus the target square divided by h. (`Breakdown.CellCert.CellAnalysis.CellFormBoundInternal.cpx_complete`)

**Expand a complex sum square.** The norm square of a complex sum is the two squares plus twice the real conjugate pairing. (`Breakdown.CellCert.CellAnalysis.CellFormBoundInternal.cpx_expand`)

**Complex self-pairing is a square.** The real part of a complex number times its conjugate is its norm squared. (`Breakdown.CellCert.CellAnalysis.CellFormBoundInternal.cpx_self`)

**Split a complex square by a share.** For a share strictly between zero and one, the square of a sum is bounded by the two squares divided by their shares. (`Breakdown.CellCert.CellAnalysis.CellFormBoundInternal.cpx_far`)

**Lower bound for the strain penalty.** Positive symmetric and antisymmetric weights bound the strain penalty below by the negative weighted target squares. (`Breakdown.CellCert.CellAnalysis.CellFormBoundInternal.pen_ge`)

**Lower bound for the velocity penalty.** A positive velocity weight bounds the velocity penalty below by minus the target vector square divided by the weight. (`Breakdown.CellCert.CellAnalysis.CellFormBoundInternal.vel_ge`)

**Expand the symmetric sum square.** The symmetric square of a matrix sum expands into its square, twice the symmetric pairing and the added self-pairing. (`Breakdown.CellCert.CellAnalysis.CellFormBoundInternal.symSq_add`)

**Expand the antisymmetric sum square.** The antisymmetric square of a matrix sum expands into its square, twice the antisymmetric pairing and the added self-pairing. (`Breakdown.CellCert.CellAnalysis.CellFormBoundInternal.antiSq_add`)

**Expand the vector sum square.** The vector square of a sum expands into its square, twice the real vector pairing and the added self-pairing. (`Breakdown.CellCert.CellAnalysis.CellFormBoundInternal.vecSq_add`)

**Real part of a weighted matrix pairing.** The real weighted matrix pairing is the sum of its symmetric and antisymmetric real pairings divided by their weights. (`Breakdown.CellCert.CellAnalysis.CellFormBoundInternal.swp_re`)

**Weighted matrix self-pairing.** A weighted matrix self-pairing equals the symmetric and antisymmetric squares divided by their respective weights. (`Breakdown.CellCert.CellAnalysis.CellFormBoundInternal.swp_self`)

**Vector self-pairing.** The real vector self-pairing is the vector square. (`Breakdown.CellCert.CellAnalysis.CellFormBoundInternal.vecPair_self`)

**Complete the near strain square.** Positive strain weights give the stated lower bound after adding an optional row target to the near strain charge. (`Breakdown.CellCert.CellAnalysis.CellFormBoundInternal.strain_near`)

**Complete the near velocity square.** A positive velocity weight gives the stated lower bound after adding the row target to the near velocity charge. (`Breakdown.CellCert.CellAnalysis.CellFormBoundInternal.vel_near`)

**Nonnegative symmetric square.** The symmetric matrix square is nonnegative. (`Breakdown.CellCert.CellAnalysis.CellFormBoundInternal.symSq_nonneg'`)

**Nonnegative antisymmetric square.** The antisymmetric matrix square is nonnegative. (`Breakdown.CellCert.CellAnalysis.CellFormBoundInternal.antiSq_nonneg'`)

**Nonnegative complex vector square.** The complex vector square is nonnegative. (`Breakdown.CellCert.CellAnalysis.CellFormBoundInternal.vecSq_nonneg'`)

**Split the far symmetric square.** A share between zero and one splits the symmetric square of a sum into the two share-weighted squares. (`Breakdown.CellCert.CellAnalysis.CellFormBoundInternal.symSq_far`)

**Split the far antisymmetric square.** A share between zero and one splits the antisymmetric square of a sum into the two share-weighted squares. (`Breakdown.CellCert.CellAnalysis.CellFormBoundInternal.antiSq_far`)

**Split the far vector square.** A share between zero and one splits the vector square of a sum into the two share-weighted squares. (`Breakdown.CellCert.CellAnalysis.CellFormBoundInternal.vecSq_far`)

**Complete the far strain square.** Positive strain weights and a share between zero and one give the displayed lower bound for the far strain penalty with an optional row target. (`Breakdown.CellCert.CellAnalysis.CellFormBoundInternal.strain_far`)

**Complete the far velocity square.** A positive velocity weight and a share between zero and one give the displayed lower bound for the far velocity penalty. (`Breakdown.CellCert.CellAnalysis.CellFormBoundInternal.vel_far`)

**Real linearity of the entry pairing.** The real entry pairing preserves the stated real linear combination in its second input. (`Breakdown.CellCert.CellAnalysis.CellFormBoundInternal.ep_lin`)

**Pair against a finite matrix sum.** The real entry pairing against a finite real-weighted matrix sum equals the weighted sum of the pairings. (`Breakdown.CellCert.CellAnalysis.CellFormBoundInternal.ep_sum`)

**Linear weighted matrix pairing.** The real weighted matrix pairing preserves finite real linear combinations in its first input. (`Breakdown.CellCert.CellAnalysis.CellFormBoundInternal.swp_lin`)

**Linear vector pairing.** The real vector pairing preserves a finite real linear combination in its second input. (`Breakdown.CellCert.CellAnalysis.CellFormBoundInternal.vp_lin`)

**Remove zero terms outside a subset.** A finite sum with a subset indicator equals the sum directly over that subset. (`Breakdown.CellCert.CellAnalysis.CellFormBoundInternal.sum_mem_ite`)

**Positive symmetric tail weight.** Valid cell data give a positive symmetric weight whenever the mode or polynomial index is unresolved. (`Breakdown.CellCert.CellAnalysis.CellFormBoundInternal.sym_pos`)

**Positive antisymmetric tail weight.** Valid cell data give a positive antisymmetric weight whenever the mode or polynomial index is unresolved. (`Breakdown.CellCert.CellAnalysis.CellFormBoundInternal.anti_pos`)

**Positive velocity tail weight.** Valid cell data give a positive velocity weight on resolved modes at or above the stated degree threshold. (`Breakdown.CellCert.CellAnalysis.CellFormBoundInternal.vel_pos`)

**Reorder weighted coefficient sums.** The finite row sum can be moved inside the mode and polynomial-index sums with their selection condition unchanged. (`Breakdown.CellCert.CellAnalysis.CellFormBoundInternal.comm4`)

**Expand the summed row-Y pairing.** The weighted row-Y sum equals the stated matrix and velocity coefficient pairings with the weighted row combination. (`Breakdown.CellCert.CellAnalysis.CellFormBoundInternal.rowY_sum`)

**Near charge bound by sharp penalties.** For valid cell data, the negative near charge, row-Y pairing and row-square terms are bounded by the finite sharp strain and velocity penalties. (`Breakdown.CellCert.CellAnalysis.CellFormBoundInternal.near_bound`)

**Far charge bound by sharp penalties.** For valid cell data and the stated summability assumptions, the share-weighted far charges are bounded by the sum of sharp far penalties. (`Breakdown.CellCert.CellAnalysis.CellFormBoundInternal.far_bound'`)

**Modal bound from the sharp estimate.** The sharp cell estimate bounds the local form after its near, far and row penalties by the modal density integral and pin and high-row pairings for valid form and cell data, an axisymmetric weight, admissible inputs and row-supported multipliers. (`Breakdown.CellCert.CellAnalysis.cellModeBound_of_sharp`)

**Cell-form bound from the sharp estimate.** The density-mode identity and sharp cell estimate imply the cell-form bound. (`Breakdown.CellCert.CellAnalysis.cellFormBound_of_sharp`)

### Breakdown.FracCell.CellFormBoundSharpSt

This file defines the completed-square penalties and states the sharp modal inequality before those squares are eliminated.

**Strain completion penalty.** The strain penalty combines weighted symmetric and antisymmetric input squares with twice their real target pairings. (`Breakdown.CellCert.CellAnalysis.strainPen`)

**Velocity completion penalty.** The velocity penalty is the weighted vector square plus twice its real target pairing. (`Breakdown.CellCert.CellAnalysis.velPen`)

**Target strain coefficients.** The target strain coefficient combines the folded Y coefficient with the row-coupling combination on the selected mode band. (`Breakdown.CellCert.CellAnalysis.CellScalars.targetStrain`)

**Target velocity coefficients.** The target velocity coefficient is the Y velocity coefficient plus the weighted row-coupling coefficients. (`Breakdown.CellCert.CellAnalysis.CellScalars.targetVelocity`)

**Selected sharp strain penalty.** The sharp strain term applies the strain penalty on unresolved modes or polynomial indices above the high-degree threshold, and is zero elsewhere. (`Breakdown.CellCert.CellAnalysis.CellScalars.sharpStrainTerm`)

**Selected sharp velocity penalty.** The sharp velocity term applies the velocity penalty at or above the high-degree threshold, and is zero elsewhere. (`Breakdown.CellCert.CellAnalysis.CellScalars.sharpVelocityTerm`)

**Sharp far-coefficient contribution.** Beyond the near-degree threshold, the sharp far term sums the strain and resolved velocity penalties. (`Breakdown.CellCert.CellAnalysis.CellScalars.sharpFarTerm`)

**Full sharp coefficient form.** The sharp form combines the finite near strain and velocity sums with the infinite far contribution. (`Breakdown.CellCert.CellAnalysis.CellScalars.sharpForm`)

**Sharp modal cell-bound requirement.** This proposition requires summable coefficient penalties whose local-form inequality controls the modal density, pin pairings and high-row coupling under the stated admissible cell hypotheses. (`Breakdown.CellCert.CellAnalysis.CellSharpBoundStatement`)

Proved from further statements by `Breakdown.CellCert.CellAnalysis.cellSharpBound_of_leaves`, `Breakdown.CellCert.CellAnalysis.cellSharpBound_of_open`, `Breakdown.CellCert.CellAnalysis.cellSharpBound_of_modes`, `Breakdown.CellCert.CellAnalysis.cellSharpBound_of_remaining`, `Breakdown.CellCert.CellAnalysis.cellSharpBound_of`.

### Breakdown.FracCell.CellFormBoundSt

This file states the modal lower bound obtained after completing the coefficient squares and accounting for the row charges.

**Modal lower bound with all charges.** For valid admissible cell data with 1 < α < 5/4, this proposition bounds the local form minus near, far and row charges by the modal density and the stated pin and high-row pairings. (`Breakdown.CellCert.CellAnalysis.CellModeBoundStatement`)

Proved from further statements by `Breakdown.CellCert.CellAnalysis.cellModeBound_of_sharp`.

### Breakdown.FracCell.CellMatrixBound

This file passes from a finite cell matrix to the analytic cell form, using the canonical input, scaling and gauge identities needed by the certificate argument.

**Read a scaled system coordinate.** For a selected coordinate with the specified skeleton and interior values, the assembled system vector equals the supplied value divided by its datum scale. (`_private.Breakdown.FracCell.CellMatrixBound.0.Breakdown.CellCert.CellCoordinates.systemVector_eq_of_mem`)

**Expansion commutes with scaling.** Conjugation closure of the selected coordinates and conjugation invariance of the scale make system expansion commute with division by that scale. (`_private.Breakdown.FracCell.CellMatrixBound.0.Breakdown.CellCert.CellCoordinates.expandSystem_div_of_mem`)

**Conjugation preserves preset scale.** Conjugating a datum leaves its preset scale unchanged. (`_private.Breakdown.FracCell.CellMatrixBound.0.Breakdown.CellCert.CellCoordinates.presetScale_conj`)

**Preset scales do not vanish.** Positive viscosity makes every preset scale nonzero. (`_private.Breakdown.FracCell.CellMatrixBound.0.Breakdown.CellCert.CellCoordinates.presetScale_ne`)

**Cell matrix below scaled cell form.** The exact formula, canonical input, real reduction and gauge statements bound the assembled cell matrix by 4π times the cell form when 1 < α < 5/4 and the form, coordinates, matching and conjugation hypotheses hold. (`Breakdown.CellCert.CellCoordinates.cellMatrix_le_cellForm_of_parts`)

### Breakdown.FracCell.CellSharpBound

This file proves the sharper cell estimate from weighted modal orthogonality and complete-square bounds, including the summability required for the far-mode penalties.

**Continuous radial weight.** The radial line weight is continuous. (`Breakdown.CellCert.CellAnalysis.CellSharpBoundInternal.lw_cont`)

**Nonnegative radial weight.** The radial line weight is nonnegative at radii at least the inner radius. (`Breakdown.CellCert.CellAnalysis.CellSharpBoundInternal.lw_nonneg`)

**Continuous radial polynomials.** Every radial basis polynomial is continuous. (`Breakdown.CellCert.CellAnalysis.CellSharpBoundInternal.rp_cont`)

**Continuous height polynomials.** Every height basis polynomial is continuous. (`Breakdown.CellCert.CellAnalysis.CellSharpBoundInternal.hp_cont`)

**Product basis on the rectangle.** A rectangle basis function is the product of its radial and height basis polynomials. (`Breakdown.CellCert.CellAnalysis.CellSharpBoundInternal.bas`)

**Continuous product basis.** Every rectangle product basis function is continuous. (`Breakdown.CellCert.CellAnalysis.CellSharpBoundInternal.bas_cont`)

**Measurable cell rectangle.** The cell rectangle is measurable. (`Breakdown.CellCert.CellAnalysis.CellSharpBoundInternal.rect_meas`)

**Compact cell rectangle.** The cell rectangle is compact. (`Breakdown.CellCert.CellAnalysis.CellSharpBoundInternal.rect_cpt`)

**Weighted basis orthogonality.** For valid cell bases, the weighted integral of two rectangle basis functions is one for equal indices and zero otherwise. (`Breakdown.CellCert.CellAnalysis.CellSharpBoundInternal.orth`)

**Integrable basis products.** The radial weight times any two rectangle basis functions is integrable on the cell rectangle. (`Breakdown.CellCert.CellAnalysis.CellSharpBoundInternal.wbb_int`)

**Integrable weighted coefficients.** A measurable function with finite weighted square integral has integrable products with the weighted rectangle basis functions. (`Breakdown.CellCert.CellAnalysis.CellSharpBoundInternal.g_int`)

**Complex square as a conjugate product.** The squared norm of a complex number is the real part of its product with its conjugate. (`Breakdown.CellCert.CellAnalysis.CellSharpBoundInternal.sqn`)

**Expand the weighted square.** The weighted square of a function minus a finite basis expansion equals the stated function square, cross term and expansion square. (`Breakdown.CellCert.CellAnalysis.CellSharpBoundInternal.pt_id`)

**Finite coefficient energy bound.** For valid cell bases and a measurable function with finite weighted square integral, the sum of squared coefficients over a finite set is at most that integral. (`Breakdown.CellCert.CellAnalysis.CellSharpBoundInternal.coefEnergy_fin`)

**Summable squared coefficients.** For valid cell bases and a measurable function with finite weighted square integral, the squared rectangle coefficients are summable. (`Breakdown.CellCert.CellAnalysis.CellSharpBoundInternal.coef_summable`)

**Nonnegative symmetric square.** The squared symmetric part of a matrix is nonnegative. (`Breakdown.CellCert.CellAnalysis.CellSharpBoundInternal.symSq_nonneg'`)

**Nonnegative antisymmetric square.** The squared antisymmetric part of a matrix is nonnegative. (`Breakdown.CellCert.CellAnalysis.CellSharpBoundInternal.antiSq_nonneg'`)

**Nonnegative vector square.** The squared vector quantity is nonnegative. (`Breakdown.CellCert.CellAnalysis.CellSharpBoundInternal.vecSq_nonneg'`)

**Self-pairing equals entry squares.** The real part of a matrix paired with itself equals the sum of the squared norms of its entries. (`Breakdown.CellCert.CellAnalysis.CellSharpBoundInternal.ep_self`)

**Weighted matrix self-pairing.** The weighted self-pairing equals the symmetric square divided by the symmetric weight plus the antisymmetric square divided by the antisymmetric weight. (`Breakdown.CellCert.CellAnalysis.CellSharpBoundInternal.swp_self`)

**Positive far symmetric weights.** Valid cell data give positive symmetric weights at every unresolved mode or sufficiently high polynomial index. (`Breakdown.CellCert.CellAnalysis.CellSharpBoundInternal.sym_pos`)

**Positive far antisymmetric weights.** Valid cell data give positive antisymmetric weights at every unresolved mode or sufficiently high polynomial index. (`Breakdown.CellCert.CellAnalysis.CellSharpBoundInternal.anti_pos`)

**Positive high velocity weights.** Valid cell data give positive velocity weights at resolved modes and sufficiently high polynomial indices. (`Breakdown.CellCert.CellAnalysis.CellSharpBoundInternal.vel_pos`)

**Square of an average.** The squared norm of half the sum of two complex numbers is at most half the sum of their squared norms. (`Breakdown.CellCert.CellAnalysis.CellSharpBoundInternal.half_add`)

**Square of a half difference.** The squared norm of half the difference of two complex numbers is at most half the sum of their squared norms. (`Breakdown.CellCert.CellAnalysis.CellSharpBoundInternal.half_sub`)

**Sum after exchanging matrix indices.** Summing the average of the squared entries at two transposed indices gives the original sum of squared entries. (`Breakdown.CellCert.CellAnalysis.CellSharpBoundInternal.swap_avg`)

**Bound the symmetric square.** The squared symmetric part of a matrix is at most the sum of its squared entry norms. (`Breakdown.CellCert.CellAnalysis.CellSharpBoundInternal.symSq_le`)

**Bound the antisymmetric square.** The squared antisymmetric part of a matrix is at most the sum of its squared entry norms. (`Breakdown.CellCert.CellAnalysis.CellSharpBoundInternal.antiSq_le`)

**Nonnegative sum of entry squares.** The sum of squared matrix entry norms is nonnegative. (`Breakdown.CellCert.CellAnalysis.CellSharpBoundInternal.sumSq_nn`)

**Square of a finite weighted sum.** The squared norm of a finite real weighted complex sum is at most the number of terms times the sum of the weighted squared norms. (`Breakdown.CellCert.CellAnalysis.CellSharpBoundInternal.sumInner_sq`)

**Summable matrix entry squares.** Summability of each entry square gives summability of the total matrix square. (`Breakdown.CellCert.CellAnalysis.CellSharpBoundInternal.sumSq_summable`)

**Summable vector entry squares.** Summability of each vector entry square gives summability of the total vector square. (`Breakdown.CellCert.CellAnalysis.CellSharpBoundInternal.vecSq_summable`)

**Summable weighted matrix sums.** Finite real weighted combinations of matrix sequences with summable entry squares retain summable total squares. (`Breakdown.CellCert.CellAnalysis.CellSharpBoundInternal.combo_summable`)

**Summable weighted vector sums.** Finite real weighted combinations of vector sequences with summable entry squares retain summable vector squares. (`Breakdown.CellCert.CellAnalysis.CellSharpBoundInternal.combo_vec_summable`)

**Bound the far matrix charge.** Positive uniform weight floors bound the unresolved or high matrix charge by twice the matrix square divided by the weight floor. (`Breakdown.CellCert.CellAnalysis.CellSharpBoundInternal.pair_bound`)

**Nonnegative far matrix charge.** Positive symmetric and antisymmetric weights make the matrix charge nonnegative. (`Breakdown.CellCert.CellAnalysis.CellSharpBoundInternal.pair_nonneg`)

**Bound the high velocity charge.** A positive uniform velocity weight floor bounds the high velocity charge by the vector square divided by that floor. (`Breakdown.CellCert.CellAnalysis.CellSharpBoundInternal.vel_bound`)

**Summable far target charges.** Square summability of the target matrix modes and positive weight floors give summability of their selected far charges. (`Breakdown.CellCert.CellAnalysis.CellSharpBoundInternal.far_y`)

**Summable far row charges.** Square summability of the row matrix and velocity modes and positive weight floors give summability of the combined far row charges. (`Breakdown.CellCert.CellAnalysis.CellSharpBoundInternal.far_row`)

**Lower complex square bound.** For a positive weight, the complete-square identity gives the stated lower bound for a complex quadratic expression. (`Breakdown.CellCert.CellAnalysis.CellSharpBoundInternal.cc`)

**Upper complex cross-term bound.** For a positive weight, twice the real complex pairing is at most the weighted square of one factor plus the inverse-weighted square of the other. (`Breakdown.CellCert.CellAnalysis.CellSharpBoundInternal.cc'`)

**Lower strain penalty bound.** Positive symmetric and antisymmetric weights give the stated lower bound on the strain penalty. (`Breakdown.CellCert.CellAnalysis.CellSharpBoundInternal.pen_lo`)

**Upper strain penalty bound.** Positive symmetric and antisymmetric weights bound the strain penalty above by twice the weighted strain square plus the inverse-weighted target square. (`Breakdown.CellCert.CellAnalysis.CellSharpBoundInternal.pen_hi`)

**Lower velocity penalty bound.** A positive velocity weight gives the stated lower bound on the velocity penalty. (`Breakdown.CellCert.CellAnalysis.CellSharpBoundInternal.vpen_lo`)

**Upper velocity penalty bound.** A positive velocity weight bounds the velocity penalty above by twice the weighted velocity square plus the inverse-weighted target square. (`Breakdown.CellCert.CellAnalysis.CellSharpBoundInternal.vpen_hi`)

**Square of a sum.** The squared norm of a sum is at most twice the sum of the two squared norms. (`Breakdown.CellCert.CellAnalysis.CellSharpBoundInternal.sq_add_le`)

**Symmetric square of a sum.** The symmetric square of a matrix sum is at most twice the sum of the two symmetric squares. (`Breakdown.CellCert.CellAnalysis.CellSharpBoundInternal.symSq_add_le`)

**Antisymmetric square of a sum.** The antisymmetric square of a matrix sum is at most twice the sum of the two antisymmetric squares. (`Breakdown.CellCert.CellAnalysis.CellSharpBoundInternal.antiSq_add_le`)

**Vector square of a sum.** The vector square of a sum is at most twice the sum of the two vector squares. (`Breakdown.CellCert.CellAnalysis.CellSharpBoundInternal.vecSq_add_le`)

**Absolute strain penalty bound.** With positive weights, the absolute strain penalty for a target split into its base and conditional row terms is bounded by the stated weighted strain and target squares. (`Breakdown.CellCert.CellAnalysis.CellSharpBoundInternal.strain_abs`)

**Absolute velocity penalty bound.** With positive weight, the absolute velocity penalty for a target split into its base and conditional row terms is bounded by the stated weighted velocity and target squares. (`Breakdown.CellCert.CellAnalysis.CellSharpBoundInternal.vel_abs`)

**Summable sharp far penalties.** Valid cell data, the target decompositions and the stated summable mode energies and charges make the sharp far penalties summable. (`Breakdown.CellCert.CellAnalysis.CellSharpBoundInternal.far_a`)

**Sharp cell bound from modal parts.** The weighted target-square and sharp modal-core statements together imply the sharp cell bound. (`Breakdown.CellCert.CellAnalysis.cellSharpBound_of`)

### Breakdown.FracCell.CellSharpBoundSt

This file states the weighted square integrability and modal-core interfaces used to prove the sharp cell estimate; the declarations specify obligations rather than discharging them.

**Weighted square integrability.** A function has a weighted square on a cell when it is almost everywhere measurable there and its radial-weighted squared norm is integrable. (`Breakdown.CellCert.CellAnalysis.IsWeightedSquareOn`)

**Weighted target-square requirement.** For 1 < α < 5/4, valid cell data and admissible inputs must give weighted square integrability of the specified folded, velocity and row-coupling targets on their selected mode sets. (`Breakdown.CellCert.CellAnalysis.SharpTargetSquareStatement`)

Proved by `Breakdown.CellCert.CellAnalysis.sharpTargetSquare`.

**Sharp modal core requirement.** For 1 < α < 5/4, valid cell data, admissible inputs and row-supported multipliers must admit modal strain and velocity arrays with summable far energy satisfying the stated sharp cell inequality. (`Breakdown.CellCert.CellAnalysis.SharpCoreStatement`)

Proved from further statements by `Breakdown.CellCert.CellAnalysis.sharpCore_of`, `Breakdown.CellCert.CellAnalysis.sharpCore_of_parts`, `Breakdown.CellCert.CellAnalysis.sharpCore_of_leaves`.

### Breakdown.FracCell.CellSystemDefs

This file supplies the intermediate symmetry and adjoint-duality structures used when converting finite cell-system data into an analytic certificate.

**Row turning data from a mesh.** The construction takes row partners, angular modes and cell assignments from the row data, using an empty cell and zero radius for indices outside the mesh. (`Breakdown.CellCert.CellSystem.turnOf`)

**Integrable symmetric weight.** A sum weight is a measurable nonnegative integrable function invariant under the specified discrete turn and even under reflection. (`Breakdown.CellCert.CellSystem.IsSumWeight`)

**Adjoint dual analytic conditions.** The adjoint dual structure requires the specified weak derivatives, square integrability, pin and pressure regularity, decaying shifts and remainder decomposition for the chosen adjoint data. (`Breakdown.CellCert.CellSystem.IsAdjointDualStructure`)

**Assemble adjoint dual validity.** The numerical and analytic adjoint dual conditions together establish full adjoint dual validity. (`Breakdown.CellCert.CellSystem.isAdjointDual_of_parts`)

**Weight from the adjoint square.** The adjoint weight is the squared adjoint norm divided by the supplied scalar weight. (`Breakdown.CellCert.CellSystem.adjointWeightOf`)

### Breakdown.FracCell.CellSystemFinalDefs

This file states the analytic obligations needed to turn a valid finite cell system into the final fractional certificate, separating profile, geometry, row, kernel and adjoint conditions.

**Continuous rotation rate requirement.** Valid profile data and their certificate instance must give a rotation rate continuous on the parameter box. (`Breakdown.CellCert.FinalCellSystem.RotationRateContinuousOfStatement`)

Proved by `Breakdown.CellCert.FinalCellSystem.rotationRateContinuousOf_holds`.

**Continuous multiplier requirement.** Valid profile data and their certificate instance must give a multiplier continuous on the parameter box. (`Breakdown.CellCert.FinalCellSystem.MultiplierContinuousOfStatement`)

Proved by `Breakdown.CellCert.FinalCellSystem.multiplierContinuousOf_holds`.

**Smooth profile requirement.** Valid profile data and their certificate instance must give a continuously differentiable profile at every parameter in the box. (`Breakdown.CellCert.FinalCellSystem.ProfileSmoothOfStatement`)

Proved by `Breakdown.CellCert.FinalCellSystem.profileSmoothOf_holds`.

**Weak profile derivative requirement.** Valid profile data and their certificate instance must supply an almost everywhere strongly measurable weak second derivative at every parameter in the box. (`Breakdown.CellCert.FinalCellSystem.ProfileSecondOfStatement`)

Proved by `Breakdown.CellCert.FinalCellSystem.profileSecondOf_holds`.

**Solenoidal profile requirement.** Valid profile data and their certificate instance must give zero profile divergence at every parameter in the box. (`Breakdown.CellCert.FinalCellSystem.ProfileDivergenceOfStatement`)

Proved by `Breakdown.CellCert.FinalCellSystem.profileDivergenceOf_holds`.

**Profile symmetry requirement.** Valid profile data and their certificate instance must give a profile in the specified symmetry class at every parameter in the box. (`Breakdown.CellCert.FinalCellSystem.ProfileClassOfStatement`)

Proved by `Breakdown.CellCert.FinalCellSystem.profileClassOf_holds`.

**Uniform profile decay requirement.** Valid profile data and their certificate instance must give a common bound with inverse first, second and third powers of 1 plus radius for the profile and its first two derivatives. (`Breakdown.CellCert.FinalCellSystem.ProfileBoundsOfStatement`)

Proved by `Breakdown.CellCert.FinalCellSystem.profileBoundsOf_holds`.

**Square integrable profile drift.** At the exponent specified by valid profile data, the instantiated profile drift must be square integrable for every parameter in the box. (`Breakdown.CellCert.FinalCellSystem.ProfileDriftOfStatement`)

Proved by `Breakdown.CellCert.FinalCellSystem.profileDriftOf_holds`.

**Weak fractional profile power.** At the exponent specified by valid profile data, the instantiated profile power must be its weak fractional power for every parameter in the box. (`Breakdown.CellCert.FinalCellSystem.ProfilePowerOfStatement`)

Proved by `Breakdown.CellCert.FinalCellSystem.profilePowerOf_holds`.

**Continuous profile energy requirement.** Valid profile data and their certificate instance must give parameter continuity of the profile gradient in squared integral norm on the parameter box. (`Breakdown.CellCert.FinalCellSystem.ProfileContinuousOfStatement`)

Proved by `Breakdown.CellCert.FinalCellSystem.profileContinuousOf_holds`.

**Smooth centre requirement.** Valid profile data and their centre instance must give a continuously differentiable centre field. (`Breakdown.CellCert.FinalCellSystem.CentreSmoothOfStatement`)

Proved by `Breakdown.CellCert.FinalCellSystem.centreSmoothOf_holds`.

**Weak centre derivative requirement.** Valid profile data and their centre instance must supply an almost everywhere strongly measurable weak second derivative of the centre. (`Breakdown.CellCert.FinalCellSystem.CentreSecondOfStatement`)

Proved by `Breakdown.CellCert.FinalCellSystem.centreSecondOf_holds`.

**Solenoidal centre requirement.** Valid profile data and their centre instance must give zero centre divergence. (`Breakdown.CellCert.FinalCellSystem.CentreDivergenceOfStatement`)

Proved by `Breakdown.CellCert.FinalCellSystem.centreDivergenceOf_holds`.

**Centre symmetry requirement.** Valid profile data and their centre instance must put the centre in the specified symmetry class. (`Breakdown.CellCert.FinalCellSystem.CentreClassOfStatement`)

Proved by `Breakdown.CellCert.FinalCellSystem.centreClassOf_holds`.

**Centre decay requirement.** Valid profile data and their centre instance must bound the centre and its first two derivatives by inverse first, second and third powers of 1 plus radius. (`Breakdown.CellCert.FinalCellSystem.CentreBoundsOfStatement`)

Proved by `Breakdown.CellCert.FinalCellSystem.centreBoundsOf_holds`.

**Symmetric centre second derivative.** Valid profile data and their centre instance must give a centre second derivative symmetric in its two directions. (`Breakdown.CellCert.FinalCellSystem.CentreSecondSymmOfStatement`)

Proved by `Breakdown.CellCert.FinalCellSystem.centreSecondSymmOf_holds`.

**Trace-free centre curl gradient.** Valid profile data and their centre instance must give a centre curl gradient with zero trace. (`Breakdown.CellCert.FinalCellSystem.CentreTraceFreeOfStatement`)

Proved by `Breakdown.CellCert.FinalCellSystem.centreTraceFreeOf_holds`.

**Actuator regularity from chart data.** Valid chart and auxiliary data must give square integrable actuators in the required symmetry class when the certificate actuators and order match them. (`Breakdown.CellCert.FinalCellSystem.ActuatorOfGivenStatement`)

Proved by `Breakdown.CellCert.FinalCellSystem.actuatorOfGiven_holds`.

**Weak actuator gradient requirement.** Valid chart and auxiliary data must give each actuator its classical derivative as a measurable weak gradient with finite squared integral. (`Breakdown.CellCert.FinalCellSystem.ActuatorGradientOfGivenStatement`)

Proved by `Breakdown.CellCert.FinalCellSystem.actuatorGradientOfGiven_holds`.

**Actuator support requirement.** For valid chart and auxiliary data, every actuator must vanish outside any region containing the chart support range. (`Breakdown.CellCert.FinalCellSystem.ActuatorSupportOfGivenStatement`)

Proved by `Breakdown.CellCert.FinalCellSystem.actuatorSupportOfGiven_holds`.

**Smooth pin regularity requirement.** Valid chart and auxiliary data must give measurable finite-energy smooth pins and compactly supported continuously differentiable pin potentials with bounded measurable weak second derivatives. (`Breakdown.CellCert.FinalCellSystem.SmoothPinOfGivenStatement`)

Proved by `Breakdown.CellCert.FinalCellSystem.smoothPinOfGiven_holds`.

**Solenoidal adjoint requirement.** For matching certificate fields and order, valid chart and auxiliary data must give active adjoints that are solenoidal, square integrable and in the required symmetry class, with square integrable sharp fields. (`Breakdown.CellCert.FinalCellSystem.AdjointSolenoidalOfGivenStatement`)

Proved by `Breakdown.CellCert.FinalCellSystem.adjointSolenoidalOfGiven_holds`.

**Adjoint derivative requirement.** Valid chart and auxiliary data must give every adjoint the stated regularity with its classical first and second derivatives. (`Breakdown.CellCert.FinalCellSystem.AdjointRegularOfGivenStatement`)

Proved by `Breakdown.CellCert.FinalCellSystem.adjointRegularOfGiven_holds`.

**Adjoint dual core requirement.** Valid chart and auxiliary data must give the adjoint and sharp fields the stated measurable weak gradients, finite energies and weighted weak negative trace. (`Breakdown.CellCert.FinalCellSystem.AdjointDualCoreOfGivenStatement`)

Proved by `Breakdown.CellCert.FinalCellSystem.adjointDualCoreOfGiven_holds`.

**Enclose the chart support.** A region containing the closed ball of radius R must contain the chart support whenever valid chart and auxiliary data put its support radius at most R. (`Breakdown.CellCert.FinalCellSystem.SupportRegionOfStatement`)

Proved by `Breakdown.CellCert.FinalCellSystem.supportRegionOf_holds`.

**Cell region geometry requirement.** A valid mesh whose region equals the certificate cell region must make that region measurable, bounded and invariant under the specified turn and reflection. (`Breakdown.CellCert.FinalCellSystem.CellRegionClausesStatement`)

Proved by `Breakdown.CellCert.FinalCellSystem.cellRegionClauses_holds`.

**Model field clauses.** Valid mesh and model data, a matching model instance and a regular centre must give measurable bounded model fields with the stated exterior values, symmetric strain and trace-free curl gradient. (`Breakdown.CellCert.FinalCellSystem.ModelClausesStatement`)

Proved by `Breakdown.CellCert.FinalCellSystem.modelClauses_holds`.

**Model auxiliary field clauses.** A valid mesh and matching model instance must give square integrable model actuators and finite-energy measurable actuator gradients and pin fields with the stated support in the cell region. (`Breakdown.CellCert.FinalCellSystem.ModelAuxClausesStatement`)

Proved by `Breakdown.CellCert.FinalCellSystem.modelAuxClauses_holds`.

**Row and cell weight clauses.** Valid mesh and row data with matching instance and positive symmetry order must give orthonormal square integrable supported symmetric rows, bounded positive row weights and a cell weight dominating the row functional. (`Breakdown.CellCert.FinalCellSystem.RowClausesStatement`)

Proved by `Breakdown.CellCert.FinalCellSystem.rowClauses_holds`.

**Constant weight clauses.** A positive constant weight with matching lower and upper bounds must satisfy the measurable, bounded, symmetry and cylindrical sampling requirements. (`Breakdown.CellCert.FinalCellSystem.WeightClausesStatement`)

Proved by `Breakdown.CellCert.FinalCellSystem.weightClauses_holds`.

**Exterior radius clauses.** A valid mesh and the specified box radius must give a positive bounded measurable homogeneous exterior radius whose exterior agrees almost everywhere with the complement of the cell region. (`Breakdown.CellCert.FinalCellSystem.ExteriorClausesStatement`)

Proved by `Breakdown.CellCert.FinalCellSystem.exteriorClauses_holds`.

**Ball inside the mesh region.** Every valid cell mesh must contain the closed ball with radius equal to its outer size. (`Breakdown.CellCert.FinalCellSystem.BallSubsetRegionStatement`)

Proved by `Breakdown.CellCert.FinalCellSystem.ballSubsetRegion_holds`.

**Rows supported in their assigned cell.** Valid mesh and row data with a matching cell-row instance must make each selected row vanish outside that cell. (`Breakdown.CellCert.FinalCellSystem.RowsInCellOfStatement`)

Proved by `Breakdown.CellCert.FinalCellSystem.rowsInCellOf_holds`.

**Row mode support requirement.** For valid mesh and row data, a matching cell-row instance and positive symmetry order, selected row modes must vanish outside the declared row-mode set on the cell rectangle. (`Breakdown.CellCert.FinalCellSystem.RowModesOfStatement`)

No theorem in the library states this proposition as its result.

**Two-mode row support requirement.** For valid mesh and row data, a matching cell-row instance and positive symmetry order, each selected row mode must vanish except at its assigned mode and its negative. (`Breakdown.CellCert.FinalCellSystem.RowModeOfOfStatement`)

No theorem in the library states this proposition as its result.

**Polynomial row trace requirement.** Valid mesh and row data, a matching cell-row instance and a pressure layout of sufficient side degree must give polynomial component traces on every layout segment. (`Breakdown.CellCert.FinalCellSystem.RowTracesOfStatement`)

Proved by `Breakdown.CellCert.FinalCellSystem.rowTracesOf_holds`.

**Polynomial normal trace requirement.** Valid mesh and row data, a matching cell-row instance and a pressure layout of sufficient side degree must give the stated lower-degree polynomial normal traces on pressure segments. (`Breakdown.CellCert.FinalCellSystem.RowNormalTracesOfStatement`)

Proved by `Breakdown.CellCert.FinalCellSystem.rowNormalTracesOf_holds`.

**Row block support requirement.** Valid mesh and row data with a matching row instance must put each row in its assigned spectral block. (`Breakdown.CellCert.FinalCellSystem.RowsInBlockOfStatement`)

Proved by `Breakdown.CellCert.FinalCellSystem.rowsInBlockOf_holds`.

**Base analytic certificate conditions.** The base conditions require bounded positive symmetric weights, continuous parameters, regular decaying solenoidal profiles, suitable actuators and pins, orthonormal supported rows and active solenoidal adjoints. (`Breakdown.CellCert.FinalCellSystem.IsGivenBase`)

**Cell analytic certificate conditions.** The cell conditions require symmetric bounded cell geometry, controlled row weights, a regular decaying centre, model and auxiliary field regularity, and the specified support and weak actuator gradients. (`Breakdown.CellCert.FinalCellSystem.IsGivenCell`)

**Exterior analytic conditions.** The exterior conditions require a measurable positive bounded homogeneous radius describing the exterior almost everywhere and a trace-free centre curl gradient there. (`Breakdown.CellCert.FinalCellSystem.IsGivenExterior`)

**Additional regularity conditions.** The additional conditions require measurable active adjoints, differentiable solenoidal decaying profiles and regular active adjoints with their classical derivatives. (`Breakdown.CellCert.FinalCellSystem.IsGivenExtra`)

**Kernel bound from cell sums.** Valid cell-sum data and a common upper bound on all box bounds must imply the corresponding global kernel bound. (`Breakdown.CellCert.FinalCellSystem.KernelBoundOfCellSumsStatement`)

Proved by `Breakdown.CellCert.FinalCellSystem.kernelBoundOfCellSums_holds`.

**Local adjoint bound from dual data.** For 1 < α < 5/4, valid weighted profile and adjoint hypotheses, an inverse-square constant and the stated dual numerical bound must control the local adjoint pairing for every admissible second-order test field with weak fractional power and square integrable drift. (`Breakdown.CellCert.FinalCellSystem.AdjointLocalOfDualStatement`)

Proved by `Breakdown.CellCert.FinalCellSystem.adjointLocalOfDual_holds`.

**Cell validity from a system.** The cell-system condition must give valid cell data and coordinates at exponent 501/500 for every cell and identify each row assignment with membership in the cell row set. (`Breakdown.CellCert.FinalCellSystem.CellOfSystemStatement`)

Proved from further statements by `Breakdown.CellCert.FinalCellSystem.cellOfSystem_of_rest`.

**Geometry of the cell split.** The cell-system condition must make the split cells measurable, disjoint up to null sets, exhaustive of the cell region and supportive of their assigned rows. (`Breakdown.CellCert.FinalCellSystem.SplitGeometryStatement`)

Proved from further statements by `Breakdown.CellCert.FinalCellSystem.splitGeometry_of`.

**Remaining analytic cell conditions.** The remaining cell conditions package the multiplier estimate, valid box and bases, model symmetry and regularity, row support and mode restrictions, class coverage and far-field bound. (`Breakdown.CellCert.FinalCellSystem.CellDataRest`)

**Remaining coordinate conditions.** The remaining coordinate conditions require positive viscosity, row shape, a valid linear gauge with its jump and roots, and the scaled skeleton moment identity. (`Breakdown.CellCert.FinalCellSystem.CellCoordsRest`)

**Remaining cell conditions from system.** The cell-system condition must imply the remaining analytic cell conditions at exponent 501/500 for every cell. (`Breakdown.CellCert.FinalCellSystem.CellDataRestStatement`)

Proved from further statements by `Breakdown.CellCert.FinalCellSystem.cellDataRest_of_groups`.

**Remaining coordinates from system.** The cell-system condition must imply the remaining coordinate conditions at exponent 501/500 for every cell. (`Breakdown.CellCert.FinalCellSystem.CellCoordsRestStatement`)

Proved from further statements by `Breakdown.CellCert.FinalCellSystem.cellCoordsRest_of`.

**Identify a cell row set.** The cell-system condition must identify assignment to a given split cell exactly with membership in that cell row set. (`Breakdown.CellCert.FinalCellSystem.RowsHereStatement`)

Proved by `Breakdown.CellCert.FinalCellSystem.rowsHere_holds`.

**Basic box and basis conditions.** The basic cell part requires a valid box, valid cell scalars and valid bases. (`Breakdown.CellCert.FinalCellSystem.CellDataBoxPart`)

**Basic cell data from a system.** The cell-system condition must give the basic box, scalar and basis conditions at exponent 501/500 for every cell. (`Breakdown.CellCert.FinalCellSystem.CellDataBoxStatement`)

Proved by `Breakdown.CellCert.FinalCellSystem.cellDataBox_holds`.

**Model conditions inside a cell.** The model part requires an axisymmetric weight, the specified mirror laws, cell inclusion, symmetric strain, trace-free curl gradient, regular classes and restricted linear modes. (`Breakdown.CellCert.FinalCellSystem.CellDataModelPart`)

**Cell model data from a system.** The cell-system condition must give the model part of the cell conditions at exponent 501/500 for every cell. (`Breakdown.CellCert.FinalCellSystem.CellDataModelStatement`)

Proved from further statements by `Breakdown.CellCert.FinalCellSystem.cellDataModel_of`.

**Row conditions inside a cell.** The row part requires cell support, the declared row-mode support, support at each assigned pair of opposite modes and positive row weights. (`Breakdown.CellCert.FinalCellSystem.CellDataRowsPart`)

**Cell row data from a system.** The cell-system condition must give the row part of the cell conditions at exponent 501/500 for every cell. (`Breakdown.CellCert.FinalCellSystem.CellDataRowsStatement`)

Proved by `Breakdown.CellCert.FinalCellSystem.cellDataRows_holds`. Also proved from further statements by `Breakdown.CellCert.FinalCellSystem.cellDataRows_of`.

**Far-mode cell conditions.** The far part requires coverage of nonzero couplings by classes, the far-field form bound and the stated row multiplier matrix bound. (`Breakdown.CellCert.FinalCellSystem.CellDataFarPart`)

**Far-mode conditions from a system.** The cell-system condition must give the far part of the cell conditions at exponent 501/500 for every cell. (`Breakdown.CellCert.FinalCellSystem.CellDataFarStatement`)

Proved from further statements by `Breakdown.CellCert.FinalCellSystem.cellDataFar_of_form`.

**Distinct cells overlap only on null sets.** The cell-system condition must make the intersection of any two distinct split cells have zero volume. (`Breakdown.CellCert.FinalCellSystem.CellsApartStatement`)

Proved by `Breakdown.CellCert.FinalCellSystem.cellsApart_holds`.

**Axis bounds at every polynomial degree.** The proposition asks the cell-system condition to imply the prescribed axis gradient bound for every natural polynomial degree. (`Breakdown.CellCert.FinalCellSystem.AxisGradientAllStatement`)

No theorem in the library states this proposition as its result or names it.

**Valid row turning data.** Valid given data and the row-turn numerical conditions must make the row turning data extracted from the mesh valid. (`Breakdown.CellCert.FinalCellSystem.RowTurnDataOfStatement`)

Proved by `Breakdown.CellCert.FinalCellSystem.rowTurnDataOf_holds`.

**Symmetric weights from given fields.** Valid given data, a positive scalar weight and all required amplitude indices must make the listed error, amplitude, higher-profile, phase-curvature and active adjoint squares integrable symmetric sum weights. (`Breakdown.CellCert.FinalCellSystem.SumWeightsOfStatement`)

Proved by `Breakdown.CellCert.FinalCellSystem.sumWeightsOf_holds`.

**Adjoint dual structure from data.** Valid given data at exponent 501/500 with all required amplitude indices must make the constructed adjoint dual satisfy its analytic structure for every adjoint index and parameter. (`Breakdown.CellCert.FinalCellSystem.AdjointDualStructureOfStatement`)

Proved by `Breakdown.CellCert.FinalCellSystem.adjointDualStructureOf_holds`.

**Kernel bound on profile displacement.** The cell-system condition must bound the squared gradient difference between each boxed profile and the centre by the squared centre-kernel constant. (`Breakdown.CellCert.FinalCellSystem.CentreKernelSplitOfStatement`)

Proved by `Breakdown.CellCert.FinalCellSystem.centreKernelSplitOf_holds`.

**Kernel bound on active adjoints.** The cell-system condition must give the specified adjoint kernel bound for every active adjoint and parameter in the box. (`Breakdown.CellCert.FinalCellSystem.AdjointKernelOfStatement`)

Proved by `Breakdown.CellCert.FinalCellSystem.adjointKernelOf_holds`.

**Polynomial rows from a system.** The cell-system condition must make the rows on every cell polynomial with the specified row degree. (`Breakdown.CellCert.FinalCellSystem.RowPolynomialOfSystemStatement`)

Proved by `Breakdown.CellCert.FinalCellSystem.rowPolynomialOfSystem_holds`.

### Breakdown.FracCell.CentreIdentityParts

This file proves the weak product and integration-by-parts identities that cancel the centre terms in the model-form calculation, including the required integrability of each term.

**Derivative of a centre gradient product.** The gradient part is the sum of the three coordinate products obtained by differentiating a centre-gradient, field and field-gradient product. (`Breakdown.CellCert.CentreIdentityParts.gradPart`)

**Derivative of a centre value product.** The value part is the sum of the three coordinate products obtained by differentiating a centre value times two field-gradient entries. (`Breakdown.CellCert.CentreIdentityParts.valuePart`)

**Square integrability after a cutoff.** A continuous compactly supported cutoff times a bounded measurable multiplier times an Lᵖ function is square integrable when p is at least two. (`_private.Breakdown.FracCell.CentreIdentityParts.0.Breakdown.CellCert.CentreIdentityParts.memLp_cut`)

**Integrability after a cutoff.** A continuous compactly supported cutoff times a bounded measurable multiplier times a locally integrable function is integrable. (`_private.Breakdown.FracCell.CentreIdentityParts.0.Breakdown.CellCert.CentreIdentityParts.int_cut`)

**Bound a smoothed scalar function.** Convolution with the normalized smooth bump preserves an almost everywhere uniform bound on a locally integrable scalar function. (`_private.Breakdown.FracCell.CentreIdentityParts.0.Breakdown.CellCert.CentreIdentityParts.conv_bound`)

**Derivative of a smoothed function.** Convolving a locally integrable function with the normalized smooth bump turns its stated weak coordinate derivative into the classical derivative of the convolution. (`_private.Breakdown.FracCell.CentreIdentityParts.0.Breakdown.CellCert.CentreIdentityParts.conv_fderiv`)

**Weak product integration by parts.** A continuous bounded coefficient with bounded measurable weak derivative and a locally integrable weakly differentiable factor satisfy the stated tested product integration-by-parts identity. (`_private.Breakdown.FracCell.CentreIdentityParts.0.Breakdown.CellCert.CentreIdentityParts.prod_two`)

**Weak triple product rule.** A bounded continuous coefficient with bounded weak derivative, an Lᵖ factor with p at least two and square integrable remaining factors and weak derivatives satisfy the tested triple product rule. (`Breakdown.CellCert.CentreIdentityParts.triple_local`)

**Integral of a triple derivative.** Under the weak triple product hypotheses and integrability of the product and all three derivative terms, the integral of their derivative sum is zero. (`Breakdown.CellCert.CentreIdentityParts.triple_parts`)

**Coordinate from a unit pairing.** Pairing a vector with a coordinate unit vector returns that coordinate. (`Breakdown.CellCert.CentreIdentityParts.unit_inner`)

**Take coordinates of a weak derivative.** A vector weak derivative identity passes to every coordinate when the field and derivative have Lᵖ exponents at least one. (`Breakdown.CellCert.CentreIdentityParts.weak_coord`)

**Coordinates preserve integrability.** Every coordinate of an Lᵖ vector field lies in the same Lᵖ space. (`Breakdown.CellCert.CentreIdentityParts.memLp_coord`)

**Square integrable second directions.** Every pair of coordinate directions of a second-order field has a square integrable second derivative. (`Breakdown.CellCert.CentreIdentityParts.memLp_second`)

**Integrable bounded triple product.** A bounded measurable coefficient times two square integrable scalar functions is integrable. (`Breakdown.CellCert.CentreIdentityParts.int_bdd`)

**Coordinate bounded by vector norm.** The absolute value of a vector coordinate is at most the vector norm. (`Breakdown.CellCert.CentreIdentityParts.coord_le`)

**Uniform bounds on centre coordinates.** A valid fractional cell gives common uniform bounds for the coordinates of its centre and its first two derivatives. (`Breakdown.CellCert.CentreIdentityParts.centre_coord_bounds`)

**Centre coordinate integration by parts.** A valid fractional cell makes each centre-gradient coordinate the weak coordinate derivative of the corresponding centre component. (`Breakdown.CellCert.CentreIdentityParts.centre_parts`)

**Zero integral of the value part.** For a valid fractional cell and second-order field, every centre value part is integrable and has integral zero. (`Breakdown.CellCert.CentreIdentityParts.valuePart_integral`)

**Integrable inverse-radius products.** For a second-order field, a measurable weight whose product with radius is uniformly bounded makes each weighted field component square integrable. (`Breakdown.CellCert.CentreIdentityParts.weighted_sq`)

**Decay absorbs one radial factor.** For an exponent at least one, radius times the corresponding inverse power of 1 plus radius is at most one. (`Breakdown.CellCert.CentreIdentityParts.decay_mul_le`)

**Zero integral of the gradient part.** For a valid fractional cell and second-order field, every centre gradient part is integrable and has integral zero. (`Breakdown.CellCert.CentreIdentityParts.gradPart_integral`)

**Symmetric weak second derivatives.** The two coordinate directions of a second-order field can be exchanged almost everywhere. (`Breakdown.CellCert.CentreIdentityParts.second_symm_field`)

### Breakdown.FracCell.CentrePairing

This file assembles the centre and actuator pairings with the negative second trace into the identity used to derive the cell model form.

**Pairing identities from the centre law.** The centre identity implies, for valid fractional cells and second-order fields, both the centre convection pairing formula and the actuator gradient pairing formula. (`Breakdown.CellCert.centrePairing_of`)

**Centre and actuator pairing identities.** For valid fractional cells and second-order fields, the centre convection pairing equals the integrated strain-curl form and each actuator pairing equals its gradient pairing. (`Breakdown.CellCert.centrePairing`)

### Breakdown.FracCell.CentrePairingActuator

This file establishes the global weak integration-by-parts pairing for actuators, reducing vector fields to scalar coordinates and removing compact-support restrictions by approximation.

**Lift a scalar into a vector.** The lift multiplies the first coordinate unit vector by the scalar function. (`Breakdown.CellCert.CentrePairingActuatorInternal.lift`)

**Pair two scalar lifts.** The inner product of two lifted scalar values equals their scalar product. (`Breakdown.CellCert.CentrePairingActuatorInternal.lift_inner`)

**Square integrable scalar lift.** Lifting a square integrable scalar function gives a square integrable vector field. (`Breakdown.CellCert.CentrePairingActuatorInternal.memLp_lift`)

**Integral of a shifted scalar lift.** Integrating a test function times a shifted scalar lift equals the corresponding scalar integral times the first coordinate unit vector. (`Breakdown.CellCert.CentrePairingActuatorInternal.lift_shift_int`)

**Exchange a shifted scalar pairing.** For square integrable scalar functions and a scalar test function, the integral of the shifted pairing equals the stated iterated scalar integral. (`Breakdown.CellCert.CentrePairingActuatorInternal.exch`)

**Translate a scalar test function.** Translating a scalar test function preserves the test-function conditions and translates its derivative. (`Breakdown.CellCert.CentrePairingActuatorInternal.shift_test`)

**Compact support vanishes far away.** A compactly supported scalar function vanishes beyond some radius. (`Breakdown.CellCert.CentrePairingActuatorInternal.bound_zero`)

**Compact support of a shift integral.** The shift integral of a compactly supported function against a function vanishing beyond a fixed radius has compact support. (`Breakdown.CellCert.CentrePairingActuatorInternal.shift_support`)

**Pair weak derivatives with support.** Two scalar weak derivative identities give the global integration-by-parts pairing when all four functions are square integrable and the first factor vanishes beyond a fixed radius. (`Breakdown.CellCert.CentrePairingActuatorInternal.parts_scalar`)

**Norm of a coordinate unit vector.** Every coordinate unit vector has norm one. (`Breakdown.CellCert.CentrePairingActuatorInternal.unit_norm'`)

**Multiply by a bounded coefficient.** Multiplying a square integrable scalar function by a bounded continuous function preserves square integrability. (`Breakdown.CellCert.CentrePairingActuatorInternal.memLp_mulb`)

**Integrable scalar test product.** The product of a scalar test function and a square integrable scalar function is integrable. (`Breakdown.CellCert.CentrePairingActuatorInternal.tint`)

**Pair square integrable weak derivatives.** Two scalar weak derivative identities give the global integration-by-parts pairing when the functions and both weak derivatives are square integrable. (`Breakdown.CellCert.CentrePairingActuatorInternal.parts_h1`)

**Project a vector weak derivative.** A square integrable vector weak derivative identity passes to pairing with each coordinate unit vector. (`Breakdown.CellCert.CentrePairingActuatorInternal.comp_weak`)

**Expand a vector pairing.** The inner product of two vectors is the sum of the products of their coordinate unit-vector pairings. (`Breakdown.CellCert.CentrePairingActuatorInternal.comp_expand`)

**Pair a field with the negative trace.** For a second-order field, pairing its negative second trace with a square integrable field having a measurable finite-energy weak gradient equals the integrated gradient pairing. (`Breakdown.CellCert.CentrePairingActuatorInternal.pair_h1`)

**Actuator pairing with the trace.** For a valid fractional cell and second-order field, each actuator paired with the negative second trace equals the integral of the field gradient paired with the actuator gradient. (`Breakdown.CellCert.actuatorPairing`)

### Breakdown.FracCell.CentrePairingCentre

This file proves the algebraic centre identity, expressing the convection pairing as the strain-curl form plus explicit derivative terms whose integrals vanish.

**Coordinate convection polynomial.** The left polynomial is the negative coordinate contraction of the centre convection terms with the second trace. (`Breakdown.CellCert.CentrePairingCentreInternal.leftPoly`)

**Coordinate curl polynomial.** The curl polynomial contracts matrix entries with the three-dimensional permutation signs. (`Breakdown.CellCert.CentrePairingCentreInternal.curlPoly`)

**Coordinate curl gradient polynomial.** The curl-gradient polynomial contracts the second-derivative array with the three-dimensional permutation signs. (`Breakdown.CellCert.CentrePairingCentreInternal.curlGradPoly`)

**Coordinate strain-curl polynomial.** The right polynomial combines the curl-strain term with the two stated curl-gradient and field-gradient contractions. (`Breakdown.CellCert.CentrePairingCentreInternal.rightPoly`)

**Gradient product polynomial.** The gradient term is the three-term coordinate product rule for a centre gradient, field value and field-gradient entry. (`Breakdown.CellCert.CentrePairingCentreInternal.gradTerm`)

**Value product polynomial.** The value term is the three-term coordinate product rule for a centre value and two field-gradient entries. (`Breakdown.CellCert.CentrePairingCentreInternal.valueTerm`)

**Sum of derivative correction terms.** The correction sum is the specified finite real linear combination of gradient and value product terms. (`Breakdown.CellCert.CentrePairingCentreInternal.partsSum`)

**Algebraic centre identity.** Trace-free first-derivative arrays and symmetric second-derivative arrays make the convection polynomial equal the strain-curl polynomial plus the derivative correction sum. (`Breakdown.CellCert.CentrePairingCentreInternal.poly_identity`)

**Add functions with zero integral.** The sum of two integrable functions with integral zero is integrable and has integral zero. (`Breakdown.CellCert.CentrePairingCentreInternal.iz_add`)

**Scale a function with zero integral.** A real multiple of an integrable function with integral zero is integrable and has integral zero. (`Breakdown.CellCert.CentrePairingCentreInternal.iz_mul`)

**Derivative corrections integrate to zero.** If every gradient and value term is integrable with integral zero, their correction sum is integrable with integral zero. (`Breakdown.CellCert.CentrePairingCentreInternal.parts_zero`)

**Convection pairing in coordinates.** The inner product of the doubled symmetric convection expression with the negative second trace equals its coordinate convection polynomial. (`Breakdown.CellCert.CentrePairingCentreInternal.left_eq`)

**Symmetric part preserves self-pairing.** Pairing a vector with the symmetric part of a linear map applied to that vector equals the pairing with the original map. (`Breakdown.CellCert.CentrePairingCentreInternal.inner_symPart`)

**Curl as a signed coordinate sum.** Every curl component is the signed sum of the corresponding matrix entries. (`Breakdown.CellCert.CentrePairingCentreInternal.curl_apply`)

**Curl gradient as a signed sum.** Every curl-gradient matrix entry is the stated signed sum of second-derivative coordinates. (`Breakdown.CellCert.CentrePairingCentreInternal.curlGrad_entry`)

**Strain-curl form in coordinates.** The strain-curl form built from the symmetric first derivative and curl gradient equals its coordinate polynomial. (`Breakdown.CellCert.CentrePairingCentreInternal.right_eq`)

**Centre convection identity.** For a valid fractional cell and second-order field, the centre convection pairing with the negative second trace equals the integrated centre strain-curl form. (`Breakdown.CellCert.centreIdentity`)

### Breakdown.FracCell.CertificateOfCell

This file converts the verified fractional cell conditions into the abstract fractional certificate, assembling the model regularity, coercivity, residual, pin and split-row estimates.

**Regularity of the cell model field.** For 1 < α < 5/4, a valid fractional cell gives a measurable locally square integrable model field for every boxed parameter, second-order field and actuator coefficient vector. (`Breakdown.CellCert.modelRegular_holds`)

**Coercive lower bound for the model.** For 1 < α < 5/4, valid fractional cells give the stated coercive size bound by the model form, gradient-corrected row term and model pin term for boxed parameters and second-order fields. (`Breakdown.CellCert.modelLower_holds`)

**Control the model field error.** For 1 < α < 5/4, valid fractional cells and second-order fields with weak fractional power and square integrable drift admit a gradient correction whose row error is bounded by row loss times size. (`Breakdown.CellCert.modelField_holds`)

**Control the model pin error.** For 1 < α < 5/4, valid fractional cells and second-order fields with weak fractional power and square integrable drift bound the model pin error by pin loss times size. (`Breakdown.CellCert.modelPin_holds`)

**Control the split row term.** For 1 < α < 5/4, valid fractional cells and second-order fields with weak fractional power bound the split-field row term by the split constant times split energy. (`Breakdown.CellCert.splitRows_holds`)

**Model form from pairing identities.** The centre and actuator pairing identities give the model-form lower pairing bound, with the potential-loss term, for valid fractional cells and the stated fractional field and drift hypotheses. (`Breakdown.CellCert.modelForm_of_pairing`)

**Certificate from cell pairings.** For 1 < α < 5/4, the centre pairing statement turns a valid fractional cell into a valid fractional certificate. (`Breakdown.CellCert.isFracCert_of_cell_of_pairing`)

**Certificate from the centre identity.** For 1 < α < 5/4, the centre identity statement turns a valid fractional cell into a valid fractional certificate. (`Breakdown.CellCert.isFracCert_of_cell_of_centre`)

**A cell supplies a certificate.** For 1 < α < 5/4, every valid fractional cell yields a valid fractional certificate. (`Breakdown.CellCert.isFracCert_of_cell`)

**Cell existence supplies a certificate.** For 1 < α < 5/4, the fractional cell certificate hypothesis implies the abstract fractional certificate hypothesis. (`Breakdown.CellCert.fracCertificateHypothesis_of_cell`)

### Breakdown.FracCell.ChosenAgree

This file identifies the derivatives chosen by the abstract cell construction with the supplied weak first and second derivatives, allowing later model formulas to use either representation.

**Determine a map on coordinate vectors.** Two continuous linear maps on space are equal if they agree on every coordinate unit vector. (`Breakdown.CellCert.ChosenAgreeInternal.map_ext`)

**Locally integrable gradient columns.** A measurable matrix field with finite entry-square integral has locally integrable coordinate columns. (`Breakdown.CellCert.ChosenAgreeInternal.column_local`)

**Locally integrable second directions.** A measurable second-derivative field with finite summed coordinate square integral has locally integrable values in each pair of coordinate directions. (`Breakdown.CellCert.ChosenAgreeInternal.entry_local`)

**Chosen derivatives agree almost surely.** For every second-order field, the chosen first and second derivatives agree almost everywhere with the supplied derivatives. (`Breakdown.CellCert.chosenAgree`)

### Breakdown.FracCell.CircleProduct

This file develops Fourier products and matrix pairings on the circle, then connects the coefficients to cylindrical angular modes used in the cell coupling estimates.

**Circle inner product as an integral.** The complex L² circle inner product equals the integral of the conjugate of the first function times the second. (`Breakdown.CellCert.CellAnalysis.CircleProduct.inner_eq`)

**Fourier coefficient as a pairing.** Pairing a circle function with a Fourier basis vector gives the corresponding Fourier coefficient. (`Breakdown.CellCert.CellAnalysis.CircleProduct.coeff_eq`)

**Multiply by a bounded circle function.** A bounded measurable circle function times an L² circle function remains square integrable. (`Breakdown.CellCert.CellAnalysis.CircleProduct.mul_memLp`)

**Fourier coefficient of a product.** For a bounded measurable circle multiplier and an L² circle function, the convolution of their Fourier coefficients sums to the product coefficient. (`Breakdown.CellCert.CellAnalysis.CircleProduct.coeff_mul_hasSum`)

**Fourier pairing identity.** For two square integrable circle functions, the series of conjugate coefficient products sums to their integral pairing. (`Breakdown.CellCert.CellAnalysis.CircleProduct.pair_hasSum`)

**Spread coefficients to selected modes.** Spreading places each sequence value at its integer multiple of the symmetry order and sets all other coefficients to zero. (`Breakdown.CellCert.CellAnalysis.CircleProduct.spread`)

**Distinct scaled integer indices.** Multiplication of integer indices by a natural number at least one is injective. (`Breakdown.CellCert.CellAnalysis.CircleProduct.mul_injective`)

**Read a spread coefficient.** At an integer multiple of a symmetry order at least one, spreading returns the original coefficient. (`Breakdown.CellCert.CellAnalysis.CircleProduct.spread_mul`)

**Spread coefficients vanish elsewhere.** A spread coefficient is zero outside the range of multiplication by the symmetry order. (`Breakdown.CellCert.CellAnalysis.CircleProduct.spread_off`)

**Spreading preserves square sums.** For symmetry order at least one, spreading a sequence with summable squared norms preserves summability of squared norms. (`Breakdown.CellCert.CellAnalysis.CircleProduct.spread_sq_summable`)

**Spreading gives an L² sequence.** For symmetry order at least one, spreading a sequence with summable squared norms gives an element of the sequence L² space. (`Breakdown.CellCert.CellAnalysis.CircleProduct.spread_memℓp`)

**Lift modal data to the circle.** The lift applies the inverse Fourier representation to a square-summable sequence spread across multiples of a positive symmetry order. (`Breakdown.CellCert.CellAnalysis.CircleProduct.lift`)

**Fourier coefficients of the lift.** Every Fourier coefficient of the lifted circle function equals the corresponding spread coefficient. (`Breakdown.CellCert.CellAnalysis.CircleProduct.lift_coeff`)

**Read lifted symmetry modes.** For symmetry order at least one, the coefficient of the lift at a multiple of that order equals the original sequence value. (`Breakdown.CellCert.CellAnalysis.CircleProduct.lift_coeff_mul`)

**Energy of the lifted circle function.** The squared integral norm of the lifted circle function equals the sum of the original squared coefficient norms. (`Breakdown.CellCert.CellAnalysis.CircleProduct.lift_sq`)

**Product coefficient at selected modes.** For a bounded measurable multiplier and a square-summable modal sequence, the selected-mode convolution sums to the coefficient of the multiplier times the lifted function. (`Breakdown.CellCert.CellAnalysis.CircleProduct.inner_hasSum`)

**Pair a lift with a circle function.** For a square-summable modal sequence and an L² circle function, the selected coefficient pairing series sums to the integral pairing with the lift. (`Breakdown.CellCert.CellAnalysis.CircleProduct.outer_hasSum`)

**Extend a real quadratic bound.** A real-entry matrix quadratic bound for real vectors also bounds the real part of its Hermitian pairing on complex vectors. (`Breakdown.CellCert.CellAnalysis.CircleProduct.quad_re_le`)

**Pair two mode bands.** The band pairing contracts one modal vector, the matrix Fourier coefficient at the mode difference and the second modal vector. (`Breakdown.CellCert.CellAnalysis.CircleProduct.bandPairing`)

**Bound the full band pairing.** A uniformly bounded measurable real matrix field with pointwise quadratic upper bound gives summable iterated band pairings bounded by that constant times the modal square sum. (`Breakdown.CellCert.CellAnalysis.CircleProduct.bandPairing_bound`)

**Orthonormal cylindrical frame.** Two cylindrical frame vectors have inner product one at equal indices and zero otherwise. (`Breakdown.CellCert.CellAnalysis.CircleProduct.frame_inner_eq`)

**Quadratic form in a rotating frame.** The coordinate matrix quadratic form in the cylindrical frame equals the physical vector pairing with the original linear map. (`Breakdown.CellCert.CellAnalysis.CircleProduct.frame_quad`)

**Norm in a rotating frame.** The squared norm of a real linear combination of cylindrical frame vectors is the sum of the squared coefficients. (`Breakdown.CellCert.CellAnalysis.CircleProduct.frame_sq`)

**Positive angular interval length.** The interval from −π to π has positive length. (`Breakdown.CellCert.CellAnalysis.CircleProduct.pi_len`)

**Register positive circle length.** The interval length π minus −π satisfies the positive-length fact required by the circle construction. (`Breakdown.CellCert.CellAnalysis.CircleProduct.pi_fact`)

**Matrix modes as Fourier coefficients.** A cylindrical matrix mode equals the corresponding Fourier coefficient of its framed angular slice on the circle. (`Breakdown.CellCert.CellAnalysis.CircleProduct.mode_coeff`)

### Breakdown.FracCell.CircleSliceCoupling

This file proves that the angular integral of the cell strain-curl form equals its Fourier mode coupling, assembling scalar product identities into the full matrix expression.

**Coefficient of a real angular slice.** The slice coefficient is the complex circle coefficient at the azimuthal frequency determined by the order and mode. (`Breakdown.FracInternal.CircleSliceCoupling.cf`)

**Series for an angular average.** The angular-average condition requires interval integrability and a coefficient series summing to the normalized real angular integral viewed as a complex number. (`Breakdown.FracInternal.CircleSliceCoupling.Cst`)

**Add angular average series.** Adding two series for angular averages gives a series for the average of the sum. (`Breakdown.FracInternal.CircleSliceCoupling.cst_add`)

**Negate an angular average series.** Negating a series for an angular average gives a series for the average of the negative function. (`Breakdown.FracInternal.CircleSliceCoupling.cst_neg`)

**Scale an angular average series.** Real scalar multiplication preserves the series identity for the corresponding scaled angular average. (`Breakdown.FracInternal.CircleSliceCoupling.cst_const`)

**Sum angular average series.** A finite sum of angular-average identities gives the identity for the finite sum of their functions and coefficient sequences. (`Breakdown.FracInternal.CircleSliceCoupling.cst_sum`)

**Pair real angular coefficients.** A regular periodic angular slice and a square integrable slice at positive symmetry order have coefficient products summing to the average of their product. (`Breakdown.FracInternal.CircleSliceCoupling.cst_atom`)

**Bounded factors preserve circle L².** Multiplying a square integrable angular function by a bounded measurable factor preserves square integrability over a full turn. (`Breakdown.FracInternal.CircleSliceCoupling.bounded_memLp`)

**Bounded angular functions are L².** A bounded measurable angular function is square integrable over a full turn. (`Breakdown.FracInternal.CircleSliceCoupling.bounded_memLp_self`)

**Convolution for angular products.** For positive symmetry order, a square integrable slice and a regular periodic slice have a coefficient convolution summing to each coefficient of their product. (`Breakdown.FracInternal.CircleSliceCoupling.atom_inner`)

**Conjugate a mode difference.** For a real angular function, conjugating its coefficient at the reversed mode difference gives the coefficient at the original difference. (`Breakdown.FracInternal.CircleSliceCoupling.cf_conj`)

**Sum three convergent series.** Summing three series term by term gives a series with the sum of their limits. (`Breakdown.FracInternal.CircleSliceCoupling.hs3`)

**Sum three angular averages.** Three angular-average series identities combine into the identity for their sum. (`Breakdown.FracInternal.CircleSliceCoupling.cst3`)

**Replace equal angular average data.** Pointwise equality of both the coefficient sequence and angular function preserves an angular-average identity. (`Breakdown.FracInternal.CircleSliceCoupling.cst_congr`)

**Curl of an angular matrix.** The curl row contracts angular matrix entries with the three-dimensional permutation signs. (`Breakdown.FracInternal.CircleSliceCoupling.curlRow`)

**Strain-curl form on a slice.** The slice form is the stated curl-strain quadratic term plus the two curl-gradient contractions with velocity and gradient entries. (`Breakdown.FracInternal.CircleSliceCoupling.jSlice`)

**Expand the real slice form.** The real slice form equals its curl quadratic term plus four explicitly symmetrized coordinate cross terms. (`Breakdown.FracInternal.CircleSliceCoupling.jSlice_expand`)

**Expand the complex coupling form.** The complex wave form equals its curl quadratic pairing plus the four stated conjugated coordinate cross terms. (`Breakdown.FracInternal.CircleSliceCoupling.wave_expand`)

**Curl commutes with coefficients.** For interval-integrable matrix entries, taking the curl of the coefficient matrix equals taking the coefficient of the real curl row. (`Breakdown.FracInternal.CircleSliceCoupling.curl_coeff`)

**Series for the full slice form.** Regular periodic gradient and velocity slices with bounded measurable strain and curl-gradient slices at positive symmetry order give the iterated wave-coupling series for their angular-average slice form. (`Breakdown.FracInternal.CircleSliceCoupling.hbase`)

**Angular integral equals mode coupling.** For symmetry order at least three and valid circle-slice data, the strain-curl form is interval integrable and its full-turn integral equals 2π times the mode coupling. (`Breakdown.CellCert.CellAnalysis.circleSliceCoupling_holds`)

### Breakdown.FracCell.CircleSliceRegular

This file obtains almost-everywhere regular angular slices from the three-dimensional field assumptions, justifying the Fourier identities used to express cell density in modes.

**Extend a periodic almost-everywhere law.** For a 2π-periodic real function, an almost-everywhere translation identity on (−π, π) extends to almost every real angle. (`Breakdown.FracInternal.CircleSliceRegular.per_ae`)

**Transfer L² across a period.** A 2π-periodic real function square integrable on (−π, π) is square integrable on (0, 2π]. (`Breakdown.FracInternal.CircleSliceRegular.per_memLp`)

**Measurable cylindrical slices.** For a valid cell and an almost everywhere strongly measurable field, each continuous scalar observation has measurable angular slices for almost every point of the cell rectangle. (`Breakdown.FracInternal.CircleSliceRegular.slice_meas`)

**Cylindrical points remain in the cell.** For a valid cell, any cylindrical point over its rectangle lies in its solid cell. (`Breakdown.FracInternal.CircleSliceRegular.cyl_solid`)

**Square integrable cylindrical slices.** For a valid cell and a measurable field square integrable on the stated enclosing ball, continuous periodic observations bounded by the field norm have square integrable angular slices almost everywhere on the rectangle. (`Breakdown.FracInternal.CircleSliceRegular.slice_gen`)

**Measurable bounded periodic slices.** For a valid cell, measurable field and uniformly bounded continuous periodic observation, the angular observation is measurable over a full turn almost everywhere on the rectangle. (`Breakdown.FracInternal.CircleSliceRegular.slice_bdd`)

**Matrix fields from entry energy.** A measurable matrix field with finite entry-square integral is square integrable in operator norm. (`Breakdown.FracInternal.CircleSliceRegular.clm_memLp`)

**Second derivatives from entry energy.** A measurable second-derivative field with finite summed coordinate square integral is square integrable in operator norm. (`Breakdown.FracInternal.CircleSliceRegular.bil_memLp`)

**Valid circle slices almost everywhere.** For 1 < α < 5/4, valid form data, a valid cell with axisymmetric weight, model mirror symmetry and cell-region inclusion give valid circle-slice data almost everywhere for every admissible input. (`Breakdown.CellCert.CellAnalysis.circleSliceRegular_holds`)

### Breakdown.FracCell.CircleWeak

This file transfers a three-dimensional weak gradient identity to almost every circle at fixed radius and height, using smooth angular probes supported away from the axis.

**Smooth coordinate functions.** Each spatial coordinate function is smooth. (`Breakdown.CellCert.CellEnergy.Internal.CircleWeak.coord_cd`)

**Continuous cylindrical radius.** The cylindrical radius is continuous. (`Breakdown.CellCert.CellEnergy.Internal.CircleWeak.radius_cont`)

**Smooth radius away from the axis.** The cylindrical radius is smooth at every point with positive cylindrical radius. (`Breakdown.CellCert.CellEnergy.Internal.CircleWeak.radius_cdAt`)

**Angular tangent field.** The turn field has horizontal coordinates −y₁ and y₀ and zero vertical coordinate. (`Breakdown.CellCert.CellEnergy.Internal.CircleWeak.turn`)

**Complex horizontal coordinate.** The plane coordinate is the first spatial coordinate plus i times the second. (`Breakdown.CellCert.CellEnergy.Internal.CircleWeak.plane`)

**Smooth complex plane coordinate.** The complex horizontal coordinate is smooth. (`Breakdown.CellCert.CellEnergy.Internal.CircleWeak.plane_cd`)

**Single coordinate as a unit vector.** A vector with only one nonzero coordinate equals that coordinate times the corresponding unit vector. (`Breakdown.CellCert.CellEnergy.Internal.CircleWeak.single_eq`)

**Expand the angular tangent.** The angular tangent is minus the second coordinate times the first unit vector plus the first coordinate times the second unit vector. (`Breakdown.CellCert.CellEnergy.Internal.CircleWeak.turn_eq`)

**Continuous angular tangent.** The angular tangent field is continuous. (`Breakdown.CellCert.CellEnergy.Internal.CircleWeak.turn_cont`)

**Angular tangent on a cylinder.** At a cylindrical point, the angular tangent equals radius times the angular unit vector. (`Breakdown.CellCert.CellEnergy.Internal.CircleWeak.turn_cyl`)

**Complex coordinate on a cylinder.** The complex horizontal coordinate of a cylindrical point equals radius times cosine plus i times sine of its angle. (`Breakdown.CellCert.CellEnergy.Internal.CircleWeak.plane_cyl`)

**Radius of a cylindrical point.** At positive radius, the cylindrical point has that same cylindrical radius. (`Breakdown.CellCert.CellEnergy.Internal.CircleWeak.radius_cyl`)

**Height of a cylindrical point.** The third coordinate of a cylindrical point is its height. (`Breakdown.CellCert.CellEnergy.Internal.CircleWeak.height_cyl`)

**Norm bound for cylindrical points.** The norm of a cylindrical point is at most twice the absolute radius plus the absolute height. (`Breakdown.CellCert.CellEnergy.Internal.CircleWeak.cyl_norm`)

**Enclose a cylindrical point in a ball.** If twice the absolute radius plus the absolute height is at most R, the cylindrical point lies in the closed ball of radius R. (`Breakdown.CellCert.CellEnergy.Internal.CircleWeak.cyl_mem`)

**Periodic functions respect angle classes.** A 2π-periodic function takes equal values at real angles defining the same angle class. (`Breakdown.CellCert.CellEnergy.Internal.CircleWeak.per_angle`)

**Evaluate through the complex argument.** For positive radius and a 2π-periodic function, evaluating it at the argument of the cylindrical complex coordinate gives its value at the original angle. (`Breakdown.CellCert.CellEnergy.Internal.CircleWeak.w_circle`)

**Derivative preserves periodicity.** The derivative of a 2π-periodic complex function is 2π-periodic. (`Breakdown.CellCert.CellEnergy.Internal.CircleWeak.deriv_periodic`)

**Smooth periodic argument composition.** A smooth 2π-periodic function composed with complex argument is smooth at every nonzero complex point. (`Breakdown.CellCert.CellEnergy.Internal.CircleWeak.argw_cdAt`)

**Angular probe with a radial cutoff.** The probe multiplies a radial-height cutoff by an angular function evaluated at the complex horizontal argument. (`Breakdown.CellCert.CellEnergy.Internal.CircleWeak.probe`)

**Smooth angular probes off the axis.** A smooth radial-height cutoff supported at positive radii and a smooth periodic angular function give a smooth spatial probe. (`Breakdown.CellCert.CellEnergy.Internal.CircleWeak.probe_cd`)

**Horizontal coordinates below radius.** The absolute value of either horizontal coordinate is at most cylindrical radius. (`Breakdown.CellCert.CellEnergy.Internal.CircleWeak.abs_coord_le`)

**Norm below the coordinate sum.** The vector norm is at most the sum of the absolute values of its three coordinates. (`Breakdown.CellCert.CellEnergy.Internal.CircleWeak.norm_le_coords`)

**Compact support of angular probes.** A compactly supported radial-height cutoff gives a compactly supported spatial probe for every angular function. (`Breakdown.CellCert.CellEnergy.Internal.CircleWeak.probe_csupp`)

**Evaluate the cylindrical probe.** For positive radius and periodic angular data, the probe at a cylindrical point is the cutoff at radius and height times the angular value. (`Breakdown.CellCert.CellEnergy.Internal.CircleWeak.probe_cyl`)

**Derivative along a circle.** Differentiating the cylindrical point with respect to angle gives the angular tangent field. (`Breakdown.CellCert.CellEnergy.Internal.CircleWeak.curve_deriv`)

**Angular derivative of a probe.** For positive radius, a smooth probe built from smooth periodic angular data has tangent derivative equal to the cutoff times the angular derivative. (`Breakdown.CellCert.CellEnergy.Internal.CircleWeak.probe_turn`)

**Derivative retains compact support.** Evaluating the derivative of a compactly supported function along any vector field still has compact support. (`Breakdown.CellCert.CellEnergy.Internal.CircleWeak.csupp_fderiv_apply`)

**Local integrability of a fixed pairing.** Pairing a locally integrable vector field with a fixed vector gives a locally integrable scalar function. (`Breakdown.CellCert.CellEnergy.Internal.CircleWeak.loc_inner`)

**Local integrability of angular pairing.** Pairing a locally integrable vector field with the angular tangent gives a locally integrable scalar function. (`Breakdown.CellCert.CellEnergy.Internal.CircleWeak.loc_turn`)

**Real weak identity along circles.** A locally integrable scalar field and weak gradient satisfy the stated angular-tangent integration-by-parts identity against every smooth compactly supported real test function. (`Breakdown.CellCert.CellEnergy.Internal.CircleWeak.weak_turn_real`)

**Take the real part of an integral.** For an integrable complex function, the real part of its integral equals the integral of its real part. (`Breakdown.CellCert.CellEnergy.Internal.CircleWeak.re_int`)

**Take the imaginary part of an integral.** For an integrable complex function, the imaginary part of its integral equals the integral of its imaginary part. (`Breakdown.CellCert.CellEnergy.Internal.CircleWeak.im_int`)

**Complex weak identity along circles.** A locally integrable scalar field and weak gradient give integrable terms satisfying the angular-tangent integration-by-parts identity against every smooth compactly supported complex probe. (`Breakdown.CellCert.CellEnergy.Internal.CircleWeak.weak_turn`)

**Integrability in cylindrical coordinates.** An integrable spatial function has integrable angular slices at almost every positive radius and an integrable radius-weighted angular integral over the positive radial-height half-plane. (`Breakdown.CellCert.CellEnergy.Internal.CircleWeak.cyl_exchange`)

**Locally integrable angular sections.** A locally integrable scalar field has interval-integrable full-turn angular sections at almost every positive radius and height. (`Breakdown.CellCert.CellEnergy.Internal.CircleWeak.sections`)

**Bound a function of complex argument.** A continuous angular function evaluated at the horizontal complex argument is uniformly bounded on space. (`Breakdown.CellCert.CellEnergy.Internal.CircleWeak.bdd_of`)

**Measure a function of complex argument.** A continuous angular function evaluated at the horizontal complex argument is almost everywhere strongly measurable for every spatial measure. (`Breakdown.CellCert.CellEnergy.Internal.CircleWeak.meas_of`)

**Angular weak-derivative integrand.** The kernel adds the angular derivative times the scalar field to the angular function times the weak gradient paired with the tangent. (`Breakdown.CellCert.CellEnergy.Internal.CircleWeak.kern`)

**Integrable angular kernel on balls.** Smooth angular data and locally integrable scalar and gradient fields make the angular kernel integrable on every closed ball. (`Breakdown.CellCert.CellEnergy.Internal.CircleWeak.kern_int`)

**Evaluate the angular kernel.** At positive radius with periodic angular data, the kernel equals the angular derivative times the scalar slice plus the angular value times radius and the angular gradient component. (`Breakdown.CellCert.CellEnergy.Internal.CircleWeak.kern_cyl`)

**Weak derivative on almost every circle.** A locally integrable scalar field with locally integrable weak gradient has integrable angular slices almost everywhere and satisfies the stated circular integration-by-parts identity for every smooth periodic complex test function. (`Breakdown.CellCert.CellEnergy.circleWeak`)

### Breakdown.FracCell.ClassAverageRows

This file averages gradient corrections over the turn and reflection symmetries while preserving their row pairings, so the cell argument may choose a correction in the required symmetry class.

**Choose a measurable potential.** Every gradient field admits a measurable locally square integrable scalar potential satisfying its weak gradient identity, while retaining the field measurability and local square integrability. (`Breakdown.CellCert.ClassAverageRowsInternal.measurable_potential`)

**Expand a vector in coordinates.** A spatial vector equals the sum of its three coordinates times the coordinate unit vectors. (`Breakdown.CellCert.ClassAverageRowsInternal.unit_expand`)

**Integral of three summands.** The integral of three integrable real functions equals the sum of their integrals. (`Breakdown.CellCert.ClassAverageRowsInternal.integral_add3`)

**Weak gradient in any direction.** The coordinate weak gradient identities for measurable locally square integrable potential and field imply the tested identity in every fixed vector direction. (`Breakdown.CellCert.ClassAverageRowsInternal.weak_dir`)

**Transform a gradient by an isometry.** Conjugating a gradient field by a linear isometry preserves the gradient-field condition. (`Breakdown.CellCert.ClassAverageRowsInternal.grad_conj`)

**The zero field is a gradient.** The identically zero vector field is a gradient field. (`Breakdown.CellCert.ClassAverageRowsInternal.grad_zero`)

**Scale a gradient field.** A real scalar multiple of a gradient field is a gradient field. (`Breakdown.CellCert.ClassAverageRowsInternal.grad_smul`)

**Finite sums of gradient fields.** A finite initial sum of gradient fields is a gradient field. (`Breakdown.CellCert.ClassAverageRowsInternal.grad_sum`)

**Integrable pairing with a supported row.** A measurable locally square integrable field paired with a square integrable field vanishing beyond some radius gives an integrable scalar function. (`Breakdown.CellCert.ClassAverageRowsInternal.pair_int`)

**Pairing is unchanged by symmetry.** Conjugating a field by a linear isometry leaves its integral pairing with an almost everywhere equivariant row unchanged. (`Breakdown.CellCert.ClassAverageRowsInternal.pair_conj`)

**Iterate an isometry one more time.** Applying the next power of a linear isometry equals applying the preceding power after one application. (`Breakdown.CellCert.ClassAverageRowsInternal.pow_apply_succ`)

**Cancel one inverse iterate.** Applying an isometry to the inverse of its next power leaves the inverse of its preceding power. (`Breakdown.CellCert.ClassAverageRowsInternal.symm_pow_succ`)

**Symmetry under repeated isometries.** Almost everywhere equivariance under an isometry implies almost everywhere equivariance under each natural power of that isometry. (`Breakdown.CellCert.ClassAverageRowsInternal.class_pow`)

**Coordinates of repeated turns.** The jth discrete turn is horizontal rotation by j times 2π divided by the order and leaves height unchanged. (`Breakdown.CellCert.ClassAverageRowsInternal.turn_pow_apply`)

**A full cycle of turns is identity.** For nonzero symmetry order, that many discrete turns give the identity isometry. (`Breakdown.CellCert.ClassAverageRowsInternal.turn_pow_order`)

**Equivariance of a finite orbit sum.** If the mth power of an isometry is identity, summing a field over its conjugated m-element orbit gives an equivariant field. (`Breakdown.CellCert.ClassAverageRowsInternal.avg_equivariant`)

**Average over discrete turns.** The turn average is the mean of the field conjugated by all powers below the symmetry order of the discrete turn isometry. (`Breakdown.CellCert.ClassAverageRowsInternal.turnAverage`)

**Average over turns and reflection.** The full average is half the sum of the turn average and its reflected conjugate. (`Breakdown.CellCert.ClassAverageRowsInternal.fullAverage`)

**Turn averages preserve gradients.** The turn average of a gradient field is a gradient field. (`Breakdown.CellCert.ClassAverageRowsInternal.grad_turn`)

**Symmetry averages preserve gradients.** The full turn-and-reflection average of a gradient field is a gradient field. (`Breakdown.CellCert.ClassAverageRowsInternal.grad_full`)

**Turn equivariance of the average.** At nonzero symmetry order, the turn average is equivariant under the discrete turn. (`Breakdown.CellCert.ClassAverageRowsInternal.turn_equivariant`)

**Reflection commutes with turning.** Reflection and the discrete turn commute. (`Breakdown.CellCert.ClassAverageRowsInternal.mirror_turn`)

**Reflecting twice is identity.** Applying the reflection twice returns the original vector. (`Breakdown.CellCert.ClassAverageRowsInternal.mirror_mirror`)

**Inverse reflection equals reflection.** The inverse mirror isometry acts as the mirror itself. (`Breakdown.CellCert.ClassAverageRowsInternal.mirror_symm`)

**The full average has class symmetry.** At nonzero symmetry order, the full average belongs to the required turn-and-reflection symmetry class. (`Breakdown.CellCert.ClassAverageRowsInternal.class_full`)

**Turn averaging preserves row pairings.** At nonzero symmetry order, averaging a gradient over turns preserves its integral pairing with a square integrable supported row in the symmetry class. (`Breakdown.CellCert.ClassAverageRowsInternal.turn_pair`)

**Full averaging preserves shifted pairing.** For a measurable locally square integrable field, a gradient correction and a square integrable supported symmetric row at nonzero order, replacing the correction by its full average preserves the row pairing. (`Breakdown.CellCert.ClassAverageRowsInternal.pair_full`)

**Symmetric correction with the same rows.** For a valid fractional cell, every gradient correction to a measurable locally square integrable field can be replaced by a gradient in the symmetry class without changing the row functional. (`Breakdown.CellCert.classAverageRows`)

### Breakdown.FracCell.ClassCrossRegular

This file verifies integrability of the class cross-density and class-loss terms that occur when resolved modes couple to the far modes in the sharp cell estimate.

**Integrable class cross-density.** Valid form data, a valid cell box and a second-order input field make every radius-weighted class cross-density integrable on the cell rectangle. (`Breakdown.CellCert.CellAnalysis.ClassCrossRegular.Internal.cross_int`)

**Integrable class loss.** Valid cell data make each radius-weighted class-loss expression for the low strain and velocity polynomials integrable on the cell rectangle. (`Breakdown.CellCert.CellAnalysis.ClassCrossRegular.Internal.loss_int`)

**Regular class coupling terms.** For 1 < α < 5/4, valid form and cell data with an axisymmetric weight give integrable radius-weighted cross-density and class-loss terms for admissible inputs and resolved modes. (`Breakdown.CellCert.CellAnalysis.classCrossRegular_holds`)

### Breakdown.FracCell.ClassProductSplit

This file bounds interactions between two finite collections of modes by class-loss energies, using angular averaging, trace-free matrix estimates and an almost-everywhere trace argument.

**Angular complex phase.** The phase is the complex exponential at the azimuthal frequency determined by the symmetry order and integer mode. (`Breakdown.FracInternal.ClassProductSplit.ph`)

**Multiply angular phases.** The product of two angular phases is the phase at the sum of their modes. (`Breakdown.FracInternal.ClassProductSplit.ph_mul`)

**Conjugate an angular phase.** Conjugating an angular phase reverses its mode. (`Breakdown.FracInternal.ClassProductSplit.ph_conj`)

**Zero angular phase.** The phase at mode zero is one. (`Breakdown.FracInternal.ClassProductSplit.ph_zero`)

**Continuous angular phases.** Every angular phase is continuous. (`Breakdown.FracInternal.ClassProductSplit.ph_cont`)

**Continuous finite Fourier sums.** A finite complex linear combination of angular phases is continuous. (`Breakdown.FracInternal.ClassProductSplit.tp_cont`)

**Normalized angular average.** The average is the integral over (−π, π) normalized by 1 divided by 2π. (`Breakdown.FracInternal.ClassProductSplit.avg`)

**Integrable continuous angular functions.** A continuous complex function is integrable on (−π, π). (`Breakdown.FracInternal.ClassProductSplit.int_of_cont`)

**Average of a sum.** The angular average of two continuous functions added together equals the sum of their averages. (`Breakdown.FracInternal.ClassProductSplit.avg_add`)

**Average of a difference.** The angular average of the difference of two continuous functions equals the difference of their averages. (`Breakdown.FracInternal.ClassProductSplit.avg_sub`)

**Scale an angular average.** A complex constant can be taken outside the angular average. (`Breakdown.FracInternal.ClassProductSplit.avg_mul`)

**Average a finite sum.** For a finite family of continuous functions, angular averaging commutes with summation. (`Breakdown.FracInternal.ClassProductSplit.avg_sum`)

**Average of an angular phase.** At symmetry order at least one, an angular phase averages to one at mode zero and to zero otherwise. (`Breakdown.FracInternal.ClassProductSplit.avg_ph`)

**Compare real angular averages.** A pointwise lower bound by a continuous real function gives the corresponding lower bound between the real parts of angular averages. (`Breakdown.FracInternal.ClassProductSplit.avg_re_mono`)

**Expand three finite Fourier sums.** The product of a conjugated finite Fourier sum and two further sums expands into the triple coefficient sum at the combined frequency. (`Breakdown.FracInternal.ClassProductSplit.tri_point`)

**Average three Fourier sums.** At symmetry order at least one, averaging the three Fourier sums retains exactly the terms whose mode difference lies in the multiplier mode set. (`Breakdown.FracInternal.ClassProductSplit.avg_tri`)

**Reorder four finite sums.** The two finite coordinate sums can be exchanged with the two finite mode sums. (`Breakdown.FracInternal.ClassProductSplit.swap4`)

**Average a matrix Fourier pairing.** At symmetry order at least one, a finite matrix Fourier pairing averages to the stated sum over mode differences in the multiplier set. (`Breakdown.FracInternal.ClassProductSplit.avg_form`)

**Average a squared Fourier sum.** At symmetry order at least one, the angular average of a finite Fourier square equals the sum of its coefficient squares. (`Breakdown.FracInternal.ClassProductSplit.avg_sq`)

**Linear functionals on finite sums.** An additive complex-linear matrix functional commutes with a finite weighted matrix sum. (`Breakdown.FracInternal.ClassProductSplit.lin_sum`)

**Curl of a finite modal sum.** The curl components of a finite weighted matrix sum are the corresponding weighted sums of curl components. (`Breakdown.FracInternal.ClassProductSplit.curl_tp`)

**Coupling map of a modal sum.** The coupling map of a finite weighted matrix sum is the corresponding weighted sum of coupling maps. (`Breakdown.FracInternal.ClassProductSplit.cm_tp`)

**Expand coupling in vector coordinates.** The coupling map applied to a vector is the sum of its values on coordinate vectors weighted by that vector’s coordinates. (`Breakdown.FracInternal.ClassProductSplit.cm_vec`)

**Expand the matrix coupling pairing.** Pairing a coupling map with a matrix equals the stated sum over matrix entries and vector coordinates. (`Breakdown.FracInternal.ClassProductSplit.pairing_expand`)

**Expand the strain pairing.** The strain pairing equals the double coordinate sum of conjugated first-vector entries, matrix entries and second-vector entries. (`Breakdown.FracInternal.ClassProductSplit.strain_expand`)

**Weighted product bound.** For positive t, twice the product of two real numbers is at most t times the first square plus the second square divided by t. (`Breakdown.FracInternal.ClassProductSplit.amgm`)

**Nonnegative curl square.** The squared curl quantity is nonnegative. (`Breakdown.FracInternal.ClassProductSplit.curlSq_nonneg`)

**Real part above minus the norm.** The real part of a complex number is at least minus its norm. (`Breakdown.FracInternal.ClassProductSplit.re_ge`)

**Bound a strain coupling.** A nonnegative matrix operator bound controls the curl-strain pairing by that bound times the two curl norms. (`Breakdown.FracInternal.ClassProductSplit.strain_le`)

**Lower bound for a paired wave term.** Nonnegative matrix bounds, positive share and length parameters and a trace-free curl-gradient matrix bound the paired wave expression below by the stated weighted strain, curl and velocity losses. (`Breakdown.FracInternal.ClassProductSplit.point_bound`)

**Average of a negative.** Negation commutes with angular averaging. (`Breakdown.FracInternal.ClassProductSplit.avg_neg`)

**Complex form of a squared norm.** A complex number’s squared norm, embedded in the complex numbers, equals its conjugate times itself. (`Breakdown.FracInternal.ClassProductSplit.nsq`)

**Complex form of the curl square.** The real curl square embedded in the complex numbers equals the sum of the conjugate curl-component products. (`Breakdown.FracInternal.ClassProductSplit.curlSq_c`)

**Complex form of the vector square.** The real vector square embedded in the complex numbers equals the sum of its conjugate coordinate products. (`Breakdown.FracInternal.ClassProductSplit.vecSq_c`)

**Complex form of the matrix square.** The real matrix square embedded in the complex numbers equals the sum of its conjugate entry products. (`Breakdown.FracInternal.ClassProductSplit.sumSq_c`)

**Continuous matrix Fourier pairing.** A finite matrix pairing of three Fourier sums is continuous in the angle. (`Breakdown.FracInternal.ClassProductSplit.form_cont`)

**Continuous Fourier square.** The sum of the squared components of a finite Fourier series is continuous in the angle. (`Breakdown.FracInternal.ClassProductSplit.par_cont`)

**Average six weighted terms.** The angular average of six weighted continuous complex functions is the corresponding weighted sum of their averages. (`Breakdown.FracInternal.ClassProductSplit.avg_lin6`)

**Real part of half a complex value.** The real part of half a complex number equals half its real part. (`Breakdown.FracInternal.ClassProductSplit.half_re`)

**Real part of paired wave forms.** The real part of two oppositely ordered wave forms equals the stated two curl-strain pairings plus the two matrix coupling pairings. (`Breakdown.FracInternal.ClassProductSplit.wave_re`)

**Finite mode interaction bound.** At positive symmetry order, a symmetric multiplier mode set with the stated operator and trace bounds gives the lower interaction bound by the weighted losses of the two finite mode collections. (`Breakdown.FracInternal.ClassProductSplit.hbase`)

**Trace-free modes from a trace-free field.** Interval-integrable matrix entries and pointwise zero trace on a circle give zero trace for every cylindrical matrix mode there. (`Breakdown.FracInternal.ClassProductSplit.zero_trace_gen`)

**Trace-free model modes almost everywhere.** Valid form and cell data make every model curl-gradient mode trace-free at almost every positive-radius point in the cell rectangle. (`Breakdown.FracInternal.ClassProductSplit.trace_all`)

**Trace-free reconstructed class field.** A finite modal reconstruction is trace-free whenever each of its matrix modes is trace-free. (`Breakdown.FracInternal.ClassProductSplit.classField_trace`)

**Class interaction from zero trace.** For valid form and cell data at an interior point off the axis, a trace-free reconstructed class field gives the stated lower bound for paired mode interactions by the two class-loss sums. (`Breakdown.CellCert.CellAnalysis.classProductSplit_of_trace`)

**Class split requirement.** For 1 < α < 5/4, valid form and cell data must give the class-loss lower bound for every finite paired mode collection at almost every interior point off the axis. (`Breakdown.CellCert.CellAnalysis.ClassProductSplitAeStatement`)

Proved by `Breakdown.CellCert.CellAnalysis.classProductSplitAe_holds`.

**Class bound almost everywhere.** For 1 < α < 5/4, valid form and cell data give the class-loss lower bound for every finite paired mode collection at almost every interior point off the axis. (`Breakdown.CellCert.CellAnalysis.classProductSplitAe_holds`)

### Breakdown.FracCell.ClassRowSq

This file uses angular orthogonality and cylindrical integration to bound the class-restricted row-mode square by the corresponding finite row coefficient energy.

**Periodic positive angular phase.** Adding a full turn leaves each positive angular exponential unchanged. (`Breakdown.FracInternal.ClassRowSq.pos_phase_per`)

**Angular phase orthogonality.** At symmetry order at least one, the normalized integral of one phase times the conjugate of another is one for equal modes and zero otherwise. (`Breakdown.FracInternal.ClassRowSq.orth_circ`)

**Shift the integration period.** A 2π-periodic real function has equal integrals over the full-turn interval and over (−π, π). (`Breakdown.FracInternal.ClassRowSq.per_real`)

**Bound selected Fourier squares.** At symmetry order at least one, any finite sum of squared coefficients of an L² angular function is at most its normalized square integral. (`Breakdown.FracInternal.ClassRowSq.coef_sq_le_circ`)

**Frame coordinates preserve the norm.** The sum of the three squared cylindrical frame components equals the squared vector norm. (`Breakdown.FracInternal.ClassRowSq.frame_sq`)

**Frame coordinates preserve finite sums.** Taking a cylindrical frame component commutes with a finite real linear combination of vectors. (`Breakdown.FracInternal.ClassRowSq.frame_lin`)

**Measurable angle and field pairs.** Pairing the angle with an almost everywhere measurable angular vector field preserves almost everywhere strong measurability. (`Breakdown.FracInternal.ClassRowSq.circ_pair`)

**Measurable angular frame components.** The complex-valued cylindrical frame components of a measurable angular vector field are measurable. (`Breakdown.FracInternal.ClassRowSq.frame_meas`)

**Measurable velocity mode integrands.** Each velocity-mode kernel of a measurable angular vector field is measurable. (`Breakdown.FracInternal.ClassRowSq.kernel_meas`)

**Frame component bounded by the norm.** The norm of a complex-valued cylindrical frame component is at most the original vector norm. (`Breakdown.FracInternal.ClassRowSq.frame_norm_le`)

**Square integrable frame components.** Each complex-valued cylindrical frame component of an L² angular vector field is square integrable. (`Breakdown.FracInternal.ClassRowSq.frame_memLp`)

**Mode of a finite row combination.** For square integrable angular row slices, the weighted sum of their modes equals the normalized Fourier coefficient of their finite real linear combination. (`Breakdown.FracInternal.ClassRowSq.lin_mode`)

**Bound modal squares of combined rows.** At symmetry order at least one, selected modal squares of a finite real row combination are bounded by the normalized angular square integral of that combination when the row slices are L². (`Breakdown.FracInternal.ClassRowSq.point_bound`)

**Integrable cylindrical square density.** A globally square integrable vector field has an integrable radius-weighted square density in cylindrical coordinates. (`Breakdown.FracInternal.ClassRowSq.cyl_int`)

**Square integrable circles almost surely.** A globally square integrable vector field has square integrable angular slices at almost every positive radius and height. (`Breakdown.FracInternal.ClassRowSq.circ_memLp`)

**Integrable angular energy on a cell.** For a valid cell and globally square integrable vector field, the radius-weighted angular square integral is integrable on the cell rectangle. (`Breakdown.FracInternal.ClassRowSq.circ_integrable`)

**Measurable velocity modes on a cell.** For a valid cell and measurable vector field, every velocity-mode component is measurable on the cell rectangle. (`Breakdown.FracInternal.ClassRowSq.mv_meas`)

**Integrable vector pairings.** The inner product of two square integrable vector fields is integrable. (`Breakdown.FracInternal.ClassRowSq.inner_int`)

**Class row square bound.** For 1 < α < 5/4, valid form and cell data with an axisymmetric weight give an integrable radius-weighted class row square whose integral is at most the selected row coefficient squares divided by 4π. (`Breakdown.CellCert.CellAnalysis.classRowSq_holds`)

### Breakdown.FracCell.ConjugateData

This file supplies the conjugation identities for the mode coefficients, face moments and corner data used to assemble real cell forms from complex harmonics.

**Conjugation through an interval integral.** Complex conjugation commutes with the oriented interval integral. (`Breakdown.CellCert.CellFormula.ConjugateDataInternal.conj_intervalIntegral`)

**Conjugation reverses the harmonic.** Conjugating the angular coefficient of a real field replaces the mode index by its negative. (`Breakdown.CellCert.CellFormula.ConjugateDataInternal.conj_angle`)

**The edge sign is real.** Complex conjugation leaves the edge sign unchanged. (`Breakdown.CellCert.CellFormula.ConjugateDataInternal.conj_edgeSign`)

**Conjugate a radial strip moment.** Conjugating a radial strip moment conjugates its field and radial derivative. (`Breakdown.CellCert.CellFormula.ConjugateDataInternal.conj_radialStrip`)

**Conjugate a height strip moment.** Conjugating a height strip moment conjugates its field and height derivative while retaining the real weight. (`Breakdown.CellCert.CellFormula.ConjugateDataInternal.conj_heightStrip`)

**Conjugate a corner moment.** Conjugating a corner moment conjugates all four field and derivative inputs. (`Breakdown.CellCert.CellFormula.ConjugateDataInternal.conj_corner`)

**Conjugate a face moment.** A face-segment moment commutes with conjugation of its three field inputs. (`Breakdown.CellCert.CellFormula.ConjugateDataInternal.conj_segMoment`)

**Conjugate a cell coefficient.** Conjugating a cell basis coefficient is the same as taking the coefficient of the conjugate field. (`Breakdown.CellCert.CellFormula.ConjugateDataInternal.conj_coef`)

**Opposite velocity modes.** The velocity mode at the negative index is the conjugate of the original mode. (`Breakdown.CellCert.CellFormula.ConjugateDataInternal.velMode_neg`)

**Opposite gradient modes.** The gradient mode at the negative index is the conjugate of the original mode. (`Breakdown.CellCert.CellFormula.ConjugateDataInternal.gradModeOf_neg`)

**Opposite second-derivative modes.** The second-derivative mode at the negative index is the conjugate of the original mode. (`Breakdown.CellCert.CellFormula.ConjugateDataInternal.secondModeOf_neg`)

**Opposite pressure-gradient modes.** The pressure-gradient mode at the negative index is the conjugate of the original mode. (`Breakdown.CellCert.CellFormula.ConjugateDataInternal.pressureGradMode_neg`)

**Opposite pressure modes.** The pressure mode at the negative index is the conjugate of the original mode. (`Breakdown.CellCert.CellFormula.ConjugateDataInternal.pressMode_neg`)

**Opposite extra trace values.** Each extra trace value at the negative mode index is the conjugate of its original value. (`Breakdown.CellCert.CellFormula.ConjugateDataInternal.extraValue_neg`)

**Conjugate cell data.** For a valid pressure layout and an admissible input, selecting the conjugate datum gives the complex conjugate of the original true-data value. (`Breakdown.CellCert.CellFormula.conjugateData_holds`)

### Breakdown.FracCell.CornerIndependence

This file makes the corner values independent of the auxiliary integration rectangle, using the weak mixed-derivative identities from the companion file.

**Corner moment as a rectangle integral.** The corner moment is the rectangle integral of the corner integrand multiplied by the two orientation signs. (`_private.Breakdown.FracCell.CornerIndependence.0.Breakdown.CellCert.CellFormula.cornerMoment_eq_term`)

**Integrability of the corner integrand.** For a weak mixed-derivative quadruple, the corner integrand is integrable when the radial lower bound is positive or the opposite radius is zero. (`_private.Breakdown.FracCell.CornerIndependence.0.Breakdown.CellCert.CellFormula.cornerTerm_integrableOn`)

**Move the opposite radial endpoint.** For a weak mixed-derivative quadruple, opposite radial endpoints on either side of the corner give the same corner moment. (`_private.Breakdown.FracCell.CornerIndependence.0.Breakdown.CellCert.CellFormula.cornerMoment_radial_move`)

**Move the opposite height endpoint.** For a weak mixed-derivative quadruple, opposite height endpoints on either side of the corner give the same corner moment. (`_private.Breakdown.FracCell.CornerIndependence.0.Breakdown.CellCert.CellFormula.cornerMoment_height_move`)

**Normalize the corner rectangle.** Under the stated nondegeneracy and nonnegative-radius conditions, the corner moment equals the one whose opposite endpoints are one unit above the corner coordinates. (`_private.Breakdown.FracCell.CornerIndependence.0.Breakdown.CellCert.CellFormula.corner_normal`)

**Corner values are independent.** For an admissible input and a layout with matching symmetry order, the corner moment of each velocity mode and its mixed derivatives is unchanged when the opposite rectangle endpoints change, provided the corner radius is nonzero, both rectangles are nondegenerate and their radial coordinates are nonnegative. (`Breakdown.CellCert.CellFormula.cornerIndependence_holds`)

### Breakdown.FracCell.CornerIndependenceParts

This file constructs smooth tent approximations and passes weak derivative identities to rectangular corner formulas, including rectangles that reach the axis.

**The piecewise linear tent.** The tent is the positive part of the smaller of its rising and falling affine sides. (`Breakdown.FracInternal.CornerParts.tentFn`)

**The slope of the tent.** Inside the closed support interval the tent slope is the reciprocal signed distance to the selected endpoint, and outside it is zero. (`Breakdown.FracInternal.CornerParts.tentSlope`)

**Shrinking smooth bumps.** The bump sequence has outer radius one over n plus two and inner radius half that size. (`Breakdown.FracInternal.CornerParts.bumpSeq`)

**Smooth the tent by convolution.** The smoothed tent is the convolution of the tent with the normalized shrinking bump. (`Breakdown.FracInternal.CornerParts.mollTent`)

**Slope of the rising affine side.** The rising affine function has Lipschitz constant equal to the absolute reciprocal denominator. (`Breakdown.FracInternal.CornerParts.slope_left`)

**Slope of the falling affine side.** The falling affine function has Lipschitz constant equal to the absolute reciprocal denominator. (`Breakdown.FracInternal.CornerParts.slope_right`)

**The tent is Lipschitz.** Every tent function admits a finite Lipschitz constant. (`Breakdown.FracInternal.CornerParts.tent_slope`)

**The tent is continuous.** Every tent function is continuous. (`Breakdown.FracInternal.CornerParts.tent_cont`)

**The tent vanishes outside its support.** For ordered endpoints, the tent vanishes outside the open interval between them. (`Breakdown.FracInternal.CornerParts.tent_zero`)

**The tent on its support interval.** On the closed support interval, the tent equals the affine side selected by its position relative to the peak. (`Breakdown.FracInternal.CornerParts.tent_eq_on`)

**The tent is locally affine.** Away from its endpoints and peak, the tent is affine on a small ball with slope given by the tent-slope function. (`Breakdown.FracInternal.CornerParts.tent_local`)

**Outer radius of a shrinking bump.** The nth bump has outer radius one over n plus two. (`Breakdown.FracInternal.CornerParts.bump_rOut`)

**Integral formula for the smoothed tent.** The smoothed tent evaluates as the integral of the normalized bump times the translated tent. (`Breakdown.FracInternal.CornerParts.moll_apply`)

**A bump times a continuous function.** Multiplying a continuous function by a normalized compact bump gives an integrable function. (`Breakdown.FracInternal.CornerParts.bump_mul_int`)

**The smoothed tent is smooth.** Every smoothed tent is infinitely differentiable. (`Breakdown.FracInternal.CornerParts.moll_smooth`)

**Smoothing preserves the slope bound.** Convolution with the normalized bump preserves any Lipschitz bound on the tent. (`Breakdown.FracInternal.CornerParts.moll_slope`)

**Support of a smoothed tent.** The smoothed tent vanishes outside the support interval enlarged by the bump radius. (`Breakdown.FracInternal.CornerParts.moll_zero_of`)

**The tent and its derivative vanish.** Outside a slightly larger interval, both the smoothed tent and its derivative are zero. (`Breakdown.FracInternal.CornerParts.moll_vanish`)

**The bump radii tend to zero.** The outer radii of the shrinking bumps converge to zero. (`Breakdown.FracInternal.CornerParts.rOut_tendsto`)

**Smoothed tents converge pointwise.** The smoothed tents converge at every point to the original tent. (`Breakdown.FracInternal.CornerParts.moll_tendsto`)

**Smoothed slopes converge off corners.** Away from the endpoints and peak, the derivatives of the smoothed tents converge to the tent slope. (`Breakdown.FracInternal.CornerParts.moll_deriv_tendsto`)

**A vertical line has measure zero.** Almost every point of the plane has first coordinate different from a prescribed number. (`Breakdown.FracInternal.CornerParts.ae_fst_ne`)

**A horizontal line has measure zero.** Almost every point of the plane has second coordinate different from a prescribed number. (`Breakdown.FracInternal.CornerParts.ae_snd_ne`)

**Pass a weak identity to the limit.** Uniform bounds, support control and the stated convergence assumptions pass the paired integral identity to its limiting test functions. (`Breakdown.FracInternal.CornerParts.limit_core`)

**Derivatives of a product test.** The radial and height derivatives of a separated product test differentiate the corresponding one-dimensional factor. (`Breakdown.FracInternal.CornerParts.fderiv_prod_apply`)

**Enclose compact support symmetrically.** A compactly supported real function has support in some symmetric closed interval. (`Breakdown.FracInternal.CornerParts.tsupp_sym`)

**Vanishing beyond a symmetric interval.** A compactly supported real function vanishes outside some symmetric closed interval. (`Breakdown.FracInternal.CornerParts.sym_bound`)

**Compact support away from the axis.** Compact support confined to positive radii lies in an interval with a positive lower endpoint. (`Breakdown.FracInternal.CornerParts.pos_bound`)

**Bounds on smoothed tents and slopes.** A Lipschitz bound on the tent controls the smoothed tent by the support length plus two and controls its derivative by the same Lipschitz constant. (`Breakdown.FracInternal.CornerParts.moll_bound`)

**Smoothed tents have compact support.** For ordered endpoints, every smoothed tent has compact support. (`Breakdown.FracInternal.CornerParts.moll_hasCompactSupport`)

**Reciprocal radii eventually shrink.** For every positive tolerance, one over n plus one is eventually below that tolerance. (`Breakdown.FracInternal.CornerParts.small_eventually`)

**Test a radial derivative with a tent.** The radial weak derivative identity extends to a radial tent times a smooth compact height test away from the axis. (`Breakdown.FracInternal.CornerParts.radial_core`)

**Test a height derivative with a tent.** The height weak derivative identity extends to a height tent times a smooth compact radial test supported away from the axis. (`Breakdown.FracInternal.CornerParts.height_core`)

**The tent slope is measurable.** The piecewise constant tent-slope function is measurable. (`Breakdown.FracInternal.CornerParts.tentSlope_meas`)

**A bound on the tent slope.** The absolute tent slope is at most the sum of the two absolute reciprocal side lengths. (`Breakdown.FracInternal.CornerParts.tentSlope_bound`)

**The tent has a uniform bound.** A tent with strictly ordered endpoints is bounded on the real line. (`Breakdown.FracInternal.CornerParts.tentFn_bound`)

**Both tent functions vanish outside.** Both the tent and its slope vanish outside the closed support interval. (`Breakdown.FracInternal.CornerParts.tent_out`)

**Integrability after bounded cutoffs.** Bounded measurable coordinate cutoffs supported in a rectangle turn a function integrable on that rectangle into a globally integrable product. (`Breakdown.FracInternal.CornerParts.int_region`)

**Remove interior test functions.** If an integrable rectangle function pairs to zero with every smooth compact interior radial test, its rectangle integral is zero. (`Breakdown.FracInternal.CornerParts.slice_zero`)

**Compact continuous functions are bounded.** A continuous compactly supported real function has a uniform absolute bound. (`Breakdown.FracInternal.CornerParts.bdd_of_csupp`)

**Rectangle measure within the half-plane.** Lebesgue measure restricted to the radial-height rectangle is dominated by its restriction to the positive radial half-plane. (`Breakdown.FracInternal.CornerModes.half_le`)

**Angular averages are measurable.** A continuous angular functional of an almost-everywhere measurable field has an almost-everywhere measurable cylindrical average. (`Breakdown.FracInternal.CornerModes.kmeas`)

**Cylindrical nonnegative integration.** Integrating the angular average with radial Jacobian over the positive half-plane recovers the whole-space nonnegative integral. (`Breakdown.FracInternal.CornerModes.half_eq`)

**Weighted angular averages integrate.** For a locally integrable field, a continuous angular functional bounded by its norm has a radially weighted average integrable on each bounded rectangle. (`Breakdown.FracInternal.CornerModes.weighted_int`)

**A sixth-power radial bound.** For positive radius and nonnegative t, t is at most the reciprocal fifth-root radius plus radius times the sixth power of t. (`Breakdown.FracInternal.CornerModes.root_power_bound`)

**The angular functional power bound.** A norm-bounded angular functional satisfies the corresponding extended-norm sixth-power estimate at positive radius. (`Breakdown.FracInternal.CornerModes.pt_bound`)

**Velocity averages integrate at the axis.** An L6 velocity has integrable norm-bounded angular averages on rectangles that include the axis. (`Breakdown.FracInternal.CornerModes.vel_int`)

**Remove a positive radial weight.** Integrability with radial weight and measurability imply unweighted integrability on rectangles bounded away from the axis. (`Breakdown.FracInternal.CornerModes.off_int`)

**Entry-square control gives L2.** An almost-everywhere measurable matrix field with integrable entry square belongs to L2. (`Breakdown.FracInternal.CornerModes.memLp_grad`)

**A mixed mode as an axial gradient.** The indicated mixed second-derivative mode equals the radial gradient mode of the axial contraction. (`Breakdown.FracInternal.CornerModes.third_eq`)

**Axial contraction is measurable.** Contracting an almost-everywhere measurable second-derivative field with the axial unit vector preserves measurability. (`Breakdown.FracInternal.CornerModes.axial_meas`)

**Axial contraction has finite energy.** Integrable squared coordinate values of a second-derivative field give an integrable entry square for its axial contraction. (`Breakdown.FracInternal.CornerModes.axial_sq`)

**Use height-mode integrability.** The height-axis interface gives integrability of an admissible field's height-gradient mode on each bounded rectangle. (`Breakdown.CellCert.CellFormula.modes_integrable_height_axis_of`)

**Use the four weak mode identities.** The weak-mode interface gives the two first-derivative and two mixed-derivative integration-by-parts identities for admissible fields. (`Breakdown.CellCert.CellFormula.modes_weak_identities_of`)

**Weighted mode integrability.** Admissible fields have integrable velocity modes and radially weighted radial and mixed-derivative modes on bounded rectangles. (`Breakdown.CellCert.CellFormula.modes_integrable_weighted`)

**Height modes integrate at the axis.** The height-gradient mode of an admissible field is integrable on rectangles that reach the axis. (`Breakdown.CellCert.CellFormula.modes_integrable_height_axis`)

**Derivative modes integrate off the axis.** Radial and mixed-derivative modes of an admissible field are integrable on rectangles with positive lower radius. (`Breakdown.CellCert.CellFormula.modes_integrable_off`)

**The four weak mode identities.** Admissible fields satisfy the four radial, height and mixed-derivative weak identities for compact tests away from the axis. (`Breakdown.CellCert.CellFormula.modes_weak_identities`)

**A weak mixed-derivative quadruple.** The predicate requires local weighted and unweighted integrability together with four weak derivative identities for the field and its radial, height and mixed derivatives. (`Breakdown.CellCert.CellFormula.IsMixedWeakQuad`)

**Build the weak mode quadruple.** The velocity, radial-gradient, height-gradient and mixed-derivative modes of an admissible field form a weak mixed-derivative quadruple. (`Breakdown.CellCert.CellFormula.modes_mixedWeak_of_parts`)

**Build the quadruple from interfaces.** The height-axis and weak-identity interfaces supply the weak mixed-derivative quadruple for an admissible field's modes. (`Breakdown.CellCert.CellFormula.modes_mixedWeak_of_statements`)

**The corner integrand.** The corner integrand combines the field and its three derivatives with the four affine rectangle weights. (`Breakdown.CellCert.CellFormula.cornerTerm`)

**The complete weak mode quadruple.** Every admissible field's selected modes satisfy the weak mixed-derivative predicate. (`Breakdown.CellCert.CellFormula.modes_mixedWeak`)

**Integrable field and height derivative.** A weak mixed-derivative quadruple has integrable field and height derivative on each rectangle bounded away from the axis. (`_private.Breakdown.FracCell.CornerIndependenceParts.0.Breakdown.CellCert.CellFormula.quad_F`)

**The height tent cancels.** The corner integrand with its opposite height selected across the peak has zero rectangle integral under the weak mixed-derivative and geometry assumptions. (`Breakdown.CellCert.CellFormula.height_tent_zero`)

**The radial tent cancels off the axis.** The corner integrand with its opposite radius selected across the peak has zero rectangle integral when the lower radius is positive. (`_private.Breakdown.FracCell.CornerIndependenceParts.0.Breakdown.CellCert.CellFormula.radial_pos`)

**Measurability of the corner integrand.** Measurable field inputs and a measurable choice of opposite radius give an almost-everywhere measurable corner integrand. (`_private.Breakdown.FracCell.CornerIndependenceParts.0.Breakdown.CellCert.CellFormula.corner_aesm`)

**The radial tent cancels at the axis.** The radial tent cancellation remains valid when the lower radial endpoint is zero. (`_private.Breakdown.FracCell.CornerIndependenceParts.0.Breakdown.CellCert.CellFormula.radial_zero`)

**The complete radial cancellation.** The radial tent corner integral is zero for nonnegative lower radius and distinct corner and opposite heights. (`Breakdown.CellCert.CellFormula.radial_tent_zero`)

### Breakdown.FracCell.CrossIdentity

This file reduces the cross-product identity used in the cell quadratic form to coordinate identities for linear maps and their adjoints.

**Expand a vector in coordinates.** Every spatial vector is the sum of its three coordinate multiples of the unit vectors. (`Breakdown.CellCert.CrossIdentityInternal.vec_eq`)

**Coordinates of a linear map.** Each coordinate of a linear map applied to a vector is the corresponding matrix row paired with that vector. (`Breakdown.CellCert.CrossIdentityInternal.apply_coord`)

**Coordinates of the adjoint.** Each coordinate of the adjoint applied to a vector is the corresponding matrix column paired with that vector. (`Breakdown.CellCert.CrossIdentityInternal.adjoint_coord`)

**The cell cross-product identity.** Applying each of two linear maps to the opposite vector and adding gives the sum of their two curl cross products and two adjoint-map terms. (`Breakdown.CellCert.crossIdentity`)

### Breakdown.FracCell.CylChange

This file supplies the cylindrical change of variables used to convert whole-space weak identities to the radial-height plane.

**Change to cylindrical coordinates.** For an integrable complex field on space, its spatial integral equals the integral over positive radius and all heights of radius times its full-turn angular integral. (`Breakdown.CellCert.CellFormula.cylChange`)

### Breakdown.FracCell.CylIntegral

This file proves cylindrical integration with its radial Jacobian, while accounting for the excluded axis and angular seam as null sets.

**Cartesian coordinate identification.** The measurable equivalence identifies a planar coordinate pair and height with the three-dimensional Euclidean space. (`Breakdown.CellCert.Spectral.Internal.CylIntegral.toSpace`)

**Coordinate map preserves volume.** The Cartesian coordinate identification preserves Lebesgue measure. (`Breakdown.CellCert.Spectral.Internal.CylIntegral.toSpace_mp`)

**Identify a cylindrical point.** Applying the coordinate identification to the polar planar pair and height gives the cylindrical point. (`Breakdown.CellCert.Spectral.Internal.CylIntegral.toSpace_apply`)

**The cylindrical coordinate chart.** The cylindrical chart is the planar polar chart paired with the identity on height. (`Breakdown.CellCert.Spectral.Internal.CylIntegral.cylMap`)

**Derivative of the inverse chart.** The specified cylindrical derivative combines the inverse polar derivative with the identity in height. (`Breakdown.CellCert.Spectral.Internal.CylIntegral.cylDeriv`)

**Differentiate the inverse chart.** The inverse cylindrical chart has the specified Fréchet derivative. (`Breakdown.CellCert.Spectral.Internal.CylIntegral.hasDeriv`)

**The cylindrical Jacobian.** The determinant of the inverse-chart derivative is the radial coordinate. (`Breakdown.CellCert.Spectral.Internal.CylIntegral.det_cylDeriv`)

**Domain of cylindrical coordinates.** The target of the cylindrical chart is the polar target paired with all heights. (`Breakdown.CellCert.Spectral.Internal.CylIntegral.cylMap_target`)

**The chart covers almost every point.** The image of the chart's inverse covers the Cartesian space up to a null set. (`Breakdown.CellCert.Spectral.Internal.CylIntegral.image_ae`)

**Absolute Jacobian in the chart.** Within the chart target, the absolute Jacobian determinant equals the radial coordinate. (`Breakdown.CellCert.Spectral.Internal.CylIntegral.abs_det_eq`)

**The cylindrical integral formula.** Changing a real integral to the cylindrical chart introduces the radial Jacobian. (`Breakdown.CellCert.Spectral.Internal.CylIntegral.change`)

**Integrability after the chart change.** An integrable real function remains integrable on the chart target after composition and multiplication by the radial Jacobian. (`Breakdown.CellCert.Spectral.Internal.CylIntegral.change_integrable`)

**Exchange height and angle.** The measurable equivalence exchanges the height and angular coordinates while retaining the radius. (`Breakdown.CellCert.Spectral.Internal.CylIntegral.swapEquiv`)

**The coordinate swap preserves volume.** Exchanging height and angle preserves product Lebesgue measure. (`Breakdown.CellCert.Spectral.Internal.CylIntegral.swapEquiv_mp`)

**Evaluate the coordinate swap.** The coordinate swap takes radius-height-angle order to radius-angle-height order. (`Breakdown.CellCert.Spectral.Internal.CylIntegral.swapEquiv_apply`)

**The chart after the coordinate swap.** After the swap, the chart target is positive radius, arbitrary height and angle strictly between minus pi and pi. (`Breakdown.CellCert.Spectral.Internal.CylIntegral.swapEquiv_preimage`)

**Cylindrical integration.** The integral of an integrable real spatial function equals the integral over positive radius and all heights of radius times its angular integral from −π to π. (`Breakdown.CellCert.Spectral.cylIntegral`)

### Breakdown.FracCell.CylModeWeak

This file derives the weak equation for cylindrical Fourier modes by constructing polynomial angular tests and applying the axis weak identity.

**A polynomial angular weight.** The angular weight raises the two conjugate planar coordinate combinations to the nonnegative exponents given by the positive and negative parts of the integer frequency. (`_private.Breakdown.FracCell.CylModeWeak.0.Breakdown.CellCert.CellFormula.pw`)

**The angular weight is smooth.** The polynomial angular weight is infinitely differentiable on the coordinate plane. (`_private.Breakdown.FracCell.CylModeWeak.0.Breakdown.CellCert.CellFormula.pw_smooth`)

**Angular weight on the unit circle.** On the unit circle, the polynomial weight equals the complex exponential with negative integer frequency. (`_private.Breakdown.FracCell.CylModeWeak.0.Breakdown.CellCert.CellFormula.pw_circle`)

**A weighted linear angular test.** The angular test multiplies a real linear functional by the complex polynomial angular weight. (`_private.Breakdown.FracCell.CylModeWeak.0.Breakdown.CellCert.CellFormula.wt`)

**Recover the positive radius.** The cylindrical radius of a point with positive input radius equals that input radius. (`_private.Breakdown.FracCell.CylModeWeak.0.Breakdown.CellCert.CellFormula.rad_cyl`)

**Recover the angular ratios.** At positive radius, the normalized first two coordinates are cosine and sine of the angle, and the third coordinate is the height. (`_private.Breakdown.FracCell.CylModeWeak.0.Breakdown.CellCert.CellFormula.cyl_ratio`)

**Pull an angular integral to the plane.** The cylindrical-change interface converts an integrable weighted spatial function into its full-circle angular integral over the radial-height plane. (`_private.Breakdown.FracCell.CylModeWeak.0.Breakdown.CellCert.CellFormula.cylPull`)

**Equality on positive radii suffices.** Two angular integrands equal at positive radius have equal plane integrals against a weight supported there. (`_private.Breakdown.FracCell.CylModeWeak.0.Breakdown.CellCert.CellFormula.congr_p`)

**Positive support implies positive radius.** A function whose closed support has positive radius can be nonzero only at positive radius. (`_private.Breakdown.FracCell.CylModeWeak.0.Breakdown.CellCert.CellFormula.supp_of`)

**Build the weak cylindrical mode law.** The cylindrical change-of-variables and axis-weak statements give the radial and height integration-by-parts identities for every angular Fourier mode of a locally integrable finite-dimensional field with a locally integrable weak gradient, against smooth compactly supported tests away from the axis. (`Breakdown.CellCert.CellFormula.cylModeWeak_of`)

**The weak cylindrical mode law.** A locally integrable finite-dimensional field and its locally integrable weak gradient give the stated radial and height weak identities for all angular Fourier modes, using smooth angular functionals and smooth compactly supported radial-height tests away from the axis. (`Breakdown.CellCert.CellFormula.cylModeWeak`)

### Breakdown.FracCell.CylinderComp

This file justifies composing measurable fields with cylindrical coordinates, using shifts, reflection and the null axis and angular seams.

**Angular shifts preserve volume.** Subtracting a fixed angle in the product coordinate space preserves Lebesgue measure. (`Breakdown.CellCert.CellAnalysis.CylinderCompInternal.shift_mp`)

**Radius reflection preserves volume.** Reflecting the radius and shifting the angle preserves product Lebesgue measure. (`Breakdown.CellCert.CellAnalysis.CylinderCompInternal.flip_mp`)

**The cylindrical axis is null.** The subset with zero radial coordinate has zero product Lebesgue measure. (`Breakdown.CellCert.CellAnalysis.CylinderCompInternal.axis_null`)

**The angular seams are null.** The union of angular levels at integer multiples of pi has zero product Lebesgue measure. (`Breakdown.CellCert.CellAnalysis.CylinderCompInternal.angle_null`)

**Cylindrical coordinates preserve nullity.** The cylindrical argument map is quasi-measure-preserving on the full product coordinate space. (`Breakdown.CellCert.CellAnalysis.CylinderCompInternal.qmp_full`)

**Compose with cylindrical coordinates.** Composing an almost everywhere strongly measurable matrix field with cylindrical coordinates preserves almost everywhere strong measurability on the full radial-height-angle product space. (`Breakdown.CellCert.CellAnalysis.cylinderComp`)

### Breakdown.FracCell.CylinderFlux

This file organizes divergence-free mode traces and radial-strip traces into the flux identity for a cylinder in the cell analysis.

**Zero trace of each gradient mode.** The interface requires the diagonal sum of each gradient mode of a second-order field to vanish almost everywhere at positive radius. (`Breakdown.CellCert.CellFormula.ModeTraceStatement`)

Proved by `Breakdown.CellCert.CellFormula.modeTrace`.

**The radial strip trace law.** The interface requires a trace function whose endpoint difference represents every affine-weighted radial strip integral of the zero mode. (`Breakdown.CellCert.CellFormula.StripTraceStatement`)

Proved by `Breakdown.CellCert.CellFormula.stripTrace_holds`.

**The radial flux law.** The interface equates radius times a radial strip moment with the interior integral of the radial velocity mode plus radius times its radial derivative. (`Breakdown.CellCert.CellFormula.RadialFluxStatement`)

Proved from further statements by `Breakdown.CellCert.CellFormula.radialFlux_of`.

**Almost every radius is nonzero.** Almost every point of the radial-height plane has nonzero radial coordinate. (`Breakdown.CellCert.CellFormula.Internal.CylinderFlux.axis_ae`)

**Subtract the two height traces.** For integrable field and height derivative, the difference of the weighted top and bottom strip moments equals the radially weighted derivative integral. (`Breakdown.CellCert.CellFormula.Internal.CylinderFlux.heightDiff`)

**Factor the cylindrical region measure.** The restricted cylindrical region measure is the product of the positive-half-plane measure and the open angular interval measure. (`Breakdown.CellCert.CellFormula.Internal.CylinderFlux.region_eq`)

**Pass almost-everywhere facts to circles.** A spatial almost-everywhere property holds at almost every angle on almost every circle of positive radius. (`Breakdown.CellCert.CellFormula.Internal.CylinderFlux.slice_ae`)

**Measurable slices on almost every circle.** An almost-everywhere measurable gradient field has measurable angular slices for almost every radial-height point of positive radius. (`Breakdown.CellCert.CellFormula.Internal.CylinderFlux.slice_aesm`)

**Finite energy on almost every circle.** Integrable entry-square energy gives finite angular entry-square energy on almost every positive-radius circle. (`Breakdown.CellCert.CellFormula.Internal.CylinderFlux.slice_lint`)

**Entry square is continuous.** The sum of squared matrix entries depends continuously on the linear map. (`Breakdown.CellCert.CellFormula.Internal.CylinderFlux.entrySq_cont`)

**A norm bound from entry square.** The operator norm of a spatial linear map is at most one plus its entry square. (`Breakdown.CellCert.CellFormula.Internal.CylinderFlux.norm_le_entry`)

**Integrability of a gradient-mode slice.** A measurable angular slice with finite entry-square integral has an integrable gradient-mode kernel. (`Breakdown.CellCert.CellFormula.Internal.CylinderFlux.slice_int`)

**Rewrite the affine strip weight.** The radial strip weight can be rewritten as a constant coefficient on the field plus an affine coefficient on its derivative. (`Breakdown.CellCert.CellFormula.Internal.CylinderFlux.strip_eq`)

**Radial flux from strip traces.** The radial-strip trace statement identifies positive radius times the zero-mode radial strip moment with the rectangle integral of the radial velocity mode plus radius times its radial gradient mode for a second-order field, with nonnegative distinct reference radius and strictly ordered heights. (`Breakdown.CellCert.CellFormula.radialFlux_of`)

**Gradient modes have zero trace.** For every second-order field, the diagonal sum of each gradient mode vanishes at almost every positive-radius point in the radial-height plane. (`Breakdown.CellCert.CellFormula.modeTrace`)

**Assemble cylinder flux.** The strip-integrability, angular-mode and strip-trace statements make the radius-weighted lateral zero-mode flux plus upper axial flux minus lower axial flux vanish for every second-order field on a cylinder of positive radius, with nonnegative distinct reference radius and strictly ordered heights. (`Breakdown.CellCert.CellFormula.cylinderFlux_of`)

### Breakdown.FracCell.Defs

This file defines the fractional cell quadratic form and the complete analytic cell hypothesis, connecting cell estimates to the fractional certificate data.

**Squared curl-gradient size.** The curl-gradient square sums the squares of the alternating second-derivative coordinate combinations. (`Breakdown.CellCert.curlGradSq`)

**Squared full second derivative.** The full second-derivative square sums squared norms over all coordinate directions. (`Breakdown.CellCert.fullSecondSq`)

**The stretching cross form.** The cross form combines strain acting on curl with the velocity and curl-gradient couplings against the gradient entries. (`Breakdown.CellCert.jForm`)

**The smoothing variational form.** The smoothing form is the infimum of the squared L2 approximation error plus inverse-scale weak-gradient energy over admissible L2 approximants. (`Breakdown.CellCert.smoothingForm`)

**The cell model field.** The model field combines similarity drift, split viscosity, the two curl couplings and the actuator sum. (`Breakdown.CellCert.FracCellData.modelFieldOf`)

**The cell model quadratic form.** The model form adds weighted derivative energies, stretching and actuator-gradient pairings with the specified cell coefficients. (`Breakdown.CellCert.FracCellData.formOf`)

**The model pin functional.** Each model pin is the pin pairing of the corresponding model pin field with the supplied gradient. (`Breakdown.CellCert.FracCellData.pinOf`)

**The corrected cell quadratic form.** The corrected form subtracts the coercive energy from the model form and adds row and pin squares while subtracting the multiplier penalty. (`Breakdown.CellCert.FracCellData.quadForm`)

**Choose a weak gradient.** The selected gradient is chosen from a second-order field witness when one exists and is zero otherwise. (`Breakdown.CellCert.FracCellData.chosenGrad`)

**Choose a weak second derivative.** The selected second derivative comes from the same chosen second-order witness and is zero when no such witness exists. (`Breakdown.CellCert.FracCellData.chosenSecond`)

**Convert cell data to certificate data.** The conversion installs the model form, model field and model pins evaluated using the selected weak derivatives. (`Breakdown.CellCert.FracCellData.toCertData`)

**The fractional certificate base.** The proposition structure collects positivity, regularity, symmetry, decay, row, contraction, adjoint and parameter-box bounds for fractional certificate data. (`Breakdown.CellCert.IsFracCertBase`)

**The full fractional cell hypothesis.** The proposition structure adds cell geometry, model data, nonnegative quadratic form, approximation losses and spectral bounds to the fractional certificate base. (`Breakdown.CellCert.IsFracCell`)

**Existence of fractional cell data.** The fractional cell-certificate hypothesis asserts that some finite-dimensional cell data satisfy the full cell hypothesis at the specified exponent. (`Breakdown.CellCert.FracCellCertificateHypothesis`)

### Breakdown.FracCell.DensitySlice

This file uses Parseval identities on circles to express the cell density and pin and actuator pairings through Fourier modes in the cylindrical frame.

**Parseval for an interval pairing.** For two L2 functions on an interval of positive length, the sum of paired Fourier coefficients equals their normalized integral pairing. (`Breakdown.FracInternal.DensitySlice.pair_modeCoeffOn`)

**The full-circle Fourier coefficient.** The circle coefficient is the angular exponential integral divided by two pi. (`Breakdown.FracInternal.DensitySlice.circleCoeff`)

**The circle length is positive.** The full-circle length, two pi, is positive. (`Breakdown.FracInternal.DensitySlice.circle_len_pos`)

**Circle and interval Fourier coefficients.** At integer frequency, the circle coefficient equals the interval Fourier coefficient on the full circle. (`Breakdown.FracInternal.DensitySlice.circleCoeff_eq`)

**Rotation kills incompatible harmonics.** A periodic function invariant almost everywhere under the m-fold turn has zero coefficient at integer frequencies not divisible by positive m. (`Breakdown.FracInternal.DensitySlice.circleCoeff_shift`)

**Parseval on the allowed harmonics.** For L2 circle functions with the stated periodicity and turn symmetry, the allowed-harmonic coefficient pairing sums to the normalized angular pairing. (`Breakdown.FracInternal.DensitySlice.circle_modes`)

**Expand a vector in the unit basis.** Every spatial vector equals the finite sum of its coordinate multiples of unit vectors. (`Breakdown.FracInternal.DensitySlice.coord_sum`)

**Expand a matrix pairing.** The inner product of a mapped vector with another vector equals the double sum of their coordinates against the matrix entries. (`Breakdown.FracInternal.DensitySlice.inner_expand`)

**Entry pairing in the rotating frame.** The matrix entry pairing equals the sum of paired entries in the cylindrical orthonormal frame. (`Breakdown.FracInternal.DensitySlice.frame_entryInner`)

**Cylindrical points are periodic.** Adding a full turn to the angle leaves the cylindrical point unchanged. (`Breakdown.FracInternal.DensitySlice.cyl_per`)

**Frame matrices are periodic.** Adding a full turn leaves every matrix entry in the cylindrical frame unchanged. (`Breakdown.FracInternal.DensitySlice.frameMat_add`)

**Parseval for real slice entries.** For a regular periodic real slice and an L2 partner, the allowed-mode pairing sums to the normalized real angular product integral. (`Breakdown.FracInternal.DensitySlice.entry_modes`)

**Products of L2 circle functions.** The product of two real L2 circle functions is integrable over a full turn. (`Breakdown.FracInternal.DensitySlice.product_integrable`)

**Pair matrix fields by their modes.** Under the stated slice regularity and L2 assumptions, the sum of paired matrix modes equals the normalized angular entry pairing. (`Breakdown.FracInternal.DensitySlice.slice_pair`)

**Expand a second-derivative pairing.** Pairing a bilinear spatial map with three vectors expands as a triple coordinate sum. (`Breakdown.FracInternal.DensitySlice.inner_expand3`)

**Curl in matrix coordinates.** Each component of the curl is the alternating sum of the corresponding gradient entries. (`Breakdown.FracInternal.DensitySlice.curlOf_apply`)

**Curl square in the rotating frame.** The squared curl norm equals the sum of squared alternating combinations of the frame matrix entries. (`Breakdown.FracInternal.DensitySlice.frame_curl`)

**Frame coordinates preserve norm square.** The sum of squared components in the cylindrical frame equals the squared vector norm. (`_private.Breakdown.FracCell.DensitySlice.0.Breakdown.FracInternal.DensitySlice.frame_coordSq`)

**Frame directions preserve matrix energy.** Summing squared images over frame directions gives the same matrix energy as summing over coordinate unit vectors. (`_private.Breakdown.FracCell.DensitySlice.0.Breakdown.FracInternal.DensitySlice.frame_normSq`)

**Second-derivative energy in the frame.** The full second-derivative square equals the sum of squares of all three-index frame components. (`Breakdown.FracInternal.DensitySlice.frame_second`)

**Curl-gradient energy in the frame.** The curl-gradient square equals the sum of squared alternating combinations of the three-index frame components. (`Breakdown.FracInternal.DensitySlice.frame_curlGrad`)

**Entry square in the rotating frame.** The matrix entry square equals the sum of squared cylindrical-frame entries. (`Breakdown.FracInternal.DensitySlice.entrySq_frame`)

**Second-derivative frames are periodic.** A full angular turn leaves every three-index frame component unchanged. (`Breakdown.FracInternal.DensitySlice.frameThird_add`)

**Regular slices are integrable.** A regular circle slice is integrable over a full turn. (`Breakdown.FracInternal.DensitySlice.regular_integrable`)

**Scale a regular circle slice.** Multiplying a regular circle slice by a real constant preserves its regularity. (`Breakdown.FracInternal.DensitySlice.regular_const`)

**Sum regular circle slices.** A finite sum of regular circle slices is regular. (`Breakdown.FracInternal.DensitySlice.regular_sum`)

**Scale a circle coefficient.** A real scalar factor can be pulled outside the circle coefficient. (`Breakdown.FracInternal.DensitySlice.circleCoeff_const`)

**Sum circle coefficients.** The circle coefficient of a finite sum of integrable real functions is the sum of their coefficients. (`Breakdown.FracInternal.DensitySlice.circleCoeff_sum`)

**A mode sum represents a circle average.** The mode-sum predicate requires angular integrability and convergence of the series to the normalized circle integral. (`Breakdown.FracInternal.DensitySlice.ModeSum`)

**Add finite families of mode sums.** A finite sum of mode-sum identities represents the corresponding finite sum of angular functions. (`Breakdown.FracInternal.DensitySlice.modeSum_sum`)

**Scale a mode-sum identity.** Multiplying both the modal series and angular function by a real constant preserves their mode-sum identity. (`Breakdown.FracInternal.DensitySlice.modeSum_const`)

**Add two mode-sum identities.** Adding two modal series and their angular functions preserves the mode-sum relation. (`Breakdown.FracInternal.DensitySlice.modeSum_add`)

**Transport a mode sum across equality.** Pointwise equal modal terms and angular functions satisfy the same mode-sum relation. (`Breakdown.FracInternal.DensitySlice.modeSum_congr`)

**Parseval for a real square.** For a regular periodic circle slice, squared allowed-mode magnitudes sum to the normalized integral of its square. (`Breakdown.FracInternal.DensitySlice.modeSum_sq`)

**Quadratic density on a circle.** At symmetry order at least three, valid circle-slice data give an integrable quadratic density whose normalized full-turn angular integral is the sum of the local mode densities. (`Breakdown.FracInternal.DensitySlice.quadratic_slice`)

**Fourier coefficients of a product.** Under the L2 and turn-symmetry assumptions, convolution of the allowed-harmonic coefficients sums to the coefficient of the product. (`Breakdown.FracInternal.DensitySlice.circle_conv`)

**Apply a matrix in coordinates.** A coordinate of a mapped vector is the finite sum of matrix entries times input coordinates. (`Breakdown.FracInternal.DensitySlice.clm_coord`)

**The stretching form in frame entries.** The stretching cross form expands into its curl, velocity and gradient couplings in the cylindrical frame. (`Breakdown.FracInternal.DensitySlice.frame_jForm`)

**A symmetry turn shifts the angle.** The discrete spatial turn adds two pi divided by the symmetry order to a cylindrical point's angle. (`Breakdown.FracInternal.DensitySlice.turn_cyl`)

**A symmetry turn shifts the frame.** The discrete turn carries each frame vector to the corresponding frame vector at the shifted angle. (`Breakdown.FracInternal.DensitySlice.turn_frame`)

**A symmetry turn preserves pairings.** The discrete turn preserves real inner products. (`Breakdown.FracInternal.DensitySlice.turn_inner`)

**Matrix components under a turn.** Intertwining spatial linear maps have equal frame entries at angles related by the discrete turn. (`Breakdown.FracInternal.DensitySlice.frameMat_turn`)

**Frame components as inner products.** A frame-vector component is the inner product with the corresponding frame unit vector. (`Breakdown.FracInternal.DensitySlice.frameVec_unit`)

**Vector components under a turn.** Vectors related by the discrete turn have equal frame components at the correspondingly shifted angles. (`Breakdown.FracInternal.DensitySlice.frameVec_turn`)

**Second derivatives under a turn.** Equivariant bilinear spatial maps have equal three-index frame components at correspondingly shifted angles. (`Breakdown.FracInternal.DensitySlice.frameThird_turn`)

**The radial zero set is null.** Almost every point of the radial-height plane has nonzero first coordinate. (`Breakdown.FracInternal.DensitySlice.ae_fst_ne`)

**Almost-everywhere facts on cell circles.** A spatial almost-everywhere property holds at almost every angle for almost every radial-height point in a valid cell rectangle. (`Breakdown.FracInternal.DensitySlice.slice_ae`)

**The pin pairing on a circle.** For valid circle data and symmetry order at least three, the angular model-pin pairing is two pi times its mode-field pairing. (`Breakdown.FracInternal.DensitySlice.pin_slice`)

**The actuator pairing on a circle.** For valid circle data and symmetry order at least three, the actuator-gradient pairing is angularly integrable and equals two pi times its mode-field pairing. (`Breakdown.FracInternal.DensitySlice.actuator_slice`)

**Assemble the density-slice identity.** The circle-regularity and coupling statements express full-turn density and pin integrals almost everywhere as 2π times the modal sums and pairings for admissible inputs when 1 < α < 5/4, the form and cell are valid, the weight is axisymmetric, the model has reflection symmetry and the cell lies in the cell region. (`Breakdown.CellCert.CellAnalysis.densitySlice_of`)

### Breakdown.FracCell.DensitySliceParts

This file states the angular regularity, quadratic-density and coupling obligations used by the density-slice proof.

**Regularity of a circle slice.** A regular circle slice is L2 over one full turn and almost everywhere invariant under the discrete symmetry turn. (`Breakdown.CellCert.CellAnalysis.IsCircleSliceRegular`)

**The data on one circle.** The circle-data predicate collects regular velocity and derivative slices, measurable bounded model entries, L2 actuator and pin slices, and the sampled weight identity. (`Breakdown.CellCert.CellAnalysis.IsCircleSliceData`)

**Regular slices in almost every cell.** For exponent between one and five quarters, valid symmetric form data and an admissible field give valid circle data almost everywhere in each valid cell. (`Breakdown.CellCert.CellAnalysis.CircleSliceRegularStatement`)

Proved by `Breakdown.CellCert.CellAnalysis.circleSliceRegular_holds`.

**The quadratic density.** The quadratic density combines full second-derivative, curl-gradient, curl and gradient squares with the specified cell coefficients. (`Breakdown.CellCert.CellAnalysis.quadraticDensity`)

**Modal expansion of quadratic density.** The interface requires angular integrability and a mode series representing the average quadratic density for valid circle data of order at least three. (`Breakdown.CellCert.CellAnalysis.CircleSliceQuadraticStatement`)

Proved by `Breakdown.FracInternal.DensitySlice.quadratic_slice`.

**Modal expansion of the coupling.** The interface requires the angular stretching coupling to be integrable and equal to two pi times its modal coupling for valid circle data of order at least three. (`Breakdown.CellCert.CellAnalysis.CircleSliceCouplingStatement`)

Proved by `Breakdown.CellCert.CellAnalysis.circleSliceCoupling_holds`.

### Breakdown.FracCell.EnergyAngular

This file identifies angular test suprema with inverse-Gram quadratic forms and proves the angular component of the cell energy matrix.

**Pull back a matrix through its rows.** The matrix formed from rows is the conjugate-transpose row matrix times the original matrix times the row matrix. (`_private.Breakdown.FracCell.EnergyAngular.0.Breakdown.CellCert.CellEnergy.formOfRows_eq`)

**Evaluate the row-pullback form.** The pulled-back quadratic form equals the real part of the matrix pairing of the evaluated rows. (`_private.Breakdown.FracCell.EnergyAngular.0.Breakdown.CellCert.CellEnergy.quad_formOfRows`)

**Swap a Hermitian pairing.** Conjugating a Hermitian matrix pairing exchanges its two vector arguments. (`_private.Breakdown.FracCell.EnergyAngular.0.Breakdown.CellCert.CellEnergy.conj_swap`)

**A Hermitian quadratic value is real.** A Hermitian matrix's self-pairing equals its real part embedded in the complex numbers. (`_private.Breakdown.FracCell.EnergyAngular.0.Breakdown.CellCert.CellEnergy.conj_re`)

**Positive definite quadratic values.** A positive definite matrix has strictly positive real quadratic value on every nonzero vector. (`_private.Breakdown.FracCell.EnergyAngular.0.Breakdown.CellCert.CellEnergy.pd_re_pos`)

**Cauchy-Schwarz for a positive matrix.** For a positive definite matrix, the squared norm of a mixed pairing is bounded by the product of the two self-pairings. (`_private.Breakdown.FracCell.EnergyAngular.0.Breakdown.CellCert.CellEnergy.sesq_bound`)

**The inverse-Gram supremum.** For a positive definite matrix, the supremum of squared dual pairings divided by positive matrix energy equals the inverse-matrix quadratic value. (`_private.Breakdown.FracCell.EnergyAngular.0.Breakdown.CellCert.CellEnergy.sup_identity`)

**Add quadratic-form values.** The quadratic value of a sum of matrices is the sum of their quadratic values. (`_private.Breakdown.FracCell.EnergyAngular.0.Breakdown.CellCert.CellEnergy.quad_add`)

**Identify a finite test supremum.** A two-way coefficient representation with positive definite Gram matrix identifies the test supremum with the inverse-Gram quadratic value. (`_private.Breakdown.FracCell.EnergyAngular.0.Breakdown.CellCert.CellEnergy.supremum_eq_of`)

**Pair a finite test expansion.** Under the stated integrability assumptions, a finite test expansion has the Gram-matrix norm and the coefficient-vector pairing. (`_private.Breakdown.FracCell.EnergyAngular.0.Breakdown.CellCert.CellEnergy.param_eq`)

**Cell basis functions are continuous.** Every tensor-product cell basis function is continuous. (`_private.Breakdown.FracCell.EnergyAngular.0.Breakdown.CellCert.CellEnergy.poly_cont`)

**Cell rectangles are compact.** Every closed cell rectangle is compact. (`_private.Breakdown.FracCell.EnergyAngular.0.Breakdown.CellCert.CellEnergy.rect_compact`)

**Cell rectangles are measurable.** Every cell rectangle is measurable. (`_private.Breakdown.FracCell.EnergyAngular.0.Breakdown.CellCert.CellEnergy.rect_meas`)

**Coefficients of a strain combination.** For integrable weighted gradient modes, the coefficient of a strain combination is the same combination of the mode coefficients. (`_private.Breakdown.FracCell.EnergyAngular.0.Breakdown.CellCert.CellEnergy.coef_strain`)

**Apply a low strain row.** Applying a low strain row gives the component-weighted sum of its indexed strain coordinates. (`_private.Breakdown.FracCell.EnergyAngular.0.Breakdown.CellCert.CellEnergy.lowRow_apply`)

**Apply a low pairing row.** A low pairing row evaluates as the sum of basis-test rectangle integrals times the corresponding low row values. (`_private.Breakdown.FracCell.EnergyAngular.0.Breakdown.CellCert.CellEnergy.lowPair_apply`)

**Orthogonality of the product basis.** A valid cell basis has radially weighted product-basis integrals equal to one for identical indices and zero otherwise. (`_private.Breakdown.FracCell.EnergyAngular.0.Breakdown.CellCert.CellEnergy.orth2`)

**Expand a polynomial test pairing.** A pairing against a test in the finite basis span equals the sum of its basis pairings times the field coefficients. (`_private.Breakdown.FracCell.EnergyAngular.0.Breakdown.CellCert.CellEnergy.expand`)

**Powers lie in the polynomial span.** Polynomials of increasing degree with nonzero leading coefficients span every monomial up to the selected degree. (`_private.Breakdown.FracCell.EnergyAngular.0.Breakdown.CellCert.CellEnergy.pow_span`)

**Monomials lie in the cell basis span.** A valid tensor-product cell basis spans every monomial whose two degrees are at most the selected cutoff. (`_private.Breakdown.FracCell.EnergyAngular.0.Breakdown.CellCert.CellEnergy.mono_span`)

**A polynomial vanishing on an interval.** A complex polynomial that vanishes on a nonempty open real interval has zero coefficient vector. (`_private.Breakdown.FracCell.EnergyAngular.0.Breakdown.CellCert.CellEnergy.poly1_zero`)

**A polynomial vanishing on a rectangle.** A bivariate complex polynomial that vanishes on a nonempty open rectangle has all coefficients zero. (`_private.Breakdown.FracCell.EnergyAngular.0.Breakdown.CellCert.CellEnergy.poly2_zero`)

**Positive weighted polynomial Gram.** A continuous nonnegative weight, positive on the cell interior, gives a positive definite Gram matrix for the angular polynomial tests. (`_private.Breakdown.FracCell.EnergyAngular.0.Breakdown.CellCert.CellEnergy.pairing_pd`)

**Positive Gram matrix at the axis.** For a valid cell meeting the axis, the angular-test Gram matrix with radial weight is positive definite. (`_private.Breakdown.FracCell.EnergyAngular.0.Breakdown.CellCert.CellEnergy.pairing_axis_pd`)

**Positive Gram matrix off the axis.** For a valid cell away from the axis, the angular-test Gram matrix with the prescribed off-axis weight is positive definite. (`_private.Breakdown.FracCell.EnergyAngular.0.Breakdown.CellCert.CellEnergy.pairing_off_pd`)

**Coefficients of a polynomial.** Membership in the bivariate polynomial space is equivalent to a finite monomial coefficient representation. (`_private.Breakdown.FracCell.EnergyAngular.0.Breakdown.CellCert.CellEnergy.poly_mem`)

**Basis functions lie in the monomial span.** Every tensor-product cell basis function of bounded degree lies in the corresponding finite monomial span. (`_private.Breakdown.FracCell.EnergyAngular.0.Breakdown.CellCert.CellEnergy.basis_in_mono`)

**Projection energy is coefficient energy.** For a valid cell away from the axis and an integrable field, the unweighted square of its polynomial projection is the sum of squared basis coefficients. (`_private.Breakdown.FracCell.EnergyAngular.0.Breakdown.CellCert.CellEnergy.proj_norm`)

**Cancel radius in the angular pairing.** Multiplying a field value and test by radius permits the displayed cancellation through division by radius, including the zero-radius convention. (`_private.Breakdown.FracCell.EnergyAngular.0.Breakdown.CellCert.CellEnergy.axis_pt`)

**Exchange the four component sums.** The two pairs of finite component sums can be exchanged. (`_private.Breakdown.FracCell.EnergyAngular.0.Breakdown.CellCert.CellEnergy.sum_swap4`)

**Represent the scaled polynomial tests.** Membership in the radius-scaled polynomial space is equivalent to a finite expansion in the angular tests under the specified index equivalence. (`_private.Breakdown.FracCell.EnergyAngular.0.Breakdown.CellCert.CellEnergy.scaled_mem`)

**Compute a polynomial test supremum.** A finite test representation, positive Gram matrix and identified moments give the inverse-Gram formula for the test supremum. (`_private.Breakdown.FracCell.EnergyAngular.0.Breakdown.CellCert.CellEnergy.supremum_case`)

**The angular component form.** The angular-frame and mode-integrability statements identify each angular matrix quadratic form with the corresponding angular energy in every valid energy setting, using the axis or off-axis form according to the cell’s inner radius. (`Breakdown.CellCert.CellEnergy.componentAngular_of`)

### Breakdown.FracCell.EnergyAssembly

This file adds the radial, height, angular and top-degree component forms to identify the full cell energy matrix.

**Quadratic values add.** Evaluating a sum of matrices gives the sum of their quadratic values. (`Breakdown.CellCert.CellEnergy.EnergyAssemblyInternal.value_add`)

**Quadratic values subtract.** Evaluating a difference of matrices gives the difference of their quadratic values. (`Breakdown.CellCert.CellEnergy.EnergyAssemblyInternal.value_sub`)

**Real scaling of quadratic values.** Scaling a complex matrix by an embedded real scalar scales its real quadratic value by that scalar. (`Breakdown.CellCert.CellEnergy.EnergyAssemblyInternal.value_smul`)

**Quadratic evaluation as an additive map.** For a fixed vector, quadratic evaluation defines an additive map from complex matrices to real numbers. (`Breakdown.CellCert.CellEnergy.EnergyAssemblyInternal.valueHom`)

**Evaluate a finite matrix sum.** Quadratic evaluation commutes with a finite sum of matrices. (`Breakdown.CellCert.CellEnergy.EnergyAssemblyInternal.value_sum`)

**Select an array component.** Pairing the unit component array with a matrix array returns the selected entry. (`Breakdown.CellCert.CellEnergy.EnergyAssemblyInternal.unit_sum`)

**Select a curl component.** Pairing a curl component array with a matrix array returns the corresponding alternating curl component. (`Breakdown.CellCert.CellEnergy.EnergyAssemblyInternal.curl_sum`)

**A unit strain component.** The strain field selected by a unit array is the corresponding gradient mode. (`Breakdown.CellCert.CellEnergy.EnergyAssemblyInternal.strain_unit`)

**A unit radial component.** The radial field selected by a unit array is the corresponding radial gradient mode. (`Breakdown.CellCert.CellEnergy.EnergyAssemblyInternal.radial_unit`)

**A unit height component.** The height field selected by a unit array is the corresponding height gradient mode. (`Breakdown.CellCert.CellEnergy.EnergyAssemblyInternal.height_unit`)

**A unit angular component.** The angular field selected by a unit array is the corresponding angular gradient mode. (`Breakdown.CellCert.CellEnergy.EnergyAssemblyInternal.angular_unit`)

**A curl strain component.** The strain field selected by a curl array is the curl combination of gradient modes. (`Breakdown.CellCert.CellEnergy.EnergyAssemblyInternal.strain_curl`)

**A curl radial component.** The radial field selected by a curl array is the curl combination of radial gradient modes. (`Breakdown.CellCert.CellEnergy.EnergyAssemblyInternal.radial_curl`)

**A curl height component.** The height field selected by a curl array is the curl combination of height gradient modes. (`Breakdown.CellCert.CellEnergy.EnergyAssemblyInternal.height_curl`)

**A curl angular component.** The angular field selected by a curl array is the curl combination of angular gradient modes. (`Breakdown.CellCert.CellEnergy.EnergyAssemblyInternal.angular_curl`)

**Add the three directional energies.** Under the energy setting and three component interfaces, the component matrix value equals the sum of radial, height and angular energies. (`Breakdown.CellCert.CellEnergy.EnergyAssemblyInternal.component_value`)

**Assemble the full energy form.** The radial, height, angular and top-form statements identify the assembled energy matrix quadratic form with the analytic cell energy term in every valid energy setting. (`Breakdown.CellCert.CellEnergy.energyForm_of`)

### Breakdown.FracCell.EnergyClass

This file represents the class loss term as a sesquilinear form on the retained strain and velocity coefficients.

**The slot matrix quadratic value.** The quadratic form pulled back through slot rows equals the real double sum over the indexed modal coordinates. (`Breakdown.CellCert.CellEnergy.EnergyClassInternal.quad_slot`)

**The class loss pairing.** The class loss pairing combines the curl pairing with weighted strain and inverse-weighted velocity pairings. (`Breakdown.CellCert.CellEnergy.EnergyClassInternal.lossSesq`)

**Curl components add.** The curl component of a sum of arrays is the sum of the curl components. (`Breakdown.CellCert.CellEnergy.EnergyClassInternal.curl_add`)

**Curl components scale.** Scaling an array by a complex scalar scales its curl components by the same scalar. (`Breakdown.CellCert.CellEnergy.EnergyClassInternal.curl_smul`)

**Add in the first loss argument.** The loss pairing is additive in its first argument. (`Breakdown.CellCert.CellEnergy.EnergyClassInternal.loss_add_left`)

**Add in the second loss argument.** The loss pairing is additive in its second argument. (`Breakdown.CellCert.CellEnergy.EnergyClassInternal.loss_add_right`)

**Scale the first loss argument.** Scaling the first loss argument pulls out the conjugate scalar. (`Breakdown.CellCert.CellEnergy.EnergyClassInternal.loss_smul_left`)

**Scale the second loss argument.** Scaling the second loss argument pulls out the scalar unchanged. (`Breakdown.CellCert.CellEnergy.EnergyClassInternal.loss_smul_right`)

**Sum the first loss argument.** A finite weighted sum in the first argument expands into a sum of loss pairings with conjugated coefficients. (`Breakdown.CellCert.CellEnergy.EnergyClassInternal.loss_sum_left`)

**Sum the second loss argument.** A finite weighted sum in the second argument expands into a sum of loss pairings with unchanged coefficients. (`Breakdown.CellCert.CellEnergy.EnergyClassInternal.loss_sum_right`)

**The loss pairing on one vector.** For real weights, the self-pairing is the real curl square plus the weighted strain and inverse-weighted velocity squares. (`Breakdown.CellCert.CellEnergy.EnergyClassInternal.loss_self`)

**The unit value of a low slot.** A low slot selects one unit strain entry or one unit velocity component. (`Breakdown.CellCert.CellEnergy.EnergyClassInternal.slotUnit`)

**The polynomial of a low slot.** A low slot selects the tensor-product basis polynomial at its two polynomial indices. (`Breakdown.CellCert.CellEnergy.EnergyClassInternal.slotPoly`)

**Factor a slot value.** A slot value equals its real basis polynomial times its unit strain or velocity value. (`Breakdown.CellCert.CellEnergy.EnergyClassInternal.slotValue_eq`)

**Continuity of a cell basis polynomial.** Every tensor-product basis polynomial is continuous. (`Breakdown.CellCert.CellEnergy.EnergyClassInternal.basisFn_cont`)

**Continuity of a slot polynomial.** The polynomial associated with each low slot is continuous. (`Breakdown.CellCert.CellEnergy.EnergyClassInternal.slotPoly_cont`)

**A cell rectangle has finite measure.** The Lebesgue measure of a cell rectangle is finite. (`Breakdown.CellCert.CellEnergy.EnergyClassInternal.rect_fin`)

**Integrability of a weighted slot term.** On a cell rectangle, a continuous factor times a complex linear combination of bounded measurable real functions is integrable. (`Breakdown.CellCert.CellEnergy.EnergyClassInternal.term_int`)

**Split strain and velocity slot indices.** The slot equivalence separates the strain indices from the lower-degree velocity indices. (`Breakdown.CellCert.CellEnergy.EnergyClassInternal.slotEquiv`)

**Expand a sum of slot values.** The sum over all low slots expands into the separate tensor-product polynomial sums for strain and velocity. (`Breakdown.CellCert.CellEnergy.EnergyClassInternal.slot_sum`)

**The class loss matrix identity.** The class-form interface identifies the matrix loss with the corresponding modal class expression. (`Breakdown.CellCert.CellEnergy.classForm_holds`)

### Breakdown.FracCell.EnergyCross

This file identifies the off-diagonal actuator and pin blocks of the local matrix with their analytic linear pairings.

**Integrability of the cross terms.** The predicate requires integrable weighted gradient modes and radially weighted actuator-gradient and pin modes on the cell rectangle. (`Breakdown.CellCert.CellEnergy.CrossIntegrable`)

**Evaluate a real cross block.** For real auxiliary coordinates, the block matrix value is the main quadratic value plus twice the real cross-row pairing. (`Breakdown.CellCert.CellEnergy.EnergyCrossInternal.block_value`)

**Apply a combination of slot rows.** Applying a weighted sum of slot rows gives the same weighted sum of the indexed data coordinates. (`Breakdown.CellCert.CellEnergy.EnergyCrossInternal.rowApply_slot`)

**Separate the low-slot index types.** The low-slot index is equivalent to the disjoint union of strain and velocity polynomial indices. (`Breakdown.CellCert.CellEnergy.EnergyCrossInternal.slotEquiv`)

**Split the sum over low slots.** A sum over low slots separates into the full strain-index sum and the lower-degree velocity-index sum. (`Breakdown.CellCert.CellEnergy.EnergyCrossInternal.slot_sum`)

**Pair a single matrix entry.** Pairing an array supported at one entry with another array gives that value times the conjugate selected entry. (`Breakdown.CellCert.CellEnergy.EnergyCrossInternal.entry_unit`)

**Pair the zero array.** The entry pairing with a zero first array is zero. (`Breakdown.CellCert.CellEnergy.EnergyCrossInternal.entry_zero_left`)

**Expand an integral in basis coefficients.** An almost-everywhere finite basis expansion and the stated integrability assumptions permit expanding the two weighted pairings into their coefficient sums. (`Breakdown.CellCert.CellEnergy.EnergyCrossInternal.integral_expand`)

**The radial weights multiply to radius.** The cell line weight times the normalized radial factor equals the physical radius. (`Breakdown.CellCert.CellEnergy.EnergyCrossInternal.weight_eq`)

**Continuity of the basis factor.** Each tensor-product basis factor is continuous on the radial-height plane. (`Breakdown.CellCert.CellEnergy.EnergyCrossInternal.basis_continuous`)

**Integrability of a cross basis term.** A radially integrable mode remains integrable after conjugation and multiplication by a cell basis polynomial and the equivalent radial weight. (`Breakdown.CellCert.CellEnergy.EnergyCrossInternal.term_integrable`)

**Evaluate the complete local cross form.** Under the energy setting and cross-integrability assumptions, the local matrix value splits into energy minus class plus pair forms and the analytic linear term. (`Breakdown.CellCert.CellEnergy.crossForm_holds`)

### Breakdown.FracCell.EnergyCrossIntegrable

This file derives the cross-term integrability from the full energy setting and closes the local cross-form interface.

**Cross terms from the energy setting.** A valid energy setting supplies all gradient, actuator and pin integrability required by the cross form. (`Breakdown.CellCert.CellEnergy.crossIntegrable_of_setting`)

**Local form with actuator and pin terms.** Under the energy-setting hypotheses, the local matrix form on the combined field, actuator and pin coordinates equals the energy-minus-class-plus-pair form on the field coordinates plus the analytic linear actuator and pin term. (`Breakdown.CellCert.CellEnergy.crossForm_closed`)

### Breakdown.FracCell.EnergyCrossProj

This file expresses the chosen low polynomial projection through its basis coefficients almost everywhere, as required by the cross-term calculation.

**Triangular polynomial coefficients.** The coefficient array defines a polynomial by summing its row through the selected degree. (`Breakdown.CellCert.CellEnergy.EnergyCrossProjInternal.polyOf`)

**Monomials lie in a triangular span.** Positive leading coefficients ensure that each monomial up to the cutoff lies in the span of the triangular polynomial family. (`Breakdown.CellCert.CellEnergy.EnergyCrossProjInternal.pow_mem_span`)

**Write a monomial as a finite combination.** Every monomial within the degree cutoff has a finite coefficient representation in a triangular polynomial family with positive leading coefficients. (`Breakdown.CellCert.CellEnergy.EnergyCrossProjInternal.pow_eq_comb`)

**The complex cell basis.** The complex basis function embeds the real tensor-product cell basis in the complex numbers. (`Breakdown.CellCert.CellEnergy.EnergyCrossProjInternal.basisC`)

**The finite complex basis span.** The basis span is the complex submodule generated by the cell basis functions through the two degree cutoffs. (`Breakdown.CellCert.CellEnergy.EnergyCrossProjInternal.basisSpan`)

**Complex monomials lie in the basis span.** A valid cell basis spans each complex monomial within the two degree cutoffs. (`Breakdown.CellCert.CellEnergy.EnergyCrossProjInternal.mono_mem`)

**Polynomial functions lie in the span.** Every polynomial function within the degree cutoff lies in the span of a valid cell basis. (`Breakdown.CellCert.CellEnergy.EnergyCrossProjInternal.poly_mem`)

**The complex basis is continuous.** Every complex cell basis function is continuous. (`Breakdown.CellCert.CellEnergy.EnergyCrossProjInternal.basisC_continuous`)

**The radial line weight is continuous.** The cell line weight viewed on the radial-height plane is continuous. (`Breakdown.CellCert.CellEnergy.EnergyCrossProjInternal.lineWeight_continuous`)

**The projection rectangle is compact.** The cell rectangle used for projection is compact. (`Breakdown.CellCert.CellEnergy.EnergyCrossProjInternal.rect_compact`)

**The projection rectangle is measurable.** The cell rectangle used for projection is measurable. (`Breakdown.CellCert.CellEnergy.EnergyCrossProjInternal.rect_measurable`)

**Continuity of the finite basis span.** Every function in the finite complex cell basis span is continuous. (`Breakdown.CellCert.CellEnergy.EnergyCrossProjInternal.span_continuous`)

**Complex basis orthogonality.** For valid cell bases, the weighted integral of two complex basis functions is one when both polynomial indices agree and zero otherwise. (`Breakdown.CellCert.CellEnergy.EnergyCrossProjInternal.ortho`)

**The polynomial space contains zero.** The zero function belongs to every indicated bivariate polynomial space. (`Breakdown.CellCert.CellEnergy.EnergyCrossProjInternal.polyFn_zero`)

**Polynomial functions add.** Adding two functions within the same polynomial degree limits preserves those limits. (`Breakdown.CellCert.CellEnergy.EnergyCrossProjInternal.polyFn_add`)

**Polynomial functions scale.** Multiplying a polynomial function by a complex scalar preserves its degree limits. (`Breakdown.CellCert.CellEnergy.EnergyCrossProjInternal.polyFn_smul`)

**Finite sums stay polynomial.** A finite sum of functions within the same degree limits stays in that polynomial space. (`Breakdown.CellCert.CellEnergy.EnergyCrossProjInternal.polyFn_sum`)

**A bounded-degree monomial is polynomial.** A monomial whose two exponents lie within the cutoff belongs to the indicated polynomial space. (`Breakdown.CellCert.CellEnergy.EnergyCrossProjInternal.mono_poly`)

**Basis functions have bounded degree.** A cell basis function with indices within the cutoff lies in the corresponding polynomial space. (`Breakdown.CellCert.CellEnergy.EnergyCrossProjInternal.basisC_poly`)

**The finite basis span is polynomial.** Every function in the finite cell basis span satisfies the corresponding polynomial degree limits. (`Breakdown.CellCert.CellEnergy.EnergyCrossProjInternal.span_poly`)

**Polynomial functions are continuous.** Every function in a finite bivariate polynomial space is continuous. (`Breakdown.CellCert.CellEnergy.EnergyCrossProjInternal.poly_continuous`)

**Projection equals its coefficient sum.** For weighted integrable data on a valid cell with a valid basis, the low projection equals its finite basis coefficient sum almost everywhere on the rectangle. (`Breakdown.CellCert.CellEnergy.lowProj_ae_eq_coefSum`)

### Breakdown.FracCell.EnergyDefs

This file defines row evaluation and the combined data vector, then states how retained coefficients and face rows represent an actual field.

**Evaluate a complex row.** Row evaluation is the finite sum of row entries times the corresponding data coordinates. (`Breakdown.CellCert.CellEnergy.rowApply`)

**The combined cell data vector.** The data vector appends real actuator and pin coordinates, embedded in the complex numbers, to the complex cell coordinates. (`Breakdown.CellCert.CellEnergy.dataVector`)

**Cell coordinates represent a field.** The representation structure identifies strain and velocity coordinates with mode coefficients and identifies boundary rows with radial and height face moments. (`Breakdown.CellCert.CellEnergy.Represents`)

### Breakdown.FracCell.EnergyHeight

This file derives the height component-form identity from weak height derivatives, boundary moments and the polynomial projection.

**The line weight has the axis factor.** For a valid cell and a continuous radial test, either the lower radius is positive or the weighted test factors as radius times a continuous function. (`Breakdown.CellCert.CellEnergy.EnergyHeightInternal.side_lw`)

**Distribute a separated test weight.** A separated radial-height test weight distributes through a finite component combination. (`Breakdown.CellCert.CellEnergy.EnergyHeightInternal.comb_mul`)

**Component combinations are integrable.** A finite complex linear combination of integrable component fields is integrable. (`Breakdown.CellCert.CellEnergy.EnergyHeightInternal.comb_integrable`)

**Integrate a component combination.** The integral of a finite complex component combination is the same combination of component integrals. (`Breakdown.CellCert.CellEnergy.EnergyHeightInternal.comb_integral`)

**Combine weak height pairs.** Finite component combinations of weak height pairs form another weak height pair. (`Breakdown.CellCert.CellEnergy.EnergyHeightInternal.pair_comb`)

**Radial basis polynomials are continuous.** Every radial basis polynomial is continuous. (`Breakdown.CellCert.CellEnergy.EnergyHeightInternal.continuous_radialPoly`)

**Height basis polynomials are continuous.** Every height basis polynomial is continuous. (`Breakdown.CellCert.CellEnergy.EnergyHeightInternal.continuous_heightPoly`)

**Height basis polynomials differentiate.** Every height basis polynomial is differentiable. (`Breakdown.CellCert.CellEnergy.EnergyHeightInternal.differentiable_heightPoly`)

**Height basis polynomials are C1.** Every height basis polynomial is continuously differentiable. (`Breakdown.CellCert.CellEnergy.EnergyHeightInternal.contDiff_heightPoly`)

**Low rows give strain coefficients.** For represented fields with the stated weak height pairs, each low row evaluates to the corresponding strain-combination coefficient. (`Breakdown.CellCert.CellEnergy.EnergyHeightInternal.lowRow_value`)

**Height slope of a product basis.** The height slope of a tensor-product basis function is its radial factor times the derivative of its height factor. (`Breakdown.CellCert.CellEnergy.EnergyHeightInternal.slope_basis`)

**Differentiate the height expansion.** The height derivative of a finite complex basis expansion differentiates each height polynomial term. (`Breakdown.CellCert.CellEnergy.EnergyHeightInternal.heightDeriv_comb`)

**Combine height face moments.** For weak height pairs, the height face moment commutes with finite complex component combinations. (`Breakdown.CellCert.CellEnergy.EnergyHeightInternal.face_comb`)

**The reference height is continuous.** The reference-height coordinate of a cell is continuous. (`Breakdown.CellCert.CellEnergy.EnergyHeightInternal.continuous_refZ`)

**Reference height square on the cell.** The squared reference-height coordinate is at most one on the closed cell interval. (`Breakdown.CellCert.CellEnergy.EnergyHeightInternal.refZ_sq_le`)

**Reference height square in the interior.** The squared reference-height coordinate is strictly below one in the open cell interval. (`Breakdown.CellCert.CellEnergy.EnergyHeightInternal.refZ_sq_lt`)

**The height projection matrix value.** Under the weak-pair and coefficient-identification assumptions, the height projection form equals inner radius times the weighted height-derivative energy of the projection. (`Breakdown.CellCert.CellEnergy.EnergyHeightInternal.proj_value`)

**The height component form.** The weak height-mode statement identifies the sum of projected, outer and applicable inner height matrix forms with the corresponding height energy in every valid energy setting. (`Breakdown.CellCert.CellEnergy.componentHeight`)

### Breakdown.FracCell.EnergyHeightParts

This file states weak height pairing and proves the inverse-Gram representation of polynomial test suprema used in the height energy.

**A weak height derivative pair.** The predicate requires weighted integrability and height integration by parts for endpoint-vanishing C1 tests, with the stated axis factor in the radial weight. (`Breakdown.CellCert.CellEnergy.HeightWeakPair`)

**Gradient modes form weak height pairs.** The interface requires each gradient mode and its height derivative to form a weak height pair on every valid cell. (`Breakdown.CellCert.CellEnergy.HeightModeWeakStatement`)

Proved by `Breakdown.CellCert.CellEnergy.heightModeWeak`.

**Polynomial tests as a matrix supremum.** Positive interior weight and identified integrable monomial moments identify the polynomial test supremum with the inverse-Gram row matrix form. (`Breakdown.CellCert.CellEnergy.HeightParts.testSup_polyFn`)

### Breakdown.FracCell.EnergyHeightProj

This file proves the finite-basis formula and orthogonality of the height projection, including its choice-based definition.

**Pad a finite sum with zeros.** A sum through a smaller degree equals a sum through a larger finite index set with zero terms above the smaller degree. (`Breakdown.CellCert.CellEnergy.HeightProj.sum_range_eq_fin`)

**A triangular polynomial family.** Each triangular polynomial is the finite power sum given by one row of coefficients. (`Breakdown.CellCert.CellEnergy.HeightProj.triPoly`)

**Expand powers in triangular polynomials.** Nonzero leading coefficients give a finite expansion of every power within the degree cutoff in the triangular polynomial family. (`Breakdown.CellCert.CellEnergy.HeightProj.pow_span`)

**Bivariate polynomials by coefficients.** The polynomial predicate records a finite complex monomial expansion within the two specified degree limits. (`Breakdown.CellCert.CellEnergy.HeightProj.polyFnG`)

**The weighted rectangle pairing.** The pairing integrates the weighted first function against the conjugate of the second over the selected region. (`Breakdown.CellCert.CellEnergy.HeightProj.pairOnG`)

**Choose the polynomial projection.** The projection chooses a polynomial with residual orthogonal to all allowed polynomial tests when one exists and otherwise returns zero. (`Breakdown.CellCert.CellEnergy.HeightProj.projG`)

**The product triangular basis.** The two-variable basis function is the product of the radial and height triangular polynomials. (`Breakdown.CellCert.CellEnergy.HeightProj.bas`)

**Pad a triangular polynomial expansion.** A triangular polynomial can be written over a larger finite index set by setting coefficients above its degree to zero. (`Breakdown.CellCert.CellEnergy.HeightProj.triPoly_fin`)

**A product basis is polynomial.** A product basis function within the cutoff lies in the corresponding bivariate polynomial space. (`Breakdown.CellCert.CellEnergy.HeightProj.bas_mem`)

**Expand a polynomial in the product basis.** Nonzero leading coefficients in both polynomial families give a finite product-basis expansion of every polynomial within the cutoff. (`Breakdown.CellCert.CellEnergy.HeightProj.span_mem`)

**Finite combinations stay polynomial.** A finite complex combination of functions in the same bivariate polynomial space remains in that space. (`Breakdown.CellCert.CellEnergy.HeightProj.sum_mem_poly`)

**Triangular polynomials are continuous.** Every polynomial defined by a finite triangular coefficient row is continuous. (`Breakdown.CellCert.CellEnergy.HeightProj.continuous_triPoly`)

**Product-basis orthogonality.** Orthogonality of the radial and height families gives weighted orthogonality of their tensor products on the rectangle. (`Breakdown.CellCert.CellEnergy.HeightProj.ortho2`)

**The generic basis coefficient.** A generic coefficient is the weighted rectangle pairing of the field with a product basis function. (`Breakdown.CellCert.CellEnergy.HeightProj.coefG`)

**Basis formula for the chosen projection.** Under the leading-coefficient, orthogonality and integrability assumptions, the chosen projection equals its finite product-basis coefficient expansion. (`Breakdown.CellCert.CellEnergy.HeightProj.proj_eq`)

**The basis residual is orthogonal.** Under the same basis and integrability assumptions, subtracting the finite coefficient expansion leaves a residual orthogonal to every allowed polynomial test. (`Breakdown.CellCert.CellEnergy.HeightProj.orth_gen`)

**Continuity of the line weight.** The one-variable cell line weight is continuous. (`Breakdown.CellCert.CellEnergy.HeightProj.continuous_lineWeight`)

**The cell projection has a basis formula.** For a valid cell basis and the stated weighted integrability, the cell projection equals its finite basis coefficient expansion pointwise. (`Breakdown.CellCert.CellEnergy.HeightProj.proj_eq_basis`)

**The projection residual is orthogonal.** For a valid cell basis and the stated integrability, the basis-expansion residual pairs to zero with every polynomial test within the cutoff. (`Breakdown.CellCert.CellEnergy.HeightProj.proj_orth`)

### Breakdown.FracCell.EnergyHeightRows

This file turns the height integration-by-parts formulas into concrete interior and boundary row values for the cell energy matrix.

**A product polynomial lies in the space.** A product of real polynomials whose degrees are at most Q lies in the complex polynomial space with both degree limits Q. (`Breakdown.CellCert.CellEnergy.HeightRows.poly_mem`)

**A low pairing row is an integral.** When low rows encode basis coefficients, a low pairing row against bounded-degree product polynomials equals the corresponding weighted field integral. (`Breakdown.CellCert.CellEnergy.HeightRows.expand`)

**The interior height rows.** For a valid cell away from the axis, weak height pairing identifies the interior height row with the weighted derivative moment. (`Breakdown.CellCert.CellEnergy.HeightRows.inner_rows`)

**Row evaluation preserves addition.** Evaluating a sum of two rows gives the sum of their evaluations. (`Breakdown.CellCert.CellEnergy.HeightRows.rowApply_add`)

**Row evaluation preserves scaling.** A complex scalar multiplying a row can be pulled outside its evaluation. (`Breakdown.CellCert.CellEnergy.HeightRows.rowApply_mul`)

**Row evaluation preserves finite sums.** Evaluating a finite sum of rows gives the finite sum of their evaluations. (`Breakdown.CellCert.CellEnergy.HeightRows.rowApply_sum`)

**Expand powers in the radial basis.** A radial power within the cutoff is the sum of its radial moments times the valid radial basis polynomials. (`Breakdown.CellCert.CellEnergy.HeightRows.pow_expand`)

**The outer height rows.** With compatible degree cutoffs and represented face moments, the outer height row equals the radius-weighted reference-height derivative moment. (`Breakdown.CellCert.CellEnergy.HeightRows.outer_rows`)

### Breakdown.FracCell.EnergyPair

This file expands the local interaction matrix using sesquilinearity and identifies it with the analytic coupling of retained modes.

**The slot-pullback quadratic value.** The slot-row pullback has quadratic value equal to the real double sum over retained mode and component coordinates. (`_private.Breakdown.FracCell.EnergyPair.0.Breakdown.CellCert.CellEnergy.quad_slot`)

**Pull out a conjugated scalar.** A scalar multiplying the first vector can be factored out of the coordinate pairing as its conjugate. (`_private.Breakdown.FracCell.EnergyPair.0.Breakdown.CellCert.CellEnergy.sum3_left`)

**Pull out a scalar in the second vector.** A scalar multiplying the inner vector factors unchanged out of the finite matrix pairing. (`_private.Breakdown.FracCell.EnergyPair.0.Breakdown.CellCert.CellEnergy.sum3_right`)

**Curl components preserve addition.** A curl component of a sum of matrix arrays is the sum of the corresponding components. (`_private.Breakdown.FracCell.EnergyPair.0.Breakdown.CellCert.CellEnergy.curl_add`)

**Curl components preserve scaling.** A complex scalar multiplying a matrix array factors unchanged out of its curl component. (`_private.Breakdown.FracCell.EnergyPair.0.Breakdown.CellCert.CellEnergy.curl_smul`)

**The coupling map preserves addition.** The coupling map is additive in its velocity argument. (`_private.Breakdown.FracCell.EnergyPair.0.Breakdown.CellCert.CellEnergy.coupling_add`)

**The coupling map preserves scaling.** The coupling map respects complex scaling of its velocity argument. (`_private.Breakdown.FracCell.EnergyPair.0.Breakdown.CellCert.CellEnergy.coupling_smul`)

**Entry pairing adds in the first slot.** The entry pairing is additive in its first matrix argument. (`_private.Breakdown.FracCell.EnergyPair.0.Breakdown.CellCert.CellEnergy.pairing_add_left`)

**Entry pairing adds in the second slot.** The entry pairing is additive in its second matrix argument. (`_private.Breakdown.FracCell.EnergyPair.0.Breakdown.CellCert.CellEnergy.pairing_add_right`)

**Entry pairing scales in the first slot.** A scalar in the first entry-pairing argument comes out unchanged. (`_private.Breakdown.FracCell.EnergyPair.0.Breakdown.CellCert.CellEnergy.pairing_smul_left`)

**Entry pairing conjugates second scalars.** A scalar in the second entry-pairing argument comes out conjugated. (`_private.Breakdown.FracCell.EnergyPair.0.Breakdown.CellCert.CellEnergy.pairing_smul_right`)

**The combined pair vector adds.** Adding both strain and velocity inputs adds their combined twelve-component pair vectors. (`_private.Breakdown.FracCell.EnergyPair.0.Breakdown.CellCert.CellEnergy.pvec_add`)

**The combined pair vector scales.** Scaling strain and velocity by the same complex scalar scales their combined pair vector. (`_private.Breakdown.FracCell.EnergyPair.0.Breakdown.CellCert.CellEnergy.pvec_smul`)

**Matrix pairing adds in the first slot.** The twelve-dimensional matrix pairing is additive in its first vector argument. (`_private.Breakdown.FracCell.EnergyPair.0.Breakdown.CellCert.CellEnergy.msesq_add_left`)

**Matrix pairing adds in the second slot.** The twelve-dimensional matrix pairing is additive in its second vector argument. (`_private.Breakdown.FracCell.EnergyPair.0.Breakdown.CellCert.CellEnergy.msesq_add_right`)

**Matrix pairing conjugates first scalars.** A scalar in the first matrix-pairing argument comes out conjugated. (`_private.Breakdown.FracCell.EnergyPair.0.Breakdown.CellCert.CellEnergy.msesq_smul_left`)

**Matrix pairing preserves second scalars.** A scalar in the second matrix-pairing argument comes out unchanged. (`_private.Breakdown.FracCell.EnergyPair.0.Breakdown.CellCert.CellEnergy.msesq_smul_right`)

**Mode pairing adds in the first slot.** The local mode pairing is additive in its first strain-velocity argument. (`_private.Breakdown.FracCell.EnergyPair.0.Breakdown.CellCert.CellEnergy.ps_add_left`)

**Mode pairing adds in the second slot.** The local mode pairing is additive in its second strain-velocity argument. (`_private.Breakdown.FracCell.EnergyPair.0.Breakdown.CellCert.CellEnergy.ps_add_right`)

**Mode pairing conjugates first scalars.** A scalar in the first local mode-pairing argument comes out conjugated. (`_private.Breakdown.FracCell.EnergyPair.0.Breakdown.CellCert.CellEnergy.ps_smul_left`)

**Mode pairing preserves second scalars.** A scalar in the second local mode-pairing argument comes out unchanged. (`_private.Breakdown.FracCell.EnergyPair.0.Breakdown.CellCert.CellEnergy.ps_smul_right`)

**Index the low strain and velocity slots.** The index equivalence identifies low slots with the disjoint union of strain and velocity polynomial coordinates. (`_private.Breakdown.FracCell.EnergyPair.0.Breakdown.CellCert.CellEnergy.slotEquiv`)

**Expand the low-slot field.** The finite low-slot expansion separates into the strain and velocity tensor-product polynomial fields. (`_private.Breakdown.FracCell.EnergyPair.0.Breakdown.CellCert.CellEnergy.slot_sum`)

**A Hermitian self-pairing is real.** For a Hermitian twelve-dimensional matrix, its real quadratic value embedded in the complex numbers equals its self-pairing. (`_private.Breakdown.FracCell.EnergyPair.0.Breakdown.CellCert.CellEnergy.selfAdjoint_real`)

**A zero first mode-pairing argument.** The local mode pairing vanishes when its first strain-velocity argument is zero. (`_private.Breakdown.FracCell.EnergyPair.0.Breakdown.CellCert.CellEnergy.ps_zero_left`)

**A zero second mode-pairing argument.** The local mode pairing vanishes when its second strain-velocity argument is zero. (`_private.Breakdown.FracCell.EnergyPair.0.Breakdown.CellCert.CellEnergy.ps_zero_right`)

**Expand a sum in the first pairing slot.** A finite weighted sum in the first local pairing argument expands with conjugated coefficients. (`_private.Breakdown.FracCell.EnergyPair.0.Breakdown.CellCert.CellEnergy.ps_sum_left`)

**Expand a sum in the second pairing slot.** A finite weighted sum in the second local pairing argument expands with unchanged coefficients. (`_private.Breakdown.FracCell.EnergyPair.0.Breakdown.CellCert.CellEnergy.ps_sum_right`)

**Identify the interaction matrix value.** The energy setting, integrable basis pairings and pointwise low-mode expansions identify the interaction matrix value with the analytic local pair form. (`Breakdown.CellCert.CellEnergy.pairForm_holds_of`)

**Integrability of the basis pairings.** The interface requires every radially weighted local pairing of two low basis slots to be integrable in a valid energy setting. (`Breakdown.CellCert.CellEnergy.PairIntegrableStatement`)

Proved by `Breakdown.CellCert.CellEnergy.pairIntegrable_holds`.

**The low strain expansion.** The interface requires each retained strain mode to equal its finite coefficient expansion pointwise on the cell rectangle. (`Breakdown.CellCert.CellEnergy.LowStrainExpansionStatement`)

Proved by `Breakdown.CellCert.CellEnergy.lowStrainExpansion`.

**The low velocity expansion.** The interface requires each retained velocity mode to equal its lower-degree finite coefficient expansion pointwise on the cell rectangle. (`Breakdown.CellCert.CellEnergy.LowVelocityExpansionStatement`)

Proved by `Breakdown.CellCert.CellEnergy.lowVelocityExpansion`.

**Assemble the interaction-form identity.** The basis-pair integrability, low-strain expansion and low-velocity expansion statements identify the matrix pairing form with the analytic local pairing form in every valid energy setting. (`Breakdown.CellCert.CellEnergy.pairForm_holds_of_parts`)

### Breakdown.FracCell.EnergyPairIntegrable

This file proves that the finite basis pairings entering the local interaction matrix are integrable on the compact cell rectangle.

**Bounded measurable cell functions.** The predicate combines almost-everywhere strong measurability on the rectangle with a pointwise finite norm bound there. (`Breakdown.FracInternal.EnergyPairIntegrable.Bdd`)

**Constants are bounded cell functions.** Every constant complex function is bounded and measurable on a cell rectangle. (`Breakdown.FracInternal.EnergyPairIntegrable.bdd_const`)

**Bounded cell functions add.** The sum of two bounded measurable cell functions is bounded and measurable. (`Breakdown.FracInternal.EnergyPairIntegrable.bdd_add`)

**Bounded cell functions subtract.** The difference of two bounded measurable cell functions is bounded and measurable. (`Breakdown.FracInternal.EnergyPairIntegrable.bdd_sub`)

**Negate a bounded cell function.** Negating a bounded measurable cell function preserves the predicate. (`Breakdown.FracInternal.EnergyPairIntegrable.bdd_neg`)

**Bounded cell functions multiply.** The product of two bounded measurable cell functions is bounded and measurable. (`Breakdown.FracInternal.EnergyPairIntegrable.bdd_mul`)

**Conjugate a bounded cell function.** Complex conjugation preserves bounded measurable cell functions. (`Breakdown.FracInternal.EnergyPairIntegrable.bdd_conj`)

**Finite sums of bounded cell functions.** A finite sum of bounded measurable cell functions is bounded and measurable. (`Breakdown.FracInternal.EnergyPairIntegrable.bdd_sum`)

**Compactness of the cell rectangle.** Every cell rectangle is compact. (`Breakdown.FracInternal.EnergyPairIntegrable.rect_compact`)

**Continuous cell functions are bounded.** A continuous complex function is bounded and measurable on each cell rectangle. (`Breakdown.FracInternal.EnergyPairIntegrable.bdd_cont`)

**Bounded cell functions are integrable.** A bounded measurable complex cell function is integrable on the cell rectangle. (`Breakdown.FracInternal.EnergyPairIntegrable.Bdd.integrableOn`)

**Basis polynomials are bounded on cells.** Every complex cell basis polynomial is bounded and measurable on a cell rectangle. (`Breakdown.FracInternal.EnergyPairIntegrable.bdd_basis`)

**Strain slot components are bounded.** Each strain component of a low slot value is bounded and measurable on the rectangle. (`Breakdown.FracInternal.EnergyPairIntegrable.bdd_slot_fst`)

**Velocity slot components are bounded.** Each velocity component of a low slot value is bounded and measurable on the rectangle. (`Breakdown.FracInternal.EnergyPairIntegrable.bdd_slot_snd`)

**Modes of bounded fields are bounded.** An almost-everywhere measurable globally bounded matrix field has bounded measurable modal entries on each valid cell. (`Breakdown.FracInternal.EnergyPairIntegrable.bdd_mode`)

**Curl combinations are bounded.** Bounded measurable matrix entries give bounded measurable curl components. (`Breakdown.FracInternal.EnergyPairIntegrable.bdd_curl`)

**The coupling map is bounded.** Bounded measurable matrix and velocity components give bounded measurable components of the coupling map. (`Breakdown.FracInternal.EnergyPairIntegrable.bdd_coupling`)

**The wave pairing is bounded.** If all listed model, strain and velocity components are bounded and measurable, their wave-form combination is bounded and measurable. (`Breakdown.FracInternal.EnergyPairIntegrable.bdd_wave`)

**The pair vector is bounded.** Bounded measurable strain and velocity components give bounded measurable components of the combined pair vector. (`Breakdown.FracInternal.EnergyPairIntegrable.bdd_pairVec`)

**The matrix pairing is bounded.** Bounded measurable matrix entries and vector components give a bounded measurable matrix pairing. (`Breakdown.FracInternal.EnergyPairIntegrable.bdd_msesq`)

**Recover the physical radial weight.** The cell line weight multiplied by the normalized radial factor equals the radius. (`Breakdown.FracInternal.EnergyPairIntegrable.weight_eq`)

**All basis pairings are integrable.** Under the energy-setting hypotheses, every retained mode and basis-slot pairing is integrable on the cell rectangle after multiplication by the specified radial weight. (`Breakdown.CellCert.CellEnergy.pairIntegrable_holds`)

### Breakdown.FracCell.EnergyRadial

This file closes the radial component-form identity from the radial trace interface and the companion projection and pairing lemmas.

**The radial component form.** The radial-trace statement identifies the sum of projected, outer and applicable inner radial matrix forms with the corresponding radial energy in every valid energy setting. (`Breakdown.CellCert.CellEnergy.componentRadial`)

### Breakdown.FracCell.EnergyRadialForm

This file proves the finite-dimensional quadratic-form identities and inverse-Gram supremum used by the radial energy calculation.

**Radial form values add.** The quadratic value of a sum of radial matrices is the sum of their values. (`Breakdown.CellCert.CellEnergy.RadialForm.value_add`)

**The zero matrix has zero value.** The quadratic value of the zero matrix is zero. (`Breakdown.CellCert.CellEnergy.RadialForm.value_zero`)

**The row-pullback matrix formula.** The row-based form equals the conjugate-transpose row matrix times the Gram matrix times the row matrix. (`Breakdown.CellCert.CellEnergy.RadialForm.formOfRows_eq`)

**Evaluate a row-pullback matrix.** The row-pullback quadratic value equals the real Gram pairing of the row evaluations. (`Breakdown.CellCert.CellEnergy.RadialForm.value_formOfRows`)

**Swap a Hermitian Gram pairing.** A Hermitian Gram pairing equals the conjugate of the pairing with its arguments exchanged. (`Breakdown.CellCert.CellEnergy.RadialForm.conj_swap`)

**Hermitian self-pairings are real.** A Hermitian Gram matrix's self-pairing equals its real part embedded in the complex numbers. (`Breakdown.CellCert.CellEnergy.RadialForm.real_form`)

**Bound a normalized Gram pairing.** For a nonnegative Hermitian form and a test vector of positive energy, the normalized squared mixed pairing is bounded by the other vector's energy. (`Breakdown.CellCert.CellEnergy.RadialForm.ratio_le`)

**The radial inverse-Gram supremum.** Strict positivity on nonzero vectors and an invertible Gram determinant identify the dual-pairing supremum with the inverse-Gram quadratic value. (`Breakdown.CellCert.CellEnergy.RadialForm.sup_identity`)

### Breakdown.FracCell.EnergyRadialPairing

This file supplies polynomial independence and strict positivity of the weighted Gram matrix needed to invert radial test pairings.

**Polynomial independence on infinite sets.** A finite complex polynomial vanishing on an infinite set of real inputs has zero coefficients. (`Breakdown.CellCert.CellEnergy.RadialForm.poly_indep`)

**Monomial independence on rectangles.** A bivariate finite complex polynomial vanishing on a nonempty open rectangle has zero coefficients. (`Breakdown.CellCert.CellEnergy.RadialForm.monomial_indep`)

**The test Gram matrix is Hermitian.** A real weighted Gram matrix of real test functions is Hermitian. (`Breakdown.CellCert.CellEnergy.RadialForm.pairing_selfAdj`)

**Gram energy as a weighted square.** With integrable basis products, the real Gram quadratic value equals the integral of the weighted squared norm of the test expansion. (`Breakdown.CellCert.CellEnergy.RadialForm.pairing_value`)

**Strict positivity of the test Gram form.** Continuous independent tests and a continuous nonnegative weight positive on the interior give positive Gram energy for every nonzero coefficient vector. (`Breakdown.CellCert.CellEnergy.RadialForm.pairing_pos`)

**Strict positivity gives invertibility.** A complex matrix with strictly positive real self-pairing on every nonzero vector has an invertible determinant. (`Breakdown.CellCert.CellEnergy.RadialForm.pairing_unit`)
<!-- /passage:front -->

