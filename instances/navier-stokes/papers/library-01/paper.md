
<!-- passage:front -->
# Library guide 1: Breakdown/Base, Breakdown/CellReduction

**Navier–Stokes pages:** [the paper](../navier-stokes-paper/paper.pdf) · [proof routes](../navier-stokes-routes/paper.md) · [routes in detail](../navier-stokes-route-details/paper.md) · library guide: **1** [2](../navier-stokes-library-02/paper.md) [3](../navier-stokes-library-03/paper.md) [4](../navier-stokes-library-04/paper.md) [5](../navier-stokes-library-05/paper.md) [6](../navier-stokes-library-06/paper.md) [7](../navier-stokes-library-07/paper.md) [8](../navier-stokes-library-08/paper.md) [9](../navier-stokes-library-09/paper.md) [10](../navier-stokes-library-10/paper.md) [11](../navier-stokes-library-11/paper.md) [12](../navier-stokes-library-12/paper.md) [13](../navier-stokes-library-13/paper.md) [14](../navier-stokes-library-14/paper.md) [15](../navier-stokes-library-15/paper.md) [16](../navier-stokes-library-16/paper.md) [17](../navier-stokes-library-17/paper.md) [18](../navier-stokes-library-18/paper.md) [19](../navier-stokes-library-19/paper.md) [20](../navier-stokes-library-20/paper.md) [21](../navier-stokes-library-21/paper.md) [22](../navier-stokes-library-22/paper.md) [23](../navier-stokes-library-23/paper.md) [24](../navier-stokes-library-24/paper.md) [25](../navier-stokes-library-25/paper.md) [26](../navier-stokes-library-26/paper.md) [27](../navier-stokes-library-27/paper.md) [28](../navier-stokes-library-28/paper.md) [29](../navier-stokes-library-29/paper.md) [30](../navier-stokes-library-30/paper.md)

*A plain title and a sentence for each declaration in `Breakdown.Base.Framework` to `Breakdown.CellReduction.InstOffsetIdentity` of Alpöge and Buckmaster's Lean at `ad53419de079eb8f95f60313473374624a348546`, in the authors' file order. Prepared with AI assistance. The authors have not reviewed it.*

Each paragraph names one declaration and says whether it is a definition, a proposition that the library defines (its name usually ends in `Holds` or `Statement`) or a proved result, then what it states. Click a paragraph to open its Lean on the right.
<!-- /passage:front -->

## Breakdown/Base

<!-- passage:sec-breakdown-base -->

### Breakdown.Base.Framework

The abstract evolution separates heat flow, dilation and the bilinear interaction, then states the compatibility needed to pass into similarity time.

**Paper context:** §2.1 and Proposition 2.1; abstract support for the profile-to-breakdown argument.

**Definition: Evolution in similarity time.** The similarity-time linear operator applies heat evolution at one minus the exponential time scale, then dilates by the exponential scale. Source: `Breakdown.MildFramework.S` (`Breakdown/Base/Framework.lean:46`).

**Definition: The similarity-time interaction.** The similarity-time interaction applies the bilinear evolution at one minus the negative-time exponential and then dilates by that exponential. Source: `Breakdown.MildFramework.Ks` (`Breakdown/Base/Framework.lean:48`).

**Definition: Evolution respects an isometry.** This proposition requires that the isometry commutes with heat evolution, bilinear interaction and dilation. Source: `Breakdown.MildFramework.Commutes` (`Breakdown/Base/Framework.lean:50`).

### Breakdown.Base.Realization

The physical realization compares vector fields through field, gradient and convection pairings.

**Paper context:** §2.1 and Appendix A.1; support for reading the abstract evolution as the PDE.

**Definition: Pairing of the spatial gradients.** The gradient pairing integrates the sum of the coordinatewise derivative inner products. Source: `Breakdown.gradientPairing` (`Breakdown/Base/Realization.lean:23`).

**Definition: Pairing with convection.** The convection pairing integrates the inner product of advection with the test field. Source: `Breakdown.advectionPairing` (`Breakdown/Base/Realization.lean:26`).

**Definition: Pairing of the physical fields.** The field pairing integrates the ordinary vector inner product over space. Source: `Breakdown.fieldPairing` (`Breakdown/Base/Realization.lean:29`).
<!-- /passage:sec-breakdown-base -->

## Breakdown/CellReduction

<!-- passage:sec-breakdown-cellreduction -->

### Breakdown.CellReduction.AdjointAssembly

The adjoint defect estimate first needs finite period integrals and the algebra for summing its separate errors.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: Integrate the six adjoint terms.** The sum of the six integrable adjoint contributions is integrable, and its integral splits into the same scalar-weighted sums of integrals. Source: `Breakdown.AdjointDefect.Internal.integral_six` (`Breakdown/CellReduction/AdjointAssembly.lean:16`).

**Theorem: The dual error bound is nonnegative.** The dual-bound hypothesis implies that its error coefficient is nonnegative. Source: `Breakdown.AdjointDefect.Internal.dualBounded_nonneg` (`Breakdown/CellReduction/AdjointAssembly.lean:39`).

**Theorem: The zero matrix pairs to zero.** The matrix pairing with a zero second argument is zero. Source: `Breakdown.AdjointDefect.Internal.periodMatrixIntegral_zero` (`Breakdown/CellReduction/AdjointAssembly.lean:43`).

**Theorem: Matrix squares of a sum.** The column-square sum of two matrices added together is at most twice the sum of their individual column-square sums. Source: `Breakdown.AdjointDefect.Internal.colSq_add_le` (`Breakdown/CellReduction/AdjointAssembly.lean:47`).

**Theorem: The matrix square norm is continuous.** The sum of the squared matrix-column norms depends continuously on the matrix. Source: `Breakdown.AdjointDefect.Internal.colSq_continuous` (`Breakdown/CellReduction/AdjointAssembly.lean:54`).

**Theorem: Subadditivity of the period integral.** The nonnegative period integral of a sum is at most the sum of the two nonnegative period integrals. Source: `Breakdown.AdjointDefect.Internal.periodLIntegral_add_le_of_joint` (`Breakdown/CellReduction/AdjointAssembly.lean:58`).

**Theorem: Doubling preserves finite period size.** Multiplying a field by two preserves finiteness of its nonnegative period integral. Source: `Breakdown.AdjointDefect.Internal.periodLIntegral_two_mul_lt_top` (`Breakdown/CellReduction/AdjointAssembly.lean:77`).

**Theorem: Finite square integral of a pin.** The round bounds imply that each pin matrix has a finite period square integral. Source: `Breakdown.AdjointDefect.Internal.pinSquare_finite_of_round` (`Breakdown/CellReduction/AdjointAssembly.lean:83`).

### Breakdown.CellReduction.AdjointAssemblyAlgebra

Transpose identities, matrix pairings and parameter-coordinate bounds let the adjoint residual split into its pin and flow contributions.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: Transpose action preserves addition.** Applying the transpose of a sum equals the sum of the two transpose actions. Source: `Breakdown.AdjointDefect.Internal.transposeApply_add` (`Breakdown/CellReduction/AdjointAssemblyAlgebra.lean:15`).

**Theorem: Transpose action preserves scaling.** A scalar factor can be pulled outside the transpose action. Source: `Breakdown.AdjointDefect.Internal.transposeApply_smul` (`Breakdown/CellReduction/AdjointAssemblyAlgebra.lean:19`).

**Theorem: The zero transpose acts as zero.** The transpose action of the zero matrix is zero. Source: `Breakdown.AdjointDefect.Internal.transposeApply_zero` (`Breakdown/CellReduction/AdjointAssemblyAlgebra.lean:23`).

**Theorem: Transpose action preserves finite sums.** The transpose action distributes over a finite scalar-weighted matrix sum. Source: `Breakdown.AdjointDefect.Internal.transposeApply_sum` (`Breakdown/CellReduction/AdjointAssemblyAlgebra.lean:26`).

**Theorem: Coordinate vectors have unit norm.** Every coordinate unit vector has norm one. Source: `Breakdown.AdjointDefect.Internal.norm_unitVector` (`Breakdown/CellReduction/AdjointAssemblyAlgebra.lean:34`).

**Theorem: Bound the transpose action.** The transpose action has norm at most three times the matrix operator norm times the vector norm. Source: `Breakdown.AdjointDefect.Internal.norm_transposeApply_le` (`Breakdown/CellReduction/AdjointAssemblyAlgebra.lean:37`).

**Theorem: Coordinates stay inside their bounds.** A coefficient vector in the entry box has each coordinate bounded in absolute value by its assigned coordinate bound. Source: `Breakdown.AdjointDefect.Internal.coord_le_bound` (`Breakdown/CellReduction/AdjointAssemblyAlgebra.lean:82`).

**Theorem: Matrix pairing preserves addition.** The matrix pairing distributes over addition in its second argument. Source: `Breakdown.AdjointDefect.Internal.matrixPairing_add` (`Breakdown/CellReduction/AdjointAssemblyAlgebra.lean:97`).

**Theorem: Matrix pairing preserves subtraction.** The matrix pairing distributes over subtraction in its second argument. Source: `Breakdown.AdjointDefect.Internal.matrixPairing_sub` (`Breakdown/CellReduction/AdjointAssemblyAlgebra.lean:100`).

**Theorem: Scale the matrix pairing.** A scalar factor in the second matrix becomes the same scalar factor outside the pairing. Source: `Breakdown.AdjointDefect.Internal.matrixPairing_smul` (`Breakdown/CellReduction/AdjointAssemblyAlgebra.lean:103`).

**Theorem: The zero matrix pairs to zero.** The matrix pairing with a zero second argument is zero. Source: `Breakdown.AdjointDefect.Internal.matrixPairing_zero` (`Breakdown/CellReduction/AdjointAssemblyAlgebra.lean:106`).

**Theorem: Pair a finite matrix sum.** The matrix pairing of a finite weighted sum equals the weighted sum of the pairings. Source: `Breakdown.AdjointDefect.Internal.matrixPairing_sum` (`Breakdown/CellReduction/AdjointAssemblyAlgebra.lean:109`).

**Theorem: Split the adjoint gradient pairing.** The adjoint gradient pairing splits into the pin-flux pairing and the weighted antisymmetric generator pairings. Source: `Breakdown.AdjointDefect.Internal.matrixPairing_pin_split` (`Breakdown/CellReduction/AdjointAssemblyAlgebra.lean:117`).

### Breakdown.CellReduction.AdjointAssemblyBasics

Differentiation of time slices and closure of the decay classes keep the adjoint, potential and flow pieces admissible under linear combinations.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: Spatial slice of a joint derivative.** The derivative on a fixed time slice is the joint derivative restricted to the spatial direction. Source: `Breakdown.AdjointDefect.Internal.slice_hasFDerivAt` (`Breakdown/CellReduction/AdjointAssemblyBasics.lean:14`).

**Theorem: The spatial slice is differentiable.** Joint continuous differentiability gives differentiability of each spatial slice at the specified point. Source: `Breakdown.AdjointDefect.Internal.slice_differentiableAt` (`Breakdown/CellReduction/AdjointAssemblyBasics.lean:23`).

**Theorem: Read the derivative of a spatial slice.** The spatial derivative of the slice is the joint derivative composed with the spatial inclusion. Source: `Breakdown.AdjointDefect.Internal.slice_fderiv_eq` (`Breakdown/CellReduction/AdjointAssemblyBasics.lean:28`).

**Theorem: The spatial derivative is continuous.** The spatial derivative of the joint continuously differentiable field is continuous in time and space. Source: `Breakdown.AdjointDefect.Internal.slice_fderiv_continuous` (`Breakdown/CellReduction/AdjointAssemblyBasics.lean:34`).

**Theorem: Time derivative from the joint map.** Differentiation in time is the joint derivative applied to the unit time direction. Source: `Breakdown.AdjointDefect.Internal.time_hasDerivAt` (`Breakdown/CellReduction/AdjointAssemblyBasics.lean:44`).

**Theorem: The time derivative is continuous.** The time derivative of the jointly continuously differentiable field is continuous in time and space. Source: `Breakdown.AdjointDefect.Internal.timeDerivative_continuous` (`Breakdown/CellReduction/AdjointAssemblyBasics.lean:52`).

**Theorem: Increase the adjoint decay bound.** An admissible adjoint field remains admissible after increasing its decay constant. Source: `Breakdown.AdjointDefect.Internal.adjointField_mono` (`Breakdown/CellReduction/AdjointAssemblyBasics.lean:62`).

**Theorem: Increase the curl-potential bound.** An admissible curl potential remains admissible after increasing its decay constant. Source: `Breakdown.AdjointDefect.Internal.curlPotential_mono` (`Breakdown/CellReduction/AdjointAssemblyBasics.lean:75`).

**Theorem: Increase the residual decay bound.** An admissible residual field remains admissible after increasing its decay constant. Source: `Breakdown.AdjointDefect.Internal.residualField_mono` (`Breakdown/CellReduction/AdjointAssemblyBasics.lean:84`).

**Theorem: Increase the potential bound.** The potential data remain admissible after increasing their common bound. Source: `Breakdown.AdjointDefect.Internal.potentialData_mono` (`Breakdown/CellReduction/AdjointAssemblyBasics.lean:95`).

**Theorem: The flow bound is nonnegative.** The admissible flow-piece bound is nonnegative. Source: `Breakdown.AdjointDefect.Internal.flowPiece_nonneg` (`Breakdown/CellReduction/AdjointAssemblyBasics.lean:114`).

**Theorem: Increase the flow-piece bound.** An admissible flow piece remains admissible after increasing its common bound. Source: `Breakdown.AdjointDefect.Internal.flowPiece_mono` (`Breakdown/CellReduction/AdjointAssemblyBasics.lean:117`).

**Theorem: Transport the flow class by equality.** Pointwise equality preserves the admissible flow-piece class. Source: `Breakdown.AdjointDefect.Internal.flowPiece_congr` (`Breakdown/CellReduction/AdjointAssemblyBasics.lean:124`).

**Theorem: The zero field is a flow piece.** The zero vector field is an admissible flow piece with bound zero. Source: `Breakdown.AdjointDefect.Internal.flowPiece_zero` (`Breakdown/CellReduction/AdjointAssemblyBasics.lean:129`).

**Theorem: Add two admissible flow pieces.** The sum of two admissible flow pieces has a bound equal to the sum of their bounds. Source: `Breakdown.AdjointDefect.Internal.flowPiece_add` (`Breakdown/CellReduction/AdjointAssemblyBasics.lean:134`).

**Theorem: Scale an admissible flow piece.** Scaling a flow piece multiplies its bound by the absolute value of the scalar. Source: `Breakdown.AdjointDefect.Internal.flowPiece_smul` (`Breakdown/CellReduction/AdjointAssemblyBasics.lean:155`).

**Theorem: Sum finitely many flow pieces.** A finite scalar-weighted sum of uniformly bounded flow pieces is bounded by the sum of the absolute coefficients times the common bound. Source: `Breakdown.AdjointDefect.Internal.flowPiece_sum` (`Breakdown/CellReduction/AdjointAssemblyBasics.lean:174`).

### Breakdown.CellReduction.AdjointAssemblyCentre

The centre residual is built from weak divergence identities, compactly supported pin generators and decay estimates.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: Coordinate vectors have unit norm.** Every coordinate unit vector has norm one. Source: `Breakdown.AdjointDefect.Internal.CentreResidual.norm_unitVector` (`Breakdown/CellReduction/AdjointAssemblyCentre.lean:14`).

**Theorem: Coordinates as inner products.** A vector coordinate equals its inner product with the corresponding coordinate unit vector. Source: `Breakdown.AdjointDefect.Internal.CentreResidual.component_eq_inner` (`Breakdown/CellReduction/AdjointAssemblyCentre.lean:17`).

**Theorem: Adjoint entries are transposed.** The matrix adjoint exchanges the two coordinate indices. Source: `Breakdown.AdjointDefect.Internal.CentreResidual.adjoint_component` (`Breakdown/CellReduction/AdjointAssemblyCentre.lean:20`).

**Theorem: Read a coordinate of a finite sum.** Taking a vector coordinate commutes with the finite sum. Source: `Breakdown.AdjointDefect.Internal.CentreResidual.sum_component` (`Breakdown/CellReduction/AdjointAssemblyCentre.lean:24`).

**Theorem: Read weak derivatives componentwise.** Testing a weak derivative in a coordinate direction gives two integrable scalar products whose integrals are negatives of one another. Source: `Breakdown.AdjointDefect.Internal.CentreResidual.weak_component` (`Breakdown/CellReduction/AdjointAssemblyCentre.lean:28`).

**Definition: Weak matrix divergence.** This proposition requires that the matrix field and vector field obey the componentwise distributional divergence identity. Source: `Breakdown.AdjointDefect.Internal.CentreResidual.WeakDivPair` (`Breakdown/CellReduction/AdjointAssemblyCentre.lean:55`).

**Theorem: Weak divergence respects zero.** The zero matrix field has zero weak divergence. Source: `Breakdown.AdjointDefect.Internal.CentreResidual.weakDivPair_zero` (`Breakdown/CellReduction/AdjointAssemblyCentre.lean:61`).

**Theorem: Weak divergence respects addition.** The weak matrix-divergence identity is preserved by addition. Source: `Breakdown.AdjointDefect.Internal.CentreResidual.weakDivPair_add` (`Breakdown/CellReduction/AdjointAssemblyCentre.lean:65`).

**Theorem: Weak divergence respects subtraction.** The weak matrix-divergence identity is preserved by subtraction. Source: `Breakdown.AdjointDefect.Internal.CentreResidual.weakDivPair_sub` (`Breakdown/CellReduction/AdjointAssemblyCentre.lean:84`).

**Theorem: Scale a weak divergence identity.** The weak matrix-divergence identity is preserved by scalar multiplication. Source: `Breakdown.AdjointDefect.Internal.CentreResidual.weakDivPair_smul` (`Breakdown/CellReduction/AdjointAssemblyCentre.lean:103`).

**Theorem: Weak divergence respects finite sums.** The weak matrix-divergence identity is preserved by finite sums. Source: `Breakdown.AdjointDefect.Internal.CentreResidual.weakDivPair_sum` (`Breakdown/CellReduction/AdjointAssemblyCentre.lean:123`).

**Theorem: The gradient has its Laplacian trace.** The weak divergence of the gradient matrix is the trace of the weak second derivative. Source: `Breakdown.AdjointDefect.Internal.CentreResidual.weakDivPair_grad` (`Breakdown/CellReduction/AdjointAssemblyCentre.lean:134`).

**Theorem: Divergence of the transposed gradient.** The adjoint gradient has the weak divergence given by the coordinate traces of the adjoint second derivative. Source: `Breakdown.AdjointDefect.Internal.CentreResidual.weakDivPair_adjoint` (`Breakdown/CellReduction/AdjointAssemblyCentre.lean:152`).

**Theorem: Bound the transpose action.** The transpose action has norm at most three times the matrix operator norm times the vector norm. Source: `Breakdown.AdjointDefect.Internal.CentreResidual.transposeApply_norm_le` (`Breakdown/CellReduction/AdjointAssemblyCentre.lean:178`).

**Theorem: One bound for the periodic field.** The periodic scalar field with bounded spatial support has a common nonnegative upper bound for all times and positions. Source: `Breakdown.AdjointDefect.Internal.CentreResidual.exists_bound_periodic` (`Breakdown/CellReduction/AdjointAssemblyCentre.lean:194`).

**Theorem: Turn bounded support into a decay bound.** A bound B supported at radii at most R is also bounded by B times (1+|R|)^e divided by (1+t)^e. Source: `Breakdown.AdjointDefect.Internal.CentreResidual.le_decay_of_support` (`Breakdown/CellReduction/AdjointAssemblyCentre.lean:217`).

**Theorem: The derivative vanishes off the support.** Outside the stated support region, the field is locally zero and its derivative vanishes. Source: `Breakdown.AdjointDefect.Internal.CentreResidual.fderiv_eq_zero_of_support` (`Breakdown/CellReduction/AdjointAssemblyCentre.lean:229`).

**Theorem: The Hessian vanishes off the support.** Outside the stated support region, the second derivative vanishes. Source: `Breakdown.AdjointDefect.Internal.CentreResidual.secondDeriv_eq_zero_of_support` (`Breakdown/CellReduction/AdjointAssemblyCentre.lean:238`).

**Definition: Adjoint as a bounded linear map.** The matrix adjoint is packaged as a continuous linear map on matrices. Source: `Breakdown.AdjointDefect.Internal.CentreResidual.adjointLinear` (`Breakdown/CellReduction/AdjointAssemblyCentre.lean:243`).

**Theorem: Read the adjoint linear map.** The packaged continuous linear map evaluates to the ordinary matrix adjoint. Source: `Breakdown.AdjointDefect.Internal.CentreResidual.adjointLinear_apply` (`Breakdown/CellReduction/AdjointAssemblyCentre.lean:250`).

**Theorem: The adjoint map has norm at most one.** The operator norm of the map taking a matrix to its adjoint is at most one. Source: `Breakdown.AdjointDefect.Internal.CentreResidual.adjointLinear_norm_le` (`Breakdown/CellReduction/AdjointAssemblyCentre.lean:253`).

**Theorem: Bound a five-term transport sum.** The norm of the five-term transport combination is at most the sum of the component norms multiplied by their absolute coefficients. Source: `Breakdown.AdjointDefect.Internal.CentreResidual.norm_transport_le` (`Breakdown/CellReduction/AdjointAssemblyCentre.lean:256`).

**Theorem: Bound the pin-corrected flux.** The pin-corrected flux norm is bounded by the profile derivative norm plus twice the coefficient-weighted sum of generator derivative norms. Source: `Breakdown.AdjointDefect.Internal.CentreResidual.norm_pinFlux_le` (`Breakdown/CellReduction/AdjointAssemblyCentre.lean:264`).

**Theorem: Bound the corrected second derivative.** Subtracting the skew parts of the generator Hessians increases the norm by at most twice their absolute-coefficient-weighted norms. Source: `Breakdown.AdjointDefect.Internal.CentreResidual.norm_secondCombo_le` (`Breakdown/CellReduction/AdjointAssemblyCentre.lean:275`).

**Theorem: Bound the second-derivative trace.** The norm of the diagonal trace is at most three times the norm of the second-derivative map. Source: `Breakdown.AdjointDefect.Internal.CentreResidual.norm_diagSum_le` (`Breakdown/CellReduction/AdjointAssemblyCentre.lean:286`).

**Theorem: Trace the corrected Hessian.** The diagonal trace of the corrected Hessian equals the original trace minus the coefficient-weighted difference of the generator trace and its adjoint trace. Source: `Breakdown.AdjointDefect.Internal.CentreResidual.diagSum_combo` (`Breakdown/CellReduction/AdjointAssemblyCentre.lean:296`).

**Theorem: Construct the centre residual.** The adjoint transport and pin flux form a decaying residual under the adjoint, flow-piece and pin hypotheses. Source: `Breakdown.AdjointDefect.centreResidualField_proof` (`Breakdown/CellReduction/AdjointAssemblyCentre.lean:314`).

**Theorem: Construct the centre residual.** Under the stated hypotheses, the adjoint transport and pin flux form a decaying residual under the adjoint, flow-piece and pin hypotheses. Source: `Breakdown.AdjointDefect.centreResidualField_of_slope` (`Breakdown/CellReduction/AdjointAssemblyCentre.lean:467`).

### Breakdown.CellReduction.AdjointAssemblyFields

This file controls the adjoint transport, its change under convection and the gradient energy used to estimate their pairings.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: Transpose evaluation is continuous.** Applying the transpose of a matrix to a vector depends continuously on both inputs. Source: `Breakdown.AdjointDefect.Internal.continuous_transposeApply` (`Breakdown/CellReduction/AdjointAssemblyFields.lean:14`).

**Theorem: The shifted advection is continuous.** The regularity hypotheses make the shifted advection field jointly continuous in time and space. Source: `Breakdown.AdjointDefect.Internal.continuous_advectionShift` (`Breakdown/CellReduction/AdjointAssemblyFields.lean:19`).

**Theorem: The adjoint transport is continuous.** The regularity hypotheses make the adjoint transport field jointly continuous in time and space. Source: `Breakdown.AdjointDefect.Internal.continuous_adjointTransport` (`Breakdown/CellReduction/AdjointAssemblyFields.lean:26`).

**Theorem: The field decay constant is nonnegative.** The admissibility assumptions force the stated field decay constant to be nonnegative. Source: `Breakdown.AdjointDefect.Internal.adjointField_nonneg` (`Breakdown/CellReduction/AdjointAssemblyFields.lean:37`).

**Theorem: Decay of shifted advection.** The shifted advection norm is at most 4DC divided by (1+|y|) to the power gamma. Source: `Breakdown.AdjointDefect.Internal.norm_advectionShift_le` (`Breakdown/CellReduction/AdjointAssemblyFields.lean:42`).

**Theorem: Decay of adjoint transport.** The adjoint transport norm is bounded by (|1/P|+2+4D)C times the prescribed gamma-order radial decay. Source: `Breakdown.AdjointDefect.Internal.norm_adjointTransport_le` (`Breakdown/CellReduction/AdjointAssemblyFields.lean:68`).

**Theorem: Decay after fitting the time derivative.** Subtracting c times the time derivative gives the residual norm bound (4D+|c|)C times the prescribed radial decay. Source: `Breakdown.AdjointDefect.Internal.norm_fittedResidual_le` (`Breakdown/CellReduction/AdjointAssemblyFields.lean:100`).

**Theorem: The zero flux has zero divergence.** The matrix divergence of the zero field is zero. Source: `Breakdown.AdjointDefect.Internal.matrixDivergence_zero` (`Breakdown/CellReduction/AdjointAssemblyFields.lean:113`).

**Theorem: Admissible adjoint residual.** Under the stated hypotheses, the residual and flux are measurable, the flux has its weak divergence, and all three satisfy the stated decay bounds. Source: `Breakdown.AdjointDefect.Internal.fittedField` (`Breakdown/CellReduction/AdjointAssemblyFields.lean:117`).

**Theorem: Energy controls the gradient norm.** For positive constant weight, the gradient norm is at most the square root of weighted energy divided by the square root of that weight. Source: `Breakdown.AdjointDefect.Internal.gradientNorm_le` (`Breakdown/CellReduction/AdjointAssemblyFields.lean:138`).

**Theorem: Bound a periodic compact field.** Joint continuity, time periodicity and common compact spatial support give a uniform bound on the field norm. Source: `Breakdown.AdjointDefect.Internal.exists_bound_periodic_compact` (`Breakdown/CellReduction/AdjointAssemblyFields.lean:187`).

**Theorem: Decay of the skew generator flux.** The generator derivative minus its adjoint is jointly continuous and has one uniform inverse-square spatial decay bound. Source: `Breakdown.AdjointDefect.Internal.generatorFlux_bound` (`Breakdown/CellReduction/AdjointAssemblyFields.lean:205`).

### Breakdown.CellReduction.AdjointAssemblyMeasure

The product measure on one time period makes the decay and integrability estimates compatible with the iterated integrals used in the certificate.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Definition: Measure over one time period.** The period measure is Lebesgue measure on the closed unit interval times spatial Lebesgue measure. Source: `Breakdown.AdjointDefect.Internal.periodMeasure` (`Breakdown/CellReduction/AdjointAssemblyMeasure.lean:14`).

**Theorem: The period measure is dominated.** The period product measure is absolutely continuous with respect to spacetime Lebesgue measure. Source: `Breakdown.AdjointDefect.Internal.periodMeasure_ac` (`Breakdown/CellReduction/AdjointAssemblyMeasure.lean:16`).

**Theorem: Restrict measurability to one period.** Almost-everywhere strong measurability on spacetime passes to the product measure restricted to one time period. Source: `Breakdown.AdjointDefect.Internal.aesm_period` (`Breakdown/CellReduction/AdjointAssemblyMeasure.lean:20`).

**Theorem: Fubini over one time period.** For an integrable field, the iterated period integral equals the integral against the period product measure. Source: `Breakdown.AdjointDefect.Internal.iterated_eq` (`Breakdown/CellReduction/AdjointAssemblyMeasure.lean:24`).

**Theorem: Product form of the period integral.** The nonnegative iterated period integral equals the integral against the product measure on the unit period. Source: `Breakdown.AdjointDefect.Internal.periodL_eq` (`Breakdown/CellReduction/AdjointAssemblyMeasure.lean:28`).

**Theorem: Integrable decay beyond dimension three.** The radial weight with decay exponent greater than three is integrable in three-dimensional space. Source: `Breakdown.AdjointDefect.Internal.space_weight_integrable` (`Breakdown/CellReduction/AdjointAssemblyMeasure.lean:33`).

**Theorem: Increase a nonnegative radial power.** Increasing the exponent by one cannot decrease a power of one plus a nonnegative radius. Source: `Breakdown.AdjointDefect.Internal.rpow_succ_le` (`Breakdown/CellReduction/AdjointAssemblyMeasure.lean:38`).

**Theorem: One extra decay power is smaller.** For nonnegative numerator and radius, an additional denominator power decreases the decay bound. Source: `Breakdown.AdjointDefect.Internal.div_succ_le` (`Breakdown/CellReduction/AdjointAssemblyMeasure.lean:41`).

**Theorem: Radius consumes one decay power.** Multiplication by a nonnegative radius costs at most one power of one plus that radius in a decay bound. Source: `Breakdown.AdjointDefect.Internal.mul_div_succ_le` (`Breakdown/CellReduction/AdjointAssemblyMeasure.lean:45`).

**Theorem: Square a weighted radial decay bound.** Multiplying the squared gamma-order decay bound by radius squared gives decay of order twice gamma minus two. Source: `Breakdown.AdjointDefect.Internal.weighted_sq_le` (`Breakdown/CellReduction/AdjointAssemblyMeasure.lean:53`).

**Theorem: Finite radius-weighted square norm.** The decay assumptions make the period integral of radius squared times the field norm squared finite. Source: `Breakdown.AdjointDefect.Internal.weighted_period_finite` (`Breakdown/CellReduction/AdjointAssemblyMeasure.lean:67`).

**Theorem: The residual pairing is integrable.** The inverse-square control of the first field and radius-weighted square control of the second make their period pairing integrable. Source: `Breakdown.AdjointDefect.Internal.pairing_integrable` (`Breakdown/CellReduction/AdjointAssemblyMeasure.lean:84`).

**Theorem: The matrix square norm is continuous.** The sum of the squared matrix-column norms depends continuously on the matrix. Source: `Breakdown.AdjointDefect.Internal.continuous_entrySq` (`Breakdown/CellReduction/AdjointAssemblyMeasure.lean:94`).

**Theorem: Matrix square norm is nonnegative.** The sum of the squared matrix-column norms is nonnegative. Source: `Breakdown.AdjointDefect.Internal.entrySq_nonneg` (`Breakdown/CellReduction/AdjointAssemblyMeasure.lean:98`).

**Theorem: The matrix pairing is continuous.** The matrix inner product is continuous in both matrix arguments. Source: `Breakdown.AdjointDefect.Internal.continuous_matrixPairing` (`Breakdown/CellReduction/AdjointAssemblyMeasure.lean:102`).

**Theorem: Column squares versus operator norm.** The matrix column-square sum is at most three times the squared operator norm. Source: `Breakdown.AdjointDefect.Internal.entrySq_le` (`Breakdown/CellReduction/AdjointAssemblyMeasure.lean:106`).

**Theorem: Young inequality for matrix pairing.** The absolute matrix pairing is at most half of each matrix column-square sum added together. Source: `Breakdown.AdjointDefect.Internal.abs_matrixPairing_le` (`Breakdown/CellReduction/AdjointAssemblyMeasure.lean:116`).

**Theorem: Integrate the gradient square.** The finite nonnegative period gradient integral makes the column-square sum integrable over the period product measure. Source: `Breakdown.AdjointDefect.Internal.gradient_integrable` (`Breakdown/CellReduction/AdjointAssemblyMeasure.lean:124`).

**Theorem: The matrix pairing is integrable.** The stated square-integrability bounds make the matrix inner product integrable over one time period and all space. Source: `Breakdown.AdjointDefect.Internal.matrix_integrable` (`Breakdown/CellReduction/AdjointAssemblyMeasure.lean:135`).

### Breakdown.CellReduction.AdjointAssemblyPairing

Weighted Young inequalities turn a vector pairing into the inverse-square and weighted-square quantities used by the adjoint estimate.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: Split a product with radial weights.** For nonzero s, the product ab is at most a squared divided by s squared plus s squared times b squared. Source: `Breakdown.AdjointDefect.Internal.pairing_le_weighted_sum` (`Breakdown/CellReduction/AdjointAssemblyPairing.lean:14`).

**Theorem: Split the pairing by radial weight.** Away from the origin, the extended norm of the vector pairing is bounded by the inverse-square weighted first norm plus the radius-square weighted second norm. Source: `Breakdown.AdjointDefect.Internal.pairing_enorm_le` (`Breakdown/CellReduction/AdjointAssemblyPairing.lean:24`).

### Breakdown.CellReduction.AdjointAssemblyStatements

Three proposition definitions isolate the weak-gradient slope bound, weighted pairing integrability and centre-residual construction.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Interface definition: Slope from a bounded weak gradient.** This proposition requires that a continuous field with weak gradient bounded by M is Lipschitz with constant 3M. Source: `Breakdown.AdjointDefect.WeakGradientSlopeHolds` (`Breakdown/CellReduction/AdjointAssemblyStatements.lean:12`).

No theorem in the library states this proposition as its result.

**Interface definition: Integrability of the weighted pairing.** This proposition requires that the velocity-residual pairing is integrable when the weak-gradient energy and the residual's weighted square integral are finite. Source: `Breakdown.AdjointDefect.WeightedPairingIntegrableHolds` (`Breakdown/CellReduction/AdjointAssemblyStatements.lean:17`).

Supplied by `Breakdown.AdjointDefect.weightedPairingIntegrable_proof` (`lean/Breakdown/CellReduction/AdjointAssemblyPairing.lean:34`).

**Interface definition: Construct the centre residual.** This proposition requires that the adjoint transport and pin flux form a decaying residual under the adjoint, flow-piece and pin hypotheses. Source: `Breakdown.AdjointDefect.CentreResidualFieldHolds` (`Breakdown/CellReduction/AdjointAssemblyStatements.lean:29`).

Supplied by `Breakdown.AdjointDefect.centreResidualField_proof` (`lean/Breakdown/CellReduction/AdjointAssemblyCentre.lean:314`); `Breakdown.AdjointDefect.centreResidualField_of_slope` (`lean/Breakdown/CellReduction/AdjointAssemblyCentre.lean:467`).

### Breakdown.CellReduction.AdjointEntryDefs

The adjoint construction fixes its analytic classes for decaying fields, curl potentials, residuals and pin data.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Definition: Distributional scalar gradient.** This proposition requires that the scalar and vector fields are locally integrable and obey the test-function integration-by-parts identity. Source: `Breakdown.AdjointDefect.IsWeakScalarGradient` (`Breakdown/CellReduction/AdjointEntryDefs.lean:18`).

**Definition: Curl from coordinate derivatives.** The curl is the vector of the three antisymmetric coordinate derivative differences. Source: `Breakdown.AdjointDefect.curlAt` (`Breakdown/CellReduction/AdjointEntryDefs.lean:23`).

**Definition: Period vector pairing.** The period vector pairing integrates the spatial inner product over the closed unit time interval. Source: `Breakdown.AdjointDefect.periodInnerIntegral` (`Breakdown/CellReduction/AdjointEntryDefs.lean:28`).

**Definition: Period matrix pairing.** The period matrix pairing integrates the matrix inner product over the closed unit time interval. Source: `Breakdown.AdjointDefect.periodMatrixIntegral` (`Breakdown/CellReduction/AdjointEntryDefs.lean:31`).

**Definition: The period gradient norm.** The gradient norm is the square root of the real value of the period matrix-square integral. Source: `Breakdown.AdjointDefect.gradientNorm` (`Breakdown/CellReduction/AdjointEntryDefs.lean:34`).

**Definition: Admissible decaying adjoint field.** This proposition requires that the periodic divergence-free adjoint has the prescribed first and weak second derivatives and decay with exponent greater than five halves. Source: `Breakdown.AdjointDefect.IsAdjointField` (`Breakdown/CellReduction/AdjointEntryDefs.lean:37`).

**Definition: Admissible curl potential.** This proposition requires that the periodic continuously differentiable potential has the prescribed curl and decay with exponent greater than three halves. Source: `Breakdown.AdjointDefect.IsCurlPotential` (`Breakdown/CellReduction/AdjointEntryDefs.lean:49`).

**Definition: Admissible flow component.** This proposition requires that the continuously differentiable periodic field is divergence-free with bounded value and inverse-linear gradient decay. Source: `Breakdown.AdjointDefect.IsFlowPiece` (`Breakdown/CellReduction/AdjointEntryDefs.lean:57`).

**Definition: Admissible adjoint residual.** This proposition requires that the residual and flux are measurable, the flux has its weak divergence, and all three satisfy the stated decay bounds. Source: `Breakdown.AdjointDefect.IsResidualField` (`Breakdown/CellReduction/AdjointEntryDefs.lean:63`).

**Definition: Pin potentials and generators.** This proposition requires that the pin fields have compactly supported potentials and generators with the required weak derivatives, integrability and regularity. Source: `Breakdown.AdjointDefect.IsPinData` (`Breakdown/CellReduction/AdjointEntryDefs.lean:102`).

### Breakdown.CellReduction.AdjointFreeShift

The unfitted parameter directions are controlled by their weighted coordinate size and two adjoint pairing bounds.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: Matrix square norm is nonnegative.** The sum of the squared matrix-column norms is nonnegative. Source: `Breakdown.AdjointDefect.Internal.FreeShift.entrySqSum_nonneg` (`Breakdown/CellReduction/AdjointFreeShift.lean:17`).

**Theorem: The matrix square norm is continuous.** The sum of the squared matrix-column norms depends continuously on the matrix. Source: `Breakdown.AdjointDefect.Internal.FreeShift.continuous_entrySqSum` (`Breakdown/CellReduction/AdjointFreeShift.lean:20`).

**Theorem: Use the column norm to bound an image.** The norm of a matrix applied to a vector is bounded by the vector norm times the square root of the column-square sum. Source: `Breakdown.AdjointDefect.Internal.FreeShift.norm_apply_le_root` (`Breakdown/CellReduction/AdjointFreeShift.lean:24`).

**Theorem: Weighted finite Cauchy inequality.** The squared sum of absolute-coefficient products is bounded by the sum of coefficient squares divided by positive weights times the weighted sum of amplitude squares. Source: `Breakdown.AdjointDefect.Internal.FreeShift.sum_abs_mul_sq_le` (`Breakdown/CellReduction/AdjointFreeShift.lean:34`).

**Theorem: Differentiate a finite field sum.** The spatial derivative of a finite scalar combination of differentiable fields is the same combination of their spatial derivatives. Source: `Breakdown.AdjointDefect.Internal.FreeShift.fderiv_combo` (`Breakdown/CellReduction/AdjointFreeShift.lean:48`).

**Theorem: Almost every gradient slice is finite.** A finite period gradient-square integral gives a finite spatial gradient-square integral for almost every time in the unit interval. Source: `Breakdown.AdjointDefect.Internal.FreeShift.gradient_slice_finite` (`Breakdown/CellReduction/AdjointFreeShift.lean:60`).

**Theorem: Integrate the directional derivative.** The field bounds make the pairing with the directional derivative of the test field spatially integrable. Source: `Breakdown.AdjointDefect.Internal.FreeShift.convection_slice_integrable` (`Breakdown/CellReduction/AdjointFreeShift.lean:73`).

**Theorem: Bound the derivative pairing.** The absolute period pairing of G applied to F with the adjoint field is at most the square root of Q times nu times the gradient norm. Source: `Breakdown.AdjointDefect.Internal.FreeShift.pairing_bound` (`Breakdown/CellReduction/AdjointFreeShift.lean:100`).

**Theorem: Bound a free shift combination.** The free-shift pairing is bounded by the weighted coefficient norm times the sum of the two shift constants times the gradient norm. Source: `Breakdown.AdjointDefect.Internal.FreeShift.freeShift_of_combo` (`Breakdown/CellReduction/AdjointFreeShift.lean:182`).

### Breakdown.CellReduction.AdjointPinCharge

The pin correction is estimated by separating its potential error from its matrix error and integrating by parts.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: Weak gradients respect zero.** The zero vector field has the zero weak gradient. Source: `Breakdown.AdjointDefect.Internal.PinCharge.weak_zero` (`Breakdown/CellReduction/AdjointPinCharge.lean:17`).

**Theorem: Weak gradients respect addition.** The weak-gradient identity is preserved by addition. Source: `Breakdown.AdjointDefect.Internal.PinCharge.weak_add` (`Breakdown/CellReduction/AdjointPinCharge.lean:21`).

**Theorem: Scale a weak gradient identity.** The weak-gradient identity is preserved by scalar multiplication. Source: `Breakdown.AdjointDefect.Internal.PinCharge.weak_smul` (`Breakdown/CellReduction/AdjointPinCharge.lean:39`).

**Theorem: Weak gradients respect finite sums.** The weak-gradient identity is preserved by finite sums. Source: `Breakdown.AdjointDefect.Internal.PinCharge.weak_finsetSum` (`Breakdown/CellReduction/AdjointPinCharge.lean:48`).

**Theorem: Bound a periodic matrix field.** A continuous periodic matrix field with common compact spatial support has one uniform norm bound. Source: `Breakdown.AdjointDefect.Internal.PinCharge.bounded_of_periodic` (`Breakdown/CellReduction/AdjointPinCharge.lean:58`).

**Theorem: Young inequality with a free weight.** For positive weight u, the product ab is bounded by u times a squared over two plus b squared over twice u. Source: `Breakdown.AdjointDefect.Internal.PinCharge.mul_le_split_squares` (`Breakdown/CellReduction/AdjointPinCharge.lean:76`).

**Theorem: Take square roots of a product bound.** The stated square-product bound implies the corresponding product of square-root bounds. Source: `Breakdown.AdjointDefect.Internal.PinCharge.le_sqrt_mul` (`Breakdown/CellReduction/AdjointPinCharge.lean:80`).

**Theorem: Weighted Young bound for matrices.** For positive u, the absolute matrix inner product is at most u/2 times the first column-square sum plus 1/(2u) times the second. Source: `Breakdown.AdjointDefect.Internal.PinCharge.abs_pairMatrix_le` (`Breakdown/CellReduction/AdjointPinCharge.lean:117`).

**Theorem: Weighted Young bound for vectors.** For positive u, the absolute vector inner product is at most u/2 times the first norm squared plus 1/(2u) times the second. Source: `Breakdown.AdjointDefect.Internal.PinCharge.abs_inner_le` (`Breakdown/CellReduction/AdjointPinCharge.lean:124`).

**Theorem: Cauchy bound for an integral.** The pointwise square-product majorant bounds the absolute integral by the product of the square roots of the two majorant integrals. Source: `Breakdown.AdjointDefect.Internal.PinCharge.abs_integral_le` (`Breakdown/CellReduction/AdjointPinCharge.lean:128`).

**Theorem: The Laplacian trace is continuous.** Taking the trace of the second derivative is a continuous operation. Source: `Breakdown.AdjointDefect.Internal.PinCharge.continuous_trace` (`Breakdown/CellReduction/AdjointPinCharge.lean:140`).

**Theorem: Finite period size gives integrability.** The measurability and finite nonnegative period integral assumptions make the scalar field integrable for the period product measure. Source: `Breakdown.AdjointDefect.Internal.PinCharge.period_integrable` (`Breakdown/CellReduction/AdjointPinCharge.lean:144`).

**Theorem: Transfer a period integral bound.** The bound on the nonnegative period integral gives the same upper bound for the real integral against the period product measure. Source: `Breakdown.AdjointDefect.Internal.PinCharge.integral_le_of_period` (`Breakdown/CellReduction/AdjointPinCharge.lean:152`).

**Theorem: Almost every scalar slice is finite.** A finite nonnegative period integral gives a finite spatial nonnegative integral for almost every time in the unit interval. Source: `Breakdown.AdjointDefect.Internal.PinCharge.ae_slice_finite` (`Breakdown/CellReduction/AdjointPinCharge.lean:160`).

**Theorem: Integrate the matrix pairing.** The two matrix-square bounds make their matrix inner product integrable over the period product measure. Source: `Breakdown.AdjointDefect.Internal.PinCharge.matrix_pairing_integrable` (`Breakdown/CellReduction/AdjointPinCharge.lean:167`).

**Theorem: Integrate the vector pairing.** The two vector-square bounds make their inner product integrable over the period product measure. Source: `Breakdown.AdjointDefect.Internal.PinCharge.vector_pairing_integrable` (`Breakdown/CellReduction/AdjointPinCharge.lean:178`).

**Theorem: Regularity of a fixed time slice.** Each fixed time slice inherits continuous differentiability from the joint field. Source: `Breakdown.AdjointDefect.Internal.PinCharge.slice_contDiff` (`Breakdown/CellReduction/AdjointPinCharge.lean:188`).

**Theorem: Read the derivative of a spatial slice.** The spatial derivative of the slice is the joint derivative composed with the spatial inclusion. Source: `Breakdown.AdjointDefect.Internal.PinCharge.slice_fderiv_eq` (`Breakdown/CellReduction/AdjointPinCharge.lean:192`).

**Theorem: The spatial derivative is continuous.** The spatial derivative of the joint continuously differentiable field is continuous in time and space. Source: `Breakdown.AdjointDefect.Internal.PinCharge.slice_fderiv_continuous` (`Breakdown/CellReduction/AdjointPinCharge.lean:200`).

**Theorem: The derivative vanishes off the support.** Outside the stated support region, the field is locally zero and its derivative vanishes. Source: `Breakdown.AdjointDefect.Internal.PinCharge.fderiv_zero_outside` (`Breakdown/CellReduction/AdjointPinCharge.lean:209`).

**Theorem: Vanishing outside a box gives support.** Vanishing outside the stated bounded region gives compact support. Source: `Breakdown.AdjointDefect.Internal.PinCharge.compact_of_zero` (`Breakdown/CellReduction/AdjointPinCharge.lean:217`).

**Theorem: Integrate compact matrix squares.** A continuous periodic matrix field with common compact spatial support has integrable column-square sum over the period product measure. Source: `Breakdown.AdjointDefect.Internal.PinCharge.compact_entrySq_integrable` (`Breakdown/CellReduction/AdjointPinCharge.lean:222`).

**Theorem: Weak gradients respect subtraction.** The weak-gradient identity is preserved by subtraction. Source: `Breakdown.AdjointDefect.Internal.PinCharge.weak_sub` (`Breakdown/CellReduction/AdjointPinCharge.lean:243`).

**Theorem: Matrix pairing preserves subtraction.** The matrix pairing distributes over subtraction in its second argument. Source: `Breakdown.AdjointDefect.Internal.PinCharge.pairMatrix_sub` (`Breakdown/CellReduction/AdjointPinCharge.lean:249`).

**Theorem: Pair a finite matrix sum.** The matrix pairing of a finite weighted sum equals the weighted sum of the pairings. Source: `Breakdown.AdjointDefect.Internal.PinCharge.pairMatrix_sum_smul` (`Breakdown/CellReduction/AdjointPinCharge.lean:253`).

**Theorem: Adjoints commute with weighted sums.** Taking the adjoint commutes with a finite real scalar-weighted sum. Source: `Breakdown.AdjointDefect.Internal.PinCharge.adjoint_sum_smul` (`Breakdown/CellReduction/AdjointPinCharge.lean:260`).

**Theorem: Take a square-root coefficient bound.** The squared coefficient estimate implies that the square root of b is at most t times the coefficient norm. Source: `Breakdown.AdjointDefect.Internal.PinCharge.sqrt_bound` (`Breakdown/CellReduction/AdjointPinCharge.lean:264`).

**Theorem: Combine the two pin-charge errors.** The absolute pin charge is at most epsilon plus the coefficient norm times rho divided by the square root of the weight, all multiplied by the square root of energy. Source: `Breakdown.AdjointDefect.Internal.PinCharge.final_bound` (`Breakdown/CellReduction/AdjointPinCharge.lean:270`).

**Theorem: The transpose pairing vanishes a.e..** For almost every time, the weak gradient has zero integrated matrix pairing with the adjoint of the coefficient-weighted generator derivative. Source: `Breakdown.AdjointDefect.Internal.PinCharge.slice_transpose` (`Breakdown/CellReduction/AdjointPinCharge.lean:291`).

**Theorem: Move derivatives in the pin pairing.** For almost every time, pairing the weak gradient with the potential-minus-generator derivative equals minus the pairing of the weak Laplacian with that potential-minus-generator field. Source: `Breakdown.AdjointDefect.Internal.PinCharge.slice_by_parts` (`Breakdown/CellReduction/AdjointPinCharge.lean:327`).

### Breakdown.CellReduction.AdjointPinChargeParts

Coordinatewise weak differentiation proves the vanishing transpose pairing and the trace integration-by-parts identity used for pins.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: Coordinates as inner products.** A vector coordinate equals its inner product with the corresponding coordinate unit vector. Source: `Breakdown.AdjointDefect.Internal.PinCharge.coord_inner` (`Breakdown/CellReduction/AdjointPinChargeParts.lean:17`).

**Theorem: Adjoint entries are transposed.** The matrix adjoint exchanges the two coordinate indices. Source: `Breakdown.AdjointDefect.Internal.PinCharge.adjoint_entry` (`Breakdown/CellReduction/AdjointPinChargeParts.lean:20`).

**Theorem: Expand the Euclidean inner product.** The Euclidean inner product equals the sum of the three coordinate products. Source: `Breakdown.AdjointDefect.Internal.PinCharge.inner_coords` (`Breakdown/CellReduction/AdjointPinChargeParts.lean:24`).

**Theorem: Expand the transposed matrix pairing.** The inner product involving one adjoint matrix equals the double coordinate sum of entries with their indices exchanged. Source: `Breakdown.AdjointDefect.Internal.PinCharge.pairMatrix_adjoint_right` (`Breakdown/CellReduction/AdjointPinChargeParts.lean:28`).

**Theorem: Expand the transposed matrix pairing.** The inner product involving one adjoint matrix equals the double coordinate sum of entries with their indices exchanged. Source: `Breakdown.AdjointDefect.Internal.PinCharge.pairMatrix_adjoint_left` (`Breakdown/CellReduction/AdjointPinChargeParts.lean:35`).

**Theorem: Test a weak derivative coordinate.** Pairing one weak derivative coordinate with a compact scalar test equals minus the pairing of the original coordinate with the test derivative. Source: `Breakdown.AdjointDefect.Internal.PinCharge.weak_coord` (`Breakdown/CellReduction/AdjointPinChargeParts.lean:41`).

**Theorem: Differentiate a derivative entry.** Differentiating one coordinate of a first derivative gives the corresponding coordinate of the second derivative. Source: `Breakdown.AdjointDefect.Internal.PinCharge.fderiv_entry` (`Breakdown/CellReduction/AdjointPinChargeParts.lean:61`).

**Theorem: A smooth derivative entry stays smooth.** Each coordinate entry of the derivative of a smooth field is smooth. Source: `Breakdown.AdjointDefect.Internal.PinCharge.entry_contDiff` (`Breakdown/CellReduction/AdjointPinChargeParts.lean:73`).

**Theorem: Derivative entries have compact support.** Each derivative entry of the compactly supported smooth field has compact support. Source: `Breakdown.AdjointDefect.Internal.PinCharge.entry_hasCompactSupport` (`Breakdown/CellReduction/AdjointPinChargeParts.lean:78`).

**Theorem: Differentiate the divergence trace.** The derivative of the divergence trace is the sum of the corresponding second-derivative coordinates. Source: `Breakdown.AdjointDefect.Internal.PinCharge.fderiv_trace` (`Breakdown/CellReduction/AdjointPinChargeParts.lean:82`).

**Theorem: Trade transposed derivatives for trace.** The integrated transposed derivative column pairing equals the integrated divergence trace paired with the matching diagonal weak derivative. Source: `Breakdown.AdjointDefect.Internal.PinCharge.transpose_column_smooth` (`Breakdown/CellReduction/AdjointPinChargeParts.lean:91`).

**Theorem: Solenoidality kills the transpose term.** The integrated pairing of the weak gradient with the transpose derivative vanishes under the divergence-free hypotheses. Source: `Breakdown.AdjointDefect.Internal.PinCharge.transpose_pairing_smooth` (`Breakdown/CellReduction/AdjointPinChargeParts.lean:119`).

**Theorem: Approximate a field and its gradient.** There are compactly supported smooth fields converging to the field in L2, with every derivative column converging to the corresponding weak-gradient column in L2. Source: `Breakdown.AdjointDefect.Internal.PinCharge.mollified` (`Breakdown/CellReduction/AdjointPinChargeParts.lean:143`).

**Theorem: Move the gradient onto the Laplacian.** The integrated matrix pairing of G with the derivative of f equals minus the integrated pairing of the weak Laplacian with f. Source: `Breakdown.AdjointDefect.Internal.PinCharge.trace_by_parts` (`Breakdown/CellReduction/AdjointPinChargeParts.lean:180`).

**Theorem: Each adjoint column belongs to L2.** Every column of the adjoint weak-gradient matrix is square integrable. Source: `Breakdown.AdjointDefect.Internal.PinCharge.adjoint_column_memLp` (`Breakdown/CellReduction/AdjointPinChargeParts.lean:203`).

**Theorem: Expand the adjoint-column pairing.** The sum of inner products of adjoint columns with matrix columns equals the double sum of the corresponding transposed coordinate products. Source: `Breakdown.AdjointDefect.Internal.PinCharge.pair_adjoint_column` (`Breakdown/CellReduction/AdjointPinChargeParts.lean:211`).

**Theorem: Solenoidality kills the transpose term.** The integrated pairing of the weak gradient with the transpose derivative vanishes under the divergence-free hypotheses. Source: `Breakdown.AdjointDefect.Internal.PinCharge.transpose_pairing_zero` (`Breakdown/CellReduction/AdjointPinChargeParts.lean:219`).

### Breakdown.CellReduction.AdjointPotentialBound

Periodwise Cauchy–Schwarz and the weighted two-term inequality assemble the potential contribution to the adjoint defect.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: Almost every period slice is finite.** A finite nonnegative period integral implies a finite spatial nonnegative integral for almost every time in the unit interval. Source: `Breakdown.AdjointDefect.Internal.PotentialBound.ae_slice_finite` (`Breakdown/CellReduction/AdjointPotentialBound.lean:16`).

**Theorem: Cauchy–Schwarz for matrix pairing.** The absolute matrix pairing is bounded by the product of the square roots of the two column-square sums. Source: `Breakdown.AdjointDefect.Internal.PotentialBound.abs_matrixInner_le` (`Breakdown/CellReduction/AdjointPotentialBound.lean:23`).

**Theorem: Recover a finite integral from its root.** A finite nonnegative period integral is bounded by the nonnegative embedding of the square of its real square root. Source: `Breakdown.AdjointDefect.Internal.PotentialBound.period_lintegral_le_sq` (`Breakdown/CellReduction/AdjointPotentialBound.lean:30`).

**Theorem: Period matrix Cauchy inequality.** The absolute integrated matrix pairing is bounded by the product of the two assumed period square-norm bounds. Source: `Breakdown.AdjointDefect.Internal.PotentialBound.period_matrix_bound` (`Breakdown/CellReduction/AdjointPotentialBound.lean:34`).

**Theorem: Period vector Cauchy inequality.** The absolute period vector pairing is bounded by the product of the two assumed square-norm bounds. Source: `Breakdown.AdjointDefect.Internal.PotentialBound.period_inner_bound` (`Breakdown/CellReduction/AdjointPotentialBound.lean:64`).

**Theorem: Combine gradient and Laplacian bounds.** For positive w, ax+by is at most the square root of a squared plus b squared divided by w times the square root of x squared plus w times y squared. Source: `Breakdown.AdjointDefect.Internal.PotentialBound.pairing_two_term_le` (`Breakdown/CellReduction/AdjointPotentialBound.lean:88`).

**Theorem: The Laplacian trace is continuous.** Taking the trace of the second derivative is a continuous operation. Source: `Breakdown.AdjointDefect.Internal.PotentialBound.continuous_traceSecond` (`Breakdown/CellReduction/AdjointPotentialBound.lean:104`).

**Theorem: A finite period norm is integrable.** Measurability and finiteness of the nonnegative period integral imply integrability for the period product measure. Source: `Breakdown.AdjointDefect.Internal.PotentialBound.integrable_period_of_lintegral` (`Breakdown/CellReduction/AdjointPotentialBound.lean:108`).

**Theorem: Add nonnegative period integrands.** The nonnegative period integral distributes over addition with the stated nonnegative scalar weight. Source: `Breakdown.AdjointDefect.Internal.PotentialBound.period_add_smul` (`Breakdown/CellReduction/AdjointPotentialBound.lean:116`).

### Breakdown.CellReduction.AdjointPotentialBoundPairing

Spatial cutoffs and mollification extend integration by parts from compact test fields to the decaying fields used by the potentials.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: Expand the Euclidean inner product.** The Euclidean inner product equals the sum of the three coordinate products. Source: `Breakdown.AdjointDefect.Internal.PotentialBound.inner_eq_sum` (`Breakdown/CellReduction/AdjointPotentialBoundPairing.lean:22`).

**Theorem: Integrate a product majorant.** The pointwise product bound and the two square-integral bounds imply that the absolute integral is at most AB. Source: `Breakdown.AdjointDefect.Internal.PotentialBound.abs_integral_le_of_le_mul` (`Breakdown/CellReduction/AdjointPotentialBoundPairing.lean:25`).

**Theorem: The inner cutoff derivative vanishes.** Inside the region where the radial cutoff is one, its derivative is zero. Source: `Breakdown.AdjointDefect.Internal.PotentialBound.cut_fderiv_zero` (`Breakdown/CellReduction/AdjointPotentialBoundPairing.lean:63`).

**Theorem: The outer cutoff derivative vanishes.** Outside the support region of the radial cutoff, its derivative is zero. Source: `Breakdown.AdjointDefect.Internal.PotentialBound.cut_fderiv_zero_far` (`Breakdown/CellReduction/AdjointPotentialBoundPairing.lean:71`).

**Theorem: A uniform scaled cutoff derivative.** Radius times the norm of the radial-cutoff derivative has one nonnegative bound independent of cutoff scale. Source: `Breakdown.AdjointDefect.Internal.PotentialBound.cut_weight_bound` (`Breakdown/CellReduction/AdjointPotentialBoundPairing.lean:79`).

**Theorem: Expanding cutoffs equal one locally.** At each fixed spatial point, the radial cutoff at radius n+1 eventually equals one. Source: `Breakdown.AdjointDefect.Internal.PotentialBound.cut_eventually_one` (`Breakdown/CellReduction/AdjointPotentialBoundPairing.lean:94`).

**Theorem: Expanding cutoff derivatives vanish.** At each fixed spatial point, the derivative of the radial cutoff at radius n+1 is eventually zero. Source: `Breakdown.AdjointDefect.Internal.PotentialBound.cut_fderiv_eventually_zero` (`Breakdown/CellReduction/AdjointPotentialBoundPairing.lean:101`).

**Theorem: Radial cutoff derivative is continuous.** The derivative of the smooth radial cutoff is continuous. Source: `Breakdown.AdjointDefect.Internal.PotentialBound.cut_continuous_fderiv` (`Breakdown/CellReduction/AdjointPotentialBoundPairing.lean:109`).

**Theorem: Integrability after compact testing.** Multiplying a locally integrable vector component by the compact test function gives an integrable scalar function. Source: `Breakdown.AdjointDefect.Internal.PotentialBound.integrable_mul_apply_compact` (`Breakdown/CellReduction/AdjointPotentialBoundPairing.lean:112`).

**Theorem: A compact pairing is integrable.** The compact-support and local-integrability hypotheses make the vector inner product spatially integrable. Source: `Breakdown.AdjointDefect.Internal.PotentialBound.integrable_inner_compact` (`Breakdown/CellReduction/AdjointPotentialBoundPairing.lean:120`).

**Theorem: Differentiate a vector coordinate.** The derivative of one vector coordinate is the coordinate projection composed with the vector derivative. Source: `Breakdown.AdjointDefect.Internal.PotentialBound.hasFDerivAt_component` (`Breakdown/CellReduction/AdjointPotentialBoundPairing.lean:129`).

**Theorem: The cutoff product rule.** The derivative of a cutoff times one field coordinate is the cutoff times the coordinate derivative plus the coordinate times the cutoff derivative. Source: `Breakdown.AdjointDefect.Internal.PotentialBound.fderiv_cut_mul` (`Breakdown/CellReduction/AdjointPotentialBoundPairing.lean:133`).

**Theorem: Integrate the cutoff product by parts.** The cutoff-weighted divergence pairing equals minus the sum of the cutoff-weighted derivative pairing and the derivative-of-cutoff error. Source: `Breakdown.AdjointDefect.Internal.PotentialBound.summed_rel` (`Breakdown/CellReduction/AdjointPotentialBoundPairing.lean:145`).

**Theorem: Remove a radial cutoff by convergence.** The limiting cutoff identities give the uncut integral of f equal to minus the integral of F. Source: `Breakdown.AdjointDefect.Internal.PotentialBound.cut_limit` (`Breakdown/CellReduction/AdjointPotentialBoundPairing.lean:214`).

**Definition: Weak divergence by columns.** This proposition requires that the vector field is the distributional divergence of the listed matrix columns. Source: `Breakdown.AdjointDefect.Internal.PotentialBound.WeakColumnDivergence` (`Breakdown/CellReduction/AdjointPotentialBoundPairing.lean:250`).

**Theorem: The origin has measure zero.** Almost every spatial point is different from the origin. Source: `Breakdown.AdjointDefect.Internal.PotentialBound.ae_ne_zero` (`Breakdown/CellReduction/AdjointPotentialBoundPairing.lean:254`).

**Theorem: First-order integration by parts.** The integrated pairing of w with the divergence d equals minus the sum of pairings of the derivative columns of w with the corresponding flux columns. Source: `Breakdown.AdjointDefect.Internal.PotentialBound.cut_pairing` (`Breakdown/CellReduction/AdjointPotentialBoundPairing.lean:258`).

**Theorem: First-order integration by parts.** The integrated pairing of w with the divergence d equals minus the sum of pairings of the derivative columns of w with the corresponding flux columns. Source: `Breakdown.AdjointDefect.Internal.PotentialBound.smooth_pairing` (`Breakdown/CellReduction/AdjointPotentialBoundPairing.lean:300`).

**Theorem: First-order integration by parts.** The integrated pairing of w with the divergence d equals minus the sum of pairings of the derivative columns of w with the corresponding flux columns. Source: `Breakdown.AdjointDefect.Internal.PotentialBound.first_order_pairing` (`Breakdown/CellReduction/AdjointPotentialBoundPairing.lean:314`).

**Definition: Mollification of a vector field.** The mollified field is convolution with the normalized bump kernel. Source: `Breakdown.AdjointDefect.Internal.PotentialBound.mollified` (`Breakdown/CellReduction/AdjointPotentialBoundPairing.lean:327`).

**Theorem: Mollification produces a smooth field.** Convolving the field with the stated compact smooth mollifier gives an infinitely differentiable field. Source: `Breakdown.AdjointDefect.Internal.PotentialBound.mollified_contDiff` (`Breakdown/CellReduction/AdjointPotentialBoundPairing.lean:331`).

**Theorem: Pass to the reusable weak-gradient class.** The stated weak-gradient relation implies the reusable weak-gradient formulation used by the approximation machinery. Source: `Breakdown.AdjointDefect.Internal.PotentialBound.weakOf_of` (`Breakdown/CellReduction/AdjointPotentialBoundPairing.lean:336`).

**Theorem: A smooth field has its usual gradient.** A continuously differentiable field has its classical derivative as weak gradient. Source: `Breakdown.AdjointDefect.Internal.PotentialBound.weak_smooth` (`Breakdown/CellReduction/AdjointPotentialBoundPairing.lean:340`).

**Theorem: Mollify the weak gradient.** Each derivative column of the mollified field is the mollification of the matching weak-gradient column. Source: `Breakdown.AdjointDefect.Internal.PotentialBound.mollified_fderiv` (`Breakdown/CellReduction/AdjointPotentialBoundPairing.lean:344`).

**Theorem: Local integrability of gradient columns.** Each coordinate column of the weak gradient is locally integrable. Source: `Breakdown.AdjointDefect.Internal.PotentialBound.column_locallyIntegrable` (`Breakdown/CellReduction/AdjointPotentialBoundPairing.lean:349`).

**Theorem: Mollification preserves L6.** The mollified field has an integrable sixth power of its norm. Source: `Breakdown.AdjointDefect.Internal.PotentialBound.mollified_sixth` (`Breakdown/CellReduction/AdjointPotentialBoundPairing.lean:354`).

**Theorem: Bound the sixth power of a difference.** The sixth power of a difference norm is at most sixty-four times the sum of the individual sixth powers. Source: `Breakdown.AdjointDefect.Internal.PotentialBound.sixth_sub_le` (`Breakdown/CellReduction/AdjointPotentialBoundPairing.lean:363`).

**Theorem: Weak gradients respect subtraction.** The weak-gradient identity is preserved by subtraction. Source: `Breakdown.AdjointDefect.Internal.PotentialBound.weak_sub` (`Breakdown/CellReduction/AdjointPotentialBoundPairing.lean:376`).

**Theorem: A finite nonnegative norm is integrable.** The measurability and finite nonnegative integral hypotheses imply integrability of the real function. Source: `Breakdown.AdjointDefect.Internal.PotentialBound.integrable_of_lintegral_lt` (`Breakdown/CellReduction/AdjointPotentialBoundPairing.lean:401`).

**Theorem: Insert reciprocal radial factors.** Away from the origin, the absolute vector pairing is at most the first norm divided by radius times radius times the second norm. Source: `Breakdown.AdjointDefect.Internal.PotentialBound.inner_le_weighted` (`Breakdown/CellReduction/AdjointPotentialBoundPairing.lean:405`).

**Theorem: Weighted square norms give a pairing.** The inverse-radius norm of f and radius-weighted norm of d make their vector pairing integrable. Source: `Breakdown.AdjointDefect.Internal.PotentialBound.integrable_inner_weighted` (`Breakdown/CellReduction/AdjointPotentialBoundPairing.lean:411`).

**Theorem: Weighted Cauchy bound for a pairing.** The absolute integral of the pairing is at most the inverse-radius norm bound A times the square root of the radius-weighted square integral of d. Source: `Breakdown.AdjointDefect.Internal.PotentialBound.abs_integral_inner_weighted_le` (`Breakdown/CellReduction/AdjointPotentialBoundPairing.lean:428`).

**Theorem: Sum integrable column pairings.** The column-square assumptions make the finite sum of column inner products integrable. Source: `Breakdown.AdjointDefect.Internal.PotentialBound.integrable_cols` (`Breakdown/CellReduction/AdjointPotentialBoundPairing.lean:445`).

**Theorem: Cauchy inequality for column pairings.** The absolute integral of the sum of column pairings is at most the product of the square roots of the two integrated column-square sums. Source: `Breakdown.AdjointDefect.Internal.PotentialBound.abs_integral_cols_le` (`Breakdown/CellReduction/AdjointPotentialBoundPairing.lean:456`).

### Breakdown.CellReduction.AdjointPotentialBoundSlice

On each admissible time slice, pressure pairs to zero and potential derivatives transfer across the pairing by integration by parts.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Definition: Weak field on one time slice.** This proposition requires that the field is in L6 and its measurable weak gradient has finite square integral. Source: `Breakdown.AdjointDefect.Internal.PotentialBound.SliceField` (`Breakdown/CellReduction/AdjointPotentialBoundSlice.lean:16`).

**Theorem: Sufficient decay gives integrability.** The prescribed decay bound and measurability assumptions make the scalar function spatially integrable. Source: `Breakdown.AdjointDefect.Internal.PotentialBound.integrable_of_decay` (`Breakdown/CellReduction/AdjointPotentialBoundSlice.lean:23`).

**Theorem: Square a radial decay estimate.** Squaring the decay bound with coefficient B doubles its exponent and squares its coefficient. Source: `Breakdown.AdjointDefect.Internal.PotentialBound.sq_le_of_decay` (`Breakdown/CellReduction/AdjointPotentialBoundSlice.lean:27`).

**Theorem: Decay gives square integrability.** The prescribed decay exponent makes the square of the scalar field spatially integrable. Source: `Breakdown.AdjointDefect.Internal.PotentialBound.sq_integrable_of_decay` (`Breakdown/CellReduction/AdjointPotentialBoundSlice.lean:38`).

**Theorem: Each column is bounded by the operator.** The norm of a coordinate column is at most the matrix operator norm. Source: `Breakdown.AdjointDefect.Internal.PotentialBound.column_norm_le` (`Breakdown/CellReduction/AdjointPotentialBoundSlice.lean:44`).

**Theorem: Integrate the weighted residual square.** The decay assumptions make radius squared times the residual norm squared spatially integrable. Source: `Breakdown.AdjointDefect.Internal.PotentialBound.weighted_integrable_of_decay` (`Breakdown/CellReduction/AdjointPotentialBoundSlice.lean:48`).

**Theorem: A solenoidal field kills pressure.** The pairing of the weak divergence-free field with the pressure gradient is integrable and has zero integral. Source: `Breakdown.AdjointDefect.Internal.PotentialBound.pair_pressure` (`Breakdown/CellReduction/AdjointPotentialBoundSlice.lean:70`).

**Theorem: Read a coordinate of a finite sum.** Taking a vector coordinate commutes with the finite sum. Source: `Breakdown.AdjointDefect.Internal.PotentialBound.column_sum_apply` (`Breakdown/CellReduction/AdjointPotentialBoundSlice.lean:103`).

**Theorem: Integrate a vector coordinate.** The integral of a vector coordinate equals that coordinate of the vector integral. Source: `Breakdown.AdjointDefect.Internal.PotentialBound.integral_apply_comm` (`Breakdown/CellReduction/AdjointPotentialBoundSlice.lean:106`).

**Theorem: Move the potential Laplacian once.** Pairing the field with the potential Laplacian gives an integrable function whose integral is minus the gradient matrix pairing. Source: `Breakdown.AdjointDefect.Internal.PotentialBound.pair_potential` (`Breakdown/CellReduction/AdjointPotentialBoundSlice.lean:111`).

**Theorem: Integrate inverse-radius column products.** The inverse-radius field norm times the sum of the flux-column norms is integrable under the stated weighted bounds. Source: `Breakdown.AdjointDefect.Internal.PotentialBound.integrable_weighted_cols` (`Breakdown/CellReduction/AdjointPotentialBoundSlice.lean:175`).

**Theorem: Move the field Laplacian once.** Pairing the weak Laplacian with the potential gives an integrable function whose integral is minus the gradient matrix pairing. Source: `Breakdown.AdjointDefect.Internal.PotentialBound.pair_second` (`Breakdown/CellReduction/AdjointPotentialBoundSlice.lean:198`).

**Theorem: Rewrite decay as a negative power.** Division by the positive radial power equals multiplication by the corresponding negative real power. Source: `Breakdown.AdjointDefect.Internal.PotentialBound.div_pow_eq_rpow` (`Breakdown/CellReduction/AdjointPotentialBoundSlice.lean:314`).

**Theorem: Rewrite decay as a negative power.** Division by the positive radial power equals multiplication by the corresponding negative real power. Source: `Breakdown.AdjointDefect.Internal.PotentialBound.div_rpow_eq` (`Breakdown/CellReduction/AdjointPotentialBoundSlice.lean:318`).

**Theorem: Higher exponents give stronger decay.** For nonnegative coefficient and radius, decreasing the decay exponent increases the radial upper bound. Source: `Breakdown.AdjointDefect.Internal.PotentialBound.decay_mono` (`Breakdown/CellReduction/AdjointPotentialBoundSlice.lean:322`).

**Theorem: Radius costs one power of decay.** Multiplication by radius reduces the available decay exponent by at most one. Source: `Breakdown.AdjointDefect.Internal.PotentialBound.mul_decay_le` (`Breakdown/CellReduction/AdjointPotentialBoundSlice.lean:326`).

**Theorem: Weighted pressure decays quadratically.** The radius-weighted pressure quantity is bounded by four times C divided by the square of one plus radius. Source: `Breakdown.AdjointDefect.Internal.PotentialBound.pressure_weight_le` (`Breakdown/CellReduction/AdjointPotentialBoundSlice.lean:335`).

**Theorem: Finite inverse-square field energy.** The field has a finite spatial integral of its norm squared divided by radius squared. Source: `Breakdown.AdjointDefect.Internal.PotentialBound.inverse_square_slice` (`Breakdown/CellReduction/AdjointPotentialBoundSlice.lean:349`).

**Theorem: Regularity of a fixed time slice.** Each fixed time slice inherits continuous differentiability from the joint field. Source: `Breakdown.AdjointDefect.Internal.PotentialBound.slice_contDiff` (`Breakdown/CellReduction/AdjointPotentialBoundSlice.lean:354`).

### Breakdown.CellReduction.AdjointQuadTerm

The quadratic adjoint term is bounded using the weighted energy and either a cubic or square-integrable size estimate.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: The Laplacian trace is continuous.** Taking the trace of the second derivative is a continuous operation. Source: `Breakdown.CertReduction.AdjointQuadInternal.traceOfSecond_continuous` (`Breakdown/CellReduction/AdjointQuadTerm.lean:14`).

**Theorem: Matrix square norm is nonnegative.** The sum of the squared matrix-column norms is nonnegative. Source: `Breakdown.CertReduction.AdjointQuadInternal.columnSquares_nonneg` (`Breakdown/CellReduction/AdjointQuadTerm.lean:19`).

**Theorem: The adjoint coefficient is nonnegative.** The quadratic adjoint coefficient is nonnegative under the positive-weight assumptions. Source: `Breakdown.CertReduction.AdjointQuadInternal.coeff_nonneg` (`Breakdown/CellReduction/AdjointQuadTerm.lean:22`).

**Theorem: Cauchy inequality for lower integrals.** The square of the nonnegative integral of a product is bounded by the product of the two square integrals. Source: `Breakdown.CertReduction.AdjointQuadInternal.pairing_sq_le` (`Breakdown/CellReduction/AdjointQuadTerm.lean:32`).

**Theorem: Compare real and nonnegative integrals.** The nonnegative embedding of the real integral is bounded by the lower integral of the nonnegative embeddings. Source: `Breakdown.CertReduction.AdjointQuadInternal.ofReal_integral_le` (`Breakdown/CellReduction/AdjointQuadTerm.lean:46`).

**Theorem: Embed the real slice energy.** The nonnegative embedding of the sum of the Laplacian and weighted gradient integrals is bounded by the lower integral of their sum. Source: `Breakdown.CertReduction.AdjointQuadInternal.sliceEnergy_le` (`Breakdown/CellReduction/AdjointQuadTerm.lean:53`).

**Theorem: The weighted period energy is finite.** The stated field hypotheses give a finite period integral of Laplacian norm squared plus the constant-weighted gradient column-square sum. Source: `Breakdown.CertReduction.AdjointQuadInternal.energy_lt_top` (`Breakdown/CellReduction/AdjointQuadTerm.lean:69`).

**Theorem: Gradient squares lie below energy.** The weighted gradient-square integral is bounded by the total gradient-plus-Laplacian energy. Source: `Breakdown.CertReduction.AdjointQuadInternal.columnSquares_le_energy` (`Breakdown/CellReduction/AdjointQuadTerm.lean:95`).

**Theorem: Column squares dominate operator norm.** The integrated squared operator norm of the gradient is at most its integrated column-square sum. Source: `Breakdown.CertReduction.AdjointQuadInternal.opNorm_sq_le_lintegral` (`Breakdown/CellReduction/AdjointQuadTerm.lean:104`).

**Theorem: The two-thirds power of a cube.** For a nonnegative real number, taking the two-thirds power of its cube gives its square in the nonnegative extended reals. Source: `Breakdown.CertReduction.AdjointQuadInternal.cube_rpow_twoThirds` (`Breakdown/CellReduction/AdjointQuadTerm.lean:108`).

**Theorem: Cancel the noncubic weight factor.** For positive w, the square of az divided by the square root of w, multiplied by w, equals a squared times z squared. Source: `Breakdown.CertReduction.AdjointQuadInternal.squareCoeff_noncubic` (`Breakdown/CellReduction/AdjointQuadTerm.lean:115`).

**Theorem: Cancel the cubic weight factor.** For positive weight, squaring 2z divided by the square root of three and by the weight, then multiplying by the weight squared, gives four thirds times z squared. Source: `Breakdown.CertReduction.AdjointQuadInternal.squareCoeff_cubic` (`Breakdown/CellReduction/AdjointQuadTerm.lean:122`).

### Breakdown.CellReduction.AdjointQuadraticBridge

The coefficient used to transfer the quadratic adjoint estimate is nonnegative for a positive energy weight.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: The adjoint coefficient is nonnegative.** The quadratic adjoint coefficient is nonnegative for the prescribed positive weight. Source: `Breakdown.CertReduction.adjointQuadCoeff_nonneg` (`Breakdown/CellReduction/AdjointQuadraticBridge.lean:12`).

### Breakdown.CellReduction.AdjointRemainderAzimuthal

Azimuthal groups and temporal orthogonality combine the modewise Hardy estimates into the remainder dual bound.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Definition: Temporal Fourier phase.** The temporal coefficient is the complex exponential at the key's integer temporal frequency. Source: `Breakdown.AdjointDefect.AzimuthalParts.Internal.timeCoef` (`Breakdown/CellReduction/AdjointRemainderAzimuthal.lean:27`).

**Theorem: The component weight is positive.** Every complex-component weight is strictly positive. Source: `Breakdown.AdjointDefect.AzimuthalParts.Internal.componentWeight_pos` (`Breakdown/CellReduction/AdjointRemainderAzimuthal.lean:30`).

**Theorem: Frequencies stay distinct in a group.** Injectivity of the component-frequency-order labels makes temporal frequencies distinct inside each fixed component-and-order group. Source: `Breakdown.AdjointDefect.AzimuthalParts.Internal.groupSet_injOn` (`Breakdown/CellReduction/AdjointRemainderAzimuthal.lean:34`).

**Theorem: Flatten the weighted mode sum.** The sum grouped by component and angular order equals the corresponding single sum over the original indices. Source: `Breakdown.AdjointDefect.AzimuthalParts.Internal.regroup` (`Breakdown/CellReduction/AdjointRemainderAzimuthal.lean:44`).

**Theorem: Grouped weighted energy is measurable.** The radius-weighted square norm of a frequency group is jointly measurable almost everywhere in time and space. Source: `Breakdown.AdjointDefect.AzimuthalParts.Internal.joint_meas_group` (`Breakdown/CellReduction/AdjointRemainderAzimuthal.lean:64`).

**Theorem: Take square roots of a product bound.** The stated square-product bound implies the corresponding product of square-root bounds. Source: `Breakdown.AdjointDefect.AzimuthalParts.Internal.sqrt_split` (`Breakdown/CellReduction/AdjointRemainderAzimuthal.lean:79`).

**Theorem: Compare the angular denominator.** The component weight divided by the squared mode weight is bounded by the same component weight divided by the square of absolute order plus one half. Source: `Breakdown.AdjointDefect.AzimuthalParts.Internal.weight_le` (`Breakdown/CellReduction/AdjointRemainderAzimuthal.lean:88`).

**Theorem: Squaring a square root recovers its base.** For a nonnegative real number, the square of its one-half real power equals the original number. Source: `Breakdown.AdjointDefect.AzimuthalParts.Internal.half_sq` (`Breakdown/CellReduction/AdjointRemainderAzimuthal.lean:93`).

**Theorem: Azimuthal remainder dual bound.** Under the stated hypotheses, the azimuthal remainder bound implies the remainder dual estimate. Source: `Breakdown.AdjointDefect.AzimuthalParts.remainderAzimuthalHolds_of` (`Breakdown/CellReduction/AdjointRemainderAzimuthal.lean:101`).

### Breakdown.CellReduction.AdjointRemainderAzimuthalAlgebra

The three complex components recover the real norm and pairing with the weights used in the azimuthal decomposition.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Definition: Real map for one complex component.** The component map realizes each selected complex component as a horizontal real vector. Source: `Breakdown.AdjointDefect.AzimuthalParts.Internal.componentMap` (`Breakdown/CellReduction/AdjointRemainderAzimuthalAlgebra.lean:19`).

**Theorem: Coordinates of a complex component.** The component map places the chosen horizontal or axial component in the first two real coordinates and makes its third coordinate zero. Source: `Breakdown.AdjointDefect.AzimuthalParts.Internal.componentMap_coords` (`Breakdown/CellReduction/AdjointRemainderAzimuthalAlgebra.lean:28`).

**Theorem: Recover the selected complex component.** Taking the horizontal complex part of the component-mapped field recovers the selected complex component of the original field. Source: `Breakdown.AdjointDefect.AzimuthalParts.Internal.horizontal_componentMap` (`Breakdown/CellReduction/AdjointRemainderAzimuthalAlgebra.lean:34`).

**Theorem: Projection and complex norms agree.** The squared norm of the real component projection equals the squared norm of its complex component. Source: `Breakdown.AdjointDefect.AzimuthalParts.Internal.componentMap_norm_sq` (`Breakdown/CellReduction/AdjointRemainderAzimuthalAlgebra.lean:41`).

**Theorem: Component energies recover the norm.** The weighted sum of the three component square norms equals the original vector square norm. Source: `Breakdown.AdjointDefect.AzimuthalParts.Internal.weighted_norm_sq` (`Breakdown/CellReduction/AdjointRemainderAzimuthalAlgebra.lean:47`).

**Theorem: Component matrices recover the energy.** The weighted component matrix-square sums add to the original matrix-square sum. Source: `Breakdown.AdjointDefect.AzimuthalParts.Internal.weighted_squareSum` (`Breakdown/CellReduction/AdjointRemainderAzimuthalAlgebra.lean:54`).

**Theorem: Recover the real pairing from modes.** The real vector inner product is the weighted sum of the real parts of the component complex pairings. Source: `Breakdown.AdjointDefect.AzimuthalParts.Internal.inner_components` (`Breakdown/CellReduction/AdjointRemainderAzimuthalAlgebra.lean:61`).

**Theorem: Linear maps preserve local integrability.** A continuous linear map sends a locally integrable function to a locally integrable function. Source: `Breakdown.AdjointDefect.AzimuthalParts.Internal.locallyIntegrable_clm` (`Breakdown/CellReduction/AdjointRemainderAzimuthalAlgebra.lean:67`).

**Theorem: Linear maps preserve weak gradients.** Applying a continuous linear map to the field composes the same map with its weak gradient. Source: `Breakdown.AdjointDefect.AzimuthalParts.Internal.weakGradient_comp` (`Breakdown/CellReduction/AdjointRemainderAzimuthalAlgebra.lean:73`).

**Theorem: Rotation shifts the cylinder angle.** Rotating the zero-angle cylindrical point gives the point at the chosen angle. Source: `Breakdown.AdjointDefect.AzimuthalParts.Internal.ringPoint_rotation` (`Breakdown/CellReduction/AdjointRemainderAzimuthalAlgebra.lean:97`).

### Breakdown.CellReduction.AdjointRemainderAzimuthalApprox

Mollification followed by spatial cutoff supplies compact smooth approximants with convergent gradient energy.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: Pass to the reusable weak-gradient class.** The stated weak-gradient relation implies the reusable weak-gradient formulation used by the approximation machinery. Source: `Breakdown.AdjointDefect.AzimuthalParts.WeakClassApprox.Internal.weakGradientOf_of_weakGradient` (`Breakdown/CellReduction/AdjointRemainderAzimuthalApprox.lean:20`).

**Theorem: Matrix square norm is nonnegative.** The sum of the squared matrix-column norms is nonnegative. Source: `Breakdown.AdjointDefect.AzimuthalParts.WeakClassApprox.Internal.entrySq_nonneg'` (`Breakdown/CellReduction/AdjointRemainderAzimuthalApprox.lean:25`).

**Theorem: The matrix square norm is continuous.** The sum of the squared matrix-column norms depends continuously on the matrix. Source: `Breakdown.AdjointDefect.AzimuthalParts.WeakClassApprox.Internal.entrySq_continuous` (`Breakdown/CellReduction/AdjointRemainderAzimuthalApprox.lean:28`).

**Theorem: Matrix squares of a sum.** The column-square sum of two matrices added together is at most twice the sum of their individual column-square sums. Source: `Breakdown.AdjointDefect.AzimuthalParts.WeakClassApprox.Internal.entrySq_add_le'` (`Breakdown/CellReduction/AdjointRemainderAzimuthalApprox.lean:32`).

**Theorem: Mollification only uses nearby values.** Inside the radius-R ball, mollifying the field gives the same value as mollifying its restriction to the radius-(R+1) ball. Source: `Breakdown.AdjointDefect.AzimuthalParts.WeakClassApprox.Internal.conv_eq_on_ball` (`Breakdown/CellReduction/AdjointRemainderAzimuthalApprox.lean:42`).

**Theorem: Smooth approximation in gradient norm.** There are smooth L6 fields with integrable gradient square, converging globally in gradient square integral and locally in field square integral. Source: `Breakdown.AdjointDefect.AzimuthalParts.WeakClassApprox.Internal.smoothStep` (`Breakdown/CellReduction/AdjointRemainderAzimuthalApprox.lean:60`).

**Theorem: Compact approximation in gradient norm.** There are compactly supported smooth fields converging globally in gradient square integral and locally in field square integral. Source: `Breakdown.AdjointDefect.AzimuthalParts.WeakClassApprox.Internal.cutStep` (`Breakdown/CellReduction/AdjointRemainderAzimuthalApprox.lean:145`).

**Theorem: Approximate a weak gradient field.** A measurable L6 field with square-integrable weak gradient admits compact smooth approximants converging in gradient energy and local L2. Source: `Breakdown.AdjointDefect.AzimuthalParts.weakClassApprox` (`Breakdown/CellReduction/AdjointRemainderAzimuthalApprox.lean:213`).

### Breakdown.CellReduction.AdjointRemainderAzimuthalGradientTotal

The total energy of the angular gradient modes is bounded by the physical matrix-square integral.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: The matrix square norm is continuous.** The sum of the squared matrix-column norms depends continuously on the matrix. Source: `Breakdown.AdjointDefect.AzimuthalParts.GradientTotalInternal.entryNormSq_continuous` (`Breakdown/CellReduction/AdjointRemainderAzimuthalGradientTotal.lean:20`).

**Theorem: Two matrix-square encodings agree.** The two definitions of the matrix column-square sum have equal values. Source: `Breakdown.AdjointDefect.AzimuthalParts.GradientTotalInternal.entryNormSq_eq` (`Breakdown/CellReduction/AdjointRemainderAzimuthalGradientTotal.lean:25`).

**Theorem: Sum of mode gradient energies.** The sum of angular gradient energies is bounded by the physical gradient square integral. Source: `Breakdown.AdjointDefect.AzimuthalParts.gradientModeTotal` (`Breakdown/CellReduction/AdjointRemainderAzimuthalGradientTotal.lean:30`).

### Breakdown.CellReduction.AdjointRemainderAzimuthalPairing

A field with one angular frequency pairs only with the corresponding angular mode.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: Opposite angular phases cancel.** Multiplying the two opposite angular phases gives one. Source: `Breakdown.AdjointDefect.AzimuthalParts.Internal.ModePairing.exp_neg_mul_exp` (`Breakdown/CellReduction/AdjointRemainderAzimuthalPairing.lean:18`).

**Theorem: The oscillatory factor has unit norm.** The stated complex oscillatory factor has norm one. Source: `Breakdown.AdjointDefect.AzimuthalParts.Internal.ModePairing.norm_exp_mode` (`Breakdown/CellReduction/AdjointRemainderAzimuthalPairing.lean:22`).

**Theorem: Conjugation reverses the phase.** Conjugating the negative angular phase produces the positive angular phase. Source: `Breakdown.AdjointDefect.AzimuthalParts.Internal.ModePairing.conj_exp_mode` (`Breakdown/CellReduction/AdjointRemainderAzimuthalPairing.lean:26`).

**Theorem: Extract a pure angular mode.** A field with angular transformation law of order k has kth angular coefficient equal to its value at zero angle. Source: `Breakdown.AdjointDefect.AzimuthalParts.Internal.ModePairing.mode_of_turn` (`Breakdown/CellReduction/AdjointRemainderAzimuthalPairing.lean:33`).

**Theorem: Pairing selects the matching mode.** The angular integral of the complex pairing with a pure mode equals two pi times the pairing of the corresponding angular Fourier coefficients. Source: `Breakdown.AdjointDefect.AzimuthalParts.Internal.ModePairing.slice_eq` (`Breakdown/CellReduction/AdjointRemainderAzimuthalPairing.lean:49`).

### Breakdown.CellReduction.AdjointRemainderAzimuthalParts

The modewise inverse-square estimate, approximation, pairing and temporal orthogonality are exposed as separate propositions.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Definition: Angular frequency plus one half.** The angular Hardy weight is the absolute angular frequency plus one half. Source: `Breakdown.AdjointDefect.AzimuthalParts.modeWeight` (`Breakdown/CellReduction/AdjointRemainderAzimuthalParts.lean:18`).

**Definition: Inverse-square energy of one mode.** The mode integral weights the angular Fourier coefficient by inverse radius squared and the cylindrical Jacobian. Source: `Breakdown.AdjointDefect.AzimuthalParts.modeInverseSquare` (`Breakdown/CellReduction/AdjointRemainderAzimuthalParts.lean:20`).

**Interface definition: Hardy estimate for a smooth mode.** This proposition requires that the squared angular weight times a smooth compact field's inverse-square mode integral is bounded by its mode gradient energy. Source: `Breakdown.AdjointDefect.AzimuthalParts.SmoothModeInverseSquareHolds` (`Breakdown/CellReduction/AdjointRemainderAzimuthalParts.lean:24`).

Supplied by `Breakdown.AdjointDefect.AzimuthalParts.smoothModeInverseSquare` (`lean/Breakdown/CellReduction/AdjointRemainderAzimuthalSmooth.lean:19`).

**Interface definition: Approximate a weak gradient field.** This proposition requires that a measurable L6 field with square-integrable weak gradient admits compact smooth approximants converging in gradient energy and local L2. Source: `Breakdown.AdjointDefect.AzimuthalParts.WeakClassApproxHolds` (`Breakdown/CellReduction/AdjointRemainderAzimuthalParts.lean:29`).

Supplied by `Breakdown.AdjointDefect.AzimuthalParts.weakClassApprox` (`lean/Breakdown/CellReduction/AdjointRemainderAzimuthalApprox.lean:213`).

**Interface definition: Sum of mode gradient energies.** This proposition requires that the sum of angular gradient energies is bounded by the physical gradient square integral. Source: `Breakdown.AdjointDefect.AzimuthalParts.GradientModeTotalHolds` (`Breakdown/CellReduction/AdjointRemainderAzimuthalParts.lean:38`).

Supplied by `Breakdown.AdjointDefect.AzimuthalParts.gradientModeTotal` (`lean/Breakdown/CellReduction/AdjointRemainderAzimuthalGradientTotal.lean:30`).

**Interface definition: Pairing with one angular mode.** This proposition requires that a single-frequency field pairs with the corresponding inverse-square mode, bounded by the weighted square norm of that field. Source: `Breakdown.AdjointDefect.AzimuthalParts.ModePairingHolds` (`Breakdown/CellReduction/AdjointRemainderAzimuthalParts.lean:42`).

Supplied by `Breakdown.AdjointDefect.AzimuthalParts.modePairing` (`lean/Breakdown/CellReduction/AdjointRemainderAzimuthalPairing.lean:75`).

**Interface definition: Temporal modes are orthogonal.** This proposition requires that distinct integer temporal frequencies bound the period square integral of their sum by the sum of their weighted spatial square integrals. Source: `Breakdown.AdjointDefect.AzimuthalParts.TimeModeSumHolds` (`Breakdown/CellReduction/AdjointRemainderAzimuthalParts.lean:48`).

Supplied by `Breakdown.AdjointDefect.AzimuthalParts.timeModeSum` (`lean/Breakdown/CellReduction/AdjointRemainderAzimuthalTime.lean:124`).

**Interface definition: Hardy estimate for weak modes.** This proposition requires that the weighted sum of inverse-square mode integrals is bounded by the square integral of the weak gradient. Source: `Breakdown.AdjointDefect.AzimuthalParts.ModeInverseSquareWeakHolds` (`Breakdown/CellReduction/AdjointRemainderAzimuthalParts.lean:55`).

Supplied by `Breakdown.AdjointDefect.AzimuthalParts.modeInverseSquareWeak_of` (`lean/Breakdown/CellReduction/AdjointRemainderAzimuthalWeak.lean:80`).

### Breakdown.CellReduction.AdjointRemainderAzimuthalSlice

Fields are grouped by complex component and angular order before the weighted spatial pairing is estimated.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Definition: Group by component and angular order.** The index set selects the keys with the specified complex component and angular order. Source: `Breakdown.AdjointDefect.AzimuthalParts.Internal.groupSet` (`Breakdown/CellReduction/AdjointRemainderAzimuthalSlice.lean:21`).

**Definition: Angular orders of one component.** The angular-order set is the image of the keys assigned to the specified component. Source: `Breakdown.AdjointDefect.AzimuthalParts.Internal.orderSet` (`Breakdown/CellReduction/AdjointRemainderAzimuthalSlice.lean:24`).

**Definition: Field in one angular group.** The grouped field sums the weighted amplitudes in one component-and-order group. Source: `Breakdown.AdjointDefect.AzimuthalParts.Internal.groupField` (`Breakdown/CellReduction/AdjointRemainderAzimuthalSlice.lean:27`).

**Theorem: Regroup by angular order.** The finite sum for one component equals the sum of its groups indexed by angular order. Source: `Breakdown.AdjointDefect.AzimuthalParts.Internal.group_split` (`Breakdown/CellReduction/AdjointRemainderAzimuthalSlice.lean:31`).

**Theorem: A group has its prescribed frequency.** Each grouped field transforms by the complex phase of its common angular order under axial rotation. Source: `Breakdown.AdjointDefect.AzimuthalParts.Internal.group_rotation` (`Breakdown/CellReduction/AdjointRemainderAzimuthalSlice.lean:37`).

**Theorem: A grouped mode is measurable.** Strong measurability of the individual amplitudes gives strong measurability of each grouped field. Source: `Breakdown.AdjointDefect.AzimuthalParts.Internal.group_meas` (`Breakdown/CellReduction/AdjointRemainderAzimuthalSlice.lean:49`).

**Theorem: Measurability of weighted mode energy.** The radius-square weighted mode norm is measurable almost everywhere. Source: `Breakdown.AdjointDefect.AzimuthalParts.Internal.weightedSq_meas` (`Breakdown/CellReduction/AdjointRemainderAzimuthalSlice.lean:55`).

**Theorem: The grouped weighted norm is finite.** Finite weighted square integrals of the amplitudes give a finite weighted square integral for their finite group. Source: `Breakdown.AdjointDefect.AzimuthalParts.Internal.group_finite` (`Breakdown/CellReduction/AdjointRemainderAzimuthalSlice.lean:59`).

**Theorem: The origin has measure zero.** Almost every spatial point is different from the origin. Source: `Breakdown.AdjointDefect.AzimuthalParts.Internal.ae_ne_zero` (`Breakdown/CellReduction/AdjointRemainderAzimuthalSlice.lean:93`).

**Theorem: The complex mode pairing is integrable.** The weighted bounds make the product of the conjugated first mode and second mode integrable. Source: `Breakdown.AdjointDefect.AzimuthalParts.Internal.pair_integrable` (`Breakdown/CellReduction/AdjointRemainderAzimuthalSlice.lean:97`).

**Theorem: Sum pointwise Cauchy bounds.** If each nonnegative summand has square at most a_i b_i, the square of their sum is at most the product of the sums of a_i and b_i. Source: `Breakdown.AdjointDefect.AzimuthalParts.Internal.sq_sum_le_of_sq_le_mul` (`Breakdown/CellReduction/AdjointRemainderAzimuthalSlice.lean:124`).

### Breakdown.CellReduction.AdjointRemainderAzimuthalSliceBound

Contractivity of the component maps and positivity of their weights feed the modewise bound on one spatial pairing.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: Complex components are continuous.** Each complex component depends continuously on the real vector. Source: `Breakdown.AdjointDefect.AzimuthalParts.Internal.continuous_complexComponent` (`Breakdown/CellReduction/AdjointRemainderAzimuthalSliceBound.lean:20`).

**Theorem: The matrix square norm is continuous.** The sum of the squared matrix-column norms depends continuously on the matrix. Source: `Breakdown.AdjointDefect.AzimuthalParts.Internal.continuous_squareSum` (`Breakdown/CellReduction/AdjointRemainderAzimuthalSliceBound.lean:24`).

**Theorem: The projection decreases square norm.** The squared norm of the stated coordinate projection is bounded by the original squared vector norm. Source: `Breakdown.AdjointDefect.AzimuthalParts.Internal.componentMap_norm_sq_le` (`Breakdown/CellReduction/AdjointRemainderAzimuthalSliceBound.lean:28`).

**Theorem: The projection decreases vector norm.** The stated coordinate projection has norm no greater than the original vector. Source: `Breakdown.AdjointDefect.AzimuthalParts.Internal.componentMap_norm_le` (`Breakdown/CellReduction/AdjointRemainderAzimuthalSliceBound.lean:33`).

**Theorem: Projection decreases column energy.** Composing a matrix with the stated coordinate projection cannot increase its column-square sum. Source: `Breakdown.AdjointDefect.AzimuthalParts.Internal.squareSum_componentMap_le` (`Breakdown/CellReduction/AdjointRemainderAzimuthalSliceBound.lean:36`).

**Theorem: Matrix square norm is nonnegative.** The sum of the squared matrix-column norms is nonnegative. Source: `Breakdown.AdjointDefect.AzimuthalParts.Internal.squareSum_nonneg_component` (`Breakdown/CellReduction/AdjointRemainderAzimuthalSliceBound.lean:43`).

**Theorem: The angular Hardy weight is positive.** The angular Hardy weight is strictly positive for every integer angular order. Source: `Breakdown.AdjointDefect.AzimuthalParts.Internal.modeWeight_pos` (`Breakdown/CellReduction/AdjointRemainderAzimuthalSliceBound.lean:46`).

**Theorem: The component weight is nonnegative.** Every complex-component weight is nonnegative. Source: `Breakdown.AdjointDefect.AzimuthalParts.Internal.componentWeight_nonneg` (`Breakdown/CellReduction/AdjointRemainderAzimuthalSliceBound.lean:50`).

**Theorem: Angular weights control the remainder.** The remainder pairing is integrable, and its squared integral is bounded by gradient energy times the sum of radius-weighted mode energies divided by squared angular Hardy weights. Source: `Breakdown.AdjointDefect.AzimuthalParts.Internal.slice_bound` (`Breakdown/CellReduction/AdjointRemainderAzimuthalSliceBound.lean:54`).

### Breakdown.CellReduction.AdjointRemainderAzimuthalSmooth

The smooth-mode coefficient is the absolute angular frequency plus one half.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: The mode weight is absolute order.** The mode weight equals the real absolute value of its integer angular order plus one half. Source: `Breakdown.AdjointDefect.AzimuthalParts.modeWeight_eq_abs` (`Breakdown/CellReduction/AdjointRemainderAzimuthalSmooth.lean:16`).

### Breakdown.CellReduction.AdjointRemainderAzimuthalTime

Integration over one period removes the cross terms between distinct integer temporal frequencies.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: Complex square norm as a product.** The squared norm of the complex number equals its product with its complex conjugate. Source: `Breakdown.AdjointDefect.AzimuthalParts.Internal.TimeSum.sq_norm_eq_mul_conj` (`Breakdown/CellReduction/AdjointRemainderAzimuthalTime.lean:18`).

**Theorem: Only zero frequency has nonzero mean.** The period integral of an integer-frequency exponential is one at frequency zero and zero at every other frequency. Source: `Breakdown.AdjointDefect.AzimuthalParts.Internal.TimeSum.integral_phase` (`Breakdown/CellReduction/AdjointRemainderAzimuthalTime.lean:21`).

**Theorem: Subtract the frequencies in a pairing.** Multiplying a temporal phase by a conjugated temporal phase replaces their frequencies by their difference. Source: `Breakdown.AdjointDefect.AzimuthalParts.Internal.TimeSum.phase_mul_conj` (`Breakdown/CellReduction/AdjointRemainderAzimuthalTime.lean:45`).

**Theorem: The temporal cross terms vanish.** The period square integral of a sum with distinct temporal frequencies is the sum of the squared coefficient norms. Source: `Breakdown.AdjointDefect.AzimuthalParts.Internal.TimeSum.modeSum_integral` (`Breakdown/CellReduction/AdjointRemainderAzimuthalTime.lean:65`).

**Theorem: Orthogonality with a nonnegative weight.** A nonnegative constant weight preserves the temporal orthogonality identity for the nonnegative period integral. Source: `Breakdown.AdjointDefect.AzimuthalParts.Internal.TimeSum.modeSum_lintegral` (`Breakdown/CellReduction/AdjointRemainderAzimuthalTime.lean:103`).

### Breakdown.CellReduction.AdjointRemainderAzimuthalWeak

Projection onto the horizontal plane lets the weak angular estimate use the horizontal complex component alone.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Definition: Horizontal coordinate projection.** The planar map retains the first two coordinates and sets the third coordinate to zero. Source: `Breakdown.AdjointDefect.AzimuthalParts.Internal.planarMap` (`Breakdown/CellReduction/AdjointRemainderAzimuthalWeak.lean:18`).

**Theorem: Expand the horizontal projection.** The planar projection is the first two coordinate multiples of their unit vectors. Source: `Breakdown.AdjointDefect.AzimuthalParts.Internal.planarMap_apply` (`Breakdown/CellReduction/AdjointRemainderAzimuthalWeak.lean:22`).

**Theorem: Keep the first horizontal coordinate.** The planar projection keeps the first coordinate. Source: `Breakdown.AdjointDefect.AzimuthalParts.Internal.planarMap_zero_coord` (`Breakdown/CellReduction/AdjointRemainderAzimuthalWeak.lean:25`).

**Theorem: Keep the second horizontal coordinate.** The planar projection keeps the second coordinate. Source: `Breakdown.AdjointDefect.AzimuthalParts.Internal.planarMap_one_coord` (`Breakdown/CellReduction/AdjointRemainderAzimuthalWeak.lean:28`).

**Theorem: Remove the vertical coordinate.** The planar projection sets the third coordinate to zero. Source: `Breakdown.AdjointDefect.AzimuthalParts.Internal.planarMap_two_coord` (`Breakdown/CellReduction/AdjointRemainderAzimuthalWeak.lean:31`).

**Theorem: The projection decreases square norm.** The squared norm of the stated coordinate projection is bounded by the original squared vector norm. Source: `Breakdown.AdjointDefect.AzimuthalParts.Internal.planarMap_norm_sq_le` (`Breakdown/CellReduction/AdjointRemainderAzimuthalWeak.lean:34`).

**Theorem: The projection decreases vector norm.** The stated coordinate projection has norm no greater than the original vector. Source: `Breakdown.AdjointDefect.AzimuthalParts.Internal.planarMap_norm_le` (`Breakdown/CellReduction/AdjointRemainderAzimuthalWeak.lean:40`).

**Theorem: Projection decreases column energy.** Composing a matrix with the stated coordinate projection cannot increase its column-square sum. Source: `Breakdown.AdjointDefect.AzimuthalParts.Internal.squareSum_planar_le` (`Breakdown/CellReduction/AdjointRemainderAzimuthalWeak.lean:43`).

**Theorem: Matrix square norm is nonnegative.** The sum of the squared matrix-column norms is nonnegative. Source: `Breakdown.AdjointDefect.AzimuthalParts.Internal.squareSum_nonneg_planar` (`Breakdown/CellReduction/AdjointRemainderAzimuthalWeak.lean:49`).

**Theorem: Horizontal projection keeps the mode.** The horizontal complex component is unchanged by the planar projection. Source: `Breakdown.AdjointDefect.AzimuthalParts.Internal.horizontal_planar` (`Breakdown/CellReduction/AdjointRemainderAzimuthalWeak.lean:52`).

**Theorem: Horizontal projection removes height.** The vertical component of the planar-projected field is zero. Source: `Breakdown.AdjointDefect.AzimuthalParts.Internal.vertical_planar` (`Breakdown/CellReduction/AdjointRemainderAzimuthalWeak.lean:57`).

**Theorem: Every mode of the zero field vanishes.** The angular Fourier coefficient of the zero field is zero. Source: `Breakdown.AdjointDefect.AzimuthalParts.Internal.angularMode_zero` (`Breakdown/CellReduction/AdjointRemainderAzimuthalWeak.lean:62`).

**Theorem: Read the planar weighted mode energy.** For the planar field, the weighted mode integral is the squared angular weight times the horizontal inverse-square mode integral. Source: `Breakdown.AdjointDefect.AzimuthalParts.Internal.weightedSide_planar` (`Breakdown/CellReduction/AdjointRemainderAzimuthalWeak.lean:65`).

### Breakdown.CellReduction.AdjointRemainderPlain

The ungrouped remainder estimate uses the inverse-square weighted pairing and elementary square-root identities.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: A radially weighted pairing bound.** Away from the origin, the extended pairing norm is at most the inverse-radius norm of the first vector times the radius-weighted norm of the second. Source: `Breakdown.AdjointDefect.Internal.plainPairing_enorm_le` (`Breakdown/CellReduction/AdjointRemainderPlain.lean:15`).

**Theorem: Take the square root of four times a.** For nonnegative a, the nonnegative square root of four times a equals twice the real square root of a. Source: `Breakdown.AdjointDefect.Internal.plainSqrt_four_mul` (`Breakdown/CellReduction/AdjointRemainderPlain.lean:25`).

**Theorem: Take the root of a nonnegative square.** The extended-real square root of the embedded square of nonnegative b equals the embedding of b. Source: `Breakdown.AdjointDefect.Internal.plainSqrt_sq` (`Breakdown/CellReduction/AdjointRemainderPlain.lean:34`).

### Breakdown.CellReduction.AdjointRepresentation

Compact time windows and test-field approximation justify testing the weak equation with the decaying adjoint field.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: Smoothness includes one derivative.** The infinite differentiability order is at least one. Source: `Breakdown.AdjointDefect.Internal.Representation.one_le_smooth` (`Breakdown/CellReduction/AdjointRepresentation.lean:19`).

**Theorem: Spatial slice of a joint derivative.** The derivative on a fixed time slice is the joint derivative restricted to the spatial direction. Source: `Breakdown.AdjointDefect.Internal.Representation.sliceSpace_hasFDerivAt` (`Breakdown/CellReduction/AdjointRepresentation.lean:21`).

**Theorem: Time derivative from the joint map.** Differentiation in time is the joint derivative applied to the unit time direction. Source: `Breakdown.AdjointDefect.Internal.Representation.slice_hasDerivAt` (`Breakdown/CellReduction/AdjointRepresentation.lean:30`).

**Theorem: Read the derivative of a spatial slice.** The spatial derivative of the slice is the joint derivative composed with the spatial inclusion. Source: `Breakdown.AdjointDefect.Internal.Representation.slice_fderiv_eq` (`Breakdown/CellReduction/AdjointRepresentation.lean:40`).

**Theorem: Read the time derivative jointly.** The time derivative equals the joint derivative applied to the unit time direction. Source: `Breakdown.AdjointDefect.Internal.Representation.timeDerivative_eq_joint` (`Breakdown/CellReduction/AdjointRepresentation.lean:46`).

**Theorem: The spatial derivative is continuous.** The spatial derivative of the joint continuously differentiable field is continuous in time and space. Source: `Breakdown.AdjointDefect.Internal.Representation.continuous_slice_fderiv` (`Breakdown/CellReduction/AdjointRepresentation.lean:51`).

**Theorem: The time derivative is continuous.** The time derivative of the jointly continuously differentiable field is continuous in time and space. Source: `Breakdown.AdjointDefect.Internal.Representation.continuous_timeDerivative` (`Breakdown/CellReduction/AdjointRepresentation.lean:61`).

**Theorem: The radial derivative is continuous.** The derivative of the field applied to the spatial position is jointly continuous. Source: `Breakdown.AdjointDefect.Internal.Representation.continuous_slice_fderiv_apply_self` (`Breakdown/CellReduction/AdjointRepresentation.lean:71`).

**Theorem: The time-cut field is differentiable.** Multiplying the adjoint field by the smooth time window preserves joint continuous differentiability. Source: `Breakdown.AdjointDefect.Internal.Representation.cut_contDiff` (`Breakdown/CellReduction/AdjointRepresentation.lean:76`).

**Theorem: The time window has its usual derivative.** The smooth time window is differentiable with derivative given by the derivative operator. Source: `Breakdown.AdjointDefect.Internal.Representation.windowBump_hasDerivAt` (`Breakdown/CellReduction/AdjointRepresentation.lean:80`).

**Theorem: The strip cutoff is differentiable.** The smooth strip cutoff has its classical derivative at every time. Source: `Breakdown.AdjointDefect.Internal.Representation.stripCutoff_hasDerivAt` (`Breakdown/CellReduction/AdjointRepresentation.lean:83`).

**Theorem: Differentiate the time-window product.** The time derivative is the window derivative times the field plus the window times the field's time derivative. Source: `Breakdown.AdjointDefect.Internal.Representation.timeDerivative_cut` (`Breakdown/CellReduction/AdjointRepresentation.lean:86`).

**Theorem: The time window scales space derivatives.** The spatial derivative of the time-windowed field is the window times the original spatial derivative. Source: `Breakdown.AdjointDefect.Internal.Representation.fderiv_cut` (`Breakdown/CellReduction/AdjointRepresentation.lean:94`).

**Definition: Time-supported test field.** The compact time test is the original test field multiplied by the time-strip cutoff. Source: `Breakdown.AdjointDefect.Internal.Representation.cutTest` (`Breakdown/CellReduction/AdjointRepresentation.lean:99`).

**Theorem: The cut approximation is solenoidal.** The cut approximation is a smooth compactly supported divergence-free spacetime test field. Source: `Breakdown.AdjointDefect.Internal.Representation.cutTest_isTest` (`Breakdown/CellReduction/AdjointRepresentation.lean:101`).

**Theorem: The cut approximation is a test vector.** The cut approximation is a smooth compactly supported spacetime test vector. Source: `Breakdown.AdjointDefect.Internal.Representation.cutTest_isTestVector` (`Breakdown/CellReduction/AdjointRepresentation.lean:115`).

**Theorem: The strip cutoff preserves the target.** Multiplying the time-windowed target by the strip cutoff leaves it unchanged. Source: `Breakdown.AdjointDefect.Internal.Representation.cut_eq_strip` (`Breakdown/CellReduction/AdjointRepresentation.lean:119`).

**Theorem: Factor the cutoff value error.** The cut-test error equals the strip cutoff times the original approximation error. Source: `Breakdown.AdjointDefect.Internal.Representation.cutTest_sub` (`Breakdown/CellReduction/AdjointRepresentation.lean:123`).

**Theorem: Differentiate the cutoff error.** The time-derivative error is the strip derivative times the value error plus the strip cutoff times the time-derivative error. Source: `Breakdown.AdjointDefect.Internal.Representation.cutTest_timeDerivative_sub` (`Breakdown/CellReduction/AdjointRepresentation.lean:128`).

**Theorem: Factor the cutoff gradient error.** The spatial derivative error after cutting equals the strip cutoff times the original spatial derivative error. Source: `Breakdown.AdjointDefect.Internal.Representation.cutTest_fderiv_sub` (`Breakdown/CellReduction/AdjointRepresentation.lean:154`).

**Theorem: The field decay constant is nonnegative.** The admissibility assumptions force the stated field decay constant to be nonnegative. Source: `Breakdown.AdjointDefect.Internal.Representation.adjoint_C_nonneg` (`Breakdown/CellReduction/AdjointRepresentation.lean:169`).

**Theorem: The flow bound is nonnegative.** The admissible flow-piece bound is nonnegative. Source: `Breakdown.AdjointDefect.Internal.Representation.flow_D_nonneg` (`Breakdown/CellReduction/AdjointRepresentation.lean:174`).

**Theorem: One plus radius is positive.** One plus the spatial norm is strictly positive. Source: `Breakdown.AdjointDefect.Internal.Representation.one_add_norm_pos` (`Breakdown/CellReduction/AdjointRepresentation.lean:177`).

**Theorem: A nonnegative decay coefficient.** A nonnegative coefficient divided by a power of one plus radius remains nonnegative. Source: `Breakdown.AdjointDefect.Internal.Representation.decay_nonneg` (`Breakdown/CellReduction/AdjointRepresentation.lean:179`).

**Theorem: One extra radial power decreases size.** Adding one to the decay exponent decreases the upper bound with nonnegative coefficient. Source: `Breakdown.AdjointDefect.Internal.Representation.decay_succ_le` (`Breakdown/CellReduction/AdjointRepresentation.lean:182`).

**Theorem: The radial derivative loses one power.** Applying an operator with one extra power of decay to the position vector yields the stated lower-order decay bound. Source: `Breakdown.AdjointDefect.Internal.Representation.apply_self_le` (`Breakdown/CellReduction/AdjointRepresentation.lean:187`).

**Theorem: The time window preserves decay.** The norm of the time-windowed adjoint satisfies the original spatial decay bound. Source: `Breakdown.AdjointDefect.Internal.Representation.cut_norm_le` (`Breakdown/CellReduction/AdjointRepresentation.lean:198`).

**Theorem: Time-cut differentiation preserves decay.** The time derivative of the time-windowed adjoint obeys the same radial decay with coefficient multiplied by M+1. Source: `Breakdown.AdjointDefect.Internal.Representation.cut_time_norm_le` (`Breakdown/CellReduction/AdjointRepresentation.lean:203`).

**Theorem: The cut gradient has stronger decay.** The time-windowed spatial derivative retains the decay exponent gamma plus one. Source: `Breakdown.AdjointDefect.Internal.Representation.cut_fderiv_norm_le` (`Breakdown/CellReduction/AdjointRepresentation.lean:221`).

**Theorem: Outside the compact time window.** The stated time bound places the time outside the closed interval from minus one to one. Source: `Breakdown.AdjointDefect.Internal.Representation.outside_window` (`Breakdown/CellReduction/AdjointRepresentation.lean:226`).

**Theorem: The cut field vanishes off its window.** Outside the time window, the specified time-cut field or derivative is zero. Source: `Breakdown.AdjointDefect.Internal.Representation.cut_zero_off` (`Breakdown/CellReduction/AdjointRepresentation.lean:230`).

**Theorem: The cut field vanishes off its window.** Outside the time window, the specified time-cut field or derivative is zero. Source: `Breakdown.AdjointDefect.Internal.Representation.cut_time_zero_off` (`Breakdown/CellReduction/AdjointRepresentation.lean:234`).

**Theorem: The cut field vanishes off its window.** Outside the time window, the specified time-cut field or derivative is zero. Source: `Breakdown.AdjointDefect.Internal.Representation.cut_fderiv_zero_off` (`Breakdown/CellReduction/AdjointRepresentation.lean:240`).

**Theorem: Measurability of operator evaluation.** Applying a measurable operator field to a measurable vector field is strongly measurable almost everywhere. Source: `Breakdown.AdjointDefect.Internal.Representation.aesm_apply` (`Breakdown/CellReduction/AdjointRepresentation.lean:245`).

**Theorem: Matrix pairings are measurable a.e..** The matrix inner product of the two measurable fields is strongly measurable almost everywhere. Source: `Breakdown.AdjointDefect.Internal.Representation.aesm_pairSum` (`Breakdown/CellReduction/AdjointRepresentation.lean:252`).

**Theorem: An integrable norm bound suffices.** The finite integrable majorant for the extended norm implies integrability of h. Source: `Breakdown.AdjointDefect.Internal.Representation.integrable_of_enorm_le` (`Breakdown/CellReduction/AdjointRepresentation.lean:266`).

**Theorem: Square bounds make the product finite.** The square-integral bounds make the nonnegative integral of the product finite. Source: `Breakdown.AdjointDefect.Internal.Representation.sq_bound_lt_top` (`Breakdown/CellReduction/AdjointRepresentation.lean:270`).

**Theorem: Mixed norms make the product finite.** The complementary mixed-norm bounds make the nonnegative integral of the product finite. Source: `Breakdown.AdjointDefect.Internal.Representation.mixed_bound_lt_top` (`Breakdown/CellReduction/AdjointRepresentation.lean:278`).

**Theorem: Scaled square roots tend to zero.** A fixed finite scalar times the square root of a nonnegative sequence tending to zero also tends to zero. Source: `Breakdown.AdjointDefect.Internal.Representation.tendsto_const_mul_sqrt` (`Breakdown/CellReduction/AdjointRepresentation.lean:287`).

**Theorem: Square-small errors vanish in pairing.** A uniformly square-controlled factor paired with an error tending to zero in square integral has product integral tending to zero. Source: `Breakdown.AdjointDefect.Internal.Representation.sq_bound_tendsto` (`Breakdown/CellReduction/AdjointRepresentation.lean:295`).

**Theorem: Mixed-small errors vanish in pairing.** A controlled factor paired with an error tending to zero in the complementary mixed norm has product integral tending to zero. Source: `Breakdown.AdjointDefect.Internal.Representation.mixed_bound_tendsto` (`Breakdown/CellReduction/AdjointRepresentation.lean:308`).

**Theorem: Pass integrable pairings to the limit.** The approximating pairing integrands are eventually integrable and their integrals converge to the integral of the limiting pairing. Source: `Breakdown.AdjointDefect.Internal.Representation.pass_limit` (`Breakdown/CellReduction/AdjointRepresentation.lean:322`).

**Theorem: Reconstruct a vector from coordinates.** Every vector is the sum of its coordinates times the coordinate unit vectors. Source: `Breakdown.AdjointDefect.Internal.Representation.sum_unitVector` (`Breakdown/CellReduction/AdjointRepresentation.lean:339`).

**Theorem: Coordinate vectors have unit norm.** Every coordinate unit vector has norm one. Source: `Breakdown.AdjointDefect.Internal.Representation.norm_unitVector` (`Breakdown/CellReduction/AdjointRepresentation.lean:343`).

**Theorem: The matrix square norm is continuous.** The sum of the squared matrix-column norms depends continuously on the matrix. Source: `Breakdown.AdjointDefect.Internal.Representation.continuous_entrySq` (`Breakdown/CellReduction/AdjointRepresentation.lean:346`).

**Theorem: Matrix square norm is nonnegative.** The sum of the squared matrix-column norms is nonnegative. Source: `Breakdown.AdjointDefect.Internal.Representation.entrySq_nonneg` (`Breakdown/CellReduction/AdjointRepresentation.lean:350`).

**Theorem: Use the column norm to bound an image.** The norm of a matrix applied to a vector is bounded by the vector norm times the square root of the column-square sum. Source: `Breakdown.AdjointDefect.Internal.Representation.norm_apply_le_entrySq_root` (`Breakdown/CellReduction/AdjointRepresentation.lean:353`).

**Theorem: Compare column and operator norms.** The square root of the column-square sum is at most twice the operator norm in three dimensions. Source: `Breakdown.AdjointDefect.Internal.Representation.entrySq_root_le_two_norm` (`Breakdown/CellReduction/AdjointRepresentation.lean:367`).

**Theorem: Cauchy–Schwarz for matrix pairing.** The absolute matrix pairing is bounded by the product of the square roots of the two column-square sums. Source: `Breakdown.AdjointDefect.Internal.Representation.abs_pairSum_le` (`Breakdown/CellReduction/AdjointRepresentation.lean:379`).

**Theorem: Matrix pairing preserves subtraction.** The matrix pairing distributes over subtraction in its second argument. Source: `Breakdown.AdjointDefect.Internal.Representation.pairSum_sub_right` (`Breakdown/CellReduction/AdjointRepresentation.lean:387`).

**Theorem: Scaling a matrix squares its coefficient.** The column-square sum of c times a matrix equals c squared times its original column-square sum. Source: `Breakdown.AdjointDefect.Internal.Representation.entrySq_smul` (`Breakdown/CellReduction/AdjointRepresentation.lean:391`).

**Definition: Forcing against a test field.** The forcing integrand is the inner product of the forcing and the test field. Source: `Breakdown.AdjointDefect.Internal.Representation.pairF` (`Breakdown/CellReduction/AdjointRepresentation.lean:394`).

**Definition: Transport against a test field.** The transport integrand pairs the gradient applied to the flow with the test field. Source: `Breakdown.AdjointDefect.Internal.Representation.pairGW` (`Breakdown/CellReduction/AdjointRepresentation.lean:396`).

**Definition: Strain against a test field.** The strain integrand pairs the model gradient applied to velocity with the test field. Source: `Breakdown.AdjointDefect.Internal.Representation.pairWv` (`Breakdown/CellReduction/AdjointRepresentation.lean:399`).

**Definition: Pairing of test and weak gradients.** The gradient integrand is the matrix pairing of the weak gradient and the test gradient. Source: `Breakdown.AdjointDefect.Internal.Representation.pairG` (`Breakdown/CellReduction/AdjointRepresentation.lean:402`).

**Definition: Similarity-time test pairing.** The similarity-time integrand pairs velocity with the time, zeroth-order and radial derivative terms of the test field. Source: `Breakdown.AdjointDefect.Internal.Representation.pairT` (`Breakdown/CellReduction/AdjointRepresentation.lean:405`).

**Theorem: Embed an ordinary norm bound.** An ordinary norm bound gives the corresponding upper bound on the extended norm. Source: `Breakdown.AdjointDefect.Internal.Representation.enorm_le_ofReal` (`Breakdown/CellReduction/AdjointRepresentation.lean:409`).

**Theorem: Control the force-pairing error.** The force-pairing difference is bounded by force norm times the test-field difference norm. Source: `Breakdown.AdjointDefect.Internal.Representation.pairF_sub` (`Breakdown/CellReduction/AdjointRepresentation.lean:413`).

**Theorem: Control the transport-pairing error.** The transport-pairing difference is bounded by D times the gradient column norm times the test-field difference norm. Source: `Breakdown.AdjointDefect.Internal.Representation.pairGW_sub` (`Breakdown/CellReduction/AdjointRepresentation.lean:421`).

**Theorem: Control the background-gradient error.** The background-gradient pairing difference is bounded by D times the radially weighted velocity norm times the test-field difference norm. Source: `Breakdown.AdjointDefect.Internal.Representation.pairWv_sub` (`Breakdown/CellReduction/AdjointRepresentation.lean:435`).

**Theorem: Control the gradient-pairing error.** The gradient-pairing difference is bounded by the gradient column norm times the column norm of the test-gradient difference. Source: `Breakdown.AdjointDefect.Internal.Representation.pairG_sub` (`Breakdown/CellReduction/AdjointRepresentation.lean:453`).

**Theorem: Split the time-transport pairing error.** The time-transport pairing difference is bounded by velocity norm times the weighted time, value and radial-derivative errors. Source: `Breakdown.AdjointDefect.Internal.Representation.pairT_sub` (`Breakdown/CellReduction/AdjointRepresentation.lean:462`).

**Theorem: Derivatives of the zero field vanish.** The specified time or spatial derivative of the zero vector field is zero. Source: `Breakdown.AdjointDefect.Internal.Representation.zeroField_fderiv` (`Breakdown/CellReduction/AdjointRepresentation.lean:496`).

**Theorem: Pairing with the zero test vanishes.** The specified weak-equation pairing is zero when its test field is zero. Source: `Breakdown.AdjointDefect.Internal.Representation.pairF_zero` (`Breakdown/CellReduction/AdjointRepresentation.lean:500`).

**Theorem: Pairing with the zero test vanishes.** The specified weak-equation pairing is zero when its test field is zero. Source: `Breakdown.AdjointDefect.Internal.Representation.pairGW_zero` (`Breakdown/CellReduction/AdjointRepresentation.lean:503`).

**Theorem: Pairing with the zero test vanishes.** The specified weak-equation pairing is zero when its test field is zero. Source: `Breakdown.AdjointDefect.Internal.Representation.pairWv_zero` (`Breakdown/CellReduction/AdjointRepresentation.lean:507`).

**Theorem: Pairing with the zero test vanishes.** The specified weak-equation pairing is zero when its test field is zero. Source: `Breakdown.AdjointDefect.Internal.Representation.pairG_zero` (`Breakdown/CellReduction/AdjointRepresentation.lean:510`).

**Theorem: Pairing with the zero test vanishes.** The specified weak-equation pairing is zero when its test field is zero. Source: `Breakdown.AdjointDefect.Internal.Representation.pairT_zero` (`Breakdown/CellReduction/AdjointRepresentation.lean:513`).

**Theorem: Square the embedded real square root.** The square of the embedded real square root equals the nonnegative embedding of the original real number. Source: `Breakdown.AdjointDefect.Internal.Representation.ofReal_sqrt_sq` (`Breakdown/CellReduction/AdjointRepresentation.lean:516`).

**Theorem: Scale a strip square integral.** Multiplying by a fixed scalar preserves finiteness of the square integral on the time strip. Source: `Breakdown.AdjointDefect.Internal.Representation.strip_const_mul_sq` (`Breakdown/CellReduction/AdjointRepresentation.lean:519`).

**Theorem: Bound the mixed norm by a scalar.** A pointwise bound by c times f bounds the squared mixed norm by c squared times the mixed norm of f. Source: `Breakdown.AdjointDefect.Internal.Representation.mixed_le_scalar` (`Breakdown/CellReduction/AdjointRepresentation.lean:535`).

**Theorem: Bound the square integral by a scalar.** A pointwise bound by c times f bounds the square integral by c squared times the square integral of f. Source: `Breakdown.AdjointDefect.Internal.Representation.sq_le_scalar` (`Breakdown/CellReduction/AdjointRepresentation.lean:560`).

**Theorem: A finite scalar preserves a zero limit.** Multiplication by a fixed real-derived nonnegative scalar preserves convergence to zero. Source: `Breakdown.AdjointDefect.Internal.Representation.tendsto_ofReal_mul` (`Breakdown/CellReduction/AdjointRepresentation.lean:569`).

**Theorem: The strip cutoff is zero outside.** Outside the time strip, the absolute strip cutoff times any scalar is zero. Source: `Breakdown.AdjointDefect.Internal.Representation.abs_stripCutoff_mul_zero_off` (`Breakdown/CellReduction/AdjointRepresentation.lean:574`).

**Theorem: The strip derivative is zero outside.** Outside the time strip, the absolute strip-cutoff derivative times any scalar is zero. Source: `Breakdown.AdjointDefect.Internal.Representation.abs_deriv_stripCutoff_mul_zero_off` (`Breakdown/CellReduction/AdjointRepresentation.lean:578`).

**Theorem: The cutoff scales the error norm.** The cut-test error norm equals the absolute strip cutoff times the original error norm. Source: `Breakdown.AdjointDefect.Internal.Representation.norm_cutTest_sub_le` (`Breakdown/CellReduction/AdjointRepresentation.lean:582`).

**Theorem: Pass a value pairing to the limit.** The stated value-pairing integrands are integrable and their integrals converge from the cut-off test sequence to the time-truncated adjoint. Source: `Breakdown.AdjointDefect.Internal.Representation.pass_value` (`Breakdown/CellReduction/AdjointRepresentation.lean:586`).

**Theorem: The cutoff squares the gradient error.** The gradient error's column-square sum after cutting equals the strip cutoff squared times the original column-square error. Source: `Breakdown.AdjointDefect.Internal.Representation.fderiv_cutTest_sub_eq` (`Breakdown/CellReduction/AdjointRepresentation.lean:631`).

**Theorem: Pass the gradient pairing to the limit.** The gradient pairings are eventually integrable and their integrals converge to the pairing with the time-windowed adjoint. Source: `Breakdown.AdjointDefect.Internal.Representation.pass_pairG` (`Breakdown/CellReduction/AdjointRepresentation.lean:636`).

**Theorem: Derivatives of the zero field vanish.** The specified time or spatial derivative of the zero vector field is zero. Source: `Breakdown.AdjointDefect.Internal.Representation.timeDerivative_zeroField` (`Breakdown/CellReduction/AdjointRepresentation.lean:698`).

**Theorem: Derivatives of the zero field vanish.** The specified time or spatial derivative of the zero vector field is zero. Source: `Breakdown.AdjointDefect.Internal.Representation.fderiv_zeroField_apply` (`Breakdown/CellReduction/AdjointRepresentation.lean:702`).

**Theorem: Time-transport pairing is measurable.** The time-transport pairing is strongly measurable almost everywhere. Source: `Breakdown.AdjointDefect.Internal.Representation.aesm_pairT` (`Breakdown/CellReduction/AdjointRepresentation.lean:706`).

**Theorem: The test time derivative is continuous.** The time derivative of the smooth spacetime test field is jointly continuous. Source: `Breakdown.AdjointDefect.Internal.Representation.continuous_test_timeDerivative` (`Breakdown/CellReduction/AdjointRepresentation.lean:718`).

**Theorem: The test radial derivative is continuous.** The spatial derivative of the smooth test field applied to the position vector is jointly continuous. Source: `Breakdown.AdjointDefect.Internal.Representation.continuous_test_fderiv_apply` (`Breakdown/CellReduction/AdjointRepresentation.lean:722`).

**Theorem: Scale the radial derivative error.** The radial derivative error norm after cutting equals the absolute strip cutoff times the original error norm. Source: `Breakdown.AdjointDefect.Internal.Representation.cutTest_fderiv_apply_sub` (`Breakdown/CellReduction/AdjointRepresentation.lean:726`).

**Theorem: Bound the cutoff time-derivative error.** The weighted time-derivative error is bounded by the sum of the strip-derivative value error and the strip-cutoff time error. Source: `Breakdown.AdjointDefect.Internal.Representation.cutTest_timeDerivative_sub_le` (`Breakdown/CellReduction/AdjointRepresentation.lean:732`).

**Theorem: Pass the time pairing to the limit.** The time-transport pairings are eventually integrable and their integrals converge to the pairing with the time-windowed adjoint. Source: `Breakdown.AdjointDefect.Internal.Representation.pass_pairT` (`Breakdown/CellReduction/AdjointRepresentation.lean:744`).

**Theorem: Split the weak right-hand side.** The weak right-hand-side integrand with zero shape coefficients is the sum of force, transport, background-gradient and gradient pairings. Source: `Breakdown.AdjointDefect.Internal.Representation.rightSide_integrand` (`Breakdown/CellReduction/AdjointRepresentation.lean:943`).

**Theorem: An eventual constant equals the limit.** A convergent sequence that is eventually equal to a constant has that constant as its limit. Source: `Breakdown.AdjointDefect.Internal.Representation.limit_eq_of_eventually` (`Breakdown/CellReduction/AdjointRepresentation.lean:952`).

**Theorem: Pass both weak identities to the limit.** The approximating test fields yield both weak pairing identities for the time-truncated adjoint, with all listed terms integrable. Source: `Breakdown.AdjointDefect.Internal.Representation.limit_identities` (`Breakdown/CellReduction/AdjointRepresentation.lean:956`).

**Theorem: Mixed norms control integrability.** The given mixed time-space estimate makes the pairing integrand integrable. Source: `Breakdown.AdjointDefect.Internal.Representation.integrable_mixed_of` (`Breakdown/CellReduction/AdjointRepresentation.lean:1033`).

**Theorem: Square bounds give integrability.** The stated square-norm majorant and measurability hypotheses make h integrable. Source: `Breakdown.AdjointDefect.Internal.Representation.integrable_sq_of` (`Breakdown/CellReduction/AdjointRepresentation.lean:1052`).

**Definition: Indicator of one time period.** The unit weight is one on the closed unit interval and zero elsewhere. Source: `Breakdown.AdjointDefect.Internal.Representation.unitWeight` (`Breakdown/CellReduction/AdjointRepresentation.lean:1070`).

**Theorem: The period indicator is nonnegative.** The unit-period indicator is nonnegative at every time. Source: `Breakdown.AdjointDefect.Internal.Representation.unitWeight_nonneg` (`Breakdown/CellReduction/AdjointRepresentation.lean:1072`).

**Theorem: The period indicator is at most one.** The unit-period indicator is at most one at every time. Source: `Breakdown.AdjointDefect.Internal.Representation.unitWeight_le_one` (`Breakdown/CellReduction/AdjointRepresentation.lean:1076`).

**Theorem: The period indicator vanishes outside.** Outside the unit interval, the unit-period indicator is zero. Source: `Breakdown.AdjointDefect.Internal.Representation.unitWeight_zero_off` (`Breakdown/CellReduction/AdjointRepresentation.lean:1080`).

**Theorem: The period indicator is measurable.** The indicator of the unit time interval is measurable. Source: `Breakdown.AdjointDefect.Internal.Representation.measurable_unitWeight` (`Breakdown/CellReduction/AdjointRepresentation.lean:1084`).

**Theorem: Integrate spatial slices over a period.** The spatial integral is integrable as a function of time on the unit interval. Source: `Breakdown.AdjointDefect.Internal.Representation.slice_integrableOn` (`Breakdown/CellReduction/AdjointRepresentation.lean:1087`).

**Theorem: Separate a time weight by Fubini.** The spacetime integral with a time-only scalar weight equals the time integral of that weight times the spatial integral. Source: `Breakdown.AdjointDefect.Internal.Representation.integral_weight_prod` (`Breakdown/CellReduction/AdjointRepresentation.lean:1102`).

**Theorem: The time derivative is periodic.** The time derivative of the periodic differentiable field has period one. Source: `Breakdown.AdjointDefect.Internal.Representation.timeDerivative_periodic` (`Breakdown/CellReduction/AdjointRepresentation.lean:1110`).

**Theorem: A unit shift preserves the whole slice.** Pointwise time periodicity identifies the entire vector-field slice after a unit shift. Source: `Breakdown.AdjointDefect.Internal.Representation.slice_periodic` (`Breakdown/CellReduction/AdjointRepresentation.lean:1118`).

**Theorem: Move a matrix across an inner product.** Pairing K applied to w with z equals pairing w with the transpose of K applied to z. Source: `Breakdown.AdjointDefect.Internal.Representation.inner_apply_transpose` (`Breakdown/CellReduction/AdjointRepresentation.lean:1121`).

**Theorem: Scale the matrix pairing.** A scalar factor in the second matrix becomes the same scalar factor outside the pairing. Source: `Breakdown.AdjointDefect.Internal.Representation.pairSum_smul_right` (`Breakdown/CellReduction/AdjointRepresentation.lean:1131`).

**Theorem: Bound the transpose action.** The transpose action has norm at most three times the matrix operator norm times the vector norm. Source: `Breakdown.AdjointDefect.Internal.Representation.norm_transposeApply_le` (`Breakdown/CellReduction/AdjointRepresentation.lean:1134`).

**Theorem: Collect the adjoint transport terms.** The four weak pairing terms combine into the window-weighted adjoint transport and gradient pairings plus the derivative-of-window correction. Source: `Breakdown.AdjointDefect.Internal.Representation.combine_pointwise` (`Breakdown/CellReduction/AdjointRepresentation.lean:1147`).

**Theorem: Finite gradient slices almost everywhere.** For almost every time in the strip, the spatial column-square integral of the weak gradient is finite. Source: `Breakdown.AdjointDefect.Internal.Representation.entrySq_slice_ae` (`Breakdown/CellReduction/AdjointRepresentation.lean:1163`).

**Theorem: Move convection onto the adjoint.** The transport pairing with the time-cut adjoint equals minus the window-weighted velocity pairing with the adjoint's directional derivative. Source: `Breakdown.AdjointDefect.Internal.Representation.convection_integral` (`Breakdown/CellReduction/AdjointRepresentation.lean:1175`).

**Theorem: Adjoint transport is jointly continuous.** The given regularity makes the adjoint transport field jointly continuous. Source: `Breakdown.AdjointDefect.Internal.Representation.continuous_adjointTransport` (`Breakdown/CellReduction/AdjointRepresentation.lean:1204`).

**Theorem: Adjoint transport retains radial decay.** The adjoint transport norm is bounded by (|1/P|+2+4D)C times the gamma-order radial decay. Source: `Breakdown.AdjointDefect.Internal.Representation.adjointTransport_norm_le` (`Breakdown/CellReduction/AdjointRepresentation.lean:1221`).

**Theorem: All windowed weak terms are integrable.** The five windowed convection, cutoff-derivative, force, velocity and adjoint-energy integrands are integrable. Source: `Breakdown.AdjointDefect.Internal.Representation.weighted_integrabilities` (`Breakdown/CellReduction/AdjointRepresentation.lean:1253`).

**Theorem: Adjoint transport has period one.** The periodic data make the adjoint transport invariant under a unit time shift. Source: `Breakdown.AdjointDefect.Internal.Representation.adjointTransport_periodic` (`Breakdown/CellReduction/AdjointRepresentation.lean:1372`).

### Breakdown.CellReduction.AdjointRepresentationSlice

A spatial cutoff proves the convection integration-by-parts identity for a weak gradient and a divergence-free flow.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: Expand a linear map in coordinates.** Applying a linear map to a vector equals the coordinate-weighted sum of its values on the three coordinate unit vectors. Source: `Breakdown.RepresentationParts.Internal.Slice.linear_expand` (`Breakdown/CellReduction/AdjointRepresentationSlice.lean:18`).

**Theorem: Expand the Euclidean inner product.** The Euclidean inner product equals the sum of the three coordinate products. Source: `Breakdown.RepresentationParts.Internal.Slice.inner_expand` (`Breakdown/CellReduction/AdjointRepresentationSlice.lean:23`).

**Theorem: Coordinates retain local integrability.** Each coordinate of a locally integrable vector field is locally integrable. Source: `Breakdown.RepresentationParts.Internal.Slice.component_locallyIntegrable` (`Breakdown/CellReduction/AdjointRepresentationSlice.lean:26`).

**Theorem: A matrix applied to a fixed vector.** Applying a locally integrable matrix field to a fixed vector gives a locally integrable vector field. Source: `Breakdown.RepresentationParts.Internal.Slice.apply_locallyIntegrable` (`Breakdown/CellReduction/AdjointRepresentationSlice.lean:32`).

**Theorem: A coordinate weak integration identity.** Pairing a scalar test derivative with a velocity coordinate equals minus the pairing of the test with the corresponding weak derivative. Source: `Breakdown.RepresentationParts.Internal.Slice.weak_component` (`Breakdown/CellReduction/AdjointRepresentationSlice.lean:38`).

**Theorem: Integrate cutoff convection by parts.** The cutoff-weighted convection pairing equals minus the directional test-derivative pairing and the derivative-of-cutoff error. Source: `Breakdown.RepresentationParts.Internal.Slice.cutoff_identity` (`Breakdown/CellReduction/AdjointRepresentationSlice.lean:60`).

**Theorem: Young inequality for powers 6 and 6/5.** The product of nonnegative factors is bounded by the first factor to the sixth power plus the second to the six-fifths power. Source: `Breakdown.RepresentationParts.Internal.Slice.mul_le_sixth_add` (`Breakdown/CellReduction/AdjointRepresentationSlice.lean:139`).

**Theorem: Integrable powers from radial decay.** The decay exponent and power assumptions make the stated real power spatially integrable. Source: `Breakdown.RepresentationParts.Internal.Slice.decay_rpow_integrable` (`Breakdown/CellReduction/AdjointRepresentationSlice.lean:157`).

**Theorem: Transfer convection to the test field.** The integrated pairing of the weak derivative applied to W with the adjoint equals minus the pairing of velocity with the adjoint derivative applied to W. Source: `Breakdown.RepresentationParts.slice_convection_pairing` (`Breakdown/CellReduction/AdjointRepresentationSlice.lean:179`).

### Breakdown.CellReduction.AdjointRepresentationStrip

Estimates on a finite time strip provide the square and mixed integrability needed to pass to the adjoint test limit.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: Square an indicator by squaring inside.** The square of a set indicator equals the indicator of the squared function. Source: `Breakdown.RepresentationParts.Internal.indicator_rpow_two` (`Breakdown/CellReduction/AdjointRepresentationStrip.lean:16`).

**Theorem: Restrict a spacetime lower integral.** The lower integral of the time-strip indicator equals the iterated spatial and restricted-time lower integrals. Source: `Breakdown.RepresentationParts.Internal.lintegral_strip_indicator` (`Breakdown/CellReduction/AdjointRepresentationStrip.lean:21`).

**Theorem: Replace a decay coefficient by its size.** The radial quotient with coefficient c is at most its negative-power expression with coefficient |c|. Source: `Breakdown.RepresentationParts.Internal.abs_decay_bound` (`Breakdown/CellReduction/AdjointRepresentationStrip.lean:28`).

**Theorem: Integrate sufficiently rapid decay.** The nonnegative integral of the stated radial decay is finite when its exponent exceeds the spatial dimension. Source: `Breakdown.RepresentationParts.Internal.lintegral_decay_lt_top` (`Breakdown/CellReduction/AdjointRepresentationStrip.lean:34`).

**Theorem: Bounded support gives a finite integral.** The bounded time-strip majorant makes the nonnegative time integral finite. Source: `Breakdown.RepresentationParts.Internal.strip_const_lt_top` (`Breakdown/CellReduction/AdjointRepresentationStrip.lean:41`).

**Theorem: Matrix square norm is nonnegative.** The sum of the squared matrix-column norms is nonnegative. Source: `Breakdown.RepresentationParts.Internal.entrySqSum_nonneg` (`Breakdown/CellReduction/AdjointRepresentationStrip.lean:48`).

**Theorem: The matrix square norm is continuous.** The sum of the squared matrix-column norms depends continuously on the matrix. Source: `Breakdown.RepresentationParts.Internal.entrySqSum_continuous` (`Breakdown/CellReduction/AdjointRepresentationStrip.lean:51`).

**Theorem: Cauchy inequality on a time strip.** The integral of a strip-supported product is bounded by the product of its two square-integral norms. Source: `Breakdown.RepresentationParts.lintegral_mul_le_strip_sq` (`Breakdown/CellReduction/AdjointRepresentationStrip.lean:57`).

**Theorem: Mixed Holder inequality on the strip.** The product integral is bounded by the time-L2 space-L6 norm of one factor times the time-L2 space-L6/5 norm of the other. Source: `Breakdown.RepresentationParts.lintegral_mul_le_strip_mixed` (`Breakdown/CellReduction/AdjointRepresentationStrip.lean:81`).

**Theorem: Strip decay gives a square integral.** The time support and spatial decay assumptions make the spacetime square integral finite. Source: `Breakdown.RepresentationParts.square_decay_lt_top` (`Breakdown/CellReduction/AdjointRepresentationStrip.lean:125`).

**Theorem: Strip decay gives the dual mixed norm.** The time support and spatial decay assumptions make the squared time-L2 space-L6/5 norm finite. Source: `Breakdown.RepresentationParts.mixed_decay_lt_top` (`Breakdown/CellReduction/AdjointRepresentationStrip.lean:154`).

**Theorem: Finite strip field square norm.** Periodicity and the field bounds give a finite square integral over the time strip. Source: `Breakdown.RepresentationParts.strip_square_lt_top` (`Breakdown/CellReduction/AdjointRepresentationStrip.lean:179`).

**Theorem: Finite strip gradient square norm.** Periodicity and the gradient bounds give a finite column-square integral over the time strip. Source: `Breakdown.RepresentationParts.strip_entrySq_lt_top` (`Breakdown/CellReduction/AdjointRepresentationStrip.lean:191`).

**Theorem: Finite strip radial velocity norm.** The inverse-square control gives a finite strip integral of velocity norm squared divided by (1+radius) squared. Source: `Breakdown.RepresentationParts.strip_inverseSquare_lt_top` (`Breakdown/CellReduction/AdjointRepresentationStrip.lean:201`).

**Theorem: Finite strip mixed velocity norm.** The velocity bounds give a finite integral over the strip of the cube root of its spatial sixth-power integral. Source: `Breakdown.RepresentationParts.strip_sixth_lt_top` (`Breakdown/CellReduction/AdjointRepresentationStrip.lean:224`).

### Breakdown.CellReduction.AdjointRepresentationWindow

Two compact smooth time cutoffs convert integrals of periodic quantities into integrals over one period.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Definition: Smooth period window.** The period window is the difference of two unit-shifted smooth transition functions. Source: `Breakdown.RepresentationParts.windowBump` (`Breakdown/CellReduction/AdjointRepresentationWindow.lean:12`).

**Definition: Smooth time-strip cutoff.** The time-strip cutoff multiplies a left transition by a right transition. Source: `Breakdown.RepresentationParts.stripCutoff` (`Breakdown/CellReduction/AdjointRepresentationWindow.lean:14`).

**Theorem: The transition function is smooth.** The smooth transition function is infinitely differentiable. Source: `Breakdown.RepresentationParts.Internal.transition_contDiff` (`Breakdown/CellReduction/AdjointRepresentationWindow.lean:16`).

**Theorem: Differentiate the smooth transition.** The smooth transition function is differentiable. Source: `Breakdown.RepresentationParts.Internal.transition_differentiable` (`Breakdown/CellReduction/AdjointRepresentationWindow.lean:19`).

**Theorem: Transition derivative vanishes outside.** The smooth transition has zero derivative on the stated constant side of its transition interval. Source: `Breakdown.RepresentationParts.Internal.deriv_transition_of_nonpos` (`Breakdown/CellReduction/AdjointRepresentationWindow.lean:22`).

**Theorem: Transition derivative vanishes outside.** The smooth transition has zero derivative on the stated constant side of its transition interval. Source: `Breakdown.RepresentationParts.Internal.deriv_transition_of_one_le` (`Breakdown/CellReduction/AdjointRepresentationWindow.lean:28`).

**Theorem: Differentiate outside the closed support.** A differentiable function vanishing outside the closed interval has zero derivative at the stated exterior point. Source: `Breakdown.RepresentationParts.Internal.deriv_eq_zero_off_closed` (`Breakdown/CellReduction/AdjointRepresentationWindow.lean:34`).

**Theorem: The time window vanishes outside.** The time window is zero outside its support interval from minus one to one. Source: `Breakdown.RepresentationParts.Internal.windowBump_eq_zero_of_le` (`Breakdown/CellReduction/AdjointRepresentationWindow.lean:41`).

**Theorem: The time window vanishes outside.** The time window is zero outside its support interval from minus one to one. Source: `Breakdown.RepresentationParts.Internal.windowBump_eq_zero_of_ge` (`Breakdown/CellReduction/AdjointRepresentationWindow.lean:47`).

**Theorem: Two shifted windows sum to one.** On the unit interval, the window at u minus one plus the window at u equals one. Source: `Breakdown.RepresentationParts.Internal.windowBump_pair` (`Breakdown/CellReduction/AdjointRepresentationWindow.lean:52`).

**Theorem: Differentiate the window difference.** The time-window derivative is the transition derivative at s+1 minus the transition derivative at s. Source: `Breakdown.RepresentationParts.Internal.deriv_windowBump` (`Breakdown/CellReduction/AdjointRepresentationWindow.lean:59`).

**Theorem: The window derivative vanishes outside.** The time-window derivative is zero outside the closed interval from minus one to one. Source: `Breakdown.RepresentationParts.Internal.deriv_windowBump_eq_zero_of_le` (`Breakdown/CellReduction/AdjointRepresentationWindow.lean:67`).

**Theorem: The window derivative vanishes outside.** The time-window derivative is zero outside the closed interval from minus one to one. Source: `Breakdown.RepresentationParts.Internal.deriv_windowBump_eq_zero_of_ge` (`Breakdown/CellReduction/AdjointRepresentationWindow.lean:73`).

**Theorem: Shifted window derivatives cancel.** On the unit interval, the derivatives of the two shifted windows sum to zero. Source: `Breakdown.RepresentationParts.Internal.deriv_windowBump_pair` (`Breakdown/CellReduction/AdjointRepresentationWindow.lean:79`).

**Theorem: Two sides of the time window.** A real number outside the open interval from minus one to one is at most minus one or at least one. Source: `Breakdown.RepresentationParts.Internal.not_mem_Ioo_cases` (`Breakdown/CellReduction/AdjointRepresentationWindow.lean:86`).

**Theorem: The time window is smooth.** The time window is infinitely differentiable. Source: `Breakdown.RepresentationParts.windowBump_contDiff` (`Breakdown/CellReduction/AdjointRepresentationWindow.lean:90`).

**Theorem: The time window vanishes outside.** The time window is zero outside its support interval from minus one to one. Source: `Breakdown.RepresentationParts.windowBump_eq_zero` (`Breakdown/CellReduction/AdjointRepresentationWindow.lean:96`).

**Theorem: The time window has compact support.** The time window has compact support in time. Source: `Breakdown.RepresentationParts.windowBump_hasCompactSupport` (`Breakdown/CellReduction/AdjointRepresentationWindow.lean:102`).

**Theorem: The window derivative vanishes outside.** The time-window derivative is zero outside the closed interval from minus one to one. Source: `Breakdown.RepresentationParts.deriv_windowBump_eq_zero` (`Breakdown/CellReduction/AdjointRepresentationWindow.lean:105`).

**Theorem: The time window has size at most one.** The absolute value of the time window is at most one. Source: `Breakdown.RepresentationParts.abs_windowBump_le` (`Breakdown/CellReduction/AdjointRepresentationWindow.lean:108`).

**Theorem: Bound the compact function's derivative.** A continuously differentiable compactly supported function has a uniformly bounded derivative. Source: `Breakdown.RepresentationParts.Internal.exists_abs_deriv_le_of_contDiff` (`Breakdown/CellReduction/AdjointRepresentationWindow.lean:116`).

**Theorem: The window derivative is bounded.** There is one nonnegative bound for the absolute time-window derivative. Source: `Breakdown.RepresentationParts.exists_abs_deriv_windowBump_le` (`Breakdown/CellReduction/AdjointRepresentationWindow.lean:124`).

**Theorem: The strip cutoff is smooth.** The strip cutoff is infinitely differentiable. Source: `Breakdown.RepresentationParts.stripCutoff_contDiff` (`Breakdown/CellReduction/AdjointRepresentationWindow.lean:127`).

**Theorem: The strip cutoff vanishes outside.** The specified strip cutoff or its derivative is zero outside the strip from minus two to two. Source: `Breakdown.RepresentationParts.stripCutoff_eq_zero` (`Breakdown/CellReduction/AdjointRepresentationWindow.lean:135`).

**Theorem: The strip cutoff vanishes outside.** The specified strip cutoff or its derivative is zero outside the strip from minus two to two. Source: `Breakdown.RepresentationParts.deriv_stripCutoff_eq_zero` (`Breakdown/CellReduction/AdjointRepresentationWindow.lean:142`).

**Theorem: The strip cutoff has size at most one.** The absolute strip cutoff is at most one. Source: `Breakdown.RepresentationParts.abs_stripCutoff_le` (`Breakdown/CellReduction/AdjointRepresentationWindow.lean:145`).

**Theorem: The strip derivative is bounded.** There is one nonnegative bound for the absolute strip-cutoff derivative. Source: `Breakdown.RepresentationParts.exists_abs_deriv_stripCutoff_le` (`Breakdown/CellReduction/AdjointRepresentationWindow.lean:154`).

**Theorem: The strip cutoff preserves the window.** Multiplying the time window by the strip cutoff leaves the time window unchanged. Source: `Breakdown.RepresentationParts.stripCutoff_mul_windowBump` (`Breakdown/CellReduction/AdjointRepresentationWindow.lean:158`).

**Theorem: Fold the window into one period.** For the periodic factor, the full weighted integral equals the unit-interval integral weighted by the sum of the two window shifts. Source: `Breakdown.RepresentationParts.Internal.integral_mul_periodic` (`Breakdown/CellReduction/AdjointRepresentationWindow.lean:165`).

**Theorem: The window extracts one whole period.** Multiplying a unit-periodic function by the time window and integrating over the line gives its integral over the unit interval. Source: `Breakdown.RepresentationParts.integral_windowBump_mul` (`Breakdown/CellReduction/AdjointRepresentationWindow.lean:199`).

**Theorem: The derivative-window integral vanishes.** The integral of the time-window derivative times a unit-periodic function is zero. Source: `Breakdown.RepresentationParts.integral_deriv_windowBump_mul` (`Breakdown/CellReduction/AdjointRepresentationWindow.lean:211`).

**Theorem: Shift a periodic lower integral.** The lower integral of a unit-periodic nonnegative function over any unit interval equals its integral over the standard unit interval. Source: `Breakdown.RepresentationParts.Internal.setLIntegral_shift` (`Breakdown/CellReduction/AdjointRepresentationWindow.lean:227`).

**Theorem: Four periods bound the time strip.** The nonnegative integral over the strip from minus two to two is at most four times the unit-period integral. Source: `Breakdown.RepresentationParts.setLIntegral_strip_le` (`Breakdown/CellReduction/AdjointRepresentationWindow.lean:238`).

### Breakdown.CellReduction.AdjointStatements

The adjoint argument records its potential, density, remainder, pin and free-shift obligations as named propositions.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Definition: The mixed time-space error integral.** The mixed integral takes the spatial six-fifths power and then the five-thirds power before time integration. Source: `Breakdown.AdjointDefect.mixedNorm` (`Breakdown/CellReduction/AdjointStatements.lean:13`).

**Definition: Time truncation of the adjoint.** The adjoint field is multiplied by the prescribed scalar time cutoff. Source: `Breakdown.AdjointDefect.timeCutoff` (`Breakdown/CellReduction/AdjointStatements.lean:16`).

**Interface definition: Existence of an adjoint curl potential.** This proposition requires that every admissible adjoint field has a periodic decaying curl potential. Source: `Breakdown.AdjointDefect.CurlPotentialExistsHolds` (`Breakdown/CellReduction/AdjointStatements.lean:18`).

No theorem in the library states this proposition as its result.

**Interface definition: Approximate the adjoint test field.** This proposition requires that a time-truncated adjoint with a curl potential admits divergence-free compact test approximants in the required square and mixed norms. Source: `Breakdown.AdjointDefect.TestFieldDensityHolds` (`Breakdown/CellReduction/AdjointStatements.lean:22`).

Supplied by `Breakdown.AdjointDefect.testFieldDensityHolds_proof` (`lean/Breakdown/CellReduction/AdjointTestDensity.lean:17`).

**Interface definition: Bound the potential defect pairing.** This proposition requires that the residual and flux pairings are bounded by the potential defect coefficient times the square root of weighted energy. Source: `Breakdown.AdjointDefect.PotentialBoundHolds` (`Breakdown/CellReduction/AdjointStatements.lean:50`).

Supplied by `Breakdown.AdjointDefect.potentialBoundHolds_proof` (`lean/Breakdown/CellReduction/AdjointPotentialBound.lean:135`).

**Interface definition: Direct remainder dual bound.** This proposition requires that the direct weighted remainder bound implies the remainder dual estimate. Source: `Breakdown.AdjointDefect.RemainderPlainHolds` (`Breakdown/CellReduction/AdjointStatements.lean:59`).

Supplied by `Breakdown.AdjointDefect.remainderPlainHolds_proof` (`lean/Breakdown/CellReduction/AdjointRemainderPlain.lean:41`).

**Interface definition: Azimuthal remainder dual bound.** This proposition requires that the azimuthal remainder bound implies the remainder dual estimate. Source: `Breakdown.AdjointDefect.RemainderAzimuthalHolds` (`Breakdown/CellReduction/AdjointStatements.lean:62`).

Supplied by `Breakdown.AdjointDefect.AzimuthalParts.remainderAzimuthalHolds_of` (`lean/Breakdown/CellReduction/AdjointRemainderAzimuthal.lean:101`); `Breakdown.AdjointDefect.remainderAzimuthalHolds_proof` (`lean/Breakdown/CellReduction/AdjointRemainderAzimuthal.lean:198`).

**Interface definition: Combine remainder dual estimates.** This proposition requires that the stored dual decomposition yields the remainder dual estimate. Source: `Breakdown.AdjointDefect.DualBoundedBoundHolds` (`Breakdown/CellReduction/AdjointStatements.lean:65`).

Supplied by `Breakdown.AdjointDefect.dualBoundedBound_of_parts` (`lean/Breakdown/CellReduction/AdjointDualBounded.lean:12`).

**Interface definition: Bound the pin correction.** This proposition requires that the pin correction pairing is bounded by the potential error and rounded matrix error times the square root of weighted energy. Source: `Breakdown.AdjointDefect.PinChargeHolds` (`Breakdown/CellReduction/AdjointStatements.lean:68`).

Supplied by `Breakdown.AdjointDefect.pinChargeHolds_proof` (`lean/Breakdown/CellReduction/AdjointPinCharge.lean:392`).

**Interface definition: Bound the free parameter shift.** This proposition requires that the free-shift pairing is bounded by the weighted parameter size times the two recorded adjoint error budgets and gradient norm. Source: `Breakdown.AdjointDefect.FreeShiftBoundHolds` (`Breakdown/CellReduction/AdjointStatements.lean:84`).

Supplied by `Breakdown.AdjointDefect.freeShiftBoundHolds_proof` (`lean/Breakdown/CellReduction/AdjointFreeShift.lean:312`).

**Definition: Identify the adjoint decomposition.** This proposition requires that the certificate's adjoints, coupling coefficients, profile pieces and reciprocal period agree with the listed residual data. Source: `Breakdown.AdjointDefect.AdjointDefectStructure` (`Breakdown/CellReduction/AdjointStatements.lean:97`).

**Definition: Regularity of the potential entries.** This proposition requires that the centre and fitted potentials and the pin data satisfy their analytic classes with common bounds. Source: `Breakdown.AdjointDefect.AdjointPotentialFacts` (`Breakdown/CellReduction/AdjointStatements.lean:109`).

### Breakdown.CellReduction.AdjointTestDensityCutoff

A curl-potential correction keeps the spatially truncated adjoint field divergence-free while controlling its derivatives.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: Spatial slice of a joint derivative.** The derivative on a fixed time slice is the joint derivative restricted to the spatial direction. Source: `Breakdown.AdjointDefect.Internal.TestDensity.slice_hasSpaceDeriv` (`Breakdown/CellReduction/AdjointTestDensityCutoff.lean:21`).

**Theorem: Time derivative from the joint map.** Differentiation in time is the joint derivative applied to the unit time direction. Source: `Breakdown.AdjointDefect.Internal.TestDensity.time_hasDerivAt` (`Breakdown/CellReduction/AdjointTestDensityCutoff.lean:30`).

**Theorem: Differentiate the time slice.** The time slice has derivative equal to the field's declared time derivative. Source: `Breakdown.AdjointDefect.Internal.TestDensity.time_hasDerivAt'` (`Breakdown/CellReduction/AdjointTestDensityCutoff.lean:40`).

**Theorem: The spatial derivative is continuous.** The spatial derivative of the joint continuously differentiable field is continuous in time and space. Source: `Breakdown.AdjointDefect.Internal.TestDensity.slice_spaceDeriv_continuous` (`Breakdown/CellReduction/AdjointTestDensityCutoff.lean:44`).

**Theorem: The time derivative is continuous.** The time derivative of the jointly continuously differentiable field is continuous in time and space. Source: `Breakdown.AdjointDefect.Internal.TestDensity.time_deriv_continuous` (`Breakdown/CellReduction/AdjointTestDensityCutoff.lean:53`).

**Theorem: The mollifier lies in the unit ball.** Every point where the mollifier kernel is nonzero has norm less than one. Source: `Breakdown.AdjointDefect.Internal.TestDensity.kernel_ne_norm_lt` (`Breakdown/CellReduction/AdjointTestDensityCutoff.lean:62`).

**Theorem: A normalized kernel preserves a bound.** Averaging a field bounded by B against the nonnegative normalized kernel gives a vector of norm at most B. Source: `Breakdown.AdjointDefect.Internal.TestDensity.kernel_integral_norm_le` (`Breakdown/CellReduction/AdjointTestDensityCutoff.lean:72`).

**Theorem: Differentiate under mollification.** The time derivative of the smoothed field is the convolution of the kernel with the original time derivative. Source: `Breakdown.AdjointDefect.Internal.TestDensity.smoothed_time_hasDerivAt` (`Breakdown/CellReduction/AdjointTestDensityCutoff.lean:83`).

**Theorem: Differentiate under mollification.** The time derivative of the smoothed field is the convolution of the kernel with the original time derivative. Source: `Breakdown.AdjointDefect.Internal.TestDensity.smoothed_timeDerivative` (`Breakdown/CellReduction/AdjointTestDensityCutoff.lean:109`).

**Theorem: Uniform convergence of mollification.** For every positive tolerance, the mollified field eventually differs from the original field by at most that tolerance uniformly in spacetime. Source: `Breakdown.AdjointDefect.Internal.TestDensity.kernel_uniform` (`Breakdown/CellReduction/AdjointTestDensityCutoff.lean:115`).

**Theorem: A higher decay exponent gives less.** For the stated nonnegative numerator and base at least one, increasing the denominator exponent decreases the quotient. Source: `Breakdown.AdjointDefect.Internal.TestDensity.frac_antitone` (`Breakdown/CellReduction/AdjointTestDensityCutoff.lean:129`).

**Theorem: Multiply two power-decay factors.** Multiplying the two quotients multiplies their numerators and adds the denominator exponents. Source: `Breakdown.AdjointDefect.Internal.TestDensity.frac_mul` (`Breakdown/CellReduction/AdjointTestDensityCutoff.lean:132`).

**Theorem: Shift a radial decay bound locally.** Shifting by a vector of norm less than one increases the radial decay bound by at most the factor two to the decay exponent. Source: `Breakdown.AdjointDefect.Internal.TestDensity.frac_shift` (`Breakdown/CellReduction/AdjointTestDensityCutoff.lean:138`).

**Definition: Cross product with a gradient.** The bounded bilinear map forms the coordinate cross product of a scalar derivative and a vector. Source: `Breakdown.AdjointDefect.Internal.TestDensity.crossGrad` (`Breakdown/CellReduction/AdjointTestDensityCutoff.lean:156`).

**Theorem: Coordinates of gradient cross product.** The gradient cross product has the three antisymmetric coordinate differences of the scalar derivative and vector. Source: `Breakdown.AdjointDefect.Internal.TestDensity.crossGrad_comp` (`Breakdown/CellReduction/AdjointTestDensityCutoff.lean:170`).

**Theorem: Differentiate a locally zero function.** A function that is zero throughout a neighbourhood has zero derivative at its centre. Source: `Breakdown.AdjointDefect.Internal.TestDensity.eq_zero_of_eventually` (`Breakdown/CellReduction/AdjointTestDensityCutoff.lean:176`).

**Theorem: The bump derivatives vanish far away.** Outside the round bump's support, the specified first or second derivative is zero. Source: `Breakdown.AdjointDefect.Internal.TestDensity.round_spaceDeriv_far` (`Breakdown/CellReduction/AdjointTestDensityCutoff.lean:181`).

**Theorem: The bump derivatives vanish far away.** Outside the round bump's support, the specified first or second derivative is zero. Source: `Breakdown.AdjointDefect.Internal.TestDensity.round_spaceDeriv2_far` (`Breakdown/CellReduction/AdjointTestDensityCutoff.lean:186`).

**Theorem: The inner bump derivative vanishes.** In the constant inner region of the round bump, its first derivative is zero. Source: `Breakdown.AdjointDefect.Internal.TestDensity.round_spaceDeriv_near` (`Breakdown/CellReduction/AdjointTestDensityCutoff.lean:193`).

**Theorem: The round bump has two derivatives.** The round bump is twice continuously differentiable. Source: `Breakdown.AdjointDefect.Internal.TestDensity.round_two` (`Breakdown/CellReduction/AdjointTestDensityCutoff.lean:198`).

**Theorem: Bound both round-bump derivatives.** One nonnegative constant bounds the first and second derivatives of the round bump everywhere. Source: `Breakdown.AdjointDefect.Internal.TestDensity.round_bounds` (`Breakdown/CellReduction/AdjointTestDensityCutoff.lean:200`).

**Theorem: Rescaling costs one inverse radius.** The derivative of the radius-R cutoff is one over R times the derivative of the unit bump evaluated at y divided by R. Source: `Breakdown.AdjointDefect.Internal.TestDensity.cut_hasSpaceDeriv` (`Breakdown/CellReduction/AdjointTestDensityCutoff.lean:209`).

**Theorem: Rescaling costs one inverse radius.** The derivative of the radius-R cutoff is one over R times the derivative of the unit bump evaluated at y divided by R. Source: `Breakdown.AdjointDefect.Internal.TestDensity.cut_spaceDeriv` (`Breakdown/CellReduction/AdjointTestDensityCutoff.lean:218`).

**Theorem: The Hessian costs two inverse radii.** The second derivative of the radius-R cutoff is one over R squared times the unit bump's second derivative at y divided by R. Source: `Breakdown.AdjointDefect.Internal.TestDensity.cut_spaceDeriv2` (`Breakdown/CellReduction/AdjointTestDensityCutoff.lean:221`).

**Theorem: The scaled bump has two derivatives.** The scaled bump is twice continuously differentiable. Source: `Breakdown.AdjointDefect.Internal.TestDensity.cut_two` (`Breakdown/CellReduction/AdjointTestDensityCutoff.lean:232`).

**Theorem: Smoothness implies C1 regularity.** The smooth function is continuously differentiable. Source: `Breakdown.AdjointDefect.Internal.TestDensity.smooth_one` (`Breakdown/CellReduction/AdjointTestDensityCutoff.lean:234`).

**Definition: Solenoidal spatial truncation.** The truncation adds the gradient-cutoff cross potential to the truncated adjoint field and applies the time cutoff. Source: `Breakdown.AdjointDefect.Internal.TestDensity.trunc` (`Breakdown/CellReduction/AdjointTestDensityCutoff.lean:238`).

**Theorem: Corrected truncation is differentiable.** The time-weighted cutoff field with its curl correction is jointly continuously differentiable. Source: `Breakdown.AdjointDefect.Internal.TestDensity.trunc_contDiff` (`Breakdown/CellReduction/AdjointTestDensityCutoff.lean:243`).

**Theorem: Differentiate the corrected truncation.** The truncation derivative is the time weight times the product-rule derivatives of the cutoff field and the cutoff-gradient cross potential. Source: `Breakdown.AdjointDefect.Internal.TestDensity.trunc_hasSpaceDeriv` (`Breakdown/CellReduction/AdjointTestDensityCutoff.lean:253`).

**Theorem: The corrected truncation is solenoidal.** The cutoff field together with its potential correction has zero spatial divergence. Source: `Breakdown.AdjointDefect.Internal.TestDensity.trunc_divergence` (`Breakdown/CellReduction/AdjointTestDensityCutoff.lean:267`).

**Theorem: The spatial cutoff has size at most one.** The absolute scaled bump is at most one. Source: `Breakdown.AdjointDefect.Internal.TestDensity.cut_abs` (`Breakdown/CellReduction/AdjointTestDensityCutoff.lean:291`).

**Theorem: Positive rescaling divides the norm.** Scaling a vector by the reciprocal of a positive radius divides its norm by that radius. Source: `Breakdown.AdjointDefect.Internal.TestDensity.norm_inv_smul` (`Breakdown/CellReduction/AdjointTestDensityCutoff.lean:296`).

**Theorem: Cutoff derivative vanishes off its ring.** The cutoff derivative is zero in the stated constant inner or outer region. Source: `Breakdown.AdjointDefect.Internal.TestDensity.cut_spaceDeriv_near` (`Breakdown/CellReduction/AdjointTestDensityCutoff.lean:299`).

**Theorem: Cutoff derivative vanishes off its ring.** The cutoff derivative is zero in the stated constant inner or outer region. Source: `Breakdown.AdjointDefect.Internal.TestDensity.cut_spaceDeriv_far` (`Breakdown/CellReduction/AdjointTestDensityCutoff.lean:306`).

**Theorem: First cutoff derivative decays inversely.** The first cutoff derivative has norm at most 3c divided by one plus radius. Source: `Breakdown.AdjointDefect.Internal.TestDensity.cut_bound1` (`Breakdown/CellReduction/AdjointTestDensityCutoff.lean:313`).

**Theorem: Quadratic decay of the cutoff Hessian.** The second cutoff derivative has norm at most 9c divided by the square of one plus radius. Source: `Breakdown.AdjointDefect.Internal.TestDensity.cut_bound2` (`Breakdown/CellReduction/AdjointTestDensityCutoff.lean:330`).

**Theorem: Truncation agrees in the inner region.** Near the stated inner point, the corrected truncation equals the time-cut target field. Source: `Breakdown.AdjointDefect.Internal.TestDensity.trunc_near` (`Breakdown/CellReduction/AdjointTestDensityCutoff.lean:348`).

**Theorem: Truncation vanishes outside its support.** Beyond the spatial cutoff, the specified truncation or its spatial derivative is zero. Source: `Breakdown.AdjointDefect.Internal.TestDensity.trunc_far` (`Breakdown/CellReduction/AdjointTestDensityCutoff.lean:355`).

**Theorem: Truncation vanishes outside its support.** Beyond the spatial cutoff, the specified truncation or its spatial derivative is zero. Source: `Breakdown.AdjointDefect.Internal.TestDensity.trunc_far_spaceDeriv` (`Breakdown/CellReduction/AdjointTestDensityCutoff.lean:360`).

**Theorem: The curl correction preserves decay.** The cutoff field plus its gradient-cross-potential correction obeys the original decay order with the stated enlarged coefficient. Source: `Breakdown.AdjointDefect.Internal.TestDensity.core_bound` (`Breakdown/CellReduction/AdjointTestDensityCutoff.lean:368`).

**Theorem: The corrected gradient gains one power.** The product-rule gradient of the corrected cutoff field decays one power faster than the field itself. Source: `Breakdown.AdjointDefect.Internal.TestDensity.grad_core_bound` (`Breakdown/CellReduction/AdjointTestDensityCutoff.lean:389`).

**Theorem: The field decay constant is nonnegative.** The admissibility assumptions force the stated field decay constant to be nonnegative. Source: `Breakdown.AdjointDefect.Internal.TestDensity.field_C_nonneg` (`Breakdown/CellReduction/AdjointTestDensityCutoff.lean:441`).

**Theorem: Decay of the truncated field.** The corrected truncation has the original spatial decay multiplied by the absolute time weight and an enlarged constant. Source: `Breakdown.AdjointDefect.Internal.TestDensity.trunc_bound` (`Breakdown/CellReduction/AdjointTestDensityCutoff.lean:446`).

**Theorem: Decay of the truncated gradient.** The corrected truncation's spatial derivative decays one power faster, multiplied by the absolute time weight. Source: `Breakdown.AdjointDefect.Internal.TestDensity.trunc_grad_bound` (`Breakdown/CellReduction/AdjointTestDensityCutoff.lean:456`).

**Theorem: Time product rule for the truncation.** The time derivative differentiates both the time weight and the field and potential inside the spatial correction. Source: `Breakdown.AdjointDefect.Internal.TestDensity.trunc_time_hasDerivAt` (`Breakdown/CellReduction/AdjointTestDensityCutoff.lean:467`).

**Theorem: Decay of the truncation time derivative.** The time derivative has the original spatial decay multiplied by the sum of the absolute time weight and its derivative. Source: `Breakdown.AdjointDefect.Internal.TestDensity.trunc_time_bound` (`Breakdown/CellReduction/AdjointTestDensityCutoff.lean:477`).

### Breakdown.CellReduction.AdjointTestDensityLimits

The cutoff and smoothing errors converge in the square and mixed norms required by the weak testing argument.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: A radial decay weight has finite size.** The prescribed exponent makes the nonnegative integral of the radial decay weight finite. Source: `Breakdown.AdjointDefect.Internal.TestDensity.weight_lintegral_finite` (`Breakdown/CellReduction/AdjointTestDensityLimits.lean:24`).

**Theorem: Outside the symmetric time interval.** A point outside the specified symmetric closed interval has absolute value greater than its endpoint. Source: `Breakdown.AdjointDefect.Internal.TestDensity.not_mem_Icc_abs` (`Breakdown/CellReduction/AdjointTestDensityLimits.lean:36`).

**Theorem: The approximation error vanishes in L2.** The spacetime square integral of the error tends to zero under the convergence and decay assumptions. Source: `Breakdown.AdjointDefect.Internal.TestDensity.sq_lintegral_tendsto` (`Breakdown/CellReduction/AdjointTestDensityLimits.lean:40`).

**Theorem: The dual mixed error tends to zero.** The time-L2 space-L6/5 error norm tends to zero under the convergence and decay assumptions. Source: `Breakdown.AdjointDefect.Internal.TestDensity.mixed_tendsto` (`Breakdown/CellReduction/AdjointTestDensityLimits.lean:74`).

**Theorem: Time cutoff preserves differentiability.** The time-cut field is jointly continuously differentiable. Source: `Breakdown.AdjointDefect.Internal.TestDensity.cutoff_contDiff` (`Breakdown/CellReduction/AdjointTestDensityLimits.lean:125`).

**Theorem: Time cutoffs scale space derivatives.** The time weight multiplies the spatial derivative without an additional spatial product term. Source: `Breakdown.AdjointDefect.Internal.TestDensity.cutoff_spaceDeriv` (`Breakdown/CellReduction/AdjointTestDensityLimits.lean:129`).

**Theorem: The time-cutoff product rule.** The cutoff time derivative is the time weight times the field derivative plus the weight derivative times the field. Source: `Breakdown.AdjointDefect.Internal.TestDensity.cutoff_time` (`Breakdown/CellReduction/AdjointTestDensityLimits.lean:133`).

**Theorem: Enlarge a radial decay bound.** Increasing the coefficient and decreasing the decay exponent gives a larger radial upper bound. Source: `Breakdown.AdjointDefect.Internal.TestDensity.weight_le_of_le` (`Breakdown/CellReduction/AdjointTestDensityLimits.lean:138`).

**Theorem: Cutoff and derivative vanish together.** A compactly supported smooth time cutoff and its derivative both vanish outside some symmetric bounded interval. Source: `Breakdown.AdjointDefect.Internal.TestDensity.cutoff_support` (`Breakdown/CellReduction/AdjointTestDensityLimits.lean:143`).

**Theorem: Vanishing outside a box gives support.** Vanishing outside the stated bounded region gives compact support. Source: `Breakdown.AdjointDefect.Internal.TestDensity.box_support` (`Breakdown/CellReduction/AdjointTestDensityLimits.lean:157`).

**Theorem: Mollification preserves radial decay.** The smoothed field retains q-order decay with coefficient at most P times two to the q times K. Source: `Breakdown.AdjointDefect.Internal.TestDensity.sm_bound` (`Breakdown/CellReduction/AdjointTestDensityLimits.lean:166`).

**Theorem: Time support after mollification.** The mollified field is zero at the stated time outside the enlarged support interval. Source: `Breakdown.AdjointDefect.Internal.TestDensity.sm_zero` (`Breakdown/CellReduction/AdjointTestDensityLimits.lean:176`).

**Theorem: Column squares versus operator norm.** The matrix column-square sum is at most three times the squared operator norm. Source: `Breakdown.AdjointDefect.Internal.TestDensity.columnSq_le` (`Breakdown/CellReduction/AdjointTestDensityLimits.lean:188`).

**Theorem: The truncation vanishes off time support.** When both the time cutoff and its derivative vanish, the specified truncated field or derivative is zero. Source: `Breakdown.AdjointDefect.Internal.TestDensity.trunc_zero0` (`Breakdown/CellReduction/AdjointTestDensityLimits.lean:199`).

**Theorem: The truncation vanishes off time support.** When both the time cutoff and its derivative vanish, the specified truncated field or derivative is zero. Source: `Breakdown.AdjointDefect.Internal.TestDensity.trunc_zero1` (`Breakdown/CellReduction/AdjointTestDensityLimits.lean:205`).

**Theorem: The truncation vanishes off time support.** When both the time cutoff and its derivative vanish, the specified truncated field or derivative is zero. Source: `Breakdown.AdjointDefect.Internal.TestDensity.trunc_zero2` (`Breakdown/CellReduction/AdjointTestDensityLimits.lean:215`).

**Theorem: A decay bound gives a uniform bound.** The bounded prefactor and nonnegative decay give the uniform upper bound PK. Source: `Breakdown.AdjointDefect.Internal.TestDensity.glob_le` (`Breakdown/CellReduction/AdjointTestDensityLimits.lean:227`).

**Theorem: A derivative applied to radius decays.** The operator decay bound with one additional power gives q-order decay after application to the position vector. Source: `Breakdown.AdjointDefect.Internal.TestDensity.radial_le` (`Breakdown/CellReduction/AdjointTestDensityLimits.lean:232`).

### Breakdown.CellReduction.CellLayerBreakdown

The profile-minus-model difference is split into a centre shift and a parameter shift, with separate numerical bounds.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Definition: Centre and parameter shift fields.** The two fields are the zero-parameter profile minus the model and the selected profile minus the zero-parameter profile. Source: `Breakdown.CellLayerSystem.shiftPieceFields` (`Breakdown/CellReduction/CellLayerBreakdown.lean:19`).

**Definition: The two shift error budgets.** The two shift fields are packaged with their derivatives, separate supremum and gradient bounds, and distinct square or cubic norm choices. Source: `Breakdown.CellLayerSystem.shiftPiecesOfSystem` (`Breakdown/CellReduction/CellLayerBreakdown.lean:23`).

### Breakdown.CellReduction.CellLayerBreakdownCompose

The analytic bridges assemble the cell data into the extended certificate while preserving the supplied field identifications.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: Standing assumptions for reduction.** Under the stated hypotheses, the weight is positive and constant and the model, profile and adjoints satisfy the regularity and decay required by the analytic bridges. Source: `Breakdown.CellLayerSystem.bridgeStanding_of_parts` (`Breakdown/CellReduction/CellLayerBreakdownCompose.lean:40`).

**Theorem: Change the unused Hessian choice.** Replacing the stored given Hessian preserves the instantiated profile, pressure and adjoint condition. Source: `Breakdown.CellLayerSystem.instantiationBounded_with_givenHess` (`Breakdown/CellReduction/CellLayerBreakdownCompose.lean:159`).

**Theorem: The offset ignores this Hessian choice.** Replacing the stored given Hessian preserves the offset-expansion entry condition. Source: `Breakdown.CellLayerSystem.offsetExpansion_with_givenHess` (`Breakdown/CellReduction/CellLayerBreakdownCompose.lean:165`).

### Breakdown.CellReduction.ConvectionIdentity

Approximation extends the smooth convection identity to the weak profile class used by the frozen form.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: Cauchy inequality for embedded products.** The nonnegative integral of a real product is bounded by the product of the two square-integral roots. Source: `Breakdown.CertReduction.Internal.lintegral_ofReal_mul_le` (`Breakdown/CellReduction/ConvectionIdentity.lean:15`).

**Theorem: Square control makes the product finite.** Finite square integrals imply a finite nonnegative integral of the product. Source: `Breakdown.CertReduction.Internal.lintegral_ofReal_mul_lt_top` (`Breakdown/CellReduction/ConvectionIdentity.lean:33`).

**Theorem: A small square factor kills the product.** The square-norm convergence assumptions imply that the nonnegative product integral tends to zero. Source: `Breakdown.CertReduction.Internal.tendsto_lintegral_ofReal_mul` (`Breakdown/CellReduction/ConvectionIdentity.lean:41`).

**Theorem: Zero-limit sequence is eventually small.** A nonnegative sequence tending to zero is eventually at most one. Source: `Breakdown.CertReduction.Internal.eventually_lintegral_le_one` (`Breakdown/CellReduction/ConvectionIdentity.lean:59`).

**Theorem: Small integral error gives convergence.** Vanishing nonnegative integral of the error implies convergence of the real integrals to the limiting integral. Source: `Breakdown.CertReduction.Internal.tendsto_integral_of_lintegral` (`Breakdown/CellReduction/ConvectionIdentity.lean:63`).

**Theorem: Integrable majorant gives integrability.** The measurable integrand is integrable when bounded in norm by the prescribed integrable majorant. Source: `Breakdown.CertReduction.Internal.integrable_of_bound` (`Breakdown/CellReduction/ConvectionIdentity.lean:77`).

**Theorem: Embed a three-term error estimate.** The three-term real norm bound gives the corresponding sum bound in nonnegative extended reals. Source: `Breakdown.CertReduction.Internal.enorm_le_three` (`Breakdown/CellReduction/ConvectionIdentity.lean:93`).

**Theorem: Three vanishing errors still vanish.** The integral of a fixed nonnegative multiple of the sum of three vanishing error terms tends to zero. Source: `Breakdown.CertReduction.Internal.tendsto_lintegral_three` (`Breakdown/CellReduction/ConvectionIdentity.lean:103`).

**Theorem: Split the convection approximation error.** The convection pairing difference is bounded by three products: both derivative errors, gradient error with the limiting Laplacian, and Laplacian error with the limiting gradient. Source: `Breakdown.CertReduction.Internal.convection_diff_bound` (`Breakdown/CellReduction/ConvectionIdentity.lean:132`).

**Theorem: Split the quadratic strain error.** The strain difference is bounded by 3C times the squared gradient error plus twice its product with the limiting gradient norm. Source: `Breakdown.CertReduction.Internal.strain_diff_bound` (`Breakdown/CellReduction/ConvectionIdentity.lean:159`).

**Theorem: Measurability of operator evaluation.** Applying a measurable operator field to a measurable vector field is strongly measurable almost everywhere. Source: `Breakdown.CertReduction.Internal.aestronglyMeasurable_apply` (`Breakdown/CellReduction/ConvectionIdentity.lean:212`).

**Theorem: The convection pairing is measurable.** The convection integrand formed from the measurable fields is strongly measurable almost everywhere. Source: `Breakdown.CertReduction.Internal.aestronglyMeasurable_pairing` (`Breakdown/CellReduction/ConvectionIdentity.lean:217`).

**Theorem: The strain integrand is measurable.** The finite coordinate sum defining the strain integrand is strongly measurable almost everywhere. Source: `Breakdown.CertReduction.Internal.aestronglyMeasurable_strain` (`Breakdown/CellReduction/ConvectionIdentity.lean:223`).

**Theorem: Convection equals the strain pairing.** Under the stated hypotheses, under the divergence and regularity hypotheses, convection against the negative Laplacian equals the gradient's strain pairing. Source: `Breakdown.CertReduction.convectionIdentityHolds_of` (`Breakdown/CellReduction/ConvectionIdentity.lean:248`).

**Theorem: Convection equals the strain pairing.** Under the stated hypotheses, under the divergence and regularity hypotheses, convection against the negative Laplacian equals the gradient's strain pairing. Source: `Breakdown.CertReduction.convectionIdentityHolds_of_approx` (`Breakdown/CellReduction/ConvectionIdentity.lean:354`).

### Breakdown.CellReduction.ConvectionSmooth

Integration by parts rewrites convection against the negative Laplacian as the strain pairing of the gradient.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: The derivative vanishes off the support.** Outside the stated support region, the field is locally zero and its derivative vanishes. Source: `Breakdown.CertReduction.Internal.ConvectionSmooth.fderiv_eq_zero_off` (`Breakdown/CellReduction/ConvectionSmooth.lean:14`).

**Theorem: Bounded compact integrand is integrable.** The stated boundedness and vanishing assumptions make the integrand integrable. Source: `Breakdown.CertReduction.Internal.ConvectionSmooth.integrable_off` (`Breakdown/CellReduction/ConvectionSmooth.lean:22`).

**Theorem: A compact derivative integrates to zero.** The integral of a directional derivative of the compactly supported smooth scalar function is zero. Source: `Breakdown.CertReduction.Internal.ConvectionSmooth.integral_fderiv_eq_zero` (`Breakdown/CellReduction/ConvectionSmooth.lean:26`).

**Theorem: Reconstruct a vector from coordinates.** Every vector is the sum of its coordinates times the coordinate unit vectors. Source: `Breakdown.CertReduction.Internal.ConvectionSmooth.expand` (`Breakdown/CellReduction/ConvectionSmooth.lean:43`).

**Theorem: Resolve an inner product by coordinates.** The sum of the coordinate products in the standard orthonormal basis equals the vector inner product. Source: `Breakdown.CertReduction.Internal.ConvectionSmooth.sum_inner_mul_inner` (`Breakdown/CellReduction/ConvectionSmooth.lean:47`).

**Theorem: Rewrite the strain with adjoint columns.** The sum of pairings of AB applied to basis vectors with A applied to basis vectors equals the quadratic pairing of B with the adjoint columns of A. Source: `Breakdown.CertReduction.Internal.ConvectionSmooth.pair_sum` (`Breakdown/CellReduction/ConvectionSmooth.lean:52`).

**Theorem: Expand a second derivative direction.** The coordinate-weighted sum of second-derivative pairings equals the second derivative applied directly to that vector direction. Source: `Breakdown.CertReduction.Internal.ConvectionSmooth.second_expand` (`Breakdown/CellReduction/ConvectionSmooth.lean:76`).

**Theorem: Convection equals the strain integral.** For the stated smooth divergence-free data, the pairing of the directional derivative of u with minus its Laplacian equals the quadratic strain integral formed from the derivative of W and adjoint-gradient columns of u. Source: `Breakdown.CertReduction.Internal.ConvectionSmooth.identity` (`Breakdown/CellReduction/ConvectionSmooth.lean:83`).

**Theorem: Convection equals the strain integral.** For the stated smooth divergence-free data, the pairing of the directional derivative of u with minus its Laplacian equals the quadratic strain integral formed from the derivative of W and adjoint-gradient columns of u. Source: `Breakdown.CertReduction.convectionIdentitySmooth` (`Breakdown/CellReduction/ConvectionSmooth.lean:202`).

### Breakdown.CellReduction.CubicWeightProduct

A Sobolev product estimate controls a weighted square of the velocity by a cubic weight norm and gradient energy.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: The matrix square norm is continuous.** The sum of the squared matrix-column norms depends continuously on the matrix. Source: `Breakdown.CertReduction.Internal.columnSquareSum_continuous` (`Breakdown/CellReduction/CubicWeightProduct.lean:15`).

**Theorem: Matrix square norm is nonnegative.** The sum of the squared matrix-column norms is nonnegative. Source: `Breakdown.CertReduction.Internal.columnSquareSum_nonneg` (`Breakdown/CellReduction/CubicWeightProduct.lean:20`).

**Theorem: A squared base to the three-halves.** The three-halves power of a real square equals the cube of its absolute value. Source: `Breakdown.CertReduction.Internal.sq_rpow_three_halves` (`Breakdown/CellReduction/CubicWeightProduct.lean:24`).

**Theorem: A squared base cubed is sixth power.** The real third power of a square equals the original number to the sixth power. Source: `Breakdown.CertReduction.Internal.sq_rpow_three` (`Breakdown/CellReduction/CubicWeightProduct.lean:29`).

**Theorem: The cubic-weight Sobolev estimate.** The weighted velocity square integral is bounded by four thirds times the cubic weight norm to the two-thirds power times gradient energy. Source: `Breakdown.CertReduction.cubicWeightProductHolds` (`Breakdown/CellReduction/CubicWeightProduct.lean:35`).

### Breakdown.CellReduction.EnergyBounds

The slice supremum estimate and the weighted energy combine into the bounds consumed by the reduction bridges.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: Square the supremum-energy constant.** The squared supremum-bound factor is one divided by four pi times the square root of the positive energy weight. Source: `Breakdown.CertReduction.Internal.scaleFactor_sq_eq` (`Breakdown/CellReduction/EnergyBounds.lean:14`).

**Theorem: Matrix square norm is nonnegative.** The sum of the squared matrix-column norms is nonnegative. Source: `Breakdown.CertReduction.Internal.columnSquareSum_nonneg'` (`Breakdown/CellReduction/EnergyBounds.lean:36`).

**Theorem: Slice values are bounded by energy.** Under the stated hypotheses, the slice value squared is bounded almost everywhere by the stated coefficient times its gradient–Laplacian energy. Source: `Breakdown.CertReduction.sliceEnergySup_of` (`Breakdown/CellReduction/EnergyBounds.lean:41`).

**Theorem: Profile values are bounded by energy.** Under the stated hypotheses, the stationary weak-profile value squared is bounded almost everywhere by the stated coefficient times stationary energy. Source: `Breakdown.CertReduction.profileEnergySup_of` (`Breakdown/CellReduction/EnergyBounds.lean:51`).

**Theorem: Energy controls the period gradient.** The constant energy weight times the period gradient square integral is bounded by total weighted energy. Source: `Breakdown.CertReduction.periodGradientEnergy` (`Breakdown/CellReduction/EnergyBounds.lean:61`).

**Theorem: The profile energy estimates.** Under the stated hypotheses, the required slice, stationary and period gradient estimates hold. Source: `Breakdown.CertReduction.energyBounds_of` (`Breakdown/CellReduction/EnergyBounds.lean:81`).

### Breakdown.CellReduction.FormShiftBridge

The form-shift argument checks the sign and measurability prerequisites for transferring the frozen form.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: The shift coefficient is nonnegative.** The gradient-shift coefficient is nonnegative under the prescribed weight assumption. Source: `Breakdown.CertReduction.Internal.formShift_gradCoeff_nonneg` (`Breakdown/CellReduction/FormShiftBridge.lean:14`).

**Theorem: The weak Laplacian is measurable.** Taking the second-derivative trace preserves almost-everywhere strong measurability. Source: `Breakdown.CertReduction.Internal.formShift_trace_measurable` (`Breakdown/CellReduction/FormShiftBridge.lean:18`).

**Theorem: The shift-product norm is measurable.** The nonnegative product of the applied-matrix norm and trace norm is measurable almost everywhere. Source: `Breakdown.CertReduction.Internal.formShift_product_measurable` (`Breakdown/CellReduction/FormShiftBridge.lean:29`).

### Breakdown.CellReduction.FrozenFormBridge

Positivity of the stationary energy and shift coefficient supports the lower bound for the frozen model form.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: Matrix square norm is nonnegative.** The sum of the squared matrix-column norms is nonnegative. Source: `Breakdown.CertReduction.Internal.columnSquares_nonneg` (`Breakdown/CellReduction/FrozenFormBridge.lean:14`).

**Theorem: Constant-weight energy is nonnegative.** The stationary gradient-plus-Laplacian energy is nonnegative for nonnegative constant weight. Source: `Breakdown.CertReduction.Internal.stationaryEnergy_const_nonneg` (`Breakdown/CellReduction/FrozenFormBridge.lean:18`).

**Theorem: Cubic shift coefficient is nonnegative.** The cubic gradient-shift coefficient is nonnegative under the stated weight assumption. Source: `Breakdown.CertReduction.Internal.shiftGradCoeff_cubic_nonneg` (`Breakdown/CellReduction/FrozenFormBridge.lean:25`).

### Breakdown.CellReduction.FrozenIntegrand

The two frozen convection integrands are integrable under the profile regularity and decay assumptions.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: Bound the first frozen product.** The first frozen convection product is bounded by a multiple of the gradient term plus the Laplacian square. Source: `Breakdown.CertReduction.Internal.frozen_first_pointwise` (`Breakdown/CellReduction/FrozenIntegrand.lean:14`).

**Theorem: Bound the second frozen product.** The second frozen convection product is bounded by a cubic coefficient term, a sixth-power velocity term and a Laplacian square. Source: `Breakdown.CertReduction.Internal.frozen_second_pointwise` (`Breakdown/CellReduction/FrozenIntegrand.lean:25`).

**Theorem: The Hessian trace is measurable.** The second-derivative trace of a measurable Hessian field is strongly measurable almost everywhere. Source: `Breakdown.CertReduction.Internal.trace_aestronglyMeasurable` (`Breakdown/CellReduction/FrozenIntegrand.lean:41`).

**Theorem: The matrix square norm is continuous.** The sum of the squared matrix-column norms depends continuously on the matrix. Source: `Breakdown.CertReduction.Internal.columnSquareSum_continuous` (`Breakdown/CellReduction/FrozenIntegrand.lean:52`).

**Theorem: Measurability of operator evaluation.** Applying a measurable operator field to a measurable vector field is strongly measurable almost everywhere. Source: `Breakdown.CertReduction.Internal.apply_aestronglyMeasurable` (`Breakdown/CellReduction/FrozenIntegrand.lean:56`).

**Theorem: Finite lower norm gives integrability.** The measurable real integrand is integrable when its nonnegative norm integral is finite. Source: `Breakdown.CertReduction.Internal.integrable_of_lintegral_lt` (`Breakdown/CellReduction/FrozenIntegrand.lean:61`).

**Theorem: Cubing inverse-square decay gives six.** The cube of the reciprocal square of one plus radius equals its negative sixth power. Source: `Breakdown.CertReduction.Internal.decay_cube` (`Breakdown/CellReduction/FrozenIntegrand.lean:65`).

**Theorem: The frozen convection is integrable.** Both frozen convection integrands are integrable for the stated decaying smooth model and weak profile. Source: `Breakdown.CertReduction.frozenIntegrand` (`Breakdown/CellReduction/FrozenIntegrand.lean:73`).

### Breakdown.CellReduction.GapGradTerm

The gradient part of the profile-to-model gap is controlled in the cubic or square-integrable case.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: The Laplacian trace is continuous.** Taking the trace of the second derivative is a continuous operation. Source: `Breakdown.CertReduction.traceSecond_continuous` (`Breakdown/CellReduction/GapGradTerm.lean:12`).

**Theorem: Matrix square norm is nonnegative.** The sum of the squared matrix-column norms is nonnegative. Source: `Breakdown.CertReduction.columnSquares_nonneg` (`Breakdown/CellReduction/GapGradTerm.lean:17`).

**Theorem: Compare real and lower integrals.** The nonnegative embedding of the real integral is bounded by the lower integral of the pointwise embeddings. Source: `Breakdown.CertReduction.ofReal_integral_le_lintegral` (`Breakdown/CellReduction/GapGradTerm.lean:20`).

**Theorem: Compare the two slice energies.** The embedded real gradient-plus-Laplacian energy is bounded by the lower integral of the combined energy density. Source: `Breakdown.CertReduction.ofReal_sliceEnergy_le` (`Breakdown/CellReduction/GapGradTerm.lean:27`).

**Theorem: The period energy is finite.** The field hypotheses give a finite period integral of Laplacian norm squared plus the weighted gradient column-square sum. Source: `Breakdown.CertReduction.periodEnergy_lt_top` (`Breakdown/CellReduction/GapGradTerm.lean:48`).

**Theorem: Square the operator norm inequality.** The squared norm of Au is at most the squared operator norm of A times the squared norm of u. Source: `Breakdown.CertReduction.norm_apply_sq_le` (`Breakdown/CellReduction/GapGradTerm.lean:74`).

**Theorem: Cancel the cubic gradient weight.** Squaring the cubic coefficient and multiplying by the positive weight gives four thirds times n squared. Source: `Breakdown.CertReduction.cubicCoeff_sq_mul` (`Breakdown/CellReduction/GapGradTerm.lean:80`).

**Theorem: The two-thirds power of a cube.** For a nonnegative real number, taking the two-thirds power of its cube gives its square in the nonnegative extended reals. Source: `Breakdown.CertReduction.cube_rpow_two_thirds` (`Breakdown/CellReduction/GapGradTerm.lean:90`).

**Theorem: Gradient part of the gap estimate.** Under the stated hypotheses, the selected L3 or L2 bound on the shift gradient controls its product with the perturbation velocity by weighted energy. Source: `Breakdown.CertReduction.gapGradTerm_of` (`Breakdown/CellReduction/GapGradTerm.lean:97`).

### Breakdown.CellReduction.GapSupTerm

A supremum bound on the profile shift controls its contribution to the period energy norm.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: The period measure lies below volume.** The product of unit-interval-restricted time measure and spatial volume is bounded by full spacetime volume. Source: `Breakdown.CertReduction.gapSup_window_le` (`Breakdown/CellReduction/GapSupTerm.lean:12`).

**Theorem: Product form of the period integral.** The nonnegative iterated period integral equals the integral against the product measure on the unit period. Source: `Breakdown.CertReduction.gapSup_period_eq_window` (`Breakdown/CellReduction/GapSupTerm.lean:23`).

**Theorem: The Laplacian trace is continuous.** Taking the trace of the second derivative is a continuous operation. Source: `Breakdown.CertReduction.gapSup_trace_continuous` (`Breakdown/CellReduction/GapSupTerm.lean:30`).

**Theorem: The matrix square norm is continuous.** The sum of the squared matrix-column norms depends continuously on the matrix. Source: `Breakdown.CertReduction.gapSup_columnSum_continuous` (`Breakdown/CellReduction/GapSupTerm.lean:35`).

**Theorem: Matrix square norm is nonnegative.** The sum of the squared matrix-column norms is nonnegative. Source: `Breakdown.CertReduction.gapSup_columnSum_nonneg` (`Breakdown/CellReduction/GapSupTerm.lean:40`).

**Theorem: The gap comparison has finite energy.** The field hypotheses make the weighted period gradient-plus-Laplacian energy finite. Source: `Breakdown.CertReduction.gapSup_energy_finite` (`Breakdown/CellReduction/GapSupTerm.lean:43`).

**Theorem: Supremum part of the gap estimate.** Under the stated hypotheses, a uniformly bounded shift controls the square integral of the perturbation gradient applied to it by weighted energy. Source: `Breakdown.CertReduction.gapSupTerm_of` (`Breakdown/CellReduction/GapSupTerm.lean:74`).

### Breakdown.CellReduction.GapTransferBridge

The separate gap contributions combine into one bound on the linearized profile-to-model difference.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: The applied matrix norm is measurable.** The norm of the measurable matrix field applied to the measurable vector field is measurable almost everywhere. Source: `Breakdown.CertReduction.Internal.applyNorm_aemeasurable` (`Breakdown/CellReduction/GapTransferBridge.lean:14`).

**Theorem: Gap-gradient coefficient is nonnegative.** The gap-gradient coefficient is nonnegative under the prescribed weight assumption. Source: `Breakdown.CertReduction.Internal.gapGradCoeff_nonneg` (`Breakdown/CellReduction/GapTransferBridge.lean:22`).

**Theorem: Combine the two gap-error bounds.** The period square integral of the sum of two errors is at most the square of the sum of their coefficients times the common energy. Source: `Breakdown.CertReduction.Internal.pairSum_le` (`Breakdown/CellReduction/GapTransferBridge.lean:26`).

### Breakdown.CellReduction.InstAdjointField

The stored adjoint shapes acquire their weak second derivatives, decay and curl-potential data.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: Convert an integer decay to real order.** The integer-power bound implies the prescribed real-power decay after enlarging the coefficient as stated. Source: `Breakdown.CellReduction.Instantiation.Internal.le_div_rpow_of_pow` (`Breakdown/CellReduction/InstAdjointField.lean:20`).

**Theorem: Weaken the real decay exponent.** The real-exponent decay bound implies the specified smaller integer-power decay bound. Source: `Breakdown.CellReduction.Instantiation.Internal.le_div_pow_of_le_exp` (`Breakdown/CellReduction/InstAdjointField.lean:25`).

**Theorem: Stored and classical Hessians agree.** The shape field's classical Hessian exists almost everywhere and agrees with its stored Hessian. Source: `Breakdown.CellReduction.Instantiation.secondDerivAgree_from_keys` (`Breakdown/CellReduction/InstAdjointField.lean:32`).

**Theorem: Shape data give adjoint regularity.** Under the stated hypotheses, a valid adjoint shape entry supplies the certificate's adjoint regularity and curl-potential facts. Source: `Breakdown.CellReduction.Instantiation.adjointField_holds_of` (`Breakdown/CellReduction/InstAdjointField.lean:36`).

### Breakdown.CellReduction.InstAdjointStructure

The identified profile and adjoint entries supply the structural relations required by the adjoint defect estimate.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: Identify the adjoint structure.** Under the stated hypotheses, the shape identifications and reciprocal-period expansion give the adjoint decomposition required by the residual estimate. Source: `Breakdown.CellReduction.Instantiation.adjointStructure_holds_of` (`Breakdown/CellReduction/InstAdjointStructure.lean:18`).

### Breakdown.CellReduction.InstAffineInvariant

The generators of the prescribed symmetries act correctly on every affine profile field.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: Iterate the half-period rotation law.** Iterating the basic rotation relation a times shifts time by a/2 and rotates both input and output by a times the angle. Source: `Breakdown.CellReduction.Instantiation.Internal.AffineInvariant.rotate_iterate_everywhere` (`Breakdown/CellReduction/InstAffineInvariant.lean:19`).

**Theorem: Combine rotation, reflection and periods.** The field respects the combined integer time shift, repeated half-period rotation and optional spatial reflection. Source: `Breakdown.CellReduction.Instantiation.Internal.AffineInvariant.turn_flip_shift` (`Breakdown/CellReduction/InstAffineInvariant.lean:39`).

**Theorem: Affine fields respect the symmetries.** The affine shape field transforms equivariantly under every symmetry generated by the cell class. Source: `Breakdown.CellReduction.Instantiation.affineFieldInvariant_holds` (`Breakdown/CellReduction/InstAffineInvariant.lean:56`).

### Breakdown.CellReduction.InstAffineStructure

Affine combinations of the shape fields preserve periodicity, divergence and the second-derivative data.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: The origin correction remains valid.** Replacing the origin correction by a valid origin profile preserves validity of the shape parameters. Source: `Breakdown.CellReduction.Instantiation.Internal.withOrigin_valid` (`Breakdown/CellReduction/InstAffineStructure.lean:17`).

**Definition: Matrix trace as a linear map.** The trace map sums the diagonal coordinate entries of a linear operator. Source: `Breakdown.CellReduction.Instantiation.Internal.traceOp` (`Breakdown/CellReduction/InstAffineStructure.lean:21`).

**Theorem: Read the matrix trace in coordinates.** The trace operator equals the sum of the three diagonal coordinate entries. Source: `Breakdown.CellReduction.Instantiation.Internal.traceOp_apply` (`Breakdown/CellReduction/InstAffineStructure.lean:24`).

**Theorem: Divergence is derivative trace.** When A is the derivative of the field, the field's divergence equals the trace of A. Source: `Breakdown.CellReduction.Instantiation.Internal.divergenceAt_eq_traceOp` (`Breakdown/CellReduction/InstAffineStructure.lean:28`).

**Theorem: Differentiate the spatial slice.** The spatial slice is differentiable with derivative given by its classical spatial derivative. Source: `Breakdown.CellReduction.Instantiation.Internal.slice_hasFDerivAt` (`Breakdown/CellReduction/InstAffineStructure.lean:32`).

**Theorem: Differentiate the affine profile.** The affine profile derivative is the centre-field derivative plus the coefficient-weighted sum of tangent-field derivatives. Source: `Breakdown.CellReduction.Instantiation.Internal.affineField_hasFDerivAt` (`Breakdown/CellReduction/InstAffineStructure.lean:39`).

**Theorem: Period and divergence of affine fields.** Valid affine shape data preserve time periodicity, zero divergence and measurable periodic Hessians. Source: `Breakdown.CellReduction.Instantiation.affineFieldStructure_holds` (`Breakdown/CellReduction/InstAffineStructure.lean:55`).

### Breakdown.CellReduction.InstAffineWeak

Weak gradients commute with finite affine combinations, so the stored affine Hessian is the required weak derivative.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: Weak gradients respect zero.** The zero vector field has the zero weak gradient. Source: `Breakdown.CellReduction.Instantiation.Internal.weakGradient_zero` (`Breakdown/CellReduction/InstAffineWeak.lean:19`).

**Theorem: Weak gradients respect addition.** The weak-gradient identity is preserved by addition. Source: `Breakdown.CellReduction.Instantiation.Internal.weakGradient_add` (`Breakdown/CellReduction/InstAffineWeak.lean:24`).

**Theorem: Scale a weak gradient identity.** The weak-gradient identity is preserved by scalar multiplication. Source: `Breakdown.CellReduction.Instantiation.Internal.weakGradient_smul` (`Breakdown/CellReduction/InstAffineWeak.lean:47`).

**Theorem: Weak gradients respect finite sums.** The weak-gradient identity is preserved by finite sums. Source: `Breakdown.CellReduction.Instantiation.Internal.weakGradient_sum` (`Breakdown/CellReduction/InstAffineWeak.lean:56`).

**Theorem: The spatial slice is differentiable.** Joint continuous differentiability gives differentiability of each spatial slice at the specified point. Source: `Breakdown.CellReduction.Instantiation.Internal.slice_differentiableAt` (`Breakdown/CellReduction/InstAffineWeak.lean:67`).

**Theorem: The shape field is differentiable.** The valid shape field is spatially differentiable at the specified point. Source: `Breakdown.CellReduction.Instantiation.Internal.shapeField_differentiableAt` (`Breakdown/CellReduction/InstAffineWeak.lean:73`).

**Theorem: The origin correction remains valid.** Replacing the origin correction by a valid origin profile preserves validity of the shape parameters. Source: `Breakdown.CellReduction.Instantiation.Internal.withOrigin_valid` (`Breakdown/CellReduction/InstAffineWeak.lean:77`).

**Theorem: Weak Hessian of an affine field.** The stored affine Hessian gives the weak spatial derivatives of every gradient column. Source: `Breakdown.CellReduction.Instantiation.affineFieldWeakSecondDeriv_holds` (`Breakdown/CellReduction/InstAffineWeak.lean:83`).

### Breakdown.CellReduction.InstAssembly

Regularity of the profile, pressure and pin target is assembled into the structural certificate clauses.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: Package a real Lipschitz bound.** A uniform real difference bound gives a nonnegative Lipschitz constant on the specified set. Source: `Breakdown.CellReduction.Instantiation.Internal.slopeBound_of_bound` (`Breakdown/CellReduction/InstAssembly.lean:25`).

**Theorem: Unpack a scalar Lipschitz bound.** A Lipschitz constant K bounds the absolute difference of scalar values by K times the distance. Source: `Breakdown.CellReduction.Instantiation.Internal.realBound_of_slopeBound` (`Breakdown/CellReduction/InstAssembly.lean:30`).

**Theorem: Add finitely many Lipschitz bounds.** The sum of the scalar fields has difference bounded by the sum of their Lipschitz constants times the distance. Source: `Breakdown.CellReduction.Instantiation.Internal.bound_sum` (`Breakdown/CellReduction/InstAssembly.lean:34`).

**Theorem: Scale a scalar Lipschitz bound.** Multiplying a scalar field by c multiplies its Lipschitz bound by |c|. Source: `Breakdown.CellReduction.Instantiation.Internal.bound_const_mul` (`Breakdown/CellReduction/InstAssembly.lean:41`).

**Theorem: The selected parameters remain valid.** The parameter choice at q satisfies the shape admissibility conditions. Source: `Breakdown.CellReduction.Instantiation.Internal.paramsAt_valid` (`Breakdown/CellReduction/InstAssembly.lean:48`).

**Theorem: Periodicity and local pressure slopes.** The instantiated pressure is jointly continuous, has period one, and has spatial Lipschitz bounds on every ball uniform in time. Source: `Breakdown.CellReduction.Instantiation.Internal.pressure_regular` (`Breakdown/CellReduction/InstAssembly.lean:53`).

**Theorem: Kinetic energy is locally Lipschitz.** On the prescribed closed ball, half the squared field norm has a finite Lipschitz bound. Source: `Breakdown.CellReduction.Instantiation.Internal.kinetic_bound` (`Breakdown/CellReduction/InstAssembly.lean:85`).

**Theorem: Instantiate the profile structure.** Under the stated hypotheses, the valid shape, pressure and adjoint entries supply the extended certificate's structural clauses. Source: `Breakdown.CellReduction.Instantiation.instantiation_holds_of` (`Breakdown/CellReduction/InstAssembly.lean:95`).

### Breakdown.CellReduction.InstBallAgreement

When the moving phase vanishes near the origin, the moved field and pressure agree with the original data on the matching ball.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: The moved phase agrees locally.** Near an inner phase variable, the moved radial phase equals the original radial phase. Source: `Breakdown.CellReduction.Instantiation.Internal.moved_radialPhase_eventuallyEq` (`Breakdown/CellReduction/InstBallAgreement.lean:21`).

**Theorem: Squaring preserves an inner radius bound.** A norm strictly below the positive radius has square strictly below the radius squared. Source: `Breakdown.CellReduction.Instantiation.Internal.norm_sq_lt_of_norm_lt` (`Breakdown/CellReduction/InstBallAgreement.lean:26`).

**Theorem: The inner phase slope stays fixed.** Where the moving phase vanishes locally, the moved phase slope at the chart radius equals its original value. Source: `Breakdown.CellReduction.Instantiation.Internal.moved_phaseSlope_eq` (`Breakdown/CellReduction/InstBallAgreement.lean:29`).

**Theorem: The inner reduced amplitudes stay fixed.** In the phase-free inner region, the moved reduced component amplitudes equal the original amplitudes. Source: `Breakdown.CellReduction.Instantiation.Internal.moved_reducedComps_eq` (`Breakdown/CellReduction/InstBallAgreement.lean:39`).

**Theorem: The inner complex phase stays fixed.** In the phase-free inner region, the moved key phase equals the original key phase. Source: `Breakdown.CellReduction.Instantiation.Internal.moved_keyPhase_eq` (`Breakdown/CellReduction/InstBallAgreement.lean:45`).

**Theorem: The inner key field stays fixed.** Inside the matching ball, the moved key field equals the original key field. Source: `Breakdown.CellReduction.Instantiation.Internal.moved_keyVector_eq` (`Breakdown/CellReduction/InstBallAgreement.lean:49`).

**Theorem: An interior ball is a neighbourhood.** The ball around the origin is a neighbourhood of any point strictly inside it. Source: `Breakdown.CellReduction.Instantiation.Internal.ball_mem_nhds` (`Breakdown/CellReduction/InstBallAgreement.lean:60`).

**Theorem: Moved and original modes agree locally.** Near the specified inner spatial point, the moved key field equals its original field. Source: `Breakdown.CellReduction.Instantiation.Internal.moved_keyVector_eventuallyEq` (`Breakdown/CellReduction/InstBallAgreement.lean:63`).

**Theorem: The inner key Hessian stays fixed.** Inside the matching ball, the moved key Hessian equals the original key Hessian. Source: `Breakdown.CellReduction.Instantiation.Internal.moved_keySecondDeriv_eq` (`Breakdown/CellReduction/InstBallAgreement.lean:69`).

**Theorem: The inner shape field stays fixed.** Inside the matching ball, the moved shape field equals the original shape field. Source: `Breakdown.CellReduction.Instantiation.Internal.moved_field_eq` (`Breakdown/CellReduction/InstBallAgreement.lean:77`).

**Theorem: Local agreement of moved profiles.** Near the specified inner spatial point, the moved full shape field equals its original field. Source: `Breakdown.CellReduction.Instantiation.Internal.moved_field_eventuallyEq` (`Breakdown/CellReduction/InstBallAgreement.lean:84`).

**Theorem: The inner shape Hessian stays fixed.** Inside the matching ball, the moved stored shape Hessian equals the original stored shape Hessian. Source: `Breakdown.CellReduction.Instantiation.Internal.moved_secondDeriv_eq` (`Breakdown/CellReduction/InstBallAgreement.lean:90`).

**Theorem: The inner pressure stays fixed.** Inside the matching ball, the moved pressure equals the original pressure. Source: `Breakdown.CellReduction.Instantiation.Internal.moved_pressure_eq` (`Breakdown/CellReduction/InstBallAgreement.lean:96`).

**Theorem: Local agreement of moved pressures.** Near the specified inner spatial point, the moved pressure equals its original pressure. Source: `Breakdown.CellReduction.Instantiation.Internal.moved_pressure_eventuallyEq` (`Breakdown/CellReduction/InstBallAgreement.lean:106`).

### Breakdown.CellReduction.InstFieldDecayOrder

Endpoint orders of the shape amplitudes give quantitative decay for the field and its first two derivatives.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: Combine inner and outer decay bounds.** The inner bound and outer power decay combine into one global bound using one plus radius. Source: `Breakdown.CellReduction.Instantiation.Internal.DecayOrder.near_far_bound` (`Breakdown/CellReduction/InstFieldDecayOrder.lean:19`).

**Theorem: Globalize the derivative decay bounds.** Regularity and far-field bounds give one global coefficient controlling the field, derivative and Hessian with successive decay exponents e, e+1 and e+2. Source: `Breakdown.CellReduction.Instantiation.Internal.DecayOrder.key_bounds_of_far` (`Breakdown/CellReduction/InstFieldDecayOrder.lean:49`).

**Theorem: Unpack far-field derivative bounds.** Beyond some radius at least one, the field and its first two derivatives have a common coefficient and successive decay orders a, a+1 and a+2. Source: `Breakdown.CellReduction.Instantiation.Internal.DecayOrder.farBound_bounds` (`Breakdown/CellReduction/InstFieldDecayOrder.lean:67`).

**Theorem: Equal orders give the same far bound.** Equality of the decay orders transports the far-field derivative bound to the replacement order. Source: `Breakdown.CellReduction.Instantiation.Internal.DecayOrder.farBound_degree_eq` (`Breakdown/CellReduction/InstFieldDecayOrder.lean:82`).

**Theorem: The outer radial weight has its order.** The nth power of one minus compactified radius has far-field derivative decay of order n. Source: `Breakdown.CellReduction.Instantiation.Internal.DecayOrder.farBound_weightPow` (`Breakdown/CellReduction/InstFieldDecayOrder.lean:86`).

**Theorem: Decay order of a type-two key.** A valid type-two key field has far-field derivative decay at its amplitude's outer order. Source: `Breakdown.CellReduction.Instantiation.Internal.DecayOrder.typeTwo_farBound_order` (`Breakdown/CellReduction/InstFieldDecayOrder.lean:97`).

**Definition: Full azimuthal amplitude.** The full azimuthal amplitude combines radial and polar spline derivatives with the outer radial order and angular frequency. Source: `Breakdown.CellReduction.Instantiation.Internal.DecayOrder.azimPartFull` (`Breakdown/CellReduction/InstFieldDecayOrder.lean:249`).

**Theorem: The full azimuthal amplitude is regular.** The full azimuthal amplitude satisfies the compactified slope-regularity condition. Source: `Breakdown.CellReduction.Instantiation.Internal.DecayOrder.azimPartFull_regular` (`Breakdown/CellReduction/InstFieldDecayOrder.lean:258`).

**Theorem: Radial tail power decays by its degree.** The nth power of chart length divided by radius plus chart length has spatial decay order n. Source: `Breakdown.CellReduction.Instantiation.Internal.DecayOrder.tailPow_farDecay` (`Breakdown/CellReduction/InstFieldDecayOrder.lean:277`).

**Theorem: Factor the radial reduced component.** The radial reduced component factors into the axis factor, the outer radial weight of order n+1, and the regular radial amplitude. Source: `Breakdown.CellReduction.Instantiation.Internal.DecayOrder.reduced_zero_eq` (`Breakdown/CellReduction/InstFieldDecayOrder.lean:288`).

**Theorem: Factor the polar reduced component.** The polar reduced component factors into the axis factor, the outer radial weight of order n+1, and the regular polar amplitude. Source: `Breakdown.CellReduction.Instantiation.Internal.DecayOrder.reduced_one_eq` (`Breakdown/CellReduction/InstFieldDecayOrder.lean:298`).

**Theorem: Factor the azimuthal reduced component.** The azimuthal reduced component factors into the common axis and outer-radial weights times the full azimuthal amplitude plus its phase-slope correction. Source: `Breakdown.CellReduction.Instantiation.Internal.DecayOrder.reduced_two_eq` (`Breakdown/CellReduction/InstFieldDecayOrder.lean:308`).

**Theorem: Decay order of a type-one key.** The type-one key field has spatial decay of order n+1. Source: `Breakdown.CellReduction.Instantiation.Internal.DecayOrder.typeOne_farDecay_order` (`Breakdown/CellReduction/InstFieldDecayOrder.lean:341`).

**Theorem: Bound a key at reference time.** At time zero, one nonnegative coefficient controls the key field, derivative and Hessian with successive radial decay exponents. Source: `Breakdown.CellReduction.Instantiation.Internal.DecayOrder.key_bounds_at_zero` (`Breakdown/CellReduction/InstFieldDecayOrder.lean:375`).

**Theorem: Uniform-in-time key derivative decay.** One nonnegative coefficient bounds the key field, spatial derivative and stored Hessian at all times with successive radial decay orders. Source: `Breakdown.CellReduction.Instantiation.Internal.DecayOrder.key_bounds_all` (`Breakdown/CellReduction/InstFieldDecayOrder.lean:394`).

**Theorem: Increase a scaled quotient bound.** Increasing the nonnegative coefficient and numerator preserves the stated common-denominator bound. Source: `Breakdown.CellReduction.Instantiation.Internal.DecayOrder.scale_le` (`Breakdown/CellReduction/InstFieldDecayOrder.lean:421`).

**Theorem: Differentiate a linear complex phase.** The derivative of exp(i a s) is the same phase multiplied by i a. Source: `Breakdown.CellReduction.Instantiation.Internal.DecayOrder.phase_hasDerivAt` (`Breakdown/CellReduction/InstFieldDecayOrder.lean:426`).

**Theorem: Endpoint orders give field decay.** A uniform lower bound e on the outer endpoint orders gives decay order e for the field and its time derivative, e+1 for the gradient and e+2 for the stored Hessian. Source: `Breakdown.CellReduction.Instantiation.fieldDecayOrder_holds` (`Breakdown/CellReduction/InstFieldDecayOrder.lean:436`).

### Breakdown.CellReduction.InstFieldPotential

The two shape families are combined to construct a decaying, periodic curl potential for the field.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: Construct a decaying curl potential.** Under the stated hypotheses, valid shape data of outer order at least three admit a periodic curl potential with inverse-square value and inverse-cubic gradient decay. Source: `Breakdown.CellReduction.Instantiation.fieldPotential_holds_of` (`Breakdown/CellReduction/InstFieldPotential.lean:19`).

**Theorem: Construct a decaying curl potential.** Valid shape data of outer order at least three admit a periodic curl potential with inverse-square value and inverse-cubic gradient decay. Source: `Breakdown.CellReduction.Instantiation.fieldPotential_holds` (`Breakdown/CellReduction/InstFieldPotential.lean:38`).

### Breakdown.CellReduction.InstFieldPotentialAmp

A radial phase, compactified amplitude and linear vector factor produce a continuously differentiable field with the needed decay.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Definition: Real coordinates in complex space.** The coordinate embedding views each real vector coordinate as a complex number. Source: `Breakdown.CellReduction.Instantiation.Internal.AmpField.coordLift` (`Breakdown/CellReduction/InstFieldPotentialAmp.lean:23`).

**Theorem: Complex embedding does not enlarge norm.** The coordinatewise real-to-complex embedding has norm at most the norm of its input. Source: `Breakdown.CellReduction.Instantiation.Internal.AmpField.coordLift_norm_le` (`Breakdown/CellReduction/InstFieldPotentialAmp.lean:26`).

**Theorem: Bound the complex embedding map.** The operator norm of the coordinatewise complex embedding is at most one. Source: `Breakdown.CellReduction.Instantiation.Internal.AmpField.coordLift_opNorm` (`Breakdown/CellReduction/InstFieldPotentialAmp.lean:32`).

**Definition: Radial phase times weighted amplitude.** The scalar amplitude multiplies the radial oscillation, the endpoint weight and the compactified spline amplitude. Source: `Breakdown.CellReduction.Instantiation.Internal.AmpField.ampScalar` (`Breakdown/CellReduction/InstFieldPotentialAmp.lean:35`).

**Theorem: Separate the scalar radial amplitude.** The radial amplitude field is the scalar amplitude multiplied by the complex lift of the vector field. Source: `Breakdown.CellReduction.Instantiation.Internal.AmpField.field_eq` (`Breakdown/CellReduction/InstFieldPotentialAmp.lean:39`).

**Theorem: Bound the derivative of a composition.** The derivative of the composition exists and has norm at most the product of the two derivative norms. Source: `Breakdown.CellReduction.Instantiation.Internal.AmpField.comp_real_bound` (`Breakdown/CellReduction/InstFieldPotentialAmp.lean:44`).

**Theorem: Bound the derivative of a product.** The complex product has derivative norm bounded by each factor's value norm times the other factor's derivative norm, summed. Source: `Breakdown.CellReduction.Instantiation.Internal.AmpField.mul_bound` (`Breakdown/CellReduction/InstFieldPotentialAmp.lean:52`).

**Theorem: Bound a scalar-vector product derivative.** The derivative of the scalar-vector product is bounded by scalar size times the linear vector-map norm plus scalar-derivative norm times vector size. Source: `Breakdown.CellReduction.Instantiation.Internal.AmpField.smul_bound` (`Breakdown/CellReduction/InstFieldPotentialAmp.lean:59`).

**Theorem: A two-coordinate chain-rule bound.** Composing a two-variable function with two scalar coordinates gives derivative norm at most the outer derivative norm times the sum of the coordinate-derivative norms. Source: `Breakdown.CellReduction.Instantiation.Internal.AmpField.pair_bound` (`Breakdown/CellReduction/InstFieldPotentialAmp.lean:70`).

**Theorem: Radius derivative has norm at most one.** Away from the origin, the spatial norm is differentiable with derivative norm at most one. Source: `Breakdown.CellReduction.Instantiation.Internal.AmpField.norm_deriv_bound` (`Breakdown/CellReduction/InstFieldPotentialAmp.lean:79`).

**Theorem: A scaled bound for the radial chart.** Away from the origin, the radial chart derivative norm times radius is at most t times one minus t. Source: `Breakdown.CellReduction.Instantiation.Internal.AmpField.chart_deriv_bound` (`Breakdown/CellReduction/InstFieldPotentialAmp.lean:87`).

**Theorem: A scaled bound for normalized height.** Away from the origin, the normalized-height derivative norm times radius is at most two. Source: `Breakdown.CellReduction.Instantiation.Internal.AmpField.height_deriv_bound` (`Breakdown/CellReduction/InstFieldPotentialAmp.lean:108`).

**Theorem: Derivative bound for the radial weight.** The derivative of t(1-t)^e has magnitude at most (1+e)(1-t)^(e-1) on the unit interval. Source: `Breakdown.CellReduction.Instantiation.Internal.AmpField.weight_deriv_bound` (`Breakdown/CellReduction/InstFieldPotentialAmp.lean:140`).

**Theorem: Derivative bound for the radial phase.** The spatial complex-phase derivative has norm at most twice the absolute frequency times the absolute radial-phase derivative times radius. Source: `Breakdown.CellReduction.Instantiation.Internal.AmpField.phase_deriv_bound` (`Breakdown/CellReduction/InstFieldPotentialAmp.lean:167`).

**Theorem: The spatial chart lies in its rectangle.** The compactified radius and normalized height belong to the unit radial interval times the height interval from minus one to one. Source: `Breakdown.CellReduction.Instantiation.Internal.AmpField.box_mem` (`Breakdown/CellReduction/InstFieldPotentialAmp.lean:190`).

**Theorem: Norm of the real radial weight.** The complex radial weight has norm equal to t times (1-t)^e at the compactified radius. Source: `Breakdown.CellReduction.Instantiation.Internal.AmpField.weight_norm` (`Breakdown/CellReduction/InstFieldPotentialAmp.lean:194`).

**Theorem: Bound the weighted scalar amplitude.** The scalar amplitude norm is at most the radial weight times the bound B for its compactified amplitude. Source: `Breakdown.CellReduction.Instantiation.Internal.AmpField.amp_norm_le` (`Breakdown/CellReduction/InstFieldPotentialAmp.lean:201`).

**Theorem: Bound the weighted potential derivative.** Away from the origin, the potential derivative has a bound combining amplitude, amplitude-slope and phase-slope constants times the radial weight. Source: `Breakdown.CellReduction.Instantiation.Internal.AmpField.amp_deriv_off` (`Breakdown/CellReduction/InstFieldPotentialAmp.lean:210`).

**Theorem: Potential amplitude is regular off zero.** Away from the origin, the scalar amplitude times the vector field is continuously differentiable. Source: `Breakdown.CellReduction.Instantiation.Internal.AmpField.field_smooth_off` (`Breakdown/CellReduction/InstFieldPotentialAmp.lean:308`).

**Theorem: A globally regular decaying potential.** The potential amplitude is globally continuously differentiable, with inverse-square field decay and inverse-cube derivative decay. Source: `Breakdown.CellReduction.Instantiation.Internal.AmpField.field_regular` (`Breakdown/CellReduction/InstFieldPotentialAmp.lean:321`).

**Theorem: Regularity of a radial amplitude.** A valid radial-amplitude field with endpoint order at least three is continuously differentiable and has inverse-square value and inverse-cubic gradient decay. Source: `Breakdown.CellReduction.Instantiation.radialAmpField_regular` (`Breakdown/CellReduction/InstFieldPotentialAmp.lean:445`).

### Breakdown.CellReduction.InstFieldPotentialParts

The radial-amplitude field and regularity of a height primitive are the two reusable parts of the curl-potential construction.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Definition: Radial amplitude times a linear field.** The phased radial amplitude multiplies the complex coordinates of a linear vector field. Source: `Breakdown.CellReduction.Instantiation.radialAmpField` (`Breakdown/CellReduction/InstFieldPotentialParts.lean:15`).

**Definition: Regularity of a radial amplitude.** This proposition requires that a valid radial-amplitude field with endpoint order at least three is continuously differentiable and has inverse-square value and inverse-cubic gradient decay. Source: `Breakdown.CellReduction.Instantiation.RadialAmpFieldRegular` (`Breakdown/CellReduction/InstFieldPotentialParts.lean:21`).

**Interface definition: Smoothness of a height primitive.** This proposition requires that integrating a continuously differentiable amplitude from minus one to the height coordinate gives a continuously differentiable primitive. Source: `Breakdown.CellReduction.Instantiation.PrimitiveSmoothHolds` (`Breakdown/CellReduction/InstFieldPotentialParts.lean:27`).

Supplied by `Breakdown.CellReduction.Instantiation.primitiveSmooth_holds` (`lean/Breakdown/CellReduction/InstFieldPotentialPrimitive.lean:48`).

### Breakdown.CellReduction.InstFieldPotentialPrimitive

Differentiation of parameter-dependent interval integrals supplies the regularity of the swirl primitive.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: Integrating a parameter preserves C1.** Integrating the stated continuously differentiable integrand over a fixed finite interval gives a continuously differentiable parameter function. Source: `Breakdown.CellReduction.Instantiation.Internal.fixedIntervalIntegral_contDiff` (`Breakdown/CellReduction/InstFieldPotentialPrimitive.lean:19`).

**Theorem: Smoothness of a height primitive.** Integrating a continuously differentiable amplitude from minus one to the height coordinate gives a continuously differentiable primitive. Source: `Breakdown.CellReduction.Instantiation.primitiveSmooth_holds` (`Breakdown/CellReduction/InstFieldPotentialPrimitive.lean:48`).

### Breakdown.CellReduction.InstFieldPotentialRotation

Nonzero azimuthal modes admit a curl potential built from a rotated field and the generator of axial rotations.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Definition: Keys at one absolute frequency.** The key group retains the keys whose first label has the selected absolute value. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.keysAt` (`Breakdown/CellReduction/InstFieldPotentialRotation.lean:24`).

**Theorem: Select keys by absolute angular label.** A key belongs to the k-fibre exactly when it belongs to the original data and its first label has absolute value k. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.mem_keysAt` (`Breakdown/CellReduction/InstFieldPotentialRotation.lean:27`).

**Theorem: A key fibre remains admissible.** Restricting valid field data to one absolute-angular-label fibre preserves validity. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.keysAt_valid` (`Breakdown/CellReduction/InstFieldPotentialRotation.lean:30`).

**Theorem: Split the field into angular fibres.** The full shape field is the finite sum of the fields restricted to each absolute angular label. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.shapeField_fiber` (`Breakdown/CellReduction/InstFieldPotentialRotation.lean:62`).

**Definition: Axial rotation as a linear map.** The axial isometry is viewed as a continuous linear map. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.rotL` (`Breakdown/CellReduction/InstFieldPotentialRotation.lean:68`).

**Theorem: The rotation map acts by axial rotation.** The packaged linear rotation map evaluates to the ordinary axial rotation. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.rotL_apply` (`Breakdown/CellReduction/InstFieldPotentialRotation.lean:70`).

**Theorem: Axial rotation has norm at most one.** The linear operator norm of axial rotation is at most one. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.rotL_norm_le` (`Breakdown/CellReduction/InstFieldPotentialRotation.lean:72`).

**Definition: Generator of axial rotations.** The rotation generator sends the first two coordinates to minus the second and the first, and sets the third to zero. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.turnVec` (`Breakdown/CellReduction/InstFieldPotentialRotation.lean:75`).

**Theorem: Coordinates of the unit basis vector.** A coordinate of a unit basis vector is one at the matching index and zero otherwise. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.unit_apply` (`Breakdown/CellReduction/InstFieldPotentialRotation.lean:77`).

**Theorem: Real parts commute with rotation.** Taking real Cartesian parts after complex rotation equals rotating the real Cartesian parts. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.realPart_rotate` (`Breakdown/CellReduction/InstFieldPotentialRotation.lean:80`).

**Theorem: Rotation respects scalar multiplication.** Rotating a complex vector after scaling gives the scalar times the rotated vector. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.rotate_smul` (`Breakdown/CellReduction/InstFieldPotentialRotation.lean:86`).

**Theorem: Differentiate a rotating vector.** The derivative of a rotated varying vector is the rotated vector derivative plus the rotation generator applied to the rotated vector. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.hasDerivAt_rot` (`Breakdown/CellReduction/InstFieldPotentialRotation.lean:90`).

**Theorem: Rotate each key by its angular phase.** Evaluating the shape field at a rotated point equals rotating the real part of its key sum with each key multiplied by its angular phase. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.field_rot` (`Breakdown/CellReduction/InstFieldPotentialRotation.lean:107`).

**Definition: Quarter-period angular shift.** The angular shift is minus pi divided by twice the nonzero mode frequency. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.rotShift` (`Breakdown/CellReduction/InstFieldPotentialRotation.lean:120`).

**Definition: Rotated precursor of the potential.** The potential precursor rotates the field's argument and output in opposite directions and divides by the mode frequency. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.axisPot` (`Breakdown/CellReduction/InstFieldPotentialRotation.lean:122`).

**Definition: Phase form of the rotated field.** The rotated field is expressed as a finite harmonic sum divided by the mode frequency. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.phaseSum` (`Breakdown/CellReduction/InstFieldPotentialRotation.lean:125`).

**Theorem: Rotation commutes with real scaling.** Axial rotation of a scalar multiple is the same scalar multiple of the rotated vector. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.axialRot_smul` (`Breakdown/CellReduction/InstFieldPotentialRotation.lean:130`).

**Theorem: Rotation of the axial antiderivative.** At a rotated spatial point, the axial potential equals the rotated phase sum evaluated at that angle. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.axisPot_rot` (`Breakdown/CellReduction/InstFieldPotentialRotation.lean:133`).

**Theorem: Read the axial potential at angle zero.** The axial potential equals its phase-sum representation at zero angle. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.axisPot_eq` (`Breakdown/CellReduction/InstFieldPotentialRotation.lean:139`).

**Theorem: Differentiate a shifted complex phase.** The derivative of exp(i a(b+v)) is the same phase multiplied by i a. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.hasDerivAt_phase` (`Breakdown/CellReduction/InstFieldPotentialRotation.lean:144`).

**Theorem: Differentiate every angular phase.** The phase-sum derivative multiplies each key by its angular frequency times i, retaining the prefactor one over M. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.hasDerivAt_phaseSum` (`Breakdown/CellReduction/InstFieldPotentialRotation.lean:152`).

**Theorem: The quarter-turn phase cancels frequency.** For the specified angular labels, the shifted complex phase times its frequency derivative and reciprocal frequency equals one. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.phase_at_shift` (`Breakdown/CellReduction/InstFieldPotentialRotation.lean:162`).

**Theorem: The phase derivative recovers the field.** At zero angle, the normalized derivative of the shifted phase sum equals the original shape field. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.phaseSum_deriv_zero` (`Breakdown/CellReduction/InstFieldPotentialRotation.lean:197`).

**Theorem: Differentiate the angular potential.** The axial potential differentiated along the rotation direction equals the profile plus the rotation generator applied to the potential. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.axisPot_dirDeriv` (`Breakdown/CellReduction/InstFieldPotentialRotation.lean:211`).

**Theorem: Finite real combinations stay solenoidal.** The real part of the finite constant-coefficient combination has zero divergence under the component solenoidality assumptions. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.div_smul_realPart_sum` (`Breakdown/CellReduction/InstFieldPotentialRotation.lean:229`).

**Theorem: The axial potential is solenoidal.** The constructed axial potential has zero spatial divergence. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.axisPot_div` (`Breakdown/CellReduction/InstFieldPotentialRotation.lean:252`).

**Definition: Axial cross-product field.** The axial cross-product formula combines the vertical field component and horizontal position coordinates into the potential vector. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.axisCross` (`Breakdown/CellReduction/InstFieldPotentialRotation.lean:263`).

**Theorem: Coordinates of the axial cross field.** The axial cross field has horizontal coordinates minus g's vertical component times position and vertical coordinate equal to the horizontal dot product. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.axisCross_apply` (`Breakdown/CellReduction/InstFieldPotentialRotation.lean:266`).

**Theorem: A coordinate is bounded by the norm.** The absolute value of the selected coordinate is bounded by the vector norm. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.comp_le` (`Breakdown/CellReduction/InstFieldPotentialRotation.lean:270`).

**Theorem: Bound the axial cross field.** The axial cross-field norm is at most four times the norms of its two inputs. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.axisCross_norm` (`Breakdown/CellReduction/InstFieldPotentialRotation.lean:274`).

**Definition: The axial bilinear map.** The axial cross-product formula is packaged as a continuous bilinear map with bound four. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.axisCrossL` (`Breakdown/CellReduction/InstFieldPotentialRotation.lean:292`).

**Theorem: Read the packaged axial cross map.** The packaged bilinear map evaluates to the axial cross-field formula. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.axisCrossL_apply` (`Breakdown/CellReduction/InstFieldPotentialRotation.lean:301`).

**Theorem: Bound the axial cross operator.** The axial cross bilinear operator has norm at most four. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.axisCrossL_norm` (`Breakdown/CellReduction/InstFieldPotentialRotation.lean:303`).

**Theorem: Curl recovers the target field.** Under the angular-derivative and zero-divergence identities, the curl of the axial cross construction equals the target field. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.curl_axisCross` (`Breakdown/CellReduction/InstFieldPotentialRotation.lean:306`).

**Definition: A periodic decaying curl potential.** This proposition requires that the field is the curl of the stated periodic continuously differentiable potential with inverse-square value and time-derivative decay and inverse-cubic gradient decay. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.PotentialPack` (`Breakdown/CellReduction/InstFieldPotentialRotation.lean:329`).

**Theorem: Regularity of a fixed time slice.** Each fixed time slice inherits continuous differentiability from the joint field. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.slice_smooth` (`Breakdown/CellReduction/InstFieldPotentialRotation.lean:336`).

**Theorem: The potential is differentiable in time.** The constructed potential at a fixed spatial point is continuously differentiable in time. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.time_smooth` (`Breakdown/CellReduction/InstFieldPotentialRotation.lean:340`).

**Theorem: A periodic decaying curl potential.** Under the stated hypotheses, the field is the curl of the stated periodic continuously differentiable potential with inverse-square value and time-derivative decay and inverse-cubic gradient decay. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.pack_sum` (`Breakdown/CellReduction/InstFieldPotentialRotation.lean:344`).

**Theorem: Position costs one decay power.** Multiplying a nonnegative order-(n+1) decay bound by radius gives an order-n decay bound. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.mul_norm_div_le` (`Breakdown/CellReduction/InstFieldPotentialRotation.lean:372`).

**Theorem: One extra decay power is smaller.** For nonnegative numerator and radius, an additional denominator power decreases the decay bound. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.div_pow_mono` (`Breakdown/CellReduction/InstFieldPotentialRotation.lean:381`).

**Theorem: A periodic decaying curl potential.** Under the stated hypotheses, the field is the curl of the stated periodic continuously differentiable potential with inverse-square value and time-derivative decay and inverse-cubic gradient decay. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.pack_of_cross` (`Breakdown/CellReduction/InstFieldPotentialRotation.lean:386`).

**Theorem: A bounded potential for a type-one fibre.** The axial-cross construction supplies a curl potential for the type-one field with one constant controlling the required regularity and decay. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.typeOne_pack` (`Breakdown/CellReduction/InstFieldPotentialRotation.lean:450`).

### Breakdown.CellReduction.InstFieldPotentialStream

The axisymmetric shape is rewritten in terms of stream and swirl primitives to expose its curl potential.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: Differentiate radius away from zero.** Away from the origin, the radius derivative is inner product with the unit radial vector. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.hasFDerivAt_norm_of_ne` (`Breakdown/CellReduction/InstFieldPotentialStream.lean:24`).

**Theorem: Expand a two-coordinate derivative.** A real-linear map on a coordinate pair is the sum of its two coordinate-direction values weighted by the input coordinates. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.pair_apply` (`Breakdown/CellReduction/InstFieldPotentialStream.lean:39`).

**Theorem: Derivative of a radial-height amplitude.** The scalar-potential derivative separates a radial inner-product term from a vertical-coordinate term, including phase, radial-weight and normalized-height derivatives. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.scalar_grad` (`Breakdown/CellReduction/InstFieldPotentialStream.lean:44`).

**Definition: Real-to-complex coordinate map.** The continuous linear map embeds each real vector coordinate into the complex numbers. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.ofRealL` (`Breakdown/CellReduction/InstFieldPotentialStream.lean:104`).

**Theorem: Complex embedding of real coordinates.** The real-to-complex vector map embeds each real coordinate individually. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.ofRealL_apply` (`Breakdown/CellReduction/InstFieldPotentialStream.lean:107`).

**Definition: Rotation generator as a linear map.** The coordinate rotation generator is packaged as a continuous linear map. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.turnL` (`Breakdown/CellReduction/InstFieldPotentialStream.lean:109`).

**Theorem: Read the infinitesimal rotation map.** The linear turn map applies the infinitesimal axial rotation to its input. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.turnL_apply` (`Breakdown/CellReduction/InstFieldPotentialStream.lean:115`).

**Theorem: Coordinates of infinitesimal rotation.** The infinitesimal axial rotation sends the first two coordinates to minus the second and the first, and sets the third to zero. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.turnVec_apply` (`Breakdown/CellReduction/InstFieldPotentialStream.lean:117`).

**Theorem: Bound the infinitesimal rotation map.** The infinitesimal axial rotation operator has norm at most one. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.turnL_norm` (`Breakdown/CellReduction/InstFieldPotentialStream.lean:120`).

**Theorem: A unit-vector pairing gives a coordinate.** The inner product with the ith coordinate unit vector is the ith coordinate. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.inner_unit` (`Breakdown/CellReduction/InstFieldPotentialStream.lean:128`).

**Theorem: Curl of the stream-and-swirl ansatz.** The curl of the two scalar-potential terms has the explicit radial, azimuthal and vertical coordinate contributions determined by their scalar derivatives. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.curl_scalarPair` (`Breakdown/CellReduction/InstFieldPotentialStream.lean:131`).

**Definition: Extend the origin correction.** When the origin profile edge is below one the extension uses its stored evaluation, and otherwise it uses the stored polynomial. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.originExt` (`Breakdown/CellReduction/InstFieldPotentialStream.lean:203`).

**Theorem: The origin extension matches its profile.** The origin extension equals the evaluated origin profile on the stated domain. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.originExt_eq` (`Breakdown/CellReduction/InstFieldPotentialStream.lean:205`).

**Theorem: The origin extension has C1 regularity.** The valid origin extension is continuously differentiable. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.originExt_smooth` (`Breakdown/CellReduction/InstFieldPotentialStream.lean:213`).

**Definition: The stream amplitude.** The stream amplitude adds the axis coefficient times the origin correction times height to the stored stream spline. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.streamF` (`Breakdown/CellReduction/InstFieldPotentialStream.lean:230`).

**Definition: Height primitive of the swirl.** The swirl primitive integrates the stored swirl spline from minus one to the height coordinate. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.swirlF` (`Breakdown/CellReduction/InstFieldPotentialStream.lean:233`).

**Theorem: The stream amplitude is differentiable.** The extended stream amplitude is continuously differentiable. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.streamF_smooth` (`Breakdown/CellReduction/InstFieldPotentialStream.lean:235`).

**Theorem: The extension matches the stream value.** On the stated chart domain, the extended stream amplitude equals the original stream value. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.streamF_eq` (`Breakdown/CellReduction/InstFieldPotentialStream.lean:244`).

**Theorem: The swirl primitive is differentiable.** The swirl primitive is continuously differentiable. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.swirlF_smooth` (`Breakdown/CellReduction/InstFieldPotentialStream.lean:248`).

**Theorem: Derivative along the height coordinate.** The derivative along the second coordinate is the joint derivative applied to the second coordinate direction. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.line_second` (`Breakdown/CellReduction/InstFieldPotentialStream.lean:252`).

**Theorem: Derivative along the radial coordinate.** The derivative along the first coordinate is the joint derivative applied to the first coordinate direction. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.line_first` (`Breakdown/CellReduction/InstFieldPotentialStream.lean:258`).

**Theorem: Swirl primitive differentiates correctly.** The height derivative of the swirl primitive equals the swirl spline amplitude. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.swirlF_second` (`Breakdown/CellReduction/InstFieldPotentialStream.lean:264`).

**Theorem: The compactified radius is below one.** For positive chart length, the compactified radius is strictly below one. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.chartCoord_lt_one` (`Breakdown/CellReduction/InstFieldPotentialStream.lean:281`).

**Theorem: Recover radius from its coordinate.** Applying the inverse radial chart to the compactified coordinate recovers the physical radius. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.chartRadius_coord` (`Breakdown/CellReduction/InstFieldPotentialStream.lean:286`).

**Theorem: Reconstruct a type-two key in its frame.** The type-two key is its temporal and radial phase times the radial, polar and azimuthal basis combination of its three reduced components. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.keyVector_typeTwo` (`Breakdown/CellReduction/InstFieldPotentialStream.lean:295`).

**Theorem: Differentiate the polar stream factor.** The height derivative of (1-x squared) times the stream value is minus 2x times the stream amplitude plus the polar factor times its height derivative. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.streamHeight_deriv` (`Breakdown/CellReduction/InstFieldPotentialStream.lean:313`).

**Theorem: Differentiate the radial stream weight.** The radial derivative of the weighted stream value is the weight derivative times the stream amplitude plus the weight times its radial derivative. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.streamRadial_deriv` (`Breakdown/CellReduction/InstFieldPotentialStream.lean:335`).

### Breakdown.CellReduction.InstFieldPotentialStreamKey

The stream potential for one key is checked, then the valid keys are summed with uniform decay bounds.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Definition: The single-key temporal phase.** The temporal factor is the complex exponential at the key's temporal frequency. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.timeC` (`Breakdown/CellReduction/InstFieldPotentialStreamKey.lean:22`).

**Definition: Curl potential for an axial key.** The axisymmetric potential takes the real part of the phased stream term along the rotation generator plus the swirl term along the identity field. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.typeTwoPot` (`Breakdown/CellReduction/InstFieldPotentialStreamKey.lean:24`).

**Theorem: Differentiate the radial phase.** The valid radial phase is differentiable at the squared spatial radius with its declared derivative. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.phase_hasDerivAt` (`Breakdown/CellReduction/InstFieldPotentialStreamKey.lean:28`).

**Theorem: Stream potential has the required curl.** Away from the origin, the type-two potential's curl equals the real part of its key field. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.typeTwo_curl_ne` (`Breakdown/CellReduction/InstFieldPotentialStreamKey.lean:36`).

**Theorem: Bound Cartesian real-part extraction.** The real-part reconstruction norm is at most three times the complex-vector norm. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.realPartVec_norm` (`Breakdown/CellReduction/InstFieldPotentialStreamKey.lean:135`).

**Theorem: Bound the real-part reconstruction map.** The real-part reconstruction operator has norm at most three. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.realPartVec_opNorm` (`Breakdown/CellReduction/InstFieldPotentialStreamKey.lean:145`).

**Theorem: The oscillatory factor has unit norm.** The stated complex oscillatory factor has norm one. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.timeC_norm` (`Breakdown/CellReduction/InstFieldPotentialStreamKey.lean:148`).

**Theorem: The integer phase is periodic.** An integer temporal frequency makes the complex phase invariant under a unit time shift. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.timeC_periodic` (`Breakdown/CellReduction/InstFieldPotentialStreamKey.lean:150`).

**Theorem: Differentiate the temporal phase.** The temporal phase derivative is its value multiplied by two pi times the temporal frequency times i. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.timeC_hasDerivAt` (`Breakdown/CellReduction/InstFieldPotentialStreamKey.lean:159`).

**Theorem: The temporal phase is differentiable.** The temporal complex phase is continuously differentiable. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.timeC_contDiff` (`Breakdown/CellReduction/InstFieldPotentialStreamKey.lean:165`).

**Theorem: The classical curl is continuous.** A continuously differentiable vector field has continuous curl. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.curlAt_continuous` (`Breakdown/CellReduction/InstFieldPotentialStreamKey.lean:171`).

**Theorem: A bounded potential for a type-two key.** The type-two stream construction gives the key field a curl potential with the required common regularity and decay constant. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.typeTwoKey_pack` (`Breakdown/CellReduction/InstFieldPotentialStreamKey.lean:179`).

**Theorem: A periodic decaying curl potential.** Under the stated hypotheses, the field is the curl of the stated periodic continuously differentiable potential with inverse-square value and time-derivative decay and inverse-cubic gradient decay. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.pack_congr` (`Breakdown/CellReduction/InstFieldPotentialStreamKey.lean:267`).

**Theorem: Sum the type-two curl potentials.** The finite type-two shape field admits a potential satisfying the common periodicity, curl and decay package. Source: `Breakdown.CellReduction.Instantiation.Internal.FieldPot.typeTwo_group` (`Breakdown/CellReduction/InstFieldPotentialStreamKey.lean:271`).

### Breakdown.CellReduction.InstMovedDecay

The moving radial phase preserves uniform decay of the profile and its derivatives on bounded parameter sets.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: Scaled bounds for two phase derivatives.** The radial phase has first and second derivatives bounded after multiplication by (1+s) and (1+s) squared respectively. Source: `Breakdown.CellReduction.Instantiation.Internal.MovedDecay.radialPhase_bounds` (`Breakdown/CellReduction/InstMovedDecay.lean:20`).

**Theorem: Inner-product map has norm at most one.** The bilinear inner-product operator has norm at most one. Source: `Breakdown.CellReduction.Instantiation.Internal.MovedDecay.norm_innerSL_le` (`Breakdown/CellReduction/InstMovedDecay.lean:74`).

**Theorem: Derivative of the squared radius.** The derivative of squared spatial norm is twice inner product with the spatial point. Source: `Breakdown.CellReduction.Instantiation.Internal.MovedDecay.normSq_hasFDerivAt` (`Breakdown/CellReduction/InstMovedDecay.lean:77`).

**Definition: Derivative of the squared-radius phase.** The radial-phase derivative is twice its scalar derivative times the inner-product functional at the point. Source: `Breakdown.CellReduction.Instantiation.Internal.MovedDecay.phaseGrad` (`Breakdown/CellReduction/InstMovedDecay.lean:81`).

**Theorem: Decay of the spatial phase derivatives.** Composing the radial phase with squared radius gives a differentiable gradient whose norm decays inversely and derivative norm decays quadratically. Source: `Breakdown.CellReduction.Instantiation.Internal.MovedDecay.phaseSq_bounds` (`Breakdown/CellReduction/InstMovedDecay.lean:83`).

**Theorem: Compare nearby reciprocal radii.** On the prescribed local ball, the reciprocal of one plus the nearby radius is at most twice its value at the centre. Source: `Breakdown.CellReduction.Instantiation.Internal.MovedDecay.inv_le_of_ball` (`Breakdown/CellReduction/InstMovedDecay.lean:135`).

**Theorem: Rewrite a product bound as a quotient.** The stated product bound gives the upper bound by the coefficient times the inverse positive scale. Source: `Breakdown.CellReduction.Instantiation.Internal.MovedDecay.le_mul_inv_of` (`Breakdown/CellReduction/InstMovedDecay.lean:141`).

**Theorem: Local squared-radius phase bounds.** One constant controls the phase gradient and its local variation with inverse and inverse-square radial weights. Source: `Breakdown.CellReduction.Instantiation.Internal.MovedDecay.phase_ballBound` (`Breakdown/CellReduction/InstMovedDecay.lean:145`).

**Theorem: Differentiate a linear exponential phase.** The derivative of exp(i beta u) is the same exponential times i beta. Source: `Breakdown.CellReduction.Instantiation.Internal.MovedDecay.expLine_hasDerivAt` (`Breakdown/CellReduction/InstMovedDecay.lean:178`).

**Theorem: Local bounds for an exponential phase.** The phased scalar has magnitude |alpha| and local first- and second-order bounds built from |beta| and the phase derivative bounds. Source: `Breakdown.CellReduction.Instantiation.Internal.MovedDecay.expPhase_ballBound` (`Breakdown/CellReduction/InstMovedDecay.lean:186`).

**Theorem: Absorb the bounded inner-region term.** On the stated bounded radial region, a constant term is absorbed into the chosen inverse-power bound. Source: `Breakdown.CellReduction.Instantiation.Internal.MovedDecay.le_of_near` (`Breakdown/CellReduction/InstMovedDecay.lean:234`).

**Theorem: Replace radius by one plus radius.** On the stated outer region, inverse powers of radius are bounded by the chosen multiple of inverse powers of one plus radius. Source: `Breakdown.CellReduction.Instantiation.Internal.MovedDecay.le_of_far` (`Breakdown/CellReduction/InstMovedDecay.lean:243`).

**Theorem: Globalize local derivative decay.** One nonnegative coefficient controls local field, derivative and derivative-variation bounds with decay orders one, two and three. Source: `Breakdown.CellReduction.Instantiation.Internal.MovedDecay.ballBound_global` (`Breakdown/CellReduction/InstMovedDecay.lean:258`).

**Theorem: Convert the first-order far-decay class.** The prescribed far-decay regularity yields the first-order far-bound package. Source: `Breakdown.CellReduction.Instantiation.Internal.MovedDecay.farBound_of_farDecay` (`Breakdown/CellReduction/InstMovedDecay.lean:298`).

**Theorem: Local derivative decay of a key field.** The key field has one constant controlling local value, derivative and derivative variation with radial orders one, two and three. Source: `Breakdown.CellReduction.Instantiation.Internal.MovedDecay.key_ballBound` (`Breakdown/CellReduction/InstMovedDecay.lean:313`).

**Theorem: The norm bound for scalar multiplication.** The norm of the scalar-vector product is bounded by the product of the two input norms. Source: `Breakdown.CellReduction.Instantiation.Internal.MovedDecay.lsmul_norm_le` (`Breakdown/CellReduction/InstMovedDecay.lean:326`).

**Theorem: Local decay after phase multiplication.** Multiplying the field by the controlled phase preserves decay orders one, two and three with coefficient 2m(1+bK) squared times N. Source: `Breakdown.CellReduction.Instantiation.Internal.MovedDecay.phaseMul_ballBound` (`Breakdown/CellReduction/InstMovedDecay.lean:329`).

**Theorem: Enlarge the phase coefficient bounds.** Increasing the nonnegative amplitude and frequency bounds increases m times (1+bK) squared. Source: `Breakdown.CellReduction.Instantiation.Internal.MovedDecay.coef_le` (`Breakdown/CellReduction/InstMovedDecay.lean:355`).

**Theorem: Combine two common weighted terms.** A common upper coefficient bounds the two weighted terms by twice that coefficient times the sum of their amplitudes. Source: `Breakdown.CellReduction.Instantiation.Internal.MovedDecay.two_terms_le` (`Breakdown/CellReduction/InstMovedDecay.lean:361`).

**Theorem: Uniform decay over bounded phase motion.** For a bounded motion parameter, the moved key fields have one local decay coefficient uniform in time and space. Source: `Breakdown.CellReduction.Instantiation.Internal.MovedDecay.key_uniform` (`Breakdown/CellReduction/InstMovedDecay.lean:371`).

**Theorem: Extract pointwise derivative bounds.** The local ball-bound package gives the value bound, differentiability, first-derivative bound and second-derivative bound at the ball centre. Source: `Breakdown.CellReduction.Instantiation.Internal.MovedDecay.ballBound_point` (`Breakdown/CellReduction/InstMovedDecay.lean:425`).

**Theorem: Bound real-part composition of a Hessian.** Composing a complex Hessian with real-part reconstruction has norm at most the product of their operator norms. Source: `Breakdown.CellReduction.Instantiation.Internal.MovedDecay.norm_compL_realPart_le` (`Breakdown/CellReduction/InstMovedDecay.lean:437`).

**Theorem: The origin correction remains valid.** Replacing the origin correction by a valid origin profile preserves validity of the shape parameters. Source: `Breakdown.CellReduction.Instantiation.Internal.MovedDecay.withOrigin_valid` (`Breakdown/CellReduction/InstMovedDecay.lean:444`).

**Theorem: Origin and phase changes commute.** Changing the origin correction commutes with applying the moving radial phase. Source: `Breakdown.CellReduction.Instantiation.Internal.MovedDecay.withOrigin_moved` (`Breakdown/CellReduction/InstMovedDecay.lean:448`).

**Theorem: Uniform decay of the moved profile.** For bounded motion parameter, the full moved profile and its gradient and stored Hessian have uniform inverse, inverse-square and inverse-cube decay. Source: `Breakdown.CellReduction.Instantiation.Internal.MovedDecay.field_uniform` (`Breakdown/CellReduction/InstMovedDecay.lean:451`).

**Theorem: Bound an affine sum on a coefficient box.** The norm of an affine field sum is bounded by the centre bound plus the coefficient-box size times the sum of tangent bounds, all times the common weight. Source: `Breakdown.CellReduction.Instantiation.Internal.MovedDecay.affine_norm_le` (`Breakdown/CellReduction/InstMovedDecay.lean:508`).

**Theorem: Bound the phase rate on a box.** The absolute affine phase rate is at most the sum of absolute rate coefficients times the coefficient-box bound. Source: `Breakdown.CellReduction.Instantiation.Internal.MovedDecay.phaseRate_abs_le` (`Breakdown/CellReduction/InstMovedDecay.lean:523`).

**Theorem: Uniform decay on a parameter box.** The moved affine field, gradient and stored Hessian have uniform inverse-linear, inverse-square and inverse-cubic bounds on a bounded parameter box. Source: `Breakdown.CellReduction.Instantiation.movedFieldUniformDecay_holds` (`Breakdown/CellReduction/InstMovedDecay.lean:532`).

### Breakdown.CellReduction.InstMovedParams

Adding an admissible radial phase preserves the shape-parameter regularity and derivative bounds.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: The phase has three local derivatives.** The admissible radial phase is three times continuously differentiable at the stated phase variable. Source: `Breakdown.CellReduction.Instantiation.Internal.radialPhase_contDiffAt` (`Breakdown/CellReduction/InstMovedParams.lean:17`).

**Theorem: Iterated derivatives respect affine sums.** The nth derivative of f plus a times g equals the nth derivative of f plus a times the nth derivative of g. Source: `Breakdown.CellReduction.Instantiation.Internal.iteratedDeriv_combo` (`Breakdown/CellReduction/InstMovedParams.lean:21`).

**Theorem: Bound a scalar affine combination.** The absolute affine combination is bounded by the first bound plus the absolute scalar times the second bound. Source: `Breakdown.CellReduction.Instantiation.Internal.abs_combo_le` (`Breakdown/CellReduction/InstMovedParams.lean:29`).

**Theorem: Affine combinations of valid phases.** The stated affine combination of admissible radial phases remains admissible. Source: `Breakdown.CellReduction.Instantiation.Internal.radialPhase_combo` (`Breakdown/CellReduction/InstMovedParams.lean:35`).

**Theorem: Moving preserves valid parameters.** Adding a multiple of an admissible radial phase preserves validity of the shape parameters. Source: `Breakdown.CellReduction.Instantiation.movedParamsValid_holds` (`Breakdown/CellReduction/InstMovedParams.lean:67`).

### Breakdown.CellReduction.InstMovedSmooth

The moved shape field is continuously differentiable jointly in its phase parameter, time and space.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: Joint C1 regularity of a key.** The key vector is continuously differentiable jointly in time and space. Source: `Breakdown.CellReduction.Instantiation.Internal.keyVector_jointSmooth` (`Breakdown/CellReduction/InstMovedSmooth.lean:19`).

**Theorem: Joint regularity of the moved profile.** The moved shape field is continuously differentiable jointly in motion parameter, time and space. Source: `Breakdown.CellReduction.Instantiation.Internal.movedField_jointSmooth` (`Breakdown/CellReduction/InstMovedSmooth.lean:35`).

**Theorem: Joint regularity of the moved field.** The moved affine field is continuously differentiable jointly in parameters, time and space. Source: `Breakdown.CellReduction.Instantiation.movedFieldJointSmooth_holds` (`Breakdown/CellReduction/InstMovedSmooth.lean:65`).

### Breakdown.CellReduction.InstMovedSmoothFactor

Factoring the moving phase expresses the new field through two fixed shape fields and smooth scalar multipliers.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Definition: The moving radial-phase factor.** The moving factor is the unit complex exponential of the phase index times the parameter and radial phase. Source: `Breakdown.CellReduction.Instantiation.Internal.movePhase` (`Breakdown/CellReduction/InstMovedSmoothFactor.lean:17`).

**Theorem: Compose the moving phase factors.** The moving factors at parameter a minus one and parameter one multiply to the factor at parameter a. Source: `Breakdown.CellReduction.Instantiation.Internal.movePhase_sub_one_mul` (`Breakdown/CellReduction/InstMovedSmoothFactor.lean:20`).

**Theorem: Admissible phases are differentiable.** The admissible radial phase is differentiable at the stated argument. Source: `Breakdown.CellReduction.Instantiation.Internal.radialPhase_differentiableAt` (`Breakdown/CellReduction/InstMovedSmoothFactor.lean:28`).

**Theorem: The moved phase slope is affine.** The moved phase slope equals the original slope plus the motion parameter times twice radius squared times the moving phase derivative. Source: `Breakdown.CellReduction.Instantiation.Internal.phaseSlope_moved` (`Breakdown/CellReduction/InstMovedSmoothFactor.lean:33`).

**Theorem: Interpolate the reduced components.** The moved reduced components are the affine interpolation between the original and unit-moved components. Source: `Breakdown.CellReduction.Instantiation.Internal.reducedComps_moved` (`Breakdown/CellReduction/InstMovedSmoothFactor.lean:48`).

**Theorem: Factor out the moving phase.** The full phase for the moved parameters equals the original full phase times the moving phase factor. Source: `Breakdown.CellReduction.Instantiation.Internal.keyPhase_moved` (`Breakdown/CellReduction/InstMovedSmoothFactor.lean:60`).

**Theorem: Factor motion into two phased key fields.** The moved key equals the sum of the original key weighted by one minus the motion parameter and the unit-moved key weighted by that parameter, each with its corresponding moving phase. Source: `Breakdown.CellReduction.Instantiation.Internal.keyVector_moved` (`Breakdown/CellReduction/InstMovedSmoothFactor.lean:70`).

**Theorem: Moving phase is jointly differentiable.** The complex moving phase is continuously differentiable jointly in motion parameter and space. Source: `Breakdown.CellReduction.Instantiation.Internal.contDiff_movePhase` (`Breakdown/CellReduction/InstMovedSmoothFactor.lean:82`).

### Breakdown.CellReduction.InstOffsetClause

The instantiated profile and defect have the measurability and period-norm bounds needed by the offset clause.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: The origin correction remains valid.** Replacing the origin correction by a valid origin profile preserves validity of the shape parameters. Source: `Breakdown.CellReduction.Instantiation.Internal.OffsetClause.withOrigin_isShapeParams` (`Breakdown/CellReduction/InstOffsetClause.lean:21`).

**Theorem: The Laplacian trace is continuous.** Taking the trace of the second derivative is a continuous operation. Source: `Breakdown.CellReduction.Instantiation.Internal.OffsetClause.continuous_traceSecond` (`Breakdown/CellReduction/InstOffsetClause.lean:25`).

**Theorem: Regularity of the instantiated profile.** The selected parameters are valid, the certificate profile is jointly continuously differentiable, and its supplied second derivative is strongly measurable almost everywhere. Source: `Breakdown.CellReduction.Instantiation.Internal.OffsetClause.profile_contDiff` (`Breakdown/CellReduction/InstOffsetClause.lean:44`).

**Theorem: The profile defect is measurable.** The instantiated profile defect is strongly measurable almost everywhere in time and space. Source: `Breakdown.CellReduction.Instantiation.Internal.OffsetClause.defect_aestronglyMeasurable` (`Breakdown/CellReduction/InstOffsetClause.lean:64`).

**Theorem: A period-square bound controls its norm.** The prescribed nonnegative period square-integral bound gives the upper bound a for the period norm. Source: `Breakdown.CellReduction.Instantiation.Internal.OffsetClause.periodNorm_le_of_le` (`Breakdown/CellReduction/InstOffsetClause.lean:106`).

### Breakdown.CellReduction.InstOffsetIdentity

The defect expands quadratically in the parameters on the matching ball, and the ball pairing preserves that expansion.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Definition: Quadratic parameter expansion.** This proposition requires that the quantity equals a constant term plus its linear and ordered quadratic parameter terms. Source: `Breakdown.CellReduction.Instantiation.Internal.OffsetBall.QuadExpands` (`Breakdown/CellReduction/InstOffsetIdentity.lean:26`).

**Theorem: Quadratic parameter expansion.** Under the stated hypotheses, the quantity equals a constant term plus its linear and ordered quadratic parameter terms. Source: `Breakdown.CellReduction.Instantiation.Internal.OffsetBall.quadExpands_add` (`Breakdown/CellReduction/InstOffsetIdentity.lean:33`).

**Theorem: Quadratic parameter expansion.** Under the stated hypotheses, the quantity equals a constant term plus its linear and ordered quadratic parameter terms. Source: `Breakdown.CellReduction.Instantiation.Internal.OffsetBall.quadExpands_sub` (`Breakdown/CellReduction/InstOffsetIdentity.lean:41`).

**Theorem: Quadratic parameter expansion.** The quantity equals a constant term plus its linear and ordered quadratic parameter terms. Source: `Breakdown.CellReduction.Instantiation.Internal.OffsetBall.quadExpands_linear` (`Breakdown/CellReduction/InstOffsetIdentity.lean:49`).

**Theorem: Quadratic parameter expansion.** Under the stated hypotheses, the quantity equals a constant term plus its linear and ordered quadratic parameter terms. Source: `Breakdown.CellReduction.Instantiation.Internal.OffsetBall.quadExpands_map` (`Breakdown/CellReduction/InstOffsetIdentity.lean:53`).

**Theorem: Quadratic parameter expansion.** The quantity equals a constant term plus its linear and ordered quadratic parameter terms. Source: `Breakdown.CellReduction.Instantiation.Internal.OffsetBall.quadExpands_bilin` (`Breakdown/CellReduction/InstOffsetIdentity.lean:60`).

**Theorem: Quadratic parameter expansion.** Under the stated hypotheses, the quantity equals a constant term plus its linear and ordered quadratic parameter terms. Source: `Breakdown.CellReduction.Instantiation.Internal.OffsetBall.quadExpands_fderiv` (`Breakdown/CellReduction/InstOffsetIdentity.lean:110`).

**Definition: A derivative interpreted as a gradient.** The linear gradient map uses the inverse inner-product duality map. Source: `Breakdown.CellReduction.Instantiation.Internal.OffsetBall.gradMap` (`Breakdown/CellReduction/InstOffsetIdentity.lean:125`).

**Theorem: Quadratic parameter expansion.** Under the stated hypotheses, the quantity equals a constant term plus its linear and ordered quadratic parameter terms. Source: `Breakdown.CellReduction.Instantiation.Internal.OffsetBall.quadExpands_gradient` (`Breakdown/CellReduction/InstOffsetIdentity.lean:130`).

**Theorem: Quadratic parameter expansion.** Under the stated hypotheses, the quantity equals a constant term plus its linear and ordered quadratic parameter terms. Source: `Breakdown.CellReduction.Instantiation.Internal.OffsetBall.quadExpands_deriv` (`Breakdown/CellReduction/InstOffsetIdentity.lean:138`).

**Theorem: Gradients respect subtraction.** The gradient of the difference of two differentiable scalar functions is the difference of their gradients. Source: `Breakdown.CellReduction.Instantiation.Internal.OffsetBall.gradient_sub_of` (`Breakdown/CellReduction/InstOffsetIdentity.lean:146`).

**Theorem: Spatial slice of a joint derivative.** The derivative on a fixed time slice is the joint derivative restricted to the spatial direction. Source: `Breakdown.CellReduction.Instantiation.Internal.OffsetBall.joint_slice_hasFDerivAt` (`Breakdown/CellReduction/InstOffsetIdentity.lean:153`).

**Theorem: Time derivative from the joint map.** Differentiation in time is the joint derivative applied to the unit time direction. Source: `Breakdown.CellReduction.Instantiation.Internal.OffsetBall.joint_time_hasDerivAt` (`Breakdown/CellReduction/InstOffsetIdentity.lean:163`).

**Theorem: The spatial derivative is continuous.** The spatial derivative of the joint continuously differentiable field is continuous in time and space. Source: `Breakdown.CellReduction.Instantiation.Internal.OffsetBall.joint_fderiv_continuous` (`Breakdown/CellReduction/InstOffsetIdentity.lean:171`).

**Theorem: The time derivative is continuous.** The time derivative of the jointly continuously differentiable field is continuous in time and space. Source: `Breakdown.CellReduction.Instantiation.Internal.OffsetBall.joint_time_continuous` (`Breakdown/CellReduction/InstOffsetIdentity.lean:180`).

**Theorem: Spatial gradient is jointly continuous.** The scalar field's spatial gradient is continuous jointly in time and space. Source: `Breakdown.CellReduction.Instantiation.Internal.OffsetBall.joint_gradient_continuous` (`Breakdown/CellReduction/InstOffsetIdentity.lean:188`).

**Theorem: The spatial slice is differentiable.** Joint continuous differentiability gives differentiability of each spatial slice at the specified point. Source: `Breakdown.CellReduction.Instantiation.Internal.OffsetBall.joint_differentiableAt` (`Breakdown/CellReduction/InstOffsetIdentity.lean:192`).

**Theorem: The scalar time slice is differentiable.** The joint regularity of the scalar field gives differentiability of its time slice. Source: `Breakdown.CellReduction.Instantiation.Internal.OffsetBall.joint_time_differentiableAt` (`Breakdown/CellReduction/InstOffsetIdentity.lean:196`).

**Definition: Measure over a time-ball cylinder.** The cylinder measure restricts time to the closed unit interval and space to the closed ball. Source: `Breakdown.CellReduction.Instantiation.Internal.OffsetBall.boxMeasure` (`Breakdown/CellReduction/InstOffsetIdentity.lean:205`).

**Theorem: Cylinder measure is restricted volume.** The product measure on one period and a closed spatial ball equals spacetime volume restricted to their Cartesian product. Source: `Breakdown.CellReduction.Instantiation.Internal.OffsetBall.boxMeasure_eq` (`Breakdown/CellReduction/InstOffsetIdentity.lean:208`).

**Theorem: Period-ball cylinder has finite measure.** The product of the unit time interval and a finite-radius closed spatial ball has finite measure. Source: `Breakdown.CellReduction.Instantiation.Internal.OffsetBall.boxMeasure_finite` (`Breakdown/CellReduction/InstOffsetIdentity.lean:213`).

**Definition: Bounded measurable data on a ball.** This proposition requires that the field is strongly measurable almost everywhere and uniformly bounded on the period-times-ball region. Source: `Breakdown.CellReduction.Instantiation.Internal.OffsetBall.Tame` (`Breakdown/CellReduction/InstOffsetIdentity.lean:217`).

**Theorem: Bounded measurable data on a ball.** Under the stated hypotheses, the field is strongly measurable almost everywhere and uniformly bounded on the period-times-ball region. Source: `Breakdown.CellReduction.Instantiation.Internal.OffsetBall.tame_of_volume` (`Breakdown/CellReduction/InstOffsetIdentity.lean:224`).

**Theorem: Bounded measurable data on a ball.** Under the stated hypotheses, the field is strongly measurable almost everywhere and uniformly bounded on the period-times-ball region. Source: `Breakdown.CellReduction.Instantiation.Internal.OffsetBall.tame_of_continuous` (`Breakdown/CellReduction/InstOffsetIdentity.lean:230`).

**Theorem: Bounded measurable data on a ball.** Under the stated hypotheses, the field is strongly measurable almost everywhere and uniformly bounded on the period-times-ball region. Source: `Breakdown.CellReduction.Instantiation.Internal.OffsetBall.tame_add` (`Breakdown/CellReduction/InstOffsetIdentity.lean:237`).

**Theorem: Bounded measurable data on a ball.** Under the stated hypotheses, the field is strongly measurable almost everywhere and uniformly bounded on the period-times-ball region. Source: `Breakdown.CellReduction.Instantiation.Internal.OffsetBall.tame_sub` (`Breakdown/CellReduction/InstOffsetIdentity.lean:244`).

**Theorem: Bounded measurable data on a ball.** Under the stated hypotheses, the field is strongly measurable almost everywhere and uniformly bounded on the period-times-ball region. Source: `Breakdown.CellReduction.Instantiation.Internal.OffsetBall.tame_smul` (`Breakdown/CellReduction/InstOffsetIdentity.lean:251`).

**Theorem: Bounded measurable data on a ball.** The field is strongly measurable almost everywhere and uniformly bounded on the period-times-ball region. Source: `Breakdown.CellReduction.Instantiation.Internal.OffsetBall.tame_zero` (`Breakdown/CellReduction/InstOffsetIdentity.lean:257`).

**Theorem: Bounded measurable data on a ball.** Under the stated hypotheses, the field is strongly measurable almost everywhere and uniformly bounded on the period-times-ball region. Source: `Breakdown.CellReduction.Instantiation.Internal.OffsetBall.tame_sum` (`Breakdown/CellReduction/InstOffsetIdentity.lean:260`).

**Theorem: Bounded measurable data on a ball.** Under the stated hypotheses, the field is strongly measurable almost everywhere and uniformly bounded on the period-times-ball region. Source: `Breakdown.CellReduction.Instantiation.Internal.OffsetBall.tame_clm` (`Breakdown/CellReduction/InstOffsetIdentity.lean:269`).

**Theorem: Bounded measurable data on a ball.** Under the stated hypotheses, the field is strongly measurable almost everywhere and uniformly bounded on the period-times-ball region. Source: `Breakdown.CellReduction.Instantiation.Internal.OffsetBall.tame_inner` (`Breakdown/CellReduction/InstOffsetIdentity.lean:274`).

**Theorem: Integrability of cylinder pairings.** The stated continuous field pairing is integrable over the period-ball cylinder. Source: `Breakdown.CellReduction.Instantiation.Internal.OffsetBall.pairing_integrable` (`Breakdown/CellReduction/InstOffsetIdentity.lean:283`).

**Theorem: Read the ball pairing as one integral.** The period ball pairing equals the inner-product integral against the cylinder measure. Source: `Breakdown.CellReduction.Instantiation.Internal.OffsetBall.pairing_eq_integral` (`Breakdown/CellReduction/InstOffsetIdentity.lean:292`).

**Theorem: Ball pairing distributes over addition.** Adding two fields in the first argument adds their period ball pairings. Source: `Breakdown.CellReduction.Instantiation.Internal.OffsetBall.pairing_add` (`Breakdown/CellReduction/InstOffsetIdentity.lean:297`).

**Theorem: Scale a period ball pairing.** Scaling the first field by c scales its period ball pairing by c. Source: `Breakdown.CellReduction.Instantiation.Internal.OffsetBall.pairing_smul` (`Breakdown/CellReduction/InstOffsetIdentity.lean:305`).

**Theorem: Pair a finite sum on the ball.** Pairing a finite sum equals the finite sum of its period ball pairings. Source: `Breakdown.CellReduction.Instantiation.Internal.OffsetBall.pairing_sum` (`Breakdown/CellReduction/InstOffsetIdentity.lean:310`).

**Theorem: Equality on the ball preserves pairing.** Equality of the fields on the integration region preserves the period ball pairing. Source: `Breakdown.CellReduction.Instantiation.Internal.OffsetBall.pairing_congr` (`Breakdown/CellReduction/InstOffsetIdentity.lean:322`).

**Theorem: Pair the quadratic field expansion.** The period ball pairing of the constant, linear and upper-triangular quadratic field expansion equals the same polynomial in the pairings of its coefficient fields. Source: `Breakdown.CellReduction.Instantiation.Internal.OffsetBall.pairing_expand` (`Breakdown/CellReduction/InstOffsetIdentity.lean:332`).

**Definition: Trace of a second derivative.** The continuous linear trace map sums the second derivative on the three repeated coordinate directions. Source: `Breakdown.CellReduction.Instantiation.Internal.OffsetBall.traceMap` (`Breakdown/CellReduction/InstOffsetIdentity.lean:353`).

**Theorem: Read the packaged Laplacian trace.** The packaged trace map evaluates to the second-derivative trace. Source: `Breakdown.CellReduction.Instantiation.Internal.OffsetBall.traceMap_apply` (`Breakdown/CellReduction/InstOffsetIdentity.lean:357`).

**Theorem: Bounded measurable data on a ball.** The field is strongly measurable almost everywhere and uniformly bounded on the period-times-ball region. Source: `Breakdown.CellReduction.Instantiation.Internal.OffsetBall.tame_field` (`Breakdown/CellReduction/InstOffsetIdentity.lean:360`).

**Theorem: Bounded measurable data on a ball.** The field is strongly measurable almost everywhere and uniformly bounded on the period-times-ball region. Source: `Breakdown.CellReduction.Instantiation.Internal.OffsetBall.tame_time` (`Breakdown/CellReduction/InstOffsetIdentity.lean:364`).

**Theorem: Bounded measurable data on a ball.** Under the stated hypotheses, the field is strongly measurable almost everywhere and uniformly bounded on the period-times-ball region. Source: `Breakdown.CellReduction.Instantiation.Internal.OffsetBall.tame_fderiv_apply` (`Breakdown/CellReduction/InstOffsetIdentity.lean:368`).

**Theorem: Bounded measurable data on a ball.** The field is strongly measurable almost everywhere and uniformly bounded on the period-times-ball region. Source: `Breakdown.CellReduction.Instantiation.Internal.OffsetBall.tame_fderiv_self` (`Breakdown/CellReduction/InstOffsetIdentity.lean:373`).

**Theorem: Bounded measurable data on a ball.** The field is strongly measurable almost everywhere and uniformly bounded on the period-times-ball region. Source: `Breakdown.CellReduction.Instantiation.Internal.OffsetBall.tame_gradient_smooth` (`Breakdown/CellReduction/InstOffsetIdentity.lean:377`).

**Theorem: Bounded measurable data on a ball.** Under the stated hypotheses, the field is strongly measurable almost everywhere and uniformly bounded on the period-times-ball region. Source: `Breakdown.CellReduction.Instantiation.Internal.OffsetBall.tame_secondDerivTrace` (`Breakdown/CellReduction/InstOffsetIdentity.lean:381`).

**Theorem: Bounded measurable data on a ball.** Under the stated hypotheses, the field is strongly measurable almost everywhere and uniformly bounded on the period-times-ball region. Source: `Breakdown.CellReduction.Instantiation.Internal.OffsetBall.tame_pressure` (`Breakdown/CellReduction/InstOffsetIdentity.lean:394`).

**Definition: Profile centre with origin correction.** The centre field reads the stored centre shape with its own origin correction. Source: `Breakdown.CellReduction.Instantiation.Internal.OffsetBall.cField` (`Breakdown/CellReduction/InstOffsetIdentity.lean:419`).

**Definition: Profile tangent with origin correction.** Each tangent field reads its stored shape with that tangent's origin correction. Source: `Breakdown.CellReduction.Instantiation.Internal.OffsetBall.tField` (`Breakdown/CellReduction/InstOffsetIdentity.lean:422`).

**Definition: Affine centre and tangent field.** The base field is the centre plus the parameter-weighted sum of tangent fields. Source: `Breakdown.CellReduction.Instantiation.Internal.OffsetBall.baseField` (`Breakdown/CellReduction/InstOffsetIdentity.lean:425`).

**Definition: Regular centre and tangent fields.** This proposition requires that the centre and every tangent field are jointly continuously differentiable in time and space. Source: `Breakdown.CellReduction.Instantiation.Internal.OffsetBall.BaseSmooth` (`Breakdown/CellReduction/InstOffsetIdentity.lean:428`).

**Definition: Evaluation as a bilinear map.** The bilinear map evaluates a linear operator on a vector. Source: `Breakdown.CellReduction.Instantiation.Internal.OffsetBall.applyRight` (`Breakdown/CellReduction/InstOffsetIdentity.lean:432`).

**Definition: Half the Euclidean pairing.** The bilinear form is one half of the Euclidean inner product. Source: `Breakdown.CellReduction.Instantiation.Internal.OffsetBall.halfInner` (`Breakdown/CellReduction/InstOffsetIdentity.lean:436`).

**Theorem: Quadratic parameter expansion.** Under the stated hypotheses, the quantity equals a constant term plus its linear and ordered quadratic parameter terms. Source: `Breakdown.CellReduction.Instantiation.Internal.OffsetBall.quadExpands_of_eq` (`Breakdown/CellReduction/InstOffsetIdentity.lean:441`).

**Theorem: The zero scalar has zero gradient.** The gradient of the zero scalar function is zero. Source: `Breakdown.CellReduction.Instantiation.Internal.OffsetBall.gradient_zero_fun` (`Breakdown/CellReduction/InstOffsetIdentity.lean:448`).

**Theorem: Differentiate the base affine field.** The derivative of the base affine field is the centre derivative plus the coefficient-weighted sum of tangent derivatives. Source: `Breakdown.CellReduction.Instantiation.Internal.OffsetBall.baseField_fderiv` (`Breakdown/CellReduction/InstOffsetIdentity.lean:453`).

**Theorem: The base affine field is differentiable.** The valid centre and tangent data make the base affine field spatially differentiable. Source: `Breakdown.CellReduction.Instantiation.Internal.OffsetBall.baseField_differentiableAt` (`Breakdown/CellReduction/InstOffsetIdentity.lean:461`).

**Theorem: Quadratic parameter expansion.** Under the stated hypotheses, the quantity equals a constant term plus its linear and ordered quadratic parameter terms. Source: `Breakdown.CellReduction.Instantiation.Internal.OffsetBall.time_expands` (`Breakdown/CellReduction/InstOffsetIdentity.lean:467`).

**Theorem: Quadratic parameter expansion.** The quantity equals a constant term plus its linear and ordered quadratic parameter terms. Source: `Breakdown.CellReduction.Instantiation.Internal.OffsetBall.half_expands` (`Breakdown/CellReduction/InstOffsetIdentity.lean:491`).

**Theorem: Quadratic parameter expansion.** Under the stated hypotheses, the quantity equals a constant term plus its linear and ordered quadratic parameter terms. Source: `Breakdown.CellReduction.Instantiation.Internal.OffsetBall.halfDeriv_expands` (`Breakdown/CellReduction/InstOffsetIdentity.lean:503`).

**Theorem: Quadratic parameter expansion.** The quantity equals a constant term plus its linear and ordered quadratic parameter terms. Source: `Breakdown.CellReduction.Instantiation.Internal.OffsetBall.trace_expands` (`Breakdown/CellReduction/InstOffsetIdentity.lean:517`).

**Theorem: Quadratic parameter expansion.** Under the stated hypotheses, the quantity equals a constant term plus its linear and ordered quadratic parameter terms. Source: `Breakdown.CellReduction.Instantiation.Internal.OffsetBall.advection_expands` (`Breakdown/CellReduction/InstOffsetIdentity.lean:528`).

**Theorem: Quadratic parameter expansion.** The quantity equals a constant term plus its linear and ordered quadratic parameter terms. Source: `Breakdown.CellReduction.Instantiation.Internal.OffsetBall.actuator_expands` (`Breakdown/CellReduction/InstOffsetIdentity.lean:542`).

**Theorem: Halving preserves differentiability.** A differentiable real function remains differentiable after division by two. Source: `Breakdown.CellReduction.Instantiation.Internal.OffsetBall.differentiableAt_half` (`Breakdown/CellReduction/InstOffsetIdentity.lean:550`).

**Theorem: Quadratic parameter expansion.** Under the stated hypotheses, the quantity equals a constant term plus its linear and ordered quadratic parameter terms. Source: `Breakdown.CellReduction.Instantiation.Internal.OffsetBall.pressure_expands` (`Breakdown/CellReduction/InstOffsetIdentity.lean:554`).

**Theorem: The origin correction remains valid.** Replacing the origin correction by a valid origin profile preserves validity of the shape parameters. Source: `Breakdown.CellReduction.Instantiation.Internal.OffsetBall.originParams_valid` (`Breakdown/CellReduction/InstOffsetIdentity.lean:595`).

**Theorem: Regular centre and tangent fields.** Under the stated hypotheses, the centre and every tangent field are jointly continuously differentiable in time and space. Source: `Breakdown.CellReduction.Instantiation.Internal.OffsetBall.baseSmooth_of` (`Breakdown/CellReduction/InstOffsetIdentity.lean:599`).

**Theorem: Quadratic parameter expansion.** Under the stated hypotheses, the quantity equals a constant term plus its linear and ordered quadratic parameter terms. Source: `Breakdown.CellReduction.Instantiation.Internal.OffsetBall.defect_expands` (`Breakdown/CellReduction/InstOffsetIdentity.lean:606`).

**Theorem: Symmetrize the quadratic coefficient.** Diagonal quadratic coefficients use one ordered term, while off-diagonal coefficients add the two orders of their index pair. Source: `Breakdown.CellReduction.Instantiation.Internal.OffsetBall.quadCoeff_apply` (`Breakdown/CellReduction/InstOffsetIdentity.lean:701`).

**Theorem: Quadratic offset pairing on a ball.** Under the stated hypotheses, the defect pairing on the matching ball equals its constant, linear and symmetrized quadratic parameter contributions. Source: `Breakdown.CellReduction.Instantiation.offsetBallIdentity_of` (`Breakdown/CellReduction/InstOffsetIdentity.lean:713`).
<!-- /passage:sec-breakdown-cellreduction -->

