
<!-- passage:front -->
# Library guide 2: Breakdown/CellReduction

**Navier–Stokes pages:** [the paper](../navier-stokes-paper/paper.pdf) · [proof routes](../navier-stokes-routes/paper.md) · [routes in detail](../navier-stokes-route-details/paper.md) · library guide: [1](../navier-stokes-library-01/paper.md) **2** [3](../navier-stokes-library-03/paper.md) [4](../navier-stokes-library-04/paper.md) [5](../navier-stokes-library-05/paper.md) [6](../navier-stokes-library-06/paper.md) [7](../navier-stokes-library-07/paper.md) [8](../navier-stokes-library-08/paper.md) [9](../navier-stokes-library-09/paper.md) [10](../navier-stokes-library-10/paper.md) [11](../navier-stokes-library-11/paper.md) [12](../navier-stokes-library-12/paper.md) [13](../navier-stokes-library-13/paper.md) [14](../navier-stokes-library-14/paper.md) [15](../navier-stokes-library-15/paper.md) [16](../navier-stokes-library-16/paper.md) [17](../navier-stokes-library-17/paper.md) [18](../navier-stokes-library-18/paper.md) [19](../navier-stokes-library-19/paper.md) [20](../navier-stokes-library-20/paper.md) [21](../navier-stokes-library-21/paper.md) [22](../navier-stokes-library-22/paper.md) [23](../navier-stokes-library-23/paper.md) [24](../navier-stokes-library-24/paper.md) [25](../navier-stokes-library-25/paper.md) [26](../navier-stokes-library-26/paper.md) [27](../navier-stokes-library-27/paper.md) [28](../navier-stokes-library-28/paper.md) [29](../navier-stokes-library-29/paper.md) [30](../navier-stokes-library-30/paper.md)

*A plain title and a sentence for each declaration in `Breakdown.CellReduction.InstParamsBounded` to `Breakdown.CellReduction.StrainTerm` of Alpöge and Buckmaster's Lean at `ad53419de079eb8f95f60313473374624a348546`, in the authors' file order. Prepared with AI assistance. The authors have not reviewed it.*

Each paragraph names one declaration and says whether it is a definition, a proposition that the library defines (its name usually ends in `Holds` or `Statement`) or a proved result, then what it states. Click a paragraph to open its Lean on the right.

### Breakdown.CellReduction.InstParamsBounded

Nonzero coordinate scales make the certificate parameter set bounded in every coordinate.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: The parameter coordinates are bounded.** Nonzero coordinate scales give one finite bound for every coordinate in the certificate parameter set. Source: `Breakdown.CellReduction.Instantiation.paramsBounded_holds` (`Breakdown/CellReduction/InstParamsBounded.lean:14`).

### Breakdown.CellReduction.InstPinContinuous

The period pairing of a profile gradient with a fixed pin is continuous in the parameters.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: Matrix square norm is nonnegative.** The sum of the squared matrix-column norms is nonnegative. Source: `Breakdown.CellReduction.Instantiation.Internal.columnSquares_nonneg_aux` (`Breakdown/CellReduction/InstPinContinuous.lean:16`).

**Theorem: The matrix square norm is continuous.** The sum of the squared matrix-column norms depends continuously on the matrix. Source: `Breakdown.CellReduction.Instantiation.Internal.continuous_columnSquares_aux` (`Breakdown/CellReduction/InstPinContinuous.lean:19`).

**Theorem: The matrix pairing is continuous.** The matrix inner product is continuous in both matrix arguments. Source: `Breakdown.CellReduction.Instantiation.Internal.continuous_columnPairing_aux` (`Breakdown/CellReduction/InstPinContinuous.lean:22`).

**Theorem: Bound by the two matrix squares.** The absolute matrix pairing is bounded by half the sum of the two matrix column-square sums. Source: `Breakdown.CellReduction.Instantiation.Internal.abs_columnPairing_le_half` (`Breakdown/CellReduction/InstPinContinuous.lean:27`).

**Theorem: Column squares versus operator norm.** The matrix column-square sum is at most three times the squared operator norm. Source: `Breakdown.CellReduction.Instantiation.Internal.columnSquares_le_three_mul` (`Breakdown/CellReduction/InstPinContinuous.lean:40`).

**Definition: Insert a spatial slice.** The spatial inclusion inserts zeros in the parameter and time directions. Source: `Breakdown.CellReduction.Instantiation.Internal.sliceInclusion` (`Breakdown/CellReduction/InstPinContinuous.lean:53`).

**Definition: The joint parameter-time field.** The joint field reads the parameter, time and space coordinates from a single product argument. Source: `Breakdown.CellReduction.Instantiation.Internal.jointField` (`Breakdown/CellReduction/InstPinContinuous.lean:56`).

**Definition: Pin pairing on one slice.** The slice integrand pairs the spatial part of the joint field derivative with the pin matrix. Source: `Breakdown.CellReduction.Instantiation.Internal.slicePairing` (`Breakdown/CellReduction/InstPinContinuous.lean:59`).

**Theorem: Read the derivative of a spatial slice.** The spatial derivative of the slice is the joint derivative composed with the spatial inclusion. Source: `Breakdown.CellReduction.Instantiation.Internal.fderiv_slice_eq` (`Breakdown/CellReduction/InstPinContinuous.lean:63`).

**Theorem: Continuity of the pin functional.** Joint profile regularity and uniform decay make its pairing with a fixed square-integrable pin continuous on the parameter set. Source: `Breakdown.CellReduction.Instantiation.pinValueContinuous_holds` (`Breakdown/CellReduction/InstPinContinuous.lean:75`).

### Breakdown.CellReduction.InstPressureRegular

Radial weights cancel the coordinate singularities sufficiently to give continuous pressure with uniform spatial Lipschitz bounds on balls.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: Compare normalized vectors.** The normalized-vector difference times the second scale is bounded by the original vector difference plus the difference of the two scales. Source: `Breakdown.CellReduction.Instantiation.Internal.scaled_sub_le` (`Breakdown/CellReduction/InstPressureRegular.lean:21`).

**Definition: Radius-weighted Lipschitz bound.** This proposition requires that the difference of field values times the second point's radius is bounded by a constant times the distance between the points. Source: `Breakdown.CellReduction.Instantiation.Internal.ScaleSlope` (`Breakdown/CellReduction/InstPressureRegular.lean:52`).

**Theorem: Radius-weighted Lipschitz bound.** Under the stated hypotheses, the difference of field values times the second point's radius is bounded by a constant times the distance between the points. Source: `Breakdown.CellReduction.Instantiation.Internal.scaleSlope_of_ne` (`Breakdown/CellReduction/InstPressureRegular.lean:55`).

**Theorem: Radius-weighted Lipschitz bound.** Under the stated hypotheses, the difference of field values times the second point's radius is bounded by a constant times the distance between the points. Source: `Breakdown.CellReduction.Instantiation.Internal.scaleSlope_mono` (`Breakdown/CellReduction/InstPressureRegular.lean:70`).

**Theorem: Radius-weighted Lipschitz bound.** The difference of field values times the second point's radius is bounded by a constant times the distance between the points. Source: `Breakdown.CellReduction.Instantiation.Internal.scaleSlope_mul` (`Breakdown/CellReduction/InstPressureRegular.lean:74`).

**Theorem: Radius-weighted Lipschitz bound.** Under the stated hypotheses, the difference of field values times the second point's radius is bounded by a constant times the distance between the points. Source: `Breakdown.CellReduction.Instantiation.Internal.scaleSlope_of_slopeBound` (`Breakdown/CellReduction/InstPressureRegular.lean:96`).

**Theorem: Vanishing offsets a scaled slope.** The boundedness, scaled-slope and vanishing hypotheses give a finite Lipschitz bound for the product. Source: `Breakdown.CellReduction.Instantiation.Internal.slopeBound_mul_of_vanish` (`Breakdown/CellReduction/InstPressureRegular.lean:106`).

**Theorem: Products of bounded Lipschitz fields.** The product of the two bounded Lipschitz fields has a finite Lipschitz constant on the specified set. Source: `Breakdown.CellReduction.Instantiation.Internal.slopeBound_mul` (`Breakdown/CellReduction/InstPressureRegular.lean:136`).

**Theorem: A Lipschitz field is bounded on a ball.** A Lipschitz field on the closed ball has one nonnegative bound for its norm there. Source: `Breakdown.CellReduction.Instantiation.Internal.bound_of_slopeBound` (`Breakdown/CellReduction/InstPressureRegular.lean:157`).

**Theorem: Regularity gives a local Lipschitz bound.** The continuously differentiable field has a finite Lipschitz bound on the prescribed bounded region. Source: `Breakdown.CellReduction.Instantiation.Internal.slopeBound_of_contDiff` (`Breakdown/CellReduction/InstPressureRegular.lean:171`).

**Theorem: Local Lipschitz bounds give continuity.** Lipschitz bounds on every ball imply continuity of the field. Source: `Breakdown.CellReduction.Instantiation.Internal.continuous_of_ball_slopes` (`Breakdown/CellReduction/InstPressureRegular.lean:183`).

**Theorem: The compactified radius is nonnegative.** For valid shape parameters, the compactified radius is nonnegative. Source: `Breakdown.CellReduction.Instantiation.Internal.chartCoord_nonneg` (`Breakdown/CellReduction/InstPressureRegular.lean:190`).

**Theorem: The compactified radius is at most one.** For valid shape parameters, the compactified radius is at most one. Source: `Breakdown.CellReduction.Instantiation.Internal.chartCoord_le_one` (`Breakdown/CellReduction/InstPressureRegular.lean:193`).

**Theorem: Chart radius is at most scaled radius.** The compactified radius is bounded by physical radius divided by chart length. Source: `Breakdown.CellReduction.Instantiation.Internal.chartCoord_le_norm` (`Breakdown/CellReduction/InstPressureRegular.lean:198`).

**Theorem: Difference bound for compactified radii.** The difference of compactified radii is at most spatial distance divided by chart length. Source: `Breakdown.CellReduction.Instantiation.Internal.chartCoord_dist` (`Breakdown/CellReduction/InstPressureRegular.lean:203`).

**Theorem: The radial chart is globally Lipschitz.** The compactified radial coordinate is Lipschitz with constant one over the positive chart length. Source: `Breakdown.CellReduction.Instantiation.Internal.chartCoord_slopeBound` (`Breakdown/CellReduction/InstPressureRegular.lean:222`).

**Theorem: A coordinate is bounded by the norm.** The absolute value of the selected coordinate is bounded by the vector norm. Source: `Breakdown.CellReduction.Instantiation.Internal.abs_coord_le` (`Breakdown/CellReduction/InstPressureRegular.lean:229`).

**Theorem: Normalized height has size at most one.** The absolute normalized height is at most one. Source: `Breakdown.CellReduction.Instantiation.Internal.abs_heightRatio_le_one` (`Breakdown/CellReduction/InstPressureRegular.lean:233`).

**Theorem: A weighted normalized-height bound.** The normalized-height difference times the second radius is at most twice the spatial distance. Source: `Breakdown.CellReduction.Instantiation.Internal.heightRatio_slope` (`Breakdown/CellReduction/InstPressureRegular.lean:240`).

**Definition: Horizontal complex coordinate.** The horizontal coordinate is the first real coordinate plus i times the second. Source: `Breakdown.CellReduction.Instantiation.Internal.planeVec` (`Breakdown/CellReduction/InstPressureRegular.lean:253`).

**Theorem: Square norm of the horizontal coordinate.** The horizontal complex coordinate has squared norm equal to the sum of the first two coordinate squares. Source: `Breakdown.CellReduction.Instantiation.Internal.planeVec_sq` (`Breakdown/CellReduction/InstPressureRegular.lean:255`).

**Theorem: Square norm as three coordinate squares.** The squared Euclidean norm equals the sum of the three coordinate squares. Source: `Breakdown.CellReduction.Instantiation.Internal.norm_sq_three` (`Breakdown/CellReduction/InstPressureRegular.lean:258`).

**Theorem: Horizontal norm is bounded by full norm.** The norm of the horizontal complex coordinate is bounded by the full spatial norm. Source: `Breakdown.CellReduction.Instantiation.Internal.planeVec_le` (`Breakdown/CellReduction/InstPressureRegular.lean:261`).

**Theorem: Subtract horizontal projections.** The difference of the horizontal complex coordinates equals the horizontal coordinate of the difference. Source: `Breakdown.CellReduction.Instantiation.Internal.planeVec_sub` (`Breakdown/CellReduction/InstPressureRegular.lean:266`).

**Definition: Horizontal coordinate divided by radius.** The normalized horizontal coordinate divides the horizontal complex coordinate by the full spatial radius. Source: `Breakdown.CellReduction.Instantiation.Internal.unitPlane` (`Breakdown/CellReduction/InstPressureRegular.lean:270`).

**Theorem: Normalized horizontal part is bounded.** The normalized horizontal complex coordinate has norm at most one. Source: `Breakdown.CellReduction.Instantiation.Internal.unitPlane_le` (`Breakdown/CellReduction/InstPressureRegular.lean:272`).

**Theorem: A weighted horizontal-coordinate bound.** The normalized horizontal difference times the second radius is at most twice the spatial distance. Source: `Breakdown.CellReduction.Instantiation.Internal.unitPlane_slope` (`Breakdown/CellReduction/InstPressureRegular.lean:279`).

**Theorem: The complementary height square.** One minus the squared normalized height equals the squared norm of the normalized horizontal coordinate. Source: `Breakdown.CellReduction.Instantiation.Internal.one_sub_heightRatio_sq` (`Breakdown/CellReduction/InstPressureRegular.lean:290`).

**Theorem: The point angle is the complex argument.** The azimuthal angle equals the argument of the normalized horizontal complex coordinate. Source: `Breakdown.CellReduction.Instantiation.Internal.pointAngle_eq_arg` (`Breakdown/CellReduction/InstPressureRegular.lean:299`).

**Definition: Angular mode with axis vanishing.** The angular factor multiplies the azimuthal exponential by a power of one minus height squared. Source: `Breakdown.CellReduction.Instantiation.Internal.angleAxis` (`Breakdown/CellReduction/InstPressureRegular.lean:304`).

**Definition: Angular mode on the complex disc.** The disc factor multiplies the complex argument phase by the prescribed power of its squared norm. Source: `Breakdown.CellReduction.Instantiation.Internal.angleDisc` (`Breakdown/CellReduction/InstPressureRegular.lean:307`).

**Theorem: The disc form of the axis factor.** The spatial angular-axis factor is the disc factor evaluated on the normalized horizontal complex coordinate. Source: `Breakdown.CellReduction.Instantiation.Internal.angleAxis_eq` (`Breakdown/CellReduction/InstPressureRegular.lean:310`).

**Theorem: Lipschitz bound for bounded powers.** For the stated unit-disc inputs, the difference of nth powers is at most n times the difference of the inputs. Source: `Breakdown.CellReduction.Instantiation.Internal.norm_pow_sub_pow_le` (`Breakdown/CellReduction/InstPressureRegular.lean:314`).

**Theorem: Integer powers on the unit circle.** The difference of integer powers of unit complex numbers is at most absolute exponent times their distance. Source: `Breakdown.CellReduction.Instantiation.Internal.norm_zpow_sub_zpow_le` (`Breakdown/CellReduction/InstPressureRegular.lean:329`).

**Theorem: Express an angular phase as a power.** The integer-frequency exponential of a nonzero complex argument equals the corresponding power of its normalized complex value. Source: `Breakdown.CellReduction.Instantiation.Internal.exp_arg_eq` (`Breakdown/CellReduction/InstPressureRegular.lean:341`).

**Theorem: Bound normalization away from zero.** The difference of normalized nonzero complex numbers times the second norm is at most twice their original distance. Source: `Breakdown.CellReduction.Instantiation.Internal.unit_div_slope` (`Breakdown/CellReduction/InstPressureRegular.lean:352`).

**Theorem: Complex normalization gives norm one.** Dividing a nonzero complex number by its norm gives norm one. Source: `Breakdown.CellReduction.Instantiation.Internal.norm_unit_div` (`Breakdown/CellReduction/InstPressureRegular.lean:361`).

**Theorem: Lipschitz bound for the disc factor.** The disc angular factor has difference bounded by (2a+2|M|+2) times the input distance. Source: `Breakdown.CellReduction.Instantiation.Internal.angleDisc_slope` (`Breakdown/CellReduction/InstPressureRegular.lean:365`).

**Theorem: Angular-axis factor has norm at most one.** The angular-axis factor has norm at most one. Source: `Breakdown.CellReduction.Instantiation.Internal.angleAxis_bound` (`Breakdown/CellReduction/InstPressureRegular.lean:427`).

**Theorem: The angular-axis factor has scaled slope.** One nonnegative constant controls the angular-axis factor's radius-weighted difference bound throughout space. Source: `Breakdown.CellReduction.Instantiation.Internal.angleAxis_slope` (`Breakdown/CellReduction/InstPressureRegular.lean:435`).

**Definition: An integer temporal phase.** The temporal factor is the unit complex exponential for an integer frequency over one time period. Source: `Breakdown.CellReduction.Instantiation.Internal.timeFactor` (`Breakdown/CellReduction/InstPressureRegular.lean:454`).

**Theorem: The oscillatory factor has unit norm.** The stated complex oscillatory factor has norm one. Source: `Breakdown.CellReduction.Instantiation.Internal.timeFactor_norm` (`Breakdown/CellReduction/InstPressureRegular.lean:456`).

**Theorem: The integer phase is periodic.** An integer temporal frequency makes the complex phase invariant under a unit time shift. Source: `Breakdown.CellReduction.Instantiation.Internal.timeFactor_periodic` (`Breakdown/CellReduction/InstPressureRegular.lean:458`).

**Theorem: The temporal phase is continuous.** The integer temporal phase depends continuously on time. Source: `Breakdown.CellReduction.Instantiation.Internal.timeFactor_continuous` (`Breakdown/CellReduction/InstPressureRegular.lean:465`).

**Definition: A radial oscillatory factor.** The radial factor is the complex exponential of the phase index times the phase evaluated at radius squared. Source: `Breakdown.CellReduction.Instantiation.Internal.radFactor` (`Breakdown/CellReduction/InstPressureRegular.lean:469`).

**Theorem: The oscillatory factor has unit norm.** The stated complex oscillatory factor has norm one. Source: `Breakdown.CellReduction.Instantiation.Internal.radFactor_norm` (`Breakdown/CellReduction/InstPressureRegular.lean:472`).

**Theorem: Radial phase factor is differentiable.** The admissible radial complex phase factor is continuously differentiable. Source: `Breakdown.CellReduction.Instantiation.Internal.radFactor_contDiff` (`Breakdown/CellReduction/InstPressureRegular.lean:475`).

**Theorem: The radial phase is Lipschitz on balls.** The radial complex phase factor has a finite Lipschitz constant on every prescribed closed ball. Source: `Breakdown.CellReduction.Instantiation.Internal.radFactor_slopeBound` (`Breakdown/CellReduction/InstPressureRegular.lean:484`).

**Definition: The radial endpoint weight in space.** The spatial weight evaluates the inner and outer endpoint polynomial at the compactified radius. Source: `Breakdown.CellReduction.Instantiation.Internal.weightAt` (`Breakdown/CellReduction/InstPressureRegular.lean:488`).

**Theorem: The radial weight is globally Lipschitz.** The compactified radial weight has a finite global Lipschitz constant. Source: `Breakdown.CellReduction.Instantiation.Internal.weightAt_slopeBound` (`Breakdown/CellReduction/InstPressureRegular.lean:490`).

**Theorem: The radial weight is bounded by one.** The complex radial weight has norm at most one. Source: `Breakdown.CellReduction.Instantiation.Internal.weightAt_bound` (`Breakdown/CellReduction/InstPressureRegular.lean:499`).

**Theorem: Radial weight vanishes at least linearly.** The radial weight norm is bounded by spatial radius divided by the chart length. Source: `Breakdown.CellReduction.Instantiation.Internal.weightAt_vanish` (`Breakdown/CellReduction/InstPressureRegular.lean:510`).

**Definition: Spline in compactified coordinates.** The spatial spline reads the compactified radius and normalized height. Source: `Breakdown.CellReduction.Instantiation.Internal.splineAt` (`Breakdown/CellReduction/InstPressureRegular.lean:521`).

**Theorem: Joined spline values are continuous.** The joined bivariate spline evaluation is continuous. Source: `Breakdown.CellReduction.Instantiation.Internal.spline_continuous` (`Breakdown/CellReduction/InstPressureRegular.lean:523`).

**Theorem: A spline is Lipschitz on its box.** On the unit coordinate box, the spline difference is bounded by one constant times the sum of coordinate differences. Source: `Breakdown.CellReduction.Instantiation.Internal.spline_box` (`Breakdown/CellReduction/InstPressureRegular.lean:527`).

**Theorem: A spline is bounded on its box.** One nonnegative constant bounds the spline norm on the unit coordinate box. Source: `Breakdown.CellReduction.Instantiation.Internal.spline_bounded` (`Breakdown/CellReduction/InstPressureRegular.lean:534`).

**Theorem: The compactified radius is at most one.** The absolute compactified radius is at most one. Source: `Breakdown.CellReduction.Instantiation.Internal.chartCoord_abs_le` (`Breakdown/CellReduction/InstPressureRegular.lean:538`).

**Theorem: The spatial spline amplitude is bounded.** Composing the spline with the radial-height chart gives a globally bounded spatial amplitude. Source: `Breakdown.CellReduction.Instantiation.Internal.splineAt_bound` (`Breakdown/CellReduction/InstPressureRegular.lean:541`).

**Theorem: Charted spline has a scaled local slope.** The charted spline has one nonnegative scaled-slope constant on the prescribed closed ball. Source: `Breakdown.CellReduction.Instantiation.Internal.splineAt_slope` (`Breakdown/CellReduction/InstPressureRegular.lean:546`).

**Theorem: Every interior radial knot is positive.** Every radial knot remaining after removal of the endpoints is strictly positive. Source: `Breakdown.CellReduction.Instantiation.Internal.inner_breaks_pos` (`Breakdown/CellReduction/InstPressureRegular.lean:566`).

**Theorem: A finite positive list has a lower bound.** A finite list of positive numbers has a common strictly positive lower bound. Source: `Breakdown.CellReduction.Instantiation.Internal.exists_pos_le_all` (`Breakdown/CellReduction/InstPressureRegular.lean:578`).

**Theorem: Positive cell indices exclude zero.** One positive threshold bounds below every coordinate whose cell index is at least one. Source: `Breakdown.CellReduction.Instantiation.Internal.cellIndex_pos_bound` (`Breakdown/CellReduction/InstPressureRegular.lean:588`).

**Theorem: The origin belongs to the first cell.** The cell index of zero is zero. Source: `Breakdown.CellReduction.Instantiation.Internal.cellIndex_at_zero` (`Breakdown/CellReduction/InstPressureRegular.lean:597`).

**Theorem: The selected cell index is valid.** The selected cell index is strictly below the number of cells. Source: `Breakdown.CellReduction.Instantiation.Internal.cellIndex_lt_cellCount` (`Breakdown/CellReduction/InstPressureRegular.lean:603`).

**Theorem: Evaluate a constant polynomial row.** At radial coordinate zero, the polynomial row evaluates to the constant c. Source: `Breakdown.CellReduction.Instantiation.Internal.row_value` (`Breakdown/CellReduction/InstPressureRegular.lean:617`).

**Theorem: Constant row has zero height derivative.** The height derivative of the constant radial-zero polynomial row evaluates to zero. Source: `Breakdown.CellReduction.Instantiation.Internal.row_deriv_zero` (`Breakdown/CellReduction/InstPressureRegular.lean:624`).

**Theorem: Spline inherits its constant inner row.** At radial coordinate zero, the spline equals the constant c for every height. Source: `Breakdown.CellReduction.Instantiation.Internal.spline_row_value` (`Breakdown/CellReduction/InstPressureRegular.lean:632`).

**Theorem: The height slope gains a radial factor.** The spline's height difference is bounded by C times the radial coordinate times the height difference. Source: `Breakdown.CellReduction.Instantiation.Internal.spline_xslope` (`Breakdown/CellReduction/InstPressureRegular.lean:642`).

**Theorem: A constant row gives a Lipschitz field.** The constant inner-row condition makes the charted spline globally Lipschitz. Source: `Breakdown.CellReduction.Instantiation.Internal.splineAt_slopeBound_of_row` (`Breakdown/CellReduction/InstPressureRegular.lean:699`).

**Theorem: A zero inner row gives linear vanishing.** The charted spline norm is bounded by a constant times spatial radius. Source: `Breakdown.CellReduction.Instantiation.Internal.splineAt_vanish` (`Breakdown/CellReduction/InstPressureRegular.lean:740`).

**Definition: The spatial pressure amplitude.** The spatial pressure factor multiplies the radial phase, angular factor, endpoint weight and spline value. Source: `Breakdown.CellReduction.Instantiation.Internal.spaceValue` (`Breakdown/CellReduction/InstPressureRegular.lean:756`).

**Theorem: Separate time from a pressure key.** Each pressure key value is its temporal phase times its spatial amplitude. Source: `Breakdown.CellReduction.Instantiation.Internal.pressureKeyValue_split` (`Breakdown/CellReduction/InstPressureRegular.lean:761`).

**Theorem: Local Lipschitz pressure amplitudes.** The spatial pressure-key amplitude has a finite Lipschitz bound on every prescribed closed ball. Source: `Breakdown.CellReduction.Instantiation.Internal.spaceValue_slopeBound` (`Breakdown/CellReduction/InstPressureRegular.lean:767`).

**Theorem: Regularity of the shape pressure.** Valid pressure shapes give a continuous periodic pressure with a common spatial Lipschitz constant on each ball. Source: `Breakdown.CellReduction.Instantiation.pressureFieldRegular_holds` (`Breakdown/CellReduction/InstPressureRegular.lean:835`).

### Breakdown.CellReduction.InstProfilePieces

The centre and tangent pieces remain admissible flow pieces uniformly on a bounded parameter box.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: Opposite tangent coefficients cancel.** The two identical tangent fields with coefficients s and minus s cancel, leaving the centre shape field. Source: `Breakdown.CellReduction.Instantiation.Internal.pairField_eq` (`Breakdown/CellReduction/InstProfilePieces.lean:17`).

**Theorem: Two phase coordinates recover the rate.** Pairing phase rates one and minus one with coordinates a/2 and minus a/2 gives a. Source: `Breakdown.CellReduction.Instantiation.Internal.pairRate_eq` (`Breakdown/CellReduction/InstProfilePieces.lean:22`).

**Theorem: The paired coordinates stay bounded.** When |a| is at most A, each of the two coordinates a/2 and minus a/2 has absolute value at most A/2. Source: `Breakdown.CellReduction.Instantiation.Internal.pairCoord_le` (`Breakdown/CellReduction/InstProfilePieces.lean:25`).

**Theorem: Bound the rate on a coefficient box.** The absolute phase rate is at most the sum of absolute rate coefficients times the common coordinate bound M. Source: `Breakdown.CellReduction.Instantiation.Internal.phaseRate_abs_le` (`Breakdown/CellReduction/InstProfilePieces.lean:32`).

**Theorem: Uniform flow bounds for moved profiles.** For bounded motion parameter, a common threshold makes every larger bound certify all moved profiles as admissible flow pieces. Source: `Breakdown.CellReduction.Instantiation.Internal.movedPiece_flow` (`Breakdown/CellReduction/InstProfilePieces.lean:41`).

**Theorem: Uniform bounds for profile pieces.** Under the stated hypotheses, the centre and tangent pieces are admissible flow pieces with one bound on every bounded parameter box. Source: `Breakdown.CellReduction.Instantiation.profilePiecesFlow_of` (`Breakdown/CellReduction/InstProfilePieces.lean:70`).

### Breakdown.CellReduction.InstProfileSplit

The stored profile is identified with its centre field plus the parameter-weighted tangent fields.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: Split the instantiated profile.** The instantiated profile equals the centre field plus the parameter-weighted tangent fields. Source: `Breakdown.CellReduction.Instantiation.profileSplit_holds` (`Breakdown/CellReduction/InstProfileSplit.lean:13`).

### Breakdown.CellReduction.InstScalarGradient

Locally Lipschitz scalar gradients vanish against compactly supported divergence-free test fields.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: A common support ball for all slices.** Compact spacetime support supplies one radius beyond which every spatial slice of the scalar field is zero. Source: `Breakdown.CellReduction.Instantiation.Internal.slice_vanish_outside` (`Breakdown/CellReduction/InstScalarGradient.lean:16`).

**Theorem: Reconstruct a vector from coordinates.** Every vector is the sum of its coordinates times the coordinate unit vectors. Source: `Breakdown.CellReduction.Instantiation.Internal.expand_unit` (`Breakdown/CellReduction/InstScalarGradient.lean:30`).

**Theorem: Expand a scalar gradient pairing.** The inner product of the gradient with a vector equals the sum of directional coordinate derivatives times vector coordinates. Source: `Breakdown.CellReduction.Instantiation.Internal.inner_gradient_expand` (`Breakdown/CellReduction/InstScalarGradient.lean:33`).

**Theorem: Differentiate a vector coordinate.** Differentiating a vector coordinate equals taking that coordinate after differentiation of the vector field. Source: `Breakdown.CellReduction.Instantiation.Internal.component_fderiv` (`Breakdown/CellReduction/InstScalarGradient.lean:39`).

**Theorem: Solenoidal test kills a scalar gradient.** The spatial integral of the scalar gradient paired with the compact divergence-free test field is zero. Source: `Breakdown.CellReduction.Instantiation.Internal.slice_integral_zero` (`Breakdown/CellReduction/InstScalarGradient.lean:48`).

**Theorem: Pressure gradients vanish on tests.** The gradient of a continuous locally Lipschitz pressure is measurable and pairs to zero with every solenoidal spacetime test. Source: `Breakdown.CellReduction.Instantiation.scalarGradientOrthogonal_holds` (`Breakdown/CellReduction/InstScalarGradient.lean:113`).

### Breakdown.CellReduction.InstStepPhase

A joined step spline is integrated into a radial phase that vanishes on the inner region and has a logarithmic tail.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: Every polynomial has all derivatives.** A real polynomial is continuously differentiable to every finite order. Source: `Breakdown.CellReduction.Instantiation.Internal.stepPoly_contDiff` (`Breakdown/CellReduction/InstStepPhase.lean:19`).

**Theorem: Matching jets glue differentiably.** Two polynomials whose derivatives agree through order k at the join define a continuously differentiable piecewise function of order k. Source: `Breakdown.CellReduction.Instantiation.Internal.stepGlue_contDiff` (`Breakdown/CellReduction/InstStepPhase.lean:23`).

**Theorem: Ordered thresholds select an initial sum.** For a strictly ordered knot list, summing terms whose knots are at most t equals summing the initial segment counted by that threshold. Source: `Breakdown.CellReduction.Instantiation.Internal.stepFilter_sum` (`Breakdown/CellReduction/InstStepPhase.lean:80`).

**Theorem: Write the spline as accumulated jumps.** The step-spline value equals the first polynomial plus the sum of successive polynomial differences activated at their interior knots. Source: `Breakdown.CellReduction.Instantiation.Internal.stepEval_decomp` (`Breakdown/CellReduction/InstStepPhase.lean:108`).

**Theorem: Read an interior knot by its index.** Index i in the list with its first and last knots removed is index i plus one in the original knot list. Source: `Breakdown.CellReduction.Instantiation.Internal.stepInterior_getD` (`Breakdown/CellReduction/InstStepPhase.lean:120`).

**Theorem: Joined step spline has two derivatives.** The valid joined step spline is twice continuously differentiable. Source: `Breakdown.CellReduction.Instantiation.Internal.stepEval_contDiff` (`Breakdown/CellReduction/InstStepPhase.lean:128`).

**Theorem: The inner step profile vanishes.** The step-profile value is zero throughout the specified inner region. Source: `Breakdown.CellReduction.Instantiation.Internal.stepEval_zero_lt` (`Breakdown/CellReduction/InstStepPhase.lean:145`).

**Theorem: The inner step profile vanishes.** The step-profile value is zero throughout the specified inner region. Source: `Breakdown.CellReduction.Instantiation.Internal.stepEval_zero_le` (`Breakdown/CellReduction/InstStepPhase.lean:198`).

**Theorem: Inner radius stays below the chart edge.** The stated physical-radius bound puts its compactified coordinate below the inner edge. Source: `Breakdown.CellReduction.Instantiation.Internal.stepRatio_le` (`Breakdown/CellReduction/InstStepPhase.lean:207`).

**Theorem: Outer radius exceeds the chart threshold.** The stated outer physical-radius bound puts its compactified coordinate above the specified threshold. Source: `Breakdown.CellReduction.Instantiation.Internal.stepRatio_ge` (`Breakdown/CellReduction/InstStepPhase.lean:215`).

**Definition: Integrand defining the radial phase.** The step-phase integrand evaluates the step profile at the compactified radius and divides by radius. Source: `Breakdown.CellReduction.Instantiation.Internal.stepIntegrand` (`Breakdown/CellReduction/InstStepPhase.lean:221`).

**Definition: Primitive from the origin.** The step-phase primitive integrates its radial integrand from zero to the chosen radius. Source: `Breakdown.CellReduction.Instantiation.Internal.stepPrimitive` (`Breakdown/CellReduction/InstStepPhase.lean:223`).

**Theorem: Read the phase through its primitive.** The step phase equals its radial primitive evaluated at the square root of the phase variable. Source: `Breakdown.CellReduction.Instantiation.Internal.stepPhase_eq_primitive` (`Breakdown/CellReduction/InstStepPhase.lean:225`).

**Theorem: The inner step integrand is zero.** The step integrand vanishes in the stated inner radial region. Source: `Breakdown.CellReduction.Instantiation.Internal.stepIntegrand_zero` (`Breakdown/CellReduction/InstStepPhase.lean:230`).

**Theorem: The matching radius is positive.** A positive chart length and an edge strictly between zero and one give a positive matching radius. Source: `Breakdown.CellReduction.Instantiation.Internal.stepRadius_pos` (`Breakdown/CellReduction/InstStepPhase.lean:235`).

**Theorem: The step integrand has two derivatives.** The step integrand is twice continuously differentiable on the interval above minus the chart length. Source: `Breakdown.CellReduction.Instantiation.Internal.stepIntegrand_contDiffOn` (`Breakdown/CellReduction/InstStepPhase.lean:238`).

**Theorem: Interval integrability of the step data.** The step integrand is integrable on the specified finite interval. Source: `Breakdown.CellReduction.Instantiation.Internal.stepIntegrand_intervalIntegrable` (`Breakdown/CellReduction/InstStepPhase.lean:254`).

**Theorem: Differentiate the step primitive.** The derivative of the step primitive is the step integrand at the same point. Source: `Breakdown.CellReduction.Instantiation.Internal.stepPrimitive_hasDerivAt` (`Breakdown/CellReduction/InstStepPhase.lean:264`).

**Theorem: The step primitive has three derivatives.** The step primitive is three times continuously differentiable above minus the chart length. Source: `Breakdown.CellReduction.Instantiation.Internal.stepPrimitive_contDiffOn` (`Breakdown/CellReduction/InstStepPhase.lean:272`).

**Theorem: The inner step primitive vanishes.** The step primitive is zero in the specified inner radial region. Source: `Breakdown.CellReduction.Instantiation.Internal.stepPrimitive_zero` (`Breakdown/CellReduction/InstStepPhase.lean:280`).

**Theorem: The inner moving phase vanishes.** The step phase is zero throughout the stated inner phase region. Source: `Breakdown.CellReduction.Instantiation.Internal.stepPhase_zero` (`Breakdown/CellReduction/InstStepPhase.lean:289`).

**Theorem: The step phase has three derivatives.** The completed step phase is globally three times continuously differentiable. Source: `Breakdown.CellReduction.Instantiation.Internal.stepPhase_contDiff` (`Breakdown/CellReduction/InstStepPhase.lean:296`).

**Theorem: The phase has a logarithmic tail.** Beyond a positive radius, the step phase equals a constant plus one half of the logarithm. Source: `Breakdown.CellReduction.Instantiation.Internal.stepPhase_tail` (`Breakdown/CellReduction/InstStepPhase.lean:310`).

**Theorem: Derivatives of the logarithmic tail.** For positive s, the first three derivatives of C+log(s)/2 multiplied by s, s squared and s cubed are respectively one half, minus one half and one. Source: `Breakdown.CellReduction.Instantiation.Internal.stepLog_derivs` (`Breakdown/CellReduction/InstStepPhase.lean:342`).

**Theorem: Bound the three scaled phase derivatives.** The first three step-phase derivatives remain bounded after multiplication by their corresponding powers of the nonnegative phase variable. Source: `Breakdown.CellReduction.Instantiation.Internal.stepPhase_scaled` (`Breakdown/CellReduction/InstStepPhase.lean:370`).

### Breakdown.CellReduction.InstWeakDivergence

Classical zero divergence of a continuously differentiable field yields the weak test identity.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: Expand a linear map in coordinates.** A scalar linear map applied to a vector equals the sum of vector coordinates times the map's values on the unit basis. Source: `Breakdown.CellReduction.Instantiation.Internal.clm_apply_coordSum` (`Breakdown/CellReduction/InstWeakDivergence.lean:16`).

**Theorem: Differentiate a vector component.** The derivative of one vector coordinate is that coordinate of the vector derivative. Source: `Breakdown.CellReduction.Instantiation.Internal.fderiv_coord_apply` (`Breakdown/CellReduction/InstWeakDivergence.lean:24`).

**Theorem: Classical divergence gives weak zero.** A continuously differentiable divergence-free field pairs to zero with every compact test-function gradient. Source: `Breakdown.CellReduction.Instantiation.classicalDivergenceWeak_holds` (`Breakdown/CellReduction/InstWeakDivergence.lean:35`).

### Breakdown.CellReduction.InstanceStatements

The shape-to-certificate construction is separated into precise propositions for regularity, symmetry, boundedness and agreement on the matching ball.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Definition: Structural certificate requirements.** This proposition requires that the instantiated profile, pressure, target and derivative data satisfy the regularity, symmetry, decay and weak-equation clauses of the extended certificate. Source: `Breakdown.CellReduction.Instantiation.StructuralClauses` (`Breakdown/CellReduction/InstanceStatements.lean:21`).

**Interface definition: The step spline gives a radial phase.** This proposition requires that a valid joined step profile gives an admissible radial phase that vanishes up to its prescribed inner radius. Source: `Breakdown.CellReduction.Instantiation.StepPhaseHolds` (`Breakdown/CellReduction/InstanceStatements.lean:46`).

Supplied by `Breakdown.CellReduction.Instantiation.stepPhase_holds` (`lean/Breakdown/CellReduction/InstStepPhase.lean:412`).

**Definition: Adjoint regularity and curl data.** This proposition requires that each selected adjoint is weakly divergence-free and admits uniform decaying field and curl-potential bounds. Source: `Breakdown.CellReduction.Instantiation.AdjointFieldFacts` (`Breakdown/CellReduction/InstanceStatements.lean:65`).

**Interface definition: Shape data give adjoint regularity.** This proposition requires that a valid adjoint shape entry supplies the certificate's adjoint regularity and curl-potential facts. Source: `Breakdown.CellReduction.Instantiation.AdjointFieldHolds` (`Breakdown/CellReduction/InstanceStatements.lean:72`).

Supplied by `Breakdown.CellReduction.Instantiation.adjointField_holds_of` (`lean/Breakdown/CellReduction/InstAdjointField.lean:36`).

**Interface definition: Endpoint orders give field decay.** This proposition requires that a uniform lower bound e on the outer endpoint orders gives decay order e for the field and its time derivative, e+1 for the gradient and e+2 for the stored Hessian. Source: `Breakdown.CellReduction.Instantiation.FieldDecayOrderHolds` (`Breakdown/CellReduction/InstanceStatements.lean:76`).

Supplied by `Breakdown.CellReduction.Instantiation.fieldDecayOrder_holds` (`lean/Breakdown/CellReduction/InstFieldDecayOrder.lean:436`).

**Interface definition: Stored and classical Hessians agree.** This proposition requires that the shape field's classical Hessian exists almost everywhere and agrees with its stored Hessian. Source: `Breakdown.CellReduction.Instantiation.SecondDerivAgreeHolds` (`Breakdown/CellReduction/InstanceStatements.lean:84`).

Supplied by `Breakdown.CellReduction.Instantiation.secondDerivAgree_from_keys` (`lean/Breakdown/CellReduction/InstAdjointField.lean:32`).

**Interface definition: Construct a decaying curl potential.** This proposition requires that valid shape data of outer order at least three admit a periodic curl potential with inverse-square value and inverse-cubic gradient decay. Source: `Breakdown.CellReduction.Instantiation.FieldPotentialHolds` (`Breakdown/CellReduction/InstanceStatements.lean:89`).

Supplied by `Breakdown.CellReduction.Instantiation.fieldPotential_holds_of` (`lean/Breakdown/CellReduction/InstFieldPotential.lean:19`); `Breakdown.CellReduction.Instantiation.fieldPotential_holds` (`lean/Breakdown/CellReduction/InstFieldPotential.lean:38`).

**Interface definition: Classical divergence gives weak zero.** This proposition requires that a continuously differentiable divergence-free field pairs to zero with every compact test-function gradient. Source: `Breakdown.CellReduction.Instantiation.ClassicalDivergenceWeakHolds` (`Breakdown/CellReduction/InstanceStatements.lean:97`).

Supplied by `Breakdown.CellReduction.Instantiation.classicalDivergenceWeak_holds` (`lean/Breakdown/CellReduction/InstWeakDivergence.lean:35`).

**Interface definition: Split the instantiated profile.** This proposition requires that the instantiated profile equals the centre field plus the parameter-weighted tangent fields. Source: `Breakdown.CellReduction.Instantiation.ProfileSplitHolds` (`Breakdown/CellReduction/InstanceStatements.lean:108`).

Supplied by `Breakdown.CellReduction.Instantiation.profileSplit_holds` (`lean/Breakdown/CellReduction/InstProfileSplit.lean:13`).

**Interface definition: Uniform bounds for profile pieces.** This proposition requires that the centre and tangent pieces are admissible flow pieces with one bound on every bounded parameter box. Source: `Breakdown.CellReduction.Instantiation.ProfilePiecesFlowHolds` (`Breakdown/CellReduction/InstanceStatements.lean:113`).

Supplied by `Breakdown.CellReduction.Instantiation.profilePiecesFlow_of` (`lean/Breakdown/CellReduction/InstProfilePieces.lean:70`).

**Interface definition: Identify the adjoint structure.** This proposition requires that the shape identifications and reciprocal-period expansion give the adjoint decomposition required by the residual estimate. Source: `Breakdown.CellReduction.Instantiation.AdjointStructureHolds` (`Breakdown/CellReduction/InstanceStatements.lean:118`).

Supplied by `Breakdown.CellReduction.Instantiation.adjointStructure_holds_of` (`lean/Breakdown/CellReduction/InstAdjointStructure.lean:18`).

**Definition: Identify the two shift fields.** This proposition requires that the two stored pieces and their gradients are the centre-minus-model and profile-minus-centre differences. Source: `Breakdown.CellReduction.Instantiation.ShiftPiecesLinks` (`Breakdown/CellReduction/InstanceStatements.lean:127`).

**Interface definition: Bind the shift decomposition.** This proposition requires that the two identified shape shifts sum to the profile-minus-model difference and its gradient and have the required measurability. Source: `Breakdown.CellReduction.Instantiation.ShiftPiecesLinkHolds` (`Breakdown/CellReduction/InstanceStatements.lean:136`).

No theorem in the library states this proposition as its result.

**Interface definition: Moving preserves valid parameters.** This proposition requires that adding a multiple of an admissible radial phase preserves validity of the shape parameters. Source: `Breakdown.CellReduction.Instantiation.MovedParamsValidHolds` (`Breakdown/CellReduction/InstanceStatements.lean:147`).

Supplied by `Breakdown.CellReduction.Instantiation.movedParamsValid_holds` (`lean/Breakdown/CellReduction/InstMovedParams.lean:67`).

**Interface definition: Period and divergence of affine fields.** This proposition requires that valid affine shape data preserve time periodicity, zero divergence and measurable periodic Hessians. Source: `Breakdown.CellReduction.Instantiation.AffineFieldStructureHolds` (`Breakdown/CellReduction/InstanceStatements.lean:151`).

Supplied by `Breakdown.CellReduction.Instantiation.affineFieldStructure_holds` (`lean/Breakdown/CellReduction/InstAffineStructure.lean:55`).

**Interface definition: Weak Hessian of an affine field.** This proposition requires that the stored affine Hessian gives the weak spatial derivatives of every gradient column. Source: `Breakdown.CellReduction.Instantiation.AffineFieldWeakSecondDerivHolds` (`Breakdown/CellReduction/InstanceStatements.lean:161`).

Supplied by `Breakdown.CellReduction.Instantiation.affineFieldWeakSecondDeriv_holds` (`lean/Breakdown/CellReduction/InstAffineWeak.lean:83`).

**Interface definition: Affine fields respect the symmetries.** This proposition requires that the affine shape field transforms equivariantly under every symmetry generated by the cell class. Source: `Breakdown.CellReduction.Instantiation.AffineFieldInvariantHolds` (`Breakdown/CellReduction/InstanceStatements.lean:169`).

Supplied by `Breakdown.CellReduction.Instantiation.affineFieldInvariant_holds` (`lean/Breakdown/CellReduction/InstAffineInvariant.lean:56`).

**Interface definition: Joint regularity of the moved field.** This proposition requires that the moved affine field is continuously differentiable jointly in parameters, time and space. Source: `Breakdown.CellReduction.Instantiation.MovedFieldJointSmoothHolds` (`Breakdown/CellReduction/InstanceStatements.lean:178`).

Supplied by `Breakdown.CellReduction.Instantiation.movedFieldJointSmooth_holds` (`lean/Breakdown/CellReduction/InstMovedSmooth.lean:65`).

**Interface definition: Uniform decay on a parameter box.** This proposition requires that the moved affine field, gradient and stored Hessian have uniform inverse-linear, inverse-square and inverse-cubic bounds on a bounded parameter box. Source: `Breakdown.CellReduction.Instantiation.MovedFieldUniformDecayHolds` (`Breakdown/CellReduction/InstanceStatements.lean:186`).

Supplied by `Breakdown.CellReduction.Instantiation.movedFieldUniformDecay_holds` (`lean/Breakdown/CellReduction/InstMovedDecay.lean:532`).

**Interface definition: The parameter coordinates are bounded.** This proposition requires that nonzero coordinate scales give one finite bound for every coordinate in the certificate parameter set. Source: `Breakdown.CellReduction.Instantiation.ParamsBoundedHolds` (`Breakdown/CellReduction/InstanceStatements.lean:197`).

Supplied by `Breakdown.CellReduction.Instantiation.paramsBounded_holds` (`lean/Breakdown/CellReduction/InstParamsBounded.lean:14`).

**Interface definition: Continuity of the pin functional.** This proposition requires that joint profile regularity and uniform decay make its pairing with a fixed square-integrable pin continuous on the parameter set. Source: `Breakdown.CellReduction.Instantiation.PinValueContinuousHolds` (`Breakdown/CellReduction/InstanceStatements.lean:201`).

Supplied by `Breakdown.CellReduction.Instantiation.pinValueContinuous_holds` (`lean/Breakdown/CellReduction/InstPinContinuous.lean:75`).

**Interface definition: Regularity of the shape pressure.** This proposition requires that valid pressure shapes give a continuous periodic pressure with a common spatial Lipschitz constant on each ball. Source: `Breakdown.CellReduction.Instantiation.PressureFieldRegularHolds` (`Breakdown/CellReduction/InstanceStatements.lean:210`).

Supplied by `Breakdown.CellReduction.Instantiation.pressureFieldRegular_holds` (`lean/Breakdown/CellReduction/InstPressureRegular.lean:835`).

**Interface definition: Pressure gradients vanish on tests.** This proposition requires that the gradient of a continuous locally Lipschitz pressure is measurable and pairs to zero with every solenoidal spacetime test. Source: `Breakdown.CellReduction.Instantiation.ScalarGradientOrthogonalHolds` (`Breakdown/CellReduction/InstanceStatements.lean:216`).

Supplied by `Breakdown.CellReduction.Instantiation.scalarGradientOrthogonal_holds` (`lean/Breakdown/CellReduction/InstScalarGradient.lean:113`).

**Interface definition: Agreement inside the matching ball.** This proposition requires that a phase change vanishing on the inner region leaves the field, gradient, Hessian, pressure and pressure gradient unchanged on that ball. Source: `Breakdown.CellReduction.Instantiation.BallAgreementHolds` (`Breakdown/CellReduction/InstanceStatements.lean:222`).

Supplied by `Breakdown.CellReduction.Instantiation.ballAgreement_holds` (`lean/Breakdown/CellReduction/InstBallAgreement.lean:114`).

**Interface definition: Quadratic offset pairing on a ball.** This proposition requires that the defect pairing on the matching ball equals its constant, linear and symmetrized quadratic parameter contributions. Source: `Breakdown.CellReduction.Instantiation.OffsetBallIdentityHolds` (`Breakdown/CellReduction/InstanceStatements.lean:232`).

Supplied by `Breakdown.CellReduction.Instantiation.offsetBallIdentity_of` (`lean/Breakdown/CellReduction/InstOffsetIdentity.lean:713`); `Breakdown.CellReduction.Instantiation.offsetBallIdentity_holds` (`lean/Breakdown/CellReduction/InstOffsetIdentity.lean:786`).

### Breakdown.CellReduction.MatrixFacts

Matrix column squares control the operator norm, while the symmetric part controls the quadratic strain pairing.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: Matrix square norm is nonnegative.** The sum of the squared matrix-column norms is nonnegative. Source: `Breakdown.CertReduction.columnSquareSum_nonneg` (`Breakdown/CellReduction/MatrixFacts.lean:12`).

**Theorem: Squared image bound from column norm.** The squared norm of a matrix image is bounded by its column-square sum times the squared vector norm. Source: `Breakdown.CertReduction.apply_norm_sq_le_columnSquareSum` (`Breakdown/CellReduction/MatrixFacts.lean:15`).

**Theorem: The column norm bounds the operator.** The squared operator norm of a matrix is bounded by its column square sum. Source: `Breakdown.CertReduction.operatorSquareBound` (`Breakdown/CellReduction/MatrixFacts.lean:40`).

**Theorem: The symmetric part bounds strain.** A bound S on the symmetric part gives the quadratic lower bound minus S times the vector norm squared. Source: `Breakdown.CertReduction.strainOfSymmetricPart` (`Breakdown/CellReduction/MatrixFacts.lean:51`).

**Theorem: Matrix bounds used by the reduction.** The operator-square and symmetric-strain bounds both hold. Source: `Breakdown.CertReduction.matrixFacts` (`Breakdown/CellReduction/MatrixFacts.lean:72`).

### Breakdown.CellReduction.PeriodGlue

The period integral preserves the finite-sum, pairing and almost-everywhere slice estimates used by the reduction.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: Integral bounded by absolute integral.** The absolute value of a real integral, embedded in the extended nonnegative reals, is bounded by the integral of the pointwise absolute value. Source: `Breakdown.CertReduction.Internal.ofReal_abs_integral_le` (`Breakdown/CellReduction/PeriodGlue.lean:14`).

**Theorem: Pairing bounded by product of norms.** The absolute integral pairing of two fields is bounded by the nonnegative integral of the product of their norms. Source: `Breakdown.CertReduction.Internal.ofReal_abs_integral_inner_le` (`Breakdown/CellReduction/PeriodGlue.lean:20`).

**Theorem: Square integral is the squared L2 norm.** For a nonnegative real function, the integral of its square equals the square of its extended L2 norm. Source: `Breakdown.CertReduction.Internal.lintegral_ofReal_sq_eq` (`Breakdown/CellReduction/PeriodGlue.lean:26`).

**Theorem: Remove a square from an upper bound.** A nonnegative extended real whose square is bounded by the square of a nonnegative real is bounded by that real. Source: `Breakdown.CertReduction.Internal.le_ofReal_of_sq_le` (`Breakdown/CellReduction/PeriodGlue.lean:39`).

**Theorem: Sum the period square bounds.** A nonnegative sum of pieces with energy coefficients has a period square bound with the sum of those coefficients. Source: `Breakdown.CertReduction.periodSumBound` (`Breakdown/CellReduction/PeriodGlue.lean:48`).

**Theorem: Control the period pairing.** A bound on the period integral of the product of norms bounds the absolute period pairing. Source: `Breakdown.CertReduction.periodPairingBound` (`Breakdown/CellReduction/PeriodGlue.lean:95`).

**Theorem: Control the spatial pairing.** A bound on the spatial integral of the product of norms bounds the absolute spatial pairing. Source: `Breakdown.CertReduction.stationaryPairingBound` (`Breakdown/CellReduction/PeriodGlue.lean:106`).

**Theorem: Integrate the slice inequalities.** An almost-everywhere nonnegative slice integral bound extends to the period integral. Source: `Breakdown.CertReduction.sliceIntegrate` (`Breakdown/CellReduction/PeriodGlue.lean:110`).

**Theorem: Assemble the period integral bounds.** The finite-sum, period-pairing, spatial-pairing and slice-integration estimates all hold. Source: `Breakdown.CertReduction.periodGlue` (`Breakdown/CellReduction/PeriodGlue.lean:119`).

### Breakdown.CellReduction.PerturbationSlice

An admissible spacetime perturbation has the required weak derivatives and finite energies on almost every time slice.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: Extend a periodic a.e. statement.** A periodic property holding almost everywhere on the unit interval holds almost everywhere on the whole time line. Source: `Breakdown.CertReduction.Internal.ae_of_ae_unitInterval` (`Breakdown/CellReduction/PerturbationSlice.lean:14`).

**Theorem: The matrix square norm is continuous.** The sum of the squared matrix-column norms depends continuously on the matrix. Source: `Breakdown.CertReduction.Internal.continuous_matSq_fun` (`Breakdown/CellReduction/PerturbationSlice.lean:26`).

**Theorem: The Laplacian trace is continuous.** Taking the trace of the second derivative is a continuous operation. Source: `Breakdown.CertReduction.Internal.continuous_secondDerivTrace_fun` (`Breakdown/CellReduction/PerturbationSlice.lean:31`).

**Theorem: Finite perturbation slices almost surely.** The finite spacetime bound gives a finite spatial nonnegative integral of the prescribed perturbation quantity for almost every time. Source: `Breakdown.CertReduction.Internal.slice_lintegral_ae_lt_top` (`Breakdown/CellReduction/PerturbationSlice.lean:36`).

**Theorem: Valid perturbations have good slices.** An admissible spacetime perturbation has weak first and second derivatives and finite L6, gradient and Laplacian energies on almost every slice. Source: `Breakdown.CertReduction.perturbationSliceHolds` (`Breakdown/CellReduction/PerturbationSlice.lean:62`).

### Breakdown.CellReduction.PotCell

Joined tensor-product jets define compactly supported cylindrical fields with the regularity needed by the pin potential.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: Adjacent radial jet cells agree.** The two adjacent radial polynomial pieces have equal restrictions at their common radial knot. Source: `Breakdown.PotentialShape.CellField.Internal.jet_atFirst_join` (`Breakdown/CellReduction/PotCell.lean:24`).

**Theorem: Adjacent height jet cells agree.** The two adjacent height polynomial pieces have equal restrictions at their common height knot. Source: `Breakdown.PotentialShape.CellField.Internal.jet_atSecond_join` (`Breakdown/CellReduction/PotCell.lean:43`).

**Theorem: The jet pieces meet continuously.** The Hermite jet construction makes the adjacent radial and height polynomial pieces agree at every interior join. Source: `Breakdown.PotentialShape.CellField.Internal.jet_joins` (`Breakdown/CellReduction/PotCell.lean:62`).

**Theorem: The jet amplitude is continuous.** The valid joined jet spline defines a continuous bivariate amplitude. Source: `Breakdown.PotentialShape.CellField.Internal.amp_continuous` (`Breakdown/CellReduction/PotCell.lean:79`).

**Theorem: Amplitude is Lipschitz on bounded boxes.** The amplitude difference on a bounded coordinate box is at most one constant times the sum of coordinate differences. Source: `Breakdown.PotentialShape.CellField.Internal.amp_box` (`Breakdown/CellReduction/PotCell.lean:90`).

**Theorem: The amplitude is bounded on boxes.** One nonnegative constant bounds the amplitude on each specified bounded coordinate box. Source: `Breakdown.PotentialShape.CellField.Internal.amp_bounded` (`Breakdown/CellReduction/PotCell.lean:95`).

**Theorem: Passed knot bounds the cell index below.** Passing the kth ordered knot places the selected cell index at least k. Source: `Breakdown.PotentialShape.CellField.Internal.le_cellIndex_of_getElem` (`Breakdown/CellReduction/PotCell.lean:99`).

**Theorem: The selected cell has a right endpoint.** The selected cell's successor index lies below the knot-list length. Source: `Breakdown.PotentialShape.CellField.Internal.cellIndex_succ_lt` (`Breakdown/CellReduction/PotCell.lean:126`).

**Theorem: A later knot bounds the selected cell.** A coordinate below the kth knot has selected cell successor at most k. Source: `Breakdown.PotentialShape.CellField.Internal.cellIndex_lt_of_lt` (`Breakdown/CellReduction/PotCell.lean:132`).

**Theorem: Exterior coordinates have exterior cells.** At the stated exterior coordinate, both endpoints of the selected cell have absolute value at least R. Source: `Breakdown.PotentialShape.CellField.Internal.beyond_of_ge` (`Breakdown/CellReduction/PotCell.lean:157`).

**Theorem: Exterior coordinates have exterior cells.** At the stated exterior coordinate, both endpoints of the selected cell have absolute value at least R. Source: `Breakdown.PotentialShape.CellField.Internal.beyond_of_lt` (`Breakdown/CellReduction/PotCell.lean:180`).

**Theorem: An unsupported radial term vanishes.** For the selected exterior radial cell, either the jet coefficient is zero or its radial basis polynomial is zero. Source: `Breakdown.PotentialShape.CellField.Internal.coef_or_tPoly` (`Breakdown/CellReduction/PotCell.lean:204`).

**Theorem: An unsupported height term vanishes.** For the selected exterior height cell, either the jet coefficient is zero or its height basis polynomial is zero. Source: `Breakdown.PotentialShape.CellField.Internal.coef_or_xPoly` (`Breakdown/CellReduction/PotCell.lean:224`).

**Theorem: The unsupported spline piece vanishes.** The stated vanishing of the active jet coefficients makes the selected cell polynomial identically zero. Source: `Breakdown.PotentialShape.CellField.Internal.piece_zero` (`Breakdown/CellReduction/PotCell.lean:244`).

**Theorem: Jet amplitude vanishes outside support.** The prescribed compact jet data make the spline amplitude zero in the exterior region. Source: `Breakdown.PotentialShape.CellField.Internal.amp_zero` (`Breakdown/CellReduction/PotCell.lean:251`).

**Definition: Horizontal complex coordinate.** The complex coordinate represents the first two spatial coordinates. Source: `Breakdown.PotentialShape.CellField.Internal.planeOf` (`Breakdown/CellReduction/PotCell.lean:275`).

**Definition: Angular phase weighted by radius.** The angular mode is multiplied by the complex point's norm. Source: `Breakdown.PotentialShape.CellField.Internal.turnScaled` (`Breakdown/CellReduction/PotCell.lean:277`).

**Definition: Complex unit phase.** The unit phase is the exponential of i times the complex argument. Source: `Breakdown.PotentialShape.CellField.Internal.unitOf` (`Breakdown/CellReduction/PotCell.lean:279`).

**Theorem: The oscillatory factor has unit norm.** The stated complex oscillatory factor has norm one. Source: `Breakdown.PotentialShape.CellField.Internal.unitOf_norm` (`Breakdown/CellReduction/PotCell.lean:281`).

**Theorem: Magnitude times direction.** A complex number equals its norm times its normalized direction. Source: `Breakdown.PotentialShape.CellField.Internal.norm_mul_unitOf` (`Breakdown/CellReduction/PotCell.lean:283`).

**Theorem: A scaled angular power.** The scaled angular phase is the complex norm times the integer power of its unit direction. Source: `Breakdown.PotentialShape.CellField.Internal.turnScaled_eq` (`Breakdown/CellReduction/PotCell.lean:285`).

**Theorem: Lipschitz natural powers on the circle.** The difference of nth powers of unit complex numbers is at most n times their distance. Source: `Breakdown.PotentialShape.CellField.Internal.unit_pow_sub` (`Breakdown/CellReduction/PotCell.lean:292`).

**Theorem: Lipschitz integer powers on the circle.** The difference of kth integer powers of unit complex numbers is at most the absolute integer k times their distance. Source: `Breakdown.PotentialShape.CellField.Internal.unit_zpow_sub` (`Breakdown/CellReduction/PotCell.lean:305`).

**Theorem: A weighted normalization bound.** The unit-direction difference times the second norm is at most twice the original complex difference. Source: `Breakdown.PotentialShape.CellField.Internal.scaled_unit_gap` (`Breakdown/CellReduction/PotCell.lean:315`).

**Theorem: The scaled angular map is Lipschitz.** The scaled angular map has Lipschitz constant one plus twice the absolute angular order. Source: `Breakdown.PotentialShape.CellField.Internal.turnScaled_slope` (`Breakdown/CellReduction/PotCell.lean:330`).

**Theorem: The scaled angular map preserves radius.** The scaled angular map has norm equal to the input complex norm. Source: `Breakdown.PotentialShape.CellField.Internal.turnScaled_norm` (`Breakdown/CellReduction/PotCell.lean:354`).

**Theorem: Shift the angular order multiplicatively.** Increasing the angular order by s multiplies the scaled angular map by the frequency-s exponential of the argument. Source: `Breakdown.PotentialShape.CellField.Internal.turnScaled_shift` (`Breakdown/CellReduction/PotCell.lean:358`).

**Theorem: Cosine combines adjacent angular modes.** Multiplying the scaled angular mode by cosine gives half the sum of its adjacent angular modes. Source: `Breakdown.PotentialShape.CellField.Internal.turn_cos` (`Breakdown/CellReduction/PotCell.lean:366`).

**Theorem: Sine splits neighbouring angular orders.** Multiplying the scaled angular mode by sine gives i/2 times the lower adjacent mode minus the upper adjacent mode. Source: `Breakdown.PotentialShape.CellField.Internal.turn_sin` (`Breakdown/CellReduction/PotCell.lean:376`).

**Definition: Radius-weighted cylindrical frame.** The weighted angular mode multiplies the chosen cylindrical basis vector. Source: `Breakdown.PotentialShape.CellField.Internal.frameScaled` (`Breakdown/CellReduction/PotCell.lean:386`).

**Definition: Upper-helicity frame coefficient.** The coefficient matrix gives the contribution of the angular mode with frequency increased by one. Source: `Breakdown.PotentialShape.CellField.Internal.upperWeight` (`Breakdown/CellReduction/PotCell.lean:389`).

**Definition: Lower-helicity frame coefficient.** The coefficient matrix gives the contribution of the angular mode with frequency decreased by one. Source: `Breakdown.PotentialShape.CellField.Internal.lowerWeight` (`Breakdown/CellReduction/PotCell.lean:392`).

**Definition: Axial frame coefficient.** The axial coefficient retains only the third coordinate. Source: `Breakdown.PotentialShape.CellField.Internal.axialWeight` (`Breakdown/CellReduction/PotCell.lean:395`).

**Theorem: Cylindrical frame shifts angular orders.** Each Cartesian coordinate of the framed mode is a weighted sum of angular orders M+1, M-1 and M. Source: `Breakdown.PotentialShape.CellField.Internal.frameScaled_comb` (`Breakdown/CellReduction/PotCell.lean:398`).

**Theorem: The three frame weights are bounded.** The upper, lower and axial frame coefficients each have norm at most one. Source: `Breakdown.PotentialShape.CellField.Internal.weight_norm_le` (`Breakdown/CellReduction/PotCell.lean:411`).

**Definition: A Lipschitz constant for the frame.** The frame constant is three plus twice the sum of the absolute angular orders M+1, M-1 and M. Source: `Breakdown.PotentialShape.CellField.Internal.frameConst` (`Breakdown/CellReduction/PotCell.lean:415`).

**Theorem: The framed mode is Lipschitz.** The framed angular mode has difference bounded by its frame constant times the horizontal complex distance. Source: `Breakdown.PotentialShape.CellField.Internal.frameScaled_slope` (`Breakdown/CellReduction/PotCell.lean:417`).

**Theorem: The framed mode does not enlarge radius.** The norm of the scaled cylindrical-frame mode is at most the horizontal complex norm. Source: `Breakdown.PotentialShape.CellField.Internal.frameScaled_norm` (`Breakdown/CellReduction/PotCell.lean:448`).

**Theorem: Subtract horizontal projections.** The difference of the horizontal complex coordinates equals the horizontal coordinate of the difference. Source: `Breakdown.PotentialShape.CellField.Internal.planeOf_sub` (`Breakdown/CellReduction/PotCell.lean:458`).

**Theorem: Horizontal complex norm is planar radius.** The horizontal complex coordinate has norm equal to the square root of the sum of the first two coordinate squares. Source: `Breakdown.PotentialShape.CellField.Internal.planeOf_norm` (`Breakdown/CellReduction/PotCell.lean:462`).

**Theorem: Square norm as three coordinate squares.** The squared Euclidean norm equals the sum of the three coordinate squares. Source: `Breakdown.PotentialShape.CellField.Internal.space_norm_sq` (`Breakdown/CellReduction/PotCell.lean:467`).

**Theorem: Horizontal norm is bounded by full norm.** The norm of the horizontal complex coordinate is bounded by the full spatial norm. Source: `Breakdown.PotentialShape.CellField.Internal.planeOf_norm_le` (`Breakdown/CellReduction/PotCell.lean:471`).

**Theorem: A coordinate is bounded by the norm.** The absolute value of the selected coordinate is bounded by the vector norm. Source: `Breakdown.PotentialShape.CellField.Internal.coord_two_le` (`Breakdown/CellReduction/PotCell.lean:475`).

**Theorem: First cylindrical coordinate is radius.** The first coordinate of the cylindrical chart equals the norm of the horizontal complex coordinate. Source: `Breakdown.PotentialShape.CellField.Internal.plane_fst` (`Breakdown/CellReduction/PotCell.lean:479`).

**Theorem: Read a real reconstructed coordinate.** A coordinate of the real reconstructed vector is the real part of the corresponding complex coordinate. Source: `Breakdown.PotentialShape.CellField.Internal.realPartVec_at` (`Breakdown/CellReduction/PotCell.lean:483`).

**Theorem: Separate temporal and angular phases.** The label phase equals its zero-angle value times the exponential of its angular frequency and angle. Source: `Breakdown.PotentialShape.CellField.Internal.phase_split` (`Breakdown/CellReduction/PotCell.lean:485`).

**Theorem: Complex form of a cylindrical term.** A real cylindrical frame term equals the real part of its zero-angle scalar amplitude times the scaled complex frame. Source: `Breakdown.PotentialShape.CellField.Internal.cyl_term` (`Breakdown/CellReduction/PotCell.lean:494`).

**Definition: A cylindrical spline amplitude.** The amplitude evaluates its spline at cylindrical radius and height. Source: `Breakdown.PotentialShape.CellField.Internal.ampAt` (`Breakdown/CellReduction/PotCell.lean:509`).

**Definition: A single cylindrical field term.** One cylindrical field term is the real part of its temporal phase, spline amplitude and weighted cylindrical frame. Source: `Breakdown.PotentialShape.CellField.Internal.cellTerm` (`Breakdown/CellReduction/PotCell.lean:511`).

**Theorem: Expand the cylindrical field by cells.** The cylindrical field equals the finite sum of its label and frame-component cell terms. Source: `Breakdown.PotentialShape.CellField.Internal.cylField_eq` (`Breakdown/CellReduction/PotCell.lean:514`).

**Theorem: Spatial ball maps into a coordinate box.** Inside the radius-R spatial ball, both cylindrical coordinates have absolute value at most R. Source: `Breakdown.PotentialShape.CellField.Internal.plane_box` (`Breakdown/CellReduction/PotCell.lean:520`).

**Theorem: Distance bounds for cylinder coordinates.** The radius and height coordinate differences are each bounded by spatial distance. Source: `Breakdown.PotentialShape.CellField.Internal.plane_gap` (`Breakdown/CellReduction/PotCell.lean:525`).

**Theorem: Spatial amplitude is locally Lipschitz.** On each bounded spatial ball, the charted amplitude has a finite Lipschitz constant. Source: `Breakdown.PotentialShape.CellField.Internal.ampAt_slope` (`Breakdown/CellReduction/PotCell.lean:536`).

**Theorem: The oscillatory factor has unit norm.** The stated complex oscillatory factor has norm one. Source: `Breakdown.PotentialShape.CellField.Internal.labelPhase_zero_norm` (`Breakdown/CellReduction/PotCell.lean:549`).

**Theorem: Uniform local slopes of a cell term.** On each bounded spatial ball, one Lipschitz constant controls the cell term at every time. Source: `Breakdown.PotentialShape.CellField.Internal.cellTerm_slope` (`Breakdown/CellReduction/PotCell.lean:553`).

**Theorem: Uniform local slopes of a finite sum.** Finitely many fields with uniform local Lipschitz bounds have a summed field with one such bound. Source: `Breakdown.PotentialShape.CellField.Internal.sum_slope` (`Breakdown/CellReduction/PotCell.lean:594`).

**Theorem: Compact support globalizes a ball bound.** The local Lipschitz bound and vanishing outside the prescribed ball imply the same global difference bound. Source: `Breakdown.PotentialShape.CellField.Internal.slope_of_ball` (`Breakdown/CellReduction/PotCell.lean:613`).

**Theorem: The charted amplitude vanishes far away.** The compact support assumptions make the charted amplitude zero beyond the specified spatial bound. Source: `Breakdown.PotentialShape.CellField.Internal.ampAt_far` (`Breakdown/CellReduction/PotCell.lean:642`).

**Theorem: The cell term is jointly continuous.** Each cylindrical cell term depends continuously on time and space. Source: `Breakdown.PotentialShape.CellField.Internal.cellTerm_continuous` (`Breakdown/CellReduction/PotCell.lean:660`).

**Theorem: Regularity of a cylindrical cell field.** The cylindrical cell field has its measurable weak gradient, finite period gradient energy and the prescribed compact support. Source: `Breakdown.PotentialShape.cellPotentialRegular_holds` (`Breakdown/CellReduction/PotCell.lean:691`).

### Breakdown.CellReduction.PotFlux

The radial and polar flux constructions are assembled into the required regularity and decay statement for the matrix flux.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: Regularity of the matrix flux.** Under the stated hypotheses, the matrix flux is measurable with its weak divergence, inverse-square decay and the stated radius-weighted divergence decay. Source: `Breakdown.PotentialShape.fluxPotentialRegular_of` (`Breakdown/CellReduction/PotFlux.lean:13`).

### Breakdown.CellReduction.PotFluxDecay

The scalar flux amplitude bounds become a matrix-flux decay estimate and an almost-everywhere divergence estimate.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: Off-axis height is strictly interior.** At the specified off-axis point, the normalized height has absolute value strictly below one. Source: `Breakdown.PotentialShape.FluxDecay.Internal.heightRatio_abs_lt` (`Breakdown/CellReduction/PotFluxDecay.lean:18`).

**Theorem: The compactified radius is nonnegative.** For valid shape parameters, the compactified radius is nonnegative. Source: `Breakdown.PotentialShape.FluxDecay.Internal.chartCoord_nonneg` (`Breakdown/CellReduction/PotFluxDecay.lean:28`).

**Theorem: The compactified radius is at most one.** For valid shape parameters, the compactified radius is at most one. Source: `Breakdown.PotentialShape.FluxDecay.Internal.chartCoord_le_one` (`Breakdown/CellReduction/PotFluxDecay.lean:33`).

**Theorem: The chart gap gives inverse-square decay.** The square of one minus compactified radius is at most max(chart length,1) squared divided by (1+radius) squared. Source: `Breakdown.PotentialShape.FluxDecay.Internal.chart_decay` (`Breakdown/CellReduction/PotFluxDecay.lean:39`).

**Theorem: Flux divergence away from seams.** Away from the axis plane and finite spline seams, each flux coordinate is differentiable and radius times the divergence norm is bounded by a constant times the squared chart gap. Source: `Breakdown.PotentialShape.FluxDecay.Internal.fluxVector_divergence_bound` (`Breakdown/CellReduction/PotFluxDecay.lean:53`).

**Theorem: Each flux coordinate has outer order two.** Every flux coordinate is bounded uniformly in time by a constant times the squared chart gap. Source: `Breakdown.PotentialShape.FluxDecay.Internal.fluxVector_value_bound` (`Breakdown/CellReduction/PotFluxDecay.lean:95`).

**Theorem: Coordinate evaluation is continuous.** Each coordinate of a Euclidean vector depends continuously on the vector. Source: `Breakdown.PotentialShape.FluxDecay.Internal.coord_continuous` (`Breakdown/CellReduction/PotFluxDecay.lean:120`).

**Theorem: A coordinate is bounded by the norm.** The absolute value of the selected coordinate is bounded by the vector norm. Source: `Breakdown.PotentialShape.FluxDecay.Internal.coord_abs_le` (`Breakdown/CellReduction/PotFluxDecay.lean:123`).

**Theorem: Bound a vector by its coordinate sizes.** The Euclidean vector norm is at most the sum of the three absolute coordinates. Source: `Breakdown.PotentialShape.FluxDecay.Internal.norm_le_sum_abs` (`Breakdown/CellReduction/PotFluxDecay.lean:129`).

**Theorem: A matrix-entry map has norm at most one.** Each coordinate matrix-entry map has operator norm at most one. Source: `Breakdown.PotentialShape.FluxDecay.Internal.entryMap_norm_le` (`Breakdown/CellReduction/PotFluxDecay.lean:139`).

**Theorem: Bound the helical reconstruction.** The reconstructed vector norm is at most the sum of the plus, minus and axial component norms. Source: `Breakdown.PotentialShape.FluxDecay.Internal.coords_norm_le` (`Breakdown/CellReduction/PotFluxDecay.lean:150`).

**Theorem: Azimuthal angle is measurable.** The spatial azimuthal angle is measurable. Source: `Breakdown.PotentialShape.FluxDecay.Internal.pointAngle_measurable` (`Breakdown/CellReduction/PotFluxDecay.lean:166`).

**Theorem: Normalized height is measurable.** The normalized-height function is measurable. Source: `Breakdown.PotentialShape.FluxDecay.Internal.heightRatio_measurable` (`Breakdown/CellReduction/PotFluxDecay.lean:173`).

**Theorem: Compactified radius is continuous.** The compactified radial coordinate is continuous. Source: `Breakdown.PotentialShape.FluxDecay.Internal.chartCoord_continuous` (`Breakdown/CellReduction/PotFluxDecay.lean:177`).

**Theorem: The spatial radial phase is continuous.** The admissible radial phase composed with squared spatial norm is continuous. Source: `Breakdown.PotentialShape.FluxDecay.Internal.radialPhase_norm_continuous` (`Breakdown/CellReduction/PotFluxDecay.lean:182`).

**Theorem: The scalar potential mode is measurable.** The scalar potential mode is jointly measurable in time and space. Source: `Breakdown.PotentialShape.FluxDecay.Internal.scalarValue_measurable` (`Breakdown/CellReduction/PotFluxDecay.lean:189`).

**Theorem: Polar-frame coordinates are measurable.** Each coordinate of the scaled polar basis vector is measurable. Source: `Breakdown.PotentialShape.FluxDecay.Internal.polarVecQ_measurable` (`Breakdown/CellReduction/PotFluxDecay.lean:227`).

**Theorem: Flux-vector coordinates are measurable.** Each flux-vector coordinate is jointly measurable in time and space. Source: `Breakdown.PotentialShape.FluxDecay.Internal.fluxVector_measurable` (`Breakdown/CellReduction/PotFluxDecay.lean:236`).

**Theorem: Real flux-row coordinates are measurable.** Each real coordinate of the assembled flux row is jointly measurable. Source: `Breakdown.PotentialShape.FluxDecay.Internal.fluxRow_re_measurable` (`Breakdown/CellReduction/PotFluxDecay.lean:244`).

**Theorem: Assemble the matrix from flux entries.** The real flux matrix equals the finite sum of its real row entries multiplied by the corresponding coordinate matrix maps. Source: `Breakdown.PotentialShape.FluxDecay.Internal.fluxMap_eq_sum` (`Breakdown/CellReduction/PotFluxDecay.lean:257`).

**Theorem: The assembled flux is measurable a.e..** The assembled flux matrix is strongly measurable almost everywhere in spacetime. Source: `Breakdown.PotentialShape.FluxDecay.Internal.fluxMap_aestronglyMeasurable` (`Breakdown/CellReduction/PotFluxDecay.lean:261`).

**Theorem: Flux seams are negligible.** Almost every spatial point avoids the axis plane and all radial and height seams of the finite flux data. Source: `Breakdown.PotentialShape.FluxDecay.Internal.flux_good_ae` (`Breakdown/CellReduction/PotFluxDecay.lean:271`).

**Theorem: Measurable flux with global decay.** The flux is strongly measurable almost everywhere with inverse-square decay, and radius times its divergence has the same bound almost everywhere on every time slice. Source: `Breakdown.PotentialShape.fluxMap_measurable_decay` (`Breakdown/CellReduction/PotFluxDecay.lean:312`).

### Breakdown.CellReduction.PotFluxDecayAmp

Shifted harmonic labels let radial and polar flux amplitudes reuse the framed-field calculus.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Definition: Angular vanishing for a flux scalar.** The angular factor is a power of one minus height squared, multiplied by its square root when the sine flag is set. Source: `Breakdown.PotentialShape.FluxDecay.Internal.angularPart` (`Breakdown/CellReduction/PotFluxDecayAmp.lean:16`).

**Definition: Weighted flux amplitude.** The flux amplitude multiplies its endpoint polynomial, angular factor and jet spline. Source: `Breakdown.PotentialShape.FluxDecay.Internal.scalarAmp` (`Breakdown/CellReduction/PotFluxDecayAmp.lean:19`).

**Definition: Parameters for a shifted harmonic.** The shifted parameters use the absolute shifted angular frequency, retaining the original order when that frequency is zero. Source: `Breakdown.PotentialShape.FluxDecay.Internal.shiftedParams` (`Breakdown/CellReduction/PotFluxDecayAmp.lean:22`).

**Definition: Key for the shifted angular mode.** The shifted key uses the sign of the new frequency and retains the original radial phase index. Source: `Breakdown.PotentialShape.FluxDecay.Internal.shiftedKey` (`Breakdown/CellReduction/PotFluxDecayAmp.lean:25`).

**Definition: Time rescaling for the shifted key.** The new time coordinate compensates for the shifted key's temporal frequency. Source: `Breakdown.PotentialShape.FluxDecay.Internal.shiftedTime` (`Breakdown/CellReduction/PotFluxDecayAmp.lean:27`).

**Definition: Radial and polar flux amplitudes.** The amplitude vector contains the radial and polar flux scalars followed by zero. Source: `Breakdown.PotentialShape.FluxDecay.Internal.fluxAmps` (`Breakdown/CellReduction/PotFluxDecayAmp.lean:30`).

**Theorem: The shifted angular parameters are valid.** The angular-order shift preserves validity of the shape parameters. Source: `Breakdown.PotentialShape.FluxDecay.Internal.shiftedParams_valid` (`Breakdown/CellReduction/PotFluxDecayAmp.lean:33`).

**Theorem: Auxiliary temporal frequency is nonzero.** The shifted auxiliary label has nonzero temporal frequency. Source: `Breakdown.PotentialShape.FluxDecay.Internal.labelTime_shifted_ne` (`Breakdown/CellReduction/PotFluxDecayAmp.lean:41`).

**Theorem: The shifted label has angular order M.** The auxiliary label evaluated with shifted parameters has angular frequency M. Source: `Breakdown.PotentialShape.FluxDecay.Internal.labelAzimuth_shifted` (`Breakdown/CellReduction/PotFluxDecayAmp.lean:48`).

**Theorem: Recover the requested flux phase.** The shifted key and rescaled time produce the desired sum of temporal, angular and radial phases inside the complex exponential. Source: `Breakdown.PotentialShape.FluxDecay.Internal.keyPhase_shifted` (`Breakdown/CellReduction/PotFluxDecayAmp.lean:56`).

**Theorem: Express the flux scalar as a shifted key.** The scalar value equals the shifted key phase multiplied by its radial-height scalar amplitude. Source: `Breakdown.PotentialShape.FluxDecay.Internal.scalarValue_eq` (`Breakdown/CellReduction/PotFluxDecayAmp.lean:74`).

**Theorem: Express the flux in a shifted frame.** The flux vector equals the framed field with the component-shifted angular frequency, shifted key, rescaled time and flux amplitudes. Source: `Breakdown.PotentialShape.FluxDecay.Internal.fluxVector_eq` (`Breakdown/CellReduction/PotFluxDecayAmp.lean:82`).

**Theorem: The oscillatory factor has unit norm.** The stated complex oscillatory factor has norm one. Source: `Breakdown.PotentialShape.FluxDecay.Internal.keyPhase_norm` (`Breakdown/CellReduction/PotFluxDecayAmp.lean:94`).

**Theorem: The angular flux factor is nonnegative.** The angular vanishing factor is nonnegative on its prescribed height interval. Source: `Breakdown.PotentialShape.FluxDecay.Internal.angularPart_nonneg` (`Breakdown/CellReduction/PotFluxDecayAmp.lean:98`).

**Theorem: The angular flux factor is at most one.** The angular vanishing factor is at most one on the prescribed height interval. Source: `Breakdown.PotentialShape.FluxDecay.Internal.angularPart_le_one` (`Breakdown/CellReduction/PotFluxDecayAmp.lean:103`).

**Theorem: Discard the inner radial weight.** On the unit radial interval, the radial weight norm is at most the outer factor (1-t) to its outer order. Source: `Breakdown.PotentialShape.FluxDecay.Internal.weightPoly_norm_le` (`Breakdown/CellReduction/PotFluxDecayAmp.lean:115`).

**Theorem: A scaled derivative of the radial weight.** Multiplying the radial-weight derivative magnitude by t(1-t) bounds it by the sum of inner and outer orders times the outer weight. Source: `Breakdown.PotentialShape.FluxDecay.Internal.weightDeriv_bound` (`Breakdown/CellReduction/PotFluxDecayAmp.lean:123`).

**Theorem: An interior height has square below one.** Absolute height strictly below one implies its square is strictly below one. Source: `Breakdown.PotentialShape.FluxDecay.Internal.sq_lt_one_of_abs` (`Breakdown/CellReduction/PotFluxDecayAmp.lean:149`).

**Theorem: Bound the polar angular derivative.** Inside the height interval, the derivative of (1-x squared) times the angular factor exists and has magnitude at most 2k+3. Source: `Breakdown.PotentialShape.FluxDecay.Internal.polarAngular_hasDerivAt` (`Breakdown/CellReduction/PotFluxDecayAmp.lean:153`).

**Theorem: Outer order two for scalar flux data.** The scalar flux amplitude has quadratic outer vanishing, with the same order for its scaled radial derivative and polar-weighted height derivative away from seams. Source: `Breakdown.PotentialShape.FluxDecay.Internal.scalarAmp_bound` (`Breakdown/CellReduction/PotFluxDecayAmp.lean:210`).

**Theorem: Differentiate the amplitude off seams.** Away from the prescribed radial and height seams, the scalar flux amplitude is differentiable in its two coordinates. Source: `Breakdown.PotentialShape.FluxDecay.Internal.scalarAmp_differentiableAt` (`Breakdown/CellReduction/PotFluxDecayAmp.lean:320`).

**Definition: Outer vanishing of a flux amplitude.** This proposition requires that the radial jet mesh ends at one and its endpoint vanishing supplies effective outer order at least two. Source: `Breakdown.PotentialShape.FluxDecay.Internal.FluxScalarEnd` (`Breakdown/CellReduction/PotFluxDecayAmp.lean:348`).

**Theorem: The compactified phase slope is bounded.** The compactified phase slope has absolute value at most twice the absolute phase-bound constant. Source: `Breakdown.PotentialShape.FluxDecay.Internal.phaseSlope_abs_le` (`Breakdown/CellReduction/PotFluxDecayAmp.lean:353`).

**Theorem: Framed divergence keeps outer order two.** The radial, polar and angular contributions to the framed divergence formula are jointly bounded by a constant times the squared chart gap. Source: `Breakdown.PotentialShape.FluxDecay.Internal.framedFormula_bound` (`Breakdown/CellReduction/PotFluxDecayAmp.lean:363`).

### Breakdown.CellReduction.PotFluxDecayJet

Endpoint vanishing of the Hermite jet data becomes polynomial divisibility and quantitative decay at the outer radial edge.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: The jet unit vanishes at the right end.** The nth power of one minus the polynomial variable divides the jet-unit polynomial. Source: `Breakdown.PotentialShape.FluxDecay.Internal.one_sub_pow_dvd_jetUnit` (`Breakdown/CellReduction/PotFluxDecayJet.lean:18`).

**Theorem: Jet unit has its left vanishing order.** The pth power of the polynomial variable divides the jet-unit polynomial. Source: `Breakdown.PotentialShape.FluxDecay.Internal.X_pow_dvd_jetUnit` (`Breakdown/CellReduction/PotFluxDecayJet.lean:22`).

**Theorem: Composition preserves divisibility.** A polynomial divisor remains a divisor after both polynomials are composed with the same polynomial. Source: `Breakdown.PotentialShape.FluxDecay.Internal.comp_dvd_comp` (`Breakdown/CellReduction/PotFluxDecayJet.lean:26`).

**Theorem: The left basis vanishes to right order n.** The nth power of the distance from endpoint one divides the left nodal basis polynomial. Source: `Breakdown.PotentialShape.FluxDecay.Internal.nodalLeft_dvd` (`Breakdown/CellReduction/PotFluxDecayJet.lean:30`).

**Theorem: Right basis has its specified jet order.** The pth power of the distance from endpoint one divides the right nodal basis polynomial. Source: `Breakdown.PotentialShape.FluxDecay.Internal.nodalRight_dvd` (`Breakdown/CellReduction/PotFluxDecayJet.lean:51`).

**Theorem: The bubble has right endpoint order n.** The nth power of the distance from endpoint one divides the bubble polynomial. Source: `Breakdown.PotentialShape.FluxDecay.Internal.bubblePoly_dvd` (`Breakdown/CellReduction/PotFluxDecayJet.lean:64`).

**Theorem: The last radial knot is one.** The last knot of the stated radial mesh equals one. Source: `Breakdown.PotentialShape.FluxDecay.Internal.getD_last_eq` (`Breakdown/CellReduction/PotFluxDecayJet.lean:77`).

**Theorem: The penultimate knot is below one.** Strict ordering of the radial mesh puts its penultimate knot below the final knot one. Source: `Breakdown.PotentialShape.FluxDecay.Internal.getD_before_last_lt` (`Breakdown/CellReduction/PotFluxDecayJet.lean:82`).

**Theorem: Factor the last radial cell.** The last radial cell polynomial is divisible by the zth power of radial coordinate minus one. Source: `Breakdown.PotentialShape.FluxDecay.Internal.lastPiece_dvd` (`Breakdown/CellReduction/PotFluxDecayJet.lean:90`).

**Theorem: Interior knots have a common upper bound.** The finitely many interior knots admit a common nonnegative upper bound strictly below one. Source: `Breakdown.PotentialShape.FluxDecay.Internal.exists_upper_lt_one` (`Breakdown/CellReduction/PotFluxDecayJet.lean:137`).

**Theorem: A nonnegative entry is below the total.** An indexed nonnegative entry is at most the finite double sum containing it. Source: `Breakdown.PotentialShape.FluxDecay.Internal.le_double_sum` (`Breakdown/CellReduction/PotFluxDecayJet.lean:149`).

**Theorem: Cell indices are bounded by list length.** The selected cell index is at most the knot-list length. Source: `Breakdown.PotentialShape.FluxDecay.Internal.cellIndex_le_length` (`Breakdown/CellReduction/PotFluxDecayJet.lean:156`).

**Theorem: Norm of an endpoint power.** For t at most one, the norm of (t-1) to the zth power is (1-t) to the zth power. Source: `Breakdown.PotentialShape.FluxDecay.Internal.norm_sub_one_pow` (`Breakdown/CellReduction/PotFluxDecayJet.lean:162`).

**Theorem: Restore the power after differentiation.** Multiplying the power-rule derivative term by its base restores the original power times its exponent. Source: `Breakdown.PotentialShape.FluxDecay.Internal.mul_pow_pred_eq` (`Breakdown/CellReduction/PotFluxDecayJet.lean:166`).

**Theorem: Endpoint jet controls value and slopes.** Outer vanishing of order z gives that order for the spline value, its radial derivative after one chart-gap factor, and its height derivative, away from their seams. Source: `Breakdown.PotentialShape.FluxDecay.Internal.jetEnd_bound` (`Breakdown/CellReduction/PotFluxDecayJet.lean:171`).

### Breakdown.CellReduction.PotFluxDecayNull

The coordinate axis and finitely many spline seams are negligible for the almost-everywhere flux calculation.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: The first coordinate is nonzero a.e..** The coordinate plane where the first coordinate vanishes has spatial measure zero. Source: `Breakdown.PotentialShape.FluxDecay.Internal.firstCoord_ne_ae` (`Breakdown/CellReduction/PotFluxDecayNull.lean:17`).

**Theorem: Prescribed height-square surface is null.** Almost every spatial point avoids the surface where vertical coordinate squared equals the specified function of horizontal radius squared. Source: `Breakdown.PotentialShape.FluxDecay.Internal.heightSq_ne_ae` (`Breakdown/CellReduction/PotFluxDecayNull.lean:29`).

**Theorem: A fixed radial seam is negligible.** Almost every spatial point avoids the specified compactified radial level. Source: `Breakdown.PotentialShape.FluxDecay.Internal.chartCoord_ne_ae` (`Breakdown/CellReduction/PotFluxDecayNull.lean:61`).

**Theorem: A fixed height seam is negligible.** Almost every spatial point avoids the specified normalized-height level under the stated level restriction. Source: `Breakdown.PotentialShape.FluxDecay.Internal.heightRatio_ne_ae` (`Breakdown/CellReduction/PotFluxDecayNull.lean:83`).

### Breakdown.CellReduction.PotFluxDivergence

Weak divergence is preserved by the finite helical sums that assemble the matrix flux.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Definition: Divergence of a complex vector.** The pointwise divergence sums the three coordinate directional derivatives of the complex vector field. Source: `Breakdown.PotentialShape.pointDivergence` (`Breakdown/CellReduction/PotFluxDivergence.lean:15`).

**Definition: Weak divergence of a complex field.** This proposition requires that the complex vector field has locally integrable components and almost-everywhere derivatives satisfying the distributional divergence identity. Source: `Breakdown.PotentialShape.HasWeakPointDivergence` (`Breakdown/CellReduction/PotFluxDivergence.lean:18`).

**Definition: Weak divergence of the radial flux.** This proposition requires that every valid radial flux component satisfies the complex weak-divergence identity. Source: `Breakdown.PotentialShape.RadialFluxPartWeak` (`Breakdown/CellReduction/PotFluxDivergence.lean:26`).

**Definition: Weak divergence of the polar flux.** This proposition requires that every valid polar flux component satisfies the complex weak-divergence identity. Source: `Breakdown.PotentialShape.PolarFluxPartWeak` (`Breakdown/CellReduction/PotFluxDivergence.lean:31`).

**Theorem: Compact scalar test gives integrability.** Multiplying the locally integrable complex scalar by the compact test function produces an integrable function. Source: `Breakdown.PotentialShape.Internal.integrable_test_mul` (`Breakdown/CellReduction/PotFluxDivergence.lean:38`).

**Theorem: Integrability of a tested derivative.** The compact test derivative times the locally integrable complex scalar is integrable. Source: `Breakdown.PotentialShape.Internal.integrable_testDeriv_mul` (`Breakdown/CellReduction/PotFluxDivergence.lean:44`).

**Theorem: Tested flux contraction is integrable.** The finite sum of test derivatives times locally integrable flux coordinates is integrable. Source: `Breakdown.PotentialShape.Internal.integrable_testDeriv_sum` (`Breakdown/CellReduction/PotFluxDivergence.lean:55`).

**Theorem: Divergence respects finite complex sums.** The pointwise divergence of a finite constant-coefficient flux combination is the same combination of component divergences. Source: `Breakdown.PotentialShape.Internal.pointDivergence_linComb` (`Breakdown/CellReduction/PotFluxDivergence.lean:60`).

**Theorem: Differentiate a finite flux combination.** The finite complex linear combination of differentiable flux coordinates is differentiable. Source: `Breakdown.PotentialShape.Internal.differentiableAt_linComb` (`Breakdown/CellReduction/PotFluxDivergence.lean:73`).

**Theorem: Sum weakly differentiable fluxes.** Finite complex linear combinations preserve the stated weak-divergence property. Source: `Breakdown.PotentialShape.Internal.hasWeakPointDivergence_linComb` (`Breakdown/CellReduction/PotFluxDivergence.lean:78`).

**Definition: One matrix-entry map.** The entry map sends one input coordinate into the chosen output coordinate. Source: `Breakdown.PotentialShape.Internal.entryMap` (`Breakdown/CellReduction/PotFluxDivergence.lean:113`).

**Theorem: A matrix-coordinate inclusion.** The coordinate matrix map sends v to its ith coordinate in output coordinate a and zero in the other coordinates. Source: `Breakdown.PotentialShape.Internal.entryMap_apply` (`Breakdown/CellReduction/PotFluxDivergence.lean:116`).

**Theorem: Reconstruct a matrix from its entries.** A matrix field equals the finite sum of its coordinate entries times the coordinate matrix maps. Source: `Breakdown.PotentialShape.Internal.eq_sum_entryMap` (`Breakdown/CellReduction/PotFluxDivergence.lean:120`).

**Theorem: Divergence is the sum of row derivatives.** Each matrix-divergence coordinate equals the sum of directional derivatives of the corresponding row entries. Source: `Breakdown.PotentialShape.Internal.matrixDivergence_of_entries` (`Breakdown/CellReduction/PotFluxDivergence.lean:133`).

**Theorem: Real parts preserve local integrability.** The real part of a locally integrable complex function is locally integrable. Source: `Breakdown.PotentialShape.Internal.locallyIntegrable_re` (`Breakdown/CellReduction/PotFluxDivergence.lean:148`).

**Theorem: Differentiate the real part.** The derivative of the real part of a complex scalar is real-part projection composed with its derivative. Source: `Breakdown.PotentialShape.Internal.hasFDerivAt_re` (`Breakdown/CellReduction/PotFluxDivergence.lean:154`).

**Theorem: Real flux rows give real divergence.** Each matrix-divergence coordinate is the real part of the pointwise divergence of its complex flux row. Source: `Breakdown.PotentialShape.Internal.matrixDivergence_of_rows` (`Breakdown/CellReduction/PotFluxDivergence.lean:158`).

**Theorem: Assemble matrix divergence from rows.** Weak divergence identities for the complex rows give the real matrix field its distributional divergence. Source: `Breakdown.PotentialShape.Internal.weakMatrixDivergence_of_rows` (`Breakdown/CellReduction/PotFluxDivergence.lean:167`).

**Theorem: Add weakly differentiable fluxes.** The sum of two flux fields with weak divergence again has weak divergence. Source: `Breakdown.PotentialShape.Internal.hasWeakPointDivergence_add` (`Breakdown/CellReduction/PotFluxDivergence.lean:199`).

**Definition: The three helical components.** The finite set consists of the plus, minus and axial components. Source: `Breakdown.PotentialShape.Internal.allComponents` (`Breakdown/CellReduction/PotFluxDivergence.lean:210`).

**Definition: Coefficient for helical reconstruction.** The coefficient is the Cartesian reconstruction of one unit helical component. Source: `Breakdown.PotentialShape.Internal.componentCoef` (`Breakdown/CellReduction/PotFluxDivergence.lean:212`).

**Theorem: Reconstruct from helical components.** A Cartesian component is the weighted sum of the plus, minus and axial complex components. Source: `Breakdown.PotentialShape.Internal.coords_eq_sum` (`Breakdown/CellReduction/PotFluxDivergence.lean:215`).

**Theorem: Flatten key and component reconstruction.** Summing the helical reconstructions over keys equals one finite sum over key-component pairs. Source: `Breakdown.PotentialShape.Internal.sum_coords_eq` (`Breakdown/CellReduction/PotFluxDivergence.lean:221`).

**Definition: One key's vector flux.** The single-key flux reads the selected harmonic and component of the flux data. Source: `Breakdown.PotentialShape.Internal.keyFlux` (`Breakdown/CellReduction/PotFluxDivergence.lean:227`).

**Definition: Assemble one matrix-flux row.** The flux row sums the Cartesian reconstructions of its three helical components over all keys. Source: `Breakdown.PotentialShape.Internal.fluxRow` (`Breakdown/CellReduction/PotFluxDivergence.lean:231`).

**Theorem: Expand each assembled flux row.** Each complex flux row is the coefficient-weighted finite sum of key fluxes over all key-component pairs. Source: `Breakdown.PotentialShape.Internal.fluxRow_eq` (`Breakdown/CellReduction/PotFluxDivergence.lean:235`).

**Theorem: Separate radial and polar flux pieces.** Each key flux is the sum of its radial scalar times the radial frame and polar scalar times the polar frame. Source: `Breakdown.PotentialShape.Internal.keyFlux_eq` (`Breakdown/CellReduction/PotFluxDivergence.lean:241`).

**Theorem: Apply the flux matrix by row entries.** Each output coordinate of the flux matrix applied to v is the dot product of v with the real complex-row entries. Source: `Breakdown.PotentialShape.Internal.fluxMap_apply_eq` (`Breakdown/CellReduction/PotFluxDivergence.lean:247`).

**Theorem: Assemble component flux divergences.** Each real matrix-divergence coordinate is reconstructed from the plus, minus and axial divergences summed over all keys. Source: `Breakdown.PotentialShape.matrixDivergence_fluxMap_apply` (`Breakdown/CellReduction/PotFluxDivergence.lean:254`).

**Theorem: The assembled flux has weak divergence.** The radial and polar weak identities combine into the weak matrix-divergence identity for the full flux. Source: `Breakdown.PotentialShape.fluxMap_weakMatrixDivergence_of` (`Breakdown/CellReduction/PotFluxDivergence.lean:273`).

### Breakdown.CellReduction.PotFluxPolar

Spherical coordinates and integration by parts in polar angle establish the weak divergence identity for the polar flux.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Definition: Tangent in polar angle.** The sphere tangent is the derivative of the spherical point with respect to polar angle. Source: `Breakdown.PotentialShape.Internal.PolarFlux.sphereTangent` (`Breakdown/CellReduction/PotFluxPolar.lean:25`).

**Definition: Polar-direction divergence.** The polar divergence adds the directional derivative along the polar field to its geometric scalar term. Source: `Breakdown.PotentialShape.Internal.PolarFlux.polarDiv` (`Breakdown/CellReduction/PotFluxPolar.lean:29`).

**Theorem: Expand a spherical point in the basis.** A spherical point is the sum of the three unit vectors weighted by r sin(theta) cos(a), r sin(theta) sin(a), and r cos(theta). Source: `Breakdown.PotentialShape.Internal.PolarFlux.sphericalPoint_eq` (`Breakdown/CellReduction/PotFluxPolar.lean:32`).

**Theorem: Cartesian form of a spherical point.** The spherical point has coordinates r sin(theta) cos(a), r sin(theta) sin(a), and r cos(theta). Source: `Breakdown.PotentialShape.Internal.PolarFlux.sphericalPoint_apply` (`Breakdown/CellReduction/PotFluxPolar.lean:38`).

**Theorem: Spherical radius equals the spatial norm.** For nonnegative r, the norm of the spherical point is r. Source: `Breakdown.PotentialShape.Internal.PolarFlux.norm_sphericalPoint` (`Breakdown/CellReduction/PotFluxPolar.lean:42`).

**Theorem: Differentiate the polar angle.** The derivative of the spherical point with respect to polar angle is the sphere tangent vector. Source: `Breakdown.PotentialShape.Internal.PolarFlux.hasDerivAt_sphericalPoint` (`Breakdown/CellReduction/PotFluxPolar.lean:50`).

**Theorem: The spherical polar curve is continuous.** For fixed radius and azimuth, the spherical point depends continuously on polar angle. Source: `Breakdown.PotentialShape.Internal.PolarFlux.continuous_sphericalPoint` (`Breakdown/CellReduction/PotFluxPolar.lean:63`).

**Theorem: Relate the polar frame to its tangent.** Radius times the polar field equals sine of the polar angle times the sphere tangent. Source: `Breakdown.PotentialShape.Internal.PolarFlux.polarField_sphericalPoint` (`Breakdown/CellReduction/PotFluxPolar.lean:66`).

**Theorem: Expand a scalar derivative.** A real scalar linear map applied to a vector equals the sum of its unit-direction values times the vector coordinates. Source: `Breakdown.PotentialShape.Internal.PolarFlux.clm_apply_coords` (`Breakdown/CellReduction/PotFluxPolar.lean:81`).

**Theorem: Pair polar flux with a test gradient.** The sum of test-coordinate derivatives times polar flux coordinates equals the scalar flux amplitude times the test derivative in the polar-field direction. Source: `Breakdown.PotentialShape.Internal.PolarFlux.grad_pairing` (`Breakdown/CellReduction/PotFluxPolar.lean:88`).

**Theorem: Scale the polar tangent derivative.** A linear map applied to the polar field equals its sphere-tangent value scaled by sine of the polar angle divided by radius. Source: `Breakdown.PotentialShape.Internal.PolarFlux.fderiv_polarField_sph` (`Breakdown/CellReduction/PotFluxPolar.lean:96`).

**Theorem: Polar integration by parts on a sphere.** With the spherical Jacobian, the polar divergence tested by a scalar equals minus the polar flux paired with the test derivative along each angular slice. Source: `Breakdown.PotentialShape.Internal.PolarFlux.slice_identity` (`Breakdown/CellReduction/PotFluxPolar.lean:103`).

**Theorem: The weak polar-divergence identity.** The spatial integral of test times polar divergence equals minus the integral of the test-gradient contraction with the polar flux. Source: `Breakdown.PotentialShape.Internal.PolarFlux.weak_identity` (`Breakdown/CellReduction/PotFluxPolar.lean:180`).

**Theorem: The neighbouring height cells agree.** The adjacent height-cell polynomials agree on their shared knot. Source: `Breakdown.PotentialShape.Internal.PolarFlux.jet_atSecond_join` (`Breakdown/CellReduction/PotFluxPolar.lean:213`).

**Theorem: The spline is continuous in height.** At fixed radial coordinate, the joined spline value depends continuously on height. Source: `Breakdown.PotentialShape.Internal.PolarFlux.evalHalf_continuous_height` (`Breakdown/CellReduction/PotFluxPolar.lean:232`).

**Theorem: Differentiate a height-cell polynomial.** Away from height seams, the height derivative of the spline is the height partial derivative of its selected cell polynomial. Source: `Breakdown.PotentialShape.Internal.PolarFlux.evalHalf_hasDerivAt_height` (`Breakdown/CellReduction/PotFluxPolar.lean:247`).

**Theorem: Bound the spline on its chart box.** One nonnegative constant bounds the spline norm when both chart coordinates have magnitude at most one. Source: `Breakdown.PotentialShape.Internal.PolarFlux.evalHalf_bound` (`Breakdown/CellReduction/PotFluxPolar.lean:258`).

**Theorem: Bound selected height derivatives.** One nonnegative constant bounds the height derivatives of all selected cell polynomials on the unit chart box. Source: `Breakdown.PotentialShape.Internal.PolarFlux.evalHalf_height_bound` (`Breakdown/CellReduction/PotFluxPolar.lean:262`).

**Definition: Axis factor for polar integration.** The polar profile multiplies the axis power increased by one by the optional square-root factor. Source: `Breakdown.PotentialShape.Internal.PolarFlux.axisProfile` (`Breakdown/CellReduction/PotFluxPolar.lean:268`).

**Theorem: The polar axis factor is continuous.** The axis factor used for polar integration is continuous. Source: `Breakdown.PotentialShape.Internal.PolarFlux.axisProfile_continuous` (`Breakdown/CellReduction/PotFluxPolar.lean:271`).

**Theorem: The polar axis factor is bounded by one.** The axis factor has absolute value at most one on the prescribed height interval. Source: `Breakdown.PotentialShape.Internal.PolarFlux.axisProfile_abs_le` (`Breakdown/CellReduction/PotFluxPolar.lean:275`).

**Theorem: Combine the axis and sine powers.** With the sine flag, the polar axis factor equals the square root of one minus height squared raised to power 2k+3. Source: `Breakdown.PotentialShape.Internal.PolarFlux.axisProfile_sine_eq` (`Breakdown/CellReduction/PotFluxPolar.lean:289`).

**Theorem: Polar axis factor has bounded derivative.** At an interior height, the polar axis factor has a derivative whose absolute value is at most 2k+3. Source: `Breakdown.PotentialShape.Internal.PolarFlux.axisProfile_deriv` (`Breakdown/CellReduction/PotFluxPolar.lean:300`).

**Theorem: Normalized height is cosine of angle.** The normalized height of a spherical point equals the cosine of its polar angle. Source: `Breakdown.PotentialShape.Internal.PolarFlux.heightRatio_sph` (`Breakdown/CellReduction/PotFluxPolar.lean:345`).

**Theorem: Compactified radius on a sphere.** On a sphere of radius r, the radial chart is r divided by r plus the chart length. Source: `Breakdown.PotentialShape.Internal.PolarFlux.chartCoord_sph` (`Breakdown/CellReduction/PotFluxPolar.lean:350`).

**Theorem: Azimuth does not depend on polar angle.** On the stated spherical domain, the azimuth of a spherical point equals its equatorial azimuth. Source: `Breakdown.PotentialShape.Internal.PolarFlux.pointAngle_sph` (`Breakdown/CellReduction/PotFluxPolar.lean:354`).

**Definition: Phase on a spherical slice.** The slice phase fixes radius, azimuth and time while retaining their harmonic and radial-phase contributions. Source: `Breakdown.PotentialShape.Internal.PolarFlux.sliceFactor` (`Breakdown/CellReduction/PotFluxPolar.lean:366`).

**Definition: Amplitude along a polar slice.** The polar slice amplitude multiplies the endpoint weight, angular vanishing factor and height spline. Source: `Breakdown.PotentialShape.Internal.PolarFlux.sliceProfile` (`Breakdown/CellReduction/PotFluxPolar.lean:371`).

**Theorem: Separate the polar flux along a sphere.** Sine squared times the scalar flux on a fixed sphere equals a radius-and-azimuth factor times its height profile at cosine of the polar angle. Source: `Breakdown.PotentialShape.Internal.PolarFlux.slice_eq` (`Breakdown/CellReduction/PotFluxPolar.lean:375`).

**Theorem: Normalized height has size at most one.** The absolute normalized height is at most one. Source: `Breakdown.PotentialShape.Internal.PolarFlux.heightRatio_abs_le` (`Breakdown/CellReduction/PotFluxPolar.lean:394`).

**Theorem: Square norm as three coordinate squares.** The squared Euclidean norm equals the sum of the three coordinate squares. Source: `Breakdown.PotentialShape.Internal.PolarFlux.norm_sq_coords` (`Breakdown/CellReduction/PotFluxPolar.lean:403`).

**Theorem: Reconstruct from spherical coordinates.** Using spatial norm, arccosine of normalized height and azimuth as spherical coordinates reconstructs the original point. Source: `Breakdown.PotentialShape.Internal.PolarFlux.sph_repr` (`Breakdown/CellReduction/PotFluxPolar.lean:407`).

**Theorem: Scalar flux is differentiable off seams.** The scalar flux is differentiable at the stated point away from the axis and cell seams. Source: `Breakdown.PotentialShape.Internal.PolarFlux.scalarValue_differentiableAt` (`Breakdown/CellReduction/PotFluxPolar.lean:435`).

**Theorem: Coordinate evaluation is measurable.** Each coordinate of a Euclidean vector is a measurable function. Source: `Breakdown.PotentialShape.Internal.PolarFlux.coord_measurable` (`Breakdown/CellReduction/PotFluxPolar.lean:485`).

**Theorem: The polar scalar flux is measurable.** The scalar flux at fixed time is measurable in space. Source: `Breakdown.PotentialShape.Internal.PolarFlux.scalarValue_measurable` (`Breakdown/CellReduction/PotFluxPolar.lean:488`).

**Theorem: The endpoint weight is bounded by one.** On the unit radial interval, the endpoint weight has norm at most one. Source: `Breakdown.PotentialShape.Internal.PolarFlux.weightPoly_norm_le` (`Breakdown/CellReduction/PotFluxPolar.lean:535`).

**Theorem: The radial chart lies in the unit range.** The compactified radius is nonnegative and at most one. Source: `Breakdown.PotentialShape.Internal.PolarFlux.chartCoord_mem` (`Breakdown/CellReduction/PotFluxPolar.lean:542`).

**Theorem: Angular endpoint factor is at most one.** On the prescribed height interval, the axis-power factor with its optional sine has absolute value at most one. Source: `Breakdown.PotentialShape.Internal.PolarFlux.profile_abs_le` (`Breakdown/CellReduction/PotFluxPolar.lean:546`).

**Theorem: The polar scalar flux is bounded.** One nonnegative constant bounds the scalar flux norm throughout space. Source: `Breakdown.PotentialShape.Internal.PolarFlux.scalarValue_bound` (`Breakdown/CellReduction/PotFluxPolar.lean:560`).

**Theorem: The polar frame field is measurable.** The scaled polar frame field is measurable. Source: `Breakdown.PotentialShape.Internal.PolarFlux.polarField_measurable` (`Breakdown/CellReduction/PotFluxPolar.lean:579`).

**Theorem: Measurable polar-frame coordinates.** Each coordinate of the scaled polar frame is measurable. Source: `Breakdown.PotentialShape.Internal.PolarFlux.polarVecQ_measurable` (`Breakdown/CellReduction/PotFluxPolar.lean:582`).

**Theorem: Local integrability from a uniform bound.** The stated bounded measurable function is locally integrable. Source: `Breakdown.PotentialShape.Internal.PolarFlux.locInt_of_bounded` (`Breakdown/CellReduction/PotFluxPolar.lean:588`).

**Theorem: Read divergence from the angular slice.** The polar divergence on a sphere equals the angular slice derivative divided by radius times sine of the polar angle. Source: `Breakdown.PotentialShape.Internal.PolarFlux.polarDiv_of_slice` (`Breakdown/CellReduction/PotFluxPolar.lean:594`).

**Theorem: The polar slice profile is continuous.** The radial-fixed polar slice profile is continuous in height. Source: `Breakdown.PotentialShape.Internal.PolarFlux.sliceProfile_continuous` (`Breakdown/CellReduction/PotFluxPolar.lean:614`).

**Theorem: Bound the polar slice derivative.** Away from height seams, the slice derivative exists and is bounded by (2 times axis power plus 3) times the amplitude bound plus the height-derivative bound. Source: `Breakdown.PotentialShape.Internal.PolarFlux.sliceProfile_hasDerivAt` (`Breakdown/CellReduction/PotFluxPolar.lean:619`).

**Theorem: Off-axis height lies inside the interval.** The specified off-axis point has normalized height of absolute value less than one. Source: `Breakdown.PotentialShape.Internal.PolarFlux.height_abs_lt` (`Breakdown/CellReduction/PotFluxPolar.lean:656`).

**Theorem: Polar divergence has inverse-radius size.** The polar scalar divergence norm is bounded by its amplitude-and-height-slope constant divided by spatial radius. Source: `Breakdown.PotentialShape.Internal.PolarFlux.polarDiv_bound` (`Breakdown/CellReduction/PotFluxPolar.lean:669`).

**Theorem: A fixed radial seam is negligible.** Almost every spatial point avoids the specified compactified radial level. Source: `Breakdown.PotentialShape.Internal.PolarFlux.ae_chartCoord_ne` (`Breakdown/CellReduction/PotFluxPolar.lean:718`).

**Theorem: Polar exceptions have measure zero.** Almost every point has nonzero first and second coordinates and avoids every radial and height spline knot. Source: `Breakdown.PotentialShape.Internal.PolarFlux.ae_generic_point` (`Breakdown/CellReduction/PotFluxPolar.lean:734`).

**Theorem: Differentiate a complex polar coordinate.** The derivative of a complex-valued polar-frame coordinate is coordinate projection of the polar-field derivative followed by real-to-complex inclusion. Source: `Breakdown.PotentialShape.Internal.PolarFlux.polarVecQ_hasFDerivAt` (`Breakdown/CellReduction/PotFluxPolar.lean:745`).

**Theorem: Expand a complex derivative.** A complex-valued real-linear map applied to a real vector is the coordinate-weighted sum of its basis values. Source: `Breakdown.PotentialShape.Internal.PolarFlux.clm_apply_coords_complex` (`Breakdown/CellReduction/PotFluxPolar.lean:755`).

**Theorem: Identify the polar divergence formula.** The sum of diagonal derivatives of the scalar polar flux equals its polar-divergence formula. Source: `Breakdown.PotentialShape.Internal.PolarFlux.div_eq_polarDiv` (`Breakdown/CellReduction/PotFluxPolar.lean:763`).

**Theorem: The polar flux has weak divergence.** The polar flux has locally integrable coordinates, is differentiable almost everywhere, has locally integrable divergence, and satisfies integration by parts against every test function. Source: `Breakdown.PotentialShape.Internal.PolarFlux.polar_weak_of` (`Breakdown/CellReduction/PotFluxPolar.lean:780`).

**Theorem: Almost every radius avoids the seams.** Almost every positive-radius and azimuth pair avoids the finitely many compactified radial seams. Source: `Breakdown.PotentialShape.Internal.PolarFlux.ae_radius_generic` (`Breakdown/CellReduction/PotFluxPolar.lean:807`).

**Theorem: Exceptional polar angles are countable.** The polar angles whose cosines belong to the stated finite set form a countable set. Source: `Breakdown.PotentialShape.Internal.PolarFlux.angles_countable` (`Breakdown/CellReduction/PotFluxPolar.lean:832`).

**Theorem: A scalar polar mode has weak divergence.** The scalar potential mode times the polar frame has locally integrable coordinates, almost-everywhere derivatives and locally integrable divergence satisfying the test-function integration-by-parts identity. Source: `Breakdown.PotentialShape.Internal.PolarFlux.polarScalar_weak` (`Breakdown/CellReduction/PotFluxPolar.lean:839`).

**Theorem: Each polar flux part has weak divergence.** The selected polar flux part has locally integrable coordinates and divergence, is differentiable almost everywhere, and its divergence satisfies integration by parts against every test function. Source: `Breakdown.PotentialShape.polarFluxPart_weakDivergence` (`Breakdown/CellReduction/PotFluxPolar.lean:926`).

### Breakdown.CellReduction.PotFluxRadial

Differentiation along positive rays establishes the radial flux divergence and its weak test identity.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: Reconstruct the unit radial vector.** The coordinate sum of radial-vector components equals the spatial point divided by its norm. Source: `Breakdown.PotentialShape.Internal.RadialFlux.radialVec_sum` (`Breakdown/CellReduction/PotFluxRadial.lean:17`).

**Theorem: Differentiate a radial-frame coordinate.** The derivative of a complex radial-frame coordinate is its real coordinate derivative followed by complex inclusion. Source: `Breakdown.PotentialShape.Internal.RadialFlux.radialVec_hasFDerivAt` (`Breakdown/CellReduction/PotFluxRadial.lean:21`).

**Theorem: Differentiate the weighted radial ray.** At unit scale, the derivative of s squared times u(sy) is the derivative of u applied to y plus twice u(y). Source: `Breakdown.PotentialShape.Internal.RadialFlux.ray_hasDerivAt` (`Breakdown/CellReduction/PotFluxRadial.lean:30`).

**Theorem: Radial divergence as a ray derivative.** The divergence of u times the unit radial field is the derivative of s squared times u(sy) at one divided by spatial radius. Source: `Breakdown.PotentialShape.Internal.RadialFlux.radialPart_divergence` (`Breakdown/CellReduction/PotFluxRadial.lean:42`).

**Theorem: Inverse radius is locally integrable.** A constant times inverse spatial radius is locally integrable in three dimensions. Source: `Breakdown.PotentialShape.Internal.RadialFlux.invNorm_locallyIntegrable` (`Breakdown/CellReduction/PotFluxRadial.lean:64`).

**Theorem: Each unit radial coordinate is bounded.** Every radial-frame coordinate has absolute value at most one. Source: `Breakdown.PotentialShape.Internal.RadialFlux.radialVec_norm_le` (`Breakdown/CellReduction/PotFluxRadial.lean:71`).

**Theorem: The radial flux has weak divergence.** The radial scalar flux has locally integrable coordinates and divergence, is differentiable almost everywhere, and satisfies the test-function integration-by-parts identity. Source: `Breakdown.PotentialShape.Internal.RadialFlux.radialPart_of` (`Breakdown/CellReduction/PotFluxRadial.lean:81`).

**Theorem: The radial ray formula holds a.e..** Almost everywhere, the selected radial flux divergence equals its weighted ray derivative at scale one divided by spatial radius. Source: `Breakdown.PotentialShape.radialFluxPart_divergence_ae` (`Breakdown/CellReduction/PotFluxRadial.lean:151`).

**Theorem: Weak divergence of a radial flux part.** The selected radial flux part has locally integrable coordinates and divergence, is differentiable almost everywhere, and its divergence integrates against every test function as minus the flux paired with the test gradient. Source: `Breakdown.PotentialShape.radialFluxPart_weakDivergence` (`Breakdown/CellReduction/PotFluxRadial.lean:162`).

### Breakdown.CellReduction.PotFluxRadialCell

Joined cell polynomials give the ray regularity and almost-everywhere differentiability of the radial flux amplitude.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Definition: Endpoint-weighted cell polynomial.** The cell polynomial is multiplied by its prescribed inner and outer radial powers. Source: `Breakdown.PotentialShape.Internal.RadialFlux.weightedPiece` (`Breakdown/CellReduction/PotFluxRadialCell.lean:22`).

**Definition: The weighted containing-cell value.** The weighted cell value evaluates the polynomial selected by the radial and height cell indices. Source: `Breakdown.PotentialShape.Internal.RadialFlux.cellValue` (`Breakdown/CellReduction/PotFluxRadialCell.lean:25`).

**Theorem: Evaluate a weighted cell polynomial.** Evaluating the weighted polynomial piece equals its radial endpoint weight times evaluation of the original cell polynomial. Source: `Breakdown.PotentialShape.Internal.RadialFlux.pk_weightedPiece` (`Breakdown/CellReduction/PotFluxRadialCell.lean:28`).

**Theorem: Evaluate the selected weighted cell.** The radial endpoint weight times the spline amplitude equals the selected weighted-cell value. Source: `Breakdown.PotentialShape.Internal.RadialFlux.cellValue_eq` (`Breakdown/CellReduction/PotFluxRadialCell.lean:32`).

**Theorem: Bound cell values and radial derivatives.** One nonnegative constant bounds every selected weighted-cell polynomial and its radial partial derivative on the unit coordinate box. Source: `Breakdown.PotentialShape.Internal.RadialFlux.cellValue_bounds` (`Breakdown/CellReduction/PotFluxRadialCell.lean:37`).

**Theorem: Adjacent radial cell values agree.** The adjacent radial cell polynomials agree at their common radial knot. Source: `Breakdown.PotentialShape.Internal.RadialFlux.piece_join` (`Breakdown/CellReduction/PotFluxRadialCell.lean:66`).

**Theorem: The weighted cell value is continuous.** At fixed height, the joined weighted-cell value is continuous in the radial coordinate. Source: `Breakdown.PotentialShape.Internal.RadialFlux.cellValue_continuous` (`Breakdown/CellReduction/PotFluxRadialCell.lean:89`).

**Theorem: Selected polynomial holds to the right.** In a sufficiently small right neighbourhood, the weighted-cell value equals the polynomial selected at the initial coordinate. Source: `Breakdown.PotentialShape.Internal.RadialFlux.cellValue_right` (`Breakdown/CellReduction/PotFluxRadialCell.lean:110`).

**Definition: The full scalar phase angle.** The scalar phase adds its temporal, azimuthal and squared-radius phase terms. Source: `Breakdown.PotentialShape.Internal.RadialFlux.phaseAngle` (`Breakdown/CellReduction/PotFluxRadialCell.lean:116`).

**Definition: Angular endpoint factor.** The side factor multiplies the axis power by the optional polar sine. Source: `Breakdown.PotentialShape.Internal.RadialFlux.sideFactor` (`Breakdown/CellReduction/PotFluxRadialCell.lean:119`).

**Theorem: Factor the scalar flux value.** The scalar flux is the complex exponential phase times the real side factor times the weighted radial-height cell value. Source: `Breakdown.PotentialShape.Internal.RadialFlux.scalarValue_eq` (`Breakdown/CellReduction/PotFluxRadialCell.lean:122`).

**Theorem: Angular side factor is bounded by one.** The side factor has absolute value at most one. Source: `Breakdown.PotentialShape.Internal.RadialFlux.sideFactor_abs_le` (`Breakdown/CellReduction/PotFluxRadialCell.lean:128`).

**Theorem: Azimuth is unchanged along a ray.** Multiplying a spatial point by a positive scalar leaves its azimuth unchanged. Source: `Breakdown.PotentialShape.Internal.RadialFlux.pointAngle_pos_smul` (`Breakdown/CellReduction/PotFluxRadialCell.lean:149`).

**Theorem: Restrict the scalar flux to a ray.** Along a positive radial ray, angular and side factors stay fixed while the radial phase and compactified radius use the scaled spatial radius. Source: `Breakdown.PotentialShape.Internal.RadialFlux.scalarValue_ray` (`Breakdown/CellReduction/PotFluxRadialCell.lean:157`).

**Theorem: The chart radius lies in [0,1).** The compactified radius lies in the half-open unit interval. Source: `Breakdown.PotentialShape.Internal.RadialFlux.chartCoord_mem` (`Breakdown/CellReduction/PotFluxRadialCell.lean:166`).

**Theorem: The squared-radius phase is continuous.** The radial phase composed with squared spatial norm is continuous. Source: `Breakdown.PotentialShape.Internal.RadialFlux.radialPhase_continuous` (`Breakdown/CellReduction/PotFluxRadialCell.lean:174`).

**Theorem: The radial scalar flux is measurable.** The scalar radial flux at fixed time is measurable in space. Source: `Breakdown.PotentialShape.Internal.RadialFlux.scalarValue_measurable` (`Breakdown/CellReduction/PotFluxRadialCell.lean:181`).

**Theorem: The radial scalar flux is bounded.** One nonnegative constant bounds the radial scalar flux norm throughout space. Source: `Breakdown.PotentialShape.Internal.RadialFlux.scalarValue_bound` (`Breakdown/CellReduction/PotFluxRadialCell.lean:221`).

**Theorem: Differentiate the chart along a ray.** The derivative of sr divided by sr+L is rL divided by (sr+L) squared. Source: `Breakdown.PotentialShape.Internal.RadialFlux.chart_hasDerivAt` (`Breakdown/CellReduction/PotFluxRadialCell.lean:233`).

**Theorem: Bound a weighted cell along a ray.** The derivative of the weighted phased cell along a ray exists and is bounded by the stated scale times the phase and polynomial bounds. Source: `Breakdown.PotentialShape.Internal.RadialFlux.ray_piece_deriv` (`Breakdown/CellReduction/PotFluxRadialCell.lean:240`).

**Theorem: The ray chart is continuous.** The radial chart along the ray is continuous where its denominator is nonzero. Source: `Breakdown.PotentialShape.Internal.RadialFlux.chart_continuousAt` (`Breakdown/CellReduction/PotFluxRadialCell.lean:324`).

**Theorem: The ray chart preserves right limits.** Approaching a ray parameter from the right sends its radial chart coordinate to the corresponding right-sided limit. Source: `Breakdown.PotentialShape.Internal.RadialFlux.chart_tendsto_right` (`Breakdown/CellReduction/PotFluxRadialCell.lean:328`).

**Theorem: The phase along a ray is continuous.** The complex radial phase evaluated along the ray is continuous in its scale parameter. Source: `Breakdown.PotentialShape.Internal.RadialFlux.phase_continuous` (`Breakdown/CellReduction/PotFluxRadialCell.lean:338`).

**Theorem: A uniform slope for the weighted ray.** One constant bounds the Lipschitz slope of s squared times the scalar flux at sy on the scale interval around one, uniformly over nonzero y. Source: `Breakdown.PotentialShape.Internal.RadialFlux.scalarValue_raySlopeBound` (`Breakdown/CellReduction/PotFluxRadialCell.lean:348`).

**Theorem: A cell polynomial is differentiable.** The evaluation of a bivariate cell polynomial is differentiable in its real coordinates. Source: `Breakdown.PotentialShape.Internal.RadialFlux.pk_differentiable` (`Breakdown/CellReduction/PotFluxRadialCell.lean:419`).

**Theorem: A fixed radial seam is negligible.** Almost every spatial point avoids the specified compactified radial level. Source: `Breakdown.PotentialShape.Internal.RadialFlux.ae_chartCoord_ne` (`Breakdown/CellReduction/PotFluxRadialCell.lean:444`).

**Theorem: A fixed height seam is negligible.** Almost every spatial point avoids the specified normalized-height level under the stated level restriction. Source: `Breakdown.PotentialShape.Internal.RadialFlux.ae_heightRatio_ne` (`Breakdown/CellReduction/PotFluxRadialCell.lean:462`).

**Theorem: Off-axis height has square below one.** At the stated off-axis point, normalized height squared is strictly less than one. Source: `Breakdown.PotentialShape.Internal.RadialFlux.heightRatio_sq_lt` (`Breakdown/CellReduction/PotFluxRadialCell.lean:473`).

**Theorem: Almost-everywhere flux differentiability.** Almost every spatial point is nonzero and is a differentiability point of the scalar flux. Source: `Breakdown.PotentialShape.Internal.RadialFlux.scalarValue_ae_differentiable` (`Breakdown/CellReduction/PotFluxRadialCell.lean:482`).

### Breakdown.CellReduction.PotFluxRadialWeak

A rescaling identity turns differentiation along rays into the radial weak divergence formula.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: Positive scaling multiplies the norm.** For positive s, the norm of sy equals s times the norm of y. Source: `Breakdown.PotentialShape.Internal.RadialFlux.smul_norm_pos` (`Breakdown/CellReduction/PotFluxRadialWeak.lean:17`).

**Theorem: Rescale a weighted radial integral.** Spatial rescaling moves the factor s squared from the radial flux to inverse scaling of the scalar test while retaining the inverse-radius weight. Source: `Breakdown.PotentialShape.Internal.RadialFlux.rescaled_integral` (`Breakdown/CellReduction/PotFluxRadialWeak.lean:20`).

**Theorem: Weak integration by parts along rays.** The radial derivative of the test paired with u is integrable, and its integral equals minus the test pairing with the ray derivative D divided by radius. Source: `Breakdown.PotentialShape.Internal.RadialFlux.radialWeak` (`Breakdown/CellReduction/PotFluxRadialWeak.lean:35`).

**Theorem: The ray derivative is measurable a.e..** The derivative at scale one of s squared times u(sy) is strongly measurable almost everywhere as a function of y. Source: `Breakdown.PotentialShape.Internal.RadialFlux.rayDeriv_aestronglyMeasurable` (`Breakdown/CellReduction/PotFluxRadialWeak.lean:124`).

### Breakdown.CellReduction.PotFluxSpherical

Successive cylindrical changes of variables produce the spherical integration formula with Jacobian equal to radius squared times sine of polar angle.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Definition: A point in spherical coordinates.** The spherical point uses cylindrical radius r times sine of polar angle and height r times cosine of polar angle. Source: `Breakdown.PotentialShape.sphericalPoint` (`Breakdown/CellReduction/PotFluxSpherical.lean:11`).

**Definition: The spherical coordinate domain.** The spherical domain has positive radius, polar angle between zero and pi, and azimuth between minus pi and pi. Source: `Breakdown.PotentialShape.sphericalBox` (`Breakdown/CellReduction/PotFluxSpherical.lean:13`).

**Definition: Permutation of the coordinate factors.** The measurable coordinate permutation moves the first coordinate to the end. Source: `Breakdown.PotentialShape.Internal.SphericalChange.turnEquiv` (`Breakdown/CellReduction/PotFluxSpherical.lean:17`).

**Theorem: Cyclically permute three coordinates.** The coordinate equivalence sends the nested triple ((a,b),c) to ((b,c),a). Source: `Breakdown.PotentialShape.Internal.SphericalChange.turnEquiv_apply` (`Breakdown/CellReduction/PotFluxSpherical.lean:20`).

**Theorem: Coordinate permutation preserves volume.** The cyclic coordinate equivalence preserves Lebesgue measure. Source: `Breakdown.PotentialShape.Internal.SphericalChange.turnEquiv_mp` (`Breakdown/CellReduction/PotFluxSpherical.lean:22`).

**Theorem: The permuted cylindrical domain.** The preimage of the cylindrical target under the cyclic permutation is the stated product of a free coordinate, positive radius and open azimuth interval. Source: `Breakdown.PotentialShape.Internal.SphericalChange.turnEquiv_preimage` (`Breakdown/CellReduction/PotFluxSpherical.lean:25`).

**Theorem: Invert the cylindrical map in two parts.** The inverse cylindrical map applies the inverse polar map to its first coordinate pair and retains its last coordinate. Source: `Breakdown.PotentialShape.Internal.SphericalChange.cylMap_symm_pair` (`Breakdown/CellReduction/PotFluxSpherical.lean:30`).

**Theorem: Measurability of the spherical domain.** The spherical parameter box is a measurable set. Source: `Breakdown.PotentialShape.Internal.SphericalChange.box_measurable` (`Breakdown/CellReduction/PotFluxSpherical.lean:32`).

**Theorem: Spherical box fits the cylinder chart.** The spherical parameter box is contained in the cylindrical transformation's target domain. Source: `Breakdown.PotentialShape.Internal.SphericalChange.box_sub` (`Breakdown/CellReduction/PotFluxSpherical.lean:35`).

**Theorem: Identify the transformed spherical box.** The inverse cylindrical image of the spherical box is the stated product domain for the second coordinate change. Source: `Breakdown.PotentialShape.Internal.SphericalChange.image_box` (`Breakdown/CellReduction/PotFluxSpherical.lean:40`).

**Theorem: Compose the two coordinate changes.** The two cylindrical inversions and coordinate permutation give the Cartesian triple r sin(theta) cos(phi), r sin(theta) sin(phi), and r cos(theta). Source: `Breakdown.PotentialShape.Internal.SphericalChange.box_value` (`Breakdown/CellReduction/PotFluxSpherical.lean:72`).

**Theorem: The coordinate composition is spherical.** After conversion to Euclidean space, the composed coordinate changes equal the spherical-point map. Source: `Breakdown.PotentialShape.Internal.SphericalChange.toSpace_box` (`Breakdown/CellReduction/PotFluxSpherical.lean:76`).

**Theorem: Cylindrical change of variables.** The spatial integral equals the integral over cylindrical coordinates with the radial Jacobian factor. Source: `Breakdown.PotentialShape.Internal.SphericalChange.integral_target` (`Breakdown/CellReduction/PotFluxSpherical.lean:83`).

**Theorem: Cylindrical integrability criterion.** Spatial integrability is equivalent to integrability in cylindrical coordinates after multiplication by the radial Jacobian. Source: `Breakdown.PotentialShape.Internal.SphericalChange.integrable_target` (`Breakdown/CellReduction/PotFluxSpherical.lean:91`).

**Theorem: A second polar change of variables.** The integral on the cylindrical target equals the transformed spherical-box integral with the second radial Jacobian factor. Source: `Breakdown.PotentialShape.Internal.SphericalChange.integral_turn` (`Breakdown/CellReduction/PotFluxSpherical.lean:101`).

**Theorem: Integrability after the second change.** Integrability on the cylindrical target is equivalent to integrability of the transformed integrand with its radial Jacobian on the spherical box. Source: `Breakdown.PotentialShape.Internal.SphericalChange.integrable_turn` (`Breakdown/CellReduction/PotFluxSpherical.lean:110`).

**Theorem: The two Jacobians give r squared sine.** The product of the two radial Jacobian factors equals radius squared times sine of polar angle in the spherical integrand. Source: `Breakdown.PotentialShape.Internal.SphericalChange.weight_eq` (`Breakdown/CellReduction/PotFluxSpherical.lean:119`).

**Theorem: Put polar angle in the inner coordinate.** Swapping the parameter coordinates turns the spherical box into positive-radius and azimuth pairs crossed with the polar interval. Source: `Breakdown.PotentialShape.Internal.SphericalChange.swap_preimage_box` (`Breakdown/CellReduction/PotFluxSpherical.lean:128`).

**Theorem: Spherical change of variables.** The spatial integral equals the spherical-box integral weighted by radius squared times sine of polar angle. Source: `Breakdown.PotentialShape.integral_eq_sphericalBox` (`Breakdown/CellReduction/PotFluxSpherical.lean:140`).

**Theorem: Spherical integrability criterion.** A spatial function is integrable exactly when its spherical-coordinate version multiplied by radius squared times sine of polar angle is integrable. Source: `Breakdown.PotentialShape.integrable_iff_sphericalBox` (`Breakdown/CellReduction/PotFluxSpherical.lean:145`).

**Theorem: The iterated spherical integral.** The spatial integral equals the iterated spherical integral with positive radius, polar angle from zero to pi, azimuth from minus pi to pi, and Jacobian r squared sine(theta). Source: `Breakdown.PotentialShape.integral_eq_spherical_radius_polar_azimuth` (`Breakdown/CellReduction/PotFluxSpherical.lean:152`).

**Theorem: Integrability with polar angle innermost.** The weighted spherical integrand is integrable after reordering the parameters so that polar angle is the inner coordinate. Source: `Breakdown.PotentialShape.integrableOn_spherical_polar_inner` (`Breakdown/CellReduction/PotFluxSpherical.lean:171`).

**Theorem: Integrate polar angle first.** The spatial integral equals the radius-and-azimuth integral of the inner polar-angle integral with the spherical Jacobian. Source: `Breakdown.PotentialShape.integral_eq_spherical_polar_inner` (`Breakdown/CellReduction/PotFluxSpherical.lean:178`).

**Theorem: Almost every polar slice is integrable.** For almost every radius-and-azimuth pair, the Jacobian-weighted spherical integrand is integrable over the polar interval. Source: `Breakdown.PotentialShape.spherical_polar_slice_integrable` (`Breakdown/CellReduction/PotFluxSpherical.lean:188`).

**Theorem: Use an interval integral for polar angle.** The spatial integral equals the radius-and-azimuth integral of the polar interval integral from zero to pi with the spherical Jacobian. Source: `Breakdown.PotentialShape.integral_eq_spherical_polar_interval` (`Breakdown/CellReduction/PotFluxSpherical.lean:197`).

**Theorem: Almost every polar slice is integrable.** For almost every radius-and-azimuth pair, the weighted spherical slice is interval-integrable from zero to pi. Source: `Breakdown.PotentialShape.spherical_polar_slice_intervalIntegrable` (`Breakdown/CellReduction/PotFluxSpherical.lean:204`).

### Breakdown.CellReduction.PotGenerator

The selected compact shape field has the weak second derivatives and bounded Hessian needed for a pin generator.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: Change the weak gradient on a null set.** Almost-everywhere equality of gradient representatives preserves the weak-gradient relation. Source: `Breakdown.PotentialShape.Internal.weakGradient_congr_ae` (`Breakdown/CellReduction/PotGenerator.lean:17`).

**Theorem: Differentiate the finite key sum.** The gradient of the shape field is the finite sum of key derivatives composed with real-part reconstruction. Source: `Breakdown.PotentialShape.Internal.fieldGradient_eq_keySum` (`Breakdown/CellReduction/PotGenerator.lean:25`).

**Theorem: Hessian agreement almost everywhere.** For almost every spatial point, the shape-field gradient is differentiable and its classical second derivative equals the supplied shape Hessian. Source: `Breakdown.PotentialShape.Internal.secondDeriv_ae_eq_givenSecond` (`Breakdown/CellReduction/PotGenerator.lean:39`).

**Theorem: Valid data give regular individual keys.** Every key selected by the valid field data satisfies the required key-field smoothness condition. Source: `Breakdown.PotentialShape.Internal.keysSmooth_of_data` (`Breakdown/CellReduction/PotGenerator.lean:65`).

**Theorem: Weak Hessian of a compact shape.** The compact shape field has the stored weak second derivatives and an almost-everywhere bounded classical Hessian. Source: `Breakdown.PotentialShape.compactFieldSecondRegular_holds` (`Breakdown/CellReduction/PotGenerator.lean:74`).

### Breakdown.CellReduction.PotPhi

Scalar regularity and decay are assembled for the first potential in the adjoint decomposition.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: Regularity of the phi potential.** Under the stated hypotheses, the phi potential is continuously differentiable with weak second derivatives and decay orders one, two and three. Source: `Breakdown.PotentialShape.phiPotentialRegular_of` (`Breakdown/CellReduction/PotPhi.lean:15`).

### Breakdown.CellReduction.PotPhiDecay

Finite component sums transport scalar derivative bounds to the vector potential and its Laplacian.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Definition: Helical component in Cartesian form.** Each helical component is mapped linearly into its corresponding three complex Cartesian coordinates. Source: `Breakdown.PotentialShape.componentCoordMap` (`Breakdown/CellReduction/PotPhiDecay.lean:15`).

**Definition: Helical scalar to a real vector.** The component map reconstructs the Cartesian helical vector and then takes its real part. Source: `Breakdown.PotentialShape.componentMap` (`Breakdown/CellReduction/PotPhiDecay.lean:22`).

**Definition: The three helical components.** The finite set consists of the plus, minus and axial components. Source: `Breakdown.PotentialShape.allComponents` (`Breakdown/CellReduction/PotPhiDecay.lean:24`).

**Theorem: Decompose the component maps.** Cartesian reconstruction is the sum of the plus, minus and axial continuous linear component maps. Source: `Breakdown.PotentialShape.coordsOfComponents_eq_maps` (`Breakdown/CellReduction/PotPhiDecay.lean:26`).

**Theorem: Expand the potential by components.** The vector potential is the finite sum over key-component pairs of each scalar component mapped into its real helical vector. Source: `Breakdown.PotentialShape.vectorPotential_eq_sum` (`Breakdown/CellReduction/PotPhiDecay.lean:32`).

**Theorem: Local slopes give derivatives a.e..** The local Lipschitz bounds imply spatial differentiability almost everywhere. Source: `Breakdown.PotentialShape.ae_differentiableAt_of_slopeOn` (`Breakdown/CellReduction/PotPhiDecay.lean:43`).

**Theorem: Trace norm is at most three times norm.** The norm of the second-derivative trace is at most three times the second-derivative operator norm. Source: `Breakdown.PotentialShape.Internal.norm_traceSecond_le` (`Breakdown/CellReduction/PotPhiDecay.lean:60`).

**Theorem: Bound a finite mapped vector sum.** A common denominator bound gives a norm bound for the sum with coefficient equal to the sum of map norms times component bounds. Source: `Breakdown.PotentialShape.Internal.norm_combo_le` (`Breakdown/CellReduction/PotPhiDecay.lean:77`).

**Theorem: Bound the reconstructed gradient sum.** The norm of the reconstructed derivative sum is bounded by the sum of component derivative bounds times reconstruction-map norms over the common denominator. Source: `Breakdown.PotentialShape.Internal.norm_comboDeriv_le` (`Breakdown/CellReduction/PotPhiDecay.lean:84`).

**Theorem: Bound the reconstructed Hessian sum.** The reconstructed second-derivative sum has norm at most the sum of component Hessian bounds times reconstruction-map norms over the common denominator. Source: `Breakdown.PotentialShape.Internal.norm_comboSecond_le` (`Breakdown/CellReduction/PotPhiDecay.lean:92`).

**Theorem: Differentiate the mapped component sum.** The derivative of the finite reconstructed sum is the sum of the component derivatives composed with their fixed reconstruction maps. Source: `Breakdown.PotentialShape.Internal.hasFDerivAt_combo` (`Breakdown/CellReduction/PotPhiDecay.lean:107`).

**Theorem: The derivative of the reconstructed sum.** The derivative function of the reconstructed sum equals the pointwise sum of the mapped component derivatives. Source: `Breakdown.PotentialShape.Internal.fderiv_combo` (`Breakdown/CellReduction/PotPhiDecay.lean:115`).

**Theorem: Differentiate the reconstructed gradient.** The derivative of the finite reconstructed gradient sum is the sum of the component Hessians composed with the reconstruction maps. Source: `Breakdown.PotentialShape.Internal.hasFDerivAt_comboDeriv` (`Breakdown/CellReduction/PotPhiDecay.lean:122`).

**Theorem: Decay survives finite reconstruction.** The finite reconstructed field and its gradient have successive decay orders h and h+1, while its Laplacian trace has order h+2 almost everywhere on each time slice. Source: `Breakdown.PotentialShape.Internal.comboDecay` (`Breakdown/CellReduction/PotPhiDecay.lean:131`).

**Theorem: Successive decay orders of the potential.** The selected vector potential and its gradient have uniform decay orders h and h+1, and its Laplacian trace has order h+2 almost everywhere on each time slice. Source: `Breakdown.PotentialShape.potentialDecay_of_pick` (`Breakdown/CellReduction/PotPhiDecay.lean:176`).

**Theorem: Annular slopes give derivatives a.e..** Lipschitz bounds on annuli imply spatial differentiability almost everywhere. Source: `Breakdown.PotentialShape.ae_differentiableAt_of_annulusSlope` (`Breakdown/CellReduction/PotPhiDecay.lean:201`).

**Theorem: The scalar component is differentiable.** The scalar-part regularity assumptions make the selected component differentiable everywhere. Source: `Breakdown.PotentialShape.componentDifferentiable_of_smooth` (`Breakdown/CellReduction/PotPhiDecay.lean:229`).

**Theorem: Scalar gradient is differentiable a.e..** The scalar-part regularity and slope assumptions make the selected component derivative differentiable almost everywhere. Source: `Breakdown.PotentialShape.componentSecond_ae_of_smooth` (`Breakdown/CellReduction/PotPhiDecay.lean:242`).

**Theorem: Successive decay orders of the potential.** The selected vector potential and its gradient have uniform decay orders h and h+1, and its Laplacian trace has order h+2 almost everywhere on each time slice. Source: `Breakdown.PotentialShape.potentialDecay_of_scalarParts` (`Breakdown/CellReduction/PotPhiDecay.lean:249`).

### Breakdown.CellReduction.PotPressure

The pressure potential combines weak-gradient regularity with its separate decay estimates.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Definition: The pressure has its weak gradient.** This proposition requires that a valid potential series gives measurable pressure whose selected gradient is its distributional gradient on every time slice. Source: `Breakdown.PotentialShape.PressureWeakGradientRegular` (`Breakdown/CellReduction/PotPressure.lean:13`).

**Definition: Decay of pressure and its gradient.** This proposition requires that the pressure decays quadratically and its gradient satisfies the stated radius-weighted bounds almost everywhere. Source: `Breakdown.PotentialShape.PressureDecayRegular` (`Breakdown/CellReduction/PotPressure.lean:18`).

**Theorem: Regularity of the pressure potential.** Under the stated hypotheses, the pressure is measurable with its weak gradient, inverse-square decay and the two radius-weighted gradient bounds. Source: `Breakdown.PotentialShape.pressurePotentialRegular_of` (`Breakdown/CellReduction/PotPressure.lean:24`).

### Breakdown.CellReduction.PotPressureDecay

Weighted spline and phase estimates give inverse-square pressure decay and almost-everywhere control of its gradient.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Definition: Horizontal point in complex form.** The horizontal point encodes the first two real coordinates as a complex number. Source: `Breakdown.PotentialShape.Internal.PressureDecay.planePoint` (`Breakdown/CellReduction/PotPressureDecay.lean:17`).

**Theorem: Square norm of the horizontal coordinate.** The horizontal complex coordinate has squared norm equal to the sum of the first two coordinate squares. Source: `Breakdown.PotentialShape.Internal.PressureDecay.norm_planePoint_sq` (`Breakdown/CellReduction/PotPressureDecay.lean:19`).

**Theorem: Square norm as three coordinate squares.** The squared Euclidean norm equals the sum of the three coordinate squares. Source: `Breakdown.PotentialShape.Internal.PressureDecay.norm_sq_three` (`Breakdown/CellReduction/PotPressureDecay.lean:23`).

**Theorem: Subtract horizontal projections.** The difference of the horizontal complex coordinates equals the horizontal coordinate of the difference. Source: `Breakdown.PotentialShape.Internal.PressureDecay.planePoint_sub` (`Breakdown/CellReduction/PotPressureDecay.lean:27`).

**Theorem: Horizontal norm is bounded by full norm.** The norm of the horizontal complex coordinate is bounded by the full spatial norm. Source: `Breakdown.PotentialShape.Internal.PressureDecay.norm_planePoint_le` (`Breakdown/CellReduction/PotPressureDecay.lean:33`).

**Theorem: Horizontal projection decreases distance.** The distance between horizontal complex coordinates is at most the spatial distance. Source: `Breakdown.PotentialShape.Internal.PressureDecay.planePoint_slopeBound` (`Breakdown/CellReduction/PotPressureDecay.lean:41`).

**Theorem: Complementary squared height identity.** One minus normalized height squared equals horizontal radius squared divided by spatial radius squared. Source: `Breakdown.PotentialShape.Internal.PressureDecay.one_sub_height_sq` (`Breakdown/CellReduction/PotPressureDecay.lean:45`).

**Theorem: Angular phases as unit complex powers.** For nonzero complex input, the angular exponential is the integer power of the normalized complex coordinate. Source: `Breakdown.PotentialShape.Internal.PressureDecay.angle_exp` (`Breakdown/CellReduction/PotPressureDecay.lean:52`).

**Theorem: Complex normalization has norm one.** For nonzero w, multiplying w by the reciprocal of its norm gives norm one. Source: `Breakdown.PotentialShape.Internal.PressureDecay.norm_unit` (`Breakdown/CellReduction/PotPressureDecay.lean:62`).

**Theorem: Bound the difference of unit directions.** The unit-direction difference is at most twice the original complex difference divided by the first norm. Source: `Breakdown.PotentialShape.Internal.PressureDecay.unit_sub_le` (`Breakdown/CellReduction/PotPressureDecay.lean:66`).

**Theorem: Bound natural powers on the unit circle.** The difference of nth powers of unit complex numbers is at most n times their difference. Source: `Breakdown.PotentialShape.Internal.PressureDecay.pow_sub_le_of_norm_one` (`Breakdown/CellReduction/PotPressureDecay.lean:90`).

**Theorem: Bound integer powers on the unit circle.** The difference of Mth integer powers of unit complex numbers is at most |M| times their difference. Source: `Breakdown.PotentialShape.Internal.PressureDecay.zpow_sub_le_of_norm_one` (`Breakdown/CellReduction/PotPressureDecay.lean:102`).

**Theorem: The real exponential phase is Lipschitz.** The distance between exp(i a) and exp(i b) is at most |a-b|. Source: `Breakdown.PotentialShape.Internal.PressureDecay.exp_I_sub_le` (`Breakdown/CellReduction/PotPressureDecay.lean:114`).

**Theorem: Radial phase has an inverse-scale slope.** For arguments bounded below by c>0, the phase difference is at most B/c times the argument difference with one nonnegative B. Source: `Breakdown.PotentialShape.Internal.PressureDecay.phase_slope` (`Breakdown/CellReduction/PotPressureDecay.lean:126`).

**Theorem: The compactified radius lies in [0,1].** The compactified radial coordinate is nonnegative and at most one. Source: `Breakdown.PotentialShape.Internal.PressureDecay.chart_bounds` (`Breakdown/CellReduction/PotPressureDecay.lean:144`).

**Theorem: Chart difference gains two outer factors.** The compactified-radius difference is at most spatial distance times both chart gaps divided by chart length. Source: `Breakdown.PotentialShape.Internal.PressureDecay.chart_diff` (`Breakdown/CellReduction/PotPressureDecay.lean:152`).

**Theorem: Bound the chart gap by inverse radius.** Chart length divided by radius plus chart length is at most max(chart length,1) divided by one plus radius. Source: `Breakdown.PotentialShape.Internal.PressureDecay.chartGap_le` (`Breakdown/CellReduction/PotPressureDecay.lean:167`).

**Theorem: Compare nearby chart gaps.** On the prescribed local region, the nearby chart gap is at most twice the reference radial chart gap. Source: `Breakdown.PotentialShape.Internal.PressureDecay.one_sub_chart_le_double` (`Breakdown/CellReduction/PotPressureDecay.lean:175`).

**Theorem: Compare radii inside the off-axis ball.** Inside the chosen half-horizontal-radius ball, spatial radius lies between half and three halves of the centre radius, and horizontal radius is at least half the centre's. Source: `Breakdown.PotentialShape.Internal.PressureDecay.half_ball_bounds` (`Breakdown/CellReduction/PotPressureDecay.lean:181`).

**Definition: The phased pressure amplitude.** The pressure amplitude multiplies its compactified profile by the constant, angular and radial complex phases. Source: `Breakdown.PotentialShape.Internal.PressureDecay.phasedProfile` (`Breakdown/CellReduction/PotPressureDecay.lean:190`).

**Theorem: Factor the three pressure phases.** The phased profile factors into a constant unit phase, angular and radial unit phases, and the compactified radial-height profile. Source: `Breakdown.PotentialShape.Internal.PressureDecay.phasedProfile_split` (`Breakdown/CellReduction/PotPressureDecay.lean:194`).

**Theorem: Inverse-square phased-profile decay.** The phased profile norm is at most its value constant times max(chart length,1) squared divided by (1+radius) squared. Source: `Breakdown.PotentialShape.Internal.PressureDecay.phasedProfile_value` (`Breakdown/CellReduction/PotPressureDecay.lean:205`).

**Theorem: Combine radial and height slope decay.** The two chart-gap terms combine into an inverse-radius times inverse-square-decay bound with their stated summed coefficient. Source: `Breakdown.PotentialShape.Internal.PressureDecay.decay_rate_combine` (`Breakdown/CellReduction/PotPressureDecay.lean:226`).

**Theorem: Bound the angular phase contribution.** The angular phase difference times the profile size is bounded by 16|M|Cv times chart gap squared over radius times spatial distance. Source: `Breakdown.PotentialShape.Internal.PressureDecay.angleTerm_bound` (`Breakdown/CellReduction/PotPressureDecay.lean:262`).

**Theorem: Bound the radial phase contribution.** The radial phase difference times profile size is bounded by 48|j|BCv times chart gap squared over radius times spatial distance. Source: `Breakdown.PotentialShape.Internal.PressureDecay.radialPhaseTerm_bound` (`Breakdown/CellReduction/PotPressureDecay.lean:316`).

**Theorem: Separate radial and height differences.** The profile difference is bounded by the radial-slope contribution of order chart gap cubed and the height-slope contribution of order chart gap squared over radius. Source: `Breakdown.PotentialShape.Internal.PressureDecay.profileDiff_bound` (`Breakdown/CellReduction/PotPressureDecay.lean:355`).

**Theorem: Split a phased product difference.** The phased-profile difference is at most the angular phase error times profile size plus the radial phase error times profile size plus the profile error. Source: `Breakdown.PotentialShape.Internal.PressureDecay.phase_product_diff_le` (`Breakdown/CellReduction/PotPressureDecay.lean:401`).

**Theorem: A local inverse-cubic pressure slope.** On a ball of half the horizontal radius, the phased profile has Lipschitz constant at most K divided by radius times (1+radius) squared. Source: `Breakdown.PotentialShape.Internal.PressureDecay.phasedProfile_slope` (`Breakdown/CellReduction/PotPressureDecay.lean:413`).

**Theorem: The first coordinate is nonzero a.e..** The coordinate plane where the first coordinate vanishes has spatial measure zero. Source: `Breakdown.PotentialShape.Internal.PressureDecay.ae_first_ne_zero` (`Breakdown/CellReduction/PotPressureDecay.lean:472`).

**Theorem: A nonzero first coordinate is off-axis.** A nonzero first spatial coordinate implies positive horizontal complex norm. Source: `Breakdown.PotentialShape.Internal.PressureDecay.planePoint_pos_of_first` (`Breakdown/CellReduction/PotPressureDecay.lean:484`).

**Theorem: Bound the gradient by the derivative.** The coordinate gradient norm is at most three times the scalar derivative's operator norm. Source: `Breakdown.PotentialShape.Internal.PressureDecay.norm_gradientAt_le` (`Breakdown/CellReduction/PotPressureDecay.lean:489`).

**Theorem: Pressure scalar as a phased profile.** The pressure scalar equals the axis-profile amplitude with its angular, radial and temporal phases. Source: `Breakdown.PotentialShape.Internal.PressureDecay.scalarValue_eq` (`Breakdown/CellReduction/PotPressureDecay.lean:502`).

**Theorem: Decay and slope of each pressure key.** Each pressure key has uniform inverse-square value decay and an off-axis local Lipschitz bound of order one over radius times (1+radius) squared. Source: `Breakdown.PotentialShape.Internal.PressureDecay.pressureKey_bounds` (`Breakdown/CellReduction/PotPressureDecay.lean:510`).

**Theorem: Pressure value and gradient decay.** For valid shape and potential data, one constant gives inverse-square pressure decay and bounds both radius times the pressure-gradient norm and radius cubed times that norm almost everywhere on every time slice. Source: `Breakdown.PotentialShape.pressureValue_decay_bounds` (`Breakdown/CellReduction/PotPressureDecay.lean:540`).

### Breakdown.CellReduction.PotPressureDecayProfile

Outer endpoint vanishing yields the radial decay and slope bounds of the compactified pressure amplitude.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: Interior knots precede the last knot.** Every knot remaining after the endpoints are removed lies below the final endpoint. Source: `Breakdown.PotentialShape.Internal.PressureDecay.interior_lt_last` (`Breakdown/CellReduction/PotPressureDecayProfile.lean:24`).

**Theorem: A finite list stays below one.** A finite list whose members are below one has a common upper bound still below one. Source: `Breakdown.PotentialShape.Internal.PressureDecay.exists_upper_lt_one` (`Breakdown/CellReduction/PotPressureDecayProfile.lean:36`).

**Theorem: Outer coordinate selects the last cell.** Above the prescribed interior threshold, the cell index equals the number of cells minus one. Source: `Breakdown.PotentialShape.Internal.PressureDecay.cellIndex_top` (`Breakdown/CellReduction/PotPressureDecayProfile.lean:45`).

**Theorem: Affine chart preserves an edge factor.** One minus the affine radial coordinate is a constant multiple of one minus the original coordinate. Source: `Breakdown.PotentialShape.Internal.PressureDecay.one_sub_comp_line` (`Breakdown/CellReduction/PotPressureDecayProfile.lean:51`).

**Theorem: Left nodal data vanish at the outer edge.** The nth power of one minus the variable divides the left nodal basis polynomial at the stated outer endpoint. Source: `Breakdown.PotentialShape.Internal.PressureDecay.dvd_nodalLeft` (`Breakdown/CellReduction/PotPressureDecayProfile.lean:65`).

**Theorem: The right nodal endpoint factor.** The pth power of one minus the variable divides the right nodal basis polynomial at the stated outer endpoint. Source: `Breakdown.PotentialShape.Internal.PressureDecay.dvd_nodalRight` (`Breakdown/CellReduction/PotPressureDecayProfile.lean:77`).

**Theorem: Bubble has its outer vanishing factor.** The nth power of one minus the variable divides the bubble polynomial. Source: `Breakdown.PotentialShape.Internal.PressureDecay.dvd_bubble` (`Breakdown/CellReduction/PotPressureDecayProfile.lean:85`).

**Theorem: Each last-cell basis has outer order z.** The zth power of one minus the radial variable divides the selected last-cell degree-of-freedom polynomial. Source: `Breakdown.PotentialShape.Internal.PressureDecay.dvd_dofPoly_last` (`Breakdown/CellReduction/PotPressureDecayProfile.lean:93`).

**Theorem: Factor the outer-cell vanishing.** The last radial cell polynomial factors as the required power of one minus radius times another polynomial. Source: `Breakdown.PotentialShape.Internal.PressureDecay.lastPiece_factor` (`Breakdown/CellReduction/PotPressureDecayProfile.lean:124`).

**Definition: Pressure spline with endpoint powers.** The weighted spline is the radial endpoint polynomial times the stored jet spline. Source: `Breakdown.PotentialShape.Internal.PressureDecay.weightedSpline` (`Breakdown/CellReduction/PotPressureDecayProfile.lean:148`).

**Definition: Effective outer order at least two.** This proposition requires that the stored outer power and jet endpoint vanishing together give order at least two. Source: `Breakdown.PotentialShape.Internal.PressureDecay.EndOrderBound` (`Breakdown/CellReduction/PotPressureDecayProfile.lean:150`).

**Theorem: Quadratic outer pressure vanishing.** Beyond a threshold below one, the weighted spline factors into its inner radial weight, an outer power of order at least two, and a height-cell polynomial. Source: `Breakdown.PotentialShape.Internal.PressureDecay.weightedSpline_lastForm` (`Breakdown/CellReduction/PotPressureDecayProfile.lean:153`).

**Theorem: The endpoint weight is bounded by one.** On the unit interval, the radial endpoint weight has norm at most one. Source: `Breakdown.PotentialShape.Internal.PressureDecay.weight_norm_le` (`Breakdown/CellReduction/PotPressureDecayProfile.lean:172`).

**Theorem: Drop the bounded inner radial factor.** The norm of the inner-outer radial weight is bounded by its outer factor (1-s) to the nth power. Source: `Breakdown.PotentialShape.Internal.PressureDecay.real_weight_norm_le` (`Breakdown/CellReduction/PotPressureDecayProfile.lean:179`).

**Theorem: Higher powers lie below the square.** For a base between zero and one and exponent at least two, its nth power is at most its square. Source: `Breakdown.PotentialShape.Internal.PressureDecay.pow_le_sq_of_two_le` (`Breakdown/CellReduction/PotPressureDecayProfile.lean:188`).

**Theorem: The jet spline is jointly continuous.** The joined jet spline evaluation is continuous in both chart coordinates. Source: `Breakdown.PotentialShape.Internal.PressureDecay.evalHalf_continuous` (`Breakdown/CellReduction/PotPressureDecayProfile.lean:191`).

**Theorem: The weighted spline is continuous.** Multiplying the joined spline by the radial weight preserves joint continuity. Source: `Breakdown.PotentialShape.Internal.PressureDecay.weightedSpline_continuous` (`Breakdown/CellReduction/PotPressureDecayProfile.lean:195`).

**Theorem: Quadratic outer decay of the spline.** The weighted spline norm is bounded uniformly in height by a constant times the squared outer chart gap. Source: `Breakdown.PotentialShape.Internal.PressureDecay.weightedSpline_value` (`Breakdown/CellReduction/PotPressureDecayProfile.lean:200`).

**Definition: Derivative of the endpoint weight.** The endpoint-weight derivative is the product-rule sum for the inner and outer powers. Source: `Breakdown.PotentialShape.Internal.PressureDecay.weightDeriv` (`Breakdown/CellReduction/PotPressureDecayProfile.lean:237`).

**Theorem: Differentiate the endpoint weight.** The derivative of s to the a times (1-s) to the b is the declared radial-weight derivative. Source: `Breakdown.PotentialShape.Internal.PressureDecay.wpoly_hasDerivAt` (`Breakdown/CellReduction/PotPressureDecayProfile.lean:239`).

**Theorem: Bound the endpoint-weight derivative.** The weight derivative norm is at most a+b times the outer factor with exponent b-1. Source: `Breakdown.PotentialShape.Internal.PressureDecay.wpoly_deriv_bound` (`Breakdown/CellReduction/PotPressureDecayProfile.lean:243`).

**Theorem: The radial slope loses one outer power.** The radial difference of the weighted spline is bounded by a constant times the larger outer chart gap times radial distance. Source: `Breakdown.PotentialShape.Internal.PressureDecay.weightedSpline_slope_t` (`Breakdown/CellReduction/PotPressureDecayProfile.lean:274`).

**Theorem: The height slope keeps two outer powers.** The height difference of the weighted spline is bounded by a constant times the squared chart gap times height distance. Source: `Breakdown.PotentialShape.Internal.PressureDecay.weightedSpline_slope_x` (`Breakdown/CellReduction/PotPressureDecayProfile.lean:382`).

**Definition: Axis factor times the pressure spline.** The pressure profile multiplies its weighted spline by the prescribed power of one minus height squared. Source: `Breakdown.PotentialShape.Internal.PressureDecay.axisProfile` (`Breakdown/CellReduction/PotPressureDecayProfile.lean:445`).

**Theorem: The angular square factor is nonnegative.** One minus height squared is nonnegative on the stated height interval. Source: `Breakdown.PotentialShape.Internal.PressureDecay.base_nonneg` (`Breakdown/CellReduction/PotPressureDecayProfile.lean:447`).

**Theorem: The angular square factor is at most one.** One minus height squared is at most one. Source: `Breakdown.PotentialShape.Internal.PressureDecay.base_le_one` (`Breakdown/CellReduction/PotPressureDecayProfile.lean:451`).

**Theorem: The axis power is nonnegative.** The natural power of one minus height squared is nonnegative on the prescribed height interval. Source: `Breakdown.PotentialShape.Internal.PressureDecay.axisPow_nonneg` (`Breakdown/CellReduction/PotPressureDecayProfile.lean:455`).

**Theorem: The axis power is at most one.** The natural axis power is at most one on the prescribed height interval. Source: `Breakdown.PotentialShape.Internal.PressureDecay.axisPow_le_one` (`Breakdown/CellReduction/PotPressureDecayProfile.lean:458`).

**Theorem: The axis power has slope at most 2k.** The difference of kth powers of one minus height squared is at most 2k times the height difference on the normalized interval. Source: `Breakdown.PotentialShape.Internal.PressureDecay.axisPow_slope` (`Breakdown/CellReduction/PotPressureDecayProfile.lean:461`).

**Theorem: Axis-profile value and slope bounds.** The axis profile has quadratic outer vanishing with its axis factor, a radial difference bound with one outer power, and a height difference bound with two outer powers. Source: `Breakdown.PotentialShape.Internal.PressureDecay.axisProfile_bounds` (`Breakdown/CellReduction/PotPressureDecayProfile.lean:485`).

### Breakdown.CellReduction.PotPressureWeak

Lipschitz control on annuli supplies the weak gradient of the pressure assembled from the finite harmonic series.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: The radial chart lies in [0,1].** The compactified radial coordinate lies between zero and one. Source: `Breakdown.PotentialShape.PressureWeak.Internal.chartCoord_mem` (`Breakdown/CellReduction/PotPressureWeak.lean:26`).

**Theorem: Radial-chart slopes on a shell.** On the prescribed shell, the radial-coordinate difference is at most spatial distance divided by the inner radius a. Source: `Breakdown.PotentialShape.PressureWeak.Internal.chartCoord_sub` (`Breakdown/CellReduction/PotPressureWeak.lean:32`).

**Theorem: Normalized-coordinate slopes on a shell.** The normalized coordinate difference is at most four times spatial distance divided by the inner shell radius a. Source: `Breakdown.PotentialShape.PressureWeak.Internal.qOf_sub` (`Breakdown/CellReduction/PotPressureWeak.lean:53`).

**Theorem: The two azimuth definitions agree.** The spatial point-angle definition agrees with the angular coordinate used in the shell estimates. Source: `Breakdown.PotentialShape.PressureWeak.Internal.pointAngle_eq` (`Breakdown/CellReduction/PotPressureWeak.lean:69`).

**Definition: Temporal and radial phase factor.** The radial factor combines the temporal phase with the radial oscillation. Source: `Breakdown.PotentialShape.PressureWeak.Internal.radialPart` (`Breakdown/CellReduction/PotPressureWeak.lean:74`).

**Definition: Phased angular pressure factor.** The angular pressure factor is the azimuthal exponential times the prescribed axis power. Source: `Breakdown.PotentialShape.PressureWeak.Internal.angularPart` (`Breakdown/CellReduction/PotPressureWeak.lean:77`).

**Theorem: The oscillatory factor has unit norm.** The stated complex oscillatory factor has norm one. Source: `Breakdown.PotentialShape.PressureWeak.Internal.radialPart_norm` (`Breakdown/CellReduction/PotPressureWeak.lean:80`).

**Theorem: The angular pressure factor is bounded.** The phased angular-axis factor has norm at most one. Source: `Breakdown.PotentialShape.PressureWeak.Internal.angularPart_norm` (`Breakdown/CellReduction/PotPressureWeak.lean:83`).

**Theorem: The radial phase has a shell slope.** One phase constant bounds the squared-radius phase difference by twice that constant divided by inner radius times spatial distance. Source: `Breakdown.PotentialShape.PressureWeak.Internal.phase_sub` (`Breakdown/CellReduction/PotPressureWeak.lean:92`).

**Theorem: Radial phase has controlled shell slopes.** The temporal-radial phase factor satisfies the shell-slope condition with one nonnegative constant. Source: `Breakdown.PotentialShape.PressureWeak.Internal.radialPart_shell` (`Breakdown/CellReduction/PotPressureWeak.lean:124`).

**Theorem: Lipschitz control on annuli.** Under the stated hypotheses, the field has the stated radius-dependent Lipschitz bound on every positive closed annulus. Source: `Breakdown.PotentialShape.PressureWeak.Internal.angularPart_shell` (`Breakdown/CellReduction/PotPressureWeak.lean:148`).

**Theorem: Radial endpoint weight is bounded by one.** On the unit chart interval, the radial endpoint weight has norm at most one. Source: `Breakdown.PotentialShape.PressureWeak.Internal.weightPoly_norm` (`Breakdown/CellReduction/PotPressureWeak.lean:214`).

**Theorem: The radial endpoint weight is Lipschitz.** The endpoint-weight difference is at most the sum of its two orders times the chart-coordinate difference. Source: `Breakdown.PotentialShape.PressureWeak.Internal.weightPoly_sub` (`Breakdown/CellReduction/PotPressureWeak.lean:220`).

**Theorem: Lipschitz control on annuli.** Under the stated hypotheses, the field has the stated radius-dependent Lipschitz bound on every positive closed annulus. Source: `Breakdown.PotentialShape.PressureWeak.Internal.weight_shell` (`Breakdown/CellReduction/PotPressureWeak.lean:241`).

**Theorem: Bounds and shell slopes for the spline.** The charted jet spline is uniformly bounded and has one nonnegative shell-slope constant. Source: `Breakdown.PotentialShape.PressureWeak.Internal.spline_shell` (`Breakdown/CellReduction/PotPressureWeak.lean:259`).

**Theorem: Multiply uniform scalar bounds.** The norm of the product is bounded by the product of the two uniform norm bounds. Source: `Breakdown.PotentialShape.PressureWeak.Internal.norm_mul_bound` (`Breakdown/CellReduction/PotPressureWeak.lean:288`).

**Theorem: Factor a pressure scalar into four terms.** The scalar pressure mode is the product of the temporal-radial phase, angular-axis factor, radial endpoint weight and charted spline. Source: `Breakdown.PotentialShape.PressureWeak.Internal.scalarValue_eq` (`Breakdown/CellReduction/PotPressureWeak.lean:293`).

**Theorem: Extract the radial factor's time phase.** The radial phase at time sigma equals its time-zero value times the integer-frequency temporal exponential. Source: `Breakdown.PotentialShape.PressureWeak.Internal.radialPart_time` (`Breakdown/CellReduction/PotPressureWeak.lean:308`).

**Theorem: Bound a pressure mode on shells.** Each scalar pressure mode is uniformly bounded in space and satisfies a shell-slope bound. Source: `Breakdown.PotentialShape.PressureWeak.Internal.scalar_shell` (`Breakdown/CellReduction/PotPressureWeak.lean:316`).

**Theorem: Summed pressure modes have shell slopes.** The finite complex pressure sum is uniformly bounded and satisfies a shell-slope bound. Source: `Breakdown.PotentialShape.PressureWeak.Internal.pressure_shell` (`Breakdown/CellReduction/PotPressureWeak.lean:339`).

**Theorem: Write pressure as a temporal Fourier sum.** The real pressure equals the real part of the finite sum of time-zero scalar modes multiplied by their temporal phases. Source: `Breakdown.PotentialShape.PressureWeak.Internal.pressureValue_time` (`Breakdown/CellReduction/PotPressureWeak.lean:356`).

**Theorem: Joint a.e. pressure measurability.** The real pressure is strongly measurable almost everywhere in spacetime. Source: `Breakdown.PotentialShape.PressureWeak.Internal.pressure_jointly_measurable` (`Breakdown/CellReduction/PotPressureWeak.lean:365`).

**Theorem: Measurable pressure and weak gradient.** The pressure is jointly strongly measurable almost everywhere, and on every time slice its classical coordinate gradient is also its weak scalar gradient. Source: `Breakdown.PotentialShape.pressureValue_measurable_weak` (`Breakdown/CellReduction/PotPressureWeak.lean:401`).

### Breakdown.CellReduction.PotPressureWeakShell

A uniform annular slope condition implies local Lipschitz regularity away from the origin and the weak scalar-gradient identity.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Definition: Lipschitz control on annuli.** This proposition requires that the field has the stated radius-dependent Lipschitz bound on every positive closed annulus. Source: `Breakdown.PotentialShape.PressureWeak.Internal.ShellSlope` (`Breakdown/CellReduction/PotPressureWeakShell.lean:20`).

**Theorem: The shell-slope weight is nonnegative.** For the stated positive inner radius, (1+b/a) squared divided by a is nonnegative. Source: `Breakdown.PotentialShape.PressureWeak.Internal.shellWeight_nonneg` (`Breakdown/CellReduction/PotPressureWeakShell.lean:24`).

**Theorem: Shell weight dominates inverse radius.** The shell-slope weight dominates one over the inner radius. Source: `Breakdown.PotentialShape.PressureWeak.Internal.inv_le_shellWeight` (`Breakdown/CellReduction/PotPressureWeakShell.lean:26`).

**Theorem: Shell weight dominates the ratio term.** The shell-slope weight dominates the outer radius divided by inner radius squared. Source: `Breakdown.PotentialShape.PressureWeak.Internal.ratio_le_shellWeight` (`Breakdown/CellReduction/PotPressureWeakShell.lean:30`).

**Theorem: Membership in a closed radial shell.** A point lies in the closed shell exactly when its norm lies between the two shell radii. Source: `Breakdown.PotentialShape.PressureWeak.Internal.mem_shell_iff` (`Breakdown/CellReduction/PotPressureWeakShell.lean:35`).

**Theorem: Lipschitz control on annuli.** Under the stated hypotheses, the field has the stated radius-dependent Lipschitz bound on every positive closed annulus. Source: `Breakdown.PotentialShape.PressureWeak.Internal.ShellSlope.mono` (`Breakdown/CellReduction/PotPressureWeakShell.lean:37`).

**Theorem: Lipschitz control on annuli.** The field has the stated radius-dependent Lipschitz bound on every positive closed annulus. Source: `Breakdown.PotentialShape.PressureWeak.Internal.ShellSlope.const` (`Breakdown/CellReduction/PotPressureWeakShell.lean:42`).

**Theorem: Lipschitz control on annuli.** Under the stated hypotheses, the field has the stated radius-dependent Lipschitz bound on every positive closed annulus. Source: `Breakdown.PotentialShape.PressureWeak.Internal.ShellSlope.add` (`Breakdown/CellReduction/PotPressureWeakShell.lean:46`).

**Theorem: Lipschitz control on annuli.** Under the stated hypotheses, the field has the stated radius-dependent Lipschitz bound on every positive closed annulus. Source: `Breakdown.PotentialShape.PressureWeak.Internal.ShellSlope.mul` (`Breakdown/CellReduction/PotPressureWeakShell.lean:57`).

**Theorem: Lipschitz control on annuli.** Under the stated hypotheses, the field has the stated radius-dependent Lipschitz bound on every positive closed annulus. Source: `Breakdown.PotentialShape.PressureWeak.Internal.ShellSlope.sum` (`Breakdown/CellReduction/PotPressureWeakShell.lean:72`).

**Theorem: A half-radius ball lies in a shell.** The ball around a nonzero point with half its radius lies between half and three halves of that radius. Source: `Breakdown.PotentialShape.PressureWeak.Internal.ball_in_shell` (`Breakdown/CellReduction/PotPressureWeakShell.lean:87`).

**Theorem: Real parts have local Lipschitz constant.** The real part of a shell-controlled field is Lipschitz on the half-radius ball with constant 32C divided by centre radius. Source: `Breakdown.PotentialShape.PressureWeak.Internal.re_slope_ball` (`Breakdown/CellReduction/PotPressureWeakShell.lean:96`).

**Theorem: Local Lipschitz bounds from shell slopes.** The shell-controlled field is Lipschitz on the half-radius ball with constant 32C divided by centre radius. Source: `Breakdown.PotentialShape.PressureWeak.Internal.slope_ball` (`Breakdown/CellReduction/PotPressureWeakShell.lean:114`).

**Theorem: The shell field is continuous off zero.** The annular Lipschitz estimates make the field continuous away from the origin. Source: `Breakdown.PotentialShape.PressureWeak.Internal.ShellSlope.continuousOn` (`Breakdown/CellReduction/PotPressureWeakShell.lean:129`).

**Theorem: Annular Lipschitz bounds for real parts.** The real part of a shell-controlled field has a finite Lipschitz bound on every closed annulus away from the origin. Source: `Breakdown.PotentialShape.PressureWeak.Internal.re_slope_annulus` (`Breakdown/CellReduction/PotPressureWeakShell.lean:135`).

**Theorem: Bound gradient norm by derivative norm.** The coordinate gradient norm is at most three times the scalar derivative's operator norm. Source: `Breakdown.PotentialShape.PressureWeak.Internal.norm_gradient_le` (`Breakdown/CellReduction/PotPressureWeakShell.lean:145`).

**Theorem: Read a gradient coordinate directionally.** Each coordinate of the gradient equals the scalar derivative applied to the corresponding unit vector. Source: `Breakdown.PotentialShape.PressureWeak.Internal.gradient_component` (`Breakdown/CellReduction/PotPressureWeakShell.lean:158`).

**Theorem: Distributional scalar gradient.** Under the stated hypotheses, the scalar and vector fields are locally integrable and obey the test-function integration-by-parts identity. Source: `Breakdown.PotentialShape.PressureWeak.Internal.weakScalarGradient_of_shellSlope` (`Breakdown/CellReduction/PotPressureWeakShell.lean:163`).

### Breakdown.CellReduction.PotScalarDecay

The compactified endpoint order is converted into decay of the scalar field and its first two derivatives.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: An annular neighbourhood of a point.** The annulus between half and twice a nonzero point's radius is a neighbourhood of that point. Source: `Breakdown.PotentialShape.Internal.ScalarDecay.annulus_mem_nhds` (`Breakdown/CellReduction/PotScalarDecay.lean:18`).

**Theorem: Far-field bounds for the angular factor.** The admissible radial-independent angular factor has bounded value, gradient decaying like inverse radius, and local gradient Lipschitz bounds decaying like inverse radius squared. Source: `Breakdown.PotentialShape.Internal.ScalarDecay.angular_farDecay` (`Breakdown/CellReduction/PotScalarDecay.lean:28`).

**Theorem: Large radius enters the outer chart.** Beyond the stated radius threshold, the compactified radial coordinate is at least the chosen number below one. Source: `Breakdown.PotentialShape.Internal.ScalarDecay.chart_ge_of_far` (`Breakdown/CellReduction/PotScalarDecay.lean:43`).

**Theorem: Endpoint vanishing gives scalar decay.** The outer weight and final-cell vanishing give the time-zero scalar mode value, gradient and local gradient Lipschitz bound the inverse-radius orders $h$, $h+1$ and $h+2$. Source: `Breakdown.PotentialShape.Internal.ScalarDecay.far_decay` (`Breakdown/CellReduction/PotScalarDecay.lean:54`).

**Theorem: Combine near and far radial bounds.** The bounded-region estimate and inverse-power far-field estimate combine into the uniform bound $a\leq K/(1+Y)^k$ under the stated coefficient conditions. Source: `Breakdown.PotentialShape.Internal.ScalarDecay.combine_bound` (`Breakdown/CellReduction/PotScalarDecay.lean:107`).

**Theorem: Two slope bounds control the Hessian.** The Hessian norm inside the stated radius is at most the larger of the gradient Lipschitz constants on the inner ball and overlapping annulus. Source: `Breakdown.PotentialShape.Internal.ScalarDecay.second_bound_near` (`Breakdown/CellReduction/PotScalarDecay.lean:135`).

**Theorem: Derive the scalar decay interface.** The regularity interfaces near and away from the origin imply the scalar decay interface for every natural outer order $h$. Source: `Breakdown.PotentialShape.scalarDecayOrder_of` (`Breakdown/CellReduction/PotScalarDecay.lean:158`).

### Breakdown.CellReduction.PotScalarDecayCells

Hermite basis identities isolate the outer cell and build auxiliary angular cutoff splines for the decay proof.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: Polynomial evaluation fixes constants.** Embedding a complex constant as a bivariate polynomial and then evaluating returns that constant. Source: `Breakdown.PotentialShape.Internal.ScalarDecay.evalPair_comp_algebraMap` (`Breakdown/CellReduction/PotScalarDecayCells.lean:22`).

**Theorem: Evaluate the radial polynomial embedding.** Evaluating the first-variable embedding of a univariate polynomial returns its value at the radial coordinate. Source: `Breakdown.PotentialShape.Internal.ScalarDecay.eval_embedFirst` (`Breakdown/CellReduction/PotScalarDecayCells.lean:27`).

**Theorem: Evaluate the height polynomial embedding.** Evaluating the second-variable embedding of a univariate polynomial returns its value at the height coordinate. Source: `Breakdown.PotentialShape.Internal.ScalarDecay.eval_embedSecond` (`Breakdown/CellReduction/PotScalarDecayCells.lean:31`).

**Theorem: Expand a jet spline in its cell bases.** The half-domain spline value is the coefficient-weighted double sum of the radial and height basis polynomials in their containing cells. Source: `Breakdown.PotentialShape.Internal.ScalarDecay.evalHalf_eq` (`Breakdown/CellReduction/PotScalarDecayCells.lean:35`).

**Theorem: Vanishing gives an endpoint factor.** If the first $z$ polynomial derivatives vanish at $b$, the polynomial is divisible by $(X-b)^z$. Source: `Breakdown.PotentialShape.Internal.ScalarDecay.dvd_of_iterate_derivative` (`Breakdown/CellReduction/PotScalarDecayCells.lean:42`).

**Theorem: Separate the temporal phase.** The scalar mode at time $\sigma$ is its time-zero value multiplied by the complex phase at its integer temporal frequency. Source: `Breakdown.PotentialShape.Internal.ScalarDecay.scalarValue_time` (`Breakdown/CellReduction/PotScalarDecayCells.lean:52`).

**Theorem: Weaken a far-field decay order.** A far-field decay bound of order $a$ also gives every order $b\leq a$, including its derivative and local slope bounds. Source: `Breakdown.PotentialShape.Internal.ScalarDecay.farDecay_mono` (`Breakdown/CellReduction/PotScalarDecayCells.lean:66`).

**Theorem: Far-field equality preserves decay.** Two functions that agree outside a fixed ball share the stated far-field decay bound. Source: `Breakdown.PotentialShape.Internal.ScalarDecay.farDecay_congr_far` (`Breakdown/CellReduction/PotScalarDecayCells.lean:76`).

**Theorem: Decay of the compactification tail.** The $n$th power of $L/(|y|+L)$ has far-field decay order $n$ when $L$ is positive. Source: `Breakdown.PotentialShape.Internal.ScalarDecay.tailPow_farDecay` (`Breakdown/CellReduction/PotScalarDecayCells.lean:98`).

**Theorem: Select the cell below the inner knots.** A coordinate below every interior knot has containing-cell index zero. Source: `Breakdown.PotentialShape.Internal.ScalarDecay.cellIndex_eq_zero` (`Breakdown/CellReduction/PotScalarDecayCells.lean:107`).

**Theorem: Select the cell above the inner knots.** A coordinate at or above every interior knot has the final containing-cell index. Source: `Breakdown.PotentialShape.Internal.ScalarDecay.cellIndex_eq_last` (`Breakdown/CellReduction/PotScalarDecayCells.lean:114`).

**Theorem: The cell index stays in range.** The containing-cell index is at most one less than the cell count. Source: `Breakdown.PotentialShape.Internal.ScalarDecay.cellIndex_le'` (`Breakdown/CellReduction/PotScalarDecayCells.lean:120`).

**Theorem: Count the interior mesh knots.** Removing the first and last knots leaves one fewer knot than the number of cells. Source: `Breakdown.PotentialShape.Internal.ScalarDecay.inner_length` (`Breakdown/CellReduction/PotScalarDecayCells.lean:125`).

**Theorem: Interior knots lie between the endpoints.** Every interior knot of the strictly increasing mesh lies strictly between its first and last endpoints. Source: `Breakdown.PotentialShape.Internal.ScalarDecay.inner_bounds` (`Breakdown/CellReduction/PotScalarDecayCells.lean:128`).

**Theorem: Distinct endpoints give a cell.** A knot list with ordered distinct first and last endpoints has at least one cell. Source: `Breakdown.PotentialShape.Internal.ScalarDecay.length_two_le` (`Breakdown/CellReduction/PotScalarDecayCells.lean:144`).

**Theorem: Read the last mesh knot.** Reading the knot at the cell-count index returns the final endpoint. Source: `Breakdown.PotentialShape.Internal.ScalarDecay.getD_last` (`Breakdown/CellReduction/PotScalarDecayCells.lean:154`).

**Theorem: A finite set stays below the endpoint.** A finite list whose entries are strictly below the upper endpoint has a common upper bound still below that endpoint. Source: `Breakdown.PotentialShape.Internal.ScalarDecay.exists_inner_upper` (`Breakdown/CellReduction/PotScalarDecayCells.lean:160`).

**Theorem: Choose the extreme interior knots.** A strictly increasing list of at least two knots has distinct smallest and largest entries that bound every entry in the list. Source: `Breakdown.PotentialShape.Internal.ScalarDecay.exists_inner_ends` (`Breakdown/CellReduction/PotScalarDecayCells.lean:171`).

**Definition: Nodal values with zero derivative data.** The nodal data assign the prescribed value to each order-zero node and zero to higher derivative and bubble degrees of freedom. Source: `Breakdown.PotentialShape.Internal.ScalarDecay.nodeValue` (`Breakdown/CellReduction/PotScalarDecayCells.lean:181`).

**Definition: A spline from height nodal values.** The plateau spline combines constant radial nodal data with the chosen height nodal values and zero derivative data. Source: `Breakdown.PotentialShape.Internal.ScalarDecay.plateauSpline` (`Breakdown/CellReduction/PotScalarDecayCells.lean:185`).

**Theorem: The two value bases sum to one.** The left and right order-zero Hermite basis values for depth two sum to one. Source: `Breakdown.PotentialShape.Internal.ScalarDecay.nodal_sum_eq_one` (`Breakdown/CellReduction/PotScalarDecayCells.lean:188`).

**Theorem: Only the two endpoint values contribute.** The basis expansion with zero derivative and bubble data reduces to the two value basis functions at the cell endpoints. Source: `Breakdown.PotentialShape.Internal.ScalarDecay.nodeValue_sum` (`Breakdown/CellReduction/PotScalarDecayCells.lean:195`).

**Theorem: Evaluate the plateau spline in height.** The plateau spline value is the two-endpoint Hermite interpolation of its height nodal values in the containing height cell. Source: `Breakdown.PotentialShape.Internal.ScalarDecay.plateau_evalHalf` (`Breakdown/CellReduction/PotScalarDecayCells.lean:218`).

**Theorem: The plateau spline has C1 joins.** An admissible depth-two height axis makes the constructed plateau spline a jet spline of radial and height class one. Source: `Breakdown.PotentialShape.Internal.ScalarDecay.plateau_jetClass` (`Breakdown/CellReduction/PotScalarDecayCells.lean:243`).

**Theorem: Vanishing axis cells give zero values.** A spline whose axis cells vanish evaluates to zero whenever the height coordinate belongs to the first or last cell. Source: `Breakdown.PotentialShape.Internal.ScalarDecay.evalHalf_endCell_zero` (`Breakdown/CellReduction/PotScalarDecayCells.lean:249`).

**Theorem: The plateau spline is radial-independent.** Changing the radial coordinate leaves the plateau spline's half-domain value unchanged. Source: `Breakdown.PotentialShape.Internal.ScalarDecay.plateau_tIndep` (`Breakdown/CellReduction/PotScalarDecayCells.lean:269`).

**Theorem: The endpoint height axis is admissible.** The height axis with knots $-1$ and $1$, depth two and no bubble degree satisfies the jet-axis conditions. Source: `Breakdown.PotentialShape.Internal.ScalarDecay.unitAxis` (`Breakdown/CellReduction/PotScalarDecayCells.lean:273`).

**Theorem: Unit nodal values give the constant one.** The plateau spline on the two-endpoint height axis with all nodal values one is identically one. Source: `Breakdown.PotentialShape.Internal.ScalarDecay.ones_evalHalf` (`Breakdown/CellReduction/PotScalarDecayCells.lean:275`).

**Theorem: Zero nodal values give the zero spline.** The plateau spline on the two-endpoint height axis with all nodal values zero vanishes everywhere. Source: `Breakdown.PotentialShape.Internal.ScalarDecay.zero_evalHalf` (`Breakdown/CellReduction/PotScalarDecayCells.lean:281`).

**Theorem: Zero values give zero jet data.** The nodal-data assignment is zero at every degree of freedom when every prescribed value is zero. Source: `Breakdown.PotentialShape.Internal.ScalarDecay.nodeValue_zero` (`Breakdown/CellReduction/PotScalarDecayCells.lean:285`).

**Theorem: The six cutoff knots are ordered.** The stated strict endpoint inequalities make the six height cutoff knots strictly increasing. Source: `Breakdown.PotentialShape.Internal.ScalarDecay.cutoff_sorted` (`Breakdown/CellReduction/PotScalarDecayCells.lean:288`).

**Theorem: Build an admissible angular cutoff.** There is an axis-admissible jet spline independent of radius whose value multiplies the original amplitude without changing it. Source: `Breakdown.PotentialShape.Internal.ScalarDecay.exists_unit_spline` (`Breakdown/CellReduction/PotScalarDecayCells.lean:294`).

### Breakdown.CellReduction.PotScalarDecayFactor

The outer-cell vanishing factor is removed by polynomial interpolation while retaining slope control.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: Factor the outer endpoint vanishing.** Past a common radial threshold, each height slice factors as $(t-1)^z$ times a polynomial whose degree has a uniform bound. Source: `Breakdown.PotentialShape.Internal.ScalarDecay.lastCell_factor` (`Breakdown/CellReduction/PotScalarDecayFactor.lean:18`).

**Theorem: Finite sums preserve controlled slopes.** A finite sum of continuously differentiable amplitudes with locally Lipschitz derivatives has the same regularity. Source: `Breakdown.PotentialShape.Internal.ScalarDecay.slopeRegular_sum` (`Breakdown/CellReduction/PotScalarDecayFactor.lean:100`).

**Theorem: Freeze the radial coordinate.** Fixing the radial coordinate preserves continuous differentiability and local Lipschitz regularity of the amplitude's derivative. Source: `Breakdown.PotentialShape.Internal.ScalarDecay.slopeRegular_slice` (`Breakdown/CellReduction/PotScalarDecayFactor.lean:109`).

**Theorem: Polynomial amplitudes have slope control.** A complex polynomial of the real radial coordinate is continuously differentiable with locally Lipschitz derivative. Source: `Breakdown.PotentialShape.Internal.ScalarDecay.slopeRegular_poly` (`Breakdown/CellReduction/PotScalarDecayFactor.lean:126`).

**Theorem: Choose distinct interpolation nodes.** There are $D+1$ distinct radial interpolation nodes between the chosen threshold and one. Source: `Breakdown.PotentialShape.Internal.ScalarDecay.interp_parts` (`Breakdown/CellReduction/PotScalarDecayFactor.lean:132`).

**Theorem: Interpolate the endpoint quotient.** The amplitude equals its endpoint factor $(t-1)^z$ times the Lagrange interpolation of the quotient values at the chosen radial nodes. Source: `Breakdown.PotentialShape.Internal.ScalarDecay.interp_eq` (`Breakdown/CellReduction/PotScalarDecayFactor.lean:152`).

### Breakdown.CellReduction.PotScalarOff

Axis admissibility removes angular singularities so the scalar potential has a locally Lipschitz derivative away from the origin.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Definition: A Lipschitz bound near a point.** This proposition requires the function to be Lipschitz with some finite constant on a neighbourhood of the specified point. Source: `Breakdown.PotentialShape.Internal.AwayFromOrigin.BoundedSlopeNear` (`Breakdown/CellReduction/PotScalarOff.lean:23`).

**Definition: A local bound on the derivative slope.** This proposition requires continuous differentiability at the point and a Lipschitz bound for the derivative on a neighbourhood. Source: `Breakdown.PotentialShape.Internal.AwayFromOrigin.SlopeNear` (`Breakdown/CellReduction/PotScalarOff.lean:26`).

**Theorem: Local equality preserves a slope bound.** Two functions that agree near the point share a local Lipschitz bound there. Source: `Breakdown.PotentialShape.Internal.AwayFromOrigin.BoundedSlopeNear.congr` (`Breakdown/CellReduction/PotScalarOff.lean:29`).

**Theorem: A C1 function is locally Lipschitz.** Continuous differentiability at the point gives a finite Lipschitz bound on some neighbourhood. Source: `Breakdown.PotentialShape.Internal.AwayFromOrigin.boundedSlopeNear_of_contDiffAt` (`Breakdown/CellReduction/PotScalarOff.lean:39`).

**Theorem: Add local Lipschitz functions.** The sum of two locally Lipschitz functions is locally Lipschitz near the same point. Source: `Breakdown.PotentialShape.Internal.AwayFromOrigin.BoundedSlopeNear.add` (`Breakdown/CellReduction/PotScalarOff.lean:44`).

**Theorem: A bilinear product is locally Lipschitz.** Applying a continuous bilinear map to two locally Lipschitz functions gives a locally Lipschitz function. Source: `Breakdown.PotentialShape.Internal.AwayFromOrigin.BoundedSlopeNear.bilin` (`Breakdown/CellReduction/PotScalarOff.lean:50`).

**Theorem: A C2 function has a Lipschitz derivative.** Twice continuous differentiability at a point gives continuous differentiability and a locally Lipschitz derivative there. Source: `Breakdown.PotentialShape.Internal.AwayFromOrigin.slopeNear_of_two` (`Breakdown/CellReduction/PotScalarOff.lean:86`).

**Theorem: Local equality preserves slope control.** Agreement near a point preserves continuous differentiability and the local Lipschitz bound on the derivative. Source: `Breakdown.PotentialShape.Internal.AwayFromOrigin.SlopeNear.congr` (`Breakdown/CellReduction/PotScalarOff.lean:89`).

**Theorem: Multiply functions with slope control.** The product of two complex functions with local continuous differentiability and Lipschitz derivatives has the same properties. Source: `Breakdown.PotentialShape.Internal.AwayFromOrigin.SlopeNear.mul` (`Breakdown/CellReduction/PotScalarOff.lean:95`).

**Theorem: Composition preserves slope control.** Composing the stated C1 function with a C2 change of variables preserves local continuous differentiability and Lipschitz control of its derivative. Source: `Breakdown.PotentialShape.Internal.AwayFromOrigin.SlopeNear.comp` (`Breakdown/CellReduction/PotScalarOff.lean:107`).

**Theorem: An off-origin derivative bound is global.** A continuous function differentiable away from zero with derivative norm at most $K$ is globally $K$-Lipschitz. Source: `Breakdown.PotentialShape.Internal.AwayFromOrigin.slopeBound_of_derivBound_offZero` (`Breakdown/CellReduction/PotScalarOff.lean:131`).

**Definition: The horizontal complex projection.** The real continuous linear map sends a spatial vector to its first coordinate plus $i$ times its second coordinate. Source: `Breakdown.PotentialShape.Internal.AwayFromOrigin.planeMap` (`Breakdown/CellReduction/PotScalarOff.lean:174`).

**Theorem: Evaluate the horizontal projection.** The horizontal projection of $y$ is $y_0+i y_1$. Source: `Breakdown.PotentialShape.Internal.AwayFromOrigin.planeMap_apply` (`Breakdown/CellReduction/PotScalarOff.lean:178`).

**Definition: A homogeneous angular power.** The angular power multiplies $|z|^D$ by the $M$th integer power of the normalised complex coordinate. Source: `Breakdown.PotentialShape.Internal.AwayFromOrigin.planePower` (`Breakdown/CellReduction/PotScalarOff.lean:181`).

**Theorem: Integer powers are smooth away from zero.** The complex integer-power function has every stated order of complex differentiability at a nonzero point. Source: `Breakdown.PotentialShape.Internal.AwayFromOrigin.zpow_contDiffAt` (`Breakdown/CellReduction/PotScalarOff.lean:183`).

**Theorem: Angular powers are smooth off the axis.** The homogeneous angular power has the stated order of real differentiability at every nonzero complex input. Source: `Breakdown.PotentialShape.Internal.AwayFromOrigin.planePower_contDiffAt_ne` (`Breakdown/CellReduction/PotScalarOff.lean:192`).

**Theorem: Angular powers are homogeneous.** Scaling the complex input by a positive real number scales the angular power by that number to degree $D$. Source: `Breakdown.PotentialShape.Internal.AwayFromOrigin.planePower_homog` (`Breakdown/CellReduction/PotScalarOff.lean:201`).

**Theorem: Positive-degree angular powers vanish.** The homogeneous angular power is zero at the origin when its radial degree is at least one. Source: `Breakdown.PotentialShape.Internal.AwayFromOrigin.planePower_zero` (`Breakdown/CellReduction/PotScalarOff.lean:210`).

**Theorem: Separate an even radial factor.** Increasing the angular power's radial degree by $2k$ multiplies it by the $k$th power of the squared complex norm. Source: `Breakdown.PotentialShape.Internal.AwayFromOrigin.planePower_factor` (`Breakdown/CellReduction/PotScalarOff.lean:213`).

**Theorem: Angular powers are smooth off zero.** The homogeneous angular power has the stated order of real differentiability throughout the punctured complex plane. Source: `Breakdown.PotentialShape.Internal.AwayFromOrigin.planePower_offZero` (`Breakdown/CellReduction/PotScalarOff.lean:218`).

**Theorem: Degree-three angular powers are C2.** Every degree-three homogeneous angular power is twice continuously differentiable on the complex plane. Source: `Breakdown.PotentialShape.Internal.AwayFromOrigin.planePower_three_contDiff` (`Breakdown/CellReduction/PotScalarOff.lean:221`).

**Theorem: Degree-two angular powers are C1.** Every degree-two homogeneous angular power is continuously differentiable on the complex plane. Source: `Breakdown.PotentialShape.Internal.AwayFromOrigin.planePower_two_contDiff` (`Breakdown/CellReduction/PotScalarOff.lean:226`).

**Theorem: A degree-two power has slope control.** The derivative of the degree-two homogeneous angular power has a global finite Lipschitz bound. Source: `Breakdown.PotentialShape.Internal.AwayFromOrigin.planePower_two_slope` (`Breakdown/CellReduction/PotScalarOff.lean:231`).

**Theorem: First harmonics of degree one are C2.** The degree-one angular power is twice continuously differentiable when the absolute angular frequency is one. Source: `Breakdown.PotentialShape.Internal.AwayFromOrigin.planePower_one_contDiff` (`Breakdown/CellReduction/PotScalarOff.lean:243`).

**Theorem: Even radial factors preserve C2.** Multiplication by an even radial power preserves twice continuous differentiability of the homogeneous angular power. Source: `Breakdown.PotentialShape.Internal.AwayFromOrigin.planePower_factor_contDiff` (`Breakdown/CellReduction/PotScalarOff.lean:272`).

**Definition: The total angular vanishing degree.** The angular degree is twice the axis exponent, with one extra degree when the polar-sine factor is present. Source: `Breakdown.PotentialShape.Internal.AwayFromOrigin.angDegree` (`Breakdown/CellReduction/PotScalarOff.lean:279`).

**Definition: The scalar mode's angular factor.** The angular factor combines the azimuthal complex phase, the axis-vanishing power and the optional polar sine. Source: `Breakdown.PotentialShape.Internal.AwayFromOrigin.angPart` (`Breakdown/CellReduction/PotScalarOff.lean:281`).

**Theorem: Express the angular factor homogeneously.** Away from the spatial origin, the angular factor is the homogeneous horizontal angular power divided by the corresponding power of the spatial radius under the stated axis condition. Source: `Breakdown.PotentialShape.Internal.AwayFromOrigin.ang_eq` (`Breakdown/CellReduction/PotScalarOff.lean:285`).

**Theorem: Use the homogeneous formula locally.** The angular factor agrees near the specified point with its homogeneous horizontal representation divided by the spatial radius power. Source: `Breakdown.PotentialShape.Internal.AwayFromOrigin.ang_eventually` (`Breakdown/CellReduction/PotScalarOff.lean:338`).

**Theorem: Inverse radial powers are C2 off zero.** The complex-valued inverse power of the spatial norm is twice continuously differentiable away from the origin. Source: `Breakdown.PotentialShape.Internal.AwayFromOrigin.invPow_contDiffAt` (`Breakdown/CellReduction/PotScalarOff.lean:347`).

**Theorem: Smooth angular powers give slope control.** A C2 homogeneous angular power of positive degree gives an angular factor with a locally Lipschitz derivative away from the spatial origin. Source: `Breakdown.PotentialShape.Internal.AwayFromOrigin.ang_slopeNear_smooth` (`Breakdown/CellReduction/PotScalarOff.lean:352`).

**Theorem: Angular slope control away from the axis.** Where the horizontal projection is nonzero, the angular factor is C1 with locally Lipschitz derivative. Source: `Breakdown.PotentialShape.Internal.AwayFromOrigin.ang_slopeNear_off` (`Breakdown/CellReduction/PotScalarOff.lean:357`).

**Theorem: Slope control for the zero angular mode.** The zero-frequency angular factor without a sine factor is C1 with locally Lipschitz derivative away from the origin. Source: `Breakdown.PotentialShape.Internal.AwayFromOrigin.ang_slopeNear_plain` (`Breakdown/CellReduction/PotScalarOff.lean:363`).

**Theorem: Axis vanishing controls angular slopes.** A positive axis exponent makes the angular factor without a sine factor C1 with locally Lipschitz derivative away from the origin. Source: `Breakdown.PotentialShape.Internal.AwayFromOrigin.ang_slopeNear_square` (`Breakdown/CellReduction/PotScalarOff.lean:372`).

**Theorem: The radial chart is C2 away from zero.** For positive chart length, the compactified radial coordinate is twice continuously differentiable away from the spatial origin. Source: `Breakdown.PotentialShape.Internal.AwayFromOrigin.chartCoord_contDiffAt` (`Breakdown/CellReduction/PotScalarOff.lean:387`).

**Theorem: Normalised height is C2 away from zero.** The ratio of height to radius is twice continuously differentiable away from the spatial origin. Source: `Breakdown.PotentialShape.Internal.AwayFromOrigin.heightRatio_contDiffAt` (`Breakdown/CellReduction/PotScalarOff.lean:393`).

**Theorem: A pulled-back spline has slope control.** The joined spline evaluated at compactified radius and normalised height is C1 with locally Lipschitz derivative away from the origin. Source: `Breakdown.PotentialShape.Internal.AwayFromOrigin.spline_slopeNear` (`Breakdown/CellReduction/PotScalarOff.lean:397`).

**Theorem: A common margin for interior levels.** A finite list of levels strictly inside $(-1,1)$ has a common positive distance from both endpoints. Source: `Breakdown.PotentialShape.Internal.AwayFromOrigin.exists_margin` (`Breakdown/CellReduction/PotScalarOff.lean:407`).

**Theorem: Interior height knots lie inside (-1,1).** Every interior knot of the admissible height mesh has absolute value less than one. Source: `Breakdown.PotentialShape.Internal.AwayFromOrigin.interior_abs_lt` (`Breakdown/CellReduction/PotScalarOff.lean:422`).

**Theorem: Unsupported end-cell bases vanish.** On an end cell, a degree of freedom either meets an end cell or has an identically zero basis polynomial there. Source: `Breakdown.PotentialShape.Internal.AwayFromOrigin.end_dof` (`Breakdown/CellReduction/PotScalarOff.lean:445`).

**Theorem: Zero endpoint data kill the end piece.** Vanishing of the specified endpoint-supporting jet coefficients makes the selected end-cell polynomial zero. Source: `Breakdown.PotentialShape.Internal.AwayFromOrigin.piece_zero_of_end` (`Breakdown/CellReduction/PotScalarOff.lean:464`).

**Theorem: The spline vanishes near both axis ends.** Vanishing axis cells give a common neighbourhood of the height endpoints where the spline is zero at every radial coordinate. Source: `Breakdown.PotentialShape.Internal.AwayFromOrigin.evalHalf_zero_of_abs` (`Breakdown/CellReduction/PotScalarOff.lean:477`).

**Theorem: The spline vanishes near the axis.** At the stated nonzero point on the spatial axis, the pulled-back spline vanishes throughout a neighbourhood when its axis cells vanish. Source: `Breakdown.PotentialShape.Internal.AwayFromOrigin.spline_zero_near_axis` (`Breakdown/CellReduction/PotScalarOff.lean:503`).

**Theorem: Slope control for the angular spline.** Axis admissibility makes the angular factor times the pulled-back joined spline C1 with locally Lipschitz derivative away from the origin. Source: `Breakdown.PotentialShape.Internal.AwayFromOrigin.angSpline_slopeNear` (`Breakdown/CellReduction/PotScalarOff.lean:528`).

**Theorem: The weighted radial phase is C2 off zero.** The radial complex phase multiplied by the endpoint weight is twice continuously differentiable away from the spatial origin. Source: `Breakdown.PotentialShape.Internal.AwayFromOrigin.front_contDiffAt` (`Breakdown/CellReduction/PotScalarOff.lean:569`).

**Theorem: A scalar mode has local slope control.** For valid axis-admissible data, the full scalar potential mode is C1 with locally Lipschitz derivative away from the origin. Source: `Breakdown.PotentialShape.Internal.AwayFromOrigin.scalarValue_slopeNear` (`Breakdown/CellReduction/PotScalarOff.lean:589`).

**Theorem: Prove scalar regularity away from zero.** Valid axis-admissible joined scalar modes are C1 away from zero and have Lipschitz derivatives on every closed annulus bounded away from zero. Source: `Breakdown.PotentialShape.scalarSmoothAwayFromOrigin` (`Breakdown/CellReduction/PotScalarOff.lean:614`).

### Breakdown.CellReduction.PotScalarOrigin

Quadratic vanishing of the amplitude resolves the origin and gives a zero derivative there.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: Extract the quadratic radial factor.** The assumed factor identity allows the full complex product to be regrouped with its quadratic radial factor outside. Source: `Breakdown.PotentialShape.ScalarOrigin.Internal.assemble_eq` (`Breakdown/CellReduction/PotScalarOrigin.lean:19`).

**Theorem: Quadratic scalar vanishing at the origin.** For the stated valid scalar data of effective inner order at least two, the derivative at zero vanishes, the value and gradient have quadratic and linear bounds nearby, and the gradient is locally Lipschitz. Source: `Breakdown.PotentialShape.scalarValue_origin_bounds` (`Breakdown/CellReduction/PotScalarOrigin.lean:29`).

**Theorem: Prove scalar regularity at the origin.** Valid axis-admissible scalar data with effective inner order at least two give C1 regularity at zero and a Lipschitz derivative on a small closed ball. Source: `Breakdown.PotentialShape.scalarSmoothNearOrigin` (`Breakdown/CellReduction/PotScalarOrigin.lean:153`).

### Breakdown.CellReduction.PotScalarOriginAngular

Homogeneous angular factors and their complex-plane representations supply the regularity used in the origin argument.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Definition: The horizontal complex coordinate.** The horizontal coordinate of the spatial point is its first real coordinate plus $i$ times its second. Source: `Breakdown.PotentialShape.ScalarOrigin.Internal.planeOfPoint` (`Breakdown/CellReduction/PotScalarOriginAngular.lean:21`).

**Definition: The conjugate horizontal coordinate.** The conjugate horizontal coordinate is the first coordinate minus $i$ times the second. Source: `Breakdown.PotentialShape.ScalarOrigin.Internal.planeConj` (`Breakdown/CellReduction/PotScalarOriginAngular.lean:23`).

**Definition: Angular phase and axis vanishing.** The angular factor multiplies the integer azimuthal phase by the prescribed axis-vanishing power and optional polar sine. Source: `Breakdown.PotentialShape.ScalarOrigin.Internal.angular` (`Breakdown/CellReduction/PotScalarOriginAngular.lean:25`).

**Definition: The quadratically weighted angular phase.** The phase ring is the complex argument phase at frequency $j$ multiplied by the squared complex radius. Source: `Breakdown.PotentialShape.ScalarOrigin.Internal.phaseRing` (`Breakdown/CellReduction/PotScalarOriginAngular.lean:29`).

**Theorem: Azimuth is the horizontal argument.** The spatial azimuthal angle equals the complex argument of the horizontal coordinate. Source: `Breakdown.PotentialShape.ScalarOrigin.Internal.pointAngle_eq` (`Breakdown/CellReduction/PotScalarOriginAngular.lean:32`).

**Theorem: Complex inclusion preserves real C2.** Viewing the real function as complex-valued preserves twice continuous real differentiability at the point. Source: `Breakdown.PotentialShape.ScalarOrigin.Internal.ofReal_contDiffAt` (`Breakdown/CellReduction/PotScalarOriginAngular.lean:34`).

**Theorem: The horizontal coordinate is C2.** The horizontal complex-coordinate function is twice continuously differentiable. Source: `Breakdown.PotentialShape.ScalarOrigin.Internal.planeOfPoint_contDiff` (`Breakdown/CellReduction/PotScalarOriginAngular.lean:38`).

**Theorem: The conjugate coordinate is C2.** The conjugate horizontal-coordinate function is twice continuously differentiable. Source: `Breakdown.PotentialShape.ScalarOrigin.Internal.planeConj_contDiff` (`Breakdown/CellReduction/PotScalarOriginAngular.lean:45`).

**Theorem: Polar form of the conjugate coordinate.** The conjugate horizontal coordinate equals its modulus times the complex exponential of the negative argument. Source: `Breakdown.PotentialShape.ScalarOrigin.Internal.planeConj_eq` (`Breakdown/CellReduction/PotScalarOriginAngular.lean:52`).

**Theorem: Split horizontal and vertical energy.** The squared spatial norm is the squared horizontal complex norm plus the squared height coordinate. Source: `Breakdown.PotentialShape.ScalarOrigin.Internal.norm_sq_split` (`Breakdown/CellReduction/PotScalarOriginAngular.lean:65`).

**Theorem: Complement of squared normalised height.** One minus the squared normalised height equals the squared horizontal radius divided by the squared spatial radius. Source: `Breakdown.PotentialShape.ScalarOrigin.Internal.one_sub_height` (`Breakdown/CellReduction/PotScalarOriginAngular.lean:69`).

**Theorem: The radius-ratio formula for polar sine.** The polar sine equals the horizontal radius divided by the full spatial radius. Source: `Breakdown.PotentialShape.ScalarOrigin.Internal.polarSine_eq` (`Breakdown/CellReduction/PotScalarOriginAngular.lean:75`).

**Theorem: Normalised height is C2 away from zero.** The height-to-radius ratio is twice continuously differentiable at every nonzero spatial point. Source: `Breakdown.PotentialShape.ScalarOrigin.Internal.heightRatio_contDiffAt` (`Breakdown/CellReduction/PotScalarOriginAngular.lean:78`).

**Theorem: Normalised height on the axis is ±1.** At a nonzero point with zero horizontal projection, normalised height is either one or minus one. Source: `Breakdown.PotentialShape.ScalarOrigin.Internal.heightRatio_axis` (`Breakdown/CellReduction/PotScalarOriginAngular.lean:82`).

**Theorem: Scaling preserves normalised height.** Multiplying a spatial point by a positive scalar leaves its height-to-radius ratio unchanged. Source: `Breakdown.PotentialShape.ScalarOrigin.Internal.heightRatio_smul` (`Breakdown/CellReduction/PotScalarOriginAngular.lean:97`).

**Theorem: Positive scaling preserves azimuth.** Multiplying a spatial point by a positive scalar leaves its azimuthal angle unchanged. Source: `Breakdown.PotentialShape.ScalarOrigin.Internal.pointAngle_smul` (`Breakdown/CellReduction/PotScalarOriginAngular.lean:101`).

**Theorem: Positive scaling preserves polar sine.** Multiplying a spatial point by a positive scalar leaves its polar sine unchanged. Source: `Breakdown.PotentialShape.ScalarOrigin.Internal.polarSine_smul` (`Breakdown/CellReduction/PotScalarOriginAngular.lean:107`).

**Theorem: The weighted phase has slope control.** The quadratically weighted angular phase is differentiable with locally Lipschitz derivative near every complex point. Source: `Breakdown.PotentialShape.ScalarOrigin.Internal.phaseRing_tame` (`Breakdown/CellReduction/PotScalarOriginAngular.lean:110`).

**Theorem: Powers of squared radius are C2.** Every natural power of the squared complex norm, viewed as complex-valued, is twice continuously differentiable. Source: `Breakdown.PotentialShape.ScalarOrigin.Internal.normSq_pow_contDiffAt` (`Breakdown/CellReduction/PotScalarOriginAngular.lean:119`).

**Theorem: Slope control for a flat angular mode.** The zero-frequency angular factor without a sine factor is differentiable with locally Lipschitz derivative near each nonzero point. Source: `Breakdown.PotentialShape.ScalarOrigin.Internal.angular_tame_flat` (`Breakdown/CellReduction/PotScalarOriginAngular.lean:123`).

**Theorem: Slope control for first sine harmonics.** With angular frequency one or minus one, the angular factor with polar sine is differentiable with locally Lipschitz derivative near each nonzero point. Source: `Breakdown.PotentialShape.ScalarOrigin.Internal.angular_tame_sine` (`Breakdown/CellReduction/PotScalarOriginAngular.lean:130`).

**Theorem: Even axis vanishing controls the slope.** A positive axis exponent makes the angular factor without polar sine differentiable with locally Lipschitz derivative near each nonzero point. Source: `Breakdown.PotentialShape.ScalarOrigin.Internal.angular_tame_even` (`Breakdown/CellReduction/PotScalarOriginAngular.lean:151`).

**Theorem: Raise the radial degree and angular mode.** Multiplying the quadratic phase at frequency $j-1$ by the complex coordinate gives the cubic radial factor with angular frequency $j$. Source: `Breakdown.PotentialShape.ScalarOrigin.Internal.phaseRing_mul_plane` (`Breakdown/CellReduction/PotScalarOriginAngular.lean:167`).

**Theorem: Odd axis vanishing controls the slope.** A positive axis exponent makes the angular factor with polar sine differentiable with locally Lipschitz derivative near each nonzero point. Source: `Breakdown.PotentialShape.ScalarOrigin.Internal.angular_tame_odd` (`Breakdown/CellReduction/PotScalarOriginAngular.lean:182`).

**Theorem: Angular slope control off the axis.** When the horizontal projection is nonzero, the angular factor is differentiable with locally Lipschitz derivative nearby. Source: `Breakdown.PotentialShape.ScalarOrigin.Internal.angular_tame_off` (`Breakdown/CellReduction/PotScalarOriginAngular.lean:199`).

**Theorem: Axis admissibility controls the product.** The axis-admissible angular factor times the supplied locally differentiable amplitude has locally Lipschitz derivative when the stated axis-vanishing condition holds. Source: `Breakdown.PotentialShape.ScalarOrigin.Internal.angular_prod_tame` (`Breakdown/CellReduction/PotScalarOriginAngular.lean:231`).

### Breakdown.CellReduction.PotScalarOriginParts

A local Lipschitz derivative and an explicit radial vanishing factor give the origin estimates for the scalar potential.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Definition: A locally Lipschitz derivative.** This proposition requires differentiability on a neighbourhood and a finite Lipschitz bound for the derivative there. Source: `Breakdown.PotentialShape.ScalarOrigin.Internal.TameNear` (`Breakdown/CellReduction/PotScalarOriginParts.lean:27`).

**Theorem: C2 gives local derivative control.** Twice continuous differentiability at a point gives differentiability on a neighbourhood with locally Lipschitz derivative. Source: `Breakdown.PotentialShape.ScalarOrigin.Internal.tameNear_of_contDiffAt` (`Breakdown/CellReduction/PotScalarOriginParts.lean:30`).

**Theorem: Local equality preserves slope control.** Agreement on a neighbourhood preserves local differentiability with a Lipschitz derivative. Source: `Breakdown.PotentialShape.ScalarOrigin.Internal.tameNear_congr` (`Breakdown/CellReduction/PotScalarOriginParts.lean:37`).

**Theorem: Choose a ball with derivative control.** Local differentiability with a Lipschitz derivative yields a positive-radius ball with bounded values and derivatives, and finite Lipschitz bounds for both. Source: `Breakdown.PotentialShape.ScalarOrigin.Internal.tameNear_ball` (`Breakdown/CellReduction/PotScalarOriginParts.lean:48`).

**Theorem: A product map preserves slope bounds.** The stated two-factor difference estimate makes the composite pairing Lipschitz on the set when both input functions are bounded and Lipschitz there. Source: `Breakdown.PotentialShape.ScalarOrigin.Internal.slope_pair` (`Breakdown/CellReduction/PotScalarOriginParts.lean:90`).

**Theorem: Bound a difference of scalar products.** The difference of two scalar-multiplied linear maps is bounded by the first scalar norm times the map difference plus the scalar difference times the second map norm. Source: `Breakdown.PotentialShape.ScalarOrigin.Internal.smul_pair_bound` (`Breakdown/CellReduction/PotScalarOriginParts.lean:109`).

**Theorem: Bound a difference of operator products.** The norm difference of two operator compositions is bounded by the first outer norm times the inner difference plus the outer difference times the second inner norm. Source: `Breakdown.PotentialShape.ScalarOrigin.Internal.comp_pair_bound` (`Breakdown/CellReduction/PotScalarOriginParts.lean:119`).

**Theorem: Multiply locally controlled derivatives.** The product of two complex functions differentiable near the point with Lipschitz derivatives has the same local properties. Source: `Breakdown.PotentialShape.ScalarOrigin.Internal.tameNear_mul` (`Breakdown/CellReduction/PotScalarOriginParts.lean:128`).

**Theorem: Compose locally controlled derivatives.** Composition preserves local differentiability and Lipschitz derivative control at the corresponding points. Source: `Breakdown.PotentialShape.ScalarOrigin.Internal.tameNear_comp` (`Breakdown/CellReduction/PotScalarOriginParts.lean:149`).

**Theorem: Ballwise slope bounds give local control.** A differentiable function whose derivative is Lipschitz on every centred closed ball has locally Lipschitz derivative near each point. Source: `Breakdown.PotentialShape.ScalarOrigin.Internal.tameNear_of_slope` (`Breakdown/CellReduction/PotScalarOriginParts.lean:171`).

**Definition: The spatial rescaling map.** The linear map sends the spatial increment to the pair consisting of zero scale increment and the spatial increment divided by the scale. Source: `Breakdown.PotentialShape.ScalarOrigin.Internal.scaleMap` (`Breakdown/CellReduction/PotScalarOriginParts.lean:183`).

**Theorem: Bound the spatial rescaling norm.** For positive scale, the operator norm of the spatial rescaling map is at most the reciprocal scale. Source: `Breakdown.PotentialShape.ScalarOrigin.Internal.scaleMap_norm` (`Breakdown/CellReduction/PotScalarOriginParts.lean:186`).

**Theorem: Differentiate quadratic scaling.** The quadratic scaling representation gives the derivative of the original function as scale squared times the derivative of the rescaled function composed with the spatial rescaling map. Source: `Breakdown.PotentialShape.ScalarOrigin.Internal.scaled_deriv` (`Breakdown/CellReduction/PotScalarOriginParts.lean:193`).

**Theorem: Quadratic scaling controls the origin.** The stated quadratic scaling and local derivative control imply zero derivative at the origin, quadratic value bounds, linear gradient bounds and a Lipschitz gradient on the small ball. Source: `Breakdown.PotentialShape.ScalarOrigin.Internal.origin_of_scaling` (`Breakdown/CellReduction/PotScalarOriginParts.lean:214`).

**Theorem: A zero derivative kills the coefficient.** If the polynomial's $o$th derivative vanishes at zero, its coefficient of degree $o$ is zero. Source: `Breakdown.PotentialShape.ScalarOrigin.Internal.coeff_eq_zero_of_iterate` (`Breakdown/CellReduction/PotScalarOriginParts.lean:358`).

**Theorem: The first radial cell has positive width.** An admissible radial axis begins at zero, has a positive next knot, and assigns every coordinate below that knot to the first cell. Source: `Breakdown.PotentialShape.ScalarOrigin.Internal.startAxis_facts` (`Breakdown/CellReduction/PotScalarOriginParts.lean:365`).

**Theorem: Interior knots lie between endpoints.** Every interior knot of the ordered mesh lies strictly between the first and last endpoints. Source: `Breakdown.PotentialShape.ScalarOrigin.Internal.interior_bounds` (`Breakdown/CellReduction/PotScalarOriginParts.lean:397`).

**Theorem: The end cells persist near the endpoints.** Near height one the containing cell is the last cell, and near height minus one it is the first cell. Source: `Breakdown.PotentialShape.ScalarOrigin.Internal.endCells_index` (`Breakdown/CellReduction/PotScalarOriginParts.lean:421`).

**Theorem: Initial vanishing gives a radial factor.** A first-cell basis polynomial with no active initial derivatives below order $z$ is divisible by the radial variable to power $z$. Source: `Breakdown.PotentialShape.ScalarOrigin.Internal.startPoly_dvd` (`Breakdown/CellReduction/PotScalarOriginParts.lean:440`).

**Theorem: Height derivatives retain radial factors.** Any stated iterated height derivative leaves the radial monomial factor unchanged and differentiates only the remaining polynomial. Source: `Breakdown.PotentialShape.ScalarOrigin.Internal.xDeriv_X0_mul` (`Breakdown/CellReduction/PotScalarOriginParts.lean:470`).

**Theorem: Height restriction keeps radial factors.** Restricting the height variable to a constant leaves the radial monomial factor unchanged. Source: `Breakdown.PotentialShape.ScalarOrigin.Internal.atSecond_X0_mul` (`Breakdown/CellReduction/PotScalarOriginParts.lean:480`).

**Theorem: Endpoint data eliminate the spline piece.** The specified zero endpoint coefficients force the corresponding end-cell spline polynomial to vanish. Source: `Breakdown.PotentialShape.ScalarOrigin.Internal.endPiece_zero` (`Breakdown/CellReduction/PotScalarOriginParts.lean:484`).

**Theorem: A joined spline has slope control.** A spline joined to class one in both coordinates is differentiable with locally Lipschitz derivative near every parameter point. Source: `Breakdown.PotentialShape.ScalarOrigin.Internal.spline_tame` (`Breakdown/CellReduction/PotScalarOriginParts.lean:504`).

**Theorem: Remove the inner radial vanishing factor.** The initial radial factor can be divided out to give a joined spline quotient, preserving vanishing near the two axis endpoints when the original axis cells vanish. Source: `Breakdown.PotentialShape.ScalarOrigin.Internal.start_quotient` (`Breakdown/CellReduction/PotScalarOriginParts.lean:509`).

### Breakdown.CellReduction.PotTheta

Scalar regularity and decay are assembled for the second potential in the adjoint decomposition.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: Derive theta-potential regularity.** The scalar regularity and order-two decay interfaces imply joint C1 regularity, weak second derivatives and value, gradient and Laplacian decay of orders two, three and four for the theta potential. Source: `Breakdown.PotentialShape.thetaPotentialRegular_of` (`Breakdown/CellReduction/PotTheta.lean:15`).

### Breakdown.CellReduction.PotThetaScalar

The scalar potential contracts separate axis admissibility, regularity away from zero, regularity at zero and decay.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Definition: Axis conditions for angular modes.** This proposition requires a positive axis exponent or vanishing axis cells for nonzero angular modes without sine and for sine modes whose angular frequency has absolute value different from one. Source: `Breakdown.PotentialShape.AxisAdmissible` (`Breakdown/CellReduction/PotThetaScalar.lean:14`).

**Definition: Scalar regularity away from the origin.** This proposition requires valid axis-admissible joined scalar modes to be C1 away from zero with Lipschitz derivatives on every closed annulus bounded away from zero. Source: `Breakdown.PotentialShape.ScalarSmoothAwayFromOrigin` (`Breakdown/CellReduction/PotThetaScalar.lean:18`).

**Definition: Scalar regularity near the origin.** This proposition requires valid axis-admissible scalar modes of effective inner order at least two to be C1 at zero with Lipschitz derivative on a small closed ball. Source: `Breakdown.PotentialShape.ScalarSmoothNearOrigin` (`Breakdown/CellReduction/PotThetaScalar.lean:25`).

**Definition: The scalar decay interface at order h.** This proposition requires one time-uniform constant controlling scalar values and gradients by $(1+|y|)^{-h}$ and $(1+|y|)^{-(h+1)}$, and Hessians almost everywhere by $(1+|y|)^{-(h+2)}$. Source: `Breakdown.PotentialShape.ScalarDecayOrder` (`Breakdown/CellReduction/PotThetaScalar.lean:32`).

**Definition: Admissible selected potential scalars.** This proposition bundles inner order two, the chosen outer order, and the axis-vanishing condition for every selected helical scalar at each key. Source: `Breakdown.PotentialShape.IsPotentialPick` (`Breakdown/CellReduction/PotThetaScalar.lean:39`).

**Theorem: Theta scalars have outer order two.** The theta components of a valid potential series satisfy the selected-scalar conditions with inner and outer orders both two. Source: `Breakdown.PotentialShape.isPotentialPick_theta` (`Breakdown/CellReduction/PotThetaScalar.lean:44`).

**Theorem: Phi scalars have outer order one.** The phi components of a valid potential series satisfy the selected-scalar conditions with inner order two and outer order one. Source: `Breakdown.PotentialShape.isPotentialPick_phi` (`Breakdown/CellReduction/PotThetaScalar.lean:48`).

**Theorem: Selected components meet axis conditions.** Every selected helical scalar satisfies axis admissibility at its shifted azimuthal frequency and its component's sine choice. Source: `Breakdown.PotentialShape.axisAdmissible_of_pick` (`Breakdown/CellReduction/PotThetaScalar.lean:52`).

### Breakdown.CellReduction.PotThetaSmooth

The scalar components combine into a continuously differentiable vector potential with the required weak second derivatives.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: Combine central and annular slope bounds.** A continuous function that is Lipschitz on an inner ball and on every overlapping annulus is Lipschitz on every centred closed ball. Source: `Breakdown.PotentialShape.Internal.slopeOn_closedBall_of_pieces` (`Breakdown/CellReduction/PotThetaSmooth.lean:17`).

**Definition: The positive-helicity coordinate vector.** The positive-helicity vector has coordinates $1/2$, $1/(2i)$ and zero. Source: `Breakdown.PotentialShape.Internal.plusCoords` (`Breakdown/CellReduction/PotThetaSmooth.lean:67`).

**Definition: The negative-helicity coordinate vector.** The negative-helicity vector has coordinates $1/2$, $-1/(2i)$ and zero. Source: `Breakdown.PotentialShape.Internal.minusCoords` (`Breakdown/CellReduction/PotThetaSmooth.lean:69`).

**Definition: The axial coordinate vector.** The axial coordinate vector has first and second coordinates zero and third coordinate one. Source: `Breakdown.PotentialShape.Internal.axialCoords` (`Breakdown/CellReduction/PotThetaSmooth.lean:71`).

**Theorem: Reconstruct Cartesian components.** The Cartesian vector is the linear combination of the positive-helicity, negative-helicity and axial basis vectors with their corresponding component values. Source: `Breakdown.PotentialShape.Internal.coordsOfComponents_eq_smul` (`Breakdown/CellReduction/PotThetaSmooth.lean:73`).

**Definition: Scalar multiplication by a fixed vector.** This real continuous linear map sends a complex scalar to its scalar multiple of the fixed complex vector. Source: `Breakdown.PotentialShape.Internal.scaleToVector` (`Breakdown/CellReduction/PotThetaSmooth.lean:79`).

**Theorem: Evaluate scalar multiplication.** Applying the scalar-to-vector map returns the complex scalar times the fixed vector. Source: `Breakdown.PotentialShape.Internal.scaleToVector_apply` (`Breakdown/CellReduction/PotThetaSmooth.lean:81`).

**Theorem: Factor a rank-one linear map.** The linear map formed by multiplying a scalar functional by a fixed vector equals their composition through the scalar-to-vector map. Source: `Breakdown.PotentialShape.Internal.smulRight_eq_comp` (`Breakdown/CellReduction/PotThetaSmooth.lean:83`).

**Theorem: Lift a scalar derivative's slope bound.** Multiplying the scalar derivative by a fixed vector preserves a Lipschitz bound, scaled by the operator norm of the induced composition map. Source: `Breakdown.PotentialShape.Internal.slopeOn_smulRight` (`Breakdown/CellReduction/PotThetaSmooth.lean:87`).

**Theorem: Reconstruct a field with slope control.** Reconstructing three C1 scalar components with ballwise Lipschitz derivatives gives a C1 vector field whose derivative is Lipschitz on each centred closed ball. Source: `Breakdown.PotentialShape.Internal.keyField_smooth` (`Breakdown/CellReduction/PotThetaSmooth.lean:99`).

**Theorem: Change a weak gradient on a null set.** Replacing a weak-gradient representative by an almost-everywhere equal field preserves the weak-gradient relation. Source: `Breakdown.PotentialShape.Internal.isWeakGradient_congr_ae` (`Breakdown/CellReduction/PotThetaSmooth.lean:128`).

**Theorem: Separate the temporal phase.** The scalar potential mode at a given time is its time-zero value multiplied by the phase at its integer temporal frequency. Source: `Breakdown.PotentialShape.scalarValue_time` (`Breakdown/CellReduction/PotThetaSmooth.lean:138`).

**Theorem: A scalar mode is C1 with slope control.** The two scalar regularity interfaces give global C1 regularity and ballwise Lipschitz derivatives for each valid axis-admissible scalar mode. Source: `Breakdown.PotentialShape.scalar_smooth_of` (`Breakdown/CellReduction/PotThetaSmooth.lean:153`).

**Theorem: Each helical component has slope control.** The scalar regularity interfaces give each admissible selected helical component global C1 regularity and a derivative Lipschitz on every centred closed ball. Source: `Breakdown.PotentialShape.component_smooth_of` (`Breakdown/CellReduction/PotThetaSmooth.lean:168`).

**Theorem: The vector potential is jointly C1.** The scalar regularity interfaces make the vector potential of admissibly selected components continuously differentiable jointly in time and space. Source: `Breakdown.PotentialShape.vectorPotential_contDiff_of` (`Breakdown/CellReduction/PotThetaSmooth.lean:176`).

**Theorem: The vector potential's weak Hessian.** For each time and coordinate direction, the corresponding column of the spatial gradient has the stated second-derivative column as its weak gradient. Source: `Breakdown.PotentialShape.vectorPotential_weakSecond_of` (`Breakdown/CellReduction/PotThetaSmooth.lean:205`).

**Theorem: Ballwise slope of the vector potential.** On each time slice, the admissible vector potential is C1 and its derivative is Lipschitz on every centred closed ball. Source: `Breakdown.PotentialShape.vectorPotential_gradientSlope_of` (`Breakdown/CellReduction/PotThetaSmooth.lean:240`).

### Breakdown.CellReduction.PotentialPartsClosed

The proved radial and polar divergence identities discharge the two flux-part propositions.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: Weak divergence of the radial flux.** Every valid radial flux component satisfies the complex weak-divergence identity. Source: `Breakdown.PotentialShape.radialFluxPartWeak_holds` (`Breakdown/CellReduction/PotentialPartsClosed.lean:28`).

**Theorem: Weak divergence of the polar flux.** Every valid polar flux component satisfies the complex weak-divergence identity. Source: `Breakdown.PotentialShape.polarFluxPartWeak_holds` (`Breakdown/CellReduction/PotentialPartsClosed.lean:31`).

### Breakdown.CellReduction.PotentialShape

The regularity contracts for the two vector potentials, flux, pressure, cell field and generator are assembled for the adjoint construction.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Definition: Regularity of the theta potential.** This proposition requires that the theta potential is continuously differentiable with weak second derivatives and decay orders two, three and four. Source: `Breakdown.PotentialShape.ThetaPotentialRegular` (`Breakdown/CellReduction/PotentialShape.lean:18`).

**Definition: Regularity of the phi potential.** This proposition requires that the phi potential is continuously differentiable with weak second derivatives and decay orders one, two and three. Source: `Breakdown.PotentialShape.PhiPotentialRegular` (`Breakdown/CellReduction/PotentialShape.lean:27`).

**Definition: Regularity of the matrix flux.** This proposition requires that the matrix flux is measurable with its weak divergence, inverse-square decay and the stated radius-weighted divergence decay. Source: `Breakdown.PotentialShape.FluxPotentialRegular` (`Breakdown/CellReduction/PotentialShape.lean:36`).

**Definition: Regularity of the pressure potential.** This proposition requires that the pressure is measurable with its weak gradient, inverse-square decay and the two radius-weighted gradient bounds. Source: `Breakdown.PotentialShape.PressurePotentialRegular` (`Breakdown/CellReduction/PotentialShape.lean:43`).

**Definition: Regularity of a cylindrical cell field.** This proposition requires that the cylindrical cell field has its measurable weak gradient, finite period gradient energy and the prescribed compact support. Source: `Breakdown.PotentialShape.CellPotentialRegular` (`Breakdown/CellReduction/PotentialShape.lean:50`).

**Definition: Weak Hessian of a compact shape.** This proposition requires that the compact shape field has the stored weak second derivatives and an almost-everywhere bounded classical Hessian. Source: `Breakdown.PotentialShape.CompactFieldSecondRegular` (`Breakdown/CellReduction/PotentialShape.lean:58`).

**Definition: The analytic potential components.** This proposition requires that the theta, phi, flux, pressure, cell and generator regularity interfaces and shape support conditions all hold. Source: `Breakdown.PotentialShape.PotentialPieces` (`Breakdown/CellReduction/PotentialShape.lean:65`).

**Theorem: Increase the potential bound.** The potential data remain admissible after increasing their common bound. Source: `Breakdown.PotentialShape.potentialData_mono` (`Breakdown/CellReduction/PotentialShape.lean:76`).

**Theorem: A valid entry supplies pin data.** The valid pin-shape entry yields common constants for the pin field and pin potential admissibility conditions. Source: `Breakdown.PotentialShape.pinData_of_entry` (`Breakdown/CellReduction/PotentialShape.lean:123`).

### Breakdown.CellReduction.ProfileFieldApprox

Mollification and spatial cutoff approximate weak profile fields in both gradient and Laplacian energy.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Definition: Exterior beyond a radius.** The tail set consists of points whose norm is at least the cutoff radius. Source: `Breakdown.CertReduction.Internal.ProfileFieldApprox.tailSet` (`Breakdown/CellReduction/ProfileFieldApprox.lean:25`).

**Definition: The cutoff annulus.** The ring set consists of points between the cutoff radius and twice that radius. Source: `Breakdown.CertReduction.Internal.ProfileFieldApprox.ringSet` (`Breakdown/CellReduction/ProfileFieldApprox.lean:27`).

**Definition: Convolution with the normalized bump.** The smoothed field is the convolution of the original field with the normalized spatial bump. Source: `Breakdown.CertReduction.Internal.ProfileFieldApprox.smoothed` (`Breakdown/CellReduction/ProfileFieldApprox.lean:29`).

**Theorem: The exterior region is measurable.** The region outside the chosen radius is a measurable set. Source: `Breakdown.CertReduction.Internal.ProfileFieldApprox.tailSet_measurable` (`Breakdown/CellReduction/ProfileFieldApprox.lean:32`).

**Theorem: A set indicator is nonnegative.** The indicator of a set with value one is nonnegative everywhere. Source: `Breakdown.CertReduction.Internal.ProfileFieldApprox.ind_nonneg` (`Breakdown/CellReduction/ProfileFieldApprox.lean:35`).

**Theorem: A set indicator is at most one.** The indicator of a set with value one never exceeds one. Source: `Breakdown.CertReduction.Internal.ProfileFieldApprox.ind_le_one` (`Breakdown/CellReduction/ProfileFieldApprox.lean:38`).

**Theorem: Split a square using a sixth power.** For any positive splitting parameter s, the scalar square t² is bounded by s plus t⁶ divided by s². Source: `Breakdown.CertReduction.Internal.ProfileFieldApprox.sq_le_split` (`Breakdown/CellReduction/ProfileFieldApprox.lean:43`).

**Theorem: Square of a sum of two scalars.** The square of a sum of two real numbers is at most twice the sum of their squares. Source: `Breakdown.CertReduction.Internal.ProfileFieldApprox.add_sq_le_two` (`Breakdown/CellReduction/ProfileFieldApprox.lean:58`).

**Theorem: Square of a sum of three scalars.** The square of a sum of three real numbers is at most three times the sum of their squares. Source: `Breakdown.CertReduction.Internal.ProfileFieldApprox.add_three_sq_le` (`Breakdown/CellReduction/ProfileFieldApprox.lean:61`).

**Theorem: Squared norm of a vector sum.** The squared norm of a sum of two vectors is at most twice the sum of their squared norms. Source: `Breakdown.CertReduction.Internal.ProfileFieldApprox.norm_add_sq_le` (`Breakdown/CellReduction/ProfileFieldApprox.lean:64`).

**Theorem: Coordinate vectors have unit norm.** Every coordinate unit vector has norm one. Source: `Breakdown.CertReduction.Internal.ProfileFieldApprox.norm_unit` (`Breakdown/CellReduction/ProfileFieldApprox.lean:67`).

**Theorem: Matrix square norm is nonnegative.** The sum of the squared matrix-column norms is nonnegative. Source: `Breakdown.CertReduction.Internal.ProfileFieldApprox.matSq_nonneg_map` (`Breakdown/CellReduction/ProfileFieldApprox.lean:70`).

**Theorem: Matrix squares of a sum.** The column-square sum of two matrices added together is at most twice the sum of their individual column-square sums. Source: `Breakdown.CertReduction.Internal.ProfileFieldApprox.matSq_add_le` (`Breakdown/CellReduction/ProfileFieldApprox.lean:73`).

**Theorem: Coordinate evaluation is norm-bounded.** The square of a scalar linear functional evaluated on a coordinate unit vector is bounded by its squared operator norm. Source: `Breakdown.CertReduction.Internal.ProfileFieldApprox.apply_unit_sq_le` (`Breakdown/CellReduction/ProfileFieldApprox.lean:79`).

**Theorem: Diagonal bilinear evaluation bound.** The absolute value of a bilinear form on a repeated coordinate unit vector is bounded by its operator norm. Source: `Breakdown.CertReduction.Internal.ProfileFieldApprox.apply_unit_two_le` (`Breakdown/CellReduction/ProfileFieldApprox.lean:85`).

**Theorem: Inverse-radius cutoff-gradient bound.** A uniform derivative bound c for the original bump bounds the scaled cutoff gradient by c divided by its positive radius R. Source: `Breakdown.CertReduction.Internal.ProfileFieldApprox.cut_first_le` (`Breakdown/CellReduction/ProfileFieldApprox.lean:91`).

**Theorem: Cutoff Hessian bound for large radius.** For R at least one, the Hessian of the scaled cutoff is bounded by c divided by R under the stated first and second derivative bounds. Source: `Breakdown.CertReduction.Internal.ProfileFieldApprox.cut_second_le` (`Breakdown/CellReduction/ProfileFieldApprox.lean:99`).

**Theorem: Cutoff gradient vanishes off the ring.** For positive radius, the cutoff gradient vanishes outside the transition ring. Source: `Breakdown.CertReduction.Internal.ProfileFieldApprox.cut_first_zero` (`Breakdown/CellReduction/ProfileFieldApprox.lean:111`).

**Theorem: Cutoff Hessian vanishes off the ring.** For positive radius, the cutoff Hessian vanishes outside the transition ring. Source: `Breakdown.CertReduction.Internal.ProfileFieldApprox.cut_second_zero` (`Breakdown/CellReduction/ProfileFieldApprox.lean:118`).

**Theorem: Cutoff error lies in the exterior.** The squared difference between the cutoff and one is bounded by the indicator of the exterior region. Source: `Breakdown.CertReduction.Internal.ProfileFieldApprox.cut_sub_one_sq` (`Breakdown/CellReduction/ProfileFieldApprox.lean:133`).

**Theorem: Squared cutoff-gradient bound.** The squared cutoff gradient is bounded by c² divided by R² times the indicator of the transition ring. Source: `Breakdown.CertReduction.Internal.ProfileFieldApprox.cut_first_sq` (`Breakdown/CellReduction/ProfileFieldApprox.lean:144`).

**Theorem: Squared cutoff-Hessian bound.** For R at least one, the squared cutoff Hessian is bounded by c² divided by R² times the transition-ring indicator. Source: `Breakdown.CertReduction.Internal.ProfileFieldApprox.cut_second_sq` (`Breakdown/CellReduction/ProfileFieldApprox.lean:153`).

**Theorem: Product rule for a cutoff field.** The derivative of a scalar cutoff times a smooth vector field is the cutoff times the field derivative plus the cutoff derivative times the field. Source: `Breakdown.CertReduction.Internal.ProfileFieldApprox.first_col` (`Breakdown/CellReduction/ProfileFieldApprox.lean:164`).

**Theorem: Gradient error after cutoff.** Subtracting the original field gradient leaves the cutoff-minus-one term and the derivative-of-cutoff term. Source: `Breakdown.CertReduction.Internal.ProfileFieldApprox.first_col_sub` (`Breakdown/CellReduction/ProfileFieldApprox.lean:171`).

**Theorem: Repeated directional derivative.** Differentiating a fixed directional derivative in the same direction evaluates the Hessian on that direction twice. Source: `Breakdown.CertReduction.Internal.ProfileFieldApprox.dir_second_eq` (`Breakdown/CellReduction/ProfileFieldApprox.lean:178`).

**Theorem: Second derivative of a cutoff product.** The second directional derivative of a cutoff product is the cutoff times the second field derivative, twice the product of first derivatives, and the cutoff Hessian times the field. Source: `Breakdown.CertReduction.Internal.ProfileFieldApprox.second_col` (`Breakdown/CellReduction/ProfileFieldApprox.lean:185`).

**Theorem: A smooth field has continuous Laplacian.** The sum of the coordinate second derivatives of a smooth field is continuous. Source: `Breakdown.CertReduction.Internal.ProfileFieldApprox.trace_continuous` (`Breakdown/CellReduction/ProfileFieldApprox.lean:206`).

**Theorem: Laplacian error from a cutoff.** The cutoff Laplacian error splits into the cutoff-minus-one Laplacian, twice the paired first derivatives, and the cutoff Laplacian times the field. Source: `Breakdown.CertReduction.Internal.ProfileFieldApprox.trace_product_sub` (`Breakdown/CellReduction/ProfileFieldApprox.lean:215`).

**Theorem: Gradient cutoff error estimate.** The squared gradient error is bounded by twice the exterior gradient energy plus a transition-ring field term weighted by 6c² divided by R². Source: `Breakdown.CertReduction.Internal.ProfileFieldApprox.grad_err_le` (`Breakdown/CellReduction/ProfileFieldApprox.lean:227`).

**Theorem: Laplacian cutoff error estimate.** The squared Laplacian error is bounded by an exterior Laplacian term, a gradient term weighted by 36c² divided by R², and a ring term weighted by 27c² divided by R². Source: `Breakdown.CertReduction.Internal.ProfileFieldApprox.trace_err_le` (`Breakdown/CellReduction/ProfileFieldApprox.lean:251`).

**Theorem: Restricting a nonnegative value.** Multiplying a nonnegative function by a zero-one set indicator cannot increase its nonnegative real embedding. Source: `Breakdown.CertReduction.Internal.ProfileFieldApprox.ofReal_ind_mul_le` (`Breakdown/CellReduction/ProfileFieldApprox.lean:333`).

**Theorem: The integrable exterior tail vanishes.** For a continuous nonnegative integrable function, its integral outside radius k plus one tends to zero as k tends to infinity. Source: `Breakdown.CertReduction.Internal.ProfileFieldApprox.tail_tendsto` (`Breakdown/CellReduction/ProfileFieldApprox.lean:339`).

**Theorem: Ring L2 mass controlled by an L6 tail.** The ring integral of the squared field divided by R² is bounded by 8η times the unit-ball volume plus the exterior sixth-power integral divided by η². Source: `Breakdown.CertReduction.Internal.ProfileFieldApprox.ring_bound` (`Breakdown/CellReduction/ProfileFieldApprox.lean:359`).

**Theorem: The weighted ring mass vanishes.** For a continuous field with integrable sixth power, its ring L2 mass weighted by the inverse squared radius tends to zero. Source: `Breakdown.CertReduction.Internal.ProfileFieldApprox.ring_tendsto` (`Breakdown/CellReduction/ProfileFieldApprox.lean:402`).

**Theorem: Inverse squared radii tend to zero.** The extended nonnegative-real values of one divided by the squares of k plus one tend to zero. Source: `Breakdown.CertReduction.Internal.ProfileFieldApprox.inv_sq_tendsto` (`Breakdown/CellReduction/ProfileFieldApprox.lean:431`).

**Theorem: Cutoff convergence of both derivatives.** For the stated smooth field with finite sixth-power, gradient and Laplacian integrals, both cutoff errors tend to zero in their squared L2 integrals. Source: `Breakdown.CertReduction.Internal.ProfileFieldApprox.cutoff_limits` (`Breakdown/CellReduction/ProfileFieldApprox.lean:439`).

**Theorem: Weak Hessian diagonal is locally L1.** The weak-gradient identities for the columns of G make every diagonal component of H locally integrable. Source: `Breakdown.CertReduction.Internal.ProfileFieldApprox.diag_locallyIntegrable` (`Breakdown/CellReduction/ProfileFieldApprox.lean:543`).

**Theorem: Laplacian commutes with mollification.** The Laplacian of the mollified field equals convolution of the kernel with the trace of the supplied weak Hessian. Source: `Breakdown.CertReduction.Internal.ProfileFieldApprox.smoothed_trace` (`Breakdown/CellReduction/ProfileFieldApprox.lean:550`).

**Theorem: Mollification converges in both energies.** The smooth approximants retain finite L6, gradient and Laplacian integrals and converge to the weak gradient and Laplacian in square integral. Source: `Breakdown.CertReduction.Internal.ProfileFieldApprox.mollify_limits` (`Breakdown/CellReduction/ProfileFieldApprox.lean:578`).

**Theorem: A compact smooth approximation exists.** For every positive tolerance r, a profile field has a smooth compactly supported approximation whose squared gradient and Laplacian errors are each at most r. Source: `Breakdown.CertReduction.Internal.ProfileFieldApprox.approx_step` (`Breakdown/CellReduction/ProfileFieldApprox.lean:651`).

**Theorem: Approximate in gradient and Laplacian.** The weak profile field admits compact smooth approximants converging in both gradient square integral and Laplacian square integral. Source: `Breakdown.CertReduction.profileFieldApprox` (`Breakdown/CellReduction/ProfileFieldApprox.lean:724`).

### Breakdown.CellReduction.ReductionClosed

The proved matrix, energy, convection and shift estimates are supplied to the reduction interfaces.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: Matrix bounds used by the reduction.** The operator-square and symmetric-strain bounds both hold. Source: `Breakdown.CertReduction.matrixFactsHolds_proof` (`Breakdown/CellReduction/ReductionClosed.lean:25`).

**Theorem: Supremum from two derivative energies.** A weak L6 field with finite gradient and Laplacian energies obeys the almost-everywhere supremum estimate with constant one over two pi. Source: `Breakdown.CertReduction.sliceSupNormHolds_proof` (`Breakdown/CellReduction/ReductionClosed.lean:27`).

**Theorem: Valid perturbations have good slices.** An admissible spacetime perturbation has weak first and second derivatives and finite L6, gradient and Laplacian energies on almost every slice. Source: `Breakdown.CertReduction.perturbationSliceHolds_proof` (`Breakdown/CellReduction/ReductionClosed.lean:30`).

**Theorem: Assemble the period integral bounds.** The finite-sum, period-pairing, spatial-pairing and slice-integration estimates all hold. Source: `Breakdown.CertReduction.periodGlueHolds_proof` (`Breakdown/CellReduction/ReductionClosed.lean:37`).

**Theorem: The frozen convection is integrable.** Both frozen convection integrands are integrable for the stated decaying smooth model and weak profile. Source: `Breakdown.CertReduction.frozenIntegrandHolds_proof` (`Breakdown/CellReduction/ReductionClosed.lean:39`).

**Theorem: Supremum part of the form shift.** A bounded shift controls the gradient–Laplacian product by its supremum coefficient times stationary energy. Source: `Breakdown.CertReduction.shiftSupTermHolds_proof` (`Breakdown/CellReduction/ReductionClosed.lean:48`).

**Theorem: Gradient part of the form shift.** The selected gradient norm controls the velocity–Laplacian product by its coefficient times stationary energy. Source: `Breakdown.CertReduction.shiftGradTermHolds_proof` (`Breakdown/CellReduction/ReductionClosed.lean:50`).

**Theorem: Strain gives a lower energy bound.** Under the stated hypotheses, a quadratic lower bound on the model gradient bounds convection from below by minus the strain coefficient divided by the weight times stationary energy. Source: `Breakdown.CertReduction.strainTermHolds_of_convection` (`Breakdown/CellReduction/ReductionClosed.lean:60`).

**Theorem: Assemble the analytic reduction bounds.** The named premises supply the nineteen matrix, energy, convection, gap, shift and adjoint propositions listed in the conclusion. Source: `Breakdown.CertReduction.reductionStatements_of` (`Breakdown/CellReduction/ReductionClosed.lean:68`).

### Breakdown.CellReduction.ReductionStatements

The cell-to-certificate reduction records the matrix, energy, gap, frozen-form and adjoint estimates as explicit propositions.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Interface definition: The column norm bounds the operator.** This proposition requires that the squared operator norm of a matrix is bounded by its column square sum. Source: `Breakdown.CertReduction.OperatorSquareBoundHolds` (`Breakdown/CellReduction/ReductionStatements.lean:13`).

Supplied by `Breakdown.CertReduction.operatorSquareBound` (`lean/Breakdown/CellReduction/MatrixFacts.lean:40`).

**Interface definition: The symmetric part bounds strain.** This proposition requires that a bound S on the symmetric part gives the quadratic lower bound minus S times the vector norm squared. Source: `Breakdown.CertReduction.StrainOfSymmetricPartHolds` (`Breakdown/CellReduction/ReductionStatements.lean:16`).

Supplied by `Breakdown.CertReduction.strainOfSymmetricPart` (`lean/Breakdown/CellReduction/MatrixFacts.lean:51`).

**Interface definition: Matrix bounds used by the reduction.** This proposition requires that the operator-square and symmetric-strain bounds both hold. Source: `Breakdown.CertReduction.MatrixFactsHolds` (`Breakdown/CellReduction/ReductionStatements.lean:20`).

Supplied by `Breakdown.CertReduction.matrixFacts` (`lean/Breakdown/CellReduction/MatrixFacts.lean:72`); `Breakdown.CertReduction.matrixFactsHolds_proof` (`lean/Breakdown/CellReduction/ReductionClosed.lean:25`); `Breakdown.CertReduction.reductionStatements_of` (`lean/Breakdown/CellReduction/ReductionClosed.lean:68`) with conjunction projection `.1`.

**Interface definition: Supremum from two derivative energies.** This proposition requires that a weak L6 field with finite gradient and Laplacian energies obeys the almost-everywhere supremum estimate with constant one over two pi. Source: `Breakdown.CertReduction.SliceSupNormHolds` (`Breakdown/CellReduction/ReductionStatements.lean:23`).

Supplied by `Breakdown.CertReduction.sliceSupNormHolds_proof` (`lean/Breakdown/CellReduction/ReductionClosed.lean:27`); `Breakdown.CertReduction.reductionStatements_of` (`lean/Breakdown/CellReduction/ReductionClosed.lean:68`) with conjunction projection `.2.1`; `Breakdown.CertReduction.sliceSupNorm_of` (`lean/Breakdown/CellReduction/SliceSupNorm.lean:35`).

**Interface definition: Valid perturbations have good slices.** This proposition requires that an admissible spacetime perturbation has weak first and second derivatives and finite L6, gradient and Laplacian energies on almost every slice. Source: `Breakdown.CertReduction.PerturbationSliceHolds` (`Breakdown/CellReduction/ReductionStatements.lean:34`).

Supplied by `Breakdown.CertReduction.perturbationSliceHolds` (`lean/Breakdown/CellReduction/PerturbationSlice.lean:62`); `Breakdown.CertReduction.perturbationSliceHolds_proof` (`lean/Breakdown/CellReduction/ReductionClosed.lean:30`); `Breakdown.CertReduction.reductionStatements_of` (`lean/Breakdown/CellReduction/ReductionClosed.lean:68`) with conjunction projection `.2.2.1`.

**Interface definition: Slice values are bounded by energy.** This proposition requires that the slice value squared is bounded almost everywhere by the stated coefficient times its gradient–Laplacian energy. Source: `Breakdown.CertReduction.SliceEnergySupHolds` (`Breakdown/CellReduction/ReductionStatements.lean:45`).

Supplied by `Breakdown.CertReduction.sliceEnergySup_of` (`lean/Breakdown/CellReduction/EnergyBounds.lean:41`).

**Interface definition: Profile values are bounded by energy.** This proposition requires that the stationary weak-profile value squared is bounded almost everywhere by the stated coefficient times stationary energy. Source: `Breakdown.CertReduction.ProfileEnergySupHolds` (`Breakdown/CellReduction/ReductionStatements.lean:52`).

Supplied by `Breakdown.CertReduction.profileEnergySup_of` (`lean/Breakdown/CellReduction/EnergyBounds.lean:51`).

**Interface definition: Energy controls the period gradient.** This proposition requires that the constant energy weight times the period gradient square integral is bounded by total weighted energy. Source: `Breakdown.CertReduction.PeriodGradientEnergyHolds` (`Breakdown/CellReduction/ReductionStatements.lean:58`).

Supplied by `Breakdown.CertReduction.periodGradientEnergy` (`lean/Breakdown/CellReduction/EnergyBounds.lean:61`).

**Interface definition: The cubic-weight Sobolev estimate.** This proposition requires that the weighted velocity square integral is bounded by four thirds times the cubic weight norm to the two-thirds power times gradient energy. Source: `Breakdown.CertReduction.CubicWeightProductHolds` (`Breakdown/CellReduction/ReductionStatements.lean:67`).

Supplied by `Breakdown.CertReduction.cubicWeightProductHolds` (`lean/Breakdown/CellReduction/CubicWeightProduct.lean:35`); `Breakdown.CertReduction.cubicWeightProductHolds_proof` (`lean/Breakdown/CellReduction/ReductionClosed.lean:35`); `Breakdown.CertReduction.reductionStatements_of` (`lean/Breakdown/CellReduction/ReductionClosed.lean:68`) with conjunction projection `.2.2.2.2.1`.

**Interface definition: Sum the period square bounds.** This proposition requires that a nonnegative sum of pieces with energy coefficients has a period square bound with the sum of those coefficients. Source: `Breakdown.CertReduction.PeriodSumBoundHolds` (`Breakdown/CellReduction/ReductionStatements.lean:77`).

Supplied by `Breakdown.CertReduction.periodSumBound` (`lean/Breakdown/CellReduction/PeriodGlue.lean:48`).

**Interface definition: Control the period pairing.** This proposition requires that a bound on the period integral of the product of norms bounds the absolute period pairing. Source: `Breakdown.CertReduction.PeriodPairingBoundHolds` (`Breakdown/CellReduction/ReductionStatements.lean:85`).

Supplied by `Breakdown.CertReduction.periodPairingBound` (`lean/Breakdown/CellReduction/PeriodGlue.lean:95`).

**Interface definition: Control the spatial pairing.** This proposition requires that a bound on the spatial integral of the product of norms bounds the absolute spatial pairing. Source: `Breakdown.CertReduction.StationaryPairingBoundHolds` (`Breakdown/CellReduction/ReductionStatements.lean:90`).

Supplied by `Breakdown.CertReduction.stationaryPairingBound` (`lean/Breakdown/CellReduction/PeriodGlue.lean:106`).

**Interface definition: Integrate the slice inequalities.** This proposition requires that an almost-everywhere nonnegative slice integral bound extends to the period integral. Source: `Breakdown.CertReduction.SliceIntegrateHolds` (`Breakdown/CellReduction/ReductionStatements.lean:95`).

Supplied by `Breakdown.CertReduction.sliceIntegrate` (`lean/Breakdown/CellReduction/PeriodGlue.lean:110`).

**Interface definition: Assemble the period integral bounds.** This proposition requires that the finite-sum, period-pairing, spatial-pairing and slice-integration estimates all hold. Source: `Breakdown.CertReduction.PeriodGlueHolds` (`Breakdown/CellReduction/ReductionStatements.lean:100`).

Supplied by `Breakdown.CertReduction.periodGlue` (`lean/Breakdown/CellReduction/PeriodGlue.lean:119`); `Breakdown.CertReduction.periodGlueHolds_proof` (`lean/Breakdown/CellReduction/ReductionClosed.lean:37`); `Breakdown.CertReduction.reductionStatements_of` (`lean/Breakdown/CellReduction/ReductionClosed.lean:68`) with conjunction projection `.2.2.2.2.2.1`.

**Interface definition: Convection equals the strain pairing.** This proposition requires that under the divergence and regularity hypotheses, convection against the negative Laplacian equals the gradient's strain pairing. Source: `Breakdown.CertReduction.ConvectionIdentityHolds` (`Breakdown/CellReduction/ReductionStatements.lean:103`).

Supplied by `Breakdown.CertReduction.convectionIdentityHolds_of` (`lean/Breakdown/CellReduction/ConvectionIdentity.lean:248`); `Breakdown.CertReduction.convectionIdentityHolds_of_approx` (`lean/Breakdown/CellReduction/ConvectionIdentity.lean:354`); `Breakdown.CertReduction.convectionIdentity_holds` (`lean/Breakdown/CellReduction/ConvectionIdentityClosed.lean:8`); `Breakdown.CertReduction.reductionStatements_of` (`lean/Breakdown/CellReduction/ReductionClosed.lean:68`) with conjunction projection `.2.2.2.2.2.2.1`.

**Interface definition: The frozen convection is integrable.** This proposition requires that both frozen convection integrands are integrable for the stated decaying smooth model and weak profile. Source: `Breakdown.CertReduction.FrozenIntegrandHolds` (`Breakdown/CellReduction/ReductionStatements.lean:112`).

Supplied by `Breakdown.CertReduction.frozenIntegrand` (`lean/Breakdown/CellReduction/FrozenIntegrand.lean:73`); `Breakdown.CertReduction.frozenIntegrandHolds_proof` (`lean/Breakdown/CellReduction/ReductionClosed.lean:39`); `Breakdown.CertReduction.reductionStatements_of` (`lean/Breakdown/CellReduction/ReductionClosed.lean:68`) with conjunction projection `.2.2.2.2.2.2.2.1`.

**Definition: Standing assumptions for reduction.** This proposition requires that the weight is positive and constant and the model, profile and adjoints satisfy the regularity and decay required by the analytic bridges. Source: `Breakdown.CertReduction.BridgeStanding` (`Breakdown/CellReduction/ReductionStatements.lean:120`).

**Definition: Control the profile-to-model gap.** This proposition requires that the period square of the linearized profile-minus-model term is bounded by gap size squared times weighted energy. Source: `Breakdown.CertReduction.GapTransferClause` (`Breakdown/CellReduction/ReductionStatements.lean:131`).

**Definition: Control the frozen-form shift.** This proposition requires that the profile's frozen form differs from the model's by at least minus the form-shift coefficient times stationary energy. Source: `Breakdown.CertReduction.FormShiftClause` (`Breakdown/CellReduction/ReductionStatements.lean:137`).

**Definition: The frozen model form has a bound.** This proposition requires that the model's frozen form is bounded below by minus its recorded coefficient times stationary energy. Source: `Breakdown.CertReduction.FrozenFormClause` (`Breakdown/CellReduction/ReductionStatements.lean:142`).

**Definition: Control the nonlinear adjoint pairing.** This proposition requires that the nonlinear velocity-gradient pairing with each selected adjoint is bounded by its coefficient times weighted energy. Source: `Breakdown.CertReduction.AdjointQuadraticClause` (`Breakdown/CellReduction/ReductionStatements.lean:146`).

**Definition: Pieces of the profile shift.** This proposition requires that the record stores a finite decomposition of the profile shift with gradients, norm choices and numerical bounds. Source: `Breakdown.CertReduction.ShiftPieces` (`Breakdown/CellReduction/ReductionStatements.lean:152`).

**Definition: Choose a cubic or square norm.** This proposition requires that the gradient is bounded in L3 when the flag is true and in L2 when the flag is false. Source: `Breakdown.CertReduction.PieceGradBound` (`Breakdown/CellReduction/ReductionStatements.lean:160`).

**Definition: Validity of the shift decomposition.** This proposition requires that the stored pieces sum to the profile-minus-model difference and its derivative and obey the recorded measurability, supremum and gradient-norm bounds. Source: `Breakdown.CertReduction.ShiftPiecesValid` (`Breakdown/CellReduction/ReductionStatements.lean:164`).

**Interface definition: Regularity of the shift decomposition.** This proposition requires that a smooth finite decomposition yields the derivative decomposition and measurable piece and gradient fields. Source: `Breakdown.CertReduction.SmoothShiftPiecesHolds` (`Breakdown/CellReduction/ReductionStatements.lean:176`).

Supplied by `Breakdown.CertReduction.reductionStatements_of` (`lean/Breakdown/CellReduction/ReductionClosed.lean:68`) with conjunction projection `.2.2.2.2.2.2.2.2.1`; `Breakdown.CertReduction.smoothShiftPiecesHolds` (`lean/Breakdown/CellReduction/SmoothShiftPieces.lean:32`).

**Definition: Numbers for the gap-transfer bound.** This proposition requires that the valid shift pieces have a total computed gap contribution no larger than the certificate's gap size. Source: `Breakdown.CertReduction.GapTransferBounded` (`Breakdown/CellReduction/ReductionStatements.lean:186`).

**Definition: Numbers for the form-shift bound.** This proposition requires that the valid shift pieces have a total computed form contribution no larger than the certificate's form-shift coefficient. Source: `Breakdown.CertReduction.FormShiftBounded` (`Breakdown/CellReduction/ReductionStatements.lean:191`).

**Interface definition: Supremum part of the gap estimate.** This proposition requires that a uniformly bounded shift controls the square integral of the perturbation gradient applied to it by weighted energy. Source: `Breakdown.CertReduction.GapSupTermHolds` (`Breakdown/CellReduction/ReductionStatements.lean:196`).

Supplied by `Breakdown.CertReduction.gapSupTerm_of` (`lean/Breakdown/CellReduction/GapSupTerm.lean:74`); `Breakdown.CertReduction.gapSupTermHolds_proof` (`lean/Breakdown/CellReduction/ReductionClosed.lean:41`); `Breakdown.CertReduction.reductionStatements_of` (`lean/Breakdown/CellReduction/ReductionClosed.lean:68`) with conjunction projection `.2.2.2.2.2.2.2.2.2.1`.

**Interface definition: Gradient part of the gap estimate.** This proposition requires that the selected L3 or L2 bound on the shift gradient controls its product with the perturbation velocity by weighted energy. Source: `Breakdown.CertReduction.GapGradTermHolds` (`Breakdown/CellReduction/ReductionStatements.lean:203`).

Supplied by `Breakdown.CertReduction.gapGradTerm_of` (`lean/Breakdown/CellReduction/GapGradTerm.lean:97`); `Breakdown.CertReduction.gapGradTermHolds_proof` (`lean/Breakdown/CellReduction/ReductionClosed.lean:44`); `Breakdown.CertReduction.reductionStatements_of` (`lean/Breakdown/CellReduction/ReductionClosed.lean:68`) with conjunction projection `.2.2.2.2.2.2.2.2.2.2.1`.

**Interface definition: Supremum part of the form shift.** This proposition requires that a bounded shift controls the gradient–Laplacian product by its supremum coefficient times stationary energy. Source: `Breakdown.CertReduction.ShiftSupTermHolds` (`Breakdown/CellReduction/ReductionStatements.lean:212`).

Supplied by `Breakdown.CertReduction.shiftSupTermHolds_proof` (`lean/Breakdown/CellReduction/ReductionClosed.lean:48`); `Breakdown.CertReduction.reductionStatements_of` (`lean/Breakdown/CellReduction/ReductionClosed.lean:68`) with conjunction projection `.2.2.2.2.2.2.2.2.2.2.2.1`; `Breakdown.CertReduction.shiftSupTerm_of` (`lean/Breakdown/CellReduction/ShiftSupTerm.lean:51`).

**Interface definition: Gradient part of the form shift.** This proposition requires that the selected gradient norm controls the velocity–Laplacian product by its coefficient times stationary energy. Source: `Breakdown.CertReduction.ShiftGradTermHolds` (`Breakdown/CellReduction/ReductionStatements.lean:219`).

Supplied by `Breakdown.CertReduction.shiftGradTermHolds_proof` (`lean/Breakdown/CellReduction/ReductionClosed.lean:50`); `Breakdown.CertReduction.reductionStatements_of` (`lean/Breakdown/CellReduction/ReductionClosed.lean:68`) with conjunction projection `.2.2.2.2.2.2.2.2.2.2.2.2.1`; `Breakdown.CertReduction.shiftGradTerm_of` (`lean/Breakdown/CellReduction/ShiftGradTerm.lean:62`).

**Interface definition: Strain gives a lower energy bound.** This proposition requires that a quadratic lower bound on the model gradient bounds convection from below by minus the strain coefficient divided by the weight times stationary energy. Source: `Breakdown.CertReduction.StrainTermHolds` (`Breakdown/CellReduction/ReductionStatements.lean:226`).

Supplied by `Breakdown.CertReduction.strainTermHolds_of_convection` (`lean/Breakdown/CellReduction/ReductionClosed.lean:60`); `Breakdown.CertReduction.reductionStatements_of` (`lean/Breakdown/CellReduction/ReductionClosed.lean:68`) with conjunction projection `.2.2.2.2.2.2.2.2.2.2.2.2.2.1`; `Breakdown.CertReduction.strainTerm_of` (`lean/Breakdown/CellReduction/StrainTerm.lean:47`).

**Interface definition: Bound the quadratic adjoint term.** This proposition requires that the selected adjoint size bound controls the nonlinear pairing by its coefficient times weighted energy. Source: `Breakdown.CertReduction.AdjointQuadTermHolds` (`Breakdown/CellReduction/ReductionStatements.lean:234`).

Supplied by `Breakdown.CertReduction.adjointQuadTerm_of` (`lean/Breakdown/CellReduction/AdjointQuadTerm.lean:133`); `Breakdown.CertReduction.reductionStatements_of` (`lean/Breakdown/CellReduction/ReductionClosed.lean:68`) with conjunction projection `.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1`.

### Breakdown.CellReduction.ShiftGradTerm

The derivative contribution to the form shift is bounded using the weighted energy and the selected cubic or square norm.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: Integral product controlled by L2 bounds.** For nonnegative K and L, nonnegative measurable factors with squared integral bounds K² and L² have product integral at most KL. Source: `Breakdown.CertReduction.Internal.shiftGrad_lintegral_mul_le` (`Breakdown/CellReduction/ShiftGradTerm.lean:14`).

**Theorem: Weighted Young inequality for energy.** For positive energy weight, the product of two real factors is bounded by their weighted square sum divided by twice the square root of that weight. Source: `Breakdown.CertReduction.Internal.shiftGrad_product_le_energy` (`Breakdown/CellReduction/ShiftGradTerm.lean:44`).

**Theorem: The matrix square norm is continuous.** The sum of the squared matrix-column norms depends continuously on the matrix. Source: `Breakdown.CertReduction.Internal.shiftGrad_columnSquareSum_continuous` (`Breakdown/CellReduction/ShiftGradTerm.lean:51`).

**Theorem: Matrix square norm is nonnegative.** The sum of the squared matrix-column norms is nonnegative. Source: `Breakdown.CertReduction.Internal.shiftGrad_columnSquareSum_nonneg` (`Breakdown/CellReduction/ShiftGradTerm.lean:56`).

**Theorem: Gradient part of the form shift.** Under the stated hypotheses, the selected gradient norm controls the velocity–Laplacian product by its coefficient times stationary energy. Source: `Breakdown.CertReduction.shiftGradTerm_of` (`Breakdown/CellReduction/ShiftGradTerm.lean:62`).

### Breakdown.CellReduction.ShiftSupTerm

The supremum contribution to the form shift is bounded by the stationary weighted energy.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: Weighted Young inequality for energy.** For positive energy weight, the product of two real factors is bounded by their weighted square sum divided by twice the square root of that weight. Source: `Breakdown.CertReduction.ShiftSupInternal.product_le_energy` (`Breakdown/CellReduction/ShiftSupTerm.lean:14`).

**Theorem: Matrix square norm is nonnegative.** The sum of the squared matrix-column norms is nonnegative. Source: `Breakdown.CertReduction.ShiftSupInternal.columnSum_nonneg` (`Breakdown/CellReduction/ShiftSupTerm.lean:21`).

**Theorem: The matrix square norm is continuous.** The sum of the squared matrix-column norms depends continuously on the matrix. Source: `Breakdown.CertReduction.ShiftSupInternal.columnSum_continuous` (`Breakdown/CellReduction/ShiftSupTerm.lean:24`).

**Theorem: Hessian trace through flipped columns.** The Hessian trace equals the sum of its flipped coordinate columns evaluated on the corresponding coordinate vectors. Source: `Breakdown.CertReduction.ShiftSupInternal.trace_eq` (`Breakdown/CellReduction/ShiftSupTerm.lean:28`).

**Theorem: Absorb a bounded vector into the energy.** If the vector has norm at most s, the product of the image norm and a second vector norm is bounded by s divided by twice the square root of w₀ times the weighted quadratic energy. Source: `Breakdown.CertReduction.ShiftSupInternal.pointwise_le` (`Breakdown/CellReduction/ShiftSupTerm.lean:32`).

**Theorem: Supremum part of the form shift.** Under the stated hypotheses, a bounded shift controls the gradient–Laplacian product by its supremum coefficient times stationary energy. Source: `Breakdown.CertReduction.shiftSupTerm_of` (`Breakdown/CellReduction/ShiftSupTerm.lean:51`).

### Breakdown.CellReduction.SliceSupNorm

A smooth supremum estimate and mollification provide the almost-everywhere bound for weak profile slices.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Interface definition: The smooth supremum inequality.** This proposition requires that a smooth L6 field with finite gradient and Laplacian energies satisfies the pointwise supremum estimate with constant one over two pi. Source: `Breakdown.CertReduction.SmoothSupNormBoundHolds` (`Breakdown/CellReduction/SliceSupNorm.lean:12`).

Supplied by `Breakdown.CertReduction.smoothSupNormBound` (`lean/Breakdown/CellReduction/SliceSupNormSmooth.lean:400`).

**Interface definition: Mollification preserves the energies.** This proposition requires that a weak L6 field admits smooth approximants with no larger gradient or Laplacian energy and almost-everywhere convergence. Source: `Breakdown.CertReduction.WeakFieldMollifyHolds` (`Breakdown/CellReduction/SliceSupNorm.lean:19`).

Supplied by `Breakdown.CertReduction.weakFieldMollify` (`lean/Breakdown/CellReduction/SliceSupNormMollify.lean:119`).

**Theorem: Supremum from two derivative energies.** Under the stated hypotheses, a weak L6 field with finite gradient and Laplacian energies obeys the almost-everywhere supremum estimate with constant one over two pi. Source: `Breakdown.CertReduction.sliceSupNorm_of` (`Breakdown/CellReduction/SliceSupNorm.lean:35`).

### Breakdown.CellReduction.SliceSupNormMollify

Convolution preserves the required derivative energies and produces smooth fields converging almost everywhere.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: Finite nonnegative integral gives L1.** An almost-everywhere strongly measurable nonnegative function with finite nonnegative integral is integrable. Source: `Breakdown.CertReduction.Internal.WeakFieldMollify.integrable_of_lintegral_lt` (`Breakdown/CellReduction/SliceSupNormMollify.lean:14`).

**Theorem: Convex power bound for a mollified field.** For an integer power at least one, the power of the mollified field norm is bounded by mollifying the same power of the original norm. Source: `Breakdown.CertReduction.Internal.WeakFieldMollify.kernel_pow_le` (`Breakdown/CellReduction/SliceSupNormMollify.lean:18`).

**Theorem: Mollification contracts power integrals.** Mollification preserves integrability of the indicated norm power and does not increase its integral. Source: `Breakdown.CertReduction.Internal.WeakFieldMollify.kernel_pow_integral` (`Breakdown/CellReduction/SliceSupNormMollify.lean:57`).

**Theorem: Mollify the weak-gradient columns.** A coordinate derivative of the mollified field equals the mollification of that coordinate column of its weak gradient. Source: `Breakdown.CertReduction.Internal.WeakFieldMollify.fderiv_kernel_apply` (`Breakdown/CellReduction/SliceSupNormMollify.lean:76`).

**Theorem: Diagonal second-derivative identity.** The iterated second derivative on a repeated coordinate vector equals the corresponding repeated coordinate derivative. Source: `Breakdown.CertReduction.Internal.WeakFieldMollify.second_diag_eq` (`Breakdown/CellReduction/SliceSupNormMollify.lean:106`).

**Theorem: Mollify without increasing the energies.** The weak field admits smooth approximants with no larger gradient and Laplacian energies and almost-everywhere pointwise convergence. Source: `Breakdown.CertReduction.weakFieldMollify` (`Breakdown/CellReduction/SliceSupNormMollify.lean:119`).

### Breakdown.CellReduction.SliceSupNormSmooth

Spatial cutoffs extend the sharp gradient–Laplacian supremum bound to smooth fields without compact support.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: Matrix square norm is nonnegative.** The sum of the squared matrix-column norms is nonnegative. Source: `Breakdown.CertReduction.Internal.SliceSupNormSmooth.colSq_nonneg` (`Breakdown/CellReduction/SliceSupNormSmooth.lean:18`).

**Definition: Matrix columns in a Euclidean space.** The matrix columns are viewed as a finite L2 product of three vectors. Source: `Breakdown.CertReduction.Internal.SliceSupNormSmooth.columns` (`Breakdown/CellReduction/SliceSupNormSmooth.lean:21`).

**Theorem: Frobenius norm from the column tuple.** The square root of the sum of squared column norms equals the Hilbert norm of the column tuple. Source: `Breakdown.CertReduction.Internal.SliceSupNormSmooth.sqrt_colSq_eq` (`Breakdown/CellReduction/SliceSupNormSmooth.lean:24`).

**Theorem: Column tuples preserve addition.** Taking the column tuple commutes with adding linear maps. Source: `Breakdown.CertReduction.Internal.SliceSupNormSmooth.columns_add` (`Breakdown/CellReduction/SliceSupNormSmooth.lean:28`).

**Theorem: Triangle inequality for the column norm.** The square root of the column-square sum of A plus B is at most the sum of the corresponding square roots for A and B. Source: `Breakdown.CertReduction.Internal.SliceSupNormSmooth.sqrt_colSq_add_le` (`Breakdown/CellReduction/SliceSupNormSmooth.lean:32`).

**Theorem: Scaling the column norm.** Multiplying a linear map by c multiplies the square root of its column-square sum by the absolute value of c. Source: `Breakdown.CertReduction.Internal.SliceSupNormSmooth.sqrt_colSq_smul` (`Breakdown/CellReduction/SliceSupNormSmooth.lean:37`).

**Theorem: Column-norm bound for a rank-one map.** The square root of the column-square sum of a rank-one map is at most twice the product of the defining functional and vector norms. Source: `Breakdown.CertReduction.Internal.SliceSupNormSmooth.sqrt_colSq_smulRight_le` (`Breakdown/CellReduction/SliceSupNormSmooth.lean:44`).

**Theorem: One column versus the column norm.** Each coordinate column norm is bounded by the square root of the sum of all squared column norms. Source: `Breakdown.CertReduction.Internal.SliceSupNormSmooth.norm_apply_le_sqrt_colSq` (`Breakdown/CellReduction/SliceSupNormSmooth.lean:60`).

**Theorem: The matrix square norm is continuous.** The sum of the squared matrix-column norms depends continuously on the matrix. Source: `Breakdown.CertReduction.Internal.SliceSupNormSmooth.continuous_colSq` (`Breakdown/CellReduction/SliceSupNormSmooth.lean:65`).

**Theorem: The smooth Laplacian is continuous.** The Laplacian of the stated twice continuously differentiable field is continuous. Source: `Breakdown.CertReduction.Internal.SliceSupNormSmooth.continuous_traceSecond` (`Breakdown/CellReduction/SliceSupNormSmooth.lean:68`).

**Theorem: Partial derivative of a scalar product.** For differentiable factors, a coordinate derivative of a scalar times a field obeys the product rule. Source: `Breakdown.CertReduction.Internal.SliceSupNormSmooth.pd_smul_eq` (`Breakdown/CellReduction/SliceSupNormSmooth.lean:74`).

**Theorem: Partial derivatives preserve addition.** For differentiable fields, the coordinate derivative of their sum is the sum of their coordinate derivatives. Source: `Breakdown.CertReduction.Internal.SliceSupNormSmooth.pd_add_eq` (`Breakdown/CellReduction/SliceSupNormSmooth.lean:82`).

**Theorem: Laplacian product rule.** The Laplacian of a scalar times a smooth field is the scalar times the field Laplacian, twice the paired coordinate derivatives, and the scalar Laplacian times the field. Source: `Breakdown.CertReduction.Internal.SliceSupNormSmooth.traceSecond_smul_eq` (`Breakdown/CellReduction/SliceSupNormSmooth.lean:89`).

**Theorem: Spatial scaling of a partial derivative.** The coordinate derivative of k times g evaluated at c times y acquires the factor kc. Source: `Breakdown.CertReduction.Internal.SliceSupNormSmooth.pd_scaled` (`Breakdown/CellReduction/SliceSupNormSmooth.lean:109`).

**Theorem: Inverse-square cutoff-Laplacian bound.** One nonnegative constant bounds the absolute cutoff Laplacian by that constant divided by R² for every positive radius. Source: `Breakdown.CertReduction.Internal.SliceSupNormSmooth.cutoff_second_bound` (`Breakdown/CellReduction/SliceSupNormSmooth.lean:123`).

**Theorem: Local constancy gives zero Hessian.** Every repeated coordinate derivative vanishes at a point where the function is locally constant. Source: `Breakdown.CertReduction.Internal.SliceSupNormSmooth.pd_pd_zero_of_eventuallyEq` (`Breakdown/CellReduction/SliceSupNormSmooth.lean:155`).

**Theorem: Cutoff Laplacian inside the ball.** The cutoff Laplacian is zero strictly inside its inner ball. Source: `Breakdown.CertReduction.Internal.SliceSupNormSmooth.cutoff_second_zero_of_lt` (`Breakdown/CellReduction/SliceSupNormSmooth.lean:166`).

**Theorem: Cutoff Laplacian outside twice R.** The cutoff Laplacian is zero outside the ball of radius twice R. Source: `Breakdown.CertReduction.Internal.SliceSupNormSmooth.cutoff_second_zero_of_gt` (`Breakdown/CellReduction/SliceSupNormSmooth.lean:174`).

**Theorem: L2 norm from the squared-norm integral.** For an L2 field, the extended L2 norm is the nonnegative-real embedding of the square root of its squared-norm integral. Source: `Breakdown.CertReduction.Internal.SliceSupNormSmooth.eLpNorm_two_eq_sqrt` (`Breakdown/CellReduction/SliceSupNormSmooth.lean:181`).

**Theorem: Annular L2 bound from the L6 tail.** For positive R, a weight supported in the annulus from R to 2R and bounded in magnitude by a nonnegative M gives an L2 bound of 2MR times the cube root of the unit-ball volume times the continuous field’s exterior L6 norm. Source: `Breakdown.CertReduction.Internal.SliceSupNormSmooth.annulus_bound` (`Breakdown/CellReduction/SliceSupNormSmooth.lean:187`).

**Theorem: The exterior L6 norm tends to zero.** The L6 norm of a continuous L6 field restricted outside radius R tends to zero as R tends to infinity. Source: `Breakdown.CertReduction.Internal.SliceSupNormSmooth.tail_tendsto` (`Breakdown/CellReduction/SliceSupNormSmooth.lean:237`).

**Theorem: Gradient bound after applying a cutoff.** The L2 gradient norm after cutoff is bounded by the original gradient norm plus a constant multiple of the exterior L6 norm. Source: `Breakdown.CertReduction.Internal.SliceSupNormSmooth.grad_cut_bound` (`Breakdown/CellReduction/SliceSupNormSmooth.lean:260`).

**Theorem: Laplacian bound after applying a cutoff.** The L2 Laplacian norm after cutoff is bounded by the original Laplacian norm, an inverse-radius gradient term, and an exterior L6 term. Source: `Breakdown.CertReduction.Internal.SliceSupNormSmooth.traceSecond_cut_bound` (`Breakdown/CellReduction/SliceSupNormSmooth.lean:304`).

**Theorem: The smooth supremum bound.** The squared pointwise field norm is bounded by one over two pi times the product of the square roots of its gradient and Laplacian energies. Source: `Breakdown.CertReduction.smoothSupNormBound` (`Breakdown/CellReduction/SliceSupNormSmooth.lean:400`).

### Breakdown.CellReduction.SmoothShiftPieces

Joint differentiability supplies measurable spatial derivatives for the finite profile-shift decomposition.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: Spatial slice of a joint derivative.** The derivative on a fixed time slice is the joint derivative restricted to the spatial direction. Source: `Breakdown.CertReduction.Internal.slice_hasFDerivAt` (`Breakdown/CellReduction/SmoothShiftPieces.lean:14`).

**Theorem: The spatial derivative is continuous.** The spatial derivative of the joint continuously differentiable field is continuous in time and space. Source: `Breakdown.CertReduction.Internal.slice_fderiv_continuous` (`Breakdown/CellReduction/SmoothShiftPieces.lean:19`).

**Theorem: Regularity of the shift decomposition.** A smooth finite decomposition yields the derivative decomposition and measurable piece and gradient fields. Source: `Breakdown.CertReduction.smoothShiftPiecesHolds` (`Breakdown/CellReduction/SmoothShiftPieces.lean:32`).

### Breakdown.CellReduction.StrainTerm

The lower bound for the symmetric gradient gives the strain contribution to the frozen-form estimate.

**Paper context:** Appendix B, especially Proposition B.14; analytic support for the cell-to-certificate route into Theorem 7.1.

**Theorem: A coordinate is a unit-vector pairing.** A vector coordinate equals its real inner product with the corresponding coordinate unit vector. Source: `Breakdown.CertReduction.Internal.strainCoord_eq_inner_unit` (`Breakdown/CellReduction/StrainTerm.lean:14`).

**Theorem: Column-square sum of the adjoint.** The sum of squared norms of the adjoint's coordinate columns equals the original map's column-square sum. Source: `Breakdown.CertReduction.Internal.strainAdjointColumnSquareSum` (`Breakdown/CellReduction/StrainTerm.lean:17`).

**Theorem: Sum the lower bound over columns.** A quadratic lower bound of negative S times the squared norm gives the corresponding lower bound after summing over the adjoint columns of G. Source: `Breakdown.CertReduction.Internal.strainColumnSum_lower` (`Breakdown/CellReduction/StrainTerm.lean:28`).

**Theorem: The matrix square norm is continuous.** The sum of the squared matrix-column norms depends continuously on the matrix. Source: `Breakdown.CertReduction.Internal.strainColumnSquareSum_continuous` (`Breakdown/CellReduction/StrainTerm.lean:35`).

**Theorem: Matrix square norm is nonnegative.** The sum of the squared matrix-column norms is nonnegative. Source: `Breakdown.CertReduction.Internal.strainColumnSquareSum_nonneg` (`Breakdown/CellReduction/StrainTerm.lean:42`).

**Theorem: Strain gives a lower energy bound.** Under the stated hypotheses, a quadratic lower bound on the model gradient bounds convection from below by minus the strain coefficient divided by the weight times stationary energy. Source: `Breakdown.CertReduction.strainTerm_of` (`Breakdown/CellReduction/StrainTerm.lean:47`).
<!-- /passage:front -->

